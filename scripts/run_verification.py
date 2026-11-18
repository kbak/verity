#!/usr/bin/env python3
"""Run scoped verification commands under a reusable shared Linux memory budget."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import time
import uuid

from verification_runner.commands import SUPPLEMENTAL, lake_adapter, supplemental_command
from verification_runner.runtime import EXCLUSIVE, GIB, Runtime, can_admit, process, read, write

SCRIPT = Path(__file__).resolve()


def init(args):
    root = args.root.resolve()
    if '.lake' in root.parts or not (root / 'lean-toolchain').is_file():
        raise ValueError('Use a Verity checkout outside .lake; generated outputs belong inside .lake')
    path = args.config.resolve()
    if path.exists():
        raise FileExistsError('Existing configuration is preserved; edit it explicitly')
    turbo = Path(shutil.which(args.turbo) or args.turbo).resolve(strict=True)
    lake = Path(shutil.which(args.lake) or args.lake).resolve(strict=True)
    group = Path(args.cgroup)
    directory = path.parent
    if not directory.is_relative_to(root / '.lake'):
        raise ValueError('Keep runner configuration and warmup drivers inside the checkout .lake')
    binary = directory / 'tools/turbo-lean'
    config = {'root': str(root), 'cgroup': str(group), 'slice': group.name,
              'daemonUnit': group.stem + '-daemon.service', 'turbo': str(binary),
              'lake': str(lake), 'cachePrefix': f'/dev/shm/turbo-lean-staging-{os.getuid()}/zygote_daemon_cas_',
              'memoryHighGiB': args.memory_high, 'memoryMaxGiB': args.memory_max,
              'swapGiB': args.swap, 'hostReserveGiB': 4, 'sharedReserveGiB': 10,
              'admissionGiB': args.admission, 'maxJobs': 8, 'maxMutations': 5,
              'maxPressurePct': 8, 'profiles': {'light': 0.5, 'lean': 2.75,
                  'mutation': 3.25, 'build': 12, 'foundry': 6},
              'turboSha256': hashlib.sha256(turbo.read_bytes()).hexdigest()}
    Runtime.validate(config)
    # A private executable path gives this runner a distinct persistent-server identity.
    binary.parent.mkdir(parents=True, exist_ok=True)
    if binary.exists():
        raise FileExistsError('Refusing to replace an existing runner executable')
    shutil.copy2(turbo, binary)
    (directory / 'Warmup.lean').write_text('#eval IO.println "VERITY_RUNNER_READY"\n')
    (directory / 'bin').mkdir(exist_ok=True)
    for name in ('turbo-lean', 'lake'):
        shim = directory / 'bin' / name
        shim.write_text('#!' + sys.executable + '\nimport os\n'
                        + 'os.execv(' + repr(sys.executable) + ', '
                        + repr([sys.executable, str(SCRIPT), '--config', str(path), 'tool', name])
                        + ' + __import__("sys").argv[1:])\n')
        shim.chmod(0o755)
    write(path, config)
    print(path)


def start(runtime):
    with runtime.locked():
        c = runtime.config
        if hashlib.sha256(Path(c['turbo']).read_bytes()).hexdigest() != c['turboSha256']:
            raise RuntimeError('Dedicated Turbo-Lean binary changed')
        if runtime.active_jobs():
            raise RuntimeError('Drain admitted jobs before applying kernel limits')
        if runtime.group.exists():
            current = int((runtime.group / 'memory.current').read_text())
            if current >= c['memoryMaxGiB'] * GIB:
                raise RuntimeError('Do not lower the hard cap onto live memory use')
        # Instantiate the dedicated slice before applying properties. The daemon
        # waits on the same lock, then reads the newly applied policy.
        if runtime.properties(c['daemonUnit']).get('ActiveState') != 'active':
            subprocess.run(['systemctl', '--user', 'reset-failed', c['daemonUnit']],
                           capture_output=True, check=False)
            subprocess.run(['systemd-run', '--user', '--quiet', '--unit=' + c['daemonUnit'],
                            '--slice=' + c['slice'], '--property=KillMode=control-group',
                            '--property=WorkingDirectory=' + c['root'], '--', sys.executable,
                            str(SCRIPT), '--config', str(runtime.path), 'daemon'], check=True)
        subprocess.run(['systemctl', '--user', 'set-property', '--runtime', c['slice'],
                        'MemoryAccounting=yes', 'TasksMax=4096',
                        'MemoryHigh=' + str(int(c['memoryHighGiB'] * GIB)),
                        'MemoryMax=' + str(int(c['memoryMaxGiB'] * GIB)),
                        'MemorySwapMax=' + str(int(c['swapGiB'] * GIB))], check=True)
        runtime.verify_limits()
    runtime.wait_ready()


def daemon(runtime):
    me = process(os.getpid())
    c = runtime.config
    if me['group'] != c['cgroup'] + '/' + c['daemonUnit']:
        raise RuntimeError('Daemon must run in its dedicated service')
    status = {'status': 'starting', 'pid': me['pid'], 'start': me['start']}
    write(runtime.directory / 'daemon-status.json', status)
    with runtime.locked():
        runtime.verify_limits()
    warmup = subprocess.run([c['turbo'], '--json', 'eval',
                             str(runtime.directory / 'Warmup.lean'), '--project-dir', c['root'],
                             '--timeout-ms', '180000'], cwd=c['root'],
                            env=runtime.environment(os.environ), capture_output=True,
                            text=True, timeout=240)
    (runtime.directory / 'warmup.log').write_text(warmup.stdout + warmup.stderr)
    payload = json.loads(warmup.stdout)
    if (warmup.returncode or payload.get('ok') is not True or payload.get('errors')
            or 'VERITY_RUNNER_READY' not in json.dumps(payload)):
        raise RuntimeError('Warmup failed; see warmup.log')
    while True:
        with runtime.locked():
            runtime.verify_limits()
            moved = runtime.reconcile_pool()
        write(runtime.directory / 'daemon-status.json', dict(status, status='ready',
              checkedAt=time.time(), moved=moved))
        time.sleep(1)


def validate_command(command):
    if not command:
        raise ValueError('A command is required')
    for index, word in enumerate(command):
        jobs = command[index + 1] if word == '--jobs' and index + 1 < len(command) else None
        if word.startswith('--jobs='):
            jobs = word.split('=', 1)[1]
        if jobs is not None and jobs != '1':
            raise ValueError('Use one task per admitted job; nested worker pools bypass reservations')


def run(runtime, args, command):
    validate_command(command)
    if '--parallel-shards' in command and args.kind not in EXCLUSIVE:
        raise ValueError('Internally parallel builds require an exclusive profile')
    if (not re.fullmatch('[a-z0-9-]{1,48}', args.name)
            or args.timeout <= 0 or args.queue_timeout < 0):
        raise ValueError('Use a short lowercase job name and a positive timeout')
    identifier = args.name + '-' + uuid.uuid4().hex
    directory = runtime.directory / 'jobs' / identifier
    directory.mkdir(parents=True, exist_ok=False)
    me = process(os.getpid())
    row = {'name': args.name, 'kind': args.kind, 'command': command,
           'unit': runtime.config['slice'].removesuffix('.slice') + '-job-' + identifier + '.service',
           'launcherPid': me['pid'], 'launcherStart': me['start'], 'createdAt': time.time(),
           'env': runtime.environment(os.environ)}
    write(directory / 'request.json', row)
    admitted = False
    try:
        deadline = time.monotonic() + args.queue_timeout
        while True:
            with runtime.locked():
                runtime.verify_limits()
                row['reservedGiB'] = runtime.config['profiles'][args.kind]
                if (runtime.ready() and can_admit(runtime.config, args.kind,
                        runtime.active_jobs(), runtime.metrics())
                        and not runtime.older_exclusive_waiter(row)):
                    row['admittedAt'] = time.time()
                    row['sharedReserveGiB'] = runtime.config['sharedReserveGiB']
                    write(directory / 'admission.json', row)
                    admitted = True
                    break
            if time.monotonic() >= deadline:
                raise TimeoutError('Readiness/headroom deadline reached before test execution')
            write(directory / 'status.json', {'status': 'waiting', 'at': time.time()})
            time.sleep(1)
        write(directory / 'status.json', {'status': 'running', 'at': time.time()})
        launch = ['systemd-run', '--user', '--quiet', '--wait', '--slice=' + runtime.config['slice'],
                  '--unit=' + row['unit'], '--property=KillMode=control-group',
                  '--property=OOMPolicy=stop', '--property=TasksMax=1024',
                  '--property=RuntimeMaxSec=' + str(args.timeout),
                  '--property=WorkingDirectory=' + runtime.config['root'],
                  '--property=StandardOutput=append:' + str(directory / 'output.log'),
                  '--property=StandardError=append:' + str(directory / 'output.log'),
                  '--', sys.executable, str(SCRIPT), '--config', str(runtime.path),
                  'execute', str(directory / 'request.json')]
        # request.json is immutable input to execute; admission is separate state.
        result = subprocess.run(launch, capture_output=True, text=True)
        write(directory / 'status.json', {'status': 'passed' if result.returncode == 0 else 'failed',
              'returncode': result.returncode, 'finished': time.time(), 'launcherStderr': result.stderr})
        if (directory / 'output.log').exists():
            sys.stdout.write((directory / 'output.log').read_text())
        return result.returncode
    except BaseException as error:
        if admitted:
            subprocess.run(['systemctl', '--user', 'stop', row['unit']], capture_output=True)
        write(directory / 'status.json', {'status': 'failed', 'error': repr(error),
              'testLaunched': admitted, 'finished': time.time()})
        raise
    finally:
        if admitted:
            row['finished'] = time.time()
            write(directory / 'admission.json', row)
        print('Verification evidence: ' + str(directory), file=sys.stderr)


def execute(runtime, request):
    row = read(request)
    expected = runtime.config['cgroup'] + '/' + row['unit']
    if process(os.getpid())['group'] != expected:
        raise RuntimeError('Job must run inside its admitted transient unit')
    try:
        return subprocess.run(row['command'], cwd=runtime.config['root'], env=row['env']).returncode
    finally:
        # The owner also reconciles continuously. Do not allow a short job's exit
        # to kill a shared server that was started during daemon recovery.
        with runtime.locked():
            runtime.reconcile_pool()


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--config', type=Path, default=Path('.lake/verification-runner/config.json'))
    commands = parser.add_subparsers(dest='action', required=True)
    create = commands.add_parser('init', help='Create a dedicated runner, without starting services')
    create.add_argument('--root', type=Path, default=Path.cwd())
    create.add_argument('--turbo', default='turbo-lean')
    create.add_argument('--lake', default='lake')
    create.add_argument('--cgroup', required=True, help='Full cgroup-v2 path of the dedicated user slice')
    create.add_argument('--memory-high', type=float, default=26)
    create.add_argument('--memory-max', type=float, default=28)
    create.add_argument('--admission', type=float, default=27)
    create.add_argument('--swap', type=float, default=2)
    commands.add_parser('start', help='Apply limits and start/wait for the persistent worker owner')
    commands.add_parser('daemon', help='Internal persistent-owner service entrypoint')
    commands.add_parser('stop', help='Stop this runner owner after all jobs have drained')
    execution = commands.add_parser('execute', help='Internal admitted-job entrypoint')
    execution.add_argument('request', type=Path)
    tool = commands.add_parser('tool', help='Internal bounded-tool adapter')
    tool.add_argument('name', choices=['lake', 'turbo-lean'])
    tool.add_argument('args', nargs=argparse.REMAINDER)
    for action in ('run', 'supplemental'):
        job = commands.add_parser(action)
        job.add_argument('--name', required=action == 'run', default='supplemental')
        job.add_argument('--kind', default='mutation')
        job.add_argument('--timeout', type=int, default=3600)
        job.add_argument('--queue-timeout', type=int, default=3600)
        if action == 'run':
            job.add_argument('command', nargs=argparse.REMAINDER)
        else:
            job.add_argument('campaign', choices=list(SUPPLEMENTAL))
            job.add_argument('--python', default=sys.executable)
    args = parser.parse_args(argv)
    if args.action == 'init':
        init(args)
        return 0
    runtime = Runtime(args.config)
    if args.action == 'start':
        start(runtime)
    elif args.action == 'stop':
        with runtime.locked():
            if runtime.active_jobs():
                raise RuntimeError('Drain admitted jobs before stopping their shared worker owner')
            subprocess.run(['systemctl', '--user', 'stop', runtime.config['daemonUnit']], check=True)
    elif args.action == 'daemon':
        daemon(runtime)
    elif args.action == 'execute':
        return execute(runtime, args.request)
    elif args.action == 'tool':
        if not process(os.getpid())['group'].startswith(runtime.config['cgroup'] + '/'):
            raise RuntimeError('Use run so all workers share the admission budget')
        if args.name == 'lake':
            return lake_adapter(args.args, runtime.config['turbo'], runtime.config['lake'])
        os.execv(runtime.config['turbo'], [runtime.config['turbo'], *args.args])
    else:
        if args.kind not in runtime.config['profiles']:
            raise ValueError('Unknown reservation profile')
        if args.action == 'supplemental':
            command = supplemental_command(runtime.config['root'], args.campaign,
                                           uuid.uuid4().hex, args.python)
            args.name = args.campaign
        else:
            command = args.command[1:] if args.command[:1] == ['--'] else args.command
        return run(runtime, args, command)
    return 0


if __name__ == '__main__':
    try:
        raise SystemExit(main())
    except (OSError, ValueError, RuntimeError, subprocess.SubprocessError) as error:
        print(str(error), file=sys.stderr)
        raise SystemExit(1)
