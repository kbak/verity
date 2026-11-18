"""Shared Linux cgroup admission, readiness and persistent worker ownership."""
from contextlib import contextmanager
import fcntl
import json
import math
import os
from pathlib import Path
import re
import subprocess
import tempfile
import time

GIB = 2 ** 30
EXCLUSIVE = {'build', 'native'}


def write(path, data):
    path = Path(path)
    path.parent.mkdir(parents=True, exist_ok=True)
    fd, temporary = tempfile.mkstemp(dir=path.parent, prefix='.' + path.name)
    try:
        with os.fdopen(fd, 'w') as stream:
            json.dump(data, stream, indent=2)
            stream.write('\n')
        os.replace(temporary, path)
    finally:
        Path(temporary).unlink(missing_ok=True)


def read(path):
    return json.loads(Path(path).read_text())


def process(pid, proc=Path('/proc')):
    try:
        directory = proc / str(pid)
        # The process name may contain spaces and parentheses.
        stat = (directory / 'stat').read_text().rsplit(')', 1)[1].split()
        group = next(line[3:] for line in (directory / 'cgroup').read_text().splitlines()
                     if line.startswith('0::'))
        return {'pid': int(pid), 'ppid': int(stat[1]), 'start': stat[19], 'group': group,
                'args': [arg.decode() for arg in (directory / 'cmdline').read_bytes().split(b'\0')
                         if arg]}
    except (FileNotFoundError, ProcessLookupError, PermissionError, UnicodeDecodeError):
        return None


def in_group(group, parent):
    return group == parent or group.startswith(parent.rstrip('/') + '/')


def can_admit(config, kind, active, memory):
    if active and (kind in EXCLUSIVE or any(row['kind'] in EXCLUSIVE for row in active)):
        return False
    if len(active) >= config['maxJobs']:
        return False
    if kind == 'mutation' and sum(row['kind'] == kind for row in active) >= config['maxMutations']:
        return False
    shared = max([config['sharedReserveGiB'],
                  *(row.get('sharedReserveGiB', config['sharedReserveGiB']) for row in active)])
    reserved = shared + sum(row['reservedGiB'] for row in active)
    requested = config['profiles'][kind]
    return (max(reserved, memory['workingGiB']) + requested <= config['admissionGiB']
            and memory['availableGiB'] >= config['hostReserveGiB'] + requested
                + max(0, reserved - memory['workingGiB'])
            and memory['pressurePct'] < config['maxPressurePct']
            and not any(memory['events'].get(key, 0) for key in ('oom', 'oom_kill', 'max')))


class Runtime:
    def __init__(self, config_path):
        self.path = Path(config_path).resolve()
        self.directory = self.path.parent
        self.config = read(self.path)
        self.validate(self.config)
        self.group = Path('/sys/fs/cgroup') / self.config['cgroup'].lstrip('/')

    @staticmethod
    def validate(config):
        for key in ('slice', 'daemonUnit'):
            if not re.fullmatch(r'[A-Za-z0-9_.-]+', config[key]):
                raise ValueError(f'Invalid unit: {key}')
        if not config['slice'].endswith('.slice') or not config['daemonUnit'].endswith('.service'):
            raise ValueError('Expected a slice and service unit')
        group = Path(config['cgroup'])
        if not group.is_absolute() or '..' in group.parts or group.name != config['slice']:
            raise ValueError('cgroup must name the dedicated slice under /sys/fs/cgroup')
        for key in ('root', 'turbo', 'lake', 'cachePrefix'):
            if not Path(config[key]).is_absolute():
                raise ValueError(f'{key} must be absolute')
        numbers = [config[key] for key in ('memoryHighGiB', 'memoryMaxGiB', 'hostReserveGiB',
                   'sharedReserveGiB', 'admissionGiB', 'maxJobs', 'maxMutations', 'maxPressurePct')]
        numbers += list(config['profiles'].values())
        if any(not math.isfinite(value) or value <= 0 for value in numbers):
            raise ValueError('Budgets and concurrency must be finite and positive')
        if any(type(config[key]) is not int for key in ('maxJobs', 'maxMutations')):
            raise ValueError('Concurrency limits must be integers')
        if not math.isfinite(config['swapGiB']) or config['swapGiB'] < 0:
            raise ValueError('Swap budget must be finite and nonnegative')
        if not (config['memoryHighGiB'] <= config['memoryMaxGiB']
                and config['admissionGiB'] < config['memoryMaxGiB']
                and config['maxMutations'] <= config['maxJobs']):
            raise ValueError('Inconsistent admission/kernel limits')
        if any(config['sharedReserveGiB'] + size > config['admissionGiB']
               for size in config['profiles'].values()):
            raise ValueError('A job profile cannot fit alongside the shared pool')

    @contextmanager
    def locked(self):
        with (self.directory / 'admission.lock').open('a') as lock:
            fcntl.flock(lock, fcntl.LOCK_EX)
            fresh = read(self.path)
            self.validate(fresh)
            # A live policy may change budgets, but never the environment it owns.
            for key in ('root', 'slice', 'daemonUnit', 'cgroup', 'turbo', 'cachePrefix'):
                if fresh[key] != self.config[key]:
                    raise RuntimeError(f'Cannot change live runner identity: {key}')
            self.config = fresh
            yield

    def verify_limits(self):
        for filename, key in [('memory.high', 'memoryHighGiB'), ('memory.max', 'memoryMaxGiB'),
                              ('memory.swap.max', 'swapGiB')]:
            if int((self.group / filename).read_text()) != int(self.config[key] * GIB):
                raise RuntimeError(f'Kernel/config mismatch: {filename}; run start to apply policy')

    def metrics(self):
        usage = dict((key, int(value)) for key, value in
                     (line.split() for line in (self.group / 'memory.stat').read_text().splitlines()))
        mem = dict(line.split(':', 1) for line in Path('/proc/meminfo').read_text().splitlines())
        pressures = []
        for path in [self.group / 'memory.pressure', Path('/proc/pressure/memory')]:
            fields = dict(item.split('=') for item in path.read_text().splitlines()[0].split()[1:])
            pressures.extend(float(fields[key]) for key in ('avg10', 'avg60'))
        return {'availableGiB': int(mem['MemAvailable'].split()[0]) / 2 ** 20,
                # Conservative: mapped shared pages can overlap shmem. Reservations
                # remain independent of this sampled estimate and are never shrunk.
                'workingGiB': sum(usage.get(key, 0) for key in
                                  ('anon', 'kernel', 'shmem', 'file_mapped')) / GIB,
                'pressurePct': max(pressures),
                'events': dict((k, int(v)) for k, v in (line.split() for line in
                               (self.group / 'memory.events').read_text().splitlines()))}

    def properties(self, unit):
        result = subprocess.run(['systemctl', '--user', 'show', unit,
                                 '-p', 'ActiveState', '-p', 'MainPID', '-p', 'Result', '-p', 'LoadState'],
                                capture_output=True, text=True, timeout=15)
        props = dict(line.split('=', 1) for line in result.stdout.splitlines() if '=' in line)
        if result.returncode and props.get('LoadState') != 'not-found':
            raise RuntimeError('Cannot inspect user service: ' + result.stderr)
        return props

    def ready(self):
        props = self.properties(self.config['daemonUnit'])
        try:
            status = read(self.directory / 'daemon-status.json')
        except (FileNotFoundError, json.JSONDecodeError):
            return False
        pid = props.get('MainPID', '0')
        live = process(pid) if pid != '0' else None
        return bool(props.get('ActiveState') == 'active' and live
                    and status.get('status') == 'ready' and status.get('pid') == int(pid)
                    and status.get('start') == live['start']
                    and live['group'] == self.config['cgroup'] + '/' + self.config['daemonUnit'])

    def wait_ready(self, timeout=300):
        deadline = time.monotonic() + timeout
        while not self.ready():
            if time.monotonic() >= deadline:
                raise TimeoutError('Dedicated daemon did not become ready; no test launched')
            time.sleep(0.5)

    def active_jobs(self):
        active = []
        for path in (self.directory / 'jobs').glob('*/admission.json'):
            row = read(path)
            group = self.group / row['unit']
            populated = group.exists() and 'populated 1' in (group / 'cgroup.events').read_text()
            live = process(row['launcherPid'])
            alive = live and live['start'] == row['launcherStart'] and not row.get('finished')
            # Finished bookkeeping cannot release memory still owned by a live unit.
            if alive or populated:
                active.append(row)
        return active

    def older_exclusive_waiter(self, row):
        for path in (self.directory / 'jobs').glob('*/request.json'):
            if (path.parent / 'admission.json').exists():
                continue
            other = read(path)
            if other['kind'] not in EXCLUSIVE or other['createdAt'] >= row['createdAt']:
                continue
            live = process(other['launcherPid'])
            if live and live['start'] == other['launcherStart']:
                return True
        return False

    def environment(self, inherited):
        # Persist only tool configuration in the request, not ambient credentials.
        keys = ('HOME', 'PATH', 'PYTHONPATH', 'TMPDIR', 'TURBO_LEAN_HOME',
                'TURBO_LEAN_MAX_MEMORY_MB', 'TURBO_LEAN_WORKER_RSS_LIMIT_MB',
                'TURBO_LEAN_MAX_TOTAL_ZYGOTE_RSS_MB', 'LEAN_NUM_THREADS', 'LEAN_STACK_SIZE_KB',
                'RAYON_NUM_THREADS', 'FOUNDRY_THREADS', 'FOUNDRY_PROFILE', 'FOUNDRY_SOLC',
                'FOUNDRY_MEMORY_LIMIT', 'DIFFTEST_RANDOM_SEED', 'DIFFTEST_RANDOM_SMALL',
                'DIFFTEST_RANDOM_LARGE', 'DIFFTEST_SHARD_COUNT', 'DIFFTEST_SHARD_INDEX',
                'DIFFTEST_YUL_DIR', 'VERITY_MUTANT_BUILD_TIMEOUT')
        env = {key: inherited[key] for key in keys if key in inherited}
        # Do not inject the small differential cap into stock Foundry stress tests.
        # Explicit caller overrides are retained; foundry.toml governs by default.
        env['PATH'] = str(self.directory / 'bin') + os.pathsep + env.get('PATH', os.defpath)
        env['PYTHONPATH'] = str(Path(self.config['root']) / 'scripts') + os.pathsep + env.get('PYTHONPATH', '')
        env.setdefault('LEAN_NUM_THREADS', '1')
        env.setdefault('PYTHONUNBUFFERED', '1')
        return env

    def reconcile_pool(self):
        """Under the admission lock, adopt only this runner's private server and descendants."""
        target = self.group / self.config['daemonUnit']
        if self.properties(self.config['daemonUnit']).get('ActiveState') != 'active':
            raise RuntimeError('Pool owner is not active')
        rows = {p['pid']: p for path in Path('/proc').glob('[0-9]*')
                if (p := process(path.name))}
        servers = [p for p in rows.values() if self.owns_server(p)]
        moved = []
        target_group = self.config['cgroup'] + '/' + self.config['daemonUnit']
        for server in servers:
            selected = {server['pid']}
            while True:
                children = {p['pid'] for p in rows.values() if p['ppid'] in selected}
                if children <= selected:
                    break
                selected |= children
            for pid in [server['pid'], *sorted(selected - {server['pid']})]:
                current = process(pid)
                if current is None:
                    continue
                if current['start'] != rows[pid]['start']:
                    raise RuntimeError('PID reused during pool ownership transfer')
                if current['group'] == target_group:
                    continue
                unit = current['group'].removeprefix(self.config['cgroup'] + '/')
                prefix = self.config['slice'].removesuffix('.slice') + '-job-'
                if not unit.startswith(prefix) or '/' in unit:
                    raise RuntimeError('Refusing to move a worker outside this runner')
                (target / 'cgroup.procs').write_text(str(pid))
                after = process(pid)
                if after and (after['start'] != current['start'] or after['group'] != target_group):
                    raise RuntimeError('Worker ownership transfer failed')
                moved.append(pid)
        return moved

    def owns_server(self, row):
        args = row['args']
        return (len(args) == 6 and args[0] == self.config['turbo']
                and args[1] == '--cache-dir' and args[2].startswith(self.config['cachePrefix'])
                and args[3:5] == ['serve', '--listen'] and args[5].startswith('127.0.0.1:')
                and in_group(row['group'], self.config['cgroup']))
