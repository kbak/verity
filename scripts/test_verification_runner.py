"""Regression tests for the local runner; no Lean build or full campaign required."""
import contextlib
import copy
import io
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
from types import SimpleNamespace
import unittest
import uuid
from unittest.mock import patch

import run_verification as runner
from verification_runner import artifacts, commands
from verification_runner.runtime import GIB, Runtime, can_admit, process, read, write


def config(root):
    return {'root': str(root), 'cgroup': '/user.slice/test.slice', 'slice': 'test.slice',
            'daemonUnit': 'test-daemon.service', 'turbo': str(root / 'private/turbo-lean'),
            'lake': str(root / 'lake'), 'cachePrefix': '/dev/shm/test/zygote_',
            'memoryHighGiB': 26, 'memoryMaxGiB': 28, 'swapGiB': 2,
            'hostReserveGiB': 4, 'sharedReserveGiB': 10, 'admissionGiB': 27,
            'maxJobs': 8, 'maxMutations': 5, 'maxPressurePct': 8,
            'profiles': {'light': 0.5, 'mutation': 3.25, 'build': 12, 'foundry': 6}}


def headroom(**changes):
    return dict({'availableGiB': 24, 'workingGiB': 12, 'pressurePct': 0, 'events': {}}, **changes)


class RuntimeTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.path = self.root / 'runner/config.json'
        write(self.path, config(self.root))
        self.runtime = Runtime(self.path)
        self.runtime.group = self.root / 'cgroup'
        self.runtime.group.mkdir()
        self.limits(26, 28)

    def limits(self, soft, hard):
        for filename, value in [('memory.high', soft), ('memory.max', hard), ('memory.swap.max', 2)]:
            (self.runtime.group / filename).write_text(str(int(value * GIB)))

    def test_daemon_reloads_updated_limits_under_lock(self):
        newer = dict(self.runtime.config, memoryHighGiB=28, memoryMaxGiB=30, admissionGiB=28)
        write(self.path, newer)
        self.limits(28, 30)
        with self.assertRaisesRegex(RuntimeError, 'mismatch'):
            self.runtime.verify_limits()
        with self.runtime.locked():
            self.runtime.verify_limits()
            self.assertEqual(self.runtime.config, newer)

    def test_live_identity_cannot_change_with_policy(self):
        write(self.path, dict(self.runtime.config, root=str(self.root / 'other')))
        with self.assertRaisesRegex(RuntimeError, 'identity'):
            with self.runtime.locked():
                pass

    def test_readiness_requires_live_pid_start_and_owner_group(self):
        status = {'status': 'ready', 'pid': 42, 'start': '101'}
        write(self.path.parent / 'daemon-status.json', status)
        live = {'start': '101', 'group': '/user.slice/test.slice/test-daemon.service'}
        with patch.object(self.runtime, 'properties', return_value={'ActiveState': 'active', 'MainPID': '42'}), \
                patch('verification_runner.runtime.process', return_value=live):
            self.assertTrue(self.runtime.ready())
            for change in ({'pid': 41}, {'start': '100'}, {'status': 'starting'}):
                write(self.path.parent / 'daemon-status.json', dict(status, **change))
                self.assertFalse(self.runtime.ready())
            write(self.path.parent / 'daemon-status.json', status)
            live['group'] = '/unrelated.service'
            self.assertFalse(self.runtime.ready())

    def test_missing_or_malformed_readiness_is_not_success(self):
        with patch.object(self.runtime, 'properties', return_value={'ActiveState': 'inactive', 'MainPID': '0'}):
            self.assertFalse(self.runtime.ready())
            (self.path.parent / 'daemon-status.json').write_text('{')
            self.assertFalse(self.runtime.ready())

    def test_readiness_wait_is_bounded(self):
        with patch.object(self.runtime, 'ready', return_value=False), \
                patch('verification_runner.runtime.time.sleep'):
            with self.assertRaisesRegex(TimeoutError, 'no test launched'):
                self.runtime.wait_ready(timeout=0)

    def test_absent_service_is_distinct_from_bus_failure(self):
        with patch('verification_runner.runtime.subprocess.run', return_value=
                   SimpleNamespace(returncode=1, stdout='LoadState=not-found\n', stderr='')):
            self.assertEqual(self.runtime.properties('absent')['LoadState'], 'not-found')
        with patch('verification_runner.runtime.subprocess.run', return_value=
                   SimpleNamespace(returncode=1, stdout='', stderr='Failed to connect to bus')):
            with self.assertRaisesRegex(RuntimeError, 'Cannot inspect'):
                self.runtime.properties('absent')

    def test_shared_pool_has_its_own_reservation(self):
        c = self.runtime.config
        active = [{'kind': 'mutation', 'reservedGiB': 3.25} for _ in range(4)]
        self.assertTrue(can_admit(c, 'mutation', active, headroom()))
        active.append({'kind': 'mutation', 'reservedGiB': 3.25})
        self.assertFalse(can_admit(dict(c, maxMutations=8), 'mutation', active, headroom()))
        # Lowering a profile never rewrites already admitted reservations.
        lowered = dict(c, profiles=dict(c['profiles'], mutation=2))
        self.assertFalse(can_admit(dict(lowered, maxMutations=8), 'mutation', active, headroom()))
        for row in active:
            row['sharedReserveGiB'] = 10
        self.assertFalse(can_admit(dict(c, sharedReserveGiB=2, maxMutations=8),
                                  'mutation', active, headroom()))

    def test_host_growth_pressure_oom_and_exclusivity_block_admission(self):
        for measurement in [headroom(availableGiB=5), headroom(pressurePct=8),
                            headroom(events={'oom_kill': 1}), headroom(events={'max': 1}),
                            headroom(workingGiB=26)]:
            self.assertFalse(can_admit(self.runtime.config, 'mutation', [], measurement))
        active = [{'kind': 'mutation', 'reservedGiB': 3.25}]
        self.assertFalse(can_admit(self.runtime.config, 'build', active, headroom()))
        self.assertFalse(can_admit(self.runtime.config, 'mutation',
                                  [{'kind': 'build', 'reservedGiB': 12}], headroom()))

    def test_live_cgroup_retains_reservation_after_launcher_exits(self):
        row = {'unit': 'job.service', 'kind': 'mutation', 'reservedGiB': 3.25,
               'launcherPid': 1, 'launcherStart': '1', 'finished': 10}
        write(self.path.parent / 'jobs/test/admission.json', row)
        group = self.runtime.group / row['unit']; group.mkdir()
        (group / 'cgroup.events').write_text('populated 1\n')
        with patch('verification_runner.runtime.process', return_value=None):
            self.assertEqual(self.runtime.active_jobs(), [row])
            (group / 'cgroup.events').write_text('populated 0\n')
            self.assertEqual(self.runtime.active_jobs(), [])

    def test_environment_preserves_stock_foundry_and_explicit_overrides(self):
        env = self.runtime.environment({'PATH': '/bin', 'TOKEN': 'not-a-tool-setting',
                                        'DIFFTEST_RANDOM_SEED': '42'})
        self.assertNotIn('FOUNDRY_MEMORY_LIMIT', env)
        self.assertNotIn('TOKEN', env)
        self.assertEqual(env['DIFFTEST_RANDOM_SEED'], '42')
        self.assertEqual(self.runtime.environment({'FOUNDRY_MEMORY_LIMIT': '4294967296'})[
                         'FOUNDRY_MEMORY_LIMIT'], '4294967296')

    def test_server_matching_excludes_other_runner_and_sibling_slice(self):
        row = {'args': [self.runtime.config['turbo'], '--cache-dir', '/dev/shm/test/zygote_1',
                        'serve', '--listen', '127.0.0.1:123'], 'group': '/user.slice/test.slice/job'}
        self.assertTrue(self.runtime.owns_server(row))
        for group in ['/user.slice/test.slice-other/job', '/unrelated/job']:
            self.assertFalse(self.runtime.owns_server(dict(row, group=group)))
        other = copy.deepcopy(row); other['args'][0] = '/another/turbo-lean'
        self.assertFalse(self.runtime.owns_server(other))

    def test_pool_moves_server_before_children_and_rejects_pid_reuse(self):
        group = self.runtime.config['cgroup']
        server = {'pid': 10, 'ppid': 1, 'start': '100', 'group': group + '/test-job-x.service',
                  'args': [self.runtime.config['turbo'], '--cache-dir', '/dev/shm/test/zygote_1',
                           'serve', '--listen', '127.0.0.1:123']}
        child = dict(server, pid=11, ppid=10, start='200', args=['worker'])
        original = Path.glob
        def glob(path, pattern):
            return [Path('/proc/10'), Path('/proc/11')] if path == Path('/proc') else original(path, pattern)
        target = self.runtime.group / self.runtime.config['daemonUnit']; target.mkdir()
        moved_server = dict(server, group=group + '/test-daemon.service')
        moved_child = dict(child, group=group + '/test-daemon.service')
        with patch.object(self.runtime, 'properties', return_value={'ActiveState': 'active'}), \
                patch.object(Path, 'glob', glob), \
                patch('verification_runner.runtime.process', side_effect=[server, child, server,
                       moved_server, child, moved_child]):
            self.assertEqual(self.runtime.reconcile_pool(), [10, 11])
            self.assertEqual((target / 'cgroup.procs').read_text(), '11')
        with patch.object(self.runtime, 'properties', return_value={'ActiveState': 'active'}), \
                patch.object(Path, 'glob', glob), \
                patch('verification_runner.runtime.process', side_effect=[server, child,
                       dict(server, start='reused')]):
            with self.assertRaisesRegex(RuntimeError, 'PID reused'):
                self.runtime.reconcile_pool()

    def test_failed_launch_and_retry_preserve_separate_evidence(self):
        args = SimpleNamespace(name='example', kind='foundry', timeout=100, queue_timeout=1)
        command = ['forge', 'test', '--match-test', 'Random', '--fuzz-seed', '42']
        with patch.object(self.runtime, 'verify_limits'), patch.object(self.runtime, 'ready', return_value=True), \
                patch.object(self.runtime, 'active_jobs', return_value=[]), \
                patch.object(self.runtime, 'metrics', return_value=headroom()), \
                patch.object(self.runtime, 'older_exclusive_waiter', return_value=False), \
                patch('run_verification.process', return_value={'pid': 1, 'start': '100'}), \
                patch('run_verification.subprocess.run', return_value=SimpleNamespace(returncode=7, stderr='launch failed')), \
                contextlib.redirect_stderr(io.StringIO()):
            self.assertEqual(runner.run(self.runtime, args, command), 7)
            self.assertEqual(runner.run(self.runtime, args, command), 7)
        jobs = list((self.path.parent / 'jobs').iterdir())
        self.assertEqual(len(jobs), 2)
        for job in jobs:
            self.assertEqual(read(job / 'request.json')['command'], command)
            self.assertEqual(read(job / 'status.json')['status'], 'failed')
            self.assertIn('finished', read(job / 'admission.json'))

    def test_not_ready_never_launches_test(self):
        args = SimpleNamespace(name='example', kind='mutation', timeout=100, queue_timeout=0)
        with patch.object(self.runtime, 'verify_limits'), patch.object(self.runtime, 'ready', return_value=False), \
                patch('run_verification.process', return_value={'pid': 1, 'start': '100'}), \
                patch('run_verification.subprocess.run') as launch, contextlib.redirect_stderr(io.StringIO()):
            with self.assertRaises(TimeoutError):
                runner.run(self.runtime, args, ['false'])
            launch.assert_not_called()
        job = next((self.path.parent / 'jobs').iterdir())
        self.assertFalse(read(job / 'status.json')['testLaunched'])

    def test_nested_parallelism_is_rejected(self):
        for argv in [['test', '--jobs', 'auto'], ['test', '--jobs=4']]:
            with self.assertRaises(ValueError):
                runner.validate_command(argv)
        runner.validate_command(['test', '--jobs', '1'])


class CommandTests(unittest.TestCase):
    def test_supplemental_outputs_follow_tested_checkout_and_keep_flags(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary) / 'frozen'; root.mkdir()
            for name, flags in commands.SUPPLEMENTAL.items():
                argv = commands.supplemental_command(root, name, 'attempt-2', sys.executable)
                self.assertEqual(argv[3:-2], ['--prepared', *flags])
                self.assertTrue(Path(argv[-1]).is_relative_to(root / '.lake'))
            output = Path(argv[-1]); output.mkdir(parents=True)
            with self.assertRaises(FileExistsError):
                commands.supplemental_command(root, name, 'attempt-2', sys.executable)
            with self.assertRaises(ValueError):
                commands.supplemental_command(root, name, '../../outside', sys.executable)

    def test_eval_errors_cannot_be_reported_as_success(self):
        for payload in ['bad json', '[]', '{"ok":false}', '{"ok":true,"errors":["bad"]}',
                        '{"ok":true,"timed_out":true}', '{"ok":true,"crashed":true}']:
            with self.subTest(payload=payload), contextlib.redirect_stderr(io.StringIO()):
                self.assertNotEqual(commands.eval_result(SimpleNamespace(
                    stdout=payload, stderr='', returncode=0)), 0)
        out = io.StringIO()
        with contextlib.redirect_stdout(out), contextlib.redirect_stderr(io.StringIO()):
            self.assertEqual(commands.eval_result(SimpleNamespace(
                stdout='{"ok":true,"stdout":"hello","messages":["done"]}',
                stderr='', returncode=0)), 0)
        self.assertEqual(out.getvalue(), 'hello\ndone\n')

    def test_run_adapter_preserves_unicode_quotes_and_nonzero_exit_handling(self):
        generated = commands.main_driver('def main : IO UInt32 := pure 4', ['é', '"', '\n'])
        self.assertIn('unless code == 0', generated)
        self.assertIn('["é", "\\\"", "\\n"]', generated)
        for entrypoint in ['IO Unit', 'IO UInt32', 'List String → IO Unit', 'List String → IO UInt32']:
            self.assertIn('Entrypoint (' + entrypoint + ')', generated)


class ArtifactTests(unittest.TestCase):
    def test_cas_link_churn_does_not_change_private_identity_after_capture(self):
        from solidity_differential.identity import ImplementationIdentity
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary); project = root / 'snapshot'
            lib = project / '.lake/build/lib'; lib.mkdir(parents=True)
            (project / '.lake' / artifacts.MARKER).touch()
            cas = root / 'cas.olean'; cas.write_bytes(b'compiled artifact')
            private = lib / 'Module.olean'; os.link(cas, private)
            before = private.stat()
            artifacts.isolate_private_build(project)
            saved = ImplementationIdentity._stat(private)
            self.assertEqual(private.read_bytes(), cas.read_bytes())
            self.assertEqual(private.stat().st_mtime_ns, before.st_mtime_ns)
            self.assertNotEqual(private.stat().st_ino, cas.stat().st_ino)
            os.link(cas, root / 'other.olean')
            self.assertEqual(ImplementationIdentity._stat(private), saved)
            # Strict metadata checks still detect modifications to the private artifact.
            private.write_bytes(b'changed artifact!')
            self.assertNotEqual(ImplementationIdentity._stat(private), saved)
            self.assertEqual(cas.read_bytes(), b'compiled artifact')

    def test_parent_and_shared_package_caches_are_not_detached(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary); (root / '.lake/build/lib').mkdir(parents=True)
            artifact = root / '.lake/build/lib/M.olean'; artifact.write_text('data')
            os.link(artifact, root / 'cas')
            before = artifact.stat().st_ino
            self.assertEqual(artifacts.isolate_private_build(root), 0)
            self.assertEqual(artifact.stat().st_ino, before)

    def test_private_build_symlink_escape_is_rejected(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary); project = root / 'private'; project.mkdir()
            (project / '.lake').mkdir(); (project / '.lake' / artifacts.MARKER).touch()
            (root / 'external/lib').mkdir(parents=True)
            (project / '.lake/build').symlink_to(root / 'external', target_is_directory=True)
            with self.assertRaisesRegex(RuntimeError, 'outside'):
                artifacts.isolate_private_build(project)

    def test_failed_copy_preserves_original_hardlink_and_cleans_temporary(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary); original = root / 'M.olean'
            original.write_bytes(b'correct'); os.link(original, root / 'cas')
            before = original.stat().st_ino
            with patch('verification_runner.artifacts.shutil.copyfileobj',
                       side_effect=lambda source, target: target.write(b'incorrect')):
                with self.assertRaisesRegex(RuntimeError, 'changed while copying'):
                    artifacts.detach(original)
            self.assertEqual(original.read_bytes(), b'correct')
            self.assertEqual(original.stat().st_ino, before)
            self.assertEqual(list(root.glob('.private-artifact-*')), [])

    def test_identity_capture_calls_isolation_before_stat_inventory(self):
        from solidity_differential.identity import ImplementationIdentity
        events = []
        with patch('solidity_differential.identity.isolate_private_build',
                   side_effect=lambda _: events.append('isolate')), \
                patch('solidity_differential.identity.command', return_value='/toolchain'), \
                patch.object(ImplementationIdentity, '_inventory',
                             side_effect=lambda: events.append('inventory') or []), \
                patch.object(ImplementationIdentity, 'verify'):
            ImplementationIdentity('Driver.lean')
        self.assertEqual(events, ['isolate', 'inventory'])


@unittest.skipUnless(os.environ.get('VERITY_RUNNER_INTEGRATION_TURBO'),
                     'Set VERITY_RUNNER_INTEGRATION_TURBO for the bounded systemd/Lean smoke test')
class RunnerIntegrationTests(unittest.TestCase):
    def test_real_service_and_all_warm_entrypoints(self):
        root = Path(__file__).resolve().parents[1]
        directory = root / '.lake/runner-integration' / uuid.uuid4().hex
        config_path = directory / 'config.json'
        parent = subprocess.check_output(['systemctl', '--user', 'show',
                    '--property=ControlGroup', '--value', '--', '-.slice'], text=True).strip()
        group = parent + '/verityrunnercheck' + uuid.uuid4().hex[:8] + '.slice'
        cli = [sys.executable, str(root / 'scripts/run_verification.py'), '--config', str(config_path)]
        def call(*args, timeout=360):
            return subprocess.run([*cli, *args], cwd=root, capture_output=True, text=True, timeout=timeout)
        result = call('init', '--root', str(root), '--cgroup', group,
                      '--turbo', os.environ['VERITY_RUNNER_INTEGRATION_TURBO'])
        self.assertEqual(result.returncode, 0, result.stderr)
        settings = read(config_path)
        settings.update(memoryHighGiB=3, memoryMaxGiB=4, admissionGiB=3.5,
                        sharedReserveGiB=2, maxJobs=1, maxMutations=1, profiles={'light': 0.5})
        write(config_path, settings)
        try:
            result = call('start')
            self.assertEqual(result.returncode, 0, result.stderr)
            runtime = Runtime(config_path)
            before = read(directory / 'daemon-status.json')
            cases = {
                'unit': ('def main : IO Unit := IO.println "unit passed"', [], True),
                'code': ('def main : IO UInt32 := pure 0', [], True),
                'args-unit': ('def main (args : List String) : IO Unit := do\n'
                              '  unless args == ["é", "a\\\"b"] do throw (IO.userError "args")',
                              ['é', 'a"b'], True),
                'args-code': ('def main (args : List String) : IO UInt32 :=\n'
                              '  pure (if args == ["x"] then 0 else 7)', ['x'], True),
                'unit-error': ('def main : IO Unit := throw (IO.userError "expected")', [], False),
                'code-error': ('def main : IO UInt32 := pure 7', [], False),
                'args-unit-error': ('def main (_ : List String) : IO Unit :=\n'
                                    '  throw (IO.userError "expected")', [], False),
                'args-code-error': ('def main (_ : List String) : IO UInt32 := pure 9', [], False),
                'invalid': ('def main : Nat := 0', [], False),
            }
            for name, (source, arguments, expected) in cases.items():
                with self.subTest(name=name):
                    driver = directory / (name + '.lean'); driver.write_text(source + '\n')
                    result = call('run', '--kind', 'light', '--name', name, '--timeout', '120',
                                  '--queue-timeout', '30', '--', 'lake', 'env', 'lean', '--run',
                                  str(driver), *arguments)
                    self.assertEqual(result.returncode == 0, expected, result.stdout + result.stderr)
            after = read(directory / 'daemon-status.json')
            self.assertEqual((before['pid'], before['start']), (after['pid'], after['start']))
            self.assertTrue(runtime.ready())
            self.assertFalse(runtime.active_jobs())
        finally:
            result = call('stop')
            self.assertEqual(result.returncode, 0, result.stderr)


if __name__ == '__main__':
    unittest.main()
