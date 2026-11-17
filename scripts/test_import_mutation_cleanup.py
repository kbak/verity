"""Exercise mutation workspace ownership without running Lean campaigns."""
import contextlib
import io
import tempfile
import threading
import unittest
from pathlib import Path
from unittest.mock import patch

import solidity_import_mutations as mutations


class MutationCleanupTests(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name)
        work = patch.object(mutations, "WORK", self.root)
        work.start()
        self.addCleanup(work.stop)

    def run_tasks(self, tasks, *flags):
        output = io.StringIO()
        with (
            patch.object(mutations, "tasks", return_value=tasks),
            patch.object(mutations, "setup"),
            patch("sys.argv", ["mutations", *flags]),
            contextlib.redirect_stdout(output), contextlib.redirect_stderr(output),
        ):
            mutations.main()
        return output.getvalue()

    def test_success_removes_only_its_own_snapshot(self):
        retained = self.root / "retained-from-an-earlier-run"
        retained.mkdir()
        (retained / "evidence.json").write_text("keep")
        used = []

        def task():
            used.append(mutations.work_dir())
            (used[-1] / "large-generated-build").write_bytes(b"artifact")

        self.run_tasks([("example", 1, task)])
        self.assertFalse(used[0].exists())
        self.assertEqual((retained / "evidence.json").read_text(), "keep")
        self.assertEqual(mutations.work_dir(), self.root)

    def test_retry_cleans_failure_before_creating_fresh_snapshot(self):
        used = []

        def task():
            if used:
                self.assertFalse(used[-1].exists())
            used.append(mutations.work_dir())
            (used[-1] / "partial-build").write_bytes(b"artifact")
            if len(used) == 1:
                raise RuntimeError("retry this failure")

        self.run_tasks([("example", 1, task)])
        self.assertEqual(len(set(used)), 2)
        self.assertTrue(all(not p.exists() for p in used))

    def test_final_failure_cleans_both_attempts_and_remains_a_failure(self):
        used = []

        def task():
            used.append(mutations.work_dir())
            (used[-1] / "partial-build").write_bytes(b"artifact")
            raise SystemExit("mutation escaped detection")

        with self.assertRaisesRegex(SystemExit, "failed: example"):
            self.run_tasks([("example", 1, task)])
        self.assertEqual(len(used), 2)
        self.assertTrue(all(not p.exists() for p in used))

    def test_keep_workspaces_retains_and_reports_snapshots(self):
        used = []

        def task():
            used.append(mutations.work_dir())
            (used[-1] / "evidence.json").write_text("debug")

        output = self.run_tasks([("example", 1, task)], "--keep-workspaces")
        self.assertEqual((used[0] / "evidence.json").read_text(), "debug")
        self.assertIn(str(used[0]), output)
        self.assertEqual(mutations.work_dir(), self.root)

    def test_parallel_tasks_have_independent_workspaces(self):
        barrier = threading.Barrier(2)
        used = []

        def task():
            directory = mutations.work_dir()
            used.append(directory)
            (directory / "same-filename").write_text(str(directory))
            barrier.wait(timeout=5)
            self.assertEqual(mutations.work_dir(), directory)
            self.assertEqual((directory / "same-filename").read_text(), str(directory))

        self.run_tasks([("first", 1, task), ("second", 1, task)], "--jobs", "2")
        self.assertEqual(len(set(used)), 2)
        self.assertTrue(all(not p.exists() for p in used))

    def test_keyboard_interrupt_cleans_snapshot_without_retry(self):
        used = []

        def task():
            used.append(mutations.work_dir())
            (used[-1] / "partial-build").write_bytes(b"artifact")
            raise KeyboardInterrupt()

        with self.assertRaises(KeyboardInterrupt):
            self.run_tasks([("example", 1, task)])
        self.assertEqual(len(used), 1)
        self.assertFalse(used[0].exists())

    def test_list_does_not_create_snapshots_or_prepare_builds(self):
        with (
            patch.object(mutations, "tasks", return_value=[("example", 1, lambda: None)]),
            patch.object(mutations, "setup") as setup,
            patch("sys.argv", ["mutations", "--list"]),
            contextlib.redirect_stdout(io.StringIO()) as output,
        ):
            mutations.main()
        setup.assert_not_called()
        self.assertEqual(output.getvalue().strip(), "example")
        self.assertEqual(list(self.root.iterdir()), [])


if __name__ == "__main__":
    unittest.main()
