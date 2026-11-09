"""Exercise cache admission with complete, partial, and broken tool installs."""
from pathlib import Path
import subprocess
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
CHECK = ROOT / "scripts/check_foundry_installation.sh"


class FoundryInstallationTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.bin = Path(self.temp.name) / "bin"
        self.bin.mkdir()
        for tool in ("forge", "cast", "anvil"):
            self.write_tool(tool)

    def write_tool(self, tool, version="1.5.0-v1.5.0", exit_code=0):
        target = self.bin / tool
        target.write_text(f"#!/bin/sh\necho '{tool} Version: {version}'\nexit {exit_code}\n")
        target.chmod(0o755)

    def valid(self):
        return subprocess.run(["bash", str(CHECK), str(self.bin)], capture_output=True).returncode == 0

    def test_complete_install(self):
        self.assertTrue(self.valid())

    def test_missing_cast_is_incomplete(self):
        (self.bin / "cast").unlink()
        self.assertFalse(self.valid())

    def test_foundryup_symlink_requires_cached_target(self):
        versions = self.bin.parent / "versions/1.5.0"
        versions.mkdir(parents=True)
        for tool in ("forge", "cast", "anvil"):
            target = versions / tool
            (self.bin / tool).rename(target)
            (self.bin / tool).symlink_to(target)
        self.assertTrue(self.valid())
        (versions / "forge").unlink()
        self.assertFalse(self.valid())

    def test_wrong_version_is_rejected(self):
        for version in ("1.5.01", "1.6.0", "1.5.0rc1"):
            with self.subTest(version=version):
                self.write_tool("forge", version)
                self.assertFalse(self.valid())

    def test_non_executable_is_rejected(self):
        (self.bin / "anvil").chmod(0o644)
        self.assertFalse(self.valid())

    def test_crashing_binary_is_rejected(self):
        self.write_tool("forge", exit_code=1)
        self.assertFalse(self.valid())

    def test_cache_hit_does_not_bypass_validation(self):
        workflow = (ROOT / ".github/actions/setup-foundry/action.yml").read_text()
        self.assertIn("~/.foundry/versions", workflow)
        self.assertIn("if: steps.restored-foundry.outputs.installed != 'true'", workflow)
        self.assertIn("if: steps.installed-foundry.outputs.installed != 'true'", workflow)
        self.assertNotIn("steps.cache-foundry.outputs.cache-hit", workflow)


if __name__ == "__main__":
    unittest.main()
