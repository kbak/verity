"""Regression checks for fork routing and artifact fallback admission."""
from __future__ import annotations

import json
import re
import unittest
from pathlib import Path

import check_verify_sync as check
from verify_sync_spec_source import build_spec

ROOT = Path(__file__).resolve().parents[1]


class ForkHostedCiTests(unittest.TestCase):
    def test_runner_contract_accepts_configuration_and_rejects_wrong_routes(self):
        snapshot = check.Snapshot.load()
        self.assertEqual(check.check_job_contracts(snapshot, build_spec()).errors, [])
        for before, after in (
            ("github.repository == 'kbak/verity'", "github.repository == 'lfglabs-dev/verity'"),
            ('["ubuntu-24.04"]', '["self-hosted"]'),
            ('"build-heavy"', '"build-medium"'),
        ):
            with self.subTest(after=after):
                text = snapshot.workflow_text.replace(before, after)
                changed = check.Snapshot(text, text.splitlines(), snapshot.jobs)
                self.assertTrue(check.check_job_contracts(changed, build_spec()).errors)

    def test_all_verification_jobs_route_the_fork_to_hosted_ubuntu(self):
        for filename in ("verify.yml", "turbo-lean-cache.yml"):
            text = (ROOT / ".github/workflows" / filename).read_text()
            routes = re.findall(r"^    runs-on: (.*)$", text, re.M)
            self.assertTrue(routes)
            for route in routes:
                match = re.fullmatch(
                    r"\$\{\{ fromJSON\(github.repository == 'kbak/verity' && '(.*?)' ",
                    route.split("||")[0].rstrip() + " ",
                )
                self.assertIsNotNone(match, route)
                self.assertEqual(json.loads(match[1]), ["ubuntu-24.04"])
                self.assertIn('"self-hosted"', route.split("||")[1])

    def test_local_restores_are_skipped_and_artifact_fallbacks_remain(self):
        snapshot = check.Snapshot.load()
        for job in snapshot.jobs:
            body = snapshot.job_body(job)
            for step in re.split(r"(?=^      - )", body, flags=re.M):
                if 'ci_local_persistence.sh' in step or 'source_dir="${VERIFY_LOCAL_ARTIFACT_ROOT}' in step:
                    self.assertTrue(
                        "if: github.repository != 'kbak/verity'" in step
                        or "if: env.VERIFY_USE_STICKY_DISKS == 'true'" in step,
                        (job, step),
                    )
                if "id: local-restore-" in step:
                    step_id = re.search(r"id: (local-restore-[\w-]+)", step)[1]
                    self.assertIn(f"if: steps.{step_id}.outcome != 'success'", body)
                    self.assertIn("uses: actions/download-artifact@", body)
        self.assertIn(
            "VERIFY_USE_STICKY_DISKS: ${{ (github.repository == 'kbak/verity' ||",
            snapshot.workflow_text,
        )

    def test_ocr_is_explicitly_skipped_and_checks_do_not_rewrite_fork_heads(self):
        text = (ROOT / ".github/workflows/ocr-review.yml").read_text()
        self.assertIn("github.repository != 'kbak/verity' && (", text)
        body = check.Snapshot.load().job_body("checks")
        self.assertIn("github.event.pull_request.head.sha", body)
        for name in ("Regenerate derived artifacts", "Auto-commit refreshed artifacts"):
            step = next(s for s in re.split(r"(?=^      - )", body, flags=re.M) if f"name: {name}" in s)
            self.assertIn("if: github.repository != 'kbak/verity'", step)


if __name__ == "__main__":
    unittest.main()
