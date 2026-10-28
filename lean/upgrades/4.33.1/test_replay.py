#!/usr/bin/env python3
"""Test exact dependency replay without accessing installed dependencies."""

import hashlib
import json
import shutil
import subprocess
import tempfile
import unittest
from pathlib import Path


class ReplayTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.repo = self.root / "externals/example"
        self.repo.mkdir(parents=True)
        self.bundle = self.root / "bundle"
        self.bundle.mkdir()
        shutil.copyfile(Path(__file__).with_name("replay.py"), self.bundle / "replay.py")
        self.git("init", "-q")
        self.git("config", "user.name", "Fixture")
        self.git("config", "user.email", "fixture@example.invalid")
        self.source = self.repo / "Example.lean"
        self.source.write_text("def example := 1\n")
        self.git("add", "Example.lean")
        self.git("commit", "-qm", "fixture base")
        self.base = self.git("rev-parse", "HEAD").decode().strip()
        self.source.write_text("def example := 2\n")
        patch = self.git("diff", "--binary")
        self.expected = self.source.read_bytes()
        self.git("restore", "Example.lean")
        (self.bundle / "migration.patch").write_bytes(b"")
        (self.bundle / "compatibility.patch").write_bytes(patch)
        self.entry = {
            "base": self.base,
            "patch": "migration.patch",
            "patch_sha256": hashlib.sha256(b"").hexdigest(),
            "files": {"Example.lean": hashlib.sha256(self.source.read_bytes()).hexdigest()},
            "overlay": {
                "base": self.base,
                "patch": "compatibility.patch",
                "patch_sha256": hashlib.sha256(patch).hexdigest(),
                "files": {"Example.lean": hashlib.sha256(self.expected).hexdigest()},
            },
        }
        self.save_manifest()

    def git(self, *args):
        return subprocess.check_output(["git", *args], cwd=self.repo, stderr=subprocess.PIPE)

    def save_manifest(self):
        (self.bundle / "externals.json").write_text(json.dumps({
            "repositories": {"externals/example": self.entry}}))

    def replay(self, mode=None):
        return subprocess.run(["python3", str(self.bundle / "replay.py"),
                               "externals/example", "--lean-root", str(self.root),
                               *([mode] if mode else [])],
                              capture_output=True, text=True)

    def test_prepare_replays_the_overlay_and_verify_checks_its_postimage(self):
        result = self.replay("--prepare")
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(self.source.read_bytes(), self.expected)
        self.assertEqual(self.replay("--verify").returncode, 0)
        self.source.write_text("def example := 3\n")
        self.assertNotEqual(self.replay("--verify").returncode, 0)

    def test_prepare_preserves_existing_work(self):
        self.source.write_text("def example := 4\n")
        before = self.source.read_bytes()
        self.assertNotEqual(self.replay("--prepare").returncode, 0)
        self.assertEqual(self.source.read_bytes(), before)

    def test_prepare_requires_the_published_revision(self):
        self.entry["overlay"]["base"] = "0" * 40
        self.save_manifest()
        before = self.source.read_bytes()
        self.assertNotEqual(self.replay("--prepare").returncode, 0)
        self.assertEqual(self.source.read_bytes(), before)

    def test_overlay_digest_is_checked_before_any_write(self):
        (self.bundle / "compatibility.patch").write_bytes(b"not the recorded patch")
        before = self.source.read_bytes()
        self.assertNotEqual(self.replay("--prepare").returncode, 0)
        self.assertEqual(self.source.read_bytes(), before)

    def test_unpatched_published_sources_do_not_pass_effective_verification(self):
        self.assertNotEqual(self.replay("--verify").returncode, 0)

    def test_legacy_apply_also_replays_an_overlay(self):
        result = self.replay("--apply")
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(self.source.read_bytes(), self.expected)

    def two_stage_profile(self):
        self.source.write_text("def example := 10\n")
        migration = self.git("diff", "--binary")
        self.git("add", "Example.lean")
        self.git("commit", "-qm", "fixture published revision")
        published = self.git("rev-parse", "HEAD").decode().strip()
        baseline = self.source.read_bytes()
        self.source.write_bytes(self.expected)
        overlay = self.git("diff", "--binary")
        self.git("restore", "Example.lean")
        self.git("checkout", "-q", "--detach", self.base)
        (self.bundle / "migration.patch").write_bytes(migration)
        (self.bundle / "compatibility.patch").write_bytes(overlay)
        self.entry["patch_sha256"] = hashlib.sha256(migration).hexdigest()
        self.entry["files"]["Example.lean"] = hashlib.sha256(baseline).hexdigest()
        self.entry["overlay"]["base"] = published
        self.entry["overlay"]["patch_sha256"] = hashlib.sha256(overlay).hexdigest()
        self.save_manifest()

    def test_sequential_dry_run_preserves_worktree_index_and_objects(self):
        self.two_stage_profile()
        before = self.source.read_bytes()
        index = self.git("write-tree")
        objects = self.git("count-objects", "-v")
        result = self.replay()
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(self.source.read_bytes(), before)
        self.assertEqual(self.git("write-tree"), index)
        self.assertEqual(self.git("count-objects", "-v"), objects)

    def test_legacy_migration_then_overlay_reaches_the_recorded_source(self):
        self.two_stage_profile()
        result = self.replay("--apply")
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(self.source.read_bytes(), self.expected)
        self.assertEqual(self.replay("--verify").returncode, 0)

    def required_manifest(self, extra=()):
        project = self.root / "mettapedia"
        project.mkdir(exist_ok=True)
        (project / "lake-manifest.json").write_text(json.dumps({"packages": [
            {"type": "path", "name": "example", "dir": "../externals/example"}, *extra]}))

    def verify_required(self):
        return subprocess.run(["python3", str(self.bundle / "replay.py"),
                               "--lean-root", str(self.root), "--verify-required"],
                              capture_output=True, text=True)

    def test_required_profiles_are_checked_after_the_overlay(self):
        self.required_manifest()
        self.assertNotEqual(self.verify_required().returncode, 0)
        self.assertEqual(self.replay("--prepare").returncode, 0)
        result = self.verify_required()
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertIn("1/1 verified", result.stdout)

    def test_unused_profiles_do_not_require_unused_checkouts(self):
        self.required_manifest()
        self.replay("--prepare")
        manifest = json.loads((self.bundle / "externals.json").read_text())
        manifest["repositories"]["externals/unused"] = self.entry
        (self.bundle / "externals.json").write_text(json.dumps(manifest))
        self.assertEqual(self.verify_required().returncode, 0)

    def test_new_external_local_package_requires_a_source_profile(self):
        self.required_manifest([{"type": "path", "name": "new", "dir": "../externals/new"}])
        self.replay("--prepare")
        result = self.verify_required()
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("has no recorded source profile", result.stdout)


if __name__ == "__main__":
    unittest.main()
