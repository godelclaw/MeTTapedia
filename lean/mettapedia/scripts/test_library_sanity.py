#!/usr/bin/env python3
"""Regression tests for import coverage and the qualification command."""

import importlib.util
import json
import os
import shutil
import subprocess
import tempfile
import unittest
from pathlib import Path


SCRIPTS = Path(__file__).resolve().parent
SPEC = importlib.util.spec_from_file_location("closure", SCRIPTS / "check_import_closure.py")
closure = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(closure)


class HeaderTests(unittest.TestCase):
    def test_comments_modifiers_and_body_are_distinguished(self):
        source = '''/- import Mettapedia.Fake /- nested -/ -/
module
prelude
public import Mettapedia.First -- import Mettapedia.Fake
meta import Mettapedia.Second
public meta import Mettapedia.Third
import all Mettapedia.Fourth
/- An example: import Mettapedia.Fake -/
def text := "import Mettapedia.Fake"
/- import Mettapedia.Fake -/
'''
        self.assertEqual(closure.parse_imports(source), [
            (4, "Mettapedia.First"), (5, "Mettapedia.Second"),
            (6, "Mettapedia.Third"), (7, "Mettapedia.Fourth"),
        ])

    def test_unicode_escaped_names_and_multiline_import(self):
        self.assertEqual(closure.parse_imports(
            "import\n Mettapedia.α\nimport Mettapedia.«example».Basic\nnamespace X"),
            [(2, "Mettapedia.α"), (3, "Mettapedia.example.Basic")])

    def test_unterminated_header_comment_is_an_error(self):
        with self.assertRaises(ValueError):
            closure.parse_imports("import Mettapedia.Basic\n/- unfinished")

    def test_reachability_handles_cycles_and_shared_dependencies(self):
        graph = {"A": ["B", "C"], "B": ["D"], "C": ["D"], "D": ["A"], "E": []}
        self.assertEqual(closure.reachable(graph, ["A"]), {"A", "B", "C", "D"})


class RepositoryTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name) / "lean/mettapedia"
        self.root.mkdir(parents=True)
        subprocess.run(["git", "init", "-q", str(self.root)], check=True)
        (self.root / "scripts").mkdir()
        for name in ("check_import_closure.py", "check_library_sanity.sh"):
            shutil.copyfile(SCRIPTS / name, self.root / "scripts" / name)

    def source(self, name, text="-- empty module\n", tracked=True):
        path = self.root / (name.replace(".", "/") + ".lean")
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(text)
        if tracked:
            subprocess.run(["git", "add", "--", str(path)], cwd=self.root, check=True)
        return path

    def check(self, *args):
        return subprocess.run([
            "python3", str(self.root / "scripts/check_import_closure.py"),
            "--tracked", "--report", str(self.root / "coverage.json"), *args,
        ], cwd=self.root, capture_output=True, text=True)

    def test_untracked_source_cannot_repair_a_published_import(self):
        self.source("Mettapedia", "module\npublic import Mettapedia.Unpublished\n")
        self.source("Mettapedia.Unpublished", tracked=False)
        result = self.check("--root", "Mettapedia")
        self.assertEqual(result.returncode, 1)
        report = json.loads((self.root / "coverage.json").read_text())
        self.assertEqual(report["dangling"], [["Mettapedia.lean", 2, "Mettapedia.Unpublished"]])
        self.assertEqual(report["sources"], 1)

    def test_coverage_fails_until_the_uncovered_module_has_a_build_root(self):
        self.source("Mettapedia")
        self.source("Mettapedia.Independent")
        result = self.check("--root", "Mettapedia", "--require-covered")
        self.assertEqual(result.returncode, 1)
        report = json.loads((self.root / "coverage.json").read_text())
        self.assertEqual(report["uncovered"], ["Mettapedia.Independent"])
        self.assertEqual(len(report["source_sha256"]), 2)
        result = self.check("--root", "Mettapedia", "--root", "Mettapedia.Independent", "--require-covered")
        self.assertEqual(result.returncode, 0, result.stderr)

    def test_missing_root_fails_even_without_strict_coverage(self):
        self.source("Mettapedia")
        self.assertEqual(self.check("--root", "Mettapedia.Missing").returncode, 1)

    def gate_fixture(self):
        script = self.root / "scripts/check_library_sanity.sh"
        bundle = self.root.parent / "upgrades/4.33.1"
        bundle.mkdir(parents=True)
        original = SCRIPTS.parent.parent / "upgrades/4.33.1/replay.py"
        shutil.copyfile(original, bundle / "replay.py")
        (bundle / "externals.json").write_text('{"repositories": {}}')
        (self.root / "lake-manifest.json").write_text('{"packages": []}')
        # --list validates the source paths, so create them from the original list.
        result = subprocess.run(["bash", str(SCRIPTS / script.name), "--list"],
                                capture_output=True, text=True, check=True)
        for name in result.stdout.splitlines():
            self.source(name)
        bindir = self.root / "bin"
        bindir.mkdir()
        lake = bindir / "lake"
        lake.write_text('#!/bin/sh\nprintf "%s\\n" "$*" >> "$LAKE_CALLS"\nexit "${LAKE_EXIT:-0}"\n')
        lake.chmod(0o755)
        env = dict(os.environ, PATH=f"{bindir}:{os.environ['PATH']}",
                   LAKE_CALLS=str(self.root / "lake-calls"))
        return script, env

    def test_no_build_still_checks_freshness_when_coverage_fails(self):
        script, env = self.gate_fixture()
        self.source("Mettapedia.Uncovered")
        result = subprocess.run(["bash", str(script), "--no-build"], env=env,
                                capture_output=True, text=True)
        self.assertEqual(result.returncode, 1)
        calls = (self.root / "lake-calls").read_text().splitlines()
        self.assertEqual(len(calls), 1)
        self.assertTrue(calls[0].startswith("--no-build build Mettapedia "))
        self.assertIn("build=not-run freshness=0 imports/coverage=1", result.stdout)

    def test_failed_build_is_not_hidden_by_source_coverage(self):
        script, env = self.gate_fixture()
        env["LAKE_EXIT"] = "7"
        result = subprocess.run(["bash", str(script)], env=env, capture_output=True, text=True)
        self.assertEqual(result.returncode, 1)
        self.assertIn("build=7 freshness=7 imports/coverage=0", result.stdout)
        self.assertEqual(len((self.root / "lake-calls").read_text().splitlines()), 2)

    def test_dependency_failure_is_reported_independently(self):
        script, env = self.gate_fixture()
        (self.root / "lake-manifest.json").write_text(json.dumps({"packages": [
            {"type": "path", "dir": "../externals/Unregistered"},
        ]}))
        result = subprocess.run(["bash", str(script), "--no-build"], env=env,
                                capture_output=True, text=True)
        self.assertEqual(result.returncode, 1)
        self.assertIn("imports/coverage=0 dependencies=1", result.stdout)
        self.assertIn("has no recorded source profile", result.stdout)


if __name__ == "__main__":
    unittest.main()
