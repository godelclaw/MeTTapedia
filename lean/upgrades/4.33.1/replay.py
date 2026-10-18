#!/usr/bin/env python3
"""Check or apply the recorded external migration to an exact, clean base."""

import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess
import tempfile


def git(repo, *args, env=None):
    return subprocess.check_output(["git", "-C", str(repo), *args], env=env)


def check_patches(repo, patches, revision="HEAD"):
    """Replay sequential patches in a private index and object store."""
    objects = Path(git(repo, "rev-parse", "--git-path", "objects").decode().strip())
    if not objects.is_absolute():
        objects = repo / objects
    with tempfile.TemporaryDirectory(prefix="dependency-replay-") as temporary:
        scratch = Path(temporary)
        (scratch / "objects").mkdir()
        env = dict(os.environ, GIT_INDEX_FILE=str(scratch / "index"),
                   GIT_OBJECT_DIRECTORY=str(scratch / "objects"),
                   GIT_ALTERNATE_OBJECT_DIRECTORIES=str(objects.resolve()))
        git(repo, "read-tree", revision, env=env)
        for patch in patches:
            if patch.stat().st_size:
                git(repo, "apply", "--cached", str(patch), env=env)


def contained(root, relative):
    path = root / relative
    if Path(relative).is_absolute() or not path.resolve().is_relative_to(root.resolve()):
        raise ValueError(f"Path escapes its root: {relative}")
    return path


def sha256(data):
    return hashlib.sha256(data).hexdigest()


def checked_patches(bundle, entry):
    patch = contained(bundle, entry["patch"])
    if sha256(patch.read_bytes()) != entry["patch_sha256"]:
        raise ValueError("Migration patch fingerprint differs")
    overlay = entry.get("overlay")
    overlay_patch = contained(bundle, overlay["patch"]) if overlay else None
    if overlay and sha256(overlay_patch.read_bytes()) != overlay["patch_sha256"]:
        raise ValueError("Compatibility overlay fingerprint differs")
    return patch, overlay, overlay_patch


def required_repositories(lean):
    """Select external path packages from Lake's resolved dependency graph."""
    lock = json.loads((lean / "mettapedia/lake-manifest.json").read_text())
    required = set()
    for package in lock["packages"]:
        if package["type"] != "path":
            continue
        path = (lean / "mettapedia" / package["dir"]).resolve()
        relative = path.relative_to(lean.resolve())
        if relative.parts[0] in {"externals", "standalone"}:
            required.add(relative.as_posix())
    return sorted(required)


def verify_sources(repo, entry, *, overlay=True):
    files = dict(entry["files"])
    if overlay:
        files.update(entry.get("overlay", {}).get("files", {}))
    for relative, expected in files.items():
        path = contained(repo, relative)
        if expected is None:
            if path.exists():
                raise ValueError(f"Expected absent file: {relative}")
        elif not path.is_file() or sha256(path.read_bytes()) != expected:
            raise ValueError(f"Source fingerprint differs: {relative}")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("repository", nargs="?", help="Repository path relative to lean/")
    parser.add_argument("--lean-root", type=Path, help="Alternate dependency workspace")
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument("--apply", action="store_true", help="Apply to a clean, pinned checkout")
    mode.add_argument("--verify", action="store_true", help="Verify already migrated source fingerprints")
    mode.add_argument("--prepare", action="store_true",
                      help="Verify a published checkout and apply its recorded compatibility overlay")
    mode.add_argument("--verify-required", action="store_true",
                      help="Verify external local source profiles required by the library's Lake manifest")
    args = parser.parse_args()
    bundle = Path(__file__).resolve().parent
    lean = args.lean_root or bundle.parent.parent
    manifest = json.loads((bundle / "externals.json").read_text())
    if args.verify_required:
        if args.repository:
            parser.error("--verify-required does not take a repository")
        failed = []
        required = required_repositories(lean)
        for repository in required:
            try:
                if repository not in manifest["repositories"]:
                    raise ValueError("required local dependency has no recorded source profile")
                entry = manifest["repositories"][repository]
                checked_patches(bundle, entry)
                verify_sources(contained(lean, repository), entry)
            except (ValueError, OSError) as error:
                failed.append((repository, str(error)))
        for repository, error in failed:
            print(f"{repository}: {error}")
        print(f"Required local source profiles: {len(required) - len(failed)}/{len(required)} verified")
        return int(bool(failed))
    if not args.repository:
        parser.error("provide a repository or --verify-required")
    entry = manifest["repositories"][args.repository]
    repo = contained(lean, args.repository)
    patch, overlay, overlay_patch = checked_patches(bundle, entry)
    if args.verify:
        verify_sources(repo, entry)
        print(f"Verified migration: {args.repository}")
        return
    if args.prepare:
        if overlay:
            if git(repo, "rev-parse", "HEAD").decode().strip() != overlay["base"]:
                raise ValueError("Compatibility overlay requires its recorded published revision")
            if git(repo, "status", "--porcelain", "--untracked-files=all").strip():
                raise ValueError("Compatibility overlay requires a clean checkout; existing work is preserved")
            verify_sources(repo, entry, overlay=False)
            git(repo, "apply", "--check", str(overlay_patch))
            git(repo, "apply", str(overlay_patch))
        verify_sources(repo, entry)
        print(f"Prepared published sources: {args.repository}")
        return
    if git(repo, "rev-parse", "HEAD").decode().strip() != entry["base"]:
        raise ValueError("Repository is not at the recorded base revision")
    if git(repo, "status", "--porcelain", "--untracked-files=all").strip():
        raise ValueError("Migration requires a clean checkout; existing work is preserved")
    if not patch.stat().st_size and not overlay:
        verify_sources(repo, entry)
        print(f"No migration changes: {args.repository}")
        return
    if args.apply:
        check_patches(repo, [patch] + ([overlay_patch] if overlay else []))
        if patch.stat().st_size:
            git(repo, "apply", str(patch))
        if overlay:
            git(repo, "apply", "--check", str(overlay_patch))
            git(repo, "apply", str(overlay_patch))
        verify_sources(repo, entry)
        print(f"Applied migration: {args.repository}")
    else:
        check_patches(repo, [patch] + ([overlay_patch] if overlay else []))
        print(f"Recorded patches apply cleanly: {args.repository}")


if __name__ == "__main__":
    raise SystemExit(main())
