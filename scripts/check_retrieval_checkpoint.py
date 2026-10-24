#!/usr/bin/env python3
"""Build the staged retrieval core from an explicit source-only import closure.

Only external package artifacts are reused. No live-tree Mettapedia olean can
satisfy an import. The output directory retains sources, build logs and a hash
manifest for inspection; this is a focused checkpoint, not an umbrella build.
"""

import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess

REPO = Path(__file__).resolve().parents[1]
LEAN_ROOT = REPO / "lean/mettapedia"
ROOTS = [
    "Mettapedia.Algorithms.Retrieval." + name
    for name in ("BlockedPostings", "OrderedScoreMerge", "ScreeningCertificate",
                 "SparseBayes", "OrderedContributionBlocks", "CollectionObservation",
                 "BulkPreparation", "RankedCoordinateProjection", "GroupedFoldColumns")
] + ["Mettapedia.Machines.TrialRollback", "Mettapedia.Machines.StrictBooleanIntrinsics",
     "Mettapedia.Machines.IndexScalarEncoding",
     "Mettapedia.Algebra.SupportTensorLayout",
     "Mettapedia.Algebra.SupportTensorSchedule",
     "Mettapedia.Algorithms.Collections.AtomicIngress",
     "Mettapedia.Algorithms.Collections.StableKeyEncoding",
     "Mettapedia.Algorithms.Collections.OrderedIntersection"]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", required=True, type=Path)
    parser.add_argument("--extra-root", action="append", default=[],
                        help="Additional staged module whose complete source closure is checked")
    args = parser.parse_args()
    output = args.output.resolve()
    # Refuse reuse: a previous olean must never mask a missing source here.
    output.mkdir(parents=True, exist_ok=False)
    sources, artifacts = output / "sources", output / "lib"
    artifacts.mkdir()
    captured, ordered, visiting = {}, [], set()

    def visit(module):
        if module in visiting:
            raise RuntimeError(f"cyclic import: {module}")
        if module in captured:
            return
        visiting.add(module)
        relative = Path(*module.split(".")).with_suffix(".lean")
        index_path = (Path("lean/mettapedia") / relative).as_posix()
        data = subprocess.check_output(["git", "show", ":" + index_path], cwd=REPO)
        # This scanner consumes these modules' ordinary top-level imports;
        # unsupported multiline or generated imports must not be invented.
        dependencies = []
        for line in data.decode().splitlines():
            declaration = re.match(r"^(?:(?:public|meta|private)\s+)*import\s+(.+)$", line)
            if declaration:
                for name in declaration[1].split("--", 1)[0].split():
                    if name.startswith("Mettapedia."):
                        dependencies.append(name)
                        visit(name)
        visiting.remove(module)
        captured[module] = (relative, index_path, data, dependencies)
        ordered.append(module)

    roots = ROOTS + args.extra_root
    for module in roots:
        visit(module)

    manifest = {"roots": roots, "modules": []}
    for module in ordered:
        relative, index_path, data, dependencies = captured[module]
        source = sources / relative
        source.parent.mkdir(parents=True, exist_ok=True)
        source.write_bytes(data)
        manifest["modules"].append({"module": module, "source": index_path,
            "sha256": hashlib.sha256(data).hexdigest(), "imports": dependencies})
    (output / "sources.json").write_text(json.dumps(manifest, indent=2) + "\n")

    package_path = subprocess.check_output(
        ["lake", "env", "printenv", "LEAN_PATH"], cwd=LEAN_ROOT, text=True).strip()
    live_artifacts = (LEAN_ROOT / ".lake/build/lib/lean").resolve()
    external = [entry for entry in package_path.split(os.pathsep)
                if entry and (LEAN_ROOT / entry).resolve() != live_artifacts]
    env = dict(os.environ, LEAN_PATH=os.pathsep.join([str(artifacts), *external]))
    lean = subprocess.check_output(
        ["lake", "env", "which", "lean"], cwd=LEAN_ROOT, text=True).strip()
    for module in ordered:
        relative, _, _, _ = captured[module]
        target = (artifacts / relative).with_suffix(".olean")
        target.parent.mkdir(parents=True, exist_ok=True)
        result = subprocess.run([lean, "-DwarningAsError=true", "--root=" + str(sources),
                                 "-o", str(target), str(sources / relative)],
                                cwd=LEAN_ROOT, env=env, text=True, capture_output=True)
        (output / (module + ".log")).write_text(result.stdout + result.stderr)
        if result.returncode:
            raise RuntimeError(f"{module} failed:\n{result.stdout}{result.stderr}")
        print("PASS", module, flush=True)
    # The receipt certifies exactly the captured staging snapshot, not edits
    # that another worker or the user may have staged during compilation.
    for module in ordered:
        _, index_path, data, _ = captured[module]
        current = subprocess.check_output(["git", "show", ":" + index_path], cwd=REPO)
        if current != data:
            raise RuntimeError(f"staged source changed during qualification: {module}")
    print(f"RetrievalCheckpoint {len(ordered)} 0", flush=True)


if __name__ == "__main__":
    main()
