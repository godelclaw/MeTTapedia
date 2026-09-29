#!/usr/bin/env python3
"""Kernel-check configuration-family semantics against pinned reference maps."""

import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess
import time

from replay_adapters import OPTIONS, REFERENCE_REVISION, capture

MODULES = ["ExecutableConfiguration", "ConfigurationTable", "ConfigurationRealization",
           "ConfigurationFaceGraph", "DiamondConfigurations", "DiamondInsertion",
           "DiamondInsertionGSLT", "DiamondInsertionAudit", "ExecutableContract",
           "ConfigurationContract", "DiamondContract", "DiamondContractAudit"]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--reference", type=Path, required=True)
    parser.add_argument("--mettapedia", type=Path, required=True)
    parser.add_argument("--package", type=Path, required=True)
    parser.add_argument("--reference-artifacts", type=Path)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--library-output", type=Path)
    parser.add_argument("--lean", default="lean")
    parser.add_argument("--lake", default="lake")
    args = parser.parse_args()
    reference, mettapedia, package, output = (p.resolve() for p in
        (args.reference, args.mettapedia, args.package, args.output))
    artifacts = (args.reference_artifacts or Path(os.environ.get(
        "FOURCOLOR_REFERENCE_ARTIFACTS", str(reference / ".lake/build/lib/lean")))).resolve()
    if capture(["git", "rev-parse", "HEAD"], reference) != REFERENCE_REVISION:
        raise SystemExit("Reference revision differs from the audited pin")
    if ((reference / "lean-toolchain").read_text().strip() !=
            (mettapedia / "lean-toolchain").read_text().strip()):
        raise SystemExit("The inputs must use the same Lean toolchain")
    if not (artifacts / "FourColor/CfMap.olean").is_file():
        raise SystemExit("Missing prepared reference map module")
    output.mkdir(parents=True, exist_ok=True)
    library = (args.library_output or output / "lib").resolve()
    sources = output / "src"
    env = dict(os.environ)
    env["LEAN_PATH"] = os.pathsep.join([
        str(library), str(artifacts),
        capture([args.lake, "env", "printenv", "LEAN_PATH"], mettapedia),
        capture([args.lake, "env", "printenv", "LEAN_PATH"], reference)])
    report = dict(reference_revision=REFERENCE_REVISION, compiler_options=OPTIONS,
                  native_code_generation=False, completed=False, modules=[])
    receipt = output / "family-results.json"
    for name in MODULES:
        module = "MettapediaFourColor." + name
        relative = Path(module.replace(".", "/") + ".lean")
        source = sources / relative
        source.parent.mkdir(parents=True, exist_ok=True)
        data = (package / relative).read_bytes()
        source.write_bytes(data)
        stem = library / module.replace(".", "/")
        stem.parent.mkdir(parents=True, exist_ok=True)
        for suffix in (".olean", ".ilean"):
            if Path(str(stem) + suffix).is_symlink():
                raise SystemExit("Family output must not overwrite a dependency symlink")
        command = [args.lean, "-R", str(sources), *OPTIONS,
                   "-o", str(stem) + ".olean", "-i", str(stem) + ".ilean", str(source)]
        start = time.monotonic()
        with (output / (name + ".log")).open("w") as log:
            result = subprocess.run(command, cwd=reference, env=env,
                                    stdout=log, stderr=subprocess.STDOUT)
        record = dict(module=module, source_sha256=hashlib.sha256(data).hexdigest(),
                      exit_code=result.returncode,
                      frontend_wall_seconds=round(time.monotonic() - start, 3))
        if result.returncode == 0:
            compiled = Path(str(stem) + ".olean")
            record.update(olean_bytes=compiled.stat().st_size,
                          olean_sha256=hashlib.sha256(compiled.read_bytes()).hexdigest())
        report["modules"].append(record)
        receipt.write_text(json.dumps(report, indent=2) + "\n")
        print(json.dumps(record), flush=True)
        if result.returncode:
            print((output / (name + ".log")).read_text(), flush=True)
            raise SystemExit(result.returncode)
    report["completed"] = True
    receipt.write_text(json.dumps(report, indent=2) + "\n")


if __name__ == "__main__":
    main()
