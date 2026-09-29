#!/usr/bin/env python3
"""Check the uncompressed baseline and the complete compositional endpoints.

The baseline audit runs in a separate Lean process. Its environment is not
imported by the compositional assembly, whose audit rejects the original
unconditional theorem and all superseded arity-nine, arity-ten and arity-eleven checker
declarations. Prepared reference, adapter and presentation dependencies are
required. Artifacts can be installed in the package's ordinary library output.
"""

import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess
import time

from replay_adapters import OPTIONS, REFERENCE_REVISION, capture

MODULES = ["ReferenceBaselineAudit", "DiamondFamilyReducibility", "Complete", "CompleteAudit"]


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--reference", type=Path, required=True)
    parser.add_argument("--mettapedia", type=Path, required=True)
    parser.add_argument("--package", type=Path, required=True)
    parser.add_argument("--source-root", type=Path)
    parser.add_argument("--reference-artifacts", type=Path)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--library-output", type=Path)
    parser.add_argument("--lean", default="lean")
    parser.add_argument("--lake", default="lake")
    args = parser.parse_args()
    reference, mettapedia, package, output = (p.resolve() for p in
        (args.reference, args.mettapedia, args.package, args.output))
    sources = (args.source_root or package).resolve()
    artifacts = (args.reference_artifacts or Path(os.environ.get(
        "FOURCOLOR_REFERENCE_ARTIFACTS", str(reference / ".lake/build/lib/lean")))).resolve()
    if capture(["git", "rev-parse", "HEAD"], reference) != REFERENCE_REVISION:
        raise SystemExit("Reference revision differs from the audited pin")
    if ((reference / "lean-toolchain").read_text().strip() !=
            (mettapedia / "lean-toolchain").read_text().strip()):
        raise SystemExit("The reference and Mettapedia must use the same toolchain")
    required = ["Complete", "Reduce/All", *[f"Present{n}" for n in range(5, 12)]]
    for name in required:
        if not (artifacts / f"FourColor/{name}.olean").is_file():
            raise SystemExit("Missing prepared reference module: FourColor." + name.replace("/", "."))

    adapters = package / ".lake/build/lib/lean"
    prepared = []
    for kind, expected_count in (("adapter", 21), ("orbit", 18), ("orbit11", 11),
                                 ("orbit9", 37), ("family", 19)):
        receipt = json.loads((package / f".lake/{kind}-audit/{kind}-results.json").read_text())
        if receipt["reference_revision"] != REFERENCE_REVISION:
            raise SystemExit("Prepared dependency uses another reference revision")
        if (receipt.get("compiler_options") != OPTIONS
                or receipt.get("native_code_generation") is not False):
            raise SystemExit("Prepared dependency uses different compiler settings")
        if not receipt.get("completed"):
            raise SystemExit("The prepared dependency gate has not completed")
        if len(receipt["modules"]) != expected_count:
            raise SystemExit("Unexpected prepared module count")
        for record in receipt["modules"]:
            relative = record["module"].replace(".", "/")
            source = package / (relative + ".lean")
            if not source.is_file():
                source = package / f".lake/{kind}-audit/src/{relative}.lean"
            compiled = adapters / (relative + ".olean")
            if (record["exit_code"] != 0 or digest(source) != record["source_sha256"]
                    or not compiled.is_file()):
                raise SystemExit("Prepared dependency differs from its receipt: " + record["module"])
            if digest(compiled) != record.get("olean_sha256"):
                raise SystemExit("Prepared artifact differs from its receipt: " + record["module"])
            prepared.append(dict(module=record["module"], source_sha256=digest(source),
                                 olean_sha256=digest(compiled)))

    library = (args.library_output or output / "lib").resolve()
    source_root = output / "src"
    source_root.mkdir(parents=True, exist_ok=True)
    library.mkdir(parents=True, exist_ok=True)
    owned = {"MettapediaFourColor/" + name for name in MODULES}
    for path in (adapters / "MettapediaFourColor").rglob("*"):
        if not path.is_file():
            continue
        relative = path.relative_to(adapters)
        if str(relative.with_suffix("")) in owned:
            continue
        destination = library / relative
        destination.parent.mkdir(parents=True, exist_ok=True)
        if not destination.exists() and not destination.is_symlink():
            destination.symlink_to(path)
        elif destination.resolve() != path.resolve():
            raise SystemExit("Unexpected dependency overlay: " + str(relative))

    env = dict(os.environ)
    env["LEAN_PATH"] = os.pathsep.join([
        str(library), str(artifacts),
        capture([args.lake, "env", "printenv", "LEAN_PATH"], mettapedia),
        capture([args.lake, "env", "printenv", "LEAN_PATH"], reference),
    ])
    report = dict(reference_revision=REFERENCE_REVISION, compiler_options=OPTIONS,
                  prepared_dependencies=prepared, native_code_generation=False,
                  completed=False, modules=[])
    receipt_path = output / "complete-results.json"
    receipt_path.write_text(json.dumps(report, indent=2) + "\n")
    for name in MODULES:
        module = "MettapediaFourColor." + name
        relative = module.replace(".", "/")
        source = source_root / (relative + ".lean")
        source.parent.mkdir(parents=True, exist_ok=True)
        source.write_bytes((sources / (relative + ".lean")).read_bytes())
        stem = library / relative
        stem.parent.mkdir(parents=True, exist_ok=True)
        for suffix in (".olean", ".ilean"):
            if Path(str(stem) + suffix).is_symlink():
                raise SystemExit("Output must not overwrite a dependency symlink")
        command = ["timeout", "--signal=TERM", "900s", args.lean,
                   "-R", str(source_root), *OPTIONS,
                   "-o", str(stem) + ".olean", "-i", str(stem) + ".ilean", str(source)]
        start = time.monotonic()
        with (output / (name + ".log")).open("w") as log:
            result = subprocess.run(command, cwd=reference, env=env,
                                    stdout=log, stderr=subprocess.STDOUT)
        record = dict(module=module, source_sha256=digest(source),
                      exit_code=result.returncode,
                      frontend_wall_seconds=round(time.monotonic() - start, 3))
        if not result.returncode:
            compiled = Path(str(stem) + ".olean")
            record.update(olean_bytes=compiled.stat().st_size, olean_sha256=digest(compiled))
        report["modules"].append(record)
        receipt_path.write_text(json.dumps(report, indent=2) + "\n")
        print(json.dumps(record), flush=True)
        if result.returncode:
            raise SystemExit(result.returncode)
    report["completed"] = True
    receipt_path.write_text(json.dumps(report, indent=2) + "\n")


if __name__ == "__main__":
    main()
