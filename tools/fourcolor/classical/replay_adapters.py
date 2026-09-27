#!/usr/bin/env python3
"""Check the classical/GSLT adapters against prepared reference dependencies.

The output directory is a dedicated, disposable build directory. This tool
does not build the reference certificates or change either input checkout.
"""

import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess
import time


REFERENCE_REVISION = "3db71e0a786a1f19be04c5266fe3d06fed216885"
MODULES = [
    "CompatibleTraces", "PatchWitness", "HypermapDictionary",
    "EmbeddedReconstruction", "Config4Reconstruction", "ClassicalAssembly",
    "GraphColoringBridge", "BridgeAudit",
]
OPTIONS = [
    "-Dpp.unicode.fun=true", "-DautoImplicit=false",
    "-DrelaxedAutoImplicit=false", "-Dweak.linter.mathlibStandardSet=true",
    "-DmaxSynthPendingDepth=3",
]


def capture(command, cwd):
    return subprocess.run(command, cwd=cwd, check=True, text=True,
                          stdout=subprocess.PIPE).stdout.strip()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--reference", type=Path, required=True)
    parser.add_argument("--mettapedia", type=Path, required=True)
    parser.add_argument("--reference-artifacts", type=Path)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--lean", default="lean")
    parser.add_argument("--lake", default="lake")
    args = parser.parse_args()
    reference = args.reference.resolve()
    mettapedia = args.mettapedia.resolve()
    output = args.output.resolve()
    artifacts = (args.reference_artifacts or
                 reference / ".lake/build/lib/lean").resolve()
    if capture(["git", "rev-parse", "HEAD"], reference) != REFERENCE_REVISION:
        raise SystemExit("Reference revision differs from the audited pin")
    if ((reference / "lean-toolchain").read_text().strip() !=
            (mettapedia / "lean-toolchain").read_text().strip()):
        raise SystemExit("The two inputs must use the same Lean toolchain")
    required = ["Embed", "Euler", "CfQuiz", "Main", "Pilot/Cfg003",
                "Present7Chk85", "Bulk/Cfg/Hyb218"]
    for stem in required:
        if not (artifacts / "FourColor" / (stem + ".olean")).is_file():
            raise SystemExit("Missing prepared reference module: FourColor." +
                             stem.replace("/", "."))

    output.mkdir(parents=True, exist_ok=True)
    source_root = output / "src"
    library_root = output / "lib"
    adapter_dir = Path(__file__).resolve().parent / "adapters"
    owned = {Path("FourColor/Pilot") / (name + suffix)
             for name in MODULES for suffix in (".olean", ".ilean")}
    # Lean resolves the top-level prefix first. Give the fresh FourColor
    # prefix a complete dependency overlay, including the generated checks.
    for path in sorted((artifacts / "FourColor").rglob("*")):
        if not path.is_file():
            continue
        relative = path.relative_to(artifacts)
        if relative in owned:
            continue
        destination = library_root / relative
        destination.parent.mkdir(parents=True, exist_ok=True)
        if not destination.exists():
            destination.symlink_to(path.resolve())

    env = os.environ.copy()
    env["LEAN_PATH"] = os.pathsep.join([
        str(library_root),
        capture([args.lake, "env", "printenv", "LEAN_PATH"], mettapedia),
        capture([args.lake, "env", "printenv", "LEAN_PATH"], reference),
    ])
    records = []
    for name in MODULES:
        module = "FourColor.Pilot." + name
        source = source_root / "FourColor/Pilot" / (name + ".lean")
        source.parent.mkdir(parents=True, exist_ok=True)
        data = (adapter_dir / (name + ".lean")).read_bytes()
        source.write_bytes(data)
        stem = library_root / "FourColor/Pilot" / name
        stem.parent.mkdir(parents=True, exist_ok=True)
        for suffix in (".olean", ".ilean"):
            dest = Path(str(stem) + suffix)
            if dest.is_symlink():
                raise SystemExit("Adapter output must not overwrite a dependency symlink")
        command = [args.lean, "-R", str(source_root), *OPTIONS,
                   "-o", str(stem) + ".olean", "-i", str(stem) + ".ilean", str(source)]
        start = time.monotonic()
        with (output / (name + ".log")).open("w") as log:
            result = subprocess.run(command, cwd=reference, env=env,
                                    stdout=log, stderr=subprocess.STDOUT)
        record = dict(module=module, source_sha256=hashlib.sha256(data).hexdigest(),
                      exit_code=result.returncode,
                      frontend_wall_seconds=round(time.monotonic() - start, 3))
        records.append(record)
        (output / "adapter-results.json").write_text(json.dumps(dict(
            reference_revision=REFERENCE_REVISION,
            compiler_options=OPTIONS, native_code_generation=False,
            modules=records), indent=2) + "\n")
        print(json.dumps(record), flush=True)
        if result.returncode:
            raise SystemExit(result.returncode)


if __name__ == "__main__":
    main()
