#!/usr/bin/env python3
"""Rebuild the arity-ten presentation with its periodic hubcap shared.

The seven generated modules retain the pinned reference's proof bodies,
except for the ten removed checks and their combining theorem. A separate
namespace allows comparison with the original presentation. Both versions
use the same part, rule and configuration definitions.
"""

import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import time

from replay_adapters import OPTIONS, REFERENCE_REVISION, capture


MODULES = {
    "Present10Chk2": "Checks",
    "Present10Hub1": "Hub1",
    "Present10Hub2": "Hub2",
    "Present10Step1": "Step1",
    "Present10Step2": "Step2",
    "Present10Step3": "Step3",
    "Present10": "Coverage",
}
PREFIX = "MettapediaFourColor.Orbit10"


def transform(name, source):
    """Apply the exact, bounded substitution to one pinned source."""
    if name == "Present10Chk2":
        start = source.index("theorem c10_128_1 :")
        first = source.rindex("set_option maxRecDepth", 0, start)
        end = source.index("theorem f10_128 :")
        last = source.rindex("set_option maxRecDepth", 0, end)
        removed = source[first:last]
        names = re.findall(r"^theorem (\w+)", removed, re.M)
        if names != [f"c10_128_{i}" for i in range(1, 11)]:
            raise ValueError("The selected block is not the original ten checks")
        source = source[:first] + source[last:]
        old = "  simp [hubcapFit, " + ", ".join(names) + "]"
        if source.count(old) != 1:
            raise ValueError("The combining proof differs from the recorded form")
        source = source.replace(old, "  exact FourColor.PeriodicHubcap.fit")
        source = "import MettapediaFourColor.PeriodicHubcap\n" + source
        if re.search(r"\bc10_128_\d+\b", source):
            raise ValueError("A removed certificate remains in the source")
    for old, new in MODULES.items():
        source = re.sub(rf"(?m)^import FourColor\.{old}$",
                        f"import {PREFIX}.{new}", source)
    if (source.count("\nnamespace FourColor\n") != 1 or
            source.count("\nend FourColor\n") != 1):
        raise ValueError("Unexpected namespace structure")
    return source.replace("\nnamespace FourColor\n", "\nnamespace FourColor.Orbit10\n").replace(
        "\nend FourColor\n", "\nend FourColor.Orbit10\n")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--reference", type=Path, required=True)
    parser.add_argument("--mettapedia", type=Path, required=True)
    parser.add_argument("--reference-artifacts", type=Path)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--library-output", type=Path)
    parser.add_argument("--prepare-only", action="store_true")
    parser.add_argument("--lean", default="lean")
    parser.add_argument("--lake", default="lake")
    args = parser.parse_args()
    reference, mettapedia, output = (p.resolve() for p in
                                     (args.reference, args.mettapedia, args.output))
    here = Path(__file__).resolve().parent
    package = here.parents[2] / "lean/fourcolor-classical"
    pin = json.loads((here / "orbit-presentation-sources.json").read_text())
    if (pin["reference_revision"] != REFERENCE_REVISION or
            capture(["git", "rev-parse", "HEAD"], reference) != REFERENCE_REVISION):
        raise SystemExit("Reference revision differs from the audited pin")
    if ((reference / "lean-toolchain").read_text().strip() !=
            (mettapedia / "lean-toolchain").read_text().strip()):
        raise SystemExit("The reference and Mettapedia must use the same toolchain")
    source_root = output / "src"
    source_root.mkdir(parents=True, exist_ok=True)
    (source_root / "LICENSE").write_bytes((package / "LICENSE").read_bytes())
    generated = []
    for old, new in MODULES.items():
        original = (reference / "FourColor" / (old + ".lean")).read_bytes()
        original_hash = hashlib.sha256(original).hexdigest()
        if original_hash != pin["sources"][old]:
            raise SystemExit("Reference source differs from the pin: " + old)
        data = transform(old, original.decode()).encode()
        module = PREFIX + "." + new
        path = source_root / (module.replace(".", "/") + ".lean")
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(data)
        generated.append(dict(module=module, original_module="FourColor." + old,
                              original_sha256=original_hash,
                              source_sha256=hashlib.sha256(data).hexdigest()))
    for name in ("OrbitAssembly", "OrbitAssemblyAudit"):
        module = "MettapediaFourColor." + name
        relative = Path(module.replace(".", "/") + ".lean")
        data = (package / relative).read_bytes()
        (source_root / relative).write_bytes(data)
        generated.append(dict(module=module, source_sha256=hashlib.sha256(data).hexdigest()))
    report = dict(reference_revision=REFERENCE_REVISION, generated=generated,
                  compiler_options=OPTIONS, native_code_generation=False, modules=[])
    receipt = output / "orbit-results.json"
    receipt.write_text(json.dumps(report, indent=2) + "\n")
    if args.prepare_only:
        print("Prepared seven presentation modules and two assembly/audit modules.")
        return
    artifacts = (args.reference_artifacts or Path(os.environ.get(
        "FOURCOLOR_REFERENCE_ARTIFACTS", str(reference / ".lake/build/lib/lean")))).resolve()
    for n in range(1, 25):
        if n != 2 and not (artifacts / f"FourColor/Present10Chk{n}.olean").is_file():
            raise SystemExit(f"Missing prepared reference module: FourColor.Present10Chk{n}")
    library = (args.library_output or output / "lib").resolve()
    adapters = package / ".lake/build/lib/lean"
    for name in ("PeriodicHubcap", "ClassicalAssembly"):
        if not (adapters / f"MettapediaFourColor/{name}.olean").is_file():
            raise SystemExit("Build the adapter package first: " + name)
    # Lean resolves a top-level module prefix from one search directory.
    # A separate output therefore needs a read-only overlay of the adapters.
    if library != adapters:
        own = {record["module"].replace(".", "/") for record in generated}
        for path in (adapters / "MettapediaFourColor").rglob("*"):
            if not path.is_file():
                continue
            relative = path.relative_to(adapters)
            if str(relative.with_suffix("")) in own:
                continue
            destination = library / relative
            destination.parent.mkdir(parents=True, exist_ok=True)
            if not destination.exists() and not destination.is_symlink():
                destination.symlink_to(path)
    env = dict(os.environ)
    env["LEAN_PATH"] = os.pathsep.join([
        str(library), str(adapters), str(artifacts),
        capture([args.lake, "env", "printenv", "LEAN_PATH"], mettapedia),
        capture([args.lake, "env", "printenv", "LEAN_PATH"], reference),
    ])
    for source_record in generated:
        module = source_record["module"]
        relative = module.replace(".", "/")
        stem = library / relative
        stem.parent.mkdir(parents=True, exist_ok=True)
        for suffix in (".olean", ".ilean"):
            if Path(str(stem) + suffix).is_symlink():
                raise SystemExit("Output must not overwrite a dependency symlink")
        command = [args.lean, "-R", str(source_root), *OPTIONS,
                   "-o", str(stem) + ".olean", "-i", str(stem) + ".ilean",
                   str(source_root / (relative + ".lean"))]
        started = time.monotonic()
        with (output / (module + ".log")).open("w") as log:
            result = subprocess.run(command, cwd=reference, env=env,
                                    stdout=log, stderr=subprocess.STDOUT)
        record = dict(module=module, source_sha256=source_record["source_sha256"],
                      exit_code=result.returncode,
                      frontend_wall_seconds=round(time.monotonic() - started, 3))
        if not result.returncode:
            record["olean_bytes"] = Path(str(stem) + ".olean").stat().st_size
        report["modules"].append(record)
        receipt.write_text(json.dumps(report, indent=2) + "\n")
        print(json.dumps(record), flush=True)
        if result.returncode:
            raise SystemExit(result.returncode)
    report["completed"] = True
    receipt.write_text(json.dumps(report, indent=2) + "\n")


if __name__ == "__main__":
    main()
