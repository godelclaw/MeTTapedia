#!/usr/bin/env python3
"""Rebuild the arity-ten presentation with rotation and reflection sharing.

The generated modules retain the pinned reference's split and coverage trees.
Selected hubcaps use semantic bounds assembled from representative checks.
A separate namespace allows comparison with the original presentation. Both
versions use the same part, rule and configuration definitions.
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
from semantic_hubcaps import audit_source, replace_checks, replace_consumers, selected_cases


MODULES = {
    "Present10Chk1": "Checks1",
    "Present10Chk2": "Checks",
    "Present10Chk4": "Checks4",
    "Present10Chk13": "Checks13",
    "Present10Chk18": "Checks18",
    "Present10Chk20": "Checks20",
    "Present10Chk22": "Checks22",
    "Present10Chk23": "Checks23",
    "Present10Chk24": "Checks24",
    "Present10Hub1": "Hub1",
    "Present10Hub2": "Hub2",
    "Present10Step1": "Step1",
    "Present10Step2": "Step2",
    "Present10Step3": "Step3",
    "Present10": "Coverage",
}
PREFIX = "MettapediaFourColor.Orbit10"
REPLACEMENTS = {
    "Present10Chk2": (128, "PeriodicHubcap"),
    "Present10Chk4": (242, None),
}


def transform(name, source, cases):
    """Apply the exact, bounded substitution to one pinned source."""
    if name in REPLACEMENTS:
        case, consumer = REPLACEMENTS[name]
        start = source.index(f"theorem c10_{case}_1 :")
        first = source.rindex("set_option maxRecDepth", 0, start)
        end = source.index(f"theorem f10_{case} :")
        last = source.rindex("set_option maxRecDepth", 0, end)
        removed = source[first:last]
        names = re.findall(r"^theorem (\w+)", removed, re.M)
        if names != [f"c10_{case}_{i}" for i in range(1, 11)]:
            raise ValueError("The selected block is not the original ten checks")
        old = "  simp [hubcapFit, " + ", ".join(names) + "]"
        if source.count(old) != 1:
            raise ValueError("The combining proof differs from the recorded form")
        if consumer is None:
            proof_end = source.index("\n\n", end)
            if old not in source[last:proof_end]:
                raise ValueError("The complete combining proof was not located")
            source = source[:first] + source[proof_end + 2:]
        else:
            source = source[:first] + source[last:]
            source = source.replace(old, f"  exact FourColor.{consumer}.fit")
            source = f"import MettapediaFourColor.{consumer}\n" + source
        if re.search(rf"\bc10_{case}_\d+\b", source):
            raise ValueError("A removed certificate remains in the source")
    if name == "Present10Step1":
        bounds = [4, 5, 5, 4, 2] * 2
        old = "\n".join([
            "  exact succeed_by_hubcap10 hred",
            *[("    (" if j == 0 else "     ") + f"Hubcap.one {j} {b} <|"
              for j, b in enumerate(bounds)],
            "     Hubcap.nil)",
            "    rfl (by decide +kernel) (by decide +kernel) f10_242",
        ])
        if source.count(old) != 1:
            raise ValueError("The f10_242 consumer differs from the recorded form")
        source = source.replace(old, "  exact FourColor.ReflectedHubcap.succeeds hred _")
        source = "import MettapediaFourColor.ReflectedHubcap\n" + source
        if re.search(r"\bf10_242\b", source):
            raise ValueError("The removed hubcap theorem still has a consumer")
    if "Chk" in name:
        source, _ = replace_checks(source, cases)
    if "Step" in name or "Hub" in name:
        source, _ = replace_consumers(source, cases)
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
    for name, digest in pin["sources"].items():
        data = (reference / "FourColor" / (name + ".lean")).read_bytes()
        if hashlib.sha256(data).hexdigest() != digest:
            raise SystemExit("Reference source differs from the pin: " + name)
    cases = selected_cases(reference)
    source_root = output / "src"
    source_root.mkdir(parents=True, exist_ok=True)
    (source_root / "LICENSE").write_bytes((package / "LICENSE").read_bytes())
    generated = []
    for old, new in MODULES.items():
        original = (reference / "FourColor" / (old + ".lean")).read_bytes()
        original_hash = hashlib.sha256(original).hexdigest()
        if original_hash != pin["sources"][old]:
            raise SystemExit("Reference source differs from the pin: " + old)
        data = transform(old, original.decode(), cases).encode()
        module = PREFIX + "." + new
        path = source_root / (module.replace(".", "/") + ".lean")
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(data)
        generated.append(dict(module=module, original_module="FourColor." + old,
                              original_sha256=original_hash,
                              source_sha256=hashlib.sha256(data).hexdigest()))
    presentation = "\n".join((source_root / (r["module"].replace(".", "/") + ".lean")).read_text()
                              for r in generated)
    for case, data in cases.items():
        for pattern in (rf"theorem f10_{case} \(hred", rf"\(f10_{case} hred\)"):
            if len(re.findall(pattern, presentation)) != 1:
                raise SystemExit("Expected exactly one semantic certificate and consumer: " + str(case))
        for q in data["queries"]:
            if q["name"] != q["representative"] and re.search(rf"\b{q['name']}\b", presentation):
                raise SystemExit("Removed check remains in the presentation: " + q["name"])
    for name in ("OrbitAssembly", "OrbitAssemblyAudit"):
        module = "MettapediaFourColor." + name
        relative = Path(module.replace(".", "/") + ".lean")
        data = (package / relative).read_bytes()
        (source_root / relative).write_bytes(data)
        generated.append(dict(module=module, source_sha256=hashlib.sha256(data).hexdigest()))
    module = "MettapediaFourColor.Orbit10.SemanticSharingAudit"
    data = audit_source(cases).encode()
    (source_root / (module.replace(".", "/") + ".lean")).write_bytes(data)
    generated.append(dict(module=module, source_sha256=hashlib.sha256(data).hexdigest()))
    sharing = [dict(case=case, part=data["part"], before=data["before"], after=data["after"],
                    removed_checks=[q["name"] for q in data["queries"]
                                    if q["name"] != q["representative"]])
               for case, data in cases.items()]
    report = dict(reference_revision=REFERENCE_REVISION, generated=generated,
                  semantic_sharing=sharing,
                  compiler_options=OPTIONS, native_code_generation=False, modules=[])
    receipt = output / "orbit-results.json"
    receipt.write_text(json.dumps(report, indent=2) + "\n")
    if args.prepare_only:
        print(f"Prepared {len(MODULES)} presentation modules and three assembly/audit modules.")
        return
    artifacts = (args.reference_artifacts or Path(os.environ.get(
        "FOURCOLOR_REFERENCE_ARTIFACTS", str(reference / ".lake/build/lib/lean")))).resolve()
    for n in range(1, 25):
        if f"Present10Chk{n}" not in MODULES and not (artifacts / f"FourColor/Present10Chk{n}.olean").is_file():
            raise SystemExit(f"Missing prepared reference module: FourColor.Present10Chk{n}")
    library = (args.library_output or output / "lib").resolve()
    adapters = package / ".lake/build/lib/lean"
    for name in ("PeriodicHubcap", "ReflectedHubcap", "HubcapCharges", "ClassicalAssembly",
                 "PairChargeTransport", "SourceTait"):
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
