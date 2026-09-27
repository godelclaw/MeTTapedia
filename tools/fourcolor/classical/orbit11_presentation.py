#!/usr/bin/env python3
"""Rebuild arity eleven with semantic reflection sharing and audited consumers.

The pinned case splits, parts and weighted covers are preserved. Thirteen
hubcaps use the existing semantic transport lemma to share 62 checks. The
result composes with the already checked arity-ten presentation.
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
from semantic_hubcaps import replace_checks, replace_consumers, selected_cases

MODULES = {**{f"Present11Chk{i}": f"Checks{i}" for i in range(1, 7)},
           "Present11Hub1": "Hub1", "Present11Step1": "Step1", "Present11": "Coverage"}
PREFIX = "MettapediaFourColor.Orbit11"


def digest(data):
    return hashlib.sha256(data).hexdigest()


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
    here = Path(__file__).resolve().parent
    package = here.parents[2] / "lean/fourcolor-classical"
    reference, mettapedia, output = (p.resolve() for p in
                                     (args.reference, args.mettapedia, args.output))
    pin = json.loads((here / "orbit11-presentation-sources.json").read_text())
    if (pin["reference_revision"] != REFERENCE_REVISION or
            capture(["git", "rev-parse", "HEAD"], reference) != REFERENCE_REVISION):
        raise SystemExit("Reference revision differs from the audited pin")
    if ((reference / "lean-toolchain").read_text().strip() !=
            (mettapedia / "lean-toolchain").read_text().strip()):
        raise SystemExit("The reference and Mettapedia must use the same toolchain")
    for name, expected in pin["sources"].items():
        if digest((reference / "FourColor" / (name + ".lean")).read_bytes()) != expected:
            raise SystemExit("Reference source differs from the pin: " + name)
    cases = selected_cases(reference, 11)
    if len(cases) != 13 or sum(c["before"] - c["after"] for c in cases.values()) != 62:
        raise SystemExit("The selected sharing differs from the audited inventory")
    source_root = output / "src"
    source_root.mkdir(parents=True, exist_ok=True)
    (source_root / "LICENSE").write_bytes((package / "LICENSE").read_bytes())
    generated, replaced, consumed = [], [], []
    for old, new in MODULES.items():
        original = (reference / "FourColor" / (old + ".lean")).read_bytes()
        text = original.decode()
        if "Chk" in old:
            text, changed = replace_checks(text, cases, 11)
            replaced.extend(changed)
        if "Step" in old or "Hub" in old:
            text, changed = replace_consumers(text, cases, 11)
            consumed.extend(changed)
        for src, dst in MODULES.items():
            text = re.sub(rf"(?m)^import FourColor\.{src}$", f"import {PREFIX}.{dst}", text)
        if text.count("\nnamespace FourColor\n") != 1 or text.count("\nend FourColor\n") != 1:
            raise SystemExit("Unexpected namespace structure: " + old)
        text = text.replace("\nnamespace FourColor\n", "\nnamespace FourColor.Orbit11\n")
        text = text.replace("\nend FourColor\n", "\nend FourColor.Orbit11\n")
        module = PREFIX + "." + new
        path = source_root / (module.replace(".", "/") + ".lean")
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(text)
        generated.append(dict(module=module, original_module="FourColor." + old,
                              original_sha256=digest(original), source_sha256=digest(path.read_bytes())))
    if sorted(replaced) != sorted(cases) or sorted(consumed) != sorted(cases):
        raise SystemExit("A selected certificate or its unique consumer was not replaced")
    presentation = "\n".join((source_root / (r["module"].replace(".", "/") + ".lean")).read_text()
                              for r in generated)
    for case, row in cases.items():
        for pattern in (rf"theorem f11_{case} \(hred", rf"\(f11_{case} hred\)"):
            if len(re.findall(pattern, presentation)) != 1:
                raise SystemExit("Expected one semantic certificate and consumer: " + str(case))
        for query in row["queries"]:
            if (query["name"] != query["representative"] and
                    re.search(rf"\b{query['name']}\b", presentation)):
                raise SystemExit("Removed check remains in the presentation: " + query["name"])
    for name in ("Orbit11Assembly", "Orbit11Audit"):
        module = "MettapediaFourColor." + name
        relative = Path(module.replace(".", "/") + ".lean")
        data = (package / relative).read_bytes()
        (source_root / relative).write_bytes(data)
        generated.append(dict(module=module, source_sha256=digest(data)))
    report = dict(reference_revision=REFERENCE_REVISION, generated=generated, completed=False,
                  sharing=[dict(case=i, part=r["part"], before=r["before"], after=r["after"],
                                removed_checks=[q["name"] for q in r["queries"]
                                                if q["name"] != q["representative"]])
                           for i, r in cases.items()],
                  compiler_options=OPTIONS, native_code_generation=False, modules=[])
    receipt = output / "orbit11-results.json"
    receipt.write_text(json.dumps(report, indent=2) + "\n")
    if args.prepare_only:
        print(f"Prepared {len(generated)} modules with {len(cases)} shared hubcaps.")
        return
    artifacts = (args.reference_artifacts or Path(os.environ.get(
        "FOURCOLOR_REFERENCE_ARTIFACTS", str(reference / ".lake/build/lib/lean")))).resolve()
    if not (artifacts / "FourColor/Present11Defs.olean").is_file():
        raise SystemExit("Missing prepared reference module: FourColor.Present11Defs")
    adapters = package / ".lake/build/lib/lean"
    for name in ("OrbitAssembly", "PairChargeTransport"):
        if not (adapters / f"MettapediaFourColor/{name}.olean").is_file():
            raise SystemExit("Build the adapters and shared arity-ten presentation first: " + name)
    library = (args.library_output or output / "lib").resolve()
    library.mkdir(parents=True, exist_ok=True)
    if library != adapters:
        owned = {r["module"].replace(".", "/") for r in generated}
        for path in (adapters / "MettapediaFourColor").rglob("*"):
            if not path.is_file():
                continue
            relative = path.relative_to(adapters)
            if str(relative.with_suffix("")) in owned:
                continue
            target = library / relative
            target.parent.mkdir(parents=True, exist_ok=True)
            if not target.exists() and not target.is_symlink():
                target.symlink_to(path)
            elif target.resolve() != path.resolve():
                raise SystemExit("Unexpected dependency overlay: " + str(relative))
    env = dict(os.environ)
    env["LEAN_PATH"] = os.pathsep.join([str(library), str(artifacts),
        capture([args.lake, "env", "printenv", "LEAN_PATH"], mettapedia),
        capture([args.lake, "env", "printenv", "LEAN_PATH"], reference)])
    for row in generated:
        relative = row["module"].replace(".", "/")
        stem = library / relative
        stem.parent.mkdir(parents=True, exist_ok=True)
        for suffix in (".olean", ".ilean"):
            if Path(str(stem) + suffix).is_symlink():
                raise SystemExit("Owned output must not overwrite a dependency symlink")
        command = ["timeout", "--signal=TERM", "900s", args.lean, "-R", str(source_root), *OPTIONS,
                   "-o", str(stem) + ".olean", "-i", str(stem) + ".ilean",
                   str(source_root / (relative + ".lean"))]
        started = time.monotonic()
        with (output / (row["module"] + ".log")).open("w") as log:
            result = subprocess.run(command, cwd=reference, env=env,
                                    stdout=log, stderr=subprocess.STDOUT)
        record = dict(module=row["module"], source_sha256=row["source_sha256"], exit_code=result.returncode,
                      frontend_wall_seconds=round(time.monotonic() - started, 3))
        if not result.returncode:
            compiled = Path(str(stem) + ".olean")
            record.update(olean_bytes=compiled.stat().st_size, olean_sha256=digest(compiled.read_bytes()))
        report["modules"].append(record)
        receipt.write_text(json.dumps(report, indent=2) + "\n")
        print(json.dumps(record), flush=True)
        if result.returncode:
            raise SystemExit(result.returncode)
    report["completed"] = True
    receipt.write_text(json.dumps(report, indent=2) + "\n")


if __name__ == "__main__":
    main()
