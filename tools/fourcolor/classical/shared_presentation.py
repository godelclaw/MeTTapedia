#!/usr/bin/env python3
"""Rebuild the dependency cone of a pinned presentation with semantic sharing.

The case splits, parts and weighted covers are preserved. Unchanged modules
outside the cone are imported from the reference. The generator is untrusted;
Lean checks each replacement, the coverage consumers and the final audit.
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


def digest(data):
    return hashlib.sha256(data).hexdigest()


def prepare(reference, package, pin, source_root):
    n = pin["arity"]
    cases = selected_cases(reference, n)
    actual = (len(cases), sum(c["before"] for c in cases.values()),
              sum(c["after"] for c in cases.values()))
    expected = tuple(pin[k] for k in
                     ("selected_hubcaps", "selected_checks_before", "selected_checks_after"))
    if actual != expected:
        raise SystemExit("The selected sharing differs from the pinned inventory")
    sources = {}
    for name, expected_hash in pin["sources"].items():
        data = (reference / "FourColor" / (name + ".lean")).read_bytes()
        if digest(data) != expected_hash:
            raise SystemExit("Reference source differs from the pin: " + name)
        if name != f"Present{n}Defs":
            sources[name] = data.decode()
    deps = {name: set(re.findall(r"^import FourColor\.(\w+)$", text, re.M)) & sources.keys()
            for name, text in sources.items()}
    modified, replaced, consumed = set(), [], []
    transformed = {}
    for name, text in sources.items():
        if "Chk" in name:
            text, changed = replace_checks(text, cases, n)
            replaced.extend(changed)
        elif "Hub" in name or "Step" in name:
            text, changed = replace_consumers(text, cases, n)
            consumed.extend(changed)
        else:
            changed = []
        if changed:
            modified.add(name)
        transformed[name] = text
    if sorted(replaced) != sorted(cases) or sorted(consumed) != sorted(cases):
        raise SystemExit("A selected certificate or its unique consumer was not replaced")
    while True:
        parents = {name for name, imports in deps.items() if imports & modified}
        if parents <= modified:
            break
        modified |= parents
    if f"Present{n}" not in modified:
        raise SystemExit("The modified cone does not reach its coverage theorem")
    order, pending = [], modified.copy()
    while pending:
        ready = sorted(name for name in pending if not deps[name] & pending)
        if not ready:
            raise SystemExit("Presentation import cycle")
        order.extend(ready)
        pending.difference_update(ready)
    prefix = f"MettapediaFourColor.Orbit{n}"
    names = {name: prefix + "." + (name.removeprefix(f"Present{n}").replace("Chk", "Checks")
                                    or "Coverage") for name in modified}
    source_root.mkdir(parents=True, exist_ok=True)
    (source_root / "LICENSE").write_bytes((package / "LICENSE").read_bytes())
    generated = []
    for old in order:
        text = transformed[old]
        for original, module in names.items():
            text = re.sub(rf"(?m)^import FourColor\.{original}$", f"import {module}", text)
        if text.count("\nnamespace FourColor\n") != 1 or text.count("\nend FourColor\n") != 1:
            raise SystemExit("Unexpected namespace structure: " + old)
        text = text.replace("\nnamespace FourColor\n", f"\nnamespace FourColor.Orbit{n}\n")
        text = text.replace("\nend FourColor\n", f"\nend FourColor.Orbit{n}\n")
        module = names[old]
        path = source_root / (module.replace(".", "/") + ".lean")
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(text)
        generated.append(dict(module=module, original_module="FourColor." + old,
                              original_sha256=pin["sources"][old],
                              source_sha256=digest(path.read_bytes())))
    presentation = "\n".join((source_root / (r["module"].replace(".", "/") + ".lean")).read_text()
                              for r in generated)
    for case, row in cases.items():
        for pattern in (rf"theorem f{n}_{case} \(hred", rf"\(f{n}_{case} hred\)"):
            if len(re.findall(pattern, presentation)) != 1:
                raise SystemExit("Expected one semantic certificate and consumer: " + str(case))
        for query in row["queries"]:
            if (query["name"] != query["representative"] and
                    re.search(rf"\b{query['name']}\b", presentation)):
                raise SystemExit("Removed check remains in the presentation: " + query["name"])
    for name in pin["endpoint_modules"]:
        module = "MettapediaFourColor." + name
        relative = Path(module.replace(".", "/") + ".lean")
        data = (package / relative).read_bytes()
        (source_root / relative).write_bytes(data)
        generated.append(dict(module=module, source_sha256=digest(data)))
    return generated, cases, sorted(set(sources) - modified)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    for field in ("reference", "mettapedia", "package", "pin", "output"):
        parser.add_argument("--" + field, type=Path, required=True)
    parser.add_argument("--reference-artifacts", type=Path)
    parser.add_argument("--library-output", type=Path)
    parser.add_argument("--prepare-only", action="store_true")
    parser.add_argument("--timeout-seconds", type=int, default=900)
    parser.add_argument("--lean", default="lean")
    parser.add_argument("--lake", default="lake")
    args = parser.parse_args()
    reference, mettapedia, package, output = (p.resolve() for p in
        (args.reference, args.mettapedia, args.package, args.output))
    pin = json.loads(args.pin.read_text())
    n = pin["arity"]
    if (pin["reference_revision"] != REFERENCE_REVISION or
            capture(["git", "rev-parse", "HEAD"], reference) != REFERENCE_REVISION):
        raise SystemExit("Reference revision differs from the audited pin")
    if ((reference / "lean-toolchain").read_text().strip() !=
            (mettapedia / "lean-toolchain").read_text().strip()):
        raise SystemExit("The reference and Mettapedia must use the same toolchain")
    source_root = output / "src"
    generated, cases, reused = prepare(reference, package, pin, source_root)
    report = dict(reference_revision=REFERENCE_REVISION, arity=n, generated=generated,
                  completed=False, reused_reference_modules=["FourColor." + x for x in reused],
                  sharing=[dict(case=i, part=r["part"], before=r["before"], after=r["after"],
                                removed_checks=[q["name"] for q in r["queries"]
                                                if q["name"] != q["representative"]])
                           for i, r in cases.items()],
                  compiler_options=OPTIONS, native_code_generation=False, modules=[])
    receipt = output / f"orbit{n}-results.json"
    receipt.write_text(json.dumps(report, indent=2) + "\n")
    if args.prepare_only:
        print(f"Prepared {len(generated)} modules; reusing {len(reused)} reference modules.")
        return
    artifacts = (args.reference_artifacts or Path(os.environ.get(
        "FOURCOLOR_REFERENCE_ARTIFACTS", str(reference / ".lake/build/lib/lean")))).resolve()
    for name in [f"Present{n}Defs", *reused]:
        if not (artifacts / f"FourColor/{name}.olean").is_file():
            raise SystemExit("Missing prepared reference module: FourColor." + name)
    adapters = package / ".lake/build/lib/lean"
    for name in pin["prepared_adapters"]:
        if not (adapters / f"MettapediaFourColor/{name}.olean").is_file():
            raise SystemExit("Missing prepared adapter: " + name)
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
        command = ["timeout", "--signal=TERM", str(args.timeout_seconds) + "s", args.lean,
                   "-R", str(source_root), *OPTIONS,
                   "-o", str(stem) + ".olean", "-i", str(stem) + ".ilean",
                   str(source_root / (relative + ".lean"))]
        started = time.monotonic()
        with (output / (row["module"] + ".log")).open("w") as log:
            result = subprocess.run(command, cwd=reference, env=env,
                                    stdout=log, stderr=subprocess.STDOUT)
        record = dict(module=row["module"], source_sha256=row["source_sha256"],
                      exit_code=result.returncode,
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
