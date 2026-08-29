#!/usr/bin/env python3
"""Checkpointed serial migration of named legacy f9 cases into Lean sources.

This is deliberately not a fleet.  The caller supplies an explicit finite case
list.  Every case is reconstructed from the original support/case index,
screened with a bounded exact-Q calculation, required to yield a strict exact
identity, and only then exported to the compact Lean certificate and official
semantic bridge.  The first failure stops the run.
"""

from __future__ import annotations

import os
import argparse
import hashlib
import json
import subprocess
import sys
from pathlib import Path

KRENN_ROOT = Path(os.environ.get("KRENN_ARTIFACTS", "artifacts"))
SUPPORT = "01,02,03,04,15"

sys.path.insert(0, str(KRENN_ROOT))
from strict_certificate_checker import check_c4  # noqa: E402


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def invoke(command: list[str], *, cwd: Path, accepted: tuple[int, ...] = (0,)) -> int:
    result = subprocess.run(command, cwd=cwd, text=True, capture_output=True)
    if result.stdout.strip():
        print(result.stdout.strip().splitlines()[-1], flush=True)
    if result.returncode not in accepted:
        if result.stderr.strip():
            print(result.stderr.strip(), file=sys.stderr)
        raise RuntimeError(
            f"command exited {result.returncode}: {' '.join(command)}"
        )
    return result.returncode


def strict_certificate(artifact: Path, normalizer: Path, python: str) -> Path:
    raw = artifact / "lift_direct/lift.stdout"
    normalized = artifact / "certificate_strict.txt"
    template = artifact / "certificate_template.txt"
    for candidate in (template, normalized, raw):
        if candidate.is_file():
            try:
                check_c4(artifact / "system.json", candidate)
                return candidate
            except Exception:
                pass
    manifest_path = artifact / "lift_direct/manifest.json"
    manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
    error = str(manifest.get("error", ""))
    if (manifest.get("verdict") == "strict_replay_failure"
            and "disallowed multiplier operator: Div" in error):
        invoke([
            python, str(normalizer), str(artifact / "system.json"),
            str(raw), str(normalized),
        ], cwd=normalizer.parent)
        check_c4(artifact / "system.json", normalized)
        return normalized
    raise RuntimeError(
        f"lift did not produce a strict certificate: {manifest.get('verdict')} {error}"
    )


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("cases", type=int, nargs="+")
    parser.add_argument("--artifact-root", type=Path, required=True)
    parser.add_argument("--lean-root", type=Path, required=True)
    parser.add_argument("--solve-timeout", type=int, default=30)
    parser.add_argument("--lift-timeout", type=int, default=60)
    parser.add_argument("--template-certificate", type=Path, action="append", default=[])
    parser.add_argument("--template-manifest", type=Path)
    args = parser.parse_args()
    # Exporters run from the repository root so their imports resolve.  Keep
    # the requested output directory invariant under that cwd change.
    args.artifact_root = args.artifact_root.resolve()
    args.lean_root = args.lean_root.resolve()
    if args.template_manifest is not None:
        from run_f9_template_scan_from_migration import certificate_for

        template_manifest = json.loads(
            args.template_manifest.read_text(encoding="utf-8")
        )
        seen_templates = {digest(path) for path in args.template_certificate}
        for row in template_manifest.get("cases", []):
            if row.get("migration_status") != (
                "official_normalized_case_zero_sorry_lean"
            ):
                continue
            case = int(row["case_index"])
            # Exhaustive-tree migrations have many terminal certificates and
            # therefore no single parent certificate to reuse as a template.
            # They remain valid registry entries, but are not candidates for
            # this direct-certificate discovery optimization.
            expected_value = row.get("certificate_file_sha256")
            if not isinstance(expected_value, str):
                continue
            expected = expected_value
            if expected in seen_templates:
                continue
            args.template_certificate.append(
                certificate_for(case, args.artifact_root, expected)
            )
            seen_templates.add(expected)
    if len(args.cases) != len(set(args.cases)):
        raise ValueError("case list contains duplicates")
    if any(not 0 <= case < 6 ** 5 for case in args.cases):
        raise ValueError("case index outside the five-edge case inventory")

    here = Path(__file__).resolve().parent
    repo_root = here.parents[2]
    python = sys.executable
    freeze = KRENN_ROOT / "freeze_f9_case.py"
    run_msolve = KRENN_ROOT / "run_frozen_msolve.py"
    run_lift = KRENN_ROOT / "run_exact_lift.py"
    normalizer = here / "normalize_rational_lift_certificate.py"
    selected_exporter = here / "export_lean_selected_certificate.py"
    bridge_exporter = here / "export_f9_case_bridge_lean.py"
    msolve = Path(os.environ.get("MSOLVE", "msolve"))

    completed: list[dict[str, object]] = []
    for ordinal, case in enumerate(args.cases, start=1):
        print(f"[{ordinal}/{len(args.cases)}] case {case}", flush=True)
        artifact = args.artifact_root / f"case{case}"
        system = artifact / "system.json"
        if not system.is_file():
            invoke([
                python, str(freeze), "freeze", SUPPORT, str(case), str(artifact),
                "--primes", "32003",
            ], cwd=KRENN_ROOT)
        invoke([python, str(freeze), "verify", str(system)], cwd=KRENN_ROOT)

        # Exact template reuse is stronger and cheaper than rediscovery.  A
        # template is accepted only if the unchanged strict checker replays it
        # against this case's newly reconstructed frozen system.
        template_target = artifact / "certificate_template.txt"
        if not template_target.is_file():
            for template in args.template_certificate:
                try:
                    check_c4(system, template)
                except Exception:
                    continue
                template_target.write_bytes(template.read_bytes())
                break
        template_replays = False
        if template_target.is_file():
            try:
                check_c4(system, template_target)
                template_replays = True
            except Exception:
                template_replays = False

        msolve_manifest = artifact / "msolve_q/manifest.json"
        unit = template_replays
        if msolve_manifest.is_file():
            previous = json.loads(msolve_manifest.read_text(encoding="utf-8"))
            unit = unit or previous.get("verdict") == "unit_ideal"
        if not unit:
            invoke([
                python, str(run_msolve), str(artifact / "input_q.ms"),
                str(artifact / "msolve_q"), "--msolve", str(msolve),
                "--timeout", str(args.solve_timeout), "--threads", "1",
            ], cwd=KRENN_ROOT)
        if not template_replays:
            gate = json.loads(msolve_manifest.read_text(encoding="utf-8"))
            if gate.get("verdict") != "unit_ideal":
                raise RuntimeError(f"case {case}: exact-Q gate is {gate.get('verdict')}")

        lift_manifest = artifact / "lift_direct/manifest.json"
        reusable_lift = template_replays
        if lift_manifest.is_file():
            old = json.loads(lift_manifest.read_text(encoding="utf-8"))
            reusable_lift = reusable_lift or old.get("verdict") in {
                "strict_exact_identity", "strict_replay_failure"
            }
        if not reusable_lift:
            invoke([
                python, str(run_lift), str(system), str(artifact / "lift.sing"),
                str(artifact / "lift_direct"), "--method", "posthoc",
                "--timeout", str(args.lift_timeout),
            ], cwd=KRENN_ROOT, accepted=(0, 2))
        certificate = strict_certificate(artifact, normalizer, python)
        verdict = check_c4(system, certificate)

        selected_name = f"KrennX5Case{case}Selected"
        bridge_name = f"KrennX5Case{case}Bridge"
        selected = args.lean_root / f"{selected_name}.lean"
        bridge = args.lean_root / f"{bridge_name}.lean"
        invoke([
            python, str(selected_exporter), str(system), str(certificate),
            str(selected), "--namespace", f"Krenn.X5Case{case}Selected",
        ], cwd=repo_root)
        invoke([
            python, str(bridge_exporter), str(system), str(certificate),
            str(bridge), "--certificate-module", selected_name,
            "--certificate-namespace", f"Krenn.X5Case{case}Selected",
            "--namespace", f"Krenn.X5Case{case}Bridge",
        ], cwd=repo_root)

        receipt = {
            "case_index": case,
            "certificate_file_sha256": digest(certificate),
            "max_multiplier_degree": verdict["max_multiplier_degree"],
            "selected_rows": len(verdict["nonzero_multiplier_indices_1based"]),
            "source_system_file_sha256": verdict["system_file_sha256"],
            "lean_selected_sha256": digest(selected),
            "lean_bridge_sha256": digest(bridge),
        }
        (artifact / "lean_migration.json").write_text(
            json.dumps(receipt, sort_keys=True, indent=2) + "\n",
            encoding="utf-8",
        )
        completed.append(receipt)
        print(json.dumps(receipt, sort_keys=True), flush=True)

    print(json.dumps({"completed": completed}, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
