#!/usr/bin/env python3
"""Generate the typed registry of official legacy X5 case refutations.

The registry is derived only from paired generated Selected/Bridge modules.
It deliberately does not infer proof coverage from solver logs or filenames in
the artifact tree: each imported bridge supplies the theorem stored in the
typed entry.
"""

from __future__ import annotations

import argparse
import re
from pathlib import Path


BRIDGE = re.compile(r"KrennX5Case([0-9]+)Bridge[.]lean")


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("output", type=Path)
    parser.add_argument("--lean-root", type=Path, default=Path("."))
    args = parser.parse_args()
    root = args.lean_root.resolve()

    cases: list[int] = []
    for path in root.glob("KrennX5Case*Bridge.lean"):
        match = BRIDGE.fullmatch(path.name)
        if match is None:
            continue
        case = int(match.group(1))
        selected = root / f"KrennX5Case{case}Selected.lean"
        if not selected.is_file():
            raise ValueError(f"case {case} bridge has no selected module")
        cases.append(case)
    cases.sort()
    if not cases or len(cases) != len(set(cases)):
        raise ValueError("empty or duplicate legacy case registry")

    imports = "\n".join(f"import KrennX5Case{case}Bridge" for case in cases)
    entries = "\n".join(
        f"def entry{case} : RefutedCase := ⟨{case}, "
        f"Krenn.X5Case{case}Bridge.NormalizedCase,\n  "
        f"Krenn.X5Case{case}Bridge.noNormalizedCase⟩"
        for case in cases
    )
    vector = ", ".join(f"entry{case}" for case in cases)
    indices = ", ".join(str(case) for case in cases)
    text = f"""{imports}

/-!
Typed registry for the migrated legacy `X = {{01,02,03,04,15}}` cases.

Each entry contains the actual normalized-chart predicate and its official
`EqSystemN 6 3` refutation. Thus the table counts proved attachments, not
filenames or external solver verdicts. Exhaustive coverage of all historical
cases remains a separate outer theorem.
-/

namespace Krenn.X5LegacyMigrated

open MonochromaticQuantumGraph

set_option maxRecDepth 100000

structure RefutedCase where
  caseIndex : Nat
  Normalized : WeightsN 6 3 ℂ → Prop
  impossible : ∀ W, EqSystemN 6 3 W → Normalized W → False

{entries}

def migratedCases : Fin {len(cases)} → RefutedCase := ![
  {vector}
]

def migratedCaseIndices : List Nat :=
  [{indices}]

theorem migratedCaseIndices_length :
    migratedCaseIndices.length = {len(cases)} := by decide

theorem migratedCaseIndices_nodup : migratedCaseIndices.Nodup := by decide

#print axioms Krenn.X5LegacyMigrated.migratedCaseIndices_nodup

end Krenn.X5LegacyMigrated
"""
    args.output.write_text(text, encoding="utf-8")
    print(f"legacy_registry_cases={len(cases)}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
