#!/usr/bin/env python3
"""Generate typed dispatch for every migrated historical X5 representative."""

from pathlib import Path
import re


ROOT = Path(__file__).parent


def numbers_between(path: str, start: str, end: str) -> list[int]:
    text = (ROOT / path).read_text()
    match = re.search(re.escape(start) + r"(.*?)" + re.escape(end), text, re.S)
    if match is None:
        raise RuntimeError(f"could not parse {start!r} from {path}")
    return [int(value) for value in re.findall(r"\d+", match.group(1))]


representatives = numbers_between(
    "KrennX5GaugeNormalizationData.lean",
    "def representativeCase : Fin 336 → Fin 1296 :=\n  ![",
    "]\n\ndef orbitSize",
)
cases = numbers_between(
    "KrennX5LegacyMigrated.lean",
    "def migratedCaseIndices : List Nat :=\n  [",
    "]\n\ntheorem migratedCaseIndices_length",
)

if len(representatives) != 336:
    raise RuntimeError(f"expected 336 representatives, got {len(representatives)}")
if not 1 <= len(cases) <= 317:
    raise RuntimeError(f"invalid migrated-case count: {len(cases)}")
if len(set(representatives)) != 336 or len(set(cases)) != len(cases):
    raise RuntimeError("representative or migrated-case list contains duplicates")

ordinals = {case: ordinal for ordinal, case in enumerate(representatives)}
missing = [case for case in cases if case not in ordinals]
if missing:
    raise RuntimeError(f"migrated cases absent from representative table: {missing}")


def theorem(case: int) -> str:
    ordinal = ordinals[case]
    return f"""theorem refutesRepresentative{case} (W : WeightsN 6 3 ℂ)
    (hEq : EqSystemN 6 3 W)
    (h : NormalizedRepresentative {ordinal} W) : False := by
  apply Krenn.X5Case{case}Bridge.noNormalizedCase W hEq
  refine ⟨?_, ?_, ?_, ?_, ?_, h.outside05, h.outside12, h.outside13,
    h.outside14, h.outside23, h.outside24, h.outside25, h.outside34,
    h.outside35, h.outside45⟩
  · simpa [datum, datumCase{case}, selectedCase{case}] using h.selected 0
  · simpa [datum, datumCase{case}, selectedCase{case}] using h.selected 1
  · simpa [datum, datumCase{case}, selectedCase{case}] using h.selected 2
  · simpa [datum, datumCase{case}, selectedCase{case}] using h.selected 3
  · simpa [datum, datumCase{case}, selectedCase{case}] using h.selected 4
"""


header = """import KrennX5SupportConnector
import KrennX5LegacyMigrated

/-!
Generated semantic dispatch from representative-indexed X5 normalization
predicates to every currently migrated historical refutation.

The generator derives each representative ordinal from the canonical
`representativeCase` table and rejects missing or duplicate indices.
-/

namespace Krenn.X5LegacyDispatch

open MonochromaticQuantumGraph
open Krenn.X5GaugeNormalizationData
open Krenn.X5SupportConnector

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

"""

registry_header = """structure RefutedRepresentative where
  ordinal : Fin 336
  caseIndex : Fin 1296
  caseIndex_eq : representativeCase ordinal = caseIndex
  impossible : ∀ W, EqSystemN 6 3 W →
    NormalizedRepresentative ordinal W → False

"""

entries = []
for case in cases:
    entries.append(
        f"def entry{case} : RefutedRepresentative :=\n"
        f"  ⟨{ordinals[case]}, {case}, by decide, refutesRepresentative{case}⟩\n"
    )

registry = f"""def migratedRepresentatives : Fin {len(cases)} → RefutedRepresentative := ![
  {', '.join(f'entry{case}' for case in cases)}
]

def dispatchedCaseIndices : List Nat :=
  List.ofFn fun index => (migratedRepresentatives index).caseIndex.val

theorem dispatchedCaseIndices_eq :
    dispatchedCaseIndices = Krenn.X5LegacyMigrated.migratedCaseIndices := by
  decide

#print axioms Krenn.X5LegacyDispatch.dispatchedCaseIndices_eq
#print axioms Krenn.X5LegacyDispatch.refutesRepresentative{cases[0]}
#print axioms Krenn.X5LegacyDispatch.refutesRepresentative{cases[-1]}

end Krenn.X5LegacyDispatch
"""

output = header + "\n".join(theorem(case) for case in cases)
output += "\n" + registry_header + "\n".join(entries) + "\n" + registry
(ROOT / "KrennX5LegacyDispatch.lean").write_text(output)
