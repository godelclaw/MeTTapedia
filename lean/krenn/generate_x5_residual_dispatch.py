#!/usr/bin/env python3
"""Generate the typed X5 residual representative dispatch module."""

from pathlib import Path


CASES = [
    (5, 5),
    (84, 66),
    (86, 68),
    (98, 80),
    (102, 84),
    (131, 95),
    (170, 110),
    (304, 160),
    (316, 172),
    (385, 199),
    (388, 202),
    (429, 213),
    (516, 216),
    (642, 270),
    (817, 295),
    (861, 309),
    (863, 311),
    (1033, 313),
    (1293, 333),
]


def theorem(case: int, ordinal: int) -> str:
    return f"""theorem refutesRepresentative{case} (W : WeightsN 6 3 ℂ)
    (hEq : EqSystemN 6 3 W)
    (h : NormalizedRepresentative {ordinal} W) : False := by
  apply Krenn.X5ResidualCase{case}.Bridge.noNormalizedCase W hEq
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
import KrennX5Residuals

/-!
Generated semantic dispatch from representative-indexed X5 normalization
predicates to the exact case-specific residual refutations.

Each theorem fixes both the representative ordinal and the frozen case index.
This prevents a certificate for one normalized case from being used under
another representative label.
-/

namespace Krenn.X5ResidualDispatch

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
for case, ordinal in CASES:
    entries.append(
        f"def entry{case} : RefutedRepresentative :=\n"
        f"  ⟨{ordinal}, {case}, by decide, refutesRepresentative{case}⟩\n"
    )

registry = """def residualRepresentatives : Fin 19 → RefutedRepresentative := ![
  """ + ", ".join(f"entry{case}" for case, _ in CASES) + """
]

def dispatchedCaseIndices : List Nat :=
  List.ofFn fun index => (residualRepresentatives index).caseIndex.val

theorem dispatchedCaseIndices_eq :
    dispatchedCaseIndices = Krenn.X5Residuals.residualCaseIndices := by
  decide

#print axioms Krenn.X5ResidualDispatch.dispatchedCaseIndices_eq
#print axioms Krenn.X5ResidualDispatch.refutesRepresentative5
#print axioms Krenn.X5ResidualDispatch.refutesRepresentative1293

end Krenn.X5ResidualDispatch
"""

output = header + "\n".join(theorem(case, ordinal) for case, ordinal in CASES)
output += "\n" + registry_header + "\n".join(entries) + "\n" + registry
Path(__file__).with_name("KrennX5ResidualDispatch.lean").write_text(output)
