import MettapediaFourColor.PuncturedPairCharge
import MettapediaFourColor.ChainBoundaryGeometry

/-! Two finite receivers instantiate the exact high-boundary formula.
Their full source-rule sums remain explicit in these kernel conclusions;
the separate program audit evaluates them in both transfer directions. -/

namespace FourColor.PuncturedChargeExample

open Mettapedia.GraphTheory.FourColor SimpleGraphDartRotation
open ChainBoundaryExample NearLinearCharge PuncturedCyclicCharge

set_option maxRecDepth 65536

def roots : Fin 2 → graph.Dart :=
  ![⟨(107,104), by decide +kernel⟩, ⟨(41,32), by decide +kernel⟩]

/-- The high neighbour is retained; every other neighbour is genuinely low. -/
theorem observations (k : Fin 2) :
    graph.degree (roots k).fst = 7 ∧ 7 ≤ graph.degree (roots k).snd ∧
    (∀ w, graph.Adj (roots k).fst w → 5 ≤ graph.degree w) ∧
    (∀ w, graph.Adj (roots k).fst w → w ≠ (roots k).snd → graph.degree w ≤ 6) := by
  fin_cases k <;> decide +kernel

/-- The same exact formula retains both actual directions of the high edge.
No replacement by separately maximized transfers or numerical assumptions occurs. -/
theorem charges (k : Fin 2) :
    finalCharge rotation (roots k).fst = -10 + lowBudget rotation (roots k).fst +
      (RuleMatcher.sentAt rotation (roots k).symm -
        RuleMatcher.sentAt rotation (roots k)) := by
  obtain ⟨seven,high,lower,others⟩ := observations k
  have h := exact_charge rotation triangular (roots k).fst (by omega) lower
  rw [seven,
    unique_boundary rotation (roots k).fst (roots k).snd (roots k).adj high others,
    net] at h
  norm_num at h
  have incoming := RuleMatcher.sentAt_eq rotation (roots k).symm
  change RuleMatcher.sentAt rotation (roots k).symm =
    sent rotation (roots k).snd (roots k).fst at incoming
  rw [incoming, RuleMatcher.sentAt_eq rotation (roots k)]
  exact h

end FourColor.PuncturedChargeExample
