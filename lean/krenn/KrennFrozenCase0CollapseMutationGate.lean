import KrennFrozenCase0CollapseLayer

/-!
Negative provenance gates for the frozen case-0 collapse seam.  These are
deliberately semantic rather than textual: a changed source index must fail at
polynomial evaluation, even when the surrounding Boolean cover is unchanged.
-/

namespace Krenn.FrozenCase0CollapseMutationGate

open MvPolynomial
open Krenn.SparseCertificate
open Krenn.FrozenCase0CollapseLayer

def oneValues : Fin 75 → ℤ := fun _ => 1

/-- Source equation five, named locally so the negative gate does not need to
unfold the complete 747-entry vector while evaluating a single mutation. -/
def sourceEquationFive : SparsePoly (Fin 75) :=
  [{ coefficient := 1, powers := [(10, 1), (40, 1)] },
   { coefficient := 1, powers := [(30, 1), (68, 1)] }]

def determinantFive : SparsePoly (Fin 75) :=
  [{ coefficient := 1, powers := [(11, 1), (22, 1)] },
   { coefficient := -1, powers := [(14, 1), (19, 1)] }]

theorem sourceEquationFive_exact :
    Krenn.FrozenCase0System.equations 5 = sourceEquationFive := by rfl

theorem determinantFive_exact :
    frozenCollapseEquation 5 = determinantFive := by rfl

/- Replacing determinant five's recorded source equation 6 by neighbouring
source equation 5 changes the polynomial.  The all-one valuation is a compact
kernel-checked separating witness. -/
set_option maxRecDepth 100000 in
theorem source_index_five_mutation_rejected :
    (frozenCollapseEquation 5).toPoly ≠
      (Krenn.FrozenCase0System.equations 5).toPoly := by
  intro equal
  have evaluated := congrArg
    (eval₂Hom (Int.castRingHom ℤ) oneValues) equal
  rw [sourceEquationFive_exact] at evaluated
  rw [determinantFive_exact] at evaluated
  norm_num [oneValues, frozenCollapseEquation,
    sourceEquationFive, determinantFive, SparsePoly.toPoly,
    SparseTerm.toPoly] at evaluated

/-- The intended source index is specifically six, not its neighbouring
equation five. -/
theorem source_index_five_is_six : collapseSourceIndex 5 = 6 := by decide

end Krenn.FrozenCase0CollapseMutationGate

#print axioms Krenn.FrozenCase0CollapseMutationGate.source_index_five_mutation_rejected
