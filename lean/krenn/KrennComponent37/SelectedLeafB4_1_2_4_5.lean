import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component37.SelectedLeafB4_1_2_4_5

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "e9d9195093bbcc8f670d7803f239ab42df34c07d7f6399fa428d7a9bbaa3302c"
def certificateSHA256 : String := "b8eee334db0d88c03560b39316e2e84a03ffc8ed8c9a87f4f1ce4e9f2afab4f4"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 10 → Fin 673 := ![
  296,
  425,
  426,
  478,
  479,
  581,
  606,
  609,
  663,
  671
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 10 → SparsePoly (Fin 68) := ![
  [{ coefficient := 1, powers := [(0, 1), (51, 1)] }, { coefficient := 1, powers := [(20, 1), (51, 1)] }, { coefficient := 1, powers := [(25, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (48, 1)] }, { coefficient := 1, powers := [(6, 1), (21, 1), (60, 1)] }, { coefficient := 1, powers := [(21, 1)] }, { coefficient := 1, powers := [(25, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (53, 1)] }, { coefficient := 1, powers := [(20, 1), (51, 1), (57, 1)] }, { coefficient := 1, powers := [(20, 1), (53, 1)] }, { coefficient := 1, powers := [(51, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (48, 1), (51, 1)] }, { coefficient := 1, powers := [(21, 1), (51, 1)] }, { coefficient := 1, powers := [(25, 1), (42, 1)] }, { coefficient := 1, powers := [(25, 1), (48, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (48, 1), (52, 1)] }, { coefficient := 1, powers := [(21, 1), (52, 1)] }, { coefficient := 1, powers := [(21, 1), (57, 1)] }, { coefficient := 1, powers := [(48, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (52, 1)] }, { coefficient := 1, powers := [(3, 1), (60, 1)] }, { coefficient := 1, powers := [(20, 1), (52, 1)] }, { coefficient := 1, powers := [(20, 1), (57, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (37, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1)] }, { coefficient := 1, powers := [(3, 1), (25, 1), (60, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1), (60, 1)] }, { coefficient := 1, powers := [(20, 1)] }, { coefficient := 1, powers := [(25, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (48, 1), (53, 1)] }, { coefficient := 1, powers := [(21, 1), (51, 1), (57, 1)] }, { coefficient := 1, powers := [(21, 1), (53, 1)] }, { coefficient := 1, powers := [(42, 1)] }, { coefficient := 1, powers := [(48, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(42, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(60, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 10 → SparsePoly (Fin 68) := ![
  [{ coefficient := -2, powers := [(48, 1), (52, 1), (63, 1)] }, { coefficient := -1, powers := [(48, 1), (57, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(51, 1), (57, 1), (63, 1)] }, { coefficient := -1, powers := [(53, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(48, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(52, 1), (63, 1)] }, { coefficient := 1, powers := [(57, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(51, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(42, 1), (63, 1)] }, { coefficient := 1, powers := [(48, 1), (51, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(42, 1), (52, 1), (63, 1)] }, { coefficient := -1, powers := [(42, 1), (57, 1), (63, 1)] }, { coefficient := 1, powers := [(48, 1), (51, 1), (52, 1), (63, 1)] }, { coefficient := 1, powers := [(48, 1), (51, 1), (57, 1), (63, 1)] }, { coefficient := 1, powers := [(48, 1), (53, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(63, 1)] }],
  [{ coefficient := -2, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (37, 1), (42, 1), (52, 1), (63, 1)] }, { coefficient := 1, powers := [(0, 1), (37, 1), (42, 1), (57, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (37, 1), (48, 1), (51, 1), (52, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (37, 1), (48, 1), (51, 1), (57, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (37, 1), (48, 1), (53, 1), (63, 1)] }, { coefficient := 1, powers := [(3, 1), (25, 1), (42, 1), (52, 1), (63, 1)] }, { coefficient := 1, powers := [(3, 1), (25, 1), (42, 1), (57, 1), (63, 1)] }, { coefficient := -1, powers := [(3, 1), (25, 1), (48, 1), (51, 1), (52, 1), (63, 1)] }, { coefficient := -1, powers := [(3, 1), (25, 1), (48, 1), (51, 1), (57, 1), (63, 1)] }, { coefficient := -1, powers := [(3, 1), (25, 1), (48, 1), (53, 1), (63, 1)] }, { coefficient := -1, powers := [(3, 1), (42, 1), (63, 1)] }, { coefficient := -1, powers := [(3, 1), (48, 1), (51, 1), (63, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1), (42, 1), (52, 1), (63, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1), (42, 1), (57, 1), (63, 1)] }, { coefficient := -1, powers := [(6, 1), (20, 1), (48, 1), (51, 1), (52, 1), (63, 1)] }, { coefficient := -1, powers := [(6, 1), (20, 1), (48, 1), (51, 1), (57, 1), (63, 1)] }, { coefficient := -1, powers := [(6, 1), (20, 1), (48, 1), (53, 1), (63, 1)] }, { coefficient := 1, powers := [(6, 1), (21, 1), (51, 1), (57, 1), (63, 1)] }, { coefficient := 1, powers := [(6, 1), (21, 1), (53, 1), (63, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
/-- Lean replays the exact selected-row integer certificate. -/
theorem constantIdentity :
    ∑ index, (multipliers index).toPoly *
      (selectedEquations index).toPoly = C (2 : ℤ) := by
  simp (config := { maxSteps := 1000000 })
    [Fin.sum_univ_succ, multipliers, selectedEquations,
    SparsePoly.toPoly, SparseTerm.toPoly]
  ring

/-- The selected rows have no common zero in a characteristic-zero ring. -/
theorem selectedHasNoCommonZero {R : Type*} [CommRing R] [Nontrivial R] [CharZero R]
    (values : Fin 68 → R) :
    ¬ ∀ index : Fin 10,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((2 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (2 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (2 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component37.SelectedLeafB4_1_2_4_5.selectedHasNoCommonZero

end Krenn.Component37.SelectedLeafB4_1_2_4_5
