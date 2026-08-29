import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component16.SelectedLeafB6_6_1

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "f54f7da67ab6a3561577e1afd7e9da84ffa3d7bc493eaa7b3999ffc8423c85e2"
def certificateSHA256 : String := "cce75df239d993c2df7a2492d399a42b429a59d77634d20e637d8e4825944807"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 5 → Fin 671 := ![
  36,
  277,
  663,
  665,
  670
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 5 → SparsePoly (Fin 67) := ![
  [{ coefficient := 1, powers := [(1, 1), (27, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (27, 1), (45, 1), (52, 1)] }, { coefficient := 1, powers := [(1, 1), (41, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(41, 1), (64, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(58, 1), (66, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 5 → SparsePoly (Fin 67) := ![
  [{ coefficient := -1, powers := [(45, 1), (63, 1), (64, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(63, 1), (64, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(41, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(1, 1), (41, 1), (63, 1), (64, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
/-- Lean replays the exact selected-row integer certificate. -/
theorem constantIdentity :
    ∑ index, (multipliers index).toPoly *
      (selectedEquations index).toPoly = C (1 : ℤ) := by
  simp (config := { maxSteps := 1000000 })
    [Fin.sum_univ_succ, multipliers, selectedEquations,
    SparsePoly.toPoly, SparseTerm.toPoly]
  ring

/-- The selected rows have no common zero in a characteristic-zero ring. -/
theorem selectedHasNoCommonZero {R : Type*} [CommRing R] [Nontrivial R] [CharZero R]
    (values : Fin 67 → R) :
    ¬ ∀ index : Fin 5,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component16.SelectedLeafB6_6_1.selectedHasNoCommonZero

end Krenn.Component16.SelectedLeafB6_6_1
