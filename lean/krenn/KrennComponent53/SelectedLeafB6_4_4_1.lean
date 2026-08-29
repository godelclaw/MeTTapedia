import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component53.SelectedLeafB6_4_4_1

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "27ef616eefd991ed4f6d8c80b7dfe273bdddfd40a79fb52c52e5a9606f16d2f5"
def certificateSHA256 : String := "09cece6a3f1d13ed66fc6a65a7ec4f6c91e185fdf274448b79c23023d4bf91ca"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 6 → Fin 649 := ![
  22,
  198,
  357,
  449,
  641,
  648
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 6 → SparsePoly (Fin 66) := ![
  [{ coefficient := 1, powers := [(21, 1), (22, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (22, 1)] }, { coefficient := 1, powers := [(20, 1), (26, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (47, 1)] }, { coefficient := 1, powers := [(21, 1), (42, 1)] }, { coefficient := 1, powers := [(21, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (26, 1), (47, 1)] }, { coefficient := 1, powers := [(21, 1), (26, 1), (42, 1)] }, { coefficient := 1, powers := [(21, 1)] }],
  [{ coefficient := 1, powers := [(42, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (65, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 6 → SparsePoly (Fin 66) := ![
  [{ coefficient := -1, powers := [(51, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(47, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(65, 1)] }],
  [{ coefficient := -1, powers := [(21, 1), (22, 1), (65, 1)] }, { coefficient := -1, powers := [(21, 1), (26, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [] }]
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
    (values : Fin 66 → R) :
    ¬ ∀ index : Fin 6,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component53.SelectedLeafB6_4_4_1.selectedHasNoCommonZero

end Krenn.Component53.SelectedLeafB6_4_4_1
