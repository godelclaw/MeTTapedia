import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component24.SelectedLeafB5_7_5

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "3a60c78eedf95fa29ae9a4894399039a61075eb5f107ed26af4826c71a9dc3b4"
def certificateSHA256 : String := "3021ca420c4af5d7450b8ee850d1061e8176a3f6f07a2caad05c4c5d0acfda51"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 7 → Fin 673 := ![
  18,
  19,
  443,
  614,
  669,
  671,
  672
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 7 → SparsePoly (Fin 69) := ![
  [{ coefficient := 1, powers := [(20, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (54, 1)] }, { coefficient := 1, powers := [(20, 1), (51, 1), (57, 1)] }, { coefficient := 1, powers := [(20, 1), (54, 1)] }, { coefficient := 1, powers := [(51, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (48, 1), (54, 1)] }, { coefficient := 1, powers := [(21, 1), (51, 1), (57, 1)] }, { coefficient := 1, powers := [(21, 1), (54, 1)] }, { coefficient := 1, powers := [(43, 1)] }, { coefficient := 1, powers := [(48, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(43, 1), (66, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(57, 1)] }],
  [{ coefficient := 1, powers := [(58, 1), (68, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 7 → SparsePoly (Fin 69) := ![
  [{ coefficient := 1, powers := [(48, 1), (54, 1), (66, 1), (68, 1)] }],
  [{ coefficient := -1, powers := [(54, 1), (66, 1), (68, 1)] }],
  [{ coefficient := -1, powers := [(48, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(66, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(0, 1), (43, 1), (66, 1)] }, { coefficient := 1, powers := [(20, 1), (48, 1), (51, 1), (66, 1)] }, { coefficient := -1, powers := [(21, 1), (51, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(20, 1), (48, 1), (54, 1), (66, 1)] }, { coefficient := 1, powers := [(21, 1), (54, 1), (66, 1)] }]
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
    (values : Fin 69 → R) :
    ¬ ∀ index : Fin 7,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component24.SelectedLeafB5_7_5.selectedHasNoCommonZero

end Krenn.Component24.SelectedLeafB5_7_5
