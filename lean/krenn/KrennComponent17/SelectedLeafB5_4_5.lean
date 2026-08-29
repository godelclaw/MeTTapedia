import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component17.SelectedLeafB5_4_5

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "6a33552f05f98585681c660393ce07c9175a85b0006d73641ef65ec45d4272ac"
def certificateSHA256 : String := "d5a0bddad0efe2bd98cdd942f8c8799e8a3c4e44bfc8338732244282478a6ba3"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 13 → Fin 611 := ![
  27,
  330,
  425,
  432,
  459,
  550,
  572,
  602,
  604,
  606,
  608,
  609,
  610
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 13 → SparsePoly (Fin 64) := ![
  [{ coefficient := 1, powers := [(17, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1), (50, 1)] }, { coefficient := 1, powers := [(19, 1), (43, 1), (50, 1)] }, { coefficient := 1, powers := [(43, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (51, 1)] }, { coefficient := 1, powers := [(3, 1), (25, 1), (57, 1)] }, { coefficient := 1, powers := [(19, 1), (51, 1)] }, { coefficient := 1, powers := [(25, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (50, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (50, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (54, 1)] }, { coefficient := 1, powers := [(17, 1), (28, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1), (50, 1)] }, { coefficient := 1, powers := [(40, 1), (43, 1)] }, { coefficient := 1, powers := [(43, 1), (50, 1)] }, { coefficient := 1, powers := [(45, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (50, 1)] }, { coefficient := 1, powers := [(3, 1), (57, 1)] }, { coefficient := 1, powers := [(19, 1), (50, 1)] }, { coefficient := 1, powers := [(19, 1), (54, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (40, 1), (55, 1)] }, { coefficient := 1, powers := [(0, 1), (45, 1), (51, 1)] }, { coefficient := 1, powers := [(25, 1), (40, 1), (43, 1)] }, { coefficient := 1, powers := [(25, 1), (45, 1)] }, { coefficient := 1, powers := [(43, 1), (51, 1)] }, { coefficient := 1, powers := [(55, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (59, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (60, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(40, 1)] }],
  [{ coefficient := 1, powers := [(53, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(54, 1)] }],
  [{ coefficient := 1, powers := [(55, 1), (63, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 13 → SparsePoly (Fin 64) := ![
  [{ coefficient := 1, powers := [(0, 1), (22, 1), (50, 1), (60, 1), (62, 1)] }, { coefficient := 1, powers := [(0, 1), (28, 1), (60, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (25, 1), (50, 1), (59, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (51, 1), (59, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1), (50, 1), (59, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (25, 1), (59, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (51, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (25, 1), (43, 1), (50, 1), (59, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (50, 1), (63, 1)] }, { coefficient := 1, powers := [(0, 1), (59, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (25, 1), (45, 1), (50, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (45, 1), (51, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (50, 1)] }],
  [{ coefficient := -1, powers := [(0, 2), (50, 1), (55, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 2), (55, 1), (59, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (25, 1), (43, 1), (50, 1), (63, 1)] }, { coefficient := 1, powers := [(0, 1), (43, 1), (51, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (17, 1), (22, 1), (50, 1), (60, 1)] }, { coefficient := -1, powers := [(0, 1), (17, 1), (28, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (17, 1), (22, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (19, 1), (25, 1), (43, 1), (50, 1), (59, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (50, 1)] }, { coefficient := -1, powers := [(0, 1), (59, 1)] }]
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
    (values : Fin 64 → R) :
    ¬ ∀ index : Fin 13,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component17.SelectedLeafB5_4_5.selectedHasNoCommonZero

end Krenn.Component17.SelectedLeafB5_4_5
