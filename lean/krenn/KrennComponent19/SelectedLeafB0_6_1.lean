import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component19.SelectedLeafB0_6_1

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "6f1489190ea6730559c1f2f3c5467f0de9bbe48a98f08b3c0a8ef319febb640f"
def certificateSHA256 : String := "6b022894b3931e4b73b6af1d6e4889ce27238ebb841745c9a1f24007d8ce0d0a"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 8 → Fin 672 := ![
  324,
  413,
  452,
  583,
  610,
  663,
  670,
  671
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 8 → SparsePoly (Fin 65) := ![
  [{ coefficient := 1, powers := [(0, 1), (46, 1), (53, 1)] }, { coefficient := 1, powers := [(21, 1), (46, 1), (53, 1)] }, { coefficient := 1, powers := [(46, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (54, 1)] }, { coefficient := 1, powers := [(3, 1), (27, 1), (60, 1)] }, { coefficient := 1, powers := [(21, 1), (54, 1)] }, { coefficient := 1, powers := [(27, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (49, 1), (53, 1)] }, { coefficient := 1, powers := [(43, 1), (46, 1)] }, { coefficient := 1, powers := [(46, 1), (53, 1)] }, { coefficient := 1, powers := [(49, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (53, 1)] }, { coefficient := 1, powers := [(3, 1), (60, 1)] }, { coefficient := 1, powers := [(21, 1), (53, 1)] }, { coefficient := 1, powers := [(21, 1), (57, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1), (58, 1)] }, { coefficient := 1, powers := [(0, 1), (49, 1), (54, 1)] }, { coefficient := 1, powers := [(27, 1), (43, 1), (46, 1)] }, { coefficient := 1, powers := [(27, 1), (49, 1)] }, { coefficient := 1, powers := [(46, 1), (54, 1)] }, { coefficient := 1, powers := [(58, 1)] }],
  [{ coefficient := 1, powers := [(0, 1)] }],
  [{ coefficient := 1, powers := [(57, 1)] }],
  [{ coefficient := 1, powers := [(58, 1), (64, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 8 → SparsePoly (Fin 65) := ![
  [{ coefficient := 1, powers := [(27, 1), (53, 1), (64, 1)] }, { coefficient := -1, powers := [(54, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(46, 1), (53, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(27, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(27, 1), (46, 1), (53, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(64, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (49, 1), (53, 1), (64, 1)] }, { coefficient := -1, powers := [(43, 1), (58, 1), (64, 1)] }, { coefficient := -1, powers := [(49, 1), (54, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (27, 1), (46, 1), (53, 1), (64, 1)] }],
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
    (values : Fin 65 → R) :
    ¬ ∀ index : Fin 8,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component19.SelectedLeafB0_6_1.selectedHasNoCommonZero

end Krenn.Component19.SelectedLeafB0_6_1
