import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component37.SelectedLeafB0_3_2_1

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "a8ba3f83d916f1d1c49404d224e7ecd7d298303b3d0ec4c394f86e15a01a8eb5"
def certificateSHA256 : String := "4c64ce0f7c33fa055d6e6bdf23f51122152d6e0801c2a164bf313c4cb1a4ce7b"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 7 → Fin 670 := ![
  315,
  471,
  478,
  609,
  658,
  663,
  667
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 7 → SparsePoly (Fin 66) := ![
  [{ coefficient := 1, powers := [(0, 1), (46, 1), (51, 1)] }, { coefficient := 1, powers := [(25, 1), (46, 1), (51, 1)] }, { coefficient := 1, powers := [(51, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1), (53, 1)] }, { coefficient := 1, powers := [(46, 1), (51, 1)] }, { coefficient := 1, powers := [(51, 1), (57, 1)] }, { coefficient := 1, powers := [(53, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (48, 1), (51, 1)] }, { coefficient := 1, powers := [(21, 1), (51, 1)] }, { coefficient := 1, powers := [(25, 1), (42, 1)] }, { coefficient := 1, powers := [(25, 1), (48, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (48, 1), (53, 1)] }, { coefficient := 1, powers := [(21, 1), (51, 1), (57, 1)] }, { coefficient := 1, powers := [(21, 1), (53, 1)] }, { coefficient := 1, powers := [(42, 1)] }, { coefficient := 1, powers := [(48, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(0, 1)] }],
  [{ coefficient := 1, powers := [(42, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(25, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 7 → SparsePoly (Fin 66) := ![
  [{ coefficient := 1, powers := [(21, 1), (46, 1), (63, 1)] }, { coefficient := 1, powers := [(21, 1), (57, 1), (63, 1)] }, { coefficient := -1, powers := [(48, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(21, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(57, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(63, 1)] }],
  [{ coefficient := -1, powers := [(21, 1), (46, 2), (51, 1), (63, 1)] }, { coefficient := -1, powers := [(21, 1), (46, 1), (51, 1), (57, 1), (63, 1)] }, { coefficient := 1, powers := [(21, 1), (46, 1), (53, 1), (63, 1)] }, { coefficient := -1, powers := [(42, 1), (57, 1), (63, 1)] }, { coefficient := 1, powers := [(46, 1), (48, 1), (51, 1), (63, 1)] }, { coefficient := 1, powers := [(48, 1), (51, 1), (57, 1), (63, 1)] }, { coefficient := -1, powers := [(48, 1), (53, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(21, 1), (46, 2), (51, 1), (63, 1)] }, { coefficient := -1, powers := [(21, 1), (46, 1), (51, 1), (57, 1), (63, 1)] }, { coefficient := 1, powers := [(42, 1), (57, 1), (63, 1)] }, { coefficient := 1, powers := [(46, 1), (48, 1), (51, 1), (63, 1)] }, { coefficient := 1, powers := [(48, 1), (51, 1), (57, 1), (63, 1)] }]
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
    ¬ ∀ index : Fin 7,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component37.SelectedLeafB0_3_2_1.selectedHasNoCommonZero

end Krenn.Component37.SelectedLeafB0_3_2_1
