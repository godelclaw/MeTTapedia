import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component37.SelectedLeafB1_3_6_1

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "036de4288c6bed4ce9037d82d8a0451d9c477bb8a03612459bc0b23ebfc913c3"
def certificateSHA256 : String := "19eacde89d1a52ecb675b398fd936d16db081426ccfde7d2ef73a02b68a59ad8"

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
def selectedEquations : Fin 7 → SparsePoly (Fin 68) := ![
  [{ coefficient := 1, powers := [(0, 1), (46, 1), (51, 1)] }, { coefficient := 1, powers := [(25, 1), (46, 1), (51, 1)] }, { coefficient := 1, powers := [(51, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1), (53, 1)] }, { coefficient := 1, powers := [(46, 1), (51, 1)] }, { coefficient := 1, powers := [(51, 1), (57, 1)] }, { coefficient := 1, powers := [(53, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (48, 1), (51, 1)] }, { coefficient := 1, powers := [(21, 1), (51, 1)] }, { coefficient := 1, powers := [(25, 1), (42, 1)] }, { coefficient := 1, powers := [(25, 1), (48, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (48, 1), (53, 1)] }, { coefficient := 1, powers := [(21, 1), (51, 1), (57, 1)] }, { coefficient := 1, powers := [(21, 1), (53, 1)] }, { coefficient := 1, powers := [(42, 1)] }, { coefficient := 1, powers := [(48, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(0, 1)] }],
  [{ coefficient := 1, powers := [(42, 1), (64, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(25, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 7 → SparsePoly (Fin 68) := ![
  [{ coefficient := 1, powers := [(21, 1), (46, 1), (64, 1)] }, { coefficient := 1, powers := [(21, 1), (57, 1), (64, 1)] }, { coefficient := -1, powers := [(48, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(21, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(57, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(64, 1)] }],
  [{ coefficient := -1, powers := [(21, 1), (46, 2), (51, 1), (64, 1)] }, { coefficient := -1, powers := [(21, 1), (46, 1), (51, 1), (57, 1), (64, 1)] }, { coefficient := 1, powers := [(21, 1), (46, 1), (53, 1), (64, 1)] }, { coefficient := -1, powers := [(42, 1), (57, 1), (64, 1)] }, { coefficient := 1, powers := [(46, 1), (48, 1), (51, 1), (64, 1)] }, { coefficient := 1, powers := [(48, 1), (51, 1), (57, 1), (64, 1)] }, { coefficient := -1, powers := [(48, 1), (53, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(21, 1), (46, 2), (51, 1), (64, 1)] }, { coefficient := -1, powers := [(21, 1), (46, 1), (51, 1), (57, 1), (64, 1)] }, { coefficient := 1, powers := [(42, 1), (57, 1), (64, 1)] }, { coefficient := 1, powers := [(46, 1), (48, 1), (51, 1), (64, 1)] }, { coefficient := 1, powers := [(48, 1), (51, 1), (57, 1), (64, 1)] }]
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
    (values : Fin 68 → R) :
    ¬ ∀ index : Fin 7,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component37.SelectedLeafB1_3_6_1.selectedHasNoCommonZero

end Krenn.Component37.SelectedLeafB1_3_6_1
