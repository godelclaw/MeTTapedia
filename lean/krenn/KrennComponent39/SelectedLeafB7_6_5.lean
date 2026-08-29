import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component39.SelectedLeafB7_6_5

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "aa5adf237deaf673e9590be4069a74e3fb8e5b9c8967f3e1b6d1f7818fb4157e"
def certificateSHA256 : String := "8cedbb900ecd3ebee84ab99f1435f9d15a3e4a9f8a255e1ce163df5865b25dac"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 5 → Fin 670 := ![
  1,
  285,
  662,
  664,
  669
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 5 → SparsePoly (Fin 68) := ![
  [{ coefficient := 1, powers := [(1, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (24, 1), (42, 1), (50, 1)] }, { coefficient := 1, powers := [(1, 1), (38, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(38, 1), (64, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(57, 1), (67, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 5 → SparsePoly (Fin 68) := ![
  [{ coefficient := -1, powers := [(24, 1), (50, 1), (62, 1), (64, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(62, 1), (64, 1), (67, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(1, 1), (57, 1), (62, 1), (67, 1)] }],
  [{ coefficient := -1, powers := [(1, 1), (62, 1)] }]
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
    ¬ ∀ index : Fin 5,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component39.SelectedLeafB7_6_5.selectedHasNoCommonZero

end Krenn.Component39.SelectedLeafB7_6_5
