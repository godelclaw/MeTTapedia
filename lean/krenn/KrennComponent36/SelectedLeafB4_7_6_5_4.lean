import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component36.SelectedLeafB4_7_6_5_4

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "16be899554d413f6a9c280104f8f93697ee14f6d7793e1b29608d1ce5402347c"
def certificateSHA256 : String := "76b78b05af1d7b778b955f3c017b75524079e279bd38320a8c42eff3eab202cf"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 5 → Fin 678 := ![
  441,
  478,
  668,
  672,
  676
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 5 → SparsePoly (Fin 71) := ![
  [{ coefficient := 1, powers := [(0, 1), (47, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1), (60, 1)] }, { coefficient := 1, powers := [(20, 1)] }, { coefficient := 1, powers := [(24, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1), (50, 1)] }, { coefficient := 1, powers := [(20, 1), (50, 1)] }, { coefficient := 1, powers := [(24, 1), (41, 1)] }, { coefficient := 1, powers := [(24, 1), (47, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(41, 1), (65, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(24, 1), (68, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(60, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 5 → SparsePoly (Fin 71) := ![
  [{ coefficient := -1, powers := [(50, 1), (65, 1), (68, 1)] }],
  [{ coefficient := 1, powers := [(65, 1), (68, 1)] }],
  [{ coefficient := -1, powers := [(24, 1), (68, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(6, 1), (20, 1), (50, 1), (65, 1), (68, 1)] }]
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
    (values : Fin 71 → R) :
    ¬ ∀ index : Fin 5,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component36.SelectedLeafB4_7_6_5_4.selectedHasNoCommonZero

end Krenn.Component36.SelectedLeafB4_7_6_5_4
