import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component15.SelectedLeafB2_6_3

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "4ae3a024944f4545f48da0f2391546f04c9876c1db709db57d83b26032c15cec"
def certificateSHA256 : String := "9ac87293abcd164b51026594d4d9f16226f362faec704b1f490f4e3c174eedbe"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 7 → Fin 595 := ![
  0,
  4,
  234,
  475,
  586,
  587,
  594
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 7 → SparsePoly (Fin 62) := ![
  [{ coefficient := 1, powers := [(1, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(37, 1), (40, 1)] }, { coefficient := 1, powers := [(40, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (37, 1), (53, 1)] }, { coefficient := 1, powers := [(23, 1), (37, 1), (40, 1)] }, { coefficient := 1, powers := [(40, 1), (49, 1)] }, { coefficient := 1, powers := [(53, 1)] }],
  [{ coefficient := 1, powers := [(0, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (57, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(53, 1), (61, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 7 → SparsePoly (Fin 62) := ![
  [{ coefficient := 1, powers := [(23, 1), (48, 1), (57, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(40, 1), (57, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(23, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(61, 1)] }],
  [{ coefficient := -1, powers := [(37, 1), (53, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(23, 1), (40, 1), (48, 1), (61, 1)] }, { coefficient := 1, powers := [(40, 1), (49, 1), (61, 1)] }],
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
    (values : Fin 62 → R) :
    ¬ ∀ index : Fin 7,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component15.SelectedLeafB2_6_3.selectedHasNoCommonZero

end Krenn.Component15.SelectedLeafB2_6_3
