import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component24.SelectedLeafB6_6_6_7

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "e96ad5be0920e07125ef65a803e18a2bdc841c923d315b1dcda113d83e040c57"
def certificateSHA256 : String := "8e55c42dc51469e2f38c87499eefdc21ba17c8e1a00f712fd4c120100cf04310"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 6 → Fin 676 := ![
  50,
  132,
  164,
  667,
  668,
  675
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 6 → SparsePoly (Fin 71) := ![
  [{ coefficient := 1, powers := [(9, 1), (31, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (31, 1)] }, { coefficient := 1, powers := [(31, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(31, 1), (42, 1)] }, { coefficient := 1, powers := [(31, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(41, 1), (64, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(42, 1), (65, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(31, 1), (70, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 6 → SparsePoly (Fin 71) := ![
  [{ coefficient := 1, powers := [(64, 1), (65, 1), (70, 1)] }],
  [{ coefficient := -1, powers := [(46, 1), (64, 1), (65, 1), (70, 1)] }],
  [{ coefficient := 1, powers := [(65, 1), (70, 1)] }],
  [{ coefficient := 1, powers := [(46, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(41, 1), (46, 1), (64, 1), (65, 1)] }, { coefficient := -1, powers := [(42, 1), (65, 1)] }, { coefficient := -1, powers := [(46, 1), (65, 1)] }]
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
    ¬ ∀ index : Fin 6,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component24.SelectedLeafB6_6_6_7.selectedHasNoCommonZero

end Krenn.Component24.SelectedLeafB6_6_6_7
