import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component37.SelectedLeafB1_3_7

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "a0255d0a93519c5396fb55c78c1270fcb1222ef7765d593cc3cc7a7603a6e95f"
def certificateSHA256 : String := "5c37423d5cd62c5621c501fa2fed246b56cbf8ef11fd0b174e81e83f06c613c3"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 13 → Fin 667 := ![
  175,
  313,
  410,
  435,
  455,
  466,
  475,
  500,
  581,
  608,
  658,
  660,
  666
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 13 → SparsePoly (Fin 68) := ![
  [{ coefficient := 1, powers := [(18, 1), (20, 1)] }, { coefficient := 1, powers := [(18, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(20, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(44, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (25, 1), (41, 1)] }, { coefficient := 1, powers := [(18, 1), (25, 1), (46, 1)] }, { coefficient := 1, powers := [(18, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (52, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (52, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (57, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (41, 1)] }, { coefficient := 1, powers := [(29, 1), (46, 1)] }, { coefficient := 1, powers := [(29, 1), (52, 1)] }, { coefficient := 1, powers := [(29, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1), (54, 1)] }, { coefficient := 1, powers := [(20, 1), (44, 1), (54, 1)] }, { coefficient := 1, powers := [(20, 1), (58, 1)] }, { coefficient := 1, powers := [(26, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1), (52, 1)] }, { coefficient := 1, powers := [(41, 1), (44, 1)] }, { coefficient := 1, powers := [(44, 1), (52, 1)] }, { coefficient := 1, powers := [(47, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (29, 1), (60, 1)] }, { coefficient := 1, powers := [(23, 1), (52, 1)] }, { coefficient := 1, powers := [(23, 1), (57, 1)] }, { coefficient := 1, powers := [(29, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (52, 1)] }, { coefficient := 1, powers := [(3, 1), (60, 1)] }, { coefficient := 1, powers := [(20, 1), (52, 1)] }, { coefficient := 1, powers := [(20, 1), (57, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (41, 1), (58, 1)] }, { coefficient := 1, powers := [(0, 1), (47, 1), (54, 1)] }, { coefficient := 1, powers := [(26, 1), (41, 1), (44, 1)] }, { coefficient := 1, powers := [(26, 1), (47, 1)] }, { coefficient := 1, powers := [(44, 1), (54, 1)] }, { coefficient := 1, powers := [(58, 1)] }],
  [{ coefficient := 1, powers := [(0, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(58, 1), (67, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 13 → SparsePoly (Fin 68) := ![
  [{ coefficient := -1, powers := [(20, 1), (29, 1), (41, 1), (58, 1), (62, 1), (67, 1)] }, { coefficient := -1, powers := [(20, 1), (29, 1), (46, 1), (58, 1), (62, 1), (67, 1)] }],
  [{ coefficient := -1, powers := [(54, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (29, 1), (58, 1), (62, 1), (67, 1)] }],
  [{ coefficient := -1, powers := [(20, 1), (58, 1), (62, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (20, 2), (58, 1), (62, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(52, 1), (67, 1)] }],
  [{ coefficient := -1, powers := [(26, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (20, 1), (58, 1), (62, 1), (67, 1)] }],
  [{ coefficient := -1, powers := [(18, 1), (20, 1), (29, 1), (58, 1), (62, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(67, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (20, 1), (29, 1), (52, 1), (58, 1), (62, 1), (67, 1)] }, { coefficient := 1, powers := [(26, 1), (47, 1), (52, 1), (67, 1)] }, { coefficient := -1, powers := [(41, 1), (58, 1), (67, 1)] }, { coefficient := -1, powers := [(47, 1), (54, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (52, 1), (58, 1), (67, 1)] }],
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
    (values : Fin 68 → R) :
    ¬ ∀ index : Fin 13,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component37.SelectedLeafB1_3_7.selectedHasNoCommonZero

end Krenn.Component37.SelectedLeafB1_3_7
