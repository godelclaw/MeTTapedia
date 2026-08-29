import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component6.SelectedLeafB7

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "1b3d8734a3fc3f9036e62645abeb47d7b1f7531fab8a2ae7dbcd54bc5c0efe0c"
def certificateSHA256 : String := "d34747aaaa8ccbcae4231833b2ab80fe2e053ebf2d80444260fcfb5dfc89ba2a"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 26 → Fin 606 := ![
  1,
  3,
  5,
  20,
  22,
  25,
  165,
  167,
  173,
  217,
  228,
  240,
  261,
  369,
  371,
  372,
  375,
  385,
  386,
  394,
  397,
  406,
  602,
  603,
  604,
  605
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 26 → SparsePoly (Fin 62) := ![
  [{ coefficient := 1, powers := [(2, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (19, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (52, 1)] }, { coefficient := 1, powers := [(16, 1), (21, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (44, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (58, 1)] }, { coefficient := 1, powers := [(44, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (37, 1), (58, 1)] }, { coefficient := 1, powers := [(1, 1), (44, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (37, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (30, 1), (57, 1)] }, { coefficient := 1, powers := [(30, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (24, 1), (57, 1)] }, { coefficient := 1, powers := [(24, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1)] }, { coefficient := 1, powers := [(20, 1), (44, 1)] }, { coefficient := 1, powers := [(25, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (52, 1)] }, { coefficient := 1, powers := [(19, 1), (52, 1)] }, { coefficient := 1, powers := [(26, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (47, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (58, 1)] }, { coefficient := 1, powers := [(13, 1), (55, 1)] }, { coefficient := 1, powers := [(18, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (52, 1)] }, { coefficient := 1, powers := [(30, 1), (42, 1)] }, { coefficient := 1, powers := [(33, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (55, 1)] }, { coefficient := 1, powers := [(30, 1), (47, 1)] }, { coefficient := 1, powers := [(36, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1), (51, 1)] }, { coefficient := 1, powers := [(20, 1), (44, 1), (51, 1)] }, { coefficient := 1, powers := [(47, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (39, 1), (58, 1)] }, { coefficient := 1, powers := [(1, 1), (42, 1), (55, 1)] }, { coefficient := 1, powers := [(1, 1), (47, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (39, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (57, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (39, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (42, 1), (55, 1)] }, { coefficient := 1, powers := [(2, 1), (47, 1), (52, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1), (52, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (58, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (47, 1)] }, { coefficient := 1, powers := [(8, 1), (36, 1), (42, 1)] }, { coefficient := 1, powers := [(13, 1), (24, 1), (55, 1)] }, { coefficient := 1, powers := [(13, 1), (30, 1), (47, 1)] }, { coefficient := 1, powers := [(13, 1), (36, 1), (39, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (52, 1)] }, { coefficient := 1, powers := [(18, 1), (30, 1), (42, 1)] }, { coefficient := 1, powers := [(18, 1), (33, 1), (39, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (59, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1), (60, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (61, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 26 → SparsePoly (Fin 62) := ![
  [{ coefficient := 1, powers := [(8, 1), (25, 1), (33, 1), (47, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (30, 1), (58, 1)] }, { coefficient := 1, powers := [(30, 1), (37, 1), (58, 1)] }, { coefficient := -1, powers := [(33, 1), (37, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (24, 1), (58, 1)] }, { coefficient := 1, powers := [(24, 1), (37, 1), (58, 1)] }, { coefficient := -1, powers := [(36, 1), (37, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (21, 1), (47, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (52, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (23, 1), (39, 1), (57, 1), (61, 1)] }, { coefficient := 1, powers := [(24, 1), (26, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (47, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (39, 1), (49, 1), (57, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(1, 1), (2, 1), (39, 1), (57, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 2), (39, 1), (57, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (39, 1), (57, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (39, 1), (58, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (55, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (36, 1), (42, 1), (61, 1)] }, { coefficient := 1, powers := [(39, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (33, 1), (51, 1)] }],
  [{ coefficient := -1, powers := [(18, 1), (24, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(52, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (24, 1), (59, 1)] }, { coefficient := -1, powers := [(24, 1)] }],
  [{ coefficient := 1, powers := [(18, 1)] }],
  [{ coefficient := 1, powers := [(13, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (33, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(37, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(8, 1), (24, 1), (58, 1)] }, { coefficient := -1, powers := [(13, 1), (24, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (6, 1), (39, 1), (57, 1), (58, 1)] }, { coefficient := -1, powers := [(2, 1), (37, 1), (39, 1), (57, 1), (58, 1)] }, { coefficient := -1, powers := [(2, 1), (39, 1), (58, 1)] }, { coefficient := -1, powers := [(2, 1), (42, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (6, 1), (39, 1), (57, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (37, 1), (39, 1), (57, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (39, 1), (58, 1)] }, { coefficient := -1, powers := [(5, 1), (33, 1), (37, 1), (55, 1), (57, 1)] }, { coefficient := -1, powers := [(5, 1), (33, 1), (55, 1)] }, { coefficient := -1, powers := [(8, 1), (25, 1), (33, 1), (47, 1), (51, 1)] }, { coefficient := -1, powers := [(8, 1), (36, 1), (37, 1), (42, 1), (57, 1)] }, { coefficient := -1, powers := [(8, 1), (36, 1), (42, 1)] }]
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
    ¬ ∀ index : Fin 26,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component6.SelectedLeafB7.selectedHasNoCommonZero

end Krenn.Component6.SelectedLeafB7
