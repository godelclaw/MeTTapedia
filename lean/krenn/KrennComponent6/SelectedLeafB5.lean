import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component6.SelectedLeafB5

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "c28ee020b5da00adb112cd5b1902e6cc953c81ab51e75fd2c5562c1057350e51"
def certificateSHA256 : String := "a30fe8543eaa79daa4bebb56daf846d0472e7dd25ff59ac1d584aef02ad9e7e6"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 32 → Fin 606 := ![
  0,
  1,
  3,
  5,
  10,
  18,
  22,
  25,
  28,
  31,
  193,
  211,
  228,
  240,
  261,
  369,
  371,
  372,
  375,
  385,
  386,
  387,
  394,
  398,
  399,
  406,
  541,
  601,
  602,
  603,
  604,
  605
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 32 → SparsePoly (Fin 61) := ![
  [{ coefficient := 1, powers := [(2, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (19, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(28, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (55, 1)] }, { coefficient := 1, powers := [(26, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(41, 1), (44, 1)] }, { coefficient := 1, powers := [(44, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (37, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (30, 1), (57, 1)] }, { coefficient := 1, powers := [(30, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (24, 1), (57, 1)] }, { coefficient := 1, powers := [(24, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1)] }, { coefficient := 1, powers := [(20, 1), (44, 1)] }, { coefficient := 1, powers := [(25, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (52, 1)] }, { coefficient := 1, powers := [(19, 1), (52, 1)] }, { coefficient := 1, powers := [(26, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (47, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (58, 1)] }, { coefficient := 1, powers := [(13, 1), (55, 1)] }, { coefficient := 1, powers := [(18, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (52, 1)] }, { coefficient := 1, powers := [(30, 1), (42, 1)] }, { coefficient := 1, powers := [(33, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (55, 1)] }, { coefficient := 1, powers := [(30, 1), (47, 1)] }, { coefficient := 1, powers := [(36, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (41, 1), (55, 1)] }, { coefficient := 1, powers := [(26, 1), (41, 1), (44, 1)] }, { coefficient := 1, powers := [(55, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1), (51, 1)] }, { coefficient := 1, powers := [(20, 1), (44, 1), (51, 1)] }, { coefficient := 1, powers := [(47, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (41, 1), (55, 1)] }, { coefficient := 1, powers := [(4, 1), (32, 1), (55, 1)] }, { coefficient := 1, powers := [(11, 1), (22, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (42, 1), (54, 1)] }, { coefficient := 1, powers := [(7, 1), (35, 1), (42, 1)] }, { coefficient := 1, powers := [(16, 1), (28, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (39, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (57, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (51, 1)] }, { coefficient := 1, powers := [(22, 1), (54, 1)] }, { coefficient := 1, powers := [(28, 1), (41, 1)] }, { coefficient := 1, powers := [(28, 1), (46, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1)] }, { coefficient := 1, powers := [(35, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (38, 1), (57, 1)] }, { coefficient := 1, powers := [(1, 1), (41, 1), (54, 1)] }, { coefficient := 1, powers := [(1, 1), (46, 1), (51, 1)] }, { coefficient := 1, powers := [(4, 1), (28, 1), (57, 1)] }, { coefficient := 1, powers := [(4, 1), (32, 1), (54, 1)] }, { coefficient := 1, powers := [(4, 1), (35, 1), (51, 1)] }, { coefficient := 1, powers := [(7, 1), (22, 1), (57, 1)] }, { coefficient := 1, powers := [(7, 1), (32, 1), (46, 1)] }, { coefficient := 1, powers := [(7, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(11, 1), (22, 1), (54, 1)] }, { coefficient := 1, powers := [(11, 1), (28, 1), (46, 1)] }, { coefficient := 1, powers := [(11, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1), (51, 1)] }, { coefficient := 1, powers := [(16, 1), (28, 1), (41, 1)] }, { coefficient := 1, powers := [(16, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (39, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (42, 1), (55, 1)] }, { coefficient := 1, powers := [(2, 1), (47, 1), (52, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1), (52, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (58, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (47, 1)] }, { coefficient := 1, powers := [(8, 1), (36, 1), (42, 1)] }, { coefficient := 1, powers := [(13, 1), (24, 1), (55, 1)] }, { coefficient := 1, powers := [(13, 1), (30, 1), (47, 1)] }, { coefficient := 1, powers := [(13, 1), (36, 1), (39, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (52, 1)] }, { coefficient := 1, powers := [(18, 1), (30, 1), (42, 1)] }, { coefficient := 1, powers := [(18, 1), (33, 1), (39, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (59, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (60, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 32 → SparsePoly (Fin 61) := ![
  [{ coefficient := 1, powers := [(2, 1), (7, 1), (32, 1), (42, 1), (55, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (11, 1), (28, 1), (42, 1), (55, 1), (60, 1)] }, { coefficient := -1, powers := [(2, 1), (16, 1), (28, 1), (42, 1), (55, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (4, 1), (35, 1), (42, 1), (55, 1), (60, 1)] }, { coefficient := -1, powers := [(2, 1), (7, 1), (19, 1), (35, 1), (42, 1), (55, 1), (59, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (25, 1), (33, 1), (47, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (30, 1), (58, 1)] }, { coefficient := 1, powers := [(30, 1), (37, 1), (58, 1)] }, { coefficient := -1, powers := [(33, 1), (37, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (24, 1), (58, 1)] }, { coefficient := 1, powers := [(24, 1), (37, 1), (58, 1)] }, { coefficient := -1, powers := [(36, 1), (37, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (35, 1), (38, 1), (42, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (35, 1), (38, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (52, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (26, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (7, 1), (42, 1), (57, 1)] }, { coefficient := -1, powers := [(2, 1), (16, 1), (42, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (4, 1), (55, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (16, 1), (55, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (7, 1), (35, 1), (42, 1), (51, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (7, 1), (26, 1), (35, 1), (42, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (33, 1), (55, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (36, 1), (42, 1), (60, 1)] }, { coefficient := 1, powers := [(39, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (33, 1), (51, 1)] }],
  [{ coefficient := -1, powers := [(18, 1), (24, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(52, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (24, 1), (59, 1)] }, { coefficient := -1, powers := [(24, 1)] }],
  [{ coefficient := 1, powers := [(18, 1)] }],
  [{ coefficient := 1, powers := [(13, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (7, 1), (35, 1), (42, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (33, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (42, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (55, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(37, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (16, 1), (42, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (42, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(2, 1), (7, 1), (35, 1), (41, 1), (42, 1), (55, 1)] }, { coefficient := -1, powers := [(8, 1), (24, 1), (58, 1)] }, { coefficient := -1, powers := [(13, 1), (24, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (42, 1), (55, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (42, 1), (46, 1), (51, 1), (55, 1)] }, { coefficient := 1, powers := [(2, 1), (42, 1), (54, 1), (55, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (4, 1), (35, 1), (42, 1), (51, 1), (55, 1)] }, { coefficient := 1, powers := [(2, 1), (7, 1), (19, 1), (35, 1), (42, 1), (51, 1), (55, 1), (59, 1)] }, { coefficient := -1, powers := [(2, 1), (7, 1), (32, 1), (42, 1), (46, 1), (55, 1)] }, { coefficient := -1, powers := [(2, 1), (11, 1), (28, 1), (42, 1), (46, 1), (55, 1)] }, { coefficient := 1, powers := [(2, 1), (16, 1), (28, 1), (42, 1), (46, 1), (55, 1)] }, { coefficient := -1, powers := [(5, 1), (33, 1), (37, 1), (55, 1), (57, 1)] }, { coefficient := -1, powers := [(5, 1), (33, 1), (55, 1)] }, { coefficient := -1, powers := [(8, 1), (25, 1), (33, 1), (47, 1), (51, 1)] }, { coefficient := -1, powers := [(8, 1), (36, 1), (37, 1), (42, 1), (57, 1)] }, { coefficient := -1, powers := [(8, 1), (36, 1), (42, 1)] }]
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
    (values : Fin 61 → R) :
    ¬ ∀ index : Fin 32,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component6.SelectedLeafB5.selectedHasNoCommonZero

end Krenn.Component6.SelectedLeafB5
