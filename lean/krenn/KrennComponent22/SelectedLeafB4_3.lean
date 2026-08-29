import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component22.SelectedLeafB4_3

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "10e016dc33b85acfcb5f64509b50143a564347e7f27b3a4a228fdea66d7f0c9e"
def certificateSHA256 : String := "61854717e6f3cabec0acbd3137ede885f6dff7437d91f31412e16e924d98b22b"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 33 → Fin 642 := ![
  2,
  3,
  11,
  12,
  20,
  184,
  191,
  192,
  193,
  194,
  204,
  208,
  225,
  236,
  237,
  278,
  345,
  351,
  353,
  363,
  364,
  371,
  389,
  390,
  462,
  468,
  557,
  558,
  583,
  635,
  638,
  640,
  641
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 33 → SparsePoly (Fin 63) := ![
  [{ coefficient := 1, powers := [(5, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (23, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (17, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (45, 1)] }, { coefficient := 1, powers := [(12, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (40, 1)] }, { coefficient := 1, powers := [(16, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (56, 1)] }, { coefficient := 1, powers := [(24, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (49, 1)] }, { coefficient := 1, powers := [(23, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (51, 1)] }, { coefficient := 1, powers := [(18, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (51, 1)] }, { coefficient := 1, powers := [(22, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (40, 1)] }, { coefficient := 1, powers := [(29, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (29, 1), (58, 1)] }, { coefficient := 1, powers := [(29, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (18, 1), (58, 1)] }, { coefficient := 1, powers := [(18, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (22, 1), (58, 1)] }, { coefficient := 1, powers := [(22, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (17, 1), (55, 1)] }, { coefficient := 1, powers := [(12, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1)] }, { coefficient := 1, powers := [(18, 1), (43, 1)] }, { coefficient := 1, powers := [(23, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (47, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (53, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1)] }, { coefficient := 1, powers := [(12, 1), (29, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (53, 1)] }, { coefficient := 1, powers := [(29, 1), (41, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (56, 1)] }, { coefficient := 1, powers := [(29, 1), (47, 1)] }, { coefficient := 1, powers := [(35, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1), (51, 1)] }, { coefficient := 1, powers := [(18, 1), (43, 1), (51, 1)] }, { coefficient := 1, powers := [(47, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (40, 1), (56, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (40, 1)] }, { coefficient := 1, powers := [(16, 1), (29, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (41, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (55, 1)] }, { coefficient := 1, powers := [(12, 1), (22, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (59, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (46, 1)] }, { coefficient := 1, powers := [(12, 1), (56, 1)] }, { coefficient := 1, powers := [(16, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (41, 1), (55, 1)] }, { coefficient := 1, powers := [(18, 1), (49, 1), (55, 1)] }, { coefficient := 1, powers := [(18, 1), (52, 1)] }, { coefficient := 1, powers := [(41, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1)] }, { coefficient := 1, powers := [(6, 1), (58, 1)] }, { coefficient := 1, powers := [(23, 1), (40, 1)] }, { coefficient := 1, powers := [(23, 1), (45, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (51, 1)] }, { coefficient := 1, powers := [(3, 1), (58, 1)] }, { coefficient := 1, powers := [(17, 1), (51, 1)] }, { coefficient := 1, powers := [(17, 1), (55, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (36, 1), (58, 1)] }, { coefficient := 1, powers := [(0, 1)] }, { coefficient := 1, powers := [(3, 1), (23, 1), (58, 1)] }, { coefficient := 1, powers := [(6, 1), (17, 1), (58, 1)] }, { coefficient := 1, powers := [(17, 1)] }, { coefficient := 1, powers := [(23, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (41, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (47, 1), (53, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (53, 1)] }, { coefficient := 1, powers := [(8, 1), (22, 1), (59, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (47, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(12, 1), (22, 1), (56, 1)] }, { coefficient := 1, powers := [(12, 1), (29, 1), (47, 1)] }, { coefficient := 1, powers := [(12, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1), (53, 1)] }, { coefficient := 1, powers := [(16, 1), (29, 1), (41, 1)] }, { coefficient := 1, powers := [(16, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(40, 1), (61, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(41, 1), (62, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 33 → SparsePoly (Fin 63) := ![
  [{ coefficient := -1, powers := [(0, 1), (3, 1), (29, 1), (55, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (29, 1), (36, 1), (51, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (29, 1), (36, 1), (55, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (32, 1), (36, 1), (51, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (32, 1), (36, 1), (55, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (35, 1), (36, 1), (51, 1), (53, 1)] }, { coefficient := 1, powers := [(0, 1), (35, 1), (36, 1), (53, 1), (55, 1)] }, { coefficient := 1, powers := [(3, 1), (23, 1), (29, 1), (51, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (23, 1), (29, 1), (55, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (23, 1), (32, 1), (51, 1), (56, 1)] }, { coefficient := 1, powers := [(3, 1), (23, 1), (32, 1), (55, 1), (56, 1)] }, { coefficient := 1, powers := [(3, 1), (23, 1), (35, 1), (51, 1), (53, 1)] }, { coefficient := 1, powers := [(3, 1), (23, 1), (35, 1), (53, 1), (55, 1)] }, { coefficient := -1, powers := [(3, 1), (29, 1), (59, 1)] }, { coefficient := -1, powers := [(3, 1), (32, 1), (56, 1)] }, { coefficient := 1, powers := [(6, 1), (17, 1), (29, 1), (51, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (17, 1), (29, 1), (55, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (17, 1), (32, 1), (51, 1), (56, 1)] }, { coefficient := 1, powers := [(6, 1), (17, 1), (32, 1), (55, 1), (56, 1)] }, { coefficient := 1, powers := [(6, 1), (17, 1), (35, 1), (51, 1), (53, 1)] }, { coefficient := 1, powers := [(6, 1), (17, 1), (35, 1), (53, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (22, 1), (36, 1), (51, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (22, 1), (36, 1), (55, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (32, 1), (36, 1), (47, 1), (51, 1)] }, { coefficient := 1, powers := [(0, 1), (32, 1), (36, 1), (47, 1), (55, 1)] }, { coefficient := 1, powers := [(0, 1), (35, 1), (36, 1), (41, 1), (51, 1)] }, { coefficient := 1, powers := [(0, 1), (35, 1), (36, 1), (41, 1), (55, 1)] }, { coefficient := 1, powers := [(3, 1), (22, 1), (23, 1), (51, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (22, 1), (23, 1), (55, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (23, 1), (32, 1), (47, 1), (51, 1)] }, { coefficient := 1, powers := [(3, 1), (23, 1), (32, 1), (47, 1), (55, 1)] }, { coefficient := 1, powers := [(3, 1), (23, 1), (35, 1), (41, 1), (51, 1)] }, { coefficient := 1, powers := [(3, 1), (23, 1), (35, 1), (41, 1), (55, 1)] }, { coefficient := -1, powers := [(3, 1), (32, 1), (47, 1)] }, { coefficient := -1, powers := [(3, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(6, 1), (17, 1), (22, 1), (51, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (17, 1), (22, 1), (55, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (17, 1), (32, 1), (47, 1), (51, 1)] }, { coefficient := 1, powers := [(6, 1), (17, 1), (32, 1), (47, 1), (55, 1)] }, { coefficient := 1, powers := [(6, 1), (17, 1), (35, 1), (41, 1), (51, 1)] }, { coefficient := 1, powers := [(6, 1), (17, 1), (35, 1), (41, 1), (55, 1)] }, { coefficient := 1, powers := [(6, 1), (18, 1), (35, 1), (49, 1), (55, 1)] }, { coefficient := 1, powers := [(6, 1), (18, 1), (35, 1), (52, 1)] }, { coefficient := -2, powers := [(6, 1), (22, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (32, 1), (47, 1)] }, { coefficient := 1, powers := [(6, 1), (35, 1), (41, 1)] }],
  [{ coefficient := -1, powers := [(22, 1), (40, 1), (56, 1)] }, { coefficient := -1, powers := [(22, 1), (45, 1), (56, 1)] }, { coefficient := -1, powers := [(29, 1), (40, 1), (47, 1)] }, { coefficient := -1, powers := [(29, 1), (45, 1), (47, 1)] }, { coefficient := -1, powers := [(29, 1), (47, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (43, 1), (55, 1)] }, { coefficient := 1, powers := [(22, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (41, 1), (51, 1)] }, { coefficient := 1, powers := [(29, 1), (41, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (22, 1), (56, 1)] }, { coefficient := -1, powers := [(0, 1), (29, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (29, 1), (41, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (22, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(51, 1), (62, 1)] }, { coefficient := 1, powers := [(55, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(49, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (8, 1), (59, 1)] }, { coefficient := -1, powers := [(0, 1), (16, 1), (53, 1)] }, { coefficient := 1, powers := [(8, 1), (17, 1), (59, 1)] }, { coefficient := -1, powers := [(16, 1), (17, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (16, 1), (41, 1)] }, { coefficient := -1, powers := [(16, 1), (23, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (5, 1), (55, 1), (59, 1)] }, { coefficient := 1, powers := [(16, 1), (41, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (35, 1), (49, 1), (55, 1)] }, { coefficient := -1, powers := [(8, 1), (35, 1), (52, 1)] }],
  [{ coefficient := 2, powers := [(8, 1), (59, 1)] }, { coefficient := -1, powers := [(12, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (29, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (53, 1), (55, 1)] }, { coefficient := -1, powers := [(3, 1), (53, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1), (55, 1)] }, { coefficient := -1, powers := [(6, 1), (47, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (16, 1), (36, 1), (51, 1), (58, 1)] }, { coefficient := 1, powers := [(0, 1), (16, 1), (36, 1), (55, 1), (58, 1)] }, { coefficient := 1, powers := [(0, 1), (16, 1), (55, 1)] }, { coefficient := 1, powers := [(3, 1), (16, 1), (23, 1), (51, 1), (58, 1)] }, { coefficient := 1, powers := [(3, 1), (16, 1), (23, 1), (55, 1), (58, 1)] }, { coefficient := -1, powers := [(3, 1), (16, 1), (58, 1)] }, { coefficient := 1, powers := [(6, 1), (16, 1), (17, 1), (51, 1), (58, 1)] }, { coefficient := 1, powers := [(6, 1), (16, 1), (17, 1), (55, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (12, 1), (36, 1), (51, 1), (58, 1)] }, { coefficient := 1, powers := [(0, 1), (12, 1), (36, 1), (55, 1), (58, 1)] }, { coefficient := 1, powers := [(0, 1), (12, 1), (55, 1)] }, { coefficient := 1, powers := [(3, 1), (12, 1), (23, 1), (51, 1), (58, 1)] }, { coefficient := 1, powers := [(3, 1), (12, 1), (23, 1), (55, 1), (58, 1)] }, { coefficient := -1, powers := [(3, 1), (12, 1), (58, 1)] }, { coefficient := 1, powers := [(6, 1), (12, 1), (17, 1), (51, 1), (58, 1)] }, { coefficient := 1, powers := [(6, 1), (12, 1), (17, 1), (55, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (29, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (41, 1), (58, 1), (61, 1)] }, { coefficient := -1, powers := [(41, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [(22, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (35, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (22, 1), (56, 1)] }, { coefficient := 1, powers := [(12, 1), (29, 1), (47, 1)] }, { coefficient := 1, powers := [(16, 1), (29, 1), (41, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (22, 1), (59, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1), (53, 1)] }, { coefficient := -1, powers := [(16, 1), (29, 1), (41, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := -1, powers := [(51, 1)] }, { coefficient := -1, powers := [(55, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (36, 1), (51, 1), (58, 1)] }, { coefficient := -1, powers := [(0, 1), (36, 1), (55, 1), (58, 1)] }, { coefficient := -1, powers := [(0, 1), (55, 1)] }, { coefficient := -1, powers := [(3, 1), (23, 1), (51, 1), (58, 1)] }, { coefficient := -1, powers := [(3, 1), (23, 1), (55, 1), (58, 1)] }, { coefficient := 1, powers := [(3, 1), (58, 1)] }, { coefficient := -1, powers := [(6, 1), (17, 1), (51, 1), (58, 1)] }, { coefficient := -1, powers := [(6, 1), (17, 1), (55, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (36, 1), (38, 1), (51, 1), (58, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (36, 1), (38, 1), (55, 1), (58, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (36, 1), (41, 1), (51, 1), (56, 1), (58, 1)] }, { coefficient := 1, powers := [(0, 1), (36, 1), (41, 1), (55, 1), (56, 1), (58, 1)] }, { coefficient := 1, powers := [(0, 1), (36, 1), (47, 1), (51, 1), (53, 1), (58, 1)] }, { coefficient := 1, powers := [(0, 1), (36, 1), (47, 1), (53, 1), (55, 1), (58, 1)] }, { coefficient := 1, powers := [(0, 1), (38, 1), (55, 1), (59, 1)] }, { coefficient := -1, powers := [(0, 1), (47, 1), (53, 1), (55, 1)] }, { coefficient := 1, powers := [(3, 1), (23, 1), (38, 1), (51, 1), (58, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (23, 1), (38, 1), (55, 1), (58, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (23, 1), (41, 1), (51, 1), (56, 1), (58, 1)] }, { coefficient := 1, powers := [(3, 1), (23, 1), (41, 1), (55, 1), (56, 1), (58, 1)] }, { coefficient := 1, powers := [(3, 1), (23, 1), (47, 1), (51, 1), (53, 1), (58, 1)] }, { coefficient := 1, powers := [(3, 1), (23, 1), (47, 1), (53, 1), (55, 1), (58, 1)] }, { coefficient := -1, powers := [(3, 1), (38, 1), (58, 1), (59, 1)] }, { coefficient := -1, powers := [(3, 1), (41, 1), (56, 1), (58, 1)] }, { coefficient := 1, powers := [(6, 1), (17, 1), (38, 1), (51, 1), (58, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (17, 1), (38, 1), (55, 1), (58, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (17, 1), (41, 1), (51, 1), (56, 1), (58, 1)] }, { coefficient := 1, powers := [(6, 1), (17, 1), (41, 1), (55, 1), (56, 1), (58, 1)] }, { coefficient := 1, powers := [(6, 1), (17, 1), (47, 1), (51, 1), (53, 1), (58, 1)] }, { coefficient := 1, powers := [(6, 1), (17, 1), (47, 1), (53, 1), (55, 1), (58, 1)] }, { coefficient := 1, powers := [(6, 1), (40, 1), (41, 1), (56, 1), (58, 1), (61, 1)] }, { coefficient := 1, powers := [(6, 1), (47, 1), (53, 1), (58, 1)] }, { coefficient := 1, powers := [(40, 1), (41, 1), (56, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (8, 1), (35, 1), (41, 1), (58, 1)] }, { coefficient := 1, powers := [(6, 1), (16, 1), (29, 1), (41, 1), (58, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(16, 1), (29, 1), (41, 1)] }],
  [{ coefficient := -1, powers := [(23, 1), (51, 1)] }, { coefficient := -1, powers := [(23, 1), (55, 1)] }]
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
    (values : Fin 63 → R) :
    ¬ ∀ index : Fin 33,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component22.SelectedLeafB4_3.selectedHasNoCommonZero

end Krenn.Component22.SelectedLeafB4_3
