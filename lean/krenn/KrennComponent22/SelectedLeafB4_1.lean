import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component22.SelectedLeafB4_1

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "0f6ae4cb0c3c230ab2429e95546601bad71a2ede0c735a89da2f7b6881eb2e16"
def certificateSHA256 : String := "65008639f4041a7cf1d2ae6fe16c6b440149e0ea41f6663b7431891004ea98df"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 16 → Fin 642 := ![
  2,
  3,
  193,
  236,
  363,
  364,
  368,
  468,
  557,
  583,
  621,
  635,
  636,
  638,
  640,
  641
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 16 → SparsePoly (Fin 62) := ![
  [{ coefficient := 1, powers := [(5, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (49, 1)] }, { coefficient := 1, powers := [(23, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (18, 1), (58, 1)] }, { coefficient := 1, powers := [(18, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (53, 1)] }, { coefficient := 1, powers := [(29, 1), (41, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (56, 1)] }, { coefficient := 1, powers := [(29, 1), (47, 1)] }, { coefficient := 1, powers := [(35, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1), (49, 1)] }, { coefficient := 1, powers := [(23, 1), (45, 1), (49, 1)] }, { coefficient := 1, powers := [(49, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (41, 1), (55, 1)] }, { coefficient := 1, powers := [(18, 1), (49, 1), (55, 1)] }, { coefficient := 1, powers := [(18, 1), (52, 1)] }, { coefficient := 1, powers := [(41, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1)] }, { coefficient := 1, powers := [(6, 1), (58, 1)] }, { coefficient := 1, powers := [(23, 1), (40, 1)] }, { coefficient := 1, powers := [(23, 1), (45, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (36, 1), (58, 1)] }, { coefficient := 1, powers := [(0, 1)] }, { coefficient := 1, powers := [(3, 1), (23, 1), (58, 1)] }, { coefficient := 1, powers := [(6, 1), (17, 1), (58, 1)] }, { coefficient := 1, powers := [(17, 1)] }, { coefficient := 1, powers := [(23, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (37, 1), (58, 1)] }, { coefficient := 1, powers := [(0, 1), (40, 1), (55, 1)] }, { coefficient := 1, powers := [(0, 1), (45, 1), (51, 1)] }, { coefficient := 1, powers := [(40, 1)] }, { coefficient := 1, powers := [(45, 1)] }, { coefficient := 1, powers := [(51, 1)] }, { coefficient := 1, powers := [(55, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (41, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (47, 1), (53, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (53, 1)] }, { coefficient := 1, powers := [(8, 1), (22, 1), (59, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (47, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(12, 1), (22, 1), (56, 1)] }, { coefficient := 1, powers := [(12, 1), (29, 1), (47, 1)] }, { coefficient := 1, powers := [(12, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1), (53, 1)] }, { coefficient := 1, powers := [(16, 1), (29, 1), (41, 1)] }, { coefficient := 1, powers := [(16, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (60, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(40, 1)] }],
  [{ coefficient := 1, powers := [(41, 1), (61, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 16 → SparsePoly (Fin 62) := ![
  [{ coefficient := -1, powers := [(0, 1), (17, 1), (29, 1), (37, 1), (59, 1)] }, { coefficient := -1, powers := [(0, 1), (17, 1), (32, 1), (37, 1), (56, 1)] }, { coefficient := -1, powers := [(0, 1), (17, 1), (35, 1), (37, 1), (53, 1)] }, { coefficient := 1, powers := [(0, 1), (29, 1), (36, 1), (55, 1), (59, 1)] }, { coefficient := -1, powers := [(0, 1), (29, 1), (36, 1), (59, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (32, 1), (36, 1), (55, 1), (56, 1)] }, { coefficient := -1, powers := [(0, 1), (32, 1), (36, 1), (56, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (35, 1), (36, 1), (53, 1), (55, 1)] }, { coefficient := -1, powers := [(0, 1), (35, 1), (36, 1), (53, 1), (60, 1)] }, { coefficient := 1, powers := [(3, 1), (23, 1), (29, 1), (55, 1), (59, 1)] }, { coefficient := -1, powers := [(3, 1), (23, 1), (29, 1), (59, 1), (60, 1)] }, { coefficient := 1, powers := [(3, 1), (23, 1), (32, 1), (55, 1), (56, 1)] }, { coefficient := -1, powers := [(3, 1), (23, 1), (32, 1), (56, 1), (60, 1)] }, { coefficient := 1, powers := [(3, 1), (23, 1), (35, 1), (53, 1), (55, 1)] }, { coefficient := -1, powers := [(3, 1), (23, 1), (35, 1), (53, 1), (60, 1)] }, { coefficient := 1, powers := [(6, 1), (17, 1), (29, 1), (51, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (17, 1), (29, 1), (55, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (17, 1), (32, 1), (51, 1), (56, 1)] }, { coefficient := 1, powers := [(6, 1), (17, 1), (32, 1), (55, 1), (56, 1)] }, { coefficient := 1, powers := [(6, 1), (17, 1), (35, 1), (51, 1), (53, 1)] }, { coefficient := 1, powers := [(6, 1), (17, 1), (35, 1), (53, 1), (55, 1)] }, { coefficient := 1, powers := [(6, 1), (18, 1), (29, 1), (52, 1), (59, 1), (61, 1)] }, { coefficient := 1, powers := [(6, 1), (18, 1), (32, 1), (52, 1), (56, 1), (61, 1)] }, { coefficient := 1, powers := [(6, 1), (18, 1), (35, 1), (52, 1), (53, 1), (61, 1)] }, { coefficient := -1, powers := [(17, 1), (23, 1), (29, 1), (37, 1), (59, 1)] }, { coefficient := -1, powers := [(17, 1), (23, 1), (32, 1), (37, 1), (56, 1)] }, { coefficient := -1, powers := [(17, 1), (23, 1), (35, 1), (37, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (17, 1), (22, 1), (37, 1), (59, 1)] }, { coefficient := -1, powers := [(0, 1), (17, 1), (32, 1), (37, 1), (47, 1)] }, { coefficient := -1, powers := [(0, 1), (17, 1), (35, 1), (37, 1), (41, 1)] }, { coefficient := 1, powers := [(0, 1), (22, 1), (36, 1), (55, 1), (59, 1)] }, { coefficient := -1, powers := [(0, 1), (22, 1), (36, 1), (59, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (32, 1), (36, 1), (47, 1), (55, 1)] }, { coefficient := -1, powers := [(0, 1), (32, 1), (36, 1), (47, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (35, 1), (36, 1), (41, 1), (55, 1)] }, { coefficient := -1, powers := [(0, 1), (35, 1), (36, 1), (41, 1), (60, 1)] }, { coefficient := 1, powers := [(3, 1), (22, 1), (23, 1), (55, 1), (59, 1)] }, { coefficient := -1, powers := [(3, 1), (22, 1), (23, 1), (59, 1), (60, 1)] }, { coefficient := 1, powers := [(3, 1), (23, 1), (32, 1), (47, 1), (55, 1)] }, { coefficient := -1, powers := [(3, 1), (23, 1), (32, 1), (47, 1), (60, 1)] }, { coefficient := 1, powers := [(3, 1), (23, 1), (35, 1), (41, 1), (55, 1)] }, { coefficient := -1, powers := [(3, 1), (23, 1), (35, 1), (41, 1), (60, 1)] }, { coefficient := 1, powers := [(6, 1), (17, 1), (22, 1), (51, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (17, 1), (22, 1), (55, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (17, 1), (32, 1), (47, 1), (51, 1)] }, { coefficient := 1, powers := [(6, 1), (17, 1), (32, 1), (47, 1), (55, 1)] }, { coefficient := 1, powers := [(6, 1), (17, 1), (35, 1), (41, 1), (51, 1)] }, { coefficient := 1, powers := [(6, 1), (17, 1), (35, 1), (41, 1), (55, 1)] }, { coefficient := 1, powers := [(6, 1), (18, 1), (22, 1), (52, 1), (59, 1), (61, 1)] }, { coefficient := 1, powers := [(6, 1), (18, 1), (32, 1), (47, 1), (52, 1), (61, 1)] }, { coefficient := 1, powers := [(6, 1), (18, 1), (35, 1), (41, 1), (52, 1), (61, 1)] }, { coefficient := -1, powers := [(17, 1), (22, 1), (23, 1), (37, 1), (59, 1)] }, { coefficient := -1, powers := [(17, 1), (23, 1), (32, 1), (37, 1), (47, 1)] }, { coefficient := -1, powers := [(17, 1), (23, 1), (35, 1), (37, 1), (41, 1)] }],
  [{ coefficient := -1, powers := [(17, 1), (51, 1), (60, 1), (61, 1)] }, { coefficient := -1, powers := [(17, 1), (55, 1), (60, 1), (61, 1)] }, { coefficient := 1, powers := [(55, 1), (61, 1)] }, { coefficient := -1, powers := [(60, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (49, 1), (51, 1), (60, 1), (61, 1)] }, { coefficient := 1, powers := [(17, 1), (49, 1), (55, 1), (60, 1), (61, 1)] }, { coefficient := -2, powers := [(49, 1), (55, 1), (61, 1)] }, { coefficient := 1, powers := [(49, 1), (60, 1), (61, 1)] }, { coefficient := -1, powers := [(52, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (16, 1), (17, 1), (37, 1), (58, 1)] }, { coefficient := 1, powers := [(0, 1), (16, 1), (36, 1), (55, 1), (58, 1)] }, { coefficient := -1, powers := [(0, 1), (16, 1), (36, 1), (58, 1), (60, 1)] }, { coefficient := 1, powers := [(3, 1), (16, 1), (23, 1), (55, 1), (58, 1)] }, { coefficient := -1, powers := [(3, 1), (16, 1), (23, 1), (58, 1), (60, 1)] }, { coefficient := 1, powers := [(6, 1), (16, 1), (17, 1), (51, 1), (58, 1)] }, { coefficient := 1, powers := [(6, 1), (16, 1), (17, 1), (55, 1), (58, 1)] }, { coefficient := 1, powers := [(6, 1), (16, 1), (18, 1), (52, 1), (58, 1), (61, 1)] }, { coefficient := -1, powers := [(16, 1), (17, 1), (23, 1), (37, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (12, 1), (17, 1), (37, 1), (58, 1)] }, { coefficient := 1, powers := [(0, 1), (12, 1), (36, 1), (55, 1), (58, 1)] }, { coefficient := -1, powers := [(0, 1), (12, 1), (36, 1), (58, 1), (60, 1)] }, { coefficient := 1, powers := [(3, 1), (12, 1), (23, 1), (55, 1), (58, 1)] }, { coefficient := -1, powers := [(3, 1), (12, 1), (23, 1), (58, 1), (60, 1)] }, { coefficient := 1, powers := [(6, 1), (12, 1), (17, 1), (51, 1), (58, 1)] }, { coefficient := 1, powers := [(6, 1), (12, 1), (17, 1), (55, 1), (58, 1)] }, { coefficient := 1, powers := [(6, 1), (12, 1), (18, 1), (52, 1), (58, 1), (61, 1)] }, { coefficient := -1, powers := [(12, 1), (17, 1), (23, 1), (37, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (18, 1), (51, 1), (60, 1), (61, 1)] }, { coefficient := 1, powers := [(17, 1), (18, 1), (55, 1), (60, 1), (61, 1)] }, { coefficient := -2, powers := [(18, 1), (55, 1), (61, 1)] }, { coefficient := 1, powers := [(18, 1), (60, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(61, 1)] }],
  [{ coefficient := -1, powers := [(17, 1), (18, 1), (49, 1), (51, 1), (60, 1), (61, 1)] }, { coefficient := -1, powers := [(17, 1), (18, 1), (49, 1), (55, 1), (60, 1), (61, 1)] }, { coefficient := -1, powers := [(17, 1), (51, 1)] }, { coefficient := -1, powers := [(17, 1), (60, 1)] }, { coefficient := 2, powers := [(18, 1), (49, 1), (55, 1), (61, 1)] }, { coefficient := -1, powers := [(18, 1), (49, 1), (60, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(55, 1)] }, { coefficient := 1, powers := [(60, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (23, 1), (60, 1)] }, { coefficient := 1, powers := [(17, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (17, 1), (37, 1), (58, 1)] }, { coefficient := -1, powers := [(0, 1), (36, 1), (55, 1), (58, 1)] }, { coefficient := 1, powers := [(0, 1), (36, 1), (58, 1), (60, 1)] }, { coefficient := -1, powers := [(3, 1), (23, 1), (55, 1), (58, 1)] }, { coefficient := 1, powers := [(3, 1), (23, 1), (58, 1), (60, 1)] }, { coefficient := -1, powers := [(6, 1), (17, 1), (51, 1), (58, 1)] }, { coefficient := -1, powers := [(6, 1), (17, 1), (55, 1), (58, 1)] }, { coefficient := -1, powers := [(6, 1), (18, 1), (52, 1), (58, 1), (61, 1)] }, { coefficient := 1, powers := [(17, 1), (23, 1), (37, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(17, 1), (23, 1), (37, 1), (58, 1)] }, { coefficient := -1, powers := [(17, 1), (23, 1), (45, 1), (51, 1)] }, { coefficient := 1, powers := [(17, 1), (45, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(0, 1), (17, 1), (37, 1), (38, 1), (58, 1), (59, 1)] }, { coefficient := -1, powers := [(0, 1), (17, 1), (37, 1), (41, 1), (56, 1), (58, 1)] }, { coefficient := -1, powers := [(0, 1), (17, 1), (37, 1), (47, 1), (53, 1), (58, 1)] }, { coefficient := 1, powers := [(0, 1), (36, 1), (38, 1), (55, 1), (58, 1), (59, 1)] }, { coefficient := -1, powers := [(0, 1), (36, 1), (38, 1), (58, 1), (59, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (36, 1), (41, 1), (55, 1), (56, 1), (58, 1)] }, { coefficient := -1, powers := [(0, 1), (36, 1), (41, 1), (56, 1), (58, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (36, 1), (47, 1), (53, 1), (55, 1), (58, 1)] }, { coefficient := -1, powers := [(0, 1), (36, 1), (47, 1), (53, 1), (58, 1), (60, 1)] }, { coefficient := 1, powers := [(3, 1), (23, 1), (38, 1), (55, 1), (58, 1), (59, 1)] }, { coefficient := -1, powers := [(3, 1), (23, 1), (38, 1), (58, 1), (59, 1), (60, 1)] }, { coefficient := 1, powers := [(3, 1), (23, 1), (41, 1), (55, 1), (56, 1), (58, 1)] }, { coefficient := -1, powers := [(3, 1), (23, 1), (41, 1), (56, 1), (58, 1), (60, 1)] }, { coefficient := 1, powers := [(3, 1), (23, 1), (47, 1), (53, 1), (55, 1), (58, 1)] }, { coefficient := -1, powers := [(3, 1), (23, 1), (47, 1), (53, 1), (58, 1), (60, 1)] }, { coefficient := 1, powers := [(6, 1), (17, 1), (38, 1), (51, 1), (58, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (17, 1), (38, 1), (55, 1), (58, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (17, 1), (41, 1), (51, 1), (56, 1), (58, 1)] }, { coefficient := 1, powers := [(6, 1), (17, 1), (41, 1), (55, 1), (56, 1), (58, 1)] }, { coefficient := 1, powers := [(6, 1), (17, 1), (47, 1), (51, 1), (53, 1), (58, 1)] }, { coefficient := 1, powers := [(6, 1), (17, 1), (47, 1), (53, 1), (55, 1), (58, 1)] }, { coefficient := 1, powers := [(6, 1), (18, 1), (38, 1), (52, 1), (58, 1), (59, 1), (61, 1)] }, { coefficient := 1, powers := [(6, 1), (18, 1), (41, 1), (52, 1), (56, 1), (58, 1), (61, 1)] }, { coefficient := 1, powers := [(6, 1), (18, 1), (47, 1), (52, 1), (53, 1), (58, 1), (61, 1)] }, { coefficient := -1, powers := [(17, 1), (23, 1), (37, 1), (38, 1), (58, 1), (59, 1)] }, { coefficient := -1, powers := [(17, 1), (23, 1), (37, 1), (41, 1), (56, 1), (58, 1)] }, { coefficient := -1, powers := [(17, 1), (23, 1), (37, 1), (47, 1), (53, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (17, 1), (23, 1), (55, 1), (60, 1)] }, { coefficient := -1, powers := [(0, 1), (17, 1), (55, 1)] }, { coefficient := 1, powers := [(17, 1), (18, 1), (23, 1), (49, 1), (51, 1), (60, 1), (61, 1)] }, { coefficient := 1, powers := [(17, 1), (18, 1), (23, 1), (49, 1), (55, 1), (60, 1), (61, 1)] }, { coefficient := 1, powers := [(17, 1), (23, 1), (51, 1)] }, { coefficient := -1, powers := [(17, 1)] }, { coefficient := -2, powers := [(18, 1), (23, 1), (49, 1), (55, 1), (61, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (49, 1), (60, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (55, 1)] }, { coefficient := 1, powers := [(17, 1), (23, 1), (51, 1), (60, 1)] }, { coefficient := 1, powers := [(17, 1), (23, 1), (55, 1), (60, 1)] }, { coefficient := -1, powers := [(23, 1), (55, 1)] }, { coefficient := 1, powers := [(23, 1), (60, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
/-- Lean replays the exact selected-row integer certificate. -/
theorem constantIdentity :
    ∑ index, (multipliers index).toPoly *
      (selectedEquations index).toPoly = C (2 : ℤ) := by
  simp (config := { maxSteps := 1000000 })
    [Fin.sum_univ_succ, multipliers, selectedEquations,
    SparsePoly.toPoly, SparseTerm.toPoly]
  ring

/-- The selected rows have no common zero in a characteristic-zero ring. -/
theorem selectedHasNoCommonZero {R : Type*} [CommRing R] [Nontrivial R] [CharZero R]
    (values : Fin 62 → R) :
    ¬ ∀ index : Fin 16,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((2 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (2 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (2 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component22.SelectedLeafB4_1.selectedHasNoCommonZero

end Krenn.Component22.SelectedLeafB4_1
