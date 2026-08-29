import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component22.SelectedLeafB0

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "2cef3e4012c95c46d91a4328a5eb87b5095141dd515228448a2cee57fbb1fe27"
def certificateSHA256 : String := "b9989076401389c2c54eda82ddfe443577575c61902af8737b0ab2bae8292947"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 32 → Fin 639 := ![
  2,
  3,
  11,
  12,
  20,
  21,
  192,
  193,
  194,
  205,
  224,
  344,
  347,
  351,
  353,
  363,
  364,
  366,
  368,
  369,
  457,
  460,
  462,
  467,
  468,
  481,
  557,
  558,
  621,
  635,
  636,
  638
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 32 → SparsePoly (Fin 60) := ![
  [{ coefficient := 1, powers := [(5, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (23, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (17, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (18, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (56, 1)] }, { coefficient := 1, powers := [(24, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (49, 1)] }, { coefficient := 1, powers := [(23, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (51, 1)] }, { coefficient := 1, powers := [(18, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (40, 1)] }, { coefficient := 1, powers := [(24, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (24, 1), (58, 1)] }, { coefficient := 1, powers := [(24, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1)] }, { coefficient := 1, powers := [(17, 1), (43, 1)] }, { coefficient := 1, powers := [(23, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (53, 1)] }, { coefficient := 1, powers := [(17, 1), (53, 1)] }, { coefficient := 1, powers := [(24, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (47, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (53, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1)] }, { coefficient := 1, powers := [(12, 1), (29, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (53, 1)] }, { coefficient := 1, powers := [(29, 1), (41, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (56, 1)] }, { coefficient := 1, powers := [(29, 1), (47, 1)] }, { coefficient := 1, powers := [(35, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1), (51, 1)] }, { coefficient := 1, powers := [(17, 1), (43, 1), (51, 1)] }, { coefficient := 1, powers := [(43, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1), (49, 1)] }, { coefficient := 1, powers := [(23, 1), (45, 1), (49, 1)] }, { coefficient := 1, powers := [(49, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1), (53, 1)] }, { coefficient := 1, powers := [(24, 1), (45, 1), (49, 1)] }, { coefficient := 1, powers := [(53, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1)] }, { coefficient := 1, powers := [(23, 1), (40, 1), (43, 1)] }, { coefficient := 1, powers := [(23, 1), (46, 1)] }, { coefficient := 1, powers := [(43, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (59, 1)] }, { coefficient := 1, powers := [(12, 1), (47, 1)] }, { coefficient := 1, powers := [(16, 1), (18, 1), (52, 1)] }, { coefficient := 1, powers := [(16, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (59, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (46, 1)] }, { coefficient := 1, powers := [(12, 1), (56, 1)] }, { coefficient := 1, powers := [(16, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (40, 1), (56, 1)] }, { coefficient := 1, powers := [(24, 1), (40, 1), (43, 1)] }, { coefficient := 1, powers := [(24, 1), (46, 1)] }, { coefficient := 1, powers := [(56, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (41, 1), (55, 1)] }, { coefficient := 1, powers := [(18, 1), (49, 1), (55, 1)] }, { coefficient := 1, powers := [(18, 1), (52, 1)] }, { coefficient := 1, powers := [(41, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1), (51, 1)] }, { coefficient := 1, powers := [(40, 1), (43, 1)] }, { coefficient := 1, powers := [(43, 1), (51, 1)] }, { coefficient := 1, powers := [(46, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1)] }, { coefficient := 1, powers := [(6, 1), (58, 1)] }, { coefficient := 1, powers := [(23, 1), (40, 1)] }, { coefficient := 1, powers := [(23, 1), (45, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (51, 1)] }, { coefficient := 1, powers := [(3, 1), (58, 1)] }, { coefficient := 1, powers := [(17, 1), (51, 1)] }, { coefficient := 1, powers := [(17, 1), (55, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (37, 1), (58, 1)] }, { coefficient := 1, powers := [(0, 1), (40, 1), (55, 1)] }, { coefficient := 1, powers := [(0, 1), (45, 1), (51, 1)] }, { coefficient := 1, powers := [(40, 1)] }, { coefficient := 1, powers := [(45, 1)] }, { coefficient := 1, powers := [(51, 1)] }, { coefficient := 1, powers := [(55, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (41, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (47, 1), (53, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (53, 1)] }, { coefficient := 1, powers := [(8, 1), (22, 1), (59, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (47, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(12, 1), (22, 1), (56, 1)] }, { coefficient := 1, powers := [(12, 1), (29, 1), (47, 1)] }, { coefficient := 1, powers := [(12, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1), (53, 1)] }, { coefficient := 1, powers := [(16, 1), (29, 1), (41, 1)] }, { coefficient := 1, powers := [(16, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1)] }],
  [{ coefficient := 1, powers := [(2, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 32 → SparsePoly (Fin 60) := ![
  [{ coefficient := -1, powers := [(3, 1), (24, 1), (32, 1), (43, 1), (51, 1)] }, { coefficient := -1, powers := [(3, 1), (24, 1), (32, 1), (43, 1), (55, 1)] }, { coefficient := -1, powers := [(6, 1), (32, 1), (56, 1)] }, { coefficient := -2, powers := [(6, 1), (35, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (18, 1), (35, 1), (49, 1), (51, 1)] }, { coefficient := 1, powers := [(3, 1), (18, 1), (35, 1), (49, 1), (55, 1)] }, { coefficient := -2, powers := [(6, 1), (32, 1), (47, 1)] }, { coefficient := -1, powers := [(6, 1), (35, 1), (41, 1)] }],
  [{ coefficient := -1, powers := [(22, 1), (51, 1), (56, 1)] }, { coefficient := -1, powers := [(22, 1), (55, 1), (56, 1)] }, { coefficient := -2, powers := [(29, 1), (47, 1), (51, 1)] }, { coefficient := -2, powers := [(29, 1), (47, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (22, 1), (43, 1), (45, 1), (58, 1)] }, { coefficient := -1, powers := [(22, 1), (23, 1), (46, 1), (51, 1)] }, { coefficient := -1, powers := [(22, 1), (23, 1), (46, 1), (55, 1)] }],
  [{ coefficient := 2, powers := [(22, 1), (51, 1), (53, 1)] }, { coefficient := 2, powers := [(22, 1), (53, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (29, 1), (49, 1), (51, 1), (58, 1)] }, { coefficient := -1, powers := [(23, 1), (29, 1), (51, 1), (52, 1)] }, { coefficient := -1, powers := [(23, 1), (29, 1), (52, 1), (55, 1)] }, { coefficient := 1, powers := [(29, 1), (49, 1), (51, 1)] }, { coefficient := 1, powers := [(29, 1), (49, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (32, 1), (51, 1)] }, { coefficient := -1, powers := [(5, 1), (32, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (35, 1), (51, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (55, 1)] }, { coefficient := -1, powers := [(16, 1), (29, 1), (51, 1)] }, { coefficient := -1, powers := [(16, 1), (29, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (16, 1), (29, 1), (49, 1), (58, 1)] }, { coefficient := 1, powers := [(8, 1), (17, 1), (35, 1), (49, 1), (51, 1)] }, { coefficient := 1, powers := [(8, 1), (17, 1), (35, 1), (49, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (17, 1), (32, 1), (43, 1), (51, 1)] }, { coefficient := -1, powers := [(5, 1), (17, 1), (32, 1), (43, 1), (55, 1)] }, { coefficient := -1, powers := [(5, 1), (23, 1), (32, 1), (43, 1), (51, 1)] }, { coefficient := -1, powers := [(5, 1), (23, 1), (32, 1), (43, 1), (55, 1)] }, { coefficient := -1, powers := [(6, 1), (12, 1), (22, 1), (43, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (32, 1), (43, 1), (51, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (43, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (24, 1), (32, 1), (40, 1), (51, 1)] }, { coefficient := 1, powers := [(5, 1), (24, 1), (32, 1), (40, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (24, 1), (32, 1), (45, 1), (51, 1)] }, { coefficient := 1, powers := [(5, 1), (24, 1), (32, 1), (45, 1), (55, 1)] }],
  [{ coefficient := -2, powers := [(16, 1), (22, 1), (51, 1)] }, { coefficient := -2, powers := [(16, 1), (22, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (53, 1), (58, 1)] }, { coefficient := 1, powers := [(23, 1), (51, 1), (53, 1)] }, { coefficient := 1, powers := [(23, 1), (53, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (47, 1), (58, 1)] }, { coefficient := 1, powers := [(23, 1), (47, 1), (51, 1)] }, { coefficient := 1, powers := [(23, 1), (47, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (16, 1), (58, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1), (51, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (12, 1), (58, 1)] }, { coefficient := 1, powers := [(12, 1), (23, 1), (51, 1)] }, { coefficient := 1, powers := [(12, 1), (23, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (24, 1), (32, 1), (51, 1)] }, { coefficient := 1, powers := [(5, 1), (24, 1), (32, 1), (55, 1)] }],
  [{ coefficient := 2, powers := [(16, 1), (22, 1), (24, 1), (51, 1)] }, { coefficient := 2, powers := [(16, 1), (22, 1), (24, 1), (55, 1)] }],
  [{ coefficient := -2, powers := [(16, 1), (22, 1), (23, 1), (51, 1)] }, { coefficient := -2, powers := [(16, 1), (22, 1), (23, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (24, 1), (32, 1), (51, 1)] }, { coefficient := -1, powers := [(5, 1), (24, 1), (32, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (29, 1), (58, 1)] }, { coefficient := 1, powers := [(23, 1), (29, 1), (51, 1)] }, { coefficient := 1, powers := [(23, 1), (29, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (22, 1), (58, 1)] }, { coefficient := 1, powers := [(22, 1), (23, 1), (51, 1)] }, { coefficient := 1, powers := [(22, 1), (23, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (17, 1), (32, 1), (51, 1)] }, { coefficient := 1, powers := [(5, 1), (17, 1), (32, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (23, 1), (32, 1), (51, 1)] }, { coefficient := 1, powers := [(5, 1), (23, 1), (32, 1), (55, 1)] }, { coefficient := 1, powers := [(6, 1), (12, 1), (22, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (16, 1), (29, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (17, 1), (24, 1), (32, 1), (51, 1)] }, { coefficient := -1, powers := [(5, 1), (17, 1), (24, 1), (32, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [] }],
  [{ coefficient := -1, powers := [(8, 1), (18, 1), (35, 1), (49, 1), (51, 1)] }, { coefficient := -1, powers := [(8, 1), (18, 1), (35, 1), (49, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(23, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (58, 1)] }, { coefficient := -1, powers := [(23, 1), (51, 1)] }, { coefficient := -1, powers := [(23, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (17, 1), (24, 1), (32, 1), (46, 1), (51, 2)] }, { coefficient := 1, powers := [(5, 1), (17, 1), (24, 1), (32, 1), (46, 1), (51, 1), (55, 1)] }, { coefficient := -1, powers := [(5, 1), (17, 1), (32, 1), (40, 1), (51, 1), (56, 1)] }, { coefficient := -1, powers := [(5, 1), (17, 1), (32, 1), (40, 1), (55, 1), (56, 1)] }, { coefficient := -1, powers := [(5, 1), (23, 1), (32, 1), (40, 1), (51, 1), (56, 1)] }, { coefficient := -1, powers := [(5, 1), (23, 1), (32, 1), (40, 1), (55, 1), (56, 1)] }, { coefficient := -1, powers := [(5, 1), (24, 1), (32, 1), (40, 1), (43, 1), (51, 1)] }, { coefficient := -1, powers := [(5, 1), (24, 1), (32, 1), (40, 1), (43, 1), (55, 1)] }, { coefficient := -1, powers := [(5, 1), (24, 1), (32, 1), (43, 1), (45, 1), (51, 1)] }, { coefficient := -1, powers := [(5, 1), (24, 1), (32, 1), (43, 1), (45, 1), (55, 1)] }, { coefficient := -1, powers := [(5, 1), (24, 1), (32, 1), (43, 1), (51, 2)] }, { coefficient := -1, powers := [(5, 1), (24, 1), (32, 1), (43, 1), (51, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (24, 1), (32, 1), (46, 1), (51, 1)] }, { coefficient := 1, powers := [(5, 1), (24, 1), (32, 1), (46, 1), (55, 1)] }, { coefficient := -1, powers := [(6, 1), (12, 1), (22, 1), (40, 1), (56, 1), (58, 1)] }, { coefficient := -1, powers := [(6, 1), (16, 1), (29, 1), (41, 1), (55, 1), (58, 1)] }, { coefficient := 1, powers := [(8, 1), (18, 1), (35, 1), (49, 1), (51, 2)] }, { coefficient := 1, powers := [(8, 1), (18, 1), (35, 1), (49, 1), (51, 1), (55, 1)] }, { coefficient := 2, powers := [(16, 1), (22, 1), (23, 1), (45, 1), (51, 1), (53, 1)] }, { coefficient := 2, powers := [(16, 1), (22, 1), (23, 1), (45, 1), (53, 1), (55, 1)] }, { coefficient := -2, powers := [(16, 1), (22, 1), (24, 1), (45, 1), (49, 1), (51, 1)] }, { coefficient := -2, powers := [(16, 1), (22, 1), (24, 1), (45, 1), (49, 1), (55, 1)] }, { coefficient := 2, powers := [(16, 1), (22, 1), (51, 1), (53, 1)] }, { coefficient := 2, powers := [(16, 1), (22, 1), (53, 1), (55, 1)] }, { coefficient := 1, powers := [(23, 1), (37, 1), (58, 1)] }, { coefficient := 1, powers := [(23, 1), (40, 1), (55, 1)] }, { coefficient := 1, powers := [(23, 1), (45, 1), (51, 1)] }, { coefficient := -1, powers := [(45, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (38, 1), (58, 1), (59, 1)] }, { coefficient := -1, powers := [(6, 1), (41, 1), (56, 1), (58, 1)] }, { coefficient := -3, powers := [(6, 1), (47, 1), (53, 1), (58, 1)] }, { coefficient := 1, powers := [(23, 1), (38, 1), (51, 1), (59, 1)] }, { coefficient := 1, powers := [(23, 1), (38, 1), (55, 1), (59, 1)] }, { coefficient := 1, powers := [(23, 1), (41, 1), (51, 1), (56, 1)] }, { coefficient := 1, powers := [(23, 1), (41, 1), (55, 1), (56, 1)] }, { coefficient := -1, powers := [(23, 1), (47, 1), (51, 1), (53, 1)] }, { coefficient := -1, powers := [(23, 1), (47, 1), (53, 1), (55, 1)] }]
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
    (values : Fin 60 → R) :
    ¬ ∀ index : Fin 32,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component22.SelectedLeafB0.selectedHasNoCommonZero

end Krenn.Component22.SelectedLeafB0
