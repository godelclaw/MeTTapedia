import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component39.SelectedLeafB5_6_6_0

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "583d4892ef600d5937b714e9f1169e094b8acf09a4481a4a13d219eaa3914734"
def certificateSHA256 : String := "e11ca981f7e3ebc30b4cc8bf34e9ce978a96d0f271693e534b72d2ac363c9e1a"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 30 → Fin 673 := ![
  11,
  21,
  191,
  192,
  193,
  301,
  304,
  305,
  324,
  396,
  397,
  419,
  425,
  440,
  471,
  511,
  529,
  542,
  566,
  603,
  645,
  659,
  660,
  661,
  662,
  666,
  669,
  670,
  671,
  672
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 30 → SparsePoly (Fin 67) := ![
  [{ coefficient := 1, powers := [(8, 1), (30, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (20, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (54, 1)] }, { coefficient := 1, powers := [(28, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (42, 1)] }, { coefficient := 1, powers := [(26, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (53, 1)] }, { coefficient := 1, powers := [(28, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (42, 1)] }, { coefficient := 1, powers := [(23, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (44, 1)] }, { coefficient := 1, powers := [(4, 1), (33, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (51, 1)] }, { coefficient := 1, powers := [(7, 1), (30, 1)] }, { coefficient := 1, powers := [(10, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1), (51, 1)] }, { coefficient := 1, powers := [(19, 1), (42, 1), (51, 1)] }, { coefficient := 1, powers := [(47, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (23, 1), (39, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1), (44, 1)] }, { coefficient := 1, powers := [(16, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (23, 1), (45, 1)] }, { coefficient := 1, powers := [(17, 1), (23, 1), (39, 1)] }, { coefficient := 1, powers := [(17, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (47, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1)] }, { coefficient := 1, powers := [(16, 1), (26, 1), (47, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1)] }, { coefficient := 1, powers := [(12, 1), (28, 1)] }, { coefficient := 1, powers := [(16, 1), (21, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (54, 1)] }, { coefficient := 1, powers := [(28, 1), (40, 1)] }, { coefficient := 1, powers := [(28, 1), (46, 1), (49, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1), (53, 1)] }, { coefficient := 1, powers := [(19, 1), (42, 1), (53, 1)] }, { coefficient := 1, powers := [(19, 1), (57, 1)] }, { coefficient := 1, powers := [(24, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (23, 1), (59, 1)] }, { coefficient := 1, powers := [(10, 1), (23, 1), (44, 1)] }, { coefficient := 1, powers := [(14, 1), (23, 1), (39, 1)] }, { coefficient := 1, powers := [(14, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (20, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (30, 1), (44, 1)] }, { coefficient := 1, powers := [(6, 1), (33, 1), (39, 1)] }, { coefficient := 1, powers := [(20, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (20, 1), (59, 1)] }, { coefficient := 1, powers := [(8, 1), (30, 1), (44, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (39, 1)] }, { coefficient := 1, powers := [(16, 1), (20, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (42, 1), (53, 1)] }, { coefficient := 1, powers := [(22, 1), (57, 1)] }, { coefficient := 1, powers := [(28, 1), (47, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (51, 1)] }, { coefficient := 1, powers := [(20, 1), (56, 1)] }, { coefficient := 1, powers := [(25, 1), (39, 1)] }, { coefficient := 1, powers := [(25, 1), (44, 1)] }, { coefficient := 1, powers := [(30, 1), (36, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (37, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (47, 1), (54, 1)] }, { coefficient := 1, powers := [(19, 1), (42, 1), (54, 1)] }, { coefficient := 1, powers := [(19, 1), (49, 1), (57, 1)] }, { coefficient := 1, powers := [(24, 1), (40, 1), (42, 1)] }, { coefficient := 1, powers := [(24, 1), (47, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (36, 1), (59, 1)] }, { coefficient := 1, powers := [(1, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(1, 1), (44, 1), (51, 1)] }, { coefficient := 1, powers := [(4, 1), (25, 1), (59, 1)] }, { coefficient := 1, powers := [(4, 1), (30, 1), (56, 1)] }, { coefficient := 1, powers := [(4, 1), (33, 1), (51, 1)] }, { coefficient := 1, powers := [(7, 1), (20, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (30, 1), (44, 1)] }, { coefficient := 1, powers := [(7, 1), (33, 1), (39, 1)] }, { coefficient := 1, powers := [(10, 1), (20, 1), (56, 1)] }, { coefficient := 1, powers := [(10, 1), (25, 1), (44, 1)] }, { coefficient := 1, powers := [(10, 1), (33, 1), (36, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1), (51, 1)] }, { coefficient := 1, powers := [(14, 1), (25, 1), (39, 1)] }, { coefficient := 1, powers := [(14, 1), (30, 1), (36, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (37, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (47, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (28, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (22, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1), (47, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (40, 1)] }, { coefficient := 1, powers := [(12, 1), (22, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1), (28, 1), (47, 1)] }, { coefficient := 1, powers := [(12, 1), (34, 1), (37, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (54, 1)] }, { coefficient := 1, powers := [(17, 1), (28, 1), (40, 1)] }, { coefficient := 1, powers := [(17, 1), (31, 1), (37, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (61, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1)] }],
  [{ coefficient := 1, powers := [(40, 1)] }],
  [{ coefficient := 1, powers := [(57, 1)] }],
  [{ coefficient := 1, powers := [(23, 1)] }],
  [{ coefficient := 1, powers := [(25, 1)] }],
  [{ coefficient := 1, powers := [(28, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 30 → SparsePoly (Fin 67) := ![
  [{ coefficient := 1, powers := [(4, 1), (22, 1), (56, 1), (60, 1)] }, { coefficient := -1, powers := [(7, 1), (22, 1), (44, 1), (60, 1)] }, { coefficient := -1, powers := [(10, 1), (22, 1), (36, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (10, 1), (22, 1), (51, 1), (53, 1), (60, 1)] }, { coefficient := -1, powers := [(7, 1), (22, 1), (53, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(16, 1), (47, 1)] }],
  [{ coefficient := -1, powers := [(16, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (49, 1), (53, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (51, 1), (54, 1)] }, { coefficient := -1, powers := [(2, 1), (54, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (22, 1), (51, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (22, 1), (44, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (42, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(22, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(54, 1)] }],
  [{ coefficient := 1, powers := [(47, 1)] }],
  [{ coefficient := 1, powers := [(17, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (49, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (20, 1), (22, 1), (51, 1), (60, 1)] }, { coefficient := -1, powers := [(8, 1), (20, 1), (22, 1), (56, 1), (60, 1)] }, { coefficient := -1, powers := [(8, 1), (22, 1), (33, 1), (36, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (10, 1), (22, 1), (51, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (10, 1), (22, 1), (51, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (22, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(12, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (10, 1), (22, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (14, 1), (22, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (22, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(2, 1), (37, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (22, 1), (36, 1), (59, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (22, 1), (39, 1), (56, 1), (60, 1)] }, { coefficient := -1, powers := [(8, 1), (22, 1), (44, 1), (51, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (24, 1), (42, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (2, 1), (40, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (40, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (47, 1), (49, 1), (53, 1), (61, 1)] }, { coefficient := -1, powers := [(2, 1), (47, 1), (51, 1), (54, 1)] }, { coefficient := 1, powers := [(2, 1), (47, 1), (54, 1), (61, 1)] }, { coefficient := 1, powers := [(4, 1), (8, 1), (20, 1), (22, 1), (51, 1), (59, 1), (60, 1)] }, { coefficient := 1, powers := [(4, 1), (8, 1), (20, 1), (22, 1), (56, 1), (59, 1), (60, 1)] }, { coefficient := 1, powers := [(4, 1), (8, 1), (22, 1), (33, 1), (36, 1), (59, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (10, 1), (20, 1), (22, 1), (44, 1), (51, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (10, 1), (20, 1), (22, 1), (44, 1), (56, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (10, 1), (22, 1), (33, 1), (36, 1), (44, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (14, 1), (20, 1), (22, 1), (39, 1), (51, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (14, 1), (20, 1), (22, 1), (39, 1), (56, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (14, 1), (22, 1), (33, 1), (36, 1), (39, 1), (60, 1)] }, { coefficient := -1, powers := [(16, 1), (22, 1), (39, 1), (42, 1), (54, 1)] }, { coefficient := -1, powers := [(16, 1), (22, 1), (42, 1), (44, 1), (54, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1), (45, 1), (54, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (39, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (8, 1), (22, 1), (59, 1), (60, 1)] }, { coefficient := -1, powers := [(8, 1), (10, 1), (22, 1), (39, 1), (60, 1)] }, { coefficient := -1, powers := [(8, 1), (10, 1), (22, 1), (44, 1), (60, 1)] }, { coefficient := -1, powers := [(8, 1), (14, 1), (22, 1), (44, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (60, 1)] }, { coefficient := 1, powers := [(12, 1), (42, 1), (46, 1)] }, { coefficient := -1, powers := [(12, 1), (47, 1)] }, { coefficient := 1, powers := [(16, 1), (47, 1), (49, 1)] }, { coefficient := -1, powers := [(17, 1), (46, 1), (49, 1)] }]
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
    (values : Fin 67 → R) :
    ¬ ∀ index : Fin 30,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component39.SelectedLeafB5_6_6_0.selectedHasNoCommonZero

end Krenn.Component39.SelectedLeafB5_6_6_0
