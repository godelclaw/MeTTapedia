import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component62.SelectedLeafB0_7_6

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "bbb7fedb3293e0836db880d826e172836a7af10a91036d019835277b895598c1"
def certificateSHA256 : String := "d8ecc3b70c9516d5009dc2f65624a37c34197520eff7c6f1e4d4ad9df8892b95"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 37 → Fin 667 := ![
  18,
  21,
  54,
  83,
  97,
  137,
  141,
  149,
  150,
  151,
  154,
  158,
  160,
  187,
  224,
  252,
  294,
  301,
  302,
  311,
  318,
  338,
  408,
  441,
  454,
  480,
  557,
  599,
  610,
  657,
  658,
  660,
  661,
  662,
  664,
  665,
  666
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 37 → SparsePoly (Fin 65) := ![
  [{ coefficient := 1, powers := [(22, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (33, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (27, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (22, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (52, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (27, 1)] }, { coefficient := 1, powers := [(27, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (41, 1)] }, { coefficient := 1, powers := [(17, 1), (18, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (44, 1)] }, { coefficient := 1, powers := [(17, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (22, 1)] }, { coefficient := 1, powers := [(22, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (41, 1)] }, { coefficient := 1, powers := [(17, 1), (18, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (50, 1)] }, { coefficient := 1, powers := [(22, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (38, 1)] }, { coefficient := 1, powers := [(27, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (33, 1), (52, 1)] }, { coefficient := 1, powers := [(27, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (23, 1), (44, 1)] }, { coefficient := 1, powers := [(17, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (23, 1), (46, 1)] }, { coefficient := 1, powers := [(17, 1), (19, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1)] }, { coefficient := 1, powers := [(19, 1), (41, 1)] }, { coefficient := 1, powers := [(23, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (46, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (53, 1)] }, { coefficient := 1, powers := [(8, 1), (30, 1)] }, { coefficient := 1, powers := [(12, 1), (27, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (44, 1)] }, { coefficient := 1, powers := [(17, 1), (38, 1)] }, { coefficient := 1, powers := [(17, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1), (50, 1)] }, { coefficient := 1, powers := [(19, 1), (41, 1), (50, 1)] }, { coefficient := 1, powers := [(46, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (24, 1), (49, 1)] }, { coefficient := 1, powers := [(11, 1), (27, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (23, 1), (44, 1)] }, { coefficient := 1, powers := [(17, 1), (23, 1), (38, 1)] }, { coefficient := 1, powers := [(17, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (59, 1)] }, { coefficient := 1, powers := [(12, 1), (46, 1)] }, { coefficient := 1, powers := [(17, 1), (19, 1), (51, 1)] }, { coefficient := 1, powers := [(17, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (53, 1)] }, { coefficient := 1, powers := [(27, 1), (39, 1)] }, { coefficient := 1, powers := [(27, 1), (45, 1), (48, 1)] }, { coefficient := 1, powers := [(30, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1), (50, 1)] }, { coefficient := 1, powers := [(19, 1), (50, 1)] }, { coefficient := 1, powers := [(19, 1), (55, 1)] }, { coefficient := 1, powers := [(45, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (41, 1), (52, 1)] }, { coefficient := 1, powers := [(22, 1), (56, 1)] }, { coefficient := 1, powers := [(27, 1), (46, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (24, 1), (41, 1), (49, 1)] }, { coefficient := 1, powers := [(2, 1), (37, 1), (56, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (37, 1)] }, { coefficient := 1, powers := [(11, 1), (27, 1), (41, 1)] }, { coefficient := 1, powers := [(17, 1), (27, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (39, 1), (55, 1)] }, { coefficient := 1, powers := [(0, 1), (45, 1), (51, 1)] }, { coefficient := 1, powers := [(19, 1), (48, 1), (55, 1)] }, { coefficient := 1, powers := [(19, 1), (51, 1)] }, { coefficient := 1, powers := [(39, 1)] }, { coefficient := 1, powers := [(45, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (36, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (46, 1), (53, 1)] }, { coefficient := 1, powers := [(5, 1), (27, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (53, 1)] }, { coefficient := 1, powers := [(8, 1), (22, 1), (59, 1)] }, { coefficient := 1, powers := [(8, 1), (30, 1), (46, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (39, 1)] }, { coefficient := 1, powers := [(12, 1), (22, 1), (56, 1)] }, { coefficient := 1, powers := [(12, 1), (27, 1), (46, 1)] }, { coefficient := 1, powers := [(12, 1), (33, 1), (36, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (53, 1)] }, { coefficient := 1, powers := [(17, 1), (27, 1), (39, 1)] }, { coefficient := 1, powers := [(17, 1), (30, 1), (36, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1)] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(37, 1), (60, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(38, 1), (61, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(54, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(55, 1), (64, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(56, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 37 → SparsePoly (Fin 65) := ![
  [{ coefficient := -1, powers := [(12, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(17, 1), (45, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (19, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(17, 1), (39, 1), (60, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (59, 1), (63, 1), (64, 1)] }, { coefficient := -1, powers := [(17, 1), (53, 1), (63, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(37, 1), (39, 1), (41, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (39, 1), (43, 1), (60, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (27, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (23, 1), (27, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (59, 1), (63, 1)] }, { coefficient := -1, powers := [(17, 1), (53, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(19, 1), (27, 1), (51, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (13, 1), (59, 1), (63, 1), (64, 1)] }, { coefficient := 1, powers := [(13, 1), (17, 1), (53, 1), (63, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(17, 1), (39, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (19, 1), (50, 1)] }],
  [{ coefficient := -1, powers := [(19, 1), (27, 1), (50, 1)] }],
  [{ coefficient := -1, powers := [(27, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (27, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(53, 1)] }],
  [{ coefficient := 1, powers := [(46, 1)] }],
  [{ coefficient := -1, powers := [(19, 1), (23, 1), (27, 1), (51, 1)] }],
  [{ coefficient := -2, powers := [(12, 1), (27, 1)] }],
  [{ coefficient := -1, powers := [(39, 1), (41, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (27, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(27, 1)] }],
  [{ coefficient := 1, powers := [(17, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (27, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(12, 1)] }],
  [{ coefficient := 1, powers := [(39, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(17, 1), (27, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := 2, powers := [(12, 1), (27, 1), (46, 1), (50, 1)] }, { coefficient := -1, powers := [(16, 1), (27, 1), (46, 1), (51, 1)] }, { coefficient := 1, powers := [(17, 1), (27, 1), (39, 1), (55, 1)] }, { coefficient := -1, powers := [(17, 1), (27, 1), (45, 1), (48, 1), (50, 1)] }, { coefficient := 1, powers := [(17, 1), (27, 1), (45, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(36, 1), (59, 1)] }, { coefficient := -1, powers := [(37, 1), (39, 1), (41, 1), (52, 1), (60, 1)] }, { coefficient := -1, powers := [(37, 1), (39, 1), (56, 1), (60, 1)] }, { coefficient := 1, powers := [(39, 1), (56, 1)] }, { coefficient := -1, powers := [(46, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (33, 1), (39, 1)] }, { coefficient := -1, powers := [(17, 1), (27, 1), (39, 1), (43, 1), (61, 1)] }, { coefficient := -1, powers := [(17, 1), (27, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (27, 1), (39, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (22, 1), (59, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (13, 1), (22, 1), (59, 1), (63, 1)] }, { coefficient := -1, powers := [(13, 1), (17, 1), (22, 1), (53, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (30, 1)] }]
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
    (values : Fin 65 → R) :
    ¬ ∀ index : Fin 37,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component62.SelectedLeafB0_7_6.selectedHasNoCommonZero

end Krenn.Component62.SelectedLeafB0_7_6
