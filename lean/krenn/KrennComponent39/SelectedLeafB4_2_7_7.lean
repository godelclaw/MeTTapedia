import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component39.SelectedLeafB4_2_7_7

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "436413cbafce42d540f02db35d7fc8cf7491be2cac28d88bf58ec77f38343ffa"
def certificateSHA256 : String := "61c0f828127195fedc876f6e6081db432cfbbe5ae2a1a3d57bd9d713f79f7aa2"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 26 → Fin 673 := ![
  16,
  22,
  28,
  29,
  30,
  31,
  190,
  191,
  261,
  277,
  300,
  301,
  314,
  350,
  430,
  440,
  451,
  463,
  581,
  625,
  660,
  663,
  666,
  667,
  671,
  672
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 26 → SparsePoly (Fin 69) := ![
  [{ coefficient := 1, powers := [(12, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (45, 1)] }, { coefficient := -1, powers := [(27, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (54, 1)] }, { coefficient := 1, powers := [(28, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (21, 1), (53, 1)] }, { coefficient := 1, powers := [(28, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (23, 1), (47, 1)] }, { coefficient := 1, powers := [(17, 1), (19, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1)] }, { coefficient := 1, powers := [(18, 1), (42, 1)] }, { coefficient := 1, powers := [(23, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (42, 1)] }, { coefficient := 1, powers := [(23, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (21, 1)] }, { coefficient := 1, powers := [(21, 1), (55, 1)] }, { coefficient := 1, powers := [(26, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (28, 1), (59, 1)] }, { coefficient := 1, powers := [(21, 1), (53, 1)] }, { coefficient := 1, powers := [(28, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (60, 1)] }, { coefficient := 1, powers := [(12, 1), (47, 1)] }, { coefficient := 1, powers := [(17, 1), (19, 1), (52, 1)] }, { coefficient := 1, powers := [(17, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (54, 1)] }, { coefficient := 1, powers := [(28, 1), (40, 1)] }, { coefficient := 1, powers := [(28, 1), (46, 1), (49, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1), (52, 1)] }, { coefficient := 1, powers := [(3, 1), (60, 1)] }, { coefficient := 1, powers := [(18, 1), (42, 1), (52, 1)] }, { coefficient := 1, powers := [(42, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1), (54, 1)] }, { coefficient := 1, powers := [(24, 1), (45, 1), (49, 1)] }, { coefficient := 1, powers := [(42, 1), (54, 1)] }, { coefficient := 1, powers := [(49, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (51, 1)] }, { coefficient := 1, powers := [(3, 1), (59, 1)] }, { coefficient := 1, powers := [(18, 1), (51, 1)] }, { coefficient := 1, powers := [(18, 1), (56, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(3, 1), (28, 1), (60, 1)] }, { coefficient := 1, powers := [(3, 1), (31, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (34, 1), (54, 1)] }, { coefficient := 1, powers := [(21, 1), (42, 1), (54, 1)] }, { coefficient := 1, powers := [(21, 1), (49, 1), (57, 1)] }, { coefficient := 1, powers := [(28, 1), (42, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (37, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (47, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (28, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (22, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1), (47, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (40, 1)] }, { coefficient := 1, powers := [(12, 1), (22, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1), (28, 1), (47, 1)] }, { coefficient := 1, powers := [(12, 1), (34, 1), (37, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (54, 1)] }, { coefficient := 1, powers := [(17, 1), (28, 1), (40, 1)] }, { coefficient := 1, powers := [(17, 1), (31, 1), (37, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(40, 1)] }],
  [{ coefficient := 1, powers := [(55, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(25, 1), (67, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(28, 1), (68, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 26 → SparsePoly (Fin 69) := ![
  [{ coefficient := -1, powers := [(3, 1), (22, 1), (57, 1), (59, 1), (67, 1)] }, { coefficient := -1, powers := [(3, 1), (34, 1), (37, 1), (59, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (3, 1), (28, 1), (47, 1), (52, 1), (59, 1), (67, 1)] }, { coefficient := 1, powers := [(3, 1), (19, 1), (28, 1), (42, 1), (52, 1), (59, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(26, 1), (53, 1), (63, 1), (67, 1), (68, 1)] }, { coefficient := -1, powers := [(28, 1), (63, 1), (67, 1), (68, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (5, 1), (27, 1), (54, 1), (59, 1), (67, 1)] }, { coefficient := -1, powers := [(5, 1), (21, 1), (54, 1), (59, 1), (67, 1)] }, { coefficient := 1, powers := [(5, 1), (23, 1), (28, 1), (52, 1), (59, 1), (67, 1)] }, { coefficient := -1, powers := [(5, 1), (24, 1), (27, 1), (49, 1), (59, 1), (67, 1)] }, { coefficient := -1, powers := [(5, 1), (28, 1), (49, 1), (59, 1), (67, 1)] }, { coefficient := -1, powers := [(8, 1), (22, 1), (23, 1), (52, 1), (59, 1), (67, 1)] }, { coefficient := 1, powers := [(8, 1), (22, 1), (49, 1), (59, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (17, 1), (28, 1), (49, 1), (59, 1), (67, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (8, 1), (31, 1), (59, 1), (67, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (5, 1), (54, 1), (59, 1)] }, { coefficient := -1, powers := [(5, 1), (24, 1), (49, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (42, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(63, 1), (68, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (28, 1), (52, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (28, 1), (52, 1), (59, 1)] }, { coefficient := 1, powers := [(8, 1), (22, 1), (52, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (16, 1), (28, 1), (52, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(53, 1), (63, 1), (68, 1)] }],
  [{ coefficient := 1, powers := [(68, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (28, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (17, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (28, 1), (59, 1)] }, { coefficient := -1, powers := [(8, 1), (22, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (21, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(28, 1), (68, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := -1, powers := [(5, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (37, 1), (59, 1), (60, 1)] }, { coefficient := -1, powers := [(3, 1), (40, 1), (57, 1), (59, 1)] }, { coefficient := -1, powers := [(3, 1), (47, 1), (54, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (8, 1), (34, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (17, 1), (28, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (53, 1), (68, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (3, 1), (16, 1), (28, 1), (47, 1), (52, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (5, 1), (27, 1), (42, 1), (54, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (8, 1), (31, 1), (47, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (12, 1), (22, 1), (57, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (12, 1), (34, 1), (37, 1), (59, 1)] }, { coefficient := -1, powers := [(3, 1), (16, 1), (19, 1), (28, 1), (42, 1), (52, 1), (59, 1)] }, { coefficient := -1, powers := [(3, 1), (17, 1), (28, 1), (46, 1), (49, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (21, 1), (42, 1), (54, 1), (59, 1)] }, { coefficient := -1, powers := [(5, 1), (23, 1), (28, 1), (42, 1), (52, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (24, 1), (27, 1), (42, 1), (49, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (28, 1), (42, 1), (49, 1), (59, 1)] }, { coefficient := 1, powers := [(8, 1), (22, 1), (23, 1), (42, 1), (52, 1), (59, 1)] }, { coefficient := -1, powers := [(8, 1), (22, 1), (42, 1), (49, 1), (59, 1)] }, { coefficient := -1, powers := [(26, 1), (41, 1), (53, 1), (63, 1), (68, 1)] }, { coefficient := 1, powers := [(28, 1), (41, 1), (63, 1), (68, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (51, 1)] }, { coefficient := 1, powers := [(18, 1), (51, 1)] }, { coefficient := 1, powers := [(18, 1), (56, 1)] }]
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
    (values : Fin 69 → R) :
    ¬ ∀ index : Fin 26,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component39.SelectedLeafB4_2_7_7.selectedHasNoCommonZero

end Krenn.Component39.SelectedLeafB4_2_7_7
