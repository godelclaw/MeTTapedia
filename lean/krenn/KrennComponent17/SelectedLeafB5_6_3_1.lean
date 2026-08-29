import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component17.SelectedLeafB5_6_3_1

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "17a71bfb7731442ec2a052094255c171cdb16fe5855d1f33145a768b6f409e3d"
def certificateSHA256 : String := "91cfdc2c3ce2a8b001c8fd974971dc9f0c8429686712fe820e6a8cb38a430d26"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 37 → Fin 614 := ![
  5,
  7,
  17,
  18,
  32,
  60,
  206,
  210,
  306,
  307,
  311,
  312,
  325,
  327,
  330,
  334,
  410,
  415,
  430,
  432,
  436,
  441,
  454,
  541,
  550,
  552,
  567,
  568,
  599,
  601,
  602,
  604,
  607,
  608,
  609,
  610,
  611
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 37 → SparsePoly (Fin 66) := ![
  [{ coefficient := 1, powers := [(3, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (32, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (19, 1)] }, { coefficient := 1, powers := [(17, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (43, 1)] }, { coefficient := 1, powers := [(27, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1)] }, { coefficient := 1, powers := [(19, 1), (43, 1)] }, { coefficient := 1, powers := [(24, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1)] }, { coefficient := 1, powers := [(20, 1), (43, 1)] }, { coefficient := 1, powers := [(24, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (58, 1)] }, { coefficient := 1, powers := [(13, 1), (47, 1)] }, { coefficient := 1, powers := [(18, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (56, 1)] }, { coefficient := 1, powers := [(9, 1), (53, 1)] }, { coefficient := 1, powers := [(14, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (52, 1)] }, { coefficient := 1, powers := [(29, 1), (41, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (36, 1), (58, 1)] }, { coefficient := 1, powers := [(3, 1), (24, 1), (58, 1)] }, { coefficient := 1, powers := [(6, 1), (19, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1), (50, 1)] }, { coefficient := 1, powers := [(19, 1), (43, 1), (50, 1)] }, { coefficient := 1, powers := [(43, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1), (50, 1)] }, { coefficient := 1, powers := [(20, 1), (43, 1), (50, 1)] }, { coefficient := 1, powers := [(47, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (19, 1), (50, 1)] }, { coefficient := 1, powers := [(17, 1), (19, 1), (54, 1)] }, { coefficient := 1, powers := [(17, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (24, 1), (45, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (40, 1)] }, { coefficient := 1, powers := [(18, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (47, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1)] }, { coefficient := 1, powers := [(17, 1), (27, 1), (47, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (50, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (50, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (54, 1)] }, { coefficient := 1, powers := [(17, 1), (28, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (35, 1)] }, { coefficient := 1, powers := [(22, 1), (43, 1)] }, { coefficient := 1, powers := [(27, 1), (43, 1)] }, { coefficient := 1, powers := [(35, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (58, 1)] }, { coefficient := 1, powers := [(13, 1), (25, 1), (45, 1)] }, { coefficient := 1, powers := [(13, 1), (55, 1)] }, { coefficient := 1, powers := [(18, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1), (51, 1)] }, { coefficient := 1, powers := [(19, 1), (43, 1), (51, 1)] }, { coefficient := 1, powers := [(19, 1), (55, 1)] }, { coefficient := 1, powers := [(25, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (43, 1), (51, 1)] }, { coefficient := 1, powers := [(23, 1), (55, 1)] }, { coefficient := 1, powers := [(29, 1), (47, 1)] }, { coefficient := 1, powers := [(35, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (50, 1)] }, { coefficient := 1, powers := [(3, 1), (57, 1)] }, { coefficient := 1, powers := [(19, 1), (50, 1)] }, { coefficient := 1, powers := [(19, 1), (54, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (38, 1), (58, 1)] }, { coefficient := 1, powers := [(0, 1), (41, 1), (55, 1)] }, { coefficient := 1, powers := [(0, 1), (47, 1), (52, 1)] }, { coefficient := 1, powers := [(20, 1), (43, 1), (52, 1)] }, { coefficient := 1, powers := [(25, 1), (41, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1)] }, { coefficient := 1, powers := [(3, 1), (33, 1)] }, { coefficient := 1, powers := [(14, 1), (19, 1)] }, { coefficient := 1, powers := [(19, 1), (53, 1)] }, { coefficient := 1, powers := [(24, 1), (42, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (48, 1)] }, { coefficient := 1, powers := [(6, 1), (30, 1)] }, { coefficient := 1, powers := [(9, 1), (24, 1)] }, { coefficient := 1, powers := [(19, 1), (48, 1)] }, { coefficient := 1, powers := [(24, 1), (39, 1)] }, { coefficient := 1, powers := [(30, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (36, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (39, 1), (53, 1)] }, { coefficient := 1, powers := [(0, 1), (42, 1), (48, 1)] }, { coefficient := 1, powers := [(3, 1), (24, 1), (56, 1)] }, { coefficient := 1, powers := [(3, 1), (30, 1), (53, 1)] }, { coefficient := 1, powers := [(3, 1), (33, 1), (48, 1)] }, { coefficient := 1, powers := [(6, 1), (19, 1), (56, 1)] }, { coefficient := 1, powers := [(6, 1), (30, 1), (42, 1)] }, { coefficient := 1, powers := [(6, 1), (33, 1), (39, 1)] }, { coefficient := 1, powers := [(9, 1), (19, 1), (53, 1)] }, { coefficient := 1, powers := [(9, 1), (24, 1), (42, 1)] }, { coefficient := 1, powers := [(9, 1), (33, 1), (36, 1)] }, { coefficient := 1, powers := [(14, 1), (19, 1), (48, 1)] }, { coefficient := 1, powers := [(14, 1), (24, 1), (39, 1)] }, { coefficient := 1, powers := [(14, 1), (30, 1), (36, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (41, 1), (55, 1)] }, { coefficient := 1, powers := [(2, 1), (47, 1), (52, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (52, 1)] }, { coefficient := 1, powers := [(8, 1), (23, 1), (58, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (47, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(13, 1), (23, 1), (55, 1)] }, { coefficient := 1, powers := [(13, 1), (29, 1), (47, 1)] }, { coefficient := 1, powers := [(13, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (52, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (41, 1)] }, { coefficient := 1, powers := [(18, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (59, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (60, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(41, 1)] }],
  [{ coefficient := 1, powers := [(53, 1)] }],
  [{ coefficient := 1, powers := [(54, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(55, 1), (64, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(24, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 37 → SparsePoly (Fin 66) := ![
  [{ coefficient := -1, powers := [(2, 1), (38, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (8, 1), (23, 1), (36, 1), (56, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (19, 1), (38, 1), (57, 1), (59, 1)] }, { coefficient := -1, powers := [(8, 1), (9, 1), (19, 1), (23, 1), (33, 1), (36, 1), (57, 1), (59, 1)] }, { coefficient := -1, powers := [(8, 1), (14, 1), (23, 1), (30, 1), (36, 1), (57, 1)] }, { coefficient := 1, powers := [(8, 1), (19, 1), (23, 1), (33, 1), (36, 1), (48, 1), (57, 1), (59, 1)] }, { coefficient := 1, powers := [(8, 1), (19, 1), (23, 1), (36, 1), (56, 1), (57, 1)] }, { coefficient := 1, powers := [(8, 1), (23, 1), (30, 1), (36, 1), (42, 1), (57, 1)] }, { coefficient := 1, powers := [(8, 1), (23, 1), (33, 1), (36, 1), (39, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (38, 1), (57, 1)] }, { coefficient := 1, powers := [(27, 1), (38, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (23, 1), (25, 1), (57, 1)] }, { coefficient := 1, powers := [(23, 1), (25, 1), (36, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (43, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (55, 1), (57, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (22, 1), (50, 2), (60, 1)] }, { coefficient := -2, powers := [(0, 1), (22, 1), (50, 1), (54, 1), (60, 1)] }, { coefficient := -1, powers := [(0, 1), (22, 1), (54, 2), (60, 1)] }, { coefficient := -1, powers := [(0, 1), (28, 1), (50, 1), (60, 1)] }, { coefficient := -1, powers := [(0, 1), (28, 1), (54, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(13, 1), (36, 1), (51, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (27, 1), (50, 1), (52, 1), (57, 1)] }, { coefficient := -1, powers := [(25, 1), (50, 2), (64, 1)] }, { coefficient := -1, powers := [(25, 1), (50, 1), (54, 1), (64, 1)] }, { coefficient := 1, powers := [(50, 1), (51, 1), (64, 1)] }, { coefficient := 1, powers := [(51, 1), (54, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (3, 1), (50, 1), (52, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (36, 1), (50, 1), (52, 1), (57, 1)] }, { coefficient := -1, powers := [(2, 1), (36, 1), (52, 1), (57, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (8, 1), (32, 1), (50, 1), (57, 1)] }, { coefficient := -1, powers := [(13, 1), (27, 1), (36, 1), (50, 1), (51, 1), (57, 1)] }, { coefficient := 1, powers := [(13, 1), (29, 1), (36, 1), (50, 1), (57, 1)] }, { coefficient := 1, powers := [(17, 1), (27, 1), (36, 1), (50, 1), (52, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (29, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (8, 1), (23, 1), (36, 1), (57, 1), (58, 1)] }, { coefficient := -1, powers := [(8, 1), (19, 1), (23, 1), (36, 1), (57, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (18, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (38, 1), (57, 1), (59, 1)] }, { coefficient := 1, powers := [(8, 1), (9, 1), (23, 1), (33, 1), (36, 1), (57, 1), (59, 1)] }, { coefficient := -1, powers := [(8, 1), (23, 1), (33, 1), (36, 1), (48, 1), (57, 1), (59, 1)] }, { coefficient := 1, powers := [(8, 1), (23, 1), (36, 1), (56, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (27, 1), (52, 1), (57, 1)] }, { coefficient := 1, powers := [(25, 1), (50, 1), (64, 1)] }, { coefficient := 1, powers := [(25, 1), (54, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (3, 1), (52, 1), (57, 1)] }, { coefficient := -1, powers := [(2, 1), (36, 1), (52, 1), (57, 1)] }, { coefficient := -1, powers := [(3, 1), (8, 1), (32, 1), (57, 1)] }, { coefficient := 1, powers := [(13, 1), (27, 1), (36, 1), (51, 1), (57, 1)] }, { coefficient := -1, powers := [(13, 1), (29, 1), (36, 1), (57, 1)] }, { coefficient := -1, powers := [(17, 1), (27, 1), (36, 1), (52, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (22, 1), (50, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (22, 1), (54, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (28, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (23, 1), (52, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(36, 1), (52, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (52, 1), (57, 1)] }, { coefficient := -1, powers := [(13, 1), (38, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (23, 1), (57, 1)] }, { coefficient := -1, powers := [(23, 1), (36, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [(50, 1), (64, 1)] }, { coefficient := -1, powers := [(54, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (36, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (36, 1), (57, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (23, 1), (36, 1), (48, 1), (57, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (14, 1), (23, 1), (36, 1), (57, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (23, 1), (36, 1), (57, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (9, 1), (23, 1), (33, 1), (36, 2), (57, 1), (58, 1)] }, { coefficient := 1, powers := [(8, 1), (23, 1), (33, 1), (36, 2), (48, 1), (57, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (50, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (2, 1), (36, 1), (55, 1), (57, 1), (59, 1)] }, { coefficient := -1, powers := [(2, 1), (3, 1), (55, 1), (57, 1)] }, { coefficient := -1, powers := [(2, 1), (25, 1), (36, 1), (43, 1), (57, 1), (59, 1)] }, { coefficient := -1, powers := [(3, 1), (8, 1), (35, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (18, 1), (29, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (8, 1), (9, 1), (23, 1), (36, 1), (57, 1), (58, 1)] }, { coefficient := 1, powers := [(0, 1), (8, 1), (23, 1), (36, 1), (39, 1), (57, 1), (58, 1)] }, { coefficient := 1, powers := [(3, 1), (8, 1), (23, 1), (30, 1), (36, 1), (57, 1), (58, 1)] }, { coefficient := 2, powers := [(8, 1), (9, 1), (19, 1), (23, 1), (36, 1), (57, 1), (58, 1)] }, { coefficient := -1, powers := [(8, 1), (19, 1), (23, 1), (36, 1), (48, 1), (57, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (5, 1), (32, 1), (55, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (50, 1)] }, { coefficient := 1, powers := [(19, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (17, 1), (22, 1), (50, 2), (60, 1)] }, { coefficient := 2, powers := [(0, 1), (17, 1), (22, 1), (50, 1), (54, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (17, 1), (22, 1), (54, 2), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (17, 1), (28, 1), (50, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (17, 1), (28, 1), (54, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (3, 1), (38, 1), (57, 1), (58, 1), (59, 1)] }, { coefficient := -1, powers := [(2, 1), (3, 1), (47, 1), (50, 1), (52, 1), (57, 1)] }, { coefficient := -1, powers := [(2, 1), (36, 1), (47, 1), (50, 1), (52, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (36, 1), (47, 1), (52, 1), (57, 1), (59, 1)] }, { coefficient := -1, powers := [(3, 1), (8, 1), (9, 1), (23, 1), (33, 1), (36, 1), (57, 1), (58, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (8, 1), (23, 1), (33, 1), (36, 1), (48, 1), (57, 1), (58, 1), (59, 1)] }, { coefficient := -1, powers := [(3, 1), (8, 1), (32, 1), (47, 1), (50, 1), (57, 1)] }, { coefficient := -1, powers := [(3, 1), (17, 1), (23, 1), (45, 1), (52, 1), (57, 1)] }, { coefficient := -1, powers := [(3, 1), (18, 1), (23, 1), (40, 1), (52, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (27, 1), (43, 1), (50, 1), (52, 1), (57, 1)] }, { coefficient := -1, powers := [(8, 1), (9, 1), (14, 1), (23, 1), (36, 1), (57, 1), (58, 1)] }, { coefficient := 1, powers := [(8, 1), (9, 1), (23, 1), (36, 1), (42, 1), (57, 1), (58, 1)] }, { coefficient := -1, powers := [(8, 1), (23, 1), (36, 1), (42, 1), (48, 1), (57, 1), (58, 1)] }, { coefficient := 1, powers := [(13, 1), (27, 1), (36, 1), (47, 1), (50, 1), (51, 1), (57, 1)] }, { coefficient := -1, powers := [(13, 1), (29, 1), (36, 1), (47, 1), (50, 1), (57, 1)] }, { coefficient := -1, powers := [(17, 1), (27, 1), (36, 1), (47, 1), (50, 1), (52, 1), (57, 1)] }, { coefficient := 1, powers := [(25, 1), (43, 1), (50, 2), (64, 1)] }, { coefficient := 1, powers := [(25, 1), (43, 1), (50, 1), (54, 1), (64, 1)] }, { coefficient := -1, powers := [(43, 1), (50, 1), (51, 1), (64, 1)] }, { coefficient := -1, powers := [(43, 1), (51, 1), (54, 1), (64, 1)] }]
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
    (values : Fin 66 → R) :
    ¬ ∀ index : Fin 37,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component17.SelectedLeafB5_6_3_1.selectedHasNoCommonZero

end Krenn.Component17.SelectedLeafB5_6_3_1
