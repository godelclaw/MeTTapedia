import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component37.SelectedLeafB5_2_4_4

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "9b7594e63877b2689ea336e221a7b33845803e4805d4eba09c0ae031131320be"
def certificateSHA256 : String := "951972dbc929bb180dfdd13158176d9383639956aa2b9979131fda14098e1e75"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 31 → Fin 670 := ![
  6,
  13,
  17,
  147,
  179,
  181,
  298,
  299,
  300,
  301,
  303,
  334,
  354,
  438,
  454,
  566,
  583,
  591,
  602,
  603,
  655,
  656,
  657,
  659,
  660,
  661,
  663,
  665,
  666,
  668,
  669
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 31 → SparsePoly (Fin 67) := ![
  [{ coefficient := 1, powers := [(5, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (31, 1)] }, { coefficient := 1, powers := [(15, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (55, 1)] }, { coefficient := 1, powers := [(30, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (54, 1)] }, { coefficient := 1, powers := [(30, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (46, 1)] }, { coefficient := 1, powers := [(4, 1), (35, 1)] }, { coefficient := 1, powers := [(15, 1), (22, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (52, 1)] }, { coefficient := 1, powers := [(7, 1), (32, 1)] }, { coefficient := 1, powers := [(10, 1), (27, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (50, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (50, 1)] }, { coefficient := 1, powers := [(18, 1), (28, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (59, 1)] }, { coefficient := 1, powers := [(9, 1), (43, 1)] }, { coefficient := 1, powers := [(13, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (46, 1)] }, { coefficient := 1, powers := [(9, 1), (57, 1)] }, { coefficient := 1, powers := [(31, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (39, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (59, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (31, 1), (57, 1)] }, { coefficient := 1, powers := [(7, 1), (31, 1), (46, 1)] }, { coefficient := 1, powers := [(15, 1), (31, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1)] }, { coefficient := 1, powers := [(12, 1), (30, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (55, 1)] }, { coefficient := 1, powers := [(30, 1), (42, 1)] }, { coefficient := 1, powers := [(30, 1), (48, 1), (51, 1)] }, { coefficient := 1, powers := [(33, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (44, 1), (54, 1)] }, { coefficient := 1, powers := [(24, 1), (58, 1)] }, { coefficient := 1, powers := [(30, 1), (49, 1)] }, { coefficient := 1, powers := [(36, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (31, 1), (57, 1)] }, { coefficient := 1, powers := [(9, 1), (20, 1), (57, 1)] }, { coefficient := 1, powers := [(9, 1)] }, { coefficient := 1, powers := [(40, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (37, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (40, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (43, 1), (50, 1)] }, { coefficient := 1, powers := [(17, 1), (23, 1), (50, 1)] }, { coefficient := 1, powers := [(17, 1), (28, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1)] }, { coefficient := 1, powers := [(3, 1), (34, 1)] }, { coefficient := 1, powers := [(13, 1), (20, 1)] }, { coefficient := 1, powers := [(20, 1), (56, 1)] }, { coefficient := 1, powers := [(25, 1), (43, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (50, 1)] }, { coefficient := 1, powers := [(6, 1), (31, 1)] }, { coefficient := 1, powers := [(9, 1), (25, 1)] }, { coefficient := 1, powers := [(20, 1), (50, 1)] }, { coefficient := 1, powers := [(25, 1), (40, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (37, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (40, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (43, 1), (50, 1)] }, { coefficient := 1, powers := [(3, 1), (25, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (31, 1), (56, 1)] }, { coefficient := 1, powers := [(3, 1), (34, 1), (50, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (31, 1), (43, 1)] }, { coefficient := 1, powers := [(6, 1), (34, 1), (40, 1)] }, { coefficient := 1, powers := [(9, 1), (20, 1), (56, 1)] }, { coefficient := 1, powers := [(9, 1), (25, 1), (43, 1)] }, { coefficient := 1, powers := [(9, 1), (34, 1), (37, 1)] }, { coefficient := 1, powers := [(13, 1), (20, 1), (50, 1)] }, { coefficient := 1, powers := [(13, 1), (25, 1), (40, 1)] }, { coefficient := 1, powers := [(13, 1), (31, 1), (37, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1), (38, 1), (60, 1)] }, { coefficient := 1, powers := [(1, 1), (41, 1), (57, 1)] }, { coefficient := 1, powers := [(1, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(4, 1), (27, 1), (60, 1)] }, { coefficient := 1, powers := [(4, 1), (32, 1), (57, 1)] }, { coefficient := 1, powers := [(4, 1), (35, 1), (52, 1)] }, { coefficient := 1, powers := [(7, 1), (22, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (32, 1), (46, 1)] }, { coefficient := 1, powers := [(7, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(10, 1), (22, 1), (57, 1)] }, { coefficient := 1, powers := [(10, 1), (27, 1), (46, 1)] }, { coefficient := 1, powers := [(10, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(15, 1), (22, 1), (52, 1)] }, { coefficient := 1, powers := [(15, 1), (27, 1), (41, 1)] }, { coefficient := 1, powers := [(15, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (39, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (42, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (49, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (49, 1)] }, { coefficient := 1, powers := [(8, 1), (36, 1), (42, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (58, 1)] }, { coefficient := 1, powers := [(12, 1), (30, 1), (49, 1)] }, { coefficient := 1, powers := [(12, 1), (36, 1), (39, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (55, 1)] }, { coefficient := 1, powers := [(19, 1), (30, 1), (42, 1)] }, { coefficient := 1, powers := [(19, 1), (33, 1), (39, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(40, 1)] }],
  [{ coefficient := 1, powers := [(42, 1)] }],
  [{ coefficient := 1, powers := [(57, 1)] }],
  [{ coefficient := 1, powers := [(58, 1)] }],
  [{ coefficient := 1, powers := [(27, 1)] }],
  [{ coefficient := 1, powers := [(30, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 31 → SparsePoly (Fin 67) := ![
  [{ coefficient := 1, powers := [(6, 1), (20, 1), (36, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (23, 1), (63, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (23, 1), (43, 1), (63, 1)] }, { coefficient := 1, powers := [(20, 1), (23, 1), (43, 1), (63, 1)] }, { coefficient := 1, powers := [(20, 1), (23, 1), (56, 1), (63, 1)] }, { coefficient := 1, powers := [(23, 1), (25, 1), (43, 1), (63, 1)] }, { coefficient := 1, powers := [(23, 1), (34, 1), (37, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (22, 1), (56, 1), (60, 1)] }, { coefficient := -1, powers := [(3, 1), (32, 1), (46, 1), (56, 1)] }, { coefficient := 1, powers := [(3, 1), (35, 1), (41, 1), (56, 1)] }, { coefficient := 1, powers := [(13, 1), (22, 1), (37, 1), (60, 1)] }, { coefficient := -1, powers := [(13, 1), (32, 1), (37, 1), (46, 1)] }, { coefficient := 1, powers := [(13, 1), (35, 1), (37, 1), (41, 1)] }, { coefficient := -1, powers := [(22, 1), (37, 1), (43, 1), (60, 1)] }, { coefficient := 1, powers := [(32, 1), (37, 1), (43, 1), (46, 1)] }, { coefficient := -1, powers := [(35, 1), (37, 1), (41, 1), (43, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (18, 1), (20, 1), (49, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (12, 1), (20, 1), (44, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (31, 1), (52, 1), (56, 1)] }, { coefficient := 1, powers := [(13, 1), (31, 1), (37, 1), (52, 1)] }, { coefficient := -1, powers := [(31, 1), (37, 1), (43, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (31, 1), (46, 1), (56, 1)] }, { coefficient := 1, powers := [(13, 1), (31, 1), (37, 1), (46, 1)] }, { coefficient := -1, powers := [(31, 1), (37, 1), (43, 1), (46, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (43, 1), (63, 1)] }, { coefficient := -1, powers := [(20, 1), (43, 1), (63, 1)] }, { coefficient := -1, powers := [(20, 1), (56, 1), (63, 1)] }, { coefficient := -1, powers := [(25, 1), (43, 1), (63, 1)] }, { coefficient := -1, powers := [(34, 1), (37, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(25, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (10, 1), (35, 1), (56, 1)] }, { coefficient := 1, powers := [(10, 1), (13, 1), (35, 1), (37, 1)] }, { coefficient := -1, powers := [(10, 1), (35, 1), (37, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (20, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (32, 1), (56, 1)] }, { coefficient := 1, powers := [(13, 1), (32, 1), (37, 1)] }, { coefficient := -1, powers := [(32, 1), (37, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (20, 1), (49, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (19, 1), (20, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (12, 1), (20, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (10, 1), (35, 1), (46, 1), (56, 1)] }, { coefficient := -1, powers := [(10, 1), (13, 1), (35, 1), (37, 1), (46, 1)] }, { coefficient := 1, powers := [(10, 1), (35, 1), (37, 1), (43, 1), (46, 1)] }, { coefficient := 1, powers := [(20, 1), (56, 1)] }, { coefficient := -1, powers := [(25, 1), (43, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(50, 1)] }],
  [{ coefficient := 1, powers := [(43, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(3, 1), (31, 1), (56, 1)] }, { coefficient := -1, powers := [(13, 1), (31, 1), (37, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1), (43, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (20, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (31, 1), (38, 1), (56, 1), (60, 1)] }, { coefficient := 1, powers := [(3, 1), (31, 1), (41, 1), (56, 1), (57, 1)] }, { coefficient := -1, powers := [(3, 1), (31, 1), (46, 1), (52, 1), (56, 1)] }, { coefficient := 1, powers := [(13, 1), (31, 1), (37, 1), (38, 1), (60, 1)] }, { coefficient := 1, powers := [(13, 1), (31, 1), (37, 1), (41, 1), (57, 1)] }, { coefficient := -1, powers := [(13, 1), (31, 1), (37, 1), (46, 1), (52, 1)] }, { coefficient := -1, powers := [(31, 1), (37, 1), (38, 1), (43, 1), (60, 1)] }, { coefficient := -1, powers := [(31, 1), (37, 1), (41, 1), (43, 1), (57, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1), (43, 1), (46, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (37, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (43, 1), (50, 1)] }, { coefficient := 1, powers := [(20, 1), (43, 1), (50, 1)] }, { coefficient := 1, powers := [(20, 1), (50, 1), (56, 1)] }, { coefficient := 1, powers := [(25, 1), (43, 1), (50, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1), (50, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (2, 1), (56, 1), (63, 1)] }, { coefficient := 1, powers := [(0, 1), (3, 1), (10, 1), (35, 1), (46, 1), (56, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (10, 1), (13, 1), (35, 1), (37, 1), (46, 1), (57, 1)] }, { coefficient := -1, powers := [(0, 1), (10, 1), (35, 1), (37, 1), (43, 1), (46, 1), (57, 1)] }, { coefficient := -1, powers := [(0, 1), (17, 1), (28, 1), (63, 1)] }, { coefficient := 2, powers := [(0, 1), (18, 1), (28, 1), (43, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (20, 1), (56, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (25, 1), (43, 1), (57, 1)] }, { coefficient := -1, powers := [(0, 1), (34, 1), (37, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (56, 1)] }, { coefficient := 1, powers := [(3, 1), (10, 1), (35, 1), (46, 1), (56, 1)] }, { coefficient := -1, powers := [(3, 1), (15, 1), (22, 1), (56, 1), (60, 1)] }, { coefficient := 1, powers := [(3, 1), (15, 1), (32, 1), (46, 1), (56, 1)] }, { coefficient := -1, powers := [(3, 1), (15, 1), (35, 1), (41, 1), (56, 1)] }, { coefficient := 1, powers := [(6, 1), (34, 1)] }, { coefficient := 1, powers := [(10, 1), (13, 1), (35, 1), (37, 1), (46, 1)] }, { coefficient := -1, powers := [(10, 1), (35, 1), (37, 1), (43, 1), (46, 1)] }, { coefficient := -1, powers := [(13, 1), (15, 1), (22, 1), (37, 1), (60, 1)] }, { coefficient := 1, powers := [(13, 1), (15, 1), (32, 1), (37, 1), (46, 1)] }, { coefficient := -1, powers := [(13, 1), (15, 1), (35, 1), (37, 1), (41, 1)] }, { coefficient := 1, powers := [(15, 1), (22, 1), (37, 1), (43, 1), (60, 1)] }, { coefficient := -1, powers := [(15, 1), (32, 1), (37, 1), (43, 1), (46, 1)] }, { coefficient := 1, powers := [(15, 1), (35, 1), (37, 1), (41, 1), (43, 1)] }, { coefficient := 1, powers := [(18, 1), (20, 1), (28, 1), (43, 1), (63, 1)] }, { coefficient := 1, powers := [(18, 1), (20, 1), (28, 1), (56, 1), (63, 1)] }, { coefficient := 1, powers := [(18, 1), (25, 1), (28, 1), (43, 1), (63, 1)] }, { coefficient := 1, powers := [(18, 1), (28, 1), (34, 1), (37, 1), (63, 1)] }, { coefficient := -1, powers := [(20, 1), (56, 1)] }, { coefficient := -1, powers := [(34, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (6, 1), (20, 1), (58, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (8, 1), (20, 1), (36, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(3, 2), (10, 1), (31, 1), (35, 1), (46, 1), (56, 1)] }, { coefficient := 1, powers := [(3, 1), (9, 1), (10, 1), (20, 1), (35, 1), (46, 1), (56, 1)] }, { coefficient := -1, powers := [(3, 1), (9, 1), (10, 1), (35, 1), (56, 1)] }, { coefficient := 1, powers := [(3, 1), (10, 1), (13, 1), (31, 1), (35, 1), (37, 1), (46, 1)] }, { coefficient := 1, powers := [(3, 1), (10, 1), (22, 1), (31, 1), (56, 1)] }, { coefficient := -1, powers := [(3, 1), (10, 1), (31, 1), (35, 1), (37, 1), (43, 1), (46, 1)] }, { coefficient := -1, powers := [(3, 1), (20, 1), (31, 1), (56, 1)] }, { coefficient := 1, powers := [(3, 1), (25, 1), (31, 1), (43, 1)] }, { coefficient := -1, powers := [(3, 1), (31, 1), (34, 1), (37, 1)] }, { coefficient := 1, powers := [(9, 1), (10, 1), (13, 1), (20, 1), (35, 1), (37, 1), (46, 1)] }, { coefficient := -1, powers := [(9, 1), (10, 1), (13, 1), (35, 1), (37, 1)] }, { coefficient := -1, powers := [(9, 1), (10, 1), (20, 1), (35, 1), (37, 1), (43, 1), (46, 1)] }, { coefficient := 1, powers := [(9, 1), (10, 1), (35, 1), (37, 1), (43, 1)] }, { coefficient := -1, powers := [(9, 1), (20, 2), (56, 1)] }, { coefficient := 1, powers := [(9, 1), (20, 1), (25, 1), (43, 1)] }, { coefficient := -1, powers := [(9, 1), (20, 1), (34, 1), (37, 1)] }, { coefficient := 1, powers := [(10, 1), (13, 1), (22, 1), (31, 1), (37, 1)] }, { coefficient := -1, powers := [(10, 1), (22, 1), (31, 1), (37, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (6, 1), (20, 1), (33, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (4, 1), (31, 1), (56, 1), (60, 1)] }, { coefficient := 1, powers := [(3, 1), (15, 1), (31, 1), (41, 1), (56, 1)] }, { coefficient := 1, powers := [(4, 1), (13, 1), (31, 1), (37, 1), (60, 1)] }, { coefficient := -1, powers := [(4, 1), (31, 1), (37, 1), (43, 1), (60, 1)] }, { coefficient := 1, powers := [(13, 1), (15, 1), (31, 1), (37, 1), (41, 1)] }, { coefficient := -1, powers := [(15, 1), (31, 1), (37, 1), (41, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (12, 1), (20, 1), (44, 1), (48, 1), (59, 1)] }, { coefficient := -1, powers := [(6, 1), (12, 1), (20, 1), (49, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (18, 1), (20, 1), (49, 1), (51, 1), (59, 1)] }, { coefficient := -1, powers := [(6, 1), (19, 1), (20, 1), (48, 1), (51, 1), (59, 1)] }]
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
    ¬ ∀ index : Fin 31,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component37.SelectedLeafB5_2_4_4.selectedHasNoCommonZero

end Krenn.Component37.SelectedLeafB5_2_4_4
