import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component24.SelectedLeafB7_6_2_7

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "7d345328f58a45907f8da5c741adcac7dfc1477ca71b84a1d1fcdec0b673c22a"
def certificateSHA256 : String := "c47b6543d1b6aa6f1d46fd0775ba0262bf0b4df57e582f7775999a045344e7c9"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 37 → Fin 676 := ![
  2,
  4,
  22,
  50,
  100,
  132,
  164,
  176,
  196,
  247,
  306,
  356,
  362,
  365,
  472,
  479,
  503,
  525,
  584,
  585,
  593,
  606,
  607,
  608,
  609,
  610,
  611,
  652,
  656,
  661,
  662,
  664,
  665,
  666,
  670,
  673,
  675
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 37 → SparsePoly (Fin 71) := ![
  [{ coefficient := 1, powers := [(8, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (31, 1)] }],
  [{ coefficient := 1, powers := [(31, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (31, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(15, 1), (31, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (31, 1)] }, { coefficient := 1, powers := [(31, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(31, 1), (42, 1)] }, { coefficient := 1, powers := [(31, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (31, 1), (60, 1)] }, { coefficient := 1, powers := [(31, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (24, 1), (60, 1)] }, { coefficient := 1, powers := [(18, 1), (31, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (26, 1), (46, 1)] }, { coefficient := 1, powers := [(18, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (59, 1)] }, { coefficient := 1, powers := [(9, 1), (56, 1)] }, { coefficient := 1, powers := [(15, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (46, 1), (50, 1)] }, { coefficient := 1, powers := [(13, 1), (29, 1), (46, 1)] }, { coefficient := 1, powers := [(18, 1), (30, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (31, 1), (59, 1)] }, { coefficient := 1, powers := [(9, 1), (31, 1), (44, 1)] }, { coefficient := 1, powers := [(15, 1), (31, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (31, 1), (60, 1)] }, { coefficient := 1, powers := [(11, 1), (31, 1), (46, 1)] }, { coefficient := 1, powers := [(16, 1), (31, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(30, 1), (42, 1)] }, { coefficient := 1, powers := [(30, 1), (46, 1)] }, { coefficient := 1, powers := [(30, 1), (53, 1)] }, { coefficient := 1, powers := [(30, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1), (50, 1)] }, { coefficient := 1, powers := [(6, 1), (32, 1), (46, 1)] }, { coefficient := 1, powers := [(9, 1), (26, 1), (46, 1)] }, { coefficient := 1, powers := [(50, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (26, 1), (60, 1)] }, { coefficient := 1, powers := [(11, 1), (26, 1), (46, 1)] }, { coefficient := 1, powers := [(16, 1), (26, 1), (42, 1)] }, { coefficient := 1, powers := [(16, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1)] }, { coefficient := 1, powers := [(6, 1), (60, 1)] }, { coefficient := 1, powers := [(26, 1), (42, 1)] }, { coefficient := 1, powers := [(26, 1), (46, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (53, 1)] }, { coefficient := 1, powers := [(3, 1), (60, 1)] }, { coefficient := 1, powers := [(20, 1), (53, 1)] }, { coefficient := 1, powers := [(20, 1), (57, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1), (38, 1), (59, 1)] }, { coefficient := 1, powers := [(1, 1), (41, 1), (56, 1)] }, { coefficient := 1, powers := [(1, 1), (44, 1), (50, 1)] }, { coefficient := 1, powers := [(10, 1), (22, 1), (56, 1)] }, { coefficient := 1, powers := [(10, 1), (27, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1)] }, { coefficient := 1, powers := [(3, 1), (35, 1)] }, { coefficient := 1, powers := [(15, 1), (20, 1)] }, { coefficient := 1, powers := [(20, 1), (56, 1)] }, { coefficient := 1, powers := [(26, 1), (44, 1)] }, { coefficient := 1, powers := [(35, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (50, 1)] }, { coefficient := 1, powers := [(6, 1), (32, 1)] }, { coefficient := 1, powers := [(9, 1), (26, 1)] }, { coefficient := 1, powers := [(20, 1), (50, 1)] }, { coefficient := 1, powers := [(26, 1), (41, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (46, 1)] }, { coefficient := 1, powers := [(4, 1), (27, 1), (60, 1)] }, { coefficient := 1, powers := [(4, 1), (36, 1)] }, { coefficient := 1, powers := [(11, 1), (27, 1), (46, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (53, 1)] }, { coefficient := 1, powers := [(7, 1), (22, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (33, 1)] }, { coefficient := 1, powers := [(11, 1), (22, 1), (57, 1)] }, { coefficient := 1, powers := [(11, 1), (28, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (60, 1)] }, { coefficient := 1, powers := [(11, 1), (46, 1)] }, { coefficient := 1, powers := [(11, 1), (57, 1)] }, { coefficient := 1, powers := [(16, 1), (42, 1)] }, { coefficient := 1, powers := [(16, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (53, 1)] }, { coefficient := 1, powers := [(23, 1), (57, 1)] }, { coefficient := 1, powers := [(28, 1), (42, 1)] }, { coefficient := 1, powers := [(28, 1), (46, 1)] }, { coefficient := 1, powers := [(33, 1), (39, 1)] }, { coefficient := 1, powers := [(36, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (39, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (42, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (46, 1), (53, 1)] }, { coefficient := 1, powers := [(42, 1)] }, { coefficient := 1, powers := [(46, 1)] }, { coefficient := 1, powers := [(53, 1)] }, { coefficient := 1, powers := [(57, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (39, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (42, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (46, 1), (53, 1)] }, { coefficient := 1, powers := [(18, 1), (30, 1), (42, 1)] }, { coefficient := 1, powers := [(18, 1), (30, 1), (46, 1)] }, { coefficient := 1, powers := [(18, 1), (30, 1), (53, 1)] }, { coefficient := 1, powers := [(18, 1), (30, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (38, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (41, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (44, 1), (50, 1)] }, { coefficient := 1, powers := [(3, 1), (26, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (32, 1), (56, 1)] }, { coefficient := 1, powers := [(3, 1), (35, 1), (50, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (32, 1), (44, 1)] }, { coefficient := 1, powers := [(6, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(9, 1), (20, 1), (56, 1)] }, { coefficient := 1, powers := [(9, 1), (26, 1), (44, 1)] }, { coefficient := 1, powers := [(9, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(15, 1), (20, 1), (50, 1)] }, { coefficient := 1, powers := [(15, 1), (26, 1), (41, 1)] }, { coefficient := 1, powers := [(15, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1), (39, 1), (60, 1)] }, { coefficient := 1, powers := [(1, 1), (42, 1), (57, 1)] }, { coefficient := 1, powers := [(1, 1), (46, 1), (53, 1)] }, { coefficient := 1, powers := [(4, 1), (28, 1), (60, 1)] }, { coefficient := 1, powers := [(4, 1), (33, 1), (57, 1)] }, { coefficient := 1, powers := [(4, 1), (36, 1), (53, 1)] }, { coefficient := 1, powers := [(7, 1), (23, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (33, 1), (46, 1)] }, { coefficient := 1, powers := [(7, 1), (36, 1), (42, 1)] }, { coefficient := 1, powers := [(11, 1), (23, 1), (57, 1)] }, { coefficient := 1, powers := [(11, 1), (28, 1), (46, 1)] }, { coefficient := 1, powers := [(11, 1), (36, 1), (39, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1), (53, 1)] }, { coefficient := 1, powers := [(16, 1), (28, 1), (42, 1)] }, { coefficient := 1, powers := [(16, 1), (33, 1), (39, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (64, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(56, 1)] }],
  [{ coefficient := 1, powers := [(26, 1), (68, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(31, 1), (70, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 37 → SparsePoly (Fin 71) := ![
  [{ coefficient := -1, powers := [(1, 1), (15, 1), (24, 2), (50, 1), (53, 1), (64, 1), (70, 1)] }, { coefficient := -1, powers := [(1, 1), (15, 1), (24, 1), (29, 1), (50, 1), (53, 1), (64, 1), (70, 1)] }, { coefficient := -1, powers := [(1, 1), (24, 1), (29, 1), (35, 1), (38, 1), (50, 1), (53, 1), (64, 1), (68, 1), (70, 1)] }, { coefficient := 1, powers := [(1, 1), (24, 1), (30, 1), (35, 1), (38, 1), (50, 1), (53, 1), (64, 1), (70, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (26, 2), (36, 1), (46, 1), (53, 1), (57, 1), (68, 1), (70, 1)] }, { coefficient := 1, powers := [(3, 1), (26, 1), (36, 1), (46, 1), (53, 1), (57, 1), (70, 1)] }, { coefficient := -1, powers := [(3, 1), (36, 1), (46, 1), (57, 1), (70, 1)] }, { coefficient := -2, powers := [(23, 1), (26, 2), (53, 1), (57, 1), (68, 1), (70, 1)] }, { coefficient := -1, powers := [(23, 1), (26, 2), (57, 2), (68, 1), (70, 1)] }, { coefficient := 2, powers := [(23, 1), (26, 1), (53, 1), (57, 1), (70, 1)] }, { coefficient := 1, powers := [(23, 1), (26, 1), (57, 2), (70, 1)] }, { coefficient := -1, powers := [(26, 2), (36, 1), (39, 1), (57, 1), (68, 1), (70, 1)] }, { coefficient := 1, powers := [(26, 1), (36, 1), (39, 1), (57, 1), (70, 1)] }, { coefficient := -1, powers := [(28, 1), (46, 1), (70, 1)] }, { coefficient := 1, powers := [(36, 1), (39, 1), (70, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (1, 1), (46, 1), (50, 1), (53, 1), (70, 1)] }, { coefficient := -1, powers := [(1, 2), (50, 1), (53, 1), (63, 1), (70, 1)] }, { coefficient := 1, powers := [(1, 1), (9, 1), (26, 1), (46, 1), (53, 1), (70, 1)] }, { coefficient := -1, powers := [(1, 1), (10, 1), (27, 1), (53, 1), (63, 1), (70, 1)] }, { coefficient := 1, powers := [(1, 1), (20, 1), (46, 1), (50, 1), (53, 1), (70, 1)] }, { coefficient := 1, powers := [(1, 1), (26, 1), (41, 1), (46, 1), (53, 1), (70, 1)] }, { coefficient := 1, powers := [(1, 1), (26, 1), (46, 1), (50, 1), (53, 1), (70, 1)] }, { coefficient := 1, powers := [(1, 1), (32, 1), (38, 1), (46, 1), (53, 1), (70, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (6, 1), (35, 1), (53, 1), (70, 1)] }, { coefficient := -1, powers := [(1, 1), (15, 1), (26, 1), (53, 1), (70, 1)] }, { coefficient := -1, powers := [(1, 1), (35, 1), (38, 1), (53, 1), (70, 1)] }],
  [{ coefficient := -2, powers := [(1, 1), (20, 1), (50, 1), (53, 1), (70, 1)] }],
  [{ coefficient := -1, powers := [(1, 1), (6, 1), (35, 1), (46, 1), (53, 1), (70, 1)] }, { coefficient := 1, powers := [(1, 1), (15, 1), (26, 1), (46, 1), (53, 1), (70, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (1, 1), (20, 1), (46, 1), (57, 1), (62, 1), (70, 1)] }, { coefficient := 1, powers := [(0, 1), (2, 1), (4, 1), (33, 1), (57, 1), (64, 1), (70, 1)] }, { coefficient := -1, powers := [(0, 1), (4, 1), (20, 1), (33, 1), (57, 1), (62, 1), (70, 1)] }, { coefficient := -1, powers := [(0, 1), (4, 1), (33, 1), (57, 1), (70, 1)] }, { coefficient := 1, powers := [(1, 1), (2, 1), (20, 1), (46, 1), (57, 1), (64, 1), (70, 1)] }, { coefficient := -1, powers := [(1, 1), (2, 1), (57, 1), (64, 1), (70, 1)] }, { coefficient := 2, powers := [(1, 1), (15, 1), (20, 1), (50, 1), (53, 1), (70, 1)] }, { coefficient := -1, powers := [(1, 1), (20, 1), (46, 1), (62, 1), (70, 1)] }, { coefficient := 1, powers := [(1, 1), (26, 1), (38, 1), (53, 1), (59, 1), (70, 1)] }, { coefficient := 1, powers := [(1, 1), (57, 1), (70, 1)] }, { coefficient := 1, powers := [(2, 1), (4, 1), (20, 1), (33, 1), (57, 1), (64, 1), (70, 1)] }, { coefficient := -1, powers := [(4, 1), (20, 1), (33, 1), (62, 1), (70, 1)] }, { coefficient := -1, powers := [(4, 1), (33, 1), (70, 1)] }, { coefficient := 1, powers := [(7, 1), (36, 1), (70, 1)] }, { coefficient := -1, powers := [(16, 1), (28, 1), (70, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (46, 1), (62, 1), (70, 1)] }, { coefficient := 1, powers := [(4, 1), (33, 1), (62, 1), (70, 1)] }, { coefficient := -1, powers := [(7, 1), (36, 1), (46, 1), (70, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (15, 1), (24, 1), (50, 1), (53, 1), (64, 1), (70, 1)] }, { coefficient := 1, powers := [(1, 1), (15, 1), (29, 1), (50, 1), (53, 1), (64, 1), (70, 1)] }, { coefficient := 1, powers := [(1, 1), (29, 1), (35, 1), (38, 1), (50, 1), (53, 1), (64, 1), (68, 1), (70, 1)] }, { coefficient := -1, powers := [(1, 1), (30, 1), (35, 1), (38, 1), (50, 1), (53, 1), (64, 1), (70, 1)] }],
  [{ coefficient := -1, powers := [(1, 1), (29, 1), (35, 1), (38, 1), (53, 1), (64, 1), (68, 1)] }],
  [{ coefficient := -1, powers := [(1, 1), (20, 1), (46, 1), (53, 1)] }, { coefficient := 1, powers := [(1, 1), (38, 1), (53, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (35, 1), (38, 1), (53, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(1, 1), (26, 1), (46, 1), (53, 1), (70, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (26, 1), (36, 1), (46, 1), (53, 1), (70, 1)] }, { coefficient := -1, powers := [(3, 1), (36, 1), (46, 1), (70, 1)] }, { coefficient := 1, powers := [(22, 1), (46, 1), (70, 1)] }, { coefficient := 2, powers := [(23, 1), (26, 1), (53, 1), (70, 1)] }, { coefficient := 1, powers := [(23, 1), (26, 1), (57, 1), (70, 1)] }, { coefficient := -1, powers := [(23, 1), (70, 1)] }, { coefficient := 1, powers := [(26, 1), (36, 1), (39, 1), (70, 1)] }, { coefficient := -1, powers := [(27, 1), (53, 1), (70, 1)] }, { coefficient := 1, powers := [(28, 1), (70, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (4, 1), (18, 1), (33, 1), (64, 1)] }, { coefficient := 1, powers := [(1, 1), (18, 1), (20, 1), (46, 1), (64, 1)] }, { coefficient := -1, powers := [(1, 1), (18, 1), (64, 1)] }, { coefficient := 1, powers := [(4, 1), (18, 1), (20, 1), (33, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (15, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(1, 1), (15, 1), (50, 1), (53, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (26, 1), (36, 1), (46, 1), (53, 1), (68, 1)] }, { coefficient := -2, powers := [(23, 1), (26, 1), (53, 1), (68, 1)] }, { coefficient := -1, powers := [(23, 1), (26, 1), (57, 1), (68, 1)] }, { coefficient := -1, powers := [(26, 1), (36, 1), (39, 1), (68, 1)] }],
  [{ coefficient := -1, powers := [(1, 1), (38, 1), (53, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(1, 1), (31, 1), (46, 1), (62, 1), (70, 1)] }, { coefficient := -1, powers := [(4, 1), (31, 1), (33, 1), (62, 1), (70, 1)] }, { coefficient := 1, powers := [(7, 1), (31, 1), (36, 1), (46, 1), (70, 1)] }, { coefficient := -1, powers := [(7, 1), (36, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (53, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(1, 1), (46, 1), (50, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(1, 1), (15, 1), (46, 1), (53, 1)] }, { coefficient := -1, powers := [(1, 1), (44, 1), (46, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(53, 1)] }],
  [{ coefficient := 1, powers := [(46, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (26, 2), (36, 1), (46, 1), (53, 1), (68, 1)] }, { coefficient := -1, powers := [(3, 1), (26, 1), (31, 1), (36, 1), (46, 1), (53, 1), (70, 1)] }, { coefficient := 1, powers := [(3, 1), (31, 1), (36, 1), (46, 1), (70, 1)] }, { coefficient := -1, powers := [(22, 1), (31, 1), (46, 1), (70, 1)] }, { coefficient := 2, powers := [(23, 1), (26, 2), (53, 1), (68, 1)] }, { coefficient := 1, powers := [(23, 1), (26, 2), (57, 1), (68, 1)] }, { coefficient := -2, powers := [(23, 1), (26, 1), (31, 1), (53, 1), (70, 1)] }, { coefficient := -1, powers := [(23, 1), (26, 1), (31, 1), (57, 1), (70, 1)] }, { coefficient := 1, powers := [(23, 1), (31, 1), (70, 1)] }, { coefficient := 1, powers := [(26, 2), (36, 1), (39, 1), (68, 1)] }, { coefficient := -1, powers := [(26, 1), (31, 1), (36, 1), (39, 1), (70, 1)] }, { coefficient := 1, powers := [(27, 1), (31, 1), (53, 1), (70, 1)] }, { coefficient := -1, powers := [(27, 1), (53, 1)] }, { coefficient := -1, powers := [(28, 1), (31, 1), (70, 1)] }, { coefficient := 1, powers := [(28, 1)] }],
  [{ coefficient := 1, powers := [(16, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (20, 1), (46, 1), (62, 1)] }, { coefficient := 1, powers := [(4, 1), (20, 1), (33, 1), (62, 1)] }, { coefficient := 1, powers := [(4, 1), (33, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (4, 1), (33, 1), (64, 1)] }, { coefficient := -1, powers := [(1, 1), (20, 1), (46, 1), (64, 1)] }, { coefficient := 1, powers := [(1, 1), (64, 1)] }, { coefficient := -1, powers := [(4, 1), (20, 1), (33, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (46, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(1, 1), (20, 1), (39, 1), (46, 1), (60, 1)] }, { coefficient := -1, powers := [(1, 1), (20, 1), (46, 2), (53, 1)] }, { coefficient := 1, powers := [(1, 1), (20, 1), (46, 2), (57, 1)] }, { coefficient := 1, powers := [(1, 1), (46, 1), (53, 1)] }, { coefficient := -1, powers := [(4, 1), (20, 1), (33, 1), (39, 1), (60, 1)] }, { coefficient := -1, powers := [(4, 1), (20, 1), (33, 1), (46, 1), (53, 1)] }, { coefficient := 1, powers := [(4, 1), (20, 1), (33, 1), (46, 1), (57, 1)] }, { coefficient := 1, powers := [(4, 1), (33, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(1, 1), (38, 1), (53, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (4, 1), (33, 1), (39, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (4, 1), (33, 1), (46, 1), (53, 1)] }, { coefficient := -1, powers := [(0, 1), (4, 1), (33, 1), (46, 1), (57, 1)] }, { coefficient := 1, powers := [(1, 1), (15, 1), (38, 1), (50, 1), (53, 1), (60, 1)] }, { coefficient := 1, powers := [(1, 1), (15, 1), (50, 1), (53, 1)] }, { coefficient := 1, powers := [(1, 1), (20, 1), (39, 1), (46, 1), (60, 1)] }, { coefficient := 1, powers := [(1, 1), (20, 1), (46, 2), (53, 1)] }, { coefficient := -1, powers := [(1, 1), (20, 1), (46, 2), (57, 1)] }, { coefficient := -1, powers := [(1, 1), (35, 1), (38, 1), (46, 1), (50, 1), (53, 1)] }, { coefficient := -1, powers := [(1, 1), (39, 1), (60, 1)] }, { coefficient := -1, powers := [(1, 1), (46, 1), (53, 1)] }, { coefficient := 1, powers := [(1, 1), (46, 1), (57, 1)] }, { coefficient := 1, powers := [(4, 1), (20, 1), (33, 1), (39, 1), (60, 1)] }, { coefficient := 1, powers := [(4, 1), (20, 1), (33, 1), (46, 1), (53, 1)] }, { coefficient := -1, powers := [(4, 1), (20, 1), (33, 1), (46, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (1, 1), (41, 1), (46, 1), (53, 1)] }, { coefficient := -1, powers := [(1, 2), (41, 1), (53, 1), (63, 1)] }, { coefficient := -1, powers := [(1, 1), (3, 1), (32, 1), (46, 1), (53, 1)] }, { coefficient := -1, powers := [(1, 1), (9, 1), (38, 1), (53, 1), (60, 1)] }, { coefficient := -1, powers := [(1, 1), (10, 1), (22, 1), (53, 1), (63, 1)] }, { coefficient := 1, powers := [(1, 1), (20, 1), (46, 1), (50, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (13, 1), (29, 1), (35, 1), (38, 1), (46, 1), (53, 1), (64, 1)] }, { coefficient := -1, powers := [(3, 1), (7, 1), (26, 1), (36, 1), (46, 1), (53, 1), (60, 1)] }, { coefficient := -1, powers := [(3, 1), (16, 1), (26, 1), (36, 1), (46, 1), (53, 2)] }, { coefficient := 1, powers := [(3, 1), (16, 1), (36, 1), (46, 1), (53, 1)] }, { coefficient := -2, powers := [(7, 1), (23, 1), (26, 1), (53, 1), (60, 1)] }, { coefficient := -1, powers := [(7, 1), (23, 1), (26, 1), (57, 1), (60, 1)] }, { coefficient := -1, powers := [(7, 1), (26, 1), (36, 1), (39, 1), (60, 1)] }, { coefficient := -2, powers := [(16, 1), (23, 1), (26, 1), (53, 2)] }, { coefficient := -1, powers := [(16, 1), (23, 1), (26, 1), (53, 1), (57, 1)] }, { coefficient := 2, powers := [(16, 1), (23, 1), (53, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1), (57, 1)] }, { coefficient := -1, powers := [(16, 1), (26, 1), (36, 1), (39, 1), (53, 1)] }, { coefficient := 1, powers := [(16, 1), (36, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (1, 1), (20, 1), (42, 1), (46, 1), (57, 1), (62, 1)] }, { coefficient := 1, powers := [(0, 1), (1, 1), (20, 1), (46, 2), (57, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 1), (1, 1), (44, 1), (46, 1), (50, 1), (53, 1)] }, { coefficient := 1, powers := [(0, 1), (1, 1), (46, 1), (53, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 1), (2, 1), (4, 1), (33, 1), (42, 1), (57, 1), (64, 1)] }, { coefficient := -1, powers := [(0, 1), (2, 1), (4, 1), (33, 1), (46, 1), (57, 1), (64, 1)] }, { coefficient := 1, powers := [(0, 1), (4, 1), (20, 1), (33, 1), (42, 1), (57, 1), (62, 1)] }, { coefficient := 1, powers := [(0, 1), (4, 1), (20, 1), (33, 1), (46, 1), (57, 1), (62, 1)] }, { coefficient := 1, powers := [(0, 1), (4, 1), (33, 1), (42, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (4, 1), (33, 1), (46, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (4, 1), (33, 1), (53, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 1), (7, 1), (36, 1), (46, 1), (53, 1)] }, { coefficient := 1, powers := [(1, 2), (44, 1), (50, 1), (53, 1), (63, 1)] }, { coefficient := -1, powers := [(1, 1), (2, 1), (20, 1), (42, 1), (46, 1), (57, 1), (64, 1)] }, { coefficient := -1, powers := [(1, 1), (2, 1), (20, 1), (46, 2), (57, 1), (64, 1)] }, { coefficient := 1, powers := [(1, 1), (2, 1), (42, 1), (57, 1), (64, 1)] }, { coefficient := 1, powers := [(1, 1), (2, 1), (46, 1), (57, 1), (64, 1)] }, { coefficient := 1, powers := [(1, 1), (3, 1), (26, 1), (46, 1), (53, 1), (59, 1)] }, { coefficient := 1, powers := [(1, 1), (6, 1), (35, 1), (41, 1), (46, 1), (53, 1)] }, { coefficient := 1, powers := [(1, 1), (9, 1), (35, 1), (38, 1), (46, 1), (53, 1)] }, { coefficient := 1, powers := [(1, 1), (10, 1), (27, 1), (44, 1), (53, 1), (63, 1)] }, { coefficient := -1, powers := [(1, 1), (15, 1), (18, 1), (24, 1), (50, 1), (53, 1), (64, 1)] }, { coefficient := -1, powers := [(1, 1), (15, 1), (18, 1), (29, 1), (50, 1), (53, 1), (64, 1)] }, { coefficient := -2, powers := [(1, 1), (15, 1), (20, 1), (46, 1), (50, 1), (53, 1)] }, { coefficient := -1, powers := [(1, 1), (18, 1), (29, 1), (35, 1), (38, 1), (50, 1), (53, 1), (64, 1), (68, 1)] }, { coefficient := 1, powers := [(1, 1), (18, 1), (30, 1), (35, 1), (38, 1), (50, 1), (53, 1), (64, 1)] }, { coefficient := 1, powers := [(1, 1), (20, 1), (42, 1), (46, 1), (62, 1)] }, { coefficient := -1, powers := [(1, 1), (20, 1), (44, 1), (46, 1), (50, 1), (53, 1)] }, { coefficient := 1, powers := [(1, 1), (20, 1), (46, 2), (62, 1)] }, { coefficient := 1, powers := [(1, 1), (20, 1), (46, 1), (53, 1), (62, 1)] }, { coefficient := 1, powers := [(1, 1), (20, 1), (46, 1), (57, 1), (62, 1)] }, { coefficient := -1, powers := [(1, 1), (26, 1), (38, 1), (42, 1), (53, 1), (59, 1)] }, { coefficient := -1, powers := [(1, 1), (26, 1), (38, 1), (46, 1), (53, 1), (59, 1)] }, { coefficient := -1, powers := [(1, 1), (26, 1), (41, 1), (44, 1), (46, 1), (53, 1)] }, { coefficient := -1, powers := [(1, 1), (26, 1), (44, 1), (46, 1), (50, 1), (53, 1)] }, { coefficient := -1, powers := [(1, 1), (32, 1), (38, 1), (44, 1), (46, 1), (53, 1)] }, { coefficient := -1, powers := [(1, 1), (42, 1), (57, 1)] }, { coefficient := -1, powers := [(1, 1), (46, 1), (57, 1)] }, { coefficient := -1, powers := [(2, 1), (4, 1), (20, 1), (33, 1), (42, 1), (57, 1), (64, 1)] }, { coefficient := -1, powers := [(2, 1), (4, 1), (20, 1), (33, 1), (46, 1), (57, 1), (64, 1)] }, { coefficient := 1, powers := [(3, 1), (7, 1), (26, 1), (36, 1), (46, 1), (53, 1), (60, 1)] }, { coefficient := -1, powers := [(3, 1), (7, 1), (36, 1), (46, 1), (60, 1)] }, { coefficient := 1, powers := [(3, 1), (11, 1), (26, 2), (36, 1), (46, 1), (53, 1), (57, 1), (68, 1)] }, { coefficient := 1, powers := [(3, 1), (16, 1), (26, 1), (36, 1), (46, 1), (53, 2)] }, { coefficient := -1, powers := [(3, 1), (16, 1), (36, 1), (46, 1), (53, 1)] }, { coefficient := 1, powers := [(4, 1), (20, 1), (33, 1), (42, 1), (62, 1)] }, { coefficient := 1, powers := [(4, 1), (20, 1), (33, 1), (46, 1), (62, 1)] }, { coefficient := 1, powers := [(4, 1), (20, 1), (33, 1), (53, 1), (62, 1)] }, { coefficient := 1, powers := [(4, 1), (20, 1), (33, 1), (57, 1), (62, 1)] }, { coefficient := 1, powers := [(4, 1), (33, 1), (42, 1)] }, { coefficient := 1, powers := [(4, 1), (33, 1), (46, 1)] }, { coefficient := -1, powers := [(7, 1), (20, 1), (36, 1), (46, 1), (53, 1)] }, { coefficient := -1, powers := [(7, 1), (20, 1), (36, 1), (46, 1), (57, 1)] }, { coefficient := 1, powers := [(7, 1), (22, 1), (46, 1), (60, 1)] }, { coefficient := 2, powers := [(7, 1), (23, 1), (26, 1), (53, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (23, 1), (26, 1), (57, 1), (60, 1)] }, { coefficient := -1, powers := [(7, 1), (23, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (26, 1), (36, 1), (39, 1), (60, 1)] }, { coefficient := -1, powers := [(7, 1), (27, 1), (53, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (28, 1), (60, 1)] }, { coefficient := -1, powers := [(7, 1), (36, 1), (42, 1)] }, { coefficient := -1, powers := [(7, 1), (36, 1), (46, 1)] }, { coefficient := 1, powers := [(11, 1), (22, 1), (46, 1), (57, 1)] }, { coefficient := 2, powers := [(11, 1), (23, 1), (26, 2), (53, 1), (57, 1), (68, 1)] }, { coefficient := 1, powers := [(11, 1), (23, 1), (26, 2), (57, 2), (68, 1)] }, { coefficient := -1, powers := [(11, 1), (23, 1), (57, 1)] }, { coefficient := 1, powers := [(11, 1), (26, 2), (36, 1), (39, 1), (57, 1), (68, 1)] }, { coefficient := -1, powers := [(11, 1), (27, 1), (53, 1), (57, 1)] }, { coefficient := 1, powers := [(11, 1), (28, 1), (46, 1)] }, { coefficient := 1, powers := [(11, 1), (28, 1), (57, 1)] }, { coefficient := -1, powers := [(11, 1), (36, 1), (39, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1), (46, 1), (53, 1)] }, { coefficient := 2, powers := [(16, 1), (23, 1), (26, 1), (53, 2)] }, { coefficient := 1, powers := [(16, 1), (23, 1), (26, 1), (53, 1), (57, 1)] }, { coefficient := -1, powers := [(16, 1), (23, 1), (53, 1)] }, { coefficient := 1, powers := [(16, 1), (26, 1), (36, 1), (39, 1), (53, 1)] }, { coefficient := -1, powers := [(16, 1), (27, 1), (53, 2)] }, { coefficient := 1, powers := [(16, 1), (28, 1), (42, 1)] }, { coefficient := 1, powers := [(16, 1), (28, 1), (46, 1)] }, { coefficient := 1, powers := [(16, 1), (28, 1), (53, 1)] }]
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
    (values : Fin 71 → R) :
    ¬ ∀ index : Fin 37,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component24.SelectedLeafB7_6_2_7.selectedHasNoCommonZero

end Krenn.Component24.SelectedLeafB7_6_2_7
