import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component37.SelectedLeafB2_2_1

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "52df7c100f9ec63ed405b8f065939ca68ebe7d39fcf15a686a8a4fd592cc4498"
def certificateSHA256 : String := "01f0eedfd994d6acf30dd67b2c52d36a8430776c54d2de7bd20efc095ecf07a6"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 43 → Fin 667 := ![
  1,
  2,
  3,
  4,
  6,
  15,
  146,
  149,
  152,
  167,
  171,
  175,
  181,
  221,
  256,
  301,
  307,
  316,
  393,
  410,
  450,
  453,
  454,
  461,
  471,
  566,
  580,
  581,
  583,
  584,
  602,
  603,
  645,
  655,
  657,
  658,
  659,
  660,
  661,
  663,
  664,
  665,
  666
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 43 → SparsePoly (Fin 65) := ![
  [{ coefficient := 1, powers := [(1, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (27, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (53, 1)] }, { coefficient := 1, powers := [(11, 1), (27, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (26, 1)] }, { coefficient := 1, powers := [(26, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (44, 1)] }, { coefficient := 1, powers := [(40, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (25, 1)] }, { coefficient := 1, powers := [(18, 1), (20, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (20, 1)] }, { coefficient := 1, powers := [(18, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (54, 1)] }, { coefficient := 1, powers := [(30, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (26, 1), (47, 1)] }, { coefficient := 1, powers := [(9, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (25, 1), (46, 1)] }, { coefficient := 1, powers := [(18, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (59, 1)] }, { coefficient := 1, powers := [(9, 1), (43, 1)] }, { coefficient := 1, powers := [(13, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (46, 1)] }, { coefficient := 1, powers := [(12, 1), (57, 1)] }, { coefficient := 1, powers := [(18, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1), (55, 1)] }, { coefficient := 1, powers := [(26, 1), (46, 1), (51, 1)] }, { coefficient := 1, powers := [(55, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (20, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1)] }, { coefficient := 1, powers := [(18, 1), (20, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (25, 1), (41, 1)] }, { coefficient := 1, powers := [(18, 1), (25, 1), (46, 1)] }, { coefficient := 1, powers := [(18, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (61, 1)] }, { coefficient := 1, powers := [(12, 1), (26, 1), (47, 1)] }, { coefficient := 1, powers := [(12, 1), (58, 1)] }, { coefficient := 1, powers := [(19, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (41, 1)] }, { coefficient := 1, powers := [(18, 1), (46, 1)] }, { coefficient := 1, powers := [(18, 1), (52, 1)] }, { coefficient := 1, powers := [(18, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (55, 1)] }, { coefficient := 1, powers := [(30, 1), (42, 1)] }, { coefficient := 1, powers := [(30, 1), (48, 1), (51, 1)] }, { coefficient := 1, powers := [(33, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1), (52, 1)] }, { coefficient := 1, powers := [(3, 1), (34, 1), (52, 1)] }, { coefficient := 1, powers := [(13, 1), (20, 1), (52, 1)] }, { coefficient := 1, powers := [(43, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1), (53, 1)] }, { coefficient := 1, powers := [(46, 1), (51, 1)] }, { coefficient := 1, powers := [(51, 1), (57, 1)] }, { coefficient := 1, powers := [(53, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (44, 1), (54, 1)] }, { coefficient := 1, powers := [(24, 1), (58, 1)] }, { coefficient := 1, powers := [(30, 1), (49, 1)] }, { coefficient := 1, powers := [(36, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1)] }, { coefficient := 1, powers := [(6, 1), (60, 1)] }, { coefficient := 1, powers := [(25, 1), (41, 1)] }, { coefficient := 1, powers := [(25, 1), (46, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (52, 1)] }, { coefficient := 1, powers := [(3, 1), (60, 1)] }, { coefficient := 1, powers := [(20, 1), (52, 1)] }, { coefficient := 1, powers := [(20, 1), (57, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (31, 1), (57, 1)] }, { coefficient := 1, powers := [(9, 1), (20, 1), (57, 1)] }, { coefficient := 1, powers := [(9, 1)] }, { coefficient := 1, powers := [(40, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (40, 1), (58, 1)] }, { coefficient := 1, powers := [(3, 1), (31, 1), (58, 1)] }, { coefficient := 1, powers := [(9, 1), (20, 1), (58, 1)] }, { coefficient := 1, powers := [(9, 1), (26, 1), (44, 1)] }, { coefficient := 1, powers := [(26, 1), (40, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1)] }, { coefficient := 1, powers := [(3, 1), (34, 1)] }, { coefficient := 1, powers := [(13, 1), (20, 1)] }, { coefficient := 1, powers := [(20, 1), (56, 1)] }, { coefficient := 1, powers := [(25, 1), (43, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (50, 1)] }, { coefficient := 1, powers := [(6, 1), (31, 1)] }, { coefficient := 1, powers := [(9, 1), (25, 1)] }, { coefficient := 1, powers := [(20, 1), (50, 1)] }, { coefficient := 1, powers := [(25, 1), (40, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (38, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (41, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(41, 1)] }, { coefficient := 1, powers := [(46, 1)] }, { coefficient := 1, powers := [(52, 1)] }, { coefficient := 1, powers := [(57, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (37, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (40, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (43, 1), (50, 1)] }, { coefficient := 1, powers := [(3, 1), (25, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (31, 1), (56, 1)] }, { coefficient := 1, powers := [(3, 1), (34, 1), (50, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (31, 1), (43, 1)] }, { coefficient := 1, powers := [(6, 1), (34, 1), (40, 1)] }, { coefficient := 1, powers := [(9, 1), (20, 1), (56, 1)] }, { coefficient := 1, powers := [(9, 1), (25, 1), (43, 1)] }, { coefficient := 1, powers := [(9, 1), (34, 1), (37, 1)] }, { coefficient := 1, powers := [(13, 1), (20, 1), (50, 1)] }, { coefficient := 1, powers := [(13, 1), (25, 1), (40, 1)] }, { coefficient := 1, powers := [(13, 1), (31, 1), (37, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (39, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (42, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (49, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (49, 1)] }, { coefficient := 1, powers := [(8, 1), (36, 1), (42, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (58, 1)] }, { coefficient := 1, powers := [(12, 1), (30, 1), (49, 1)] }, { coefficient := 1, powers := [(12, 1), (36, 1), (39, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (55, 1)] }, { coefficient := 1, powers := [(19, 1), (30, 1), (42, 1)] }, { coefficient := 1, powers := [(19, 1), (33, 1), (39, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(40, 1)] }],
  [{ coefficient := 1, powers := [(42, 1)] }],
  [{ coefficient := 1, powers := [(56, 1)] }],
  [{ coefficient := 1, powers := [(57, 1)] }],
  [{ coefficient := 1, powers := [(58, 1), (64, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 43 → SparsePoly (Fin 65) := ![
  [{ coefficient := 1, powers := [(6, 1), (8, 1), (20, 1), (33, 1), (59, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (13, 1), (20, 1), (60, 1), (62, 1)] }, { coefficient := -1, powers := [(20, 1), (43, 1), (62, 1)] }, { coefficient := -1, powers := [(25, 1), (43, 1), (62, 1)] }, { coefficient := -1, powers := [(34, 1), (37, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (12, 1), (20, 1), (24, 1), (44, 1), (59, 1), (62, 1)] }, { coefficient := 1, powers := [(6, 1), (19, 1), (20, 1), (24, 1), (51, 1), (59, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (6, 1), (20, 1), (36, 1), (59, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (20, 1), (30, 1), (61, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1), (33, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (11, 1), (20, 1), (24, 1), (25, 1), (58, 1), (59, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (18, 1), (20, 1), (24, 1), (25, 1), (58, 1), (59, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (20, 1), (25, 1), (47, 1), (52, 1), (64, 1)] }, { coefficient := -1, powers := [(13, 1), (20, 1), (47, 1), (64, 1)] }, { coefficient := -1, powers := [(20, 1), (25, 1), (43, 1), (47, 1), (52, 1), (64, 1)] }, { coefficient := 1, powers := [(20, 1), (43, 1), (47, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(13, 1), (25, 1), (26, 1), (52, 1), (64, 1)] }, { coefficient := 1, powers := [(13, 1), (26, 1), (64, 1)] }, { coefficient := 1, powers := [(25, 1), (26, 1), (43, 1), (52, 1), (64, 1)] }, { coefficient := -1, powers := [(26, 1), (43, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (20, 1), (24, 1), (52, 1), (58, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (20, 1), (24, 1), (26, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (20, 1), (24, 1), (25, 1), (52, 1), (53, 1), (58, 1), (59, 1)] }, { coefficient := -1, powers := [(6, 1), (20, 1), (24, 1), (51, 1), (52, 1), (58, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1), (24, 1), (53, 1), (58, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (19, 1), (20, 1), (51, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(13, 1), (20, 1), (25, 1), (52, 1), (64, 1)] }, { coefficient := 1, powers := [(13, 1), (20, 1), (64, 1)] }, { coefficient := 1, powers := [(20, 1), (25, 1), (43, 1), (52, 1), (64, 1)] }, { coefficient := -1, powers := [(20, 1), (43, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (20, 1), (24, 1), (58, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(25, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (20, 1), (24, 1), (25, 1), (58, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (19, 1), (20, 1), (24, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (20, 1), (24, 1), (25, 1), (52, 1), (58, 1), (59, 1)] }, { coefficient := -1, powers := [(6, 1), (20, 1), (24, 1), (58, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (20, 1), (24, 1), (25, 1), (53, 1), (58, 1), (59, 1)] }, { coefficient := -1, powers := [(6, 1), (20, 1), (24, 1), (51, 1), (58, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (20, 1), (24, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (20, 1), (24, 1), (25, 2), (53, 1), (58, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1), (24, 1), (25, 1), (51, 1), (58, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (19, 1), (20, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (31, 1)] }, { coefficient := -1, powers := [(31, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (19, 1), (20, 1), (24, 1), (26, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (12, 1), (20, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (13, 1), (31, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (31, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (13, 1), (25, 1), (60, 1)] }, { coefficient := -1, powers := [(25, 1), (43, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (25, 1), (52, 1), (64, 1)] }, { coefficient := -1, powers := [(13, 1), (64, 1)] }, { coefficient := -1, powers := [(25, 1), (43, 1), (52, 1), (64, 1)] }, { coefficient := 1, powers := [(43, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (31, 1), (52, 1)] }, { coefficient := 1, powers := [(50, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (13, 1), (60, 1)] }, { coefficient := 1, powers := [(43, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (13, 1), (25, 1), (31, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(6, 1), (20, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (13, 1), (25, 1), (31, 1), (38, 1), (60, 1)] }, { coefficient := 1, powers := [(3, 1), (13, 1), (25, 1), (31, 1), (41, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (13, 1), (25, 1), (31, 1), (46, 1), (52, 1)] }, { coefficient := -1, powers := [(3, 1), (13, 1), (31, 1), (46, 1)] }, { coefficient := 1, powers := [(3, 1), (13, 1), (50, 1), (60, 1)] }, { coefficient := -1, powers := [(6, 1), (19, 1), (20, 1), (24, 1), (26, 1), (46, 1), (53, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (19, 1), (20, 1), (24, 1), (46, 1), (55, 1), (59, 1)] }, { coefficient := -1, powers := [(13, 1), (31, 1), (37, 1), (52, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1), (43, 1), (52, 1)] }, { coefficient := 1, powers := [(37, 1), (59, 1)] }, { coefficient := -1, powers := [(43, 1), (50, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (13, 1), (20, 1), (50, 1), (60, 1)] }, { coefficient := -1, powers := [(5, 1), (6, 1), (20, 1), (36, 1), (55, 1), (59, 1)] }, { coefficient := -1, powers := [(6, 1), (8, 1), (20, 1), (33, 1), (49, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (12, 1), (20, 1), (24, 1), (44, 1), (54, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (18, 1), (20, 1), (24, 1), (25, 1), (53, 1), (58, 1), (59, 1)] }, { coefficient := -1, powers := [(6, 1), (19, 1), (20, 1), (24, 1), (51, 1), (54, 1), (59, 1)] }, { coefficient := 1, powers := [(20, 1), (43, 1), (50, 1)] }, { coefficient := 1, powers := [(25, 1), (43, 1), (50, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (20, 1), (39, 1), (59, 1), (61, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1), (49, 1), (55, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (3, 1), (13, 1), (25, 1), (57, 1), (60, 1)] }, { coefficient := -1, powers := [(0, 1), (13, 1), (25, 1), (52, 1), (58, 1), (64, 1)] }, { coefficient := 1, powers := [(0, 1), (13, 1), (58, 1), (64, 1)] }, { coefficient := 1, powers := [(0, 1), (25, 1), (43, 1), (52, 1), (58, 1), (64, 1)] }, { coefficient := 1, powers := [(0, 1), (25, 1), (43, 1), (57, 1)] }, { coefficient := -1, powers := [(0, 1), (34, 1), (37, 1), (57, 1)] }, { coefficient := -1, powers := [(0, 1), (43, 1), (58, 1), (64, 1)] }, { coefficient := 1, powers := [(0, 1), (56, 1)] }, { coefficient := 1, powers := [(6, 1), (34, 1)] }, { coefficient := -1, powers := [(13, 1), (20, 1), (25, 1), (26, 1), (47, 1), (52, 1), (64, 1)] }, { coefficient := 1, powers := [(13, 1), (20, 1), (26, 1), (47, 1), (64, 1)] }, { coefficient := 1, powers := [(20, 1), (25, 1), (26, 1), (43, 1), (47, 1), (52, 1), (64, 1)] }, { coefficient := -1, powers := [(20, 1), (26, 1), (43, 1), (47, 1), (64, 1)] }, { coefficient := -1, powers := [(34, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (6, 1), (20, 1), (58, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (8, 1), (20, 1), (36, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (20, 1), (31, 1), (52, 1)] }, { coefficient := 1, powers := [(3, 1), (31, 1)] }, { coefficient := 1, powers := [(9, 1), (20, 1)] }, { coefficient := -1, powers := [(20, 1), (50, 1)] }],
  [{ coefficient := -1, powers := [(3, 2), (13, 1), (25, 1), (31, 1), (60, 1)] }, { coefficient := -1, powers := [(3, 1), (9, 1), (13, 1), (20, 1), (25, 1), (60, 1)] }, { coefficient := 1, powers := [(3, 1), (13, 1), (25, 1), (31, 1)] }, { coefficient := 1, powers := [(3, 1), (25, 1), (31, 1), (43, 1)] }, { coefficient := -1, powers := [(3, 1), (31, 1), (34, 1), (37, 1)] }, { coefficient := 1, powers := [(6, 1), (12, 1), (20, 2), (24, 1), (25, 1), (52, 1), (58, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (12, 1), (20, 2), (24, 1), (58, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (12, 1), (20, 1), (24, 1), (25, 1), (58, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (18, 1), (20, 1), (24, 1), (25, 2), (53, 1), (58, 1), (59, 1)] }, { coefficient := -1, powers := [(6, 1), (18, 1), (20, 1), (24, 1), (25, 1), (51, 1), (58, 1), (59, 1)] }, { coefficient := -1, powers := [(6, 1), (19, 1), (20, 1), (24, 1), (26, 1), (51, 1), (59, 1)] }, { coefficient := 1, powers := [(9, 1), (20, 1), (25, 1), (43, 1)] }, { coefficient := -1, powers := [(9, 1), (20, 1), (34, 1), (37, 1)] }, { coefficient := -1, powers := [(13, 1), (20, 1), (31, 1), (37, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (13, 1), (25, 1), (31, 1), (52, 1)] }, { coefficient := 1, powers := [(3, 1), (13, 1), (31, 1)] }, { coefficient := 1, powers := [(3, 1), (25, 1), (31, 1), (43, 1), (52, 1)] }, { coefficient := -1, powers := [(3, 1), (31, 1), (43, 1)] }]
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
    ¬ ∀ index : Fin 43,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component37.SelectedLeafB2_2_1.selectedHasNoCommonZero

end Krenn.Component37.SelectedLeafB2_2_1
