import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component62.SelectedLeafB6_5

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "e40905b0a08bc87f5a89a09692579a0186b0704e4aac644cc5a843a0568ba5ee"
def certificateSHA256 : String := "6b78ba495fe7e70ce7dac39b1c2a03201beac61cc41dea40f9ef97b23545d4bb"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 50 → Fin 664 := ![
  10,
  11,
  12,
  15,
  16,
  17,
  18,
  21,
  52,
  128,
  129,
  130,
  131,
  132,
  133,
  135,
  137,
  153,
  154,
  158,
  160,
  186,
  191,
  301,
  302,
  309,
  311,
  338,
  390,
  408,
  435,
  454,
  457,
  473,
  491,
  557,
  578,
  579,
  589,
  599,
  609,
  610,
  619,
  646,
  657,
  659,
  660,
  661,
  662,
  663
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 50 → SparsePoly (Fin 64) := ![
  [{ coefficient := 1, powers := [(10, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (30, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (41, 1)] }, { coefficient := 1, powers := [(10, 1), (25, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (44, 1)] }, { coefficient := 1, powers := [(10, 1), (25, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (46, 1)] }, { coefficient := 1, powers := [(10, 1), (25, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (48, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (51, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (53, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (45, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (52, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (18, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (41, 1)] }, { coefficient := 1, powers := [(17, 1), (18, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (50, 1)] }, { coefficient := 1, powers := [(22, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (38, 1)] }, { coefficient := 1, powers := [(27, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (27, 1), (58, 1)] }, { coefficient := 1, powers := [(27, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (22, 1), (58, 1)] }, { coefficient := 1, powers := [(22, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (46, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (53, 1)] }, { coefficient := 1, powers := [(8, 1), (30, 1)] }, { coefficient := 1, powers := [(12, 1), (27, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (43, 1)] }, { coefficient := 1, powers := [(12, 1), (55, 1)] }, { coefficient := 1, powers := [(16, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (44, 1)] }, { coefficient := 1, powers := [(17, 1), (38, 1)] }, { coefficient := 1, powers := [(17, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (24, 1), (49, 1)] }, { coefficient := 1, powers := [(11, 1), (27, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (18, 1), (55, 1)] }, { coefficient := 1, powers := [(12, 1)] }, { coefficient := 1, powers := [(16, 1), (18, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (23, 1), (44, 1)] }, { coefficient := 1, powers := [(17, 1), (23, 1), (38, 1)] }, { coefficient := 1, powers := [(17, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1)] }, { coefficient := 1, powers := [(23, 1), (38, 1), (41, 1)] }, { coefficient := 1, powers := [(23, 1), (44, 1)] }, { coefficient := 1, powers := [(41, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (53, 1)] }, { coefficient := 1, powers := [(27, 1), (39, 1)] }, { coefficient := 1, powers := [(27, 1), (45, 1), (48, 1)] }, { coefficient := 1, powers := [(30, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (35, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (44, 1), (51, 1)] }, { coefficient := 1, powers := [(41, 1), (51, 1)] }, { coefficient := 1, powers := [(44, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1), (48, 1)] }, { coefficient := 1, powers := [(6, 1), (59, 1)] }, { coefficient := 1, powers := [(23, 1), (44, 1), (48, 1)] }, { coefficient := 1, powers := [(41, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (27, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (30, 1), (56, 1)] }, { coefficient := 1, powers := [(3, 1), (33, 1), (53, 1)] }, { coefficient := 1, powers := [(27, 1), (41, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (41, 1), (52, 1)] }, { coefficient := 1, powers := [(22, 1), (56, 1)] }, { coefficient := 1, powers := [(27, 1), (46, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1)] }, { coefficient := 1, powers := [(6, 1), (58, 1)] }, { coefficient := 1, powers := [(23, 1), (38, 1)] }, { coefficient := 1, powers := [(23, 1), (43, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (50, 1)] }, { coefficient := 1, powers := [(3, 1), (58, 1)] }, { coefficient := 1, powers := [(18, 1), (50, 1)] }, { coefficient := 1, powers := [(18, 1), (55, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (39, 1), (55, 1)] }, { coefficient := 1, powers := [(2, 1), (45, 1), (51, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (55, 1)] }, { coefficient := 1, powers := [(12, 1), (22, 1), (55, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (24, 1), (41, 1), (49, 1)] }, { coefficient := 1, powers := [(2, 1), (37, 1), (56, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (37, 1)] }, { coefficient := 1, powers := [(11, 1), (27, 1), (41, 1)] }, { coefficient := 1, powers := [(17, 1), (27, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (38, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(24, 1), (38, 1), (41, 1)] }, { coefficient := 1, powers := [(24, 1), (44, 1)] }, { coefficient := 1, powers := [(41, 1), (52, 1)] }, { coefficient := 1, powers := [(56, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (39, 1), (55, 1)] }, { coefficient := 1, powers := [(0, 1), (45, 1), (51, 1)] }, { coefficient := 1, powers := [(19, 1), (48, 1), (55, 1)] }, { coefficient := 1, powers := [(19, 1), (51, 1)] }, { coefficient := 1, powers := [(39, 1)] }, { coefficient := 1, powers := [(45, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (36, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (45, 1), (52, 1)] }, { coefficient := 1, powers := [(5, 1), (27, 1), (58, 1)] }, { coefficient := 1, powers := [(8, 1), (22, 1), (58, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1), (52, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (35, 1), (58, 1)] }, { coefficient := 1, powers := [(0, 1), (38, 1), (55, 1)] }, { coefficient := 1, powers := [(0, 1), (43, 1), (50, 1)] }, { coefficient := 1, powers := [(38, 1)] }, { coefficient := 1, powers := [(43, 1)] }, { coefficient := 1, powers := [(50, 1)] }, { coefficient := 1, powers := [(55, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (36, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (46, 1), (53, 1)] }, { coefficient := 1, powers := [(5, 1), (27, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (53, 1)] }, { coefficient := 1, powers := [(8, 1), (22, 1), (59, 1)] }, { coefficient := 1, powers := [(8, 1), (30, 1), (46, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (39, 1)] }, { coefficient := 1, powers := [(12, 1), (22, 1), (56, 1)] }, { coefficient := 1, powers := [(12, 1), (27, 1), (46, 1)] }, { coefficient := 1, powers := [(12, 1), (33, 1), (36, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (53, 1)] }, { coefficient := 1, powers := [(17, 1), (27, 1), (39, 1)] }, { coefficient := 1, powers := [(17, 1), (30, 1), (36, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1), (61, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(37, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(38, 1)] }],
  [{ coefficient := 1, powers := [(39, 1), (63, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 50 → SparsePoly (Fin 64) := ![
  [{ coefficient := -1, powers := [(0, 1), (16, 1), (25, 1), (27, 1), (39, 1), (50, 1), (61, 1)] }, { coefficient := -1, powers := [(3, 1), (16, 1), (25, 1), (27, 1), (39, 1), (58, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (18, 1), (25, 1), (27, 1), (51, 1), (58, 1), (61, 1)] }, { coefficient := -1, powers := [(12, 1), (18, 1), (22, 1), (25, 1), (50, 1), (52, 1), (61, 1)] }, { coefficient := -1, powers := [(16, 1), (18, 1), (25, 1), (27, 1), (39, 1), (50, 1), (61, 1)] }, { coefficient := -1, powers := [(16, 1), (18, 1), (25, 1), (27, 1), (39, 1), (55, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (12, 1), (18, 1), (22, 1), (25, 1), (50, 1), (52, 1), (61, 1)] }, { coefficient := -1, powers := [(12, 1), (18, 1), (22, 1), (24, 1), (25, 1), (50, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (5, 1), (12, 1), (25, 1), (27, 1), (30, 1), (50, 1), (56, 1), (61, 1)] }, { coefficient := -1, powers := [(5, 1), (12, 1), (18, 1), (25, 1), (27, 1), (30, 1), (50, 1), (56, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (5, 1), (19, 1), (20, 1), (30, 1), (50, 1), (55, 1), (56, 1), (61, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (5, 1), (20, 1), (30, 1), (45, 1), (50, 1), (56, 1), (61, 1), (63, 1)] }, { coefficient := -1, powers := [(5, 1), (18, 1), (19, 1), (20, 1), (30, 1), (50, 1), (55, 1), (56, 1), (61, 1), (63, 1)] }, { coefficient := 1, powers := [(5, 1), (18, 1), (20, 1), (27, 1), (44, 1), (58, 1), (61, 1)] }, { coefficient := -1, powers := [(5, 1), (18, 1), (20, 1), (30, 1), (45, 1), (50, 1), (56, 1), (61, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(0, 2), (5, 1), (20, 1), (30, 1), (45, 1), (50, 1), (56, 1), (61, 1), (63, 1)] }, { coefficient := 1, powers := [(0, 1), (5, 1), (18, 1), (20, 1), (27, 1), (44, 1), (58, 1), (61, 1)] }, { coefficient := -1, powers := [(0, 1), (5, 1), (18, 1), (20, 1), (30, 1), (45, 1), (50, 1), (56, 1), (61, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (5, 1), (19, 1), (20, 1), (30, 1), (50, 1), (56, 1), (61, 1), (63, 1)] }, { coefficient := -1, powers := [(5, 1), (18, 1), (19, 1), (20, 1), (30, 1), (50, 1), (56, 1), (61, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (5, 1), (12, 1), (20, 1), (22, 1), (33, 1), (50, 1), (56, 1), (61, 1)] }, { coefficient := -1, powers := [(0, 1), (12, 1), (17, 1), (20, 1), (22, 2), (50, 1), (56, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (12, 1), (18, 1), (20, 1), (22, 1), (33, 1), (50, 1), (56, 1), (61, 1)] }, { coefficient := -1, powers := [(12, 1), (17, 1), (18, 1), (20, 1), (22, 2), (50, 1), (56, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (5, 1), (12, 1), (30, 1), (50, 1), (52, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (12, 2), (22, 1), (50, 1), (52, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (12, 1), (50, 1), (52, 1)] }, { coefficient := 1, powers := [(3, 1), (12, 1), (39, 1), (52, 1), (58, 1), (63, 1)] }, { coefficient := 1, powers := [(5, 1), (12, 1), (18, 1), (30, 1), (50, 1), (52, 1), (56, 1)] }, { coefficient := 1, powers := [(12, 2), (18, 1), (22, 1), (50, 1), (52, 1), (56, 1)] }, { coefficient := 1, powers := [(12, 1), (18, 1), (50, 1), (52, 1)] }, { coefficient := 1, powers := [(12, 1), (18, 1), (52, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (5, 1), (12, 1), (33, 1), (45, 1), (50, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (12, 1), (17, 1), (22, 1), (45, 1), (50, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (17, 1), (45, 1), (50, 1)] }, { coefficient := 1, powers := [(3, 1), (17, 1), (39, 1), (45, 1), (58, 1), (63, 1)] }, { coefficient := -1, powers := [(5, 1), (12, 1), (18, 1), (33, 1), (45, 1), (50, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (39, 1), (41, 1), (58, 1), (63, 1)] }, { coefficient := 1, powers := [(12, 1), (17, 1), (18, 1), (22, 1), (45, 1), (50, 1), (56, 1)] }, { coefficient := 1, powers := [(17, 1), (18, 1), (45, 1), (50, 1)] }, { coefficient := 1, powers := [(17, 1), (18, 1), (45, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (5, 1), (56, 1), (58, 1)] }, { coefficient := -1, powers := [(5, 1), (18, 1), (56, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (16, 1), (27, 1), (39, 1), (50, 1), (61, 1)] }, { coefficient := 1, powers := [(3, 1), (16, 1), (27, 1), (39, 1), (58, 1), (61, 1)] }, { coefficient := -1, powers := [(5, 1), (18, 1), (27, 1), (51, 1), (58, 1), (61, 1)] }, { coefficient := 1, powers := [(12, 1), (18, 1), (22, 1), (50, 1), (52, 1), (61, 1)] }, { coefficient := 1, powers := [(16, 1), (18, 1), (27, 1), (39, 1), (50, 1), (61, 1)] }, { coefficient := 1, powers := [(16, 1), (18, 1), (27, 1), (39, 1), (55, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (12, 1), (18, 1), (22, 1), (50, 1), (52, 1), (61, 1)] }, { coefficient := 1, powers := [(12, 1), (18, 1), (22, 1), (24, 1), (50, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (5, 1), (12, 1), (27, 1), (30, 1), (50, 1), (56, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (12, 1), (18, 1), (27, 1), (30, 1), (50, 1), (56, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (5, 1), (19, 1), (30, 1), (50, 1), (55, 1), (56, 1), (61, 1), (63, 1)] }, { coefficient := 1, powers := [(0, 1), (5, 1), (30, 1), (45, 1), (50, 1), (56, 1), (61, 1), (63, 1)] }, { coefficient := 1, powers := [(5, 1), (18, 1), (19, 1), (30, 1), (50, 1), (55, 1), (56, 1), (61, 1), (63, 1)] }, { coefficient := -1, powers := [(5, 1), (18, 1), (27, 1), (44, 1), (58, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (18, 1), (30, 1), (45, 1), (50, 1), (56, 1), (61, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(0, 2), (5, 1), (30, 1), (45, 1), (50, 1), (56, 1), (61, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (5, 1), (18, 1), (27, 1), (44, 1), (58, 1), (61, 1)] }, { coefficient := 1, powers := [(0, 1), (5, 1), (18, 1), (30, 1), (45, 1), (50, 1), (56, 1), (61, 1), (63, 1)] }, { coefficient := 1, powers := [(0, 1), (5, 1), (19, 1), (30, 1), (50, 1), (56, 1), (61, 1), (63, 1)] }, { coefficient := 1, powers := [(5, 1), (18, 1), (19, 1), (30, 1), (50, 1), (56, 1), (61, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (5, 1), (12, 1), (22, 1), (33, 1), (50, 1), (56, 1), (61, 1)] }, { coefficient := 1, powers := [(0, 1), (12, 1), (17, 1), (22, 2), (50, 1), (56, 1), (61, 1)] }, { coefficient := -1, powers := [(5, 1), (12, 1), (18, 1), (22, 1), (33, 1), (50, 1), (56, 1), (61, 1)] }, { coefficient := 1, powers := [(12, 1), (17, 1), (18, 1), (22, 2), (50, 1), (56, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (6, 1), (12, 1), (22, 1), (50, 1), (52, 1), (56, 1), (59, 1)] }, { coefficient := -1, powers := [(0, 1), (6, 1), (12, 1), (33, 1), (39, 1), (50, 1), (52, 1), (56, 1)] }, { coefficient := -1, powers := [(0, 1), (6, 1), (50, 1), (52, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (18, 1), (50, 1), (51, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (18, 1), (51, 1), (55, 1), (56, 1)] }, { coefficient := -1, powers := [(0, 1), (44, 1), (53, 1)] }, { coefficient := 1, powers := [(0, 1), (51, 1), (56, 1)] }, { coefficient := -1, powers := [(3, 1), (6, 1), (39, 1), (52, 1), (58, 1), (59, 1), (63, 1)] }, { coefficient := -1, powers := [(6, 1), (12, 1), (18, 1), (22, 1), (50, 1), (52, 1), (56, 1), (59, 1)] }, { coefficient := -1, powers := [(6, 1), (12, 1), (18, 1), (33, 1), (39, 1), (50, 1), (52, 1), (56, 1)] }, { coefficient := 1, powers := [(18, 2), (50, 1), (51, 1), (56, 1)] }, { coefficient := 1, powers := [(18, 2), (51, 1), (55, 1), (56, 1)] }, { coefficient := 2, powers := [(18, 1), (51, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (6, 1), (12, 1), (22, 1), (45, 1), (50, 1), (56, 1), (59, 1)] }, { coefficient := -1, powers := [(0, 1), (6, 1), (12, 1), (33, 1), (39, 1), (45, 1), (50, 1), (56, 1)] }, { coefficient := -1, powers := [(0, 1), (6, 1), (45, 1), (50, 1), (59, 1)] }, { coefficient := -1, powers := [(0, 1), (37, 1), (39, 1), (41, 1), (50, 1), (62, 1)] }, { coefficient := -1, powers := [(3, 1), (6, 1), (39, 1), (45, 1), (58, 1), (59, 1), (63, 1)] }, { coefficient := -1, powers := [(3, 1), (37, 1), (39, 1), (41, 1), (58, 1), (62, 1)] }, { coefficient := -1, powers := [(6, 1), (12, 1), (18, 1), (22, 1), (45, 1), (50, 1), (56, 1), (59, 1)] }, { coefficient := -1, powers := [(6, 1), (12, 1), (18, 1), (33, 1), (39, 1), (45, 1), (50, 1), (56, 1)] }, { coefficient := -1, powers := [(18, 1), (37, 1), (39, 1), (41, 1), (50, 1), (62, 1)] }, { coefficient := -1, powers := [(18, 1), (37, 1), (39, 1), (41, 1), (55, 1), (62, 1)] }, { coefficient := -1, powers := [(18, 1), (46, 1), (51, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (27, 1), (39, 1), (44, 1), (50, 1)] }, { coefficient := -1, powers := [(3, 1), (27, 1), (39, 1), (44, 1), (58, 1)] }, { coefficient := -1, powers := [(18, 1), (27, 1), (39, 1), (44, 1), (50, 1)] }, { coefficient := -1, powers := [(18, 1), (27, 1), (39, 1), (44, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (27, 1), (39, 1), (50, 1)] }, { coefficient := -1, powers := [(3, 1), (27, 1), (39, 1), (58, 1)] }, { coefficient := -1, powers := [(18, 1), (27, 1), (39, 1), (50, 1)] }, { coefficient := -1, powers := [(18, 1), (27, 1), (39, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (12, 1), (18, 1), (55, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (12, 1), (56, 1)] }, { coefficient := -1, powers := [(8, 1), (18, 1), (59, 1)] }, { coefficient := 1, powers := [(12, 1), (18, 2), (55, 1), (56, 1)] }, { coefficient := 2, powers := [(12, 1), (18, 1), (56, 1)] }, { coefficient := 1, powers := [(17, 1), (18, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(0, 2), (5, 1), (12, 1), (22, 1), (50, 1), (56, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 2), (5, 1), (12, 1), (33, 1), (39, 1), (50, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 2), (5, 1), (50, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (5, 1), (12, 1), (18, 1), (22, 1), (50, 1), (56, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (5, 1), (12, 1), (18, 1), (33, 1), (39, 1), (50, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (5, 1), (12, 1), (22, 1), (23, 1), (50, 1), (56, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (5, 1), (12, 1), (23, 1), (33, 1), (39, 1), (50, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (5, 1), (18, 1), (50, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (5, 1), (23, 1), (50, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (12, 2), (18, 1), (22, 1), (46, 1), (50, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (12, 1), (18, 1), (46, 1), (50, 1)] }, { coefficient := 1, powers := [(3, 1), (12, 1), (18, 1), (39, 1), (46, 1), (58, 1), (63, 1)] }, { coefficient := 1, powers := [(5, 1), (12, 1), (18, 1), (22, 1), (23, 1), (50, 1), (56, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (12, 1), (18, 1), (23, 1), (33, 1), (39, 1), (50, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (18, 1), (59, 1)] }, { coefficient := 1, powers := [(12, 2), (18, 2), (22, 1), (46, 1), (50, 1), (56, 1)] }, { coefficient := 1, powers := [(12, 1), (18, 2), (46, 1), (50, 1)] }, { coefficient := -1, powers := [(12, 1), (18, 1), (46, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (6, 1), (39, 1), (58, 1), (59, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (8, 1), (12, 1), (22, 1), (50, 1), (56, 1), (59, 1)] }, { coefficient := -1, powers := [(0, 1), (8, 1), (12, 1), (33, 1), (39, 1), (50, 1), (56, 1)] }, { coefficient := -1, powers := [(0, 1), (8, 1), (50, 1), (59, 1)] }, { coefficient := -1, powers := [(3, 1), (8, 1), (39, 1), (58, 1), (59, 1), (63, 1)] }, { coefficient := -1, powers := [(8, 1), (12, 1), (18, 1), (22, 1), (50, 1), (56, 1), (59, 1)] }, { coefficient := -1, powers := [(8, 1), (12, 1), (18, 1), (33, 1), (39, 1), (50, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (12, 1), (22, 1), (50, 1), (53, 1), (56, 1)] }, { coefficient := -1, powers := [(0, 1), (50, 1), (53, 1)] }, { coefficient := -1, powers := [(12, 1), (18, 1), (22, 1), (50, 1), (53, 1), (56, 1)] }, { coefficient := -1, powers := [(18, 1), (50, 1), (53, 1)] }, { coefficient := -1, powers := [(18, 1), (53, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (12, 1), (22, 1), (46, 1), (50, 1), (56, 1)] }, { coefficient := -1, powers := [(0, 1), (46, 1), (50, 1)] }, { coefficient := -1, powers := [(3, 1), (39, 1), (46, 1), (58, 1), (63, 1)] }, { coefficient := -1, powers := [(12, 1), (18, 1), (22, 1), (46, 1), (50, 1), (56, 1)] }, { coefficient := -1, powers := [(18, 1), (46, 1), (50, 1)] }, { coefficient := -1, powers := [(18, 1), (46, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (12, 1), (18, 1), (22, 1), (27, 1), (46, 1), (50, 1), (56, 1)] }, { coefficient := -1, powers := [(0, 1), (18, 1), (27, 1), (46, 1), (50, 1)] }, { coefficient := -1, powers := [(3, 1), (18, 1), (27, 1), (39, 1), (46, 1), (58, 1), (63, 1)] }, { coefficient := -1, powers := [(12, 1), (18, 2), (22, 1), (27, 1), (46, 1), (50, 1), (56, 1)] }, { coefficient := -1, powers := [(18, 2), (27, 1), (46, 1), (50, 1)] }, { coefficient := 1, powers := [(18, 1), (27, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (18, 1), (27, 1), (39, 1), (50, 1)] }, { coefficient := 1, powers := [(0, 1), (22, 1), (53, 1)] }, { coefficient := 1, powers := [(3, 1), (18, 1), (27, 1), (39, 1), (58, 1)] }, { coefficient := 1, powers := [(18, 2), (27, 1), (39, 1), (50, 1)] }, { coefficient := 1, powers := [(18, 2), (27, 1), (39, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (39, 1), (41, 1), (50, 1), (62, 1)] }, { coefficient := 1, powers := [(3, 1), (39, 1), (41, 1), (58, 1), (62, 1)] }, { coefficient := 1, powers := [(18, 1), (39, 1), (41, 1), (50, 1), (62, 1)] }, { coefficient := 1, powers := [(18, 1), (39, 1), (41, 1), (55, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (12, 1), (22, 1), (27, 1), (46, 1), (50, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (27, 1), (46, 1), (50, 1)] }, { coefficient := 1, powers := [(3, 1), (27, 1), (39, 1), (46, 1), (58, 1), (63, 1)] }, { coefficient := 1, powers := [(12, 1), (18, 1), (22, 1), (27, 1), (46, 1), (50, 1), (56, 1)] }, { coefficient := 1, powers := [(18, 1), (27, 1), (46, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (27, 1), (39, 1), (50, 1)] }, { coefficient := 1, powers := [(3, 1), (27, 1), (39, 1), (58, 1)] }, { coefficient := 1, powers := [(18, 1), (27, 1), (39, 1), (50, 1)] }, { coefficient := 1, powers := [(18, 1), (27, 1), (39, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (27, 1), (39, 1), (48, 1), (58, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (5, 1), (12, 1), (33, 1), (50, 1), (56, 1)] }, { coefficient := -1, powers := [(0, 1), (12, 1), (17, 1), (22, 1), (50, 1), (56, 1)] }, { coefficient := -1, powers := [(0, 1), (17, 1), (50, 1)] }, { coefficient := -1, powers := [(3, 1), (17, 1), (39, 1), (58, 1), (63, 1)] }, { coefficient := 1, powers := [(5, 1), (12, 1), (18, 1), (33, 1), (50, 1), (56, 1)] }, { coefficient := -1, powers := [(12, 1), (17, 1), (18, 1), (22, 1), (50, 1), (56, 1)] }, { coefficient := -1, powers := [(17, 1), (18, 1), (50, 1)] }, { coefficient := -1, powers := [(17, 1), (18, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (18, 1), (27, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (27, 1), (39, 1), (58, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (39, 1), (58, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (5, 1), (12, 1), (30, 1), (50, 1), (56, 1)] }, { coefficient := -1, powers := [(0, 1), (12, 2), (22, 1), (50, 1), (56, 1)] }, { coefficient := -1, powers := [(0, 1), (12, 1), (50, 1)] }, { coefficient := -1, powers := [(3, 1), (12, 1), (39, 1), (58, 1), (63, 1)] }, { coefficient := -1, powers := [(5, 1), (12, 1), (18, 1), (30, 1), (50, 1), (56, 1)] }, { coefficient := -1, powers := [(12, 2), (18, 1), (22, 1), (50, 1), (56, 1)] }, { coefficient := -1, powers := [(12, 1), (18, 1), (50, 1)] }, { coefficient := -1, powers := [(12, 1), (18, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (5, 1), (12, 1), (22, 1), (27, 1), (50, 1), (56, 1), (59, 1)] }, { coefficient := -1, powers := [(0, 1), (5, 1), (12, 1), (27, 1), (33, 1), (39, 1), (50, 1), (56, 1)] }, { coefficient := -1, powers := [(0, 1), (5, 1), (27, 1), (50, 1), (59, 1)] }, { coefficient := -1, powers := [(5, 1), (12, 1), (18, 1), (22, 1), (27, 1), (50, 1), (56, 1), (59, 1)] }, { coefficient := -1, powers := [(5, 1), (12, 1), (18, 1), (27, 1), (33, 1), (39, 1), (50, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (5, 1), (30, 1), (55, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (18, 1), (30, 1), (55, 1), (56, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := -1, powers := [(0, 1), (18, 1), (50, 1), (56, 1)] }, { coefficient := -1, powers := [(0, 1), (18, 1), (55, 1), (56, 1)] }, { coefficient := -1, powers := [(0, 1), (56, 1)] }, { coefficient := -1, powers := [(18, 2), (50, 1), (56, 1)] }, { coefficient := -1, powers := [(18, 2), (55, 1), (56, 1)] }, { coefficient := -2, powers := [(18, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (39, 1), (50, 1), (62, 1)] }, { coefficient := -1, powers := [(3, 1), (39, 1), (58, 1), (62, 1)] }, { coefficient := -1, powers := [(18, 1), (39, 1), (50, 1), (62, 1)] }, { coefficient := -1, powers := [(18, 1), (39, 1), (55, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (18, 1), (22, 1), (50, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (5, 1), (30, 1), (50, 1), (56, 1), (63, 1)] }, { coefficient := -1, powers := [(5, 1), (18, 1), (30, 1), (50, 1), (56, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (6, 1), (12, 1), (22, 1), (50, 1), (56, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (6, 1), (12, 1), (33, 1), (39, 1), (50, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (6, 1), (50, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (6, 1), (39, 1), (58, 1), (59, 1), (63, 1)] }, { coefficient := 1, powers := [(6, 1), (12, 1), (18, 1), (22, 1), (50, 1), (56, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (12, 1), (18, 1), (33, 1), (39, 1), (50, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (18, 1), (27, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (12, 1), (22, 1), (50, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (50, 1)] }, { coefficient := 1, powers := [(3, 1), (39, 1), (58, 1), (63, 1)] }, { coefficient := 1, powers := [(12, 1), (18, 1), (22, 1), (50, 1), (56, 1)] }, { coefficient := 1, powers := [(18, 1), (50, 1)] }, { coefficient := 1, powers := [(18, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(0, 2), (5, 1), (30, 1), (45, 1), (50, 1), (51, 1), (56, 1), (63, 1)] }, { coefficient := 1, powers := [(0, 1), (5, 1), (12, 1), (22, 1), (33, 1), (50, 1), (53, 1), (56, 1)] }, { coefficient := -1, powers := [(0, 1), (5, 1), (12, 1), (27, 1), (30, 1), (46, 1), (50, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (5, 1), (18, 1), (27, 1), (44, 1), (51, 1), (58, 1)] }, { coefficient := -1, powers := [(0, 1), (5, 1), (18, 1), (30, 1), (45, 1), (50, 1), (51, 1), (56, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (5, 1), (19, 1), (30, 1), (48, 1), (50, 1), (55, 1), (56, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (5, 1), (19, 1), (30, 1), (50, 1), (51, 1), (56, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (5, 1), (30, 1), (45, 1), (48, 1), (50, 1), (56, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (12, 1), (17, 1), (22, 2), (50, 1), (53, 1), (56, 1)] }, { coefficient := -1, powers := [(0, 1), (12, 1), (18, 1), (22, 1), (44, 1), (50, 1), (52, 1)] }, { coefficient := -1, powers := [(0, 1), (16, 1), (27, 1), (39, 1), (41, 1), (50, 1)] }, { coefficient := -1, powers := [(3, 1), (16, 1), (27, 1), (39, 1), (41, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (12, 1), (18, 1), (22, 1), (33, 1), (50, 1), (53, 1), (56, 1)] }, { coefficient := -1, powers := [(5, 1), (12, 1), (18, 1), (27, 1), (30, 1), (46, 1), (50, 1), (56, 1)] }, { coefficient := -1, powers := [(5, 1), (18, 1), (19, 1), (30, 1), (48, 1), (50, 1), (55, 1), (56, 1), (63, 1)] }, { coefficient := -1, powers := [(5, 1), (18, 1), (19, 1), (30, 1), (50, 1), (51, 1), (56, 1), (63, 1)] }, { coefficient := 1, powers := [(5, 1), (18, 1), (27, 1), (41, 1), (51, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (18, 1), (27, 1), (44, 1), (48, 1), (58, 1)] }, { coefficient := -1, powers := [(5, 1), (18, 1), (30, 1), (45, 1), (48, 1), (50, 1), (56, 1), (63, 1)] }, { coefficient := -1, powers := [(12, 1), (17, 1), (18, 1), (22, 2), (50, 1), (53, 1), (56, 1)] }, { coefficient := -1, powers := [(12, 1), (18, 1), (22, 1), (24, 1), (44, 1), (50, 1)] }, { coefficient := -1, powers := [(12, 1), (18, 1), (22, 1), (41, 1), (50, 1), (52, 1)] }, { coefficient := -1, powers := [(16, 1), (18, 1), (27, 1), (39, 1), (41, 1), (50, 1)] }, { coefficient := -1, powers := [(16, 1), (18, 1), (27, 1), (39, 1), (41, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (6, 1), (12, 1), (22, 1), (36, 1), (50, 1), (56, 1), (58, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (6, 1), (12, 1), (22, 1), (45, 1), (50, 1), (52, 1), (56, 1), (59, 1)] }, { coefficient := -1, powers := [(0, 1), (6, 1), (12, 1), (33, 1), (36, 1), (39, 1), (50, 1), (56, 1), (58, 1)] }, { coefficient := 1, powers := [(0, 1), (6, 1), (12, 1), (33, 1), (39, 1), (45, 1), (50, 1), (52, 1), (56, 1)] }, { coefficient := -1, powers := [(0, 1), (6, 1), (36, 1), (50, 1), (58, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (6, 1), (45, 1), (50, 1), (52, 1), (59, 1)] }, { coefficient := -1, powers := [(0, 1), (12, 1), (22, 1), (36, 1), (50, 1), (56, 1), (59, 1)] }, { coefficient := -1, powers := [(0, 1), (12, 1), (22, 1), (39, 1), (50, 1), (56, 2)] }, { coefficient := 1, powers := [(0, 1), (12, 1), (22, 1), (46, 1), (50, 1), (53, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (18, 1), (39, 1), (50, 1), (55, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (18, 1), (39, 1), (55, 2), (56, 1)] }, { coefficient := -1, powers := [(0, 1), (36, 1), (50, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (37, 1), (39, 1), (41, 1), (50, 1), (52, 1), (62, 1)] }, { coefficient := 1, powers := [(0, 1), (37, 1), (39, 1), (50, 1), (56, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 1), (39, 1), (50, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (39, 1), (55, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (44, 1), (45, 1), (53, 1)] }, { coefficient := 1, powers := [(0, 1), (46, 1), (50, 1), (53, 1)] }, { coefficient := -1, powers := [(3, 1), (6, 1), (36, 1), (39, 1), (58, 2), (59, 1), (63, 1)] }, { coefficient := 1, powers := [(3, 1), (6, 1), (39, 1), (45, 1), (52, 1), (58, 1), (59, 1), (63, 1)] }, { coefficient := -1, powers := [(3, 1), (36, 1), (39, 1), (58, 1), (59, 1), (63, 1)] }, { coefficient := 1, powers := [(3, 1), (37, 1), (39, 1), (41, 1), (52, 1), (58, 1), (62, 1)] }, { coefficient := 1, powers := [(3, 1), (37, 1), (39, 1), (56, 1), (58, 1), (62, 1)] }, { coefficient := -1, powers := [(3, 1), (39, 2), (56, 1), (58, 1), (63, 1)] }, { coefficient := -1, powers := [(6, 1), (12, 1), (18, 1), (22, 1), (36, 1), (50, 1), (56, 1), (58, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (12, 1), (18, 1), (22, 1), (45, 1), (50, 1), (52, 1), (56, 1), (59, 1)] }, { coefficient := -1, powers := [(6, 1), (12, 1), (18, 1), (33, 1), (36, 1), (39, 1), (50, 1), (56, 1), (58, 1)] }, { coefficient := 1, powers := [(6, 1), (12, 1), (18, 1), (33, 1), (39, 1), (45, 1), (50, 1), (52, 1), (56, 1)] }, { coefficient := -1, powers := [(12, 1), (18, 1), (22, 1), (36, 1), (50, 1), (56, 1), (59, 1)] }, { coefficient := -1, powers := [(12, 1), (18, 1), (22, 1), (39, 1), (50, 1), (56, 2)] }, { coefficient := 1, powers := [(12, 1), (18, 1), (22, 1), (46, 1), (50, 1), (53, 1), (56, 1)] }, { coefficient := 1, powers := [(18, 2), (39, 1), (50, 1), (55, 1), (56, 1)] }, { coefficient := 1, powers := [(18, 2), (39, 1), (55, 2), (56, 1)] }, { coefficient := -1, powers := [(18, 1), (36, 1), (50, 1), (59, 1)] }, { coefficient := -1, powers := [(18, 1), (36, 1), (55, 1), (59, 1)] }, { coefficient := 1, powers := [(18, 1), (37, 1), (39, 1), (41, 1), (50, 1), (52, 1), (62, 1)] }, { coefficient := 1, powers := [(18, 1), (37, 1), (39, 1), (41, 1), (52, 1), (55, 1), (62, 1)] }, { coefficient := 1, powers := [(18, 1), (37, 1), (39, 1), (50, 1), (56, 1), (62, 1)] }, { coefficient := 1, powers := [(18, 1), (37, 1), (39, 1), (55, 1), (56, 1), (62, 1)] }, { coefficient := -1, powers := [(18, 1), (39, 1), (50, 1), (56, 1)] }, { coefficient := 1, powers := [(18, 1), (39, 1), (55, 1), (56, 1)] }, { coefficient := 1, powers := [(18, 1), (46, 1), (50, 1), (53, 1)] }, { coefficient := 1, powers := [(18, 1), (46, 1), (51, 1), (52, 1)] }, { coefficient := 1, powers := [(18, 1), (46, 1), (53, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (8, 1), (33, 1), (39, 1), (50, 1)] }, { coefficient := 1, powers := [(0, 1), (17, 1), (27, 1), (39, 1), (50, 1)] }, { coefficient := 1, powers := [(3, 1), (8, 1), (33, 1), (39, 1), (58, 1)] }, { coefficient := 1, powers := [(3, 1), (17, 1), (27, 1), (39, 1), (58, 1)] }, { coefficient := 1, powers := [(8, 1), (18, 1), (33, 1), (39, 1), (50, 1)] }, { coefficient := 1, powers := [(8, 1), (18, 1), (33, 1), (39, 1), (55, 1)] }, { coefficient := 1, powers := [(17, 1), (18, 1), (27, 1), (39, 1), (50, 1)] }, { coefficient := 1, powers := [(17, 1), (18, 1), (27, 1), (39, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(0, 2), (5, 1), (12, 1), (22, 1), (27, 1), (50, 1), (56, 1), (59, 1)] }, { coefficient := -1, powers := [(0, 2), (5, 1), (12, 1), (27, 1), (33, 1), (39, 1), (50, 1), (56, 1)] }, { coefficient := -1, powers := [(0, 2), (5, 1), (27, 1), (50, 1), (59, 1)] }, { coefficient := -1, powers := [(0, 1), (5, 1), (12, 1), (18, 1), (22, 1), (27, 1), (50, 1), (56, 1), (59, 1)] }, { coefficient := -1, powers := [(0, 1), (5, 1), (12, 1), (18, 1), (27, 1), (33, 1), (39, 1), (50, 1), (56, 1)] }, { coefficient := -1, powers := [(0, 1), (5, 1), (18, 1), (27, 1), (50, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (5, 1), (18, 1), (27, 1), (55, 1), (59, 1)] }, { coefficient := -1, powers := [(0, 1), (12, 2), (18, 1), (22, 1), (27, 1), (46, 1), (50, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (12, 1), (18, 1), (22, 1), (50, 1), (56, 1)] }, { coefficient := -1, powers := [(0, 1), (12, 1), (18, 1), (27, 1), (46, 1), (50, 1)] }, { coefficient := -1, powers := [(0, 1), (17, 1), (18, 1), (27, 1), (39, 1), (50, 1)] }, { coefficient := -1, powers := [(0, 1), (17, 1), (22, 1), (53, 1)] }, { coefficient := -1, powers := [(0, 1), (17, 1), (23, 1), (27, 1), (39, 1), (50, 1)] }, { coefficient := -1, powers := [(3, 1), (12, 1), (18, 1), (27, 1), (39, 1), (46, 1), (58, 1), (63, 1)] }, { coefficient := -1, powers := [(3, 1), (17, 1), (18, 1), (27, 1), (39, 1), (58, 1)] }, { coefficient := -1, powers := [(3, 1), (17, 1), (23, 1), (27, 1), (39, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (23, 1), (27, 1), (39, 1), (41, 1), (48, 1), (58, 1), (63, 1)] }, { coefficient := -1, powers := [(12, 2), (18, 2), (22, 1), (27, 1), (46, 1), (50, 1), (56, 1)] }, { coefficient := -1, powers := [(12, 1), (18, 2), (27, 1), (46, 1), (50, 1)] }, { coefficient := 1, powers := [(12, 1), (18, 1), (22, 1), (24, 1), (41, 1), (50, 1)] }, { coefficient := 1, powers := [(12, 1), (18, 1), (27, 1), (46, 1)] }, { coefficient := -1, powers := [(17, 1), (18, 2), (27, 1), (39, 1), (50, 1)] }, { coefficient := -1, powers := [(17, 1), (18, 2), (27, 1), (39, 1), (55, 1)] }, { coefficient := -1, powers := [(17, 1), (18, 1), (23, 1), (27, 1), (39, 1), (50, 1)] }, { coefficient := -1, powers := [(17, 1), (18, 1), (23, 1), (27, 1), (39, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(0, 2), (5, 1), (30, 1), (50, 1), (55, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (5, 1), (18, 1), (30, 1), (50, 1), (55, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (5, 1), (30, 1), (50, 1), (56, 1)] }, { coefficient := -1, powers := [(3, 1), (8, 1), (33, 1), (39, 1), (58, 1)] }, { coefficient := 1, powers := [(3, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (18, 1), (30, 1), (50, 1), (56, 1)] }]
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
    (values : Fin 64 → R) :
    ¬ ∀ index : Fin 50,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component62.SelectedLeafB6_5.selectedHasNoCommonZero

end Krenn.Component62.SelectedLeafB6_5
