import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component62.SelectedLeafB5

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "d4ea1291034d7e670d7086a688f46717406f96a1d1c075621c2b5d98446eb3f8"
def certificateSHA256 : String := "2c3ae4d5bc8309f4160a81326ee3a2ad9a7febae85068d9aac19e9c088f25e65"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 54 → Fin 661 := ![
  1,
  2,
  4,
  5,
  7,
  18,
  21,
  22,
  52,
  135,
  137,
  140,
  150,
  153,
  158,
  159,
  160,
  172,
  191,
  293,
  294,
  296,
  309,
  311,
  313,
  316,
  318,
  340,
  363,
  390,
  408,
  440,
  441,
  444,
  454,
  476,
  480,
  483,
  515,
  557,
  578,
  579,
  588,
  589,
  604,
  606,
  619,
  646,
  647,
  656,
  657,
  658,
  659,
  660
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 54 → SparsePoly (Fin 62) := ![
  [{ coefficient := 1, powers := [(2, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (30, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(30, 1), (35, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (30, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (45, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (52, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (30, 1)] }, { coefficient := 1, powers := [(30, 1), (34, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (44, 1)] }, { coefficient := 1, powers := [(17, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (18, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (50, 1)] }, { coefficient := 1, powers := [(22, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (52, 1)] }, { coefficient := 1, powers := [(27, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (38, 1)] }, { coefficient := 1, powers := [(27, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (34, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (22, 1), (58, 1)] }, { coefficient := 1, powers := [(22, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (41, 1)] }, { coefficient := 1, powers := [(18, 1), (41, 1)] }, { coefficient := 1, powers := [(23, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1)] }, { coefficient := 1, powers := [(19, 1), (41, 1)] }, { coefficient := 1, powers := [(23, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (53, 1)] }, { coefficient := 1, powers := [(18, 1), (53, 1)] }, { coefficient := 1, powers := [(24, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (43, 1)] }, { coefficient := 1, powers := [(12, 1), (55, 1)] }, { coefficient := 1, powers := [(16, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (44, 1)] }, { coefficient := 1, powers := [(17, 1), (38, 1)] }, { coefficient := 1, powers := [(17, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (41, 1), (50, 1)] }, { coefficient := 1, powers := [(18, 1), (41, 1), (50, 1)] }, { coefficient := 1, powers := [(41, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1), (53, 1)] }, { coefficient := 1, powers := [(24, 1), (43, 1), (48, 1)] }, { coefficient := 1, powers := [(53, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1), (50, 1)] }, { coefficient := 1, powers := [(19, 1), (41, 1), (50, 1)] }, { coefficient := 1, powers := [(46, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (35, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (38, 1), (55, 1)] }, { coefficient := 1, powers := [(2, 1), (43, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (30, 1), (55, 1)] }, { coefficient := 1, powers := [(7, 1), (30, 1), (43, 1)] }, { coefficient := 1, powers := [(14, 1), (30, 1), (35, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (18, 1), (55, 1)] }, { coefficient := 1, powers := [(12, 1)] }, { coefficient := 1, powers := [(16, 1), (18, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (23, 1), (44, 1)] }, { coefficient := 1, powers := [(17, 1), (23, 1), (38, 1)] }, { coefficient := 1, powers := [(17, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (58, 1)] }, { coefficient := 1, powers := [(16, 1), (19, 1), (50, 1)] }, { coefficient := 1, powers := [(16, 1), (19, 1), (55, 1)] }, { coefficient := 1, powers := [(16, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (59, 1)] }, { coefficient := 1, powers := [(12, 1), (46, 1)] }, { coefficient := 1, powers := [(17, 1), (19, 1), (51, 1)] }, { coefficient := 1, powers := [(17, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (59, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (44, 1)] }, { coefficient := 1, powers := [(12, 1), (56, 1)] }, { coefficient := 1, powers := [(17, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (53, 1)] }, { coefficient := 1, powers := [(27, 1), (39, 1)] }, { coefficient := 1, powers := [(27, 1), (45, 1), (48, 1)] }, { coefficient := 1, powers := [(30, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1), (53, 1)] }, { coefficient := 1, powers := [(24, 1), (44, 1), (48, 1)] }, { coefficient := 1, powers := [(41, 1), (53, 1)] }, { coefficient := 1, powers := [(48, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1), (50, 1)] }, { coefficient := 1, powers := [(19, 1), (50, 1)] }, { coefficient := 1, powers := [(19, 1), (55, 1)] }, { coefficient := 1, powers := [(45, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1), (51, 1)] }, { coefficient := 1, powers := [(19, 1), (41, 1), (51, 1)] }, { coefficient := 1, powers := [(39, 1), (41, 1)] }, { coefficient := 1, powers := [(46, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (22, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (30, 1), (46, 1)] }, { coefficient := 1, powers := [(6, 1), (33, 1), (39, 1)] }, { coefficient := 1, powers := [(22, 1), (41, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (41, 1), (52, 1)] }, { coefficient := 1, powers := [(22, 1), (56, 1)] }, { coefficient := 1, powers := [(27, 1), (46, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1)] }, { coefficient := 1, powers := [(6, 1), (58, 1)] }, { coefficient := 1, powers := [(23, 1), (38, 1)] }, { coefficient := 1, powers := [(23, 1), (43, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (50, 1)] }, { coefficient := 1, powers := [(3, 1), (58, 1)] }, { coefficient := 1, powers := [(18, 1), (50, 1)] }, { coefficient := 1, powers := [(18, 1), (55, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (38, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1), (44, 1)] }, { coefficient := 1, powers := [(17, 1), (27, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (39, 1), (55, 1)] }, { coefficient := 1, powers := [(2, 1), (45, 1), (51, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (55, 1)] }, { coefficient := 1, powers := [(12, 1), (22, 1), (55, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (58, 1)] }, { coefficient := 1, powers := [(7, 1), (58, 1)] }, { coefficient := 1, powers := [(10, 1), (43, 1)] }, { coefficient := 1, powers := [(10, 1), (55, 1)] }, { coefficient := 1, powers := [(14, 1), (38, 1)] }, { coefficient := 1, powers := [(14, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (34, 1), (58, 1)] }, { coefficient := 1, powers := [(0, 1)] }, { coefficient := 1, powers := [(3, 1), (23, 1), (58, 1)] }, { coefficient := 1, powers := [(6, 1), (18, 1), (58, 1)] }, { coefficient := 1, powers := [(18, 1)] }, { coefficient := 1, powers := [(23, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (36, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (45, 1), (52, 1)] }, { coefficient := 1, powers := [(5, 1), (27, 1), (58, 1)] }, { coefficient := 1, powers := [(8, 1), (22, 1), (58, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1), (52, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (35, 1), (58, 1)] }, { coefficient := 1, powers := [(0, 1), (38, 1), (55, 1)] }, { coefficient := 1, powers := [(0, 1), (43, 1), (50, 1)] }, { coefficient := 1, powers := [(38, 1)] }, { coefficient := 1, powers := [(43, 1)] }, { coefficient := 1, powers := [(50, 1)] }, { coefficient := 1, powers := [(55, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (36, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (46, 1), (53, 1)] }, { coefficient := 1, powers := [(19, 1), (41, 1), (53, 1)] }, { coefficient := 1, powers := [(19, 1), (48, 1), (56, 1)] }, { coefficient := 1, powers := [(24, 1), (39, 1), (41, 1)] }, { coefficient := 1, powers := [(24, 1), (46, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (35, 1), (58, 1)] }, { coefficient := 1, powers := [(1, 1), (38, 1), (55, 1)] }, { coefficient := 1, powers := [(1, 1), (43, 1), (50, 1)] }, { coefficient := 1, powers := [(4, 1), (26, 1), (58, 1)] }, { coefficient := 1, powers := [(4, 1), (29, 1), (55, 1)] }, { coefficient := 1, powers := [(4, 1), (32, 1), (50, 1)] }, { coefficient := 1, powers := [(7, 1), (21, 1), (58, 1)] }, { coefficient := 1, powers := [(7, 1), (29, 1), (43, 1)] }, { coefficient := 1, powers := [(7, 1), (32, 1), (38, 1)] }, { coefficient := 1, powers := [(10, 1), (21, 1), (55, 1)] }, { coefficient := 1, powers := [(10, 1), (26, 1), (43, 1)] }, { coefficient := 1, powers := [(10, 1), (32, 1), (35, 1)] }, { coefficient := 1, powers := [(14, 1), (21, 1), (50, 1)] }, { coefficient := 1, powers := [(14, 1), (26, 1), (38, 1)] }, { coefficient := 1, powers := [(14, 1), (29, 1), (35, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (36, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (46, 1), (53, 1)] }, { coefficient := 1, powers := [(5, 1), (27, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (53, 1)] }, { coefficient := 1, powers := [(8, 1), (22, 1), (59, 1)] }, { coefficient := 1, powers := [(8, 1), (30, 1), (46, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (39, 1)] }, { coefficient := 1, powers := [(12, 1), (22, 1), (56, 1)] }, { coefficient := 1, powers := [(12, 1), (27, 1), (46, 1)] }, { coefficient := 1, powers := [(12, 1), (33, 1), (36, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (53, 1)] }, { coefficient := 1, powers := [(17, 1), (27, 1), (39, 1)] }, { coefficient := 1, powers := [(17, 1), (30, 1), (36, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (60, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (61, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 54 → SparsePoly (Fin 62) := ![
  [{ coefficient := 2, powers := [(0, 1), (2, 1), (39, 1), (56, 1), (61, 1)] }, { coefficient := -2, powers := [(0, 1), (8, 1), (33, 1), (39, 1), (61, 1)] }, { coefficient := -2, powers := [(0, 1), (39, 1), (56, 1)] }, { coefficient := 2, powers := [(2, 1), (3, 1), (23, 1), (39, 1), (56, 1), (58, 1), (61, 1)] }, { coefficient := -2, powers := [(2, 1), (12, 1), (18, 1), (22, 1), (56, 1), (61, 2)] }, { coefficient := -2, powers := [(2, 1), (17, 1), (18, 1), (22, 1), (53, 1), (61, 2)] }, { coefficient := 2, powers := [(2, 1), (18, 1), (23, 1), (39, 1), (55, 1), (56, 1), (61, 1)] }, { coefficient := 2, powers := [(2, 1), (23, 1), (39, 1), (56, 1), (61, 1)] }, { coefficient := 4, powers := [(3, 1), (5, 1), (7, 1), (29, 1), (30, 1), (56, 1), (58, 1), (61, 1)] }, { coefficient := 2, powers := [(5, 1), (18, 1), (33, 1), (53, 1), (61, 1)] }, { coefficient := -2, powers := [(8, 1), (23, 1), (33, 1), (39, 1), (61, 1)] }, { coefficient := 2, powers := [(12, 1), (18, 1), (22, 1), (56, 1), (61, 1)] }, { coefficient := 2, powers := [(17, 1), (18, 1), (22, 1), (53, 1), (61, 1)] }, { coefficient := -2, powers := [(17, 1), (23, 1), (27, 1), (39, 1), (61, 1)] }, { coefficient := -2, powers := [(23, 1), (39, 1), (56, 1)] }],
  [{ coefficient := -2, powers := [(2, 1), (18, 1), (19, 1), (53, 1), (60, 1), (61, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (2, 1), (23, 1), (39, 1), (43, 1), (56, 1), (61, 1)] }, { coefficient := 4, powers := [(0, 1), (5, 1), (30, 1), (56, 1), (61, 1)] }, { coefficient := -6, powers := [(0, 1), (16, 1), (30, 1), (34, 1), (45, 1), (56, 1), (61, 1)] }, { coefficient := -2, powers := [(2, 1), (12, 1), (23, 1), (27, 1), (46, 1), (61, 2)] }, { coefficient := -2, powers := [(2, 1), (17, 1), (23, 1), (27, 1), (39, 1), (61, 2)] }, { coefficient := 2, powers := [(2, 1), (18, 1), (23, 1), (39, 1), (43, 1), (56, 1), (61, 1)] }, { coefficient := 2, powers := [(2, 1), (19, 1), (23, 1), (41, 1), (53, 1), (60, 1), (61, 1)] }, { coefficient := 2, powers := [(2, 1), (23, 2), (46, 1), (53, 1), (60, 1), (61, 1)] }, { coefficient := -2, powers := [(2, 1), (23, 1), (39, 1), (56, 1), (61, 1)] }, { coefficient := 2, powers := [(2, 1), (23, 1), (46, 1), (53, 1), (61, 1)] }, { coefficient := 4, powers := [(3, 1), (4, 1), (5, 1), (30, 1), (32, 1), (56, 1), (58, 1), (61, 1)] }, { coefficient := 4, powers := [(3, 1), (5, 1), (14, 1), (21, 1), (30, 1), (56, 1), (58, 1), (61, 1)] }, { coefficient := -4, powers := [(3, 1), (5, 1), (14, 1), (26, 1), (30, 1), (56, 1), (58, 1), (61, 1)] }, { coefficient := 4, powers := [(5, 1), (18, 1), (30, 1), (56, 1), (61, 1)] }, { coefficient := -2, powers := [(8, 1), (23, 1), (30, 1), (34, 1), (46, 1), (58, 1), (61, 1)] }, { coefficient := 2, powers := [(8, 1), (23, 1), (30, 1), (46, 1), (61, 1)] }, { coefficient := -2, powers := [(12, 1), (22, 1), (23, 1), (56, 1), (61, 1)] }],
  [{ coefficient := -2, powers := [(2, 1), (16, 1), (18, 1), (22, 1), (56, 1), (61, 2)] }, { coefficient := -2, powers := [(2, 1), (16, 1), (22, 1), (23, 1), (56, 1), (61, 2)] }, { coefficient := -2, powers := [(2, 1), (17, 1), (19, 1), (27, 1), (61, 2)] }, { coefficient := 2, powers := [(2, 1), (17, 1), (22, 1), (24, 1), (61, 2)] }, { coefficient := -2, powers := [(2, 1), (23, 1), (24, 1), (46, 1), (60, 1), (61, 1)] }, { coefficient := 2, powers := [(16, 1), (18, 1), (22, 1), (56, 1), (61, 1)] }, { coefficient := 2, powers := [(16, 1), (22, 1), (23, 1), (56, 1), (61, 1)] }, { coefficient := -2, powers := [(17, 1), (22, 1), (24, 1), (61, 1)] }],
  [{ coefficient := 4, powers := [(3, 1), (5, 1), (21, 1), (56, 1), (58, 2)] }, { coefficient := -4, powers := [(3, 1), (5, 1), (26, 1), (56, 1), (58, 2)] }, { coefficient := -4, powers := [(3, 1), (5, 1), (29, 1), (43, 1), (56, 1), (58, 1)] }, { coefficient := 4, powers := [(3, 1), (5, 1), (32, 1), (38, 1), (56, 1), (58, 1)] }],
  [{ coefficient := 2, powers := [(8, 1), (48, 1), (58, 1)] }, { coefficient := -2, powers := [(12, 1), (52, 1)] }],
  [{ coefficient := -2, powers := [(17, 1), (45, 1)] }],
  [{ coefficient := 4, powers := [(3, 1), (5, 1), (10, 1), (32, 1), (56, 1), (58, 1)] }],
  [{ coefficient := 4, powers := [(5, 1), (10, 1), (21, 1), (56, 1), (58, 1)] }, { coefficient := -4, powers := [(5, 1), (10, 1), (26, 1), (56, 1), (58, 1)] }, { coefficient := -2, powers := [(5, 1), (23, 1), (56, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (34, 1), (52, 1), (59, 1), (61, 1)] }, { coefficient := 2, powers := [(23, 1), (51, 1), (56, 1)] }, { coefficient := 1, powers := [(34, 1), (52, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (34, 1), (45, 1), (59, 1), (61, 1)] }, { coefficient := 2, powers := [(23, 1), (39, 1), (44, 1)] }, { coefficient := 1, powers := [(34, 1), (45, 1), (59, 1)] }],
  [{ coefficient := -2, powers := [(5, 1), (18, 1), (55, 1), (56, 1), (58, 1)] }, { coefficient := 2, powers := [(8, 1), (46, 1), (58, 1)] }],
  [{ coefficient := -2, powers := [(2, 1), (22, 1), (24, 1), (61, 1)] }, { coefficient := 2, powers := [(22, 1), (24, 1)] }],
  [{ coefficient := 2, powers := [(2, 1), (22, 1), (51, 1), (56, 1), (61, 1)] }, { coefficient := -2, powers := [(22, 1), (51, 1), (56, 1)] }],
  [{ coefficient := 2, powers := [(12, 1), (23, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (16, 1), (34, 1), (59, 1), (61, 1)] }, { coefficient := 1, powers := [(16, 1), (34, 1), (59, 1)] }],
  [{ coefficient := 2, powers := [(17, 1), (23, 1), (39, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (5, 1), (30, 1), (55, 1), (56, 1), (61, 1)] }, { coefficient := -2, powers := [(2, 1), (5, 1), (27, 1), (59, 1), (61, 2)] }, { coefficient := -2, powers := [(2, 1), (8, 1), (22, 1), (59, 1), (61, 2)] }, { coefficient := -2, powers := [(2, 1), (36, 1), (59, 1), (61, 1)] }, { coefficient := 2, powers := [(5, 1), (18, 1), (30, 1), (55, 1), (56, 1), (61, 1)] }, { coefficient := 2, powers := [(5, 1), (27, 1), (59, 1), (61, 1)] }, { coefficient := 6, powers := [(5, 1), (30, 1), (56, 1), (61, 1)] }, { coefficient := 2, powers := [(8, 1), (22, 1), (59, 1), (61, 1)] }, { coefficient := 2, powers := [(36, 1), (59, 1)] }],
  [{ coefficient := 2, powers := [(8, 1), (59, 1)] }],
  [{ coefficient := -2, powers := [(2, 1), (19, 1), (50, 1), (53, 1), (60, 1)] }],
  [{ coefficient := 2, powers := [(2, 1), (12, 1), (27, 1), (50, 1), (61, 1)] }, { coefficient := -2, powers := [(2, 1), (23, 1), (50, 1), (53, 1), (60, 1)] }, { coefficient := 2, powers := [(2, 1), (24, 1), (51, 1), (60, 1)] }, { coefficient := -2, powers := [(2, 1), (50, 1), (53, 1)] }, { coefficient := -2, powers := [(2, 1), (53, 1), (60, 1)] }, { coefficient := 2, powers := [(8, 1), (30, 1), (34, 1), (50, 1), (58, 1)] }, { coefficient := -2, powers := [(8, 1), (30, 1), (50, 1)] }],
  [{ coefficient := 2, powers := [(2, 1), (17, 1), (22, 1), (43, 1), (61, 1)] }, { coefficient := 2, powers := [(2, 1), (19, 1), (44, 1), (60, 1)] }, { coefficient := -2, powers := [(5, 1), (33, 1), (43, 1)] }, { coefficient := -2, powers := [(17, 1), (22, 1), (43, 1)] }],
  [{ coefficient := 2, powers := [(2, 1), (18, 1), (22, 1), (56, 1), (61, 1)] }, { coefficient := -2, powers := [(18, 1), (22, 1), (56, 1)] }],
  [{ coefficient := 2, powers := [(2, 1), (23, 1), (27, 1), (39, 1), (61, 1)] }],
  [{ coefficient := 2, powers := [(2, 1), (19, 1), (53, 1), (60, 1)] }],
  [{ coefficient := -2, powers := [(2, 1), (17, 1), (22, 1), (61, 1)] }, { coefficient := 2, powers := [(5, 1), (33, 1)] }, { coefficient := 2, powers := [(17, 1), (22, 1)] }],
  [{ coefficient := -2, powers := [(2, 1), (12, 1), (27, 1), (61, 1)] }, { coefficient := 2, powers := [(2, 1), (23, 1), (53, 1), (60, 1)] }, { coefficient := 2, powers := [(2, 1), (53, 1)] }, { coefficient := -2, powers := [(8, 1), (30, 1), (34, 1), (58, 1)] }, { coefficient := 2, powers := [(8, 1), (30, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (2, 1), (23, 1), (39, 1), (56, 1), (61, 1)] }],
  [{ coefficient := 4, powers := [(3, 1), (5, 1), (29, 1), (56, 1), (58, 1)] }],
  [{ coefficient := -2, powers := [(2, 1), (22, 1), (56, 1), (61, 1)] }, { coefficient := 2, powers := [(22, 1), (56, 1)] }],
  [{ coefficient := -2, powers := [(2, 1), (27, 1), (39, 1), (61, 1)] }],
  [{ coefficient := -6, powers := [(30, 1), (34, 1), (56, 1)] }],
  [{ coefficient := 2, powers := [(2, 1), (27, 1), (61, 1)] }],
  [{ coefficient := 2, powers := [(2, 1), (22, 1), (61, 1)] }, { coefficient := -2, powers := [(22, 1)] }],
  [{ coefficient := 2, powers := [(17, 1)] }],
  [{ coefficient := -2, powers := [(2, 1), (19, 1), (60, 1)] }],
  [{ coefficient := 6, powers := [(16, 1), (30, 1), (34, 1), (56, 1)] }],
  [{ coefficient := -2, powers := [(2, 1), (24, 1), (60, 1)] }],
  [{ coefficient := -2, powers := [(8, 1), (58, 1)] }],
  [{ coefficient := 2, powers := [(12, 1)] }],
  [{ coefficient := 2, powers := [(8, 1), (33, 1), (39, 1)] }],
  [{ coefficient := -2, powers := [(2, 1), (23, 1), (39, 1), (43, 1), (56, 1)] }, { coefficient := -4, powers := [(5, 1), (30, 1), (56, 1)] }],
  [{ coefficient := -2, powers := [(23, 1), (39, 1)] }],
  [{ coefficient := -2, powers := [(23, 1), (56, 1)] }],
  [{ coefficient := 4, powers := [(3, 1), (5, 1), (26, 1), (30, 1), (56, 1), (58, 1)] }],
  [{ coefficient := 2, powers := [(5, 1), (30, 1), (55, 1), (56, 1)] }],
  [{ coefficient := 2, powers := [(2, 1), (34, 1), (59, 1), (61, 1)] }, { coefficient := -2, powers := [(34, 1), (59, 1)] }],
  [{ coefficient := 2, powers := [(2, 1), (23, 1), (39, 1), (56, 1)] }],
  [{ coefficient := 2, powers := [(2, 1), (60, 1)] }],
  [{ coefficient := -4, powers := [(3, 1), (5, 1), (30, 1), (56, 1), (58, 1)] }],
  [{ coefficient := -2, powers := [] }],
  [{ coefficient := -2, powers := [(2, 1), (36, 1), (59, 1)] }, { coefficient := -2, powers := [(2, 1), (39, 1), (56, 1)] }],
  [{ coefficient := 4, powers := [(3, 1), (5, 1), (30, 1), (35, 1), (56, 1), (58, 2)] }, { coefficient := 4, powers := [(3, 1), (5, 1), (30, 1), (38, 1), (55, 1), (56, 1), (58, 1)] }, { coefficient := 4, powers := [(3, 1), (5, 1), (30, 1), (43, 1), (50, 1), (56, 1), (58, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (2, 1), (23, 1), (35, 1), (39, 1), (56, 1), (58, 1)] }, { coefficient := 2, powers := [(0, 1), (2, 1), (23, 1), (38, 1), (39, 1), (55, 1), (56, 1)] }, { coefficient := -2, powers := [(0, 1), (2, 1), (39, 1), (43, 1), (56, 1)] }, { coefficient := 2, powers := [(0, 1), (5, 1), (30, 1), (34, 1), (55, 1), (56, 1), (58, 1)] }, { coefficient := -4, powers := [(0, 1), (5, 1), (30, 1), (50, 1), (56, 1)] }, { coefficient := 2, powers := [(0, 1), (5, 1), (30, 1), (55, 1), (56, 1)] }, { coefficient := 2, powers := [(0, 1), (8, 1), (33, 1), (39, 1), (43, 1)] }, { coefficient := 6, powers := [(0, 1), (16, 1), (30, 1), (34, 1), (45, 1), (50, 1), (56, 1)] }, { coefficient := -2, powers := [(2, 1), (3, 1), (23, 1), (39, 1), (43, 1), (56, 1), (58, 1)] }, { coefficient := 2, powers := [(2, 1), (5, 1), (27, 1), (34, 1), (58, 1), (59, 1), (61, 1)] }, { coefficient := 2, powers := [(2, 1), (5, 1), (27, 1), (59, 1), (61, 1)] }, { coefficient := 2, powers := [(2, 1), (8, 1), (22, 1), (34, 1), (58, 1), (59, 1), (61, 1)] }, { coefficient := 2, powers := [(2, 1), (8, 1), (22, 1), (59, 1), (61, 1)] }, { coefficient := 2, powers := [(2, 1), (12, 1), (18, 1), (22, 1), (43, 1), (56, 1), (61, 1)] }, { coefficient := 2, powers := [(2, 1), (12, 1), (23, 1), (27, 1), (46, 1), (50, 1), (61, 1)] }, { coefficient := 2, powers := [(2, 1), (16, 1), (18, 1), (22, 1), (51, 1), (56, 1), (61, 1)] }, { coefficient := 2, powers := [(2, 1), (16, 1), (22, 1), (23, 1), (51, 1), (56, 1), (61, 1)] }, { coefficient := 2, powers := [(2, 1), (17, 1), (18, 1), (22, 1), (43, 1), (53, 1), (61, 1)] }, { coefficient := 2, powers := [(2, 1), (17, 1), (19, 1), (27, 1), (51, 1), (61, 1)] }, { coefficient := -2, powers := [(2, 1), (17, 1), (22, 1), (24, 1), (51, 1), (61, 1)] }, { coefficient := 2, powers := [(2, 1), (17, 1), (23, 1), (27, 1), (39, 1), (50, 1), (61, 1)] }, { coefficient := 2, powers := [(2, 1), (18, 1), (19, 1), (44, 1), (53, 1), (60, 1)] }, { coefficient := -2, powers := [(2, 1), (18, 1), (23, 1), (39, 1), (43, 1), (50, 1), (56, 1)] }, { coefficient := -2, powers := [(2, 1), (18, 1), (23, 1), (39, 1), (43, 1), (55, 1), (56, 1)] }, { coefficient := -2, powers := [(2, 1), (19, 1), (23, 1), (41, 1), (50, 1), (53, 1), (60, 1)] }, { coefficient := -2, powers := [(2, 1), (23, 2), (46, 1), (50, 1), (53, 1), (60, 1)] }, { coefficient := 2, powers := [(2, 1), (23, 1), (24, 1), (46, 1), (51, 1), (60, 1)] }, { coefficient := -2, powers := [(2, 1), (23, 1), (39, 1), (43, 1), (56, 1)] }, { coefficient := 2, powers := [(2, 1), (23, 1), (39, 1), (50, 1), (56, 1)] }, { coefficient := -2, powers := [(2, 1), (23, 1), (46, 1), (50, 1), (53, 1)] }, { coefficient := 2, powers := [(2, 1), (36, 1), (59, 1)] }, { coefficient := -4, powers := [(3, 1), (4, 1), (5, 1), (30, 1), (32, 1), (50, 1), (56, 1), (58, 1)] }, { coefficient := -4, powers := [(3, 1), (5, 1), (7, 1), (29, 1), (30, 1), (43, 1), (56, 1), (58, 1)] }, { coefficient := -4, powers := [(3, 1), (5, 1), (14, 1), (21, 1), (30, 1), (50, 1), (56, 1), (58, 1)] }, { coefficient := 4, powers := [(3, 1), (5, 1), (14, 1), (26, 1), (30, 1), (50, 1), (56, 1), (58, 1)] }, { coefficient := -2, powers := [(5, 1), (18, 1), (30, 1), (34, 1), (55, 1), (56, 1), (58, 1)] }, { coefficient := -4, powers := [(5, 1), (18, 1), (30, 1), (50, 1), (56, 1)] }, { coefficient := -2, powers := [(5, 1), (18, 1), (30, 1), (55, 1), (56, 1)] }, { coefficient := -2, powers := [(5, 1), (18, 1), (33, 1), (43, 1), (53, 1)] }, { coefficient := -2, powers := [(5, 1), (27, 1), (34, 1), (58, 1), (59, 1)] }, { coefficient := -2, powers := [(5, 1), (27, 1), (59, 1)] }, { coefficient := -6, powers := [(5, 1), (30, 1), (34, 1), (56, 1), (58, 1)] }, { coefficient := -6, powers := [(5, 1), (30, 1), (56, 1)] }, { coefficient := -2, powers := [(8, 1), (22, 1), (34, 1), (58, 1), (59, 1)] }, { coefficient := -2, powers := [(8, 1), (22, 1), (59, 1)] }, { coefficient := 2, powers := [(8, 1), (23, 1), (30, 1), (34, 1), (46, 1), (50, 1), (58, 1)] }, { coefficient := -2, powers := [(8, 1), (23, 1), (30, 1), (46, 1), (50, 1)] }, { coefficient := 2, powers := [(8, 1), (23, 1), (33, 1), (39, 1), (43, 1)] }, { coefficient := -2, powers := [(12, 1), (18, 1), (22, 1), (43, 1), (56, 1)] }, { coefficient := 2, powers := [(12, 1), (22, 1), (23, 1), (50, 1), (56, 1)] }, { coefficient := -2, powers := [(16, 1), (18, 1), (22, 1), (51, 1), (56, 1)] }, { coefficient := -2, powers := [(16, 1), (22, 1), (23, 1), (51, 1), (56, 1)] }, { coefficient := -2, powers := [(17, 1), (18, 1), (22, 1), (43, 1), (53, 1)] }, { coefficient := 2, powers := [(17, 1), (22, 1), (24, 1), (51, 1)] }, { coefficient := 2, powers := [(17, 1), (23, 1), (27, 1), (39, 1), (43, 1)] }]
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
    ¬ ∀ index : Fin 54,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((2 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (2 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (2 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component62.SelectedLeafB5.selectedHasNoCommonZero

end Krenn.Component62.SelectedLeafB5
