import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component62.SelectedLeafB6_3

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "0075faf68d1363f4c822f792a67bf1ca22407d12115d4f0a19ecedbff7ce2bf7"
def certificateSHA256 : String := "042151de03be7949ab30aa67671bf27484806b5295e819092e6ae1f3d4697a1f"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 37 → Fin 664 := ![
  10,
  11,
  12,
  17,
  18,
  21,
  128,
  129,
  130,
  133,
  134,
  135,
  137,
  138,
  160,
  186,
  187,
  191,
  260,
  301,
  302,
  322,
  440,
  443,
  453,
  454,
  557,
  578,
  579,
  588,
  609,
  619,
  657,
  659,
  660,
  662,
  663
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 37 → SparsePoly (Fin 64) := ![
  [{ coefficient := 1, powers := [(10, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (41, 1)] }, { coefficient := 1, powers := [(10, 1), (25, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (44, 1)] }, { coefficient := 1, powers := [(10, 1), (25, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (46, 1)] }, { coefficient := 1, powers := [(10, 1), (25, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (53, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (41, 1)] }, { coefficient := 1, powers := [(16, 1), (33, 1), (34, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (45, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (52, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (33, 1)] }, { coefficient := 1, powers := [(33, 1), (34, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (38, 1)] }, { coefficient := 1, powers := [(27, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (27, 1), (58, 1)] }, { coefficient := 1, powers := [(27, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (33, 1), (52, 1)] }, { coefficient := 1, powers := [(27, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (22, 1), (58, 1)] }, { coefficient := 1, powers := [(22, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (38, 1), (41, 1)] }, { coefficient := 1, powers := [(27, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (46, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (53, 1)] }, { coefficient := 1, powers := [(8, 1), (30, 1)] }, { coefficient := 1, powers := [(12, 1), (27, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (36, 1), (59, 1)] }, { coefficient := 1, powers := [(1, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(1, 1), (46, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (58, 1)] }, { coefficient := 1, powers := [(16, 1), (19, 1), (50, 1)] }, { coefficient := 1, powers := [(16, 1), (19, 1), (55, 1)] }, { coefficient := 1, powers := [(16, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (58, 1)] }, { coefficient := 1, powers := [(16, 1), (24, 1), (38, 1)] }, { coefficient := 1, powers := [(16, 1), (24, 1), (43, 1)] }, { coefficient := 1, powers := [(16, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (38, 1)] }, { coefficient := 1, powers := [(16, 1), (43, 1)] }, { coefficient := 1, powers := [(16, 1), (50, 1)] }, { coefficient := 1, powers := [(16, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (53, 1)] }, { coefficient := 1, powers := [(27, 1), (39, 1)] }, { coefficient := 1, powers := [(27, 1), (45, 1), (48, 1)] }, { coefficient := 1, powers := [(30, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (41, 1), (52, 1)] }, { coefficient := 1, powers := [(22, 1), (56, 1)] }, { coefficient := 1, powers := [(27, 1), (46, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1)] }, { coefficient := 1, powers := [(6, 1), (58, 1)] }, { coefficient := 1, powers := [(23, 1), (38, 1)] }, { coefficient := 1, powers := [(23, 1), (43, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (50, 1)] }, { coefficient := 1, powers := [(3, 1), (58, 1)] }, { coefficient := 1, powers := [(18, 1), (50, 1)] }, { coefficient := 1, powers := [(18, 1), (55, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (38, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1), (44, 1)] }, { coefficient := 1, powers := [(17, 1), (27, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (38, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(24, 1), (38, 1), (41, 1)] }, { coefficient := 1, powers := [(24, 1), (44, 1)] }, { coefficient := 1, powers := [(41, 1), (52, 1)] }, { coefficient := 1, powers := [(56, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (36, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (45, 1), (52, 1)] }, { coefficient := 1, powers := [(5, 1), (27, 1), (58, 1)] }, { coefficient := 1, powers := [(8, 1), (22, 1), (58, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1), (52, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (36, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (46, 1), (53, 1)] }, { coefficient := 1, powers := [(5, 1), (27, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (53, 1)] }, { coefficient := 1, powers := [(8, 1), (22, 1), (59, 1)] }, { coefficient := 1, powers := [(8, 1), (30, 1), (46, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (39, 1)] }, { coefficient := 1, powers := [(12, 1), (22, 1), (56, 1)] }, { coefficient := 1, powers := [(12, 1), (27, 1), (46, 1)] }, { coefficient := 1, powers := [(12, 1), (33, 1), (36, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (53, 1)] }, { coefficient := 1, powers := [(17, 1), (27, 1), (39, 1)] }, { coefficient := 1, powers := [(17, 1), (30, 1), (36, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1), (61, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(38, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(39, 1), (63, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 37 → SparsePoly (Fin 64) := ![
  [{ coefficient := 1, powers := [(5, 2), (25, 1), (27, 1), (30, 1), (52, 1), (59, 1), (61, 1)] }, { coefficient := -1, powers := [(5, 1), (12, 1), (22, 1), (25, 1), (27, 1), (52, 1), (59, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (5, 2), (25, 1), (27, 1), (30, 1), (52, 1), (59, 1), (61, 1)] }, { coefficient := -1, powers := [(0, 1), (5, 1), (12, 1), (22, 1), (25, 1), (27, 1), (52, 1), (59, 1), (61, 1)] }],
  [{ coefficient := -2, powers := [(5, 1), (8, 1), (25, 1), (27, 1), (30, 1), (59, 1), (61, 1)] }, { coefficient := 2, powers := [(5, 1), (12, 1), (25, 1), (27, 2), (59, 1), (61, 1)] }, { coefficient := 2, powers := [(5, 1), (25, 1), (30, 1), (53, 1), (61, 1), (63, 1)] }, { coefficient := 2, powers := [(12, 1), (25, 1), (27, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (8, 1), (20, 1), (22, 1), (33, 1), (59, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (17, 1), (20, 1), (22, 1), (27, 1), (59, 1), (61, 1)] }, { coefficient := -2, powers := [(5, 1), (20, 1), (22, 1), (59, 1), (61, 1), (63, 1)] }, { coefficient := 2, powers := [(17, 1), (20, 1), (22, 1), (61, 1)] }],
  [{ coefficient := 2, powers := [(5, 1), (8, 1), (30, 1), (52, 1), (59, 1)] }, { coefficient := -2, powers := [(5, 1), (12, 1), (27, 1), (52, 1), (59, 1)] }, { coefficient := -2, powers := [(12, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (8, 1), (33, 1), (45, 1), (59, 1)] }, { coefficient := -1, powers := [(5, 1), (17, 1), (27, 1), (45, 1), (59, 1)] }, { coefficient := 2, powers := [(5, 1), (45, 1), (59, 1), (63, 1)] }, { coefficient := -2, powers := [(17, 1), (45, 1)] }],
  [{ coefficient := -1, powers := [(5, 2), (27, 1), (30, 1), (52, 1), (59, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (12, 1), (22, 1), (27, 1), (52, 1), (59, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (5, 2), (27, 1), (30, 1), (52, 1), (59, 1), (61, 1)] }, { coefficient := 1, powers := [(0, 1), (5, 1), (12, 1), (22, 1), (27, 1), (52, 1), (59, 1), (61, 1)] }],
  [{ coefficient := 2, powers := [(5, 1), (8, 1), (27, 1), (30, 1), (59, 1), (61, 1)] }, { coefficient := -2, powers := [(5, 1), (12, 1), (27, 2), (59, 1), (61, 1)] }, { coefficient := -2, powers := [(5, 1), (30, 1), (53, 1), (61, 1), (63, 1)] }, { coefficient := -2, powers := [(12, 1), (27, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (8, 1), (22, 1), (33, 1), (59, 1), (61, 1)] }, { coefficient := -1, powers := [(5, 1), (17, 1), (22, 1), (27, 1), (59, 1), (61, 1)] }, { coefficient := 2, powers := [(5, 1), (22, 1), (59, 1), (61, 1), (63, 1)] }, { coefficient := -2, powers := [(17, 1), (22, 1), (61, 1)] }],
  [{ coefficient := -2, powers := [(24, 1), (38, 1), (39, 1)] }, { coefficient := -2, powers := [(24, 1), (39, 1), (43, 1)] }],
  [{ coefficient := 2, powers := [(3, 1), (5, 1), (27, 1), (52, 1), (59, 2)] }, { coefficient := 1, powers := [(5, 1), (6, 1), (30, 1), (52, 1), (56, 1), (59, 1)] }, { coefficient := 2, powers := [(6, 1), (52, 1), (59, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (39, 1), (44, 1), (50, 1), (62, 1)] }, { coefficient := 2, powers := [(3, 1), (5, 1), (27, 1), (45, 1), (59, 2)] }, { coefficient := 2, powers := [(3, 1), (45, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (6, 1), (30, 1), (45, 1), (56, 1), (59, 1)] }, { coefficient := -1, powers := [(5, 1), (27, 1), (39, 1), (44, 1), (59, 1), (62, 1)] }, { coefficient := -1, powers := [(5, 1), (30, 1), (36, 1), (44, 1), (59, 1), (62, 1)] }, { coefficient := 2, powers := [(18, 1), (39, 1), (44, 1), (50, 1), (62, 1)] }, { coefficient := 2, powers := [(18, 1), (39, 1), (44, 1), (55, 1), (62, 1)] }, { coefficient := -2, powers := [(39, 1), (41, 1)] }],
  [{ coefficient := 2, powers := [(16, 1), (24, 1), (38, 1), (39, 1)] }, { coefficient := 2, powers := [(16, 1), (24, 1), (39, 1), (43, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (5, 2), (30, 1), (56, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (5, 1), (12, 1), (22, 1), (56, 1), (59, 1)] }, { coefficient := -2, powers := [(3, 1), (16, 1), (19, 1), (59, 1)] }, { coefficient := -1, powers := [(5, 2), (23, 1), (30, 1), (56, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (12, 1), (22, 1), (23, 1), (56, 1), (59, 1)] }, { coefficient := 2, powers := [(6, 1), (16, 1), (19, 1), (59, 1)] }],
  [{ coefficient := 2, powers := [(5, 2), (27, 1), (59, 2)] }, { coefficient := 2, powers := [(5, 1), (8, 1), (22, 1), (59, 2)] }, { coefficient := 2, powers := [(5, 1), (59, 1)] }, { coefficient := -2, powers := [(17, 1), (39, 1)] }],
  [{ coefficient := 2, powers := [(16, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (8, 1), (30, 1), (56, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (12, 1), (27, 1), (56, 1), (59, 1)] }, { coefficient := 2, powers := [(8, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(5, 2), (24, 1), (30, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (12, 1), (22, 1), (24, 1), (59, 1)] }],
  [{ coefficient := 2, powers := [(5, 1), (27, 1), (53, 1), (59, 1)] }, { coefficient := 2, powers := [(53, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (22, 1), (56, 1), (59, 1)] }, { coefficient := 2, powers := [(5, 1), (27, 1), (46, 1), (59, 1)] }, { coefficient := 2, powers := [(46, 1)] }],
  [{ coefficient := 2, powers := [(5, 1), (30, 1), (61, 1), (63, 1)] }],
  [{ coefficient := -2, powers := [(3, 1), (27, 1), (59, 1)] }, { coefficient := 2, powers := [(6, 1), (27, 1), (59, 1)] }],
  [{ coefficient := -2, powers := [(3, 1), (33, 1), (39, 1)] }],
  [{ coefficient := 2, powers := [(3, 1), (19, 1), (27, 1), (59, 1)] }, { coefficient := -2, powers := [(6, 1), (19, 1), (27, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (8, 1), (33, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (17, 1), (27, 1), (59, 1)] }, { coefficient := -2, powers := [(5, 1), (59, 1), (63, 1)] }, { coefficient := 2, powers := [(17, 1)] }],
  [{ coefficient := -2, powers := [(5, 1), (8, 1), (30, 1), (59, 1)] }, { coefficient := 2, powers := [(5, 1), (12, 1), (27, 1), (59, 1)] }, { coefficient := 2, powers := [(12, 1)] }],
  [{ coefficient := 1, powers := [(5, 2), (27, 1), (30, 1), (56, 1), (59, 1)] }, { coefficient := -1, powers := [(5, 1), (12, 1), (22, 1), (27, 1), (56, 1), (59, 1)] }],
  [{ coefficient := 2, powers := [(8, 1), (33, 1), (39, 1)] }, { coefficient := 2, powers := [(17, 1), (27, 1), (39, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (39, 1), (50, 1), (62, 1)] }, { coefficient := 1, powers := [(5, 1), (27, 1), (39, 1), (59, 1), (62, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (36, 1), (59, 1), (62, 1)] }, { coefficient := -2, powers := [(18, 1), (39, 1), (50, 1), (62, 1)] }, { coefficient := -2, powers := [(18, 1), (39, 1), (55, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(5, 2), (27, 1), (30, 1), (59, 1)] }, { coefficient := -1, powers := [(5, 1), (12, 1), (22, 1), (27, 1), (59, 1)] }],
  [{ coefficient := -2, powers := [(3, 1), (5, 1), (27, 1), (59, 2)] }, { coefficient := -1, powers := [(5, 1), (6, 1), (30, 1), (56, 1), (59, 1)] }, { coefficient := -2, powers := [(6, 1), (59, 1)] }],
  [{ coefficient := -2, powers := [(5, 1), (27, 1), (59, 1)] }, { coefficient := -2, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (5, 2), (27, 1), (30, 1), (44, 1), (52, 1), (59, 1)] }, { coefficient := -1, powers := [(0, 1), (5, 1), (12, 1), (22, 1), (27, 1), (44, 1), (52, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 2), (27, 1), (30, 1), (41, 1), (52, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (8, 1), (22, 1), (33, 1), (53, 1), (59, 1)] }, { coefficient := -2, powers := [(5, 1), (8, 1), (27, 1), (30, 1), (46, 1), (59, 1)] }, { coefficient := -1, powers := [(5, 1), (12, 1), (22, 1), (27, 1), (41, 1), (52, 1), (59, 1)] }, { coefficient := 2, powers := [(5, 1), (12, 1), (27, 2), (46, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (17, 1), (22, 1), (27, 1), (53, 1), (59, 1)] }, { coefficient := -2, powers := [(5, 1), (22, 1), (53, 1), (59, 1), (63, 1)] }, { coefficient := -2, powers := [(5, 1), (30, 1), (36, 1), (59, 1), (63, 1)] }, { coefficient := -2, powers := [(5, 1), (30, 1), (39, 1), (56, 1), (63, 1)] }, { coefficient := 2, powers := [(12, 1), (27, 1), (46, 1)] }, { coefficient := 2, powers := [(17, 1), (22, 1), (53, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (38, 1), (39, 1), (50, 1), (56, 1), (62, 1)] }, { coefficient := 2, powers := [(3, 1), (5, 1), (27, 1), (36, 1), (58, 1), (59, 2)] }, { coefficient := -2, powers := [(3, 1), (5, 1), (27, 1), (45, 1), (52, 1), (59, 2)] }, { coefficient := -2, powers := [(3, 1), (45, 1), (52, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (6, 1), (30, 1), (36, 1), (56, 1), (58, 1), (59, 1)] }, { coefficient := -1, powers := [(5, 1), (6, 1), (30, 1), (45, 1), (52, 1), (56, 1), (59, 1)] }, { coefficient := -1, powers := [(5, 1), (22, 1), (53, 1), (56, 1), (59, 1)] }, { coefficient := 2, powers := [(5, 1), (27, 1), (36, 1), (59, 2)] }, { coefficient := -1, powers := [(5, 1), (27, 1), (38, 1), (39, 1), (56, 1), (59, 1), (62, 1)] }, { coefficient := 2, powers := [(5, 1), (27, 1), (39, 1), (56, 1), (59, 1)] }, { coefficient := -2, powers := [(5, 1), (27, 1), (46, 1), (53, 1), (59, 1)] }, { coefficient := -1, powers := [(5, 1), (30, 1), (36, 1), (38, 1), (56, 1), (59, 1), (62, 1)] }, { coefficient := 2, powers := [(6, 1), (36, 1), (58, 1), (59, 1)] }, { coefficient := 2, powers := [(18, 1), (38, 1), (39, 1), (50, 1), (56, 1), (62, 1)] }, { coefficient := 2, powers := [(18, 1), (38, 1), (39, 1), (55, 1), (56, 1), (62, 1)] }, { coefficient := 2, powers := [(24, 1), (38, 1), (39, 1), (41, 1)] }, { coefficient := 2, powers := [(24, 1), (39, 1), (41, 1), (43, 1)] }, { coefficient := 2, powers := [(36, 1), (59, 1)] }, { coefficient := 2, powers := [(39, 1), (41, 1), (52, 1)] }, { coefficient := 2, powers := [(39, 1), (56, 1)] }, { coefficient := -2, powers := [(46, 1), (53, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (8, 1), (33, 1), (39, 1), (50, 1)] }, { coefficient := 2, powers := [(0, 1), (17, 1), (27, 1), (39, 1), (50, 1)] }, { coefficient := -1, powers := [(5, 1), (8, 1), (27, 1), (33, 1), (39, 1), (59, 1)] }, { coefficient := -1, powers := [(5, 1), (8, 1), (30, 1), (33, 1), (36, 1), (59, 1)] }, { coefficient := -1, powers := [(5, 1), (17, 1), (27, 2), (39, 1), (59, 1)] }, { coefficient := -1, powers := [(5, 1), (17, 1), (27, 1), (30, 1), (36, 1), (59, 1)] }, { coefficient := 2, powers := [(8, 1), (18, 1), (33, 1), (39, 1), (50, 1)] }, { coefficient := 2, powers := [(8, 1), (18, 1), (33, 1), (39, 1), (55, 1)] }, { coefficient := 2, powers := [(17, 1), (18, 1), (27, 1), (39, 1), (50, 1)] }, { coefficient := 2, powers := [(17, 1), (18, 1), (27, 1), (39, 1), (55, 1)] }],
  [{ coefficient := 2, powers := [(5, 1), (27, 1), (59, 1)] }, { coefficient := -2, powers := [(5, 1), (30, 1), (56, 1)] }]
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
    (values : Fin 64 → R) :
    ¬ ∀ index : Fin 37,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((2 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (2 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (2 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component62.SelectedLeafB6_3.selectedHasNoCommonZero

end Krenn.Component62.SelectedLeafB6_3
