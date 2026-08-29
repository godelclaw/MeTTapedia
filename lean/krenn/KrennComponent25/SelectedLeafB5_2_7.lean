import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component25.SelectedLeafB5_2_7

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "d5e2f0343006f769e567927bcf12ab4ac0e89d9d686139ba79966cd1af564042"
def certificateSHA256 : String := "ff8f533845cb46dcae71dbb332841c4b774a8d98f307f5bd3a699d6e01f00ecf"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 44 → Fin 665 := ![
  2,
  15,
  16,
  17,
  21,
  22,
  23,
  142,
  162,
  167,
  168,
  171,
  251,
  294,
  300,
  307,
  312,
  314,
  319,
  361,
  388,
  411,
  424,
  438,
  440,
  450,
  459,
  460,
  475,
  501,
  535,
  600,
  601,
  613,
  630,
  653,
  655,
  656,
  658,
  659,
  661,
  662,
  663,
  664
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 44 → SparsePoly (Fin 67) := ![
  [{ coefficient := 1, powers := [(9, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(30, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(33, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (54, 1)] }, { coefficient := 1, powers := [(18, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (18, 1)] }, { coefficient := 1, powers := [(16, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (46, 1)] }, { coefficient := -1, powers := [(28, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (54, 1)] }, { coefficient := 1, powers := [(29, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (53, 1)] }, { coefficient := -1, powers := [(28, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (22, 1), (53, 1)] }, { coefficient := 1, powers := [(28, 1), (42, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (50, 1)] }, { coefficient := 1, powers := [(18, 1), (50, 1)] }, { coefficient := 1, powers := [(24, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (60, 1)] }, { coefficient := 1, powers := [(12, 1), (57, 1)] }, { coefficient := 1, powers := [(17, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (22, 1)] }, { coefficient := 1, powers := [(22, 1), (55, 1)] }, { coefficient := 1, powers := [(27, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (57, 1)] }, { coefficient := 1, powers := [(29, 1), (48, 1)] }, { coefficient := 1, powers := [(35, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (38, 1), (58, 1)] }, { coefficient := 1, powers := [(9, 1), (33, 1), (38, 1)] }, { coefficient := 1, powers := [(13, 1), (30, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1), (50, 1)] }, { coefficient := 1, powers := [(24, 1), (45, 1), (50, 1)] }, { coefficient := 1, powers := [(50, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (32, 1), (45, 1)] }, { coefficient := 1, powers := [(27, 1), (45, 1), (50, 1)] }, { coefficient := 1, powers := [(28, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (18, 1), (56, 1)] }, { coefficient := 1, powers := [(12, 1)] }, { coefficient := 1, powers := [(16, 1), (18, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(28, 1), (43, 1), (54, 1)] }, { coefficient := 1, powers := [(28, 1), (50, 1), (57, 1)] }, { coefficient := 1, powers := [(29, 1), (46, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (53, 1)] }, { coefficient := 1, powers := [(18, 1), (50, 1), (56, 1)] }, { coefficient := 1, powers := [(18, 1), (53, 1)] }, { coefficient := 1, powers := [(50, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (59, 1)] }, { coefficient := 1, powers := [(16, 1), (19, 1), (52, 1)] }, { coefficient := 1, powers := [(16, 1), (19, 1), (56, 1)] }, { coefficient := 1, powers := [(16, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (32, 1)] }, { coefficient := 1, powers := [(22, 1), (50, 1)] }, { coefficient := 1, powers := [(27, 1), (50, 1)] }, { coefficient := 1, powers := [(32, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (54, 1)] }, { coefficient := 1, powers := [(29, 1), (41, 1)] }, { coefficient := 1, powers := [(29, 1), (47, 1), (50, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1), (53, 1)] }, { coefficient := 1, powers := [(13, 1), (53, 1)] }, { coefficient := 1, powers := [(33, 1), (37, 1), (50, 1)] }, { coefficient := 1, powers := [(44, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1), (49, 1)] }, { coefficient := 1, powers := [(6, 1), (30, 1), (45, 1)] }, { coefficient := 1, powers := [(9, 1), (24, 1), (45, 1)] }, { coefficient := 1, powers := [(49, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (36, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (32, 1), (56, 1)] }, { coefficient := 1, powers := [(22, 1), (50, 1), (56, 1)] }, { coefficient := 1, powers := [(22, 1), (53, 1)] }, { coefficient := 1, powers := [(28, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (32, 1), (44, 1)] }, { coefficient := 1, powers := [(13, 1), (28, 1), (50, 1)] }, { coefficient := 1, powers := [(27, 1), (44, 1), (50, 1)] }, { coefficient := 1, powers := [(28, 1), (50, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1)] }, { coefficient := 1, powers := [(3, 1), (33, 1)] }, { coefficient := 1, powers := [(13, 1), (18, 1)] }, { coefficient := 1, powers := [(18, 1), (55, 1)] }, { coefficient := 1, powers := [(24, 1), (42, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (49, 1)] }, { coefficient := 1, powers := [(6, 1), (30, 1)] }, { coefficient := 1, powers := [(9, 1), (24, 1)] }, { coefficient := 1, powers := [(18, 1), (49, 1)] }, { coefficient := 1, powers := [(24, 1), (39, 1)] }, { coefficient := 1, powers := [(30, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1), (49, 1)] }, { coefficient := 1, powers := [(6, 1), (30, 1), (44, 1)] }, { coefficient := 1, powers := [(6, 1), (58, 1)] }, { coefficient := 1, powers := [(9, 1), (24, 1), (44, 1)] }, { coefficient := 1, powers := [(9, 1), (55, 1)] }, { coefficient := 1, powers := [(13, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (32, 1), (55, 1)] }, { coefficient := 1, powers := [(6, 1), (32, 1), (42, 1)] }, { coefficient := 1, powers := [(13, 1), (22, 1), (50, 1)] }, { coefficient := 1, powers := [(13, 1), (32, 1), (36, 1)] }, { coefficient := 1, powers := [(22, 1), (50, 1), (55, 1)] }, { coefficient := 1, powers := [(27, 1), (42, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (36, 1), (58, 1)] }, { coefficient := 1, powers := [(0, 1), (39, 1), (55, 1)] }, { coefficient := 1, powers := [(0, 1), (42, 1), (49, 1)] }, { coefficient := 1, powers := [(3, 1), (24, 1), (58, 1)] }, { coefficient := 1, powers := [(3, 1), (30, 1), (55, 1)] }, { coefficient := 1, powers := [(3, 1), (33, 1), (49, 1)] }, { coefficient := 1, powers := [(6, 1), (18, 1), (58, 1)] }, { coefficient := 1, powers := [(6, 1), (30, 1), (42, 1)] }, { coefficient := 1, powers := [(6, 1), (33, 1), (39, 1)] }, { coefficient := 1, powers := [(9, 1), (18, 1), (55, 1)] }, { coefficient := 1, powers := [(9, 1), (24, 1), (42, 1)] }, { coefficient := 1, powers := [(9, 1), (33, 1), (36, 1)] }, { coefficient := 1, powers := [(13, 1), (18, 1), (49, 1)] }, { coefficient := 1, powers := [(13, 1), (24, 1), (39, 1)] }, { coefficient := 1, powers := [(13, 1), (30, 1), (36, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (41, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (48, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (23, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (48, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(12, 1), (23, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1), (29, 1), (48, 1)] }, { coefficient := 1, powers := [(12, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(17, 1), (23, 1), (54, 1)] }, { coefficient := 1, powers := [(17, 1), (29, 1), (41, 1)] }, { coefficient := 1, powers := [(17, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (61, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(39, 1)] }],
  [{ coefficient := 1, powers := [(41, 1)] }],
  [{ coefficient := 1, powers := [(55, 1), (64, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(56, 1), (65, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(57, 1), (66, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 44 → SparsePoly (Fin 67) := ![
  [{ coefficient := 1, powers := [(0, 1), (8, 1), (32, 1), (48, 1), (55, 1), (66, 1)] }, { coefficient := 1, powers := [(2, 1), (33, 1), (36, 1), (38, 1), (60, 1), (66, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (33, 1), (36, 1), (48, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (22, 1), (29, 1), (60, 1), (62, 1), (66, 1)] }, { coefficient := -1, powers := [(5, 1), (22, 1), (32, 1), (57, 1), (62, 1), (66, 1)] }, { coefficient := -1, powers := [(5, 1), (27, 1), (29, 1), (60, 1), (62, 1), (66, 1)] }, { coefficient := -1, powers := [(5, 1), (27, 1), (32, 1), (57, 1), (62, 1), (66, 1)] }, { coefficient := -1, powers := [(23, 1), (24, 1), (53, 1), (57, 1), (66, 1)] }, { coefficient := 1, powers := [(29, 1), (36, 1), (47, 1), (60, 1), (66, 1)] }, { coefficient := 1, powers := [(32, 1), (36, 1), (47, 1), (57, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (2, 1), (38, 1), (42, 1), (45, 1), (49, 1), (60, 1), (66, 1)] }, { coefficient := -1, powers := [(0, 1), (8, 1), (13, 1), (22, 1), (30, 1), (45, 2), (48, 1), (50, 1), (66, 1)] }, { coefficient := 1, powers := [(0, 1), (8, 1), (13, 1), (32, 1), (45, 1), (48, 1), (49, 1), (66, 1)] }, { coefficient := 1, powers := [(0, 1), (8, 1), (22, 1), (30, 1), (42, 1), (45, 2), (48, 1), (50, 1), (66, 1)] }, { coefficient := 1, powers := [(0, 1), (8, 1), (22, 1), (30, 1), (44, 1), (45, 1), (48, 1), (50, 1), (66, 1)] }, { coefficient := -1, powers := [(0, 1), (8, 1), (22, 1), (45, 1), (48, 1), (50, 1), (58, 1), (66, 1)] }, { coefficient := 1, powers := [(0, 1), (8, 1), (27, 1), (30, 1), (33, 1), (37, 1), (45, 1), (48, 1), (50, 1), (66, 1)] }, { coefficient := -1, powers := [(0, 1), (8, 1), (27, 1), (30, 1), (44, 1), (48, 1), (50, 1), (56, 1), (66, 1)] }, { coefficient := -1, powers := [(0, 1), (8, 1), (27, 1), (30, 1), (44, 1), (48, 1), (53, 1), (66, 1)] }, { coefficient := -1, powers := [(0, 1), (8, 1), (27, 1), (45, 1), (48, 1), (50, 1), (58, 1), (66, 1)] }, { coefficient := -1, powers := [(0, 1), (8, 1), (32, 1), (42, 1), (45, 1), (48, 1), (49, 1), (66, 1)] }, { coefficient := -1, powers := [(0, 1), (8, 1), (32, 1), (44, 1), (48, 1), (49, 1), (66, 1)] }, { coefficient := 1, powers := [(2, 1), (6, 1), (38, 1), (58, 1), (60, 1), (66, 1)] }, { coefficient := 1, powers := [(2, 1), (9, 1), (38, 1), (55, 1), (60, 1), (66, 1)] }, { coefficient := -1, powers := [(2, 1), (24, 1), (38, 1), (42, 1), (45, 1), (49, 1), (60, 1), (66, 1)] }, { coefficient := -1, powers := [(2, 1), (38, 1), (42, 1), (49, 1), (60, 1), (66, 1)] }, { coefficient := -1, powers := [(2, 1), (38, 1), (49, 1), (55, 1), (60, 1), (66, 1)] }, { coefficient := -1, powers := [(2, 1), (48, 1), (54, 1), (61, 1), (66, 1)] }, { coefficient := -1, powers := [(5, 1), (35, 1), (54, 1), (61, 1), (66, 1)] }, { coefficient := 1, powers := [(6, 1), (8, 1), (32, 1), (48, 1), (58, 1), (66, 1)] }, { coefficient := 1, powers := [(8, 1), (9, 1), (32, 1), (48, 1), (55, 1), (66, 1)] }, { coefficient := 1, powers := [(8, 1), (22, 1), (24, 1), (30, 1), (42, 1), (45, 2), (48, 1), (50, 1), (66, 1)] }, { coefficient := -1, powers := [(8, 1), (22, 1), (24, 1), (45, 1), (48, 1), (50, 1), (58, 1), (66, 1)] }, { coefficient := 1, powers := [(8, 1), (22, 1), (30, 1), (33, 1), (36, 1), (45, 2), (48, 1), (50, 1), (66, 1)] }, { coefficient := 1, powers := [(8, 1), (22, 1), (30, 1), (42, 1), (45, 1), (48, 1), (50, 1), (66, 1)] }, { coefficient := -1, powers := [(8, 1), (24, 1), (32, 1), (42, 1), (45, 1), (48, 1), (49, 1), (66, 1)] }, { coefficient := 1, powers := [(8, 1), (27, 1), (30, 1), (42, 1), (45, 1), (48, 1), (50, 1), (66, 1)] }, { coefficient := -1, powers := [(8, 1), (32, 1), (33, 1), (36, 1), (45, 1), (48, 1), (49, 1), (66, 1)] }, { coefficient := -1, powers := [(8, 1), (32, 1), (42, 1), (48, 1), (49, 1), (66, 1)] }, { coefficient := -1, powers := [(8, 1), (32, 1), (48, 1), (49, 1), (55, 1), (66, 1)] }, { coefficient := 1, powers := [(12, 1), (23, 1), (56, 1), (57, 1), (66, 1)] }, { coefficient := 1, powers := [(17, 1), (23, 1), (54, 1), (61, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (29, 1), (36, 1), (52, 1), (60, 1), (66, 1)] }, { coefficient := 1, powers := [(16, 1), (29, 1), (36, 1), (56, 1), (60, 1), (66, 1)] }, { coefficient := 1, powers := [(16, 1), (32, 1), (36, 1), (52, 1), (57, 1), (66, 1)] }, { coefficient := 1, powers := [(16, 1), (32, 1), (36, 1), (56, 1), (57, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(17, 1), (50, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (2, 1), (36, 1), (42, 1), (45, 1), (60, 1)] }, { coefficient := -1, powers := [(2, 1), (3, 1), (13, 1), (24, 1), (60, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (3, 1), (55, 1), (60, 1)] }, { coefficient := -1, powers := [(2, 1), (24, 1), (36, 1), (42, 1), (45, 1), (60, 1)] }, { coefficient := -1, powers := [(2, 1), (36, 1), (42, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (3, 1), (9, 1), (24, 1), (60, 1), (61, 1)] }, { coefficient := -1, powers := [(2, 1), (9, 1), (36, 1), (60, 1)] }, { coefficient := -1, powers := [(2, 1), (36, 1), (49, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (48, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (61, 1)] }, { coefficient := -1, powers := [(17, 1), (23, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (53, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (8, 1), (13, 1), (30, 1), (48, 1), (54, 1), (66, 1)] }, { coefficient := -1, powers := [(0, 1), (8, 1), (30, 1), (42, 1), (48, 1), (54, 1), (66, 1)] }, { coefficient := -1, powers := [(0, 1), (8, 1), (30, 1), (48, 1), (54, 1), (55, 1), (66, 1)] }, { coefficient := -1, powers := [(8, 1), (24, 1), (30, 1), (42, 1), (48, 1), (54, 1), (66, 1)] }, { coefficient := -1, powers := [(8, 1), (24, 1), (48, 1), (54, 1), (58, 1), (65, 1), (66, 1)] }, { coefficient := -1, powers := [(8, 1), (30, 1), (33, 1), (36, 1), (48, 1), (54, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (8, 1), (13, 1), (30, 1), (46, 1), (48, 1), (66, 1)] }, { coefficient := 1, powers := [(0, 1), (8, 1), (30, 1), (42, 1), (46, 1), (48, 1), (66, 1)] }, { coefficient := 1, powers := [(0, 1), (8, 1), (30, 1), (46, 1), (48, 1), (55, 1), (66, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (30, 1), (42, 1), (46, 1), (48, 1), (66, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (46, 1), (48, 1), (58, 1), (65, 1), (66, 1)] }, { coefficient := 1, powers := [(8, 1), (30, 1), (33, 1), (36, 1), (46, 1), (48, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (8, 1), (13, 1), (30, 1), (48, 1), (57, 1), (66, 1)] }, { coefficient := -1, powers := [(0, 1), (8, 1), (30, 1), (42, 1), (48, 1), (57, 1), (66, 1)] }, { coefficient := 1, powers := [(0, 1), (8, 1), (30, 1), (42, 1), (48, 1)] }, { coefficient := -1, powers := [(0, 1), (8, 1), (30, 1), (48, 1), (55, 1), (57, 1), (66, 1)] }, { coefficient := 1, powers := [(0, 1), (8, 1), (30, 1), (48, 1), (55, 1)] }, { coefficient := -1, powers := [(8, 1), (24, 1), (30, 1), (42, 1), (48, 1), (57, 1), (66, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (30, 1), (42, 1), (48, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (42, 1), (48, 1), (58, 1), (64, 1), (65, 1)] }, { coefficient := -1, powers := [(8, 1), (24, 1), (48, 1), (57, 1), (58, 1), (65, 1), (66, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (48, 1), (58, 1), (65, 1)] }, { coefficient := -1, powers := [(8, 1), (30, 1), (33, 1), (36, 1), (48, 1), (57, 1), (66, 1)] }, { coefficient := 1, powers := [(8, 1), (30, 1), (33, 1), (36, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (24, 1), (48, 1), (58, 1), (64, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (8, 1), (13, 1), (22, 1), (30, 1), (45, 2), (48, 1)] }, { coefficient := -1, powers := [(0, 1), (8, 1), (22, 1), (30, 1), (42, 1), (45, 2), (48, 1)] }, { coefficient := -1, powers := [(0, 1), (8, 1), (22, 1), (30, 1), (44, 1), (45, 1), (48, 1)] }, { coefficient := 1, powers := [(0, 1), (8, 1), (22, 1), (45, 1), (48, 1), (58, 1)] }, { coefficient := -1, powers := [(0, 1), (8, 1), (27, 1), (30, 1), (33, 1), (37, 1), (45, 1), (48, 1)] }, { coefficient := 1, powers := [(0, 1), (8, 1), (27, 1), (45, 1), (48, 1), (58, 1)] }, { coefficient := -1, powers := [(8, 1), (22, 1), (24, 1), (30, 1), (42, 1), (45, 2), (48, 1)] }, { coefficient := 1, powers := [(8, 1), (22, 1), (24, 1), (45, 1), (48, 1), (58, 1)] }, { coefficient := -1, powers := [(8, 1), (22, 1), (30, 1), (33, 1), (36, 1), (45, 2), (48, 1)] }, { coefficient := -1, powers := [(8, 1), (22, 1), (30, 1), (42, 1), (45, 1), (48, 1)] }, { coefficient := -1, powers := [(8, 1), (27, 1), (30, 1), (42, 1), (45, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(23, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (24, 1), (48, 1), (53, 1), (58, 1), (64, 1), (65, 1)] }, { coefficient := -1, powers := [(8, 1), (30, 1), (48, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(12, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (3, 1), (24, 1), (60, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (36, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (8, 1), (13, 1), (22, 1), (30, 1), (45, 1), (48, 1)] }, { coefficient := 1, powers := [(0, 1), (8, 1), (22, 1), (30, 1), (42, 1), (45, 1), (48, 1)] }, { coefficient := 1, powers := [(0, 1), (8, 1), (22, 1), (30, 1), (44, 1), (48, 1)] }, { coefficient := -1, powers := [(0, 1), (8, 1), (22, 1), (48, 1), (58, 1)] }, { coefficient := 1, powers := [(0, 1), (8, 1), (27, 1), (30, 1), (33, 1), (37, 1), (48, 1)] }, { coefficient := -1, powers := [(0, 1), (8, 1), (27, 1), (48, 1), (58, 1)] }, { coefficient := 1, powers := [(8, 1), (22, 1), (24, 1), (30, 1), (42, 1), (45, 1), (48, 1)] }, { coefficient := -1, powers := [(8, 1), (22, 1), (24, 1), (48, 1), (58, 1)] }, { coefficient := 1, powers := [(8, 1), (22, 1), (30, 1), (33, 1), (36, 1), (45, 1), (48, 1)] }, { coefficient := 1, powers := [(8, 1), (22, 1), (30, 1), (42, 1), (48, 1)] }, { coefficient := 1, powers := [(8, 1), (27, 1), (30, 1), (42, 1), (48, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (8, 1), (13, 1), (30, 1), (48, 1)] }, { coefficient := 1, powers := [(0, 1), (8, 1), (30, 1), (42, 1), (48, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (30, 1), (42, 1), (48, 1)] }, { coefficient := 1, powers := [(8, 1), (30, 1), (33, 1), (36, 1), (48, 1)] }],
  [{ coefficient := -1, powers := [(23, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (8, 1), (13, 1), (30, 1), (48, 1), (66, 1)] }, { coefficient := -1, powers := [(0, 1), (8, 1), (30, 1), (42, 1), (48, 1), (66, 1)] }, { coefficient := -1, powers := [(0, 1), (8, 1), (30, 1), (48, 1), (55, 1), (66, 1)] }, { coefficient := -1, powers := [(8, 1), (24, 1), (30, 1), (42, 1), (48, 1), (66, 1)] }, { coefficient := -1, powers := [(8, 1), (24, 1), (48, 1), (58, 1), (65, 1), (66, 1)] }, { coefficient := -1, powers := [(8, 1), (30, 1), (33, 1), (36, 1), (48, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (8, 1), (27, 1), (30, 1), (44, 1), (48, 1)] }],
  [{ coefficient := -1, powers := [(29, 1), (36, 1), (60, 1)] }, { coefficient := -1, powers := [(32, 1), (36, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (8, 1), (13, 1), (30, 1), (45, 1), (48, 1)] }, { coefficient := -1, powers := [(0, 1), (8, 1), (30, 1), (42, 1), (45, 1), (48, 1)] }, { coefficient := -1, powers := [(0, 1), (8, 1), (30, 1), (44, 1), (48, 1)] }, { coefficient := 1, powers := [(0, 1), (8, 1), (48, 1), (58, 1)] }, { coefficient := -1, powers := [(8, 1), (24, 1), (30, 1), (42, 1), (45, 1), (48, 1)] }, { coefficient := -1, powers := [(8, 1), (30, 1), (33, 1), (36, 1), (45, 1), (48, 1)] }, { coefficient := -1, powers := [(8, 1), (30, 1), (42, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(17, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (8, 1), (27, 1), (30, 1), (48, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (2, 1), (38, 1), (42, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (8, 1), (13, 1), (32, 1), (48, 1)] }, { coefficient := -1, powers := [(0, 1), (8, 1), (32, 1), (42, 1), (48, 1)] }, { coefficient := -1, powers := [(2, 1), (24, 1), (38, 1), (42, 1), (60, 1)] }, { coefficient := -1, powers := [(8, 1), (24, 1), (32, 1), (42, 1), (48, 1)] }, { coefficient := -1, powers := [(8, 1), (32, 1), (33, 1), (36, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (29, 1), (60, 1), (62, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (57, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (24, 1), (48, 1), (58, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (8, 1), (30, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (49, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (48, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (2, 1), (38, 1), (42, 1), (45, 1), (60, 1)] }, { coefficient := -1, powers := [(0, 1), (8, 1), (13, 1), (32, 1), (45, 1), (48, 1)] }, { coefficient := 1, powers := [(0, 1), (8, 1), (32, 1), (42, 1), (45, 1), (48, 1)] }, { coefficient := 1, powers := [(0, 1), (8, 1), (32, 1), (44, 1), (48, 1)] }, { coefficient := 1, powers := [(2, 1), (24, 1), (38, 1), (42, 1), (45, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (38, 1), (42, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (32, 1), (42, 1), (45, 1), (48, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (33, 1), (36, 1), (45, 1), (48, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (42, 1), (48, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (8, 1), (32, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (30, 1), (48, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (38, 1), (60, 1)] }, { coefficient := -1, powers := [(8, 1), (32, 1), (48, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(2, 1), (3, 1), (24, 1), (38, 1), (58, 1), (60, 1)] }, { coefficient := -1, powers := [(2, 1), (48, 1), (54, 1)] }, { coefficient := -1, powers := [(5, 1), (35, 1), (54, 1)] }, { coefficient := 1, powers := [(17, 1), (23, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (29, 1), (36, 1), (59, 1), (60, 1)] }, { coefficient := -1, powers := [(5, 1), (29, 1), (60, 1)] }, { coefficient := -1, powers := [(5, 1), (32, 1), (36, 1), (57, 1), (59, 1)] }, { coefficient := -1, powers := [(5, 1), (32, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (2, 1), (24, 1), (38, 1), (42, 1), (45, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (2, 1), (38, 1), (55, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (8, 1), (13, 1), (24, 1), (32, 1), (45, 1), (48, 1)] }, { coefficient := -1, powers := [(0, 1), (8, 1), (24, 1), (32, 1), (42, 1), (45, 1), (48, 1)] }, { coefficient := -1, powers := [(0, 1), (8, 1), (24, 1), (32, 1), (44, 1), (48, 1)] }, { coefficient := 1, powers := [(0, 1), (8, 1), (32, 1), (48, 1), (55, 1)] }, { coefficient := 1, powers := [(2, 1), (6, 1), (33, 1), (38, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (13, 1), (24, 1), (38, 1), (60, 1)] }, { coefficient := -1, powers := [(2, 1), (24, 2), (38, 1), (42, 1), (45, 1), (60, 1)] }, { coefficient := -1, powers := [(2, 1), (24, 1), (38, 1), (42, 1), (60, 1)] }, { coefficient := 1, powers := [(6, 1), (8, 1), (32, 1), (33, 1), (48, 1)] }, { coefficient := 1, powers := [(8, 1), (13, 1), (24, 1), (32, 1), (48, 1)] }, { coefficient := -1, powers := [(8, 1), (24, 2), (32, 1), (42, 1), (45, 1), (48, 1)] }, { coefficient := -1, powers := [(8, 1), (24, 1), (32, 1), (33, 1), (36, 1), (45, 1), (48, 1)] }, { coefficient := -1, powers := [(8, 1), (24, 1), (32, 1), (42, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (57, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (22, 1), (24, 1), (48, 1), (53, 1), (58, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (8, 1), (24, 1), (32, 1), (48, 1), (58, 1)] }, { coefficient := -1, powers := [(8, 1), (22, 1), (24, 1), (48, 1), (50, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (2, 1), (18, 1), (38, 1), (42, 1), (45, 1), (49, 1), (60, 1)] }, { coefficient := -1, powers := [(0, 1), (8, 1), (9, 1), (32, 1), (48, 1), (55, 1)] }, { coefficient := 1, powers := [(0, 1), (8, 1), (13, 1), (18, 1), (22, 1), (30, 1), (45, 2), (48, 1), (50, 1)] }, { coefficient := -1, powers := [(0, 1), (8, 1), (13, 1), (18, 1), (32, 1), (45, 1), (48, 1), (49, 1)] }, { coefficient := -1, powers := [(0, 1), (8, 1), (13, 1), (27, 1), (30, 1), (48, 1), (53, 1)] }, { coefficient := -1, powers := [(0, 1), (8, 1), (18, 1), (22, 1), (30, 1), (42, 1), (45, 2), (48, 1), (50, 1)] }, { coefficient := -1, powers := [(0, 1), (8, 1), (18, 1), (22, 1), (30, 1), (44, 1), (45, 1), (48, 1), (50, 1)] }, { coefficient := 1, powers := [(0, 1), (8, 1), (18, 1), (22, 1), (45, 1), (48, 1), (50, 1), (58, 1)] }, { coefficient := -1, powers := [(0, 1), (8, 1), (18, 1), (27, 1), (30, 1), (33, 1), (37, 1), (45, 1), (48, 1), (50, 1)] }, { coefficient := 1, powers := [(0, 1), (8, 1), (18, 1), (27, 1), (30, 1), (44, 1), (48, 1), (50, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (8, 1), (18, 1), (27, 1), (30, 1), (44, 1), (48, 1), (53, 1)] }, { coefficient := 1, powers := [(0, 1), (8, 1), (18, 1), (27, 1), (45, 1), (48, 1), (50, 1), (58, 1)] }, { coefficient := 1, powers := [(0, 1), (8, 1), (18, 1), (32, 1), (42, 1), (45, 1), (48, 1), (49, 1)] }, { coefficient := 1, powers := [(0, 1), (8, 1), (18, 1), (32, 1), (44, 1), (48, 1), (49, 1)] }, { coefficient := 1, powers := [(0, 1), (8, 1), (27, 1), (30, 1), (42, 1), (48, 1), (53, 1)] }, { coefficient := 1, powers := [(0, 1), (8, 1), (27, 1), (30, 1), (48, 1), (53, 1), (55, 1)] }, { coefficient := -1, powers := [(2, 1), (6, 1), (18, 1), (38, 1), (58, 1), (60, 1)] }, { coefficient := -1, powers := [(2, 1), (9, 1), (18, 1), (38, 1), (55, 1), (60, 1)] }, { coefficient := -1, powers := [(2, 1), (9, 1), (33, 1), (36, 1), (38, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (18, 1), (24, 1), (38, 1), (42, 1), (45, 1), (49, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (18, 1), (38, 1), (42, 1), (49, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (18, 1), (38, 1), (49, 1), (55, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (18, 1), (48, 1), (54, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (16, 1), (22, 1), (29, 1), (60, 1), (62, 1)] }, { coefficient := 1, powers := [(5, 1), (16, 1), (22, 1), (32, 1), (57, 1), (62, 1)] }, { coefficient := 1, powers := [(5, 1), (16, 1), (27, 1), (29, 1), (60, 1), (62, 1)] }, { coefficient := 1, powers := [(5, 1), (16, 1), (27, 1), (32, 1), (57, 1), (62, 1)] }, { coefficient := 1, powers := [(5, 1), (18, 1), (35, 1), (54, 1), (61, 1)] }, { coefficient := -1, powers := [(6, 1), (8, 1), (18, 1), (32, 1), (48, 1), (58, 1)] }, { coefficient := -1, powers := [(8, 1), (9, 1), (18, 1), (32, 1), (48, 1), (55, 1)] }, { coefficient := -1, powers := [(8, 1), (9, 1), (32, 1), (33, 1), (36, 1), (48, 1)] }, { coefficient := -1, powers := [(8, 1), (18, 1), (22, 1), (24, 1), (30, 1), (42, 1), (45, 2), (48, 1), (50, 1)] }, { coefficient := 1, powers := [(8, 1), (18, 1), (22, 1), (24, 1), (45, 1), (48, 1), (50, 1), (58, 1)] }, { coefficient := -1, powers := [(8, 1), (18, 1), (22, 1), (30, 1), (33, 1), (36, 1), (45, 2), (48, 1), (50, 1)] }, { coefficient := -1, powers := [(8, 1), (18, 1), (22, 1), (30, 1), (42, 1), (45, 1), (48, 1), (50, 1)] }, { coefficient := 1, powers := [(8, 1), (18, 1), (24, 1), (32, 1), (42, 1), (45, 1), (48, 1), (49, 1)] }, { coefficient := -1, powers := [(8, 1), (18, 1), (27, 1), (30, 1), (42, 1), (45, 1), (48, 1), (50, 1)] }, { coefficient := 1, powers := [(8, 1), (18, 1), (32, 1), (33, 1), (36, 1), (45, 1), (48, 1), (49, 1)] }, { coefficient := 1, powers := [(8, 1), (18, 1), (32, 1), (42, 1), (48, 1), (49, 1)] }, { coefficient := 1, powers := [(8, 1), (18, 1), (32, 1), (48, 1), (49, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (27, 1), (30, 1), (42, 1), (48, 1), (53, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (27, 1), (48, 1), (53, 1), (58, 1), (65, 1)] }, { coefficient := 1, powers := [(8, 1), (27, 1), (30, 1), (33, 1), (36, 1), (48, 1), (53, 1)] }, { coefficient := -1, powers := [(12, 1), (18, 1), (23, 1), (56, 1), (57, 1)] }, { coefficient := -1, powers := [(16, 1), (19, 1), (29, 1), (36, 1), (52, 1), (60, 1)] }, { coefficient := -1, powers := [(16, 1), (19, 1), (29, 1), (36, 1), (56, 1), (60, 1)] }, { coefficient := -1, powers := [(16, 1), (19, 1), (32, 1), (36, 1), (52, 1), (57, 1)] }, { coefficient := -1, powers := [(16, 1), (19, 1), (32, 1), (36, 1), (56, 1), (57, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1), (24, 1), (53, 1), (57, 1)] }, { coefficient := -1, powers := [(16, 1), (29, 1), (36, 1), (47, 1), (60, 1)] }, { coefficient := -1, powers := [(16, 1), (32, 1), (36, 1), (47, 1), (57, 1)] }, { coefficient := -1, powers := [(17, 1), (18, 1), (23, 1), (54, 1), (61, 1)] }]
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
    ¬ ∀ index : Fin 44,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component25.SelectedLeafB5_2_7.selectedHasNoCommonZero

end Krenn.Component25.SelectedLeafB5_2_7
