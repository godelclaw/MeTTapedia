import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component60.SelectedLeafB6_1_2

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "3de17f65888b242f32590e428ec4bc27d40d2cea098885e4df052ef7b4e537b7"
def certificateSHA256 : String := "6d8198642afdf796fa61b45276306156219f342f34241caeecb5eac5b565e457"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 60 → Fin 665 := ![
  11,
  12,
  13,
  22,
  25,
  53,
  149,
  150,
  165,
  171,
  172,
  173,
  178,
  179,
  212,
  239,
  292,
  298,
  300,
  301,
  302,
  303,
  308,
  310,
  314,
  383,
  387,
  388,
  404,
  422,
  423,
  432,
  436,
  443,
  444,
  457,
  462,
  466,
  517,
  548,
  556,
  558,
  578,
  587,
  600,
  601,
  612,
  632,
  645,
  653,
  655,
  656,
  657,
  658,
  659,
  660,
  661,
  662,
  663,
  664
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 60 → SparsePoly (Fin 65) := ![
  [{ coefficient := 1, powers := [(11, 1), (29, 1)] }],
  [{ coefficient := 1, powers := [(15, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(15, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (30, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (30, 1)] }, { coefficient := 1, powers := [(18, 1), (26, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (26, 1)] }, { coefficient := 1, powers := [(26, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (26, 1)] }, { coefficient := 1, powers := [(18, 1), (20, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (47, 1)] }, { coefficient := -1, powers := [(18, 1), (21, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (20, 1)] }, { coefficient := 1, powers := [(18, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (43, 1)] }, { coefficient := 1, powers := [(19, 1), (20, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (53, 1)] }, { coefficient := 1, powers := [(29, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (40, 1)] }, { coefficient := 1, powers := [(29, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (26, 1), (47, 1)] }, { coefficient := 1, powers := [(30, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (26, 1), (44, 1)] }, { coefficient := 1, powers := [(17, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1)] }, { coefficient := 1, powers := [(20, 1), (43, 1)] }, { coefficient := 1, powers := [(25, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (49, 1)] }, { coefficient := 1, powers := [(15, 1), (22, 1), (49, 1)] }, { coefficient := 1, powers := [(15, 1), (27, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (54, 1)] }, { coefficient := 1, powers := [(11, 1), (27, 1), (53, 1)] }, { coefficient := 1, powers := [(15, 1), (22, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (48, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1)] }, { coefficient := 1, powers := [(12, 1), (29, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (58, 1)] }, { coefficient := 1, powers := [(9, 1), (42, 1)] }, { coefficient := 1, powers := [(13, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (45, 1)] }, { coefficient := 1, powers := [(12, 1), (56, 1)] }, { coefficient := 1, powers := [(18, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (46, 1)] }, { coefficient := 1, powers := [(19, 1), (40, 1)] }, { coefficient := 1, powers := [(19, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1), (50, 1)] }, { coefficient := 1, powers := [(25, 1), (45, 1), (50, 1)] }, { coefficient := 1, powers := [(50, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (20, 1), (56, 1)] }, { coefficient := 1, powers := [(12, 1)] }, { coefficient := 1, powers := [(18, 1), (20, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (25, 1), (44, 1)] }, { coefficient := 1, powers := [(12, 1), (55, 1)] }, { coefficient := 1, powers := [(17, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (25, 1), (47, 1)] }, { coefficient := 1, powers := [(18, 1), (21, 1), (50, 1)] }, { coefficient := 1, powers := [(18, 1), (25, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (25, 1), (46, 1)] }, { coefficient := 1, powers := [(19, 1), (25, 1), (40, 1)] }, { coefficient := 1, powers := [(19, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1)] }, { coefficient := 1, powers := [(25, 1), (40, 1), (43, 1)] }, { coefficient := 1, powers := [(25, 1), (46, 1)] }, { coefficient := 1, powers := [(43, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1)] }, { coefficient := 1, powers := [(6, 1), (21, 1), (59, 1)] }, { coefficient := 1, powers := [(21, 1)] }, { coefficient := 1, powers := [(25, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (33, 1)] }, { coefficient := 1, powers := [(17, 1), (21, 1)] }, { coefficient := 1, powers := [(18, 1), (21, 1), (25, 1), (44, 1)] }, { coefficient := 1, powers := [(18, 1), (21, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (60, 1)] }, { coefficient := 1, powers := [(12, 1), (26, 1), (46, 1)] }, { coefficient := 1, powers := [(12, 1), (57, 1)] }, { coefficient := 1, powers := [(19, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (54, 1)] }, { coefficient := 1, powers := [(29, 1), (41, 1)] }, { coefficient := 1, powers := [(29, 1), (47, 1), (50, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (21, 1), (44, 1)] }, { coefficient := 1, powers := [(13, 1), (21, 1)] }, { coefficient := 1, powers := [(21, 1), (25, 1), (44, 1)] }, { coefficient := 1, powers := [(21, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1), (53, 1)] }, { coefficient := 1, powers := [(13, 1), (26, 1), (40, 1)] }, { coefficient := 1, powers := [(13, 1), (53, 1)] }, { coefficient := 1, powers := [(26, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1), (50, 1)] }, { coefficient := 1, powers := [(6, 1), (60, 1)] }, { coefficient := 1, powers := [(25, 1), (46, 1), (50, 1)] }, { coefficient := 1, powers := [(43, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1), (50, 1)] }, { coefficient := 1, powers := [(21, 1), (50, 1)] }, { coefficient := 1, powers := [(25, 1), (41, 1)] }, { coefficient := 1, powers := [(25, 1), (47, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (24, 1), (60, 1)] }, { coefficient := 1, powers := [(6, 1), (32, 1), (48, 1)] }, { coefficient := 1, powers := [(6, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(24, 1), (43, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (25, 1), (40, 1)] }, { coefficient := 1, powers := [(17, 1)] }, { coefficient := 1, powers := [(18, 1), (25, 1), (44, 1)] }, { coefficient := 1, powers := [(18, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (43, 1), (53, 1)] }, { coefficient := 1, powers := [(24, 1), (57, 1)] }, { coefficient := 1, powers := [(29, 1), (48, 1)] }, { coefficient := 1, powers := [(35, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (21, 1), (44, 1), (53, 1)] }, { coefficient := 1, powers := [(13, 1), (21, 1), (53, 1)] }, { coefficient := 1, powers := [(21, 1), (26, 1), (44, 1)] }, { coefficient := 1, powers := [(33, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1)] }, { coefficient := 1, powers := [(6, 1), (59, 1)] }, { coefficient := 1, powers := [(25, 1), (40, 1)] }, { coefficient := 1, powers := [(25, 1), (45, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1), (36, 1), (58, 1)] }, { coefficient := 1, powers := [(1, 1), (39, 1), (55, 1)] }, { coefficient := 1, powers := [(1, 1), (42, 1), (49, 1)] }, { coefficient := 1, powers := [(14, 1), (22, 1), (49, 1)] }, { coefficient := 1, powers := [(14, 1), (27, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1)] }, { coefficient := 1, powers := [(3, 1), (33, 1)] }, { coefficient := 1, powers := [(13, 1), (20, 1)] }, { coefficient := 1, powers := [(20, 1), (55, 1)] }, { coefficient := 1, powers := [(25, 1), (42, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (49, 1)] }, { coefficient := 1, powers := [(6, 1), (30, 1)] }, { coefficient := 1, powers := [(9, 1), (25, 1)] }, { coefficient := 1, powers := [(20, 1), (49, 1)] }, { coefficient := 1, powers := [(25, 1), (39, 1)] }, { coefficient := 1, powers := [(30, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1), (49, 1)] }, { coefficient := 1, powers := [(6, 1), (30, 1), (44, 1)] }, { coefficient := 1, powers := [(6, 1), (58, 1)] }, { coefficient := 1, powers := [(9, 1), (25, 1), (44, 1)] }, { coefficient := 1, powers := [(9, 1), (55, 1)] }, { coefficient := 1, powers := [(13, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (33, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (41, 1)] }, { coefficient := 1, powers := [(12, 1), (21, 1), (26, 1), (44, 1)] }, { coefficient := 1, powers := [(12, 1), (33, 1), (38, 1)] }, { coefficient := 1, powers := [(17, 1), (21, 1), (54, 1)] }, { coefficient := 1, powers := [(17, 1), (26, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (40, 1), (55, 1)] }, { coefficient := 1, powers := [(0, 1), (44, 1)] }, { coefficient := 1, powers := [(6, 1), (33, 1), (40, 1)] }, { coefficient := 1, powers := [(13, 1), (25, 1), (40, 1)] }, { coefficient := 1, powers := [(13, 1)] }, { coefficient := 1, powers := [(25, 1), (44, 1)] }, { coefficient := 1, powers := [(55, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (36, 1), (58, 1)] }, { coefficient := 1, powers := [(0, 1), (39, 1), (55, 1)] }, { coefficient := 1, powers := [(0, 1), (42, 1), (49, 1)] }, { coefficient := 1, powers := [(3, 1), (25, 1), (58, 1)] }, { coefficient := 1, powers := [(3, 1), (30, 1), (55, 1)] }, { coefficient := 1, powers := [(3, 1), (33, 1), (49, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1), (58, 1)] }, { coefficient := 1, powers := [(6, 1), (30, 1), (42, 1)] }, { coefficient := 1, powers := [(6, 1), (33, 1), (39, 1)] }, { coefficient := 1, powers := [(9, 1), (20, 1), (55, 1)] }, { coefficient := 1, powers := [(9, 1), (25, 1), (42, 1)] }, { coefficient := 1, powers := [(9, 1), (33, 1), (36, 1)] }, { coefficient := 1, powers := [(13, 1), (20, 1), (49, 1)] }, { coefficient := 1, powers := [(13, 1), (25, 1), (39, 1)] }, { coefficient := 1, powers := [(13, 1), (30, 1), (36, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (41, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (48, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (48, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1), (29, 1), (48, 1)] }, { coefficient := 1, powers := [(12, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (54, 1)] }, { coefficient := 1, powers := [(19, 1), (29, 1), (41, 1)] }, { coefficient := 1, powers := [(19, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (61, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(39, 1)] }],
  [{ coefficient := 1, powers := [(40, 1)] }],
  [{ coefficient := 1, powers := [(41, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(55, 1)] }],
  [{ coefficient := 1, powers := [(56, 1), (64, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(57, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 60 → SparsePoly (Fin 65) := ![
  [{ coefficient := -1, powers := [(9, 1), (19, 1), (27, 1), (33, 1), (36, 1), (47, 1), (62, 1)] }, { coefficient := 1, powers := [(19, 1), (27, 1), (30, 1), (36, 1), (42, 1), (47, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (19, 1), (22, 1), (33, 1), (36, 1), (54, 1), (62, 1)] }, { coefficient := -1, powers := [(19, 1), (22, 1), (30, 1), (36, 1), (42, 1), (54, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (13, 1), (22, 1), (62, 1)] }, { coefficient := 1, powers := [(0, 1), (14, 1), (22, 2), (62, 2)] }, { coefficient := 2, powers := [(0, 1), (22, 1), (42, 1), (62, 1)] }, { coefficient := 1, powers := [(13, 1), (20, 1), (22, 1), (62, 1)] }, { coefficient := 1, powers := [(13, 1), (22, 1), (25, 1), (62, 1)] }, { coefficient := 1, powers := [(20, 1), (22, 1), (42, 1), (62, 1)] }, { coefficient := 1, powers := [(22, 1), (25, 1), (42, 1), (62, 1)] }, { coefficient := 1, powers := [(22, 1), (33, 1), (36, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (6, 1), (12, 1), (53, 1), (58, 1)] }, { coefficient := 1, powers := [(0, 1), (8, 1), (50, 1), (58, 1)] }, { coefficient := -1, powers := [(6, 1), (12, 1), (20, 1), (53, 1), (58, 1)] }, { coefficient := -1, powers := [(8, 1), (20, 1), (50, 1), (58, 1)] }, { coefficient := -1, powers := [(9, 1), (12, 1), (33, 1), (36, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (6, 1), (19, 1), (47, 1), (58, 1)] }, { coefficient := -1, powers := [(6, 1), (19, 1), (20, 1), (47, 1), (58, 1)] }, { coefficient := -1, powers := [(9, 1), (19, 1), (33, 1), (36, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (30, 1), (36, 1), (42, 1), (47, 1)] }],
  [{ coefficient := -1, powers := [(29, 1), (36, 1), (42, 1), (60, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(24, 1), (36, 1), (42, 1), (60, 1)] }, { coefficient := -1, powers := [(35, 1), (36, 1), (41, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (35, 1), (36, 1), (42, 1), (47, 1)] }],
  [{ coefficient := -1, powers := [(9, 1), (24, 1), (33, 1), (36, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (26, 1), (35, 1), (36, 1), (50, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (6, 1), (24, 1), (43, 1), (54, 1), (58, 1), (61, 1)] }, { coefficient := -1, powers := [(0, 1), (6, 1), (24, 1), (46, 1), (54, 1), (58, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1), (24, 1), (43, 1), (54, 1), (58, 1), (61, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1), (24, 1), (46, 1), (54, 1), (58, 1)] }, { coefficient := 1, powers := [(9, 1), (24, 1), (33, 1), (36, 1), (46, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (6, 1), (24, 1), (54, 1), (58, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1), (24, 1), (54, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (11, 1), (19, 1), (27, 1), (33, 1), (36, 1), (62, 1)] }, { coefficient := -1, powers := [(11, 1), (19, 1), (27, 1), (30, 1), (36, 1), (42, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(9, 1), (12, 1), (20, 1), (33, 1), (36, 1), (48, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (35, 1), (36, 1), (42, 1)] }],
  [{ coefficient := -1, powers := [(9, 1), (21, 1), (35, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (6, 1), (18, 1), (24, 1), (54, 1), (58, 1), (61, 1)] }, { coefficient := -1, powers := [(6, 1), (18, 1), (20, 1), (24, 1), (54, 1), (58, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (13, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 1), (14, 1), (22, 1), (62, 2)] }, { coefficient := -2, powers := [(0, 1), (42, 1), (62, 1)] }, { coefficient := -1, powers := [(13, 1), (20, 1), (62, 1)] }, { coefficient := -1, powers := [(13, 1), (25, 1), (62, 1)] }, { coefficient := -1, powers := [(20, 1), (42, 1), (62, 1)] }, { coefficient := -1, powers := [(25, 1), (42, 1), (62, 1)] }, { coefficient := -1, powers := [(33, 1), (36, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(9, 1), (19, 1), (24, 1), (33, 1), (36, 1), (62, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (30, 1), (36, 1), (42, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (6, 1), (54, 1), (58, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1), (54, 1), (58, 1)] }, { coefficient := 1, powers := [(9, 1), (33, 1), (36, 1), (54, 1)] }, { coefficient := -1, powers := [(30, 1), (36, 1), (42, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (33, 1), (36, 1), (48, 1)] }, { coefficient := -1, powers := [(30, 1), (36, 1), (42, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(25, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (20, 1), (29, 1), (33, 1), (36, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (6, 1), (20, 1), (24, 1), (54, 1), (58, 1)] }, { coefficient := -1, powers := [(6, 1), (20, 2), (24, 1), (54, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (21, 1), (58, 1), (63, 1)] }, { coefficient := 1, powers := [(9, 1), (21, 1), (42, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(9, 1), (29, 1), (33, 1), (36, 1), (48, 1)] }],
  [{ coefficient := -1, powers := [(9, 1), (26, 1), (35, 1), (36, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (26, 1), (35, 1), (36, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (6, 1), (24, 1), (54, 1), (58, 1)] }, { coefficient := -1, powers := [(6, 1), (20, 1), (24, 1), (54, 1), (58, 1)] }, { coefficient := -1, powers := [(9, 1), (24, 1), (33, 1), (36, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (5, 1), (29, 1), (50, 1), (58, 1)] }, { coefficient := -1, powers := [(5, 1), (20, 1), (29, 1), (50, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (50, 1), (58, 1), (63, 1)] }, { coefficient := 1, powers := [(9, 1), (42, 1), (50, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (29, 1), (36, 1), (60, 1)] }, { coefficient := -1, powers := [(9, 1), (35, 1), (36, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (24, 1), (33, 1), (36, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (6, 1), (19, 1), (58, 1)] }, { coefficient := 1, powers := [(6, 1), (19, 1), (20, 1), (58, 1)] }, { coefficient := 1, powers := [(9, 1), (19, 1), (33, 1), (36, 1)] }, { coefficient := -1, powers := [(19, 1), (30, 1), (36, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (12, 1), (35, 1), (36, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (12, 1), (21, 1), (35, 1), (36, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (5, 1), (29, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (20, 1), (29, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (58, 1), (63, 1)] }, { coefficient := -1, powers := [(9, 1), (42, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (8, 1), (58, 1)] }, { coefficient := 1, powers := [(8, 1), (20, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(9, 1), (21, 1), (29, 1), (36, 1), (60, 1)] }, { coefficient := 1, powers := [(9, 1), (21, 1), (35, 1), (36, 1), (54, 1)] }, { coefficient := -1, powers := [(9, 1), (26, 1), (35, 1), (36, 1), (41, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (6, 1), (12, 1), (58, 1)] }, { coefficient := 1, powers := [(6, 1), (12, 1), (20, 1), (58, 1)] }, { coefficient := 1, powers := [(9, 1), (12, 1), (33, 1), (36, 1)] }],
  [{ coefficient := -1, powers := [(9, 1), (12, 1), (35, 1), (36, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (21, 1), (50, 1), (58, 1), (63, 1)] }, { coefficient := -1, powers := [(9, 1), (21, 1), (42, 1), (50, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(49, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (44, 1)] }, { coefficient := -1, powers := [(25, 1), (44, 1)] }, { coefficient := 1, powers := [(42, 1)] }],
  [{ coefficient := 1, powers := [(0, 1)] }, { coefficient := 1, powers := [(25, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (35, 1), (36, 1)] }],
  [{ coefficient := -1, powers := [(9, 1), (12, 1), (21, 1), (35, 1), (36, 1), (53, 1)] }, { coefficient := 1, powers := [(20, 1), (49, 1)] }, { coefficient := 1, powers := [(30, 1), (36, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (6, 1), (58, 1)] }, { coefficient := -1, powers := [(6, 1), (20, 1), (58, 1)] }, { coefficient := -1, powers := [(9, 1), (33, 1), (36, 1)] }, { coefficient := 1, powers := [(30, 1), (36, 1), (42, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (6, 1), (18, 1), (24, 1), (43, 1), (54, 1), (58, 1)] }, { coefficient := 1, powers := [(6, 1), (18, 1), (20, 1), (24, 1), (43, 1), (54, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (13, 1), (49, 1)] }, { coefficient := 1, powers := [(0, 1), (14, 1), (22, 1), (49, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 1), (36, 1), (58, 1)] }, { coefficient := 1, powers := [(0, 1), (42, 1), (49, 1)] }, { coefficient := 1, powers := [(9, 1), (19, 1), (24, 1), (33, 1), (36, 1), (54, 1)] }, { coefficient := 1, powers := [(13, 1), (20, 1), (49, 1)] }, { coefficient := 1, powers := [(13, 1), (25, 1), (49, 1)] }, { coefficient := -1, powers := [(19, 1), (24, 1), (30, 1), (36, 1), (42, 1), (54, 1)] }, { coefficient := 1, powers := [(20, 1), (42, 1), (49, 1)] }, { coefficient := 1, powers := [(25, 1), (42, 1), (49, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1), (49, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (6, 1), (38, 1), (58, 1), (60, 1)] }, { coefficient := -1, powers := [(0, 1), (6, 1), (41, 1), (57, 1), (58, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1), (38, 1), (58, 1), (60, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1), (41, 1), (57, 1), (58, 1)] }, { coefficient := 1, powers := [(9, 1), (33, 1), (36, 1), (38, 1), (60, 1)] }, { coefficient := 1, powers := [(9, 1), (33, 1), (36, 1), (41, 1), (57, 1)] }, { coefficient := -1, powers := [(9, 1), (33, 1), (36, 1), (48, 1), (54, 1)] }, { coefficient := -1, powers := [(30, 1), (36, 1), (38, 1), (42, 1), (60, 1)] }, { coefficient := -1, powers := [(30, 1), (36, 1), (41, 1), (42, 1), (57, 1)] }, { coefficient := 1, powers := [(30, 1), (36, 1), (42, 1), (48, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (1, 1), (55, 1), (62, 1)] }, { coefficient := 1, powers := [(0, 1), (13, 1), (15, 1), (27, 1), (62, 1)] }, { coefficient := 1, powers := [(0, 1), (14, 1), (15, 1), (22, 1), (27, 1), (62, 2)] }, { coefficient := -1, powers := [(0, 1), (14, 1), (27, 1), (62, 1)] }, { coefficient := 2, powers := [(0, 1), (15, 1), (27, 1), (42, 1), (62, 1)] }, { coefficient := 1, powers := [(0, 1), (25, 1), (44, 1)] }, { coefficient := 1, powers := [(0, 1), (55, 1)] }, { coefficient := 1, powers := [(6, 1), (33, 1)] }, { coefficient := -1, powers := [(12, 1), (26, 1), (35, 1), (36, 1), (42, 1), (47, 1)] }, { coefficient := 1, powers := [(13, 1), (15, 1), (20, 1), (27, 1), (62, 1)] }, { coefficient := 1, powers := [(13, 1), (15, 1), (25, 1), (27, 1), (62, 1)] }, { coefficient := 1, powers := [(15, 1), (20, 1), (27, 1), (42, 1), (62, 1)] }, { coefficient := 1, powers := [(15, 1), (25, 1), (27, 1), (42, 1), (62, 1)] }, { coefficient := 1, powers := [(15, 1), (27, 1), (33, 1), (36, 1), (62, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (26, 1), (36, 1), (42, 1), (60, 1)] }, { coefficient := 1, powers := [(18, 1), (26, 1), (35, 1), (36, 1), (41, 1), (42, 1)] }, { coefficient := 1, powers := [(25, 2), (44, 1)] }, { coefficient := -1, powers := [(25, 1), (42, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (5, 1), (25, 1), (29, 1), (43, 1), (50, 1), (58, 1)] }, { coefficient := -1, powers := [(0, 1), (6, 1), (19, 1), (20, 1), (24, 1), (54, 1), (58, 1)] }, { coefficient := -1, powers := [(0, 1), (6, 1), (19, 1), (24, 1), (25, 1), (54, 1), (58, 1)] }, { coefficient := 1, powers := [(0, 1), (9, 1), (12, 1), (21, 1), (35, 1), (36, 1), (53, 1), (55, 1)] }, { coefficient := -1, powers := [(0, 1), (20, 1), (49, 1), (55, 1)] }, { coefficient := -1, powers := [(0, 1), (30, 1), (36, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (20, 1), (25, 1), (29, 1), (43, 1), (50, 1), (58, 1)] }, { coefficient := 1, powers := [(6, 1), (9, 1), (12, 1), (21, 1), (33, 1), (35, 1), (36, 1), (53, 1)] }, { coefficient := 1, powers := [(6, 1), (19, 1), (20, 2), (24, 1), (54, 1), (58, 1)] }, { coefficient := 1, powers := [(6, 1), (19, 1), (20, 1), (24, 1), (25, 1), (54, 1), (58, 1)] }, { coefficient := -1, powers := [(6, 1), (20, 1), (33, 1), (49, 1)] }, { coefficient := 1, powers := [(6, 1), (21, 1), (25, 1), (50, 1), (58, 1), (63, 1)] }, { coefficient := -1, powers := [(6, 1), (30, 1), (33, 1), (36, 1)] }, { coefficient := 1, powers := [(9, 1), (12, 1), (13, 1), (21, 1), (25, 1), (35, 1), (36, 1), (53, 1)] }, { coefficient := -1, powers := [(9, 1), (12, 1), (13, 1), (21, 1), (26, 1), (35, 1), (36, 1)] }, { coefficient := 1, powers := [(9, 1), (12, 1), (20, 1), (29, 1), (33, 1), (36, 1), (48, 1)] }, { coefficient := 1, powers := [(9, 1), (17, 1), (21, 1), (25, 1), (29, 1), (36, 1), (60, 1)] }, { coefficient := -1, powers := [(9, 1), (17, 1), (21, 1), (25, 1), (35, 1), (36, 1), (54, 1)] }, { coefficient := 1, powers := [(9, 1), (17, 1), (25, 1), (26, 1), (35, 1), (36, 1), (41, 1)] }, { coefficient := 1, powers := [(9, 1), (19, 1), (24, 1), (25, 1), (33, 1), (36, 1), (54, 1)] }, { coefficient := 1, powers := [(9, 1), (21, 1), (25, 1), (42, 1), (50, 1), (63, 1)] }, { coefficient := -1, powers := [(13, 1), (20, 1), (25, 1), (49, 1)] }, { coefficient := -1, powers := [(13, 1), (25, 1), (30, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (25, 1), (58, 1)] }, { coefficient := 1, powers := [(9, 1), (25, 1), (42, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (9, 1)] }, { coefficient := 1, powers := [(3, 1), (30, 1)] }, { coefficient := 1, powers := [(9, 1), (12, 1), (26, 1), (35, 1), (36, 1), (47, 1)] }, { coefficient := 1, powers := [(9, 1), (18, 1), (26, 1), (35, 1), (36, 1), (41, 1)] }, { coefficient := 1, powers := [(9, 1), (20, 1)] }, { coefficient := -1, powers := [(9, 1), (25, 1)] }, { coefficient := -2, powers := [(20, 1), (49, 1)] }, { coefficient := -1, powers := [(30, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (29, 1), (30, 1), (36, 1), (42, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (5, 1), (6, 1), (32, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (6, 1), (20, 1), (32, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (9, 1), (32, 1), (33, 1), (36, 1)] }, { coefficient := -1, powers := [(5, 1), (30, 1), (32, 1), (36, 1), (42, 1)] }, { coefficient := -1, powers := [(9, 1), (12, 1), (24, 1), (33, 1), (36, 1)] }, { coefficient := -1, powers := [(12, 1), (24, 1), (30, 1), (36, 1), (42, 1)] }]
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
    ¬ ∀ index : Fin 60,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component60.SelectedLeafB6_1_2.selectedHasNoCommonZero

end Krenn.Component60.SelectedLeafB6_1_2
