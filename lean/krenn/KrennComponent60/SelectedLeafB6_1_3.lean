import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component60.SelectedLeafB6_1_3

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "5d42dbebdfd4389acf340aef8880c981a135d0716938a390e2eb34ec5cb5fe18"
def certificateSHA256 : String := "95c3452f4949003591b716c0a33d4d52a14e0212b5211338e6c279d233dd4d98"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 70 → Fin 665 := ![
  11,
  12,
  13,
  14,
  19,
  22,
  25,
  143,
  150,
  165,
  172,
  173,
  178,
  179,
  211,
  240,
  264,
  273,
  292,
  293,
  294,
  298,
  300,
  301,
  302,
  303,
  305,
  308,
  310,
  312,
  314,
  383,
  389,
  398,
  404,
  422,
  423,
  427,
  433,
  434,
  435,
  436,
  437,
  442,
  443,
  454,
  466,
  470,
  548,
  556,
  578,
  579,
  587,
  593,
  600,
  601,
  606,
  608,
  612,
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
def selectedEquations : Fin 70 → SparsePoly (Fin 66) := ![
  [{ coefficient := 1, powers := [(11, 1), (29, 1)] }],
  [{ coefficient := 1, powers := [(15, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(15, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (47, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (26, 1)] }, { coefficient := 1, powers := [(26, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (26, 1)] }, { coefficient := 1, powers := [(18, 1), (20, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (20, 1)] }, { coefficient := 1, powers := [(18, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (43, 1)] }, { coefficient := 1, powers := [(19, 1), (20, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (53, 1)] }, { coefficient := 1, powers := [(29, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (40, 1)] }, { coefficient := 1, powers := [(29, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (26, 1), (46, 1)] }, { coefficient := 1, powers := [(9, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (26, 1), (45, 1)] }, { coefficient := 1, powers := [(18, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (25, 1), (48, 1)] }, { coefficient := 1, powers := [(19, 1), (21, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (40, 1), (43, 1)] }, { coefficient := 1, powers := [(29, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1)] }, { coefficient := 1, powers := [(20, 1), (43, 1)] }, { coefficient := 1, powers := [(25, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (48, 1)] }, { coefficient := 1, powers := [(21, 1), (43, 1)] }, { coefficient := 1, powers := [(25, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (50, 1)] }, { coefficient := 1, powers := [(20, 1), (50, 1)] }, { coefficient := 1, powers := [(25, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (49, 1)] }, { coefficient := 1, powers := [(15, 1), (22, 1), (49, 1)] }, { coefficient := 1, powers := [(15, 1), (27, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (54, 1)] }, { coefficient := 1, powers := [(11, 1), (27, 1), (53, 1)] }, { coefficient := 1, powers := [(15, 1), (22, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (48, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1)] }, { coefficient := 1, powers := [(12, 1), (29, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (58, 1)] }, { coefficient := 1, powers := [(9, 1), (42, 1)] }, { coefficient := 1, powers := [(13, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (46, 1)] }, { coefficient := 1, powers := [(16, 1), (40, 1)] }, { coefficient := 1, powers := [(16, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (45, 1)] }, { coefficient := 1, powers := [(12, 1), (56, 1)] }, { coefficient := 1, powers := [(18, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (46, 1)] }, { coefficient := 1, powers := [(19, 1), (40, 1)] }, { coefficient := 1, powers := [(19, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1), (51, 1)] }, { coefficient := 1, powers := [(20, 1), (43, 1), (51, 1)] }, { coefficient := 1, powers := [(43, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1), (50, 1)] }, { coefficient := 1, powers := [(25, 1), (45, 1), (50, 1)] }, { coefficient := 1, powers := [(50, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (20, 1), (56, 1)] }, { coefficient := 1, powers := [(12, 1)] }, { coefficient := 1, powers := [(18, 1), (20, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (26, 1), (47, 1)] }, { coefficient := 1, powers := [(18, 1), (21, 1), (54, 1)] }, { coefficient := 1, powers := [(18, 1), (26, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (20, 1), (49, 1)] }, { coefficient := 1, powers := [(18, 1), (25, 1), (39, 1)] }, { coefficient := 1, powers := [(18, 1), (30, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (25, 1), (46, 1)] }, { coefficient := 1, powers := [(19, 1), (25, 1), (40, 1)] }, { coefficient := 1, powers := [(19, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1)] }, { coefficient := 1, powers := [(25, 1), (40, 1), (43, 1)] }, { coefficient := 1, powers := [(25, 1), (46, 1)] }, { coefficient := 1, powers := [(43, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1)] }, { coefficient := 1, powers := [(6, 1), (21, 1), (59, 1)] }, { coefficient := 1, powers := [(21, 1)] }, { coefficient := 1, powers := [(25, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (46, 1)] }, { coefficient := 1, powers := [(10, 1), (27, 1), (46, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (59, 1)] }, { coefficient := 1, powers := [(18, 1), (21, 1), (51, 1)] }, { coefficient := 1, powers := [(18, 1), (21, 1), (56, 1)] }, { coefficient := 1, powers := [(18, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (60, 1)] }, { coefficient := 1, powers := [(12, 1), (48, 1)] }, { coefficient := 1, powers := [(19, 1), (21, 1), (52, 1)] }, { coefficient := 1, powers := [(19, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (59, 1)] }, { coefficient := 1, powers := [(18, 1), (26, 1), (40, 1)] }, { coefficient := 1, powers := [(18, 1), (26, 1), (45, 1)] }, { coefficient := 1, powers := [(18, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (60, 1)] }, { coefficient := 1, powers := [(12, 1), (26, 1), (46, 1)] }, { coefficient := 1, powers := [(12, 1), (57, 1)] }, { coefficient := 1, powers := [(19, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (20, 1)] }, { coefficient := 1, powers := [(18, 1), (20, 1), (55, 1)] }, { coefficient := 1, powers := [(18, 1), (25, 1), (42, 1)] }, { coefficient := 1, powers := [(18, 1), (33, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (40, 1)] }, { coefficient := 1, powers := [(18, 1), (45, 1)] }, { coefficient := 1, powers := [(18, 1), (51, 1)] }, { coefficient := 1, powers := [(18, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (54, 1)] }, { coefficient := 1, powers := [(29, 1), (41, 1)] }, { coefficient := 1, powers := [(29, 1), (47, 1), (50, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1), (53, 1)] }, { coefficient := 1, powers := [(20, 1), (43, 1), (53, 1)] }, { coefficient := 1, powers := [(20, 1), (57, 1)] }, { coefficient := 1, powers := [(26, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1), (50, 1)] }, { coefficient := 1, powers := [(21, 1), (50, 1)] }, { coefficient := 1, powers := [(25, 1), (41, 1)] }, { coefficient := 1, powers := [(25, 1), (47, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (48, 1), (52, 1)] }, { coefficient := 1, powers := [(21, 1), (43, 1), (52, 1)] }, { coefficient := 1, powers := [(41, 1), (43, 1)] }, { coefficient := 1, powers := [(48, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (25, 1), (40, 1)] }, { coefficient := 1, powers := [(17, 1)] }, { coefficient := 1, powers := [(18, 1), (25, 1), (44, 1)] }, { coefficient := 1, powers := [(18, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (43, 1), (53, 1)] }, { coefficient := 1, powers := [(24, 1), (57, 1)] }, { coefficient := 1, powers := [(29, 1), (48, 1)] }, { coefficient := 1, powers := [(35, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1)] }, { coefficient := 1, powers := [(6, 1), (59, 1)] }, { coefficient := 1, powers := [(25, 1), (40, 1)] }, { coefficient := 1, powers := [(25, 1), (45, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (51, 1)] }, { coefficient := 1, powers := [(3, 1), (59, 1)] }, { coefficient := 1, powers := [(20, 1), (51, 1)] }, { coefficient := 1, powers := [(20, 1), (56, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1), (36, 1), (58, 1)] }, { coefficient := 1, powers := [(1, 1), (39, 1), (55, 1)] }, { coefficient := 1, powers := [(1, 1), (42, 1), (49, 1)] }, { coefficient := 1, powers := [(14, 1), (22, 1), (49, 1)] }, { coefficient := 1, powers := [(14, 1), (27, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (41, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (47, 1), (52, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (56, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (56, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1)] }, { coefficient := 1, powers := [(3, 1), (33, 1)] }, { coefficient := 1, powers := [(13, 1), (20, 1)] }, { coefficient := 1, powers := [(20, 1), (55, 1)] }, { coefficient := 1, powers := [(25, 1), (42, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (49, 1)] }, { coefficient := 1, powers := [(6, 1), (30, 1)] }, { coefficient := 1, powers := [(9, 1), (25, 1)] }, { coefficient := 1, powers := [(20, 1), (49, 1)] }, { coefficient := 1, powers := [(25, 1), (39, 1)] }, { coefficient := 1, powers := [(30, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (36, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1)] }, { coefficient := 1, powers := [(3, 1), (25, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1), (59, 1)] }, { coefficient := 1, powers := [(20, 1)] }, { coefficient := 1, powers := [(25, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (46, 1), (53, 1)] }, { coefficient := 1, powers := [(26, 1), (40, 1), (43, 1)] }, { coefficient := 1, powers := [(26, 1), (46, 1)] }, { coefficient := 1, powers := [(43, 1), (53, 1)] }, { coefficient := 1, powers := [(57, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1), (49, 1)] }, { coefficient := 1, powers := [(6, 1), (30, 1), (44, 1)] }, { coefficient := 1, powers := [(6, 1), (58, 1)] }, { coefficient := 1, powers := [(9, 1), (25, 1), (44, 1)] }, { coefficient := 1, powers := [(9, 1), (55, 1)] }, { coefficient := 1, powers := [(13, 1), (49, 1)] }],
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
  [{ coefficient := 1, powers := [(57, 1), (65, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 70 → SparsePoly (Fin 66) := ![
  [{ coefficient := 1, powers := [(19, 1), (27, 1), (36, 1), (47, 1), (59, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(19, 1), (22, 1), (36, 1), (54, 1), (59, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (14, 1), (18, 1), (22, 2), (35, 1), (36, 1), (41, 1), (53, 1), (62, 2)] }, { coefficient := 1, powers := [(0, 1), (18, 1), (22, 1), (35, 1), (36, 1), (41, 1), (42, 1), (53, 1), (62, 1)] }],
  [{ coefficient := 2, powers := [(12, 1), (23, 1), (26, 1), (36, 1), (59, 1), (62, 1)] }, { coefficient := -2, powers := [(12, 1), (26, 1), (27, 1), (36, 1), (51, 1), (59, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (35, 1), (36, 1), (41, 1), (42, 1), (53, 1)] }, { coefficient := -1, powers := [(13, 1), (20, 1), (35, 1), (36, 1), (41, 1), (53, 1)] }, { coefficient := 1, powers := [(13, 1), (25, 1), (35, 1), (36, 1), (41, 1), (53, 1)] }, { coefficient := -1, powers := [(25, 1), (35, 1), (36, 1), (41, 1), (42, 1), (53, 1)] }, { coefficient := -1, powers := [(33, 1), (35, 1), (36, 2), (41, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (36, 1), (53, 1), (57, 1), (59, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (36, 1), (47, 1), (57, 1), (59, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(36, 1), (52, 1), (57, 1), (59, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(17, 1), (25, 1), (35, 1), (36, 1), (41, 1), (46, 1), (53, 1), (65, 1)] }, { coefficient := 2, powers := [(18, 1), (25, 1), (35, 1), (36, 1), (41, 1), (42, 1), (46, 1), (53, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (36, 1), (46, 1), (57, 1), (59, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (35, 1), (36, 1), (41, 1), (53, 1), (58, 1)] }, { coefficient := 1, powers := [(9, 1), (25, 1), (35, 1), (36, 1), (41, 1), (44, 1), (53, 1)] }, { coefficient := -1, powers := [(24, 1), (36, 1), (43, 1), (54, 1), (57, 1), (59, 1), (61, 1), (65, 1)] }, { coefficient := -2, powers := [(24, 1), (36, 1), (46, 1), (54, 1), (57, 1), (59, 1), (65, 1)] }, { coefficient := -1, powers := [(29, 1), (36, 1), (41, 1), (46, 1), (57, 1), (59, 1), (65, 1)] }, { coefficient := 1, powers := [(29, 1), (36, 1), (48, 1), (50, 1), (57, 1), (59, 1), (61, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(24, 1), (36, 1), (54, 1), (57, 1), (59, 1), (65, 1)] }, { coefficient := -1, powers := [(29, 1), (36, 1), (41, 1), (57, 1), (59, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(11, 1), (19, 1), (27, 1), (36, 1), (59, 1), (62, 1)] }, { coefficient := 2, powers := [(12, 1), (25, 1), (36, 1), (46, 1), (59, 1)] }],
  [{ coefficient := 2, powers := [(12, 1), (20, 1), (36, 1), (48, 1), (57, 1), (59, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (25, 1), (35, 1), (36, 1), (41, 1), (53, 1), (65, 1)] }, { coefficient := -2, powers := [(18, 1), (25, 1), (35, 1), (36, 1), (41, 1), (42, 1), (53, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(35, 1), (36, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (36, 1), (52, 1), (57, 1), (59, 1), (65, 1)] }],
  [{ coefficient := -2, powers := [(12, 1), (25, 1), (36, 1), (47, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1), (51, 1), (53, 1), (65, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (36, 1), (54, 1), (57, 1), (59, 1), (61, 1), (65, 1)] }, { coefficient := 1, powers := [(20, 1), (45, 1), (51, 1), (53, 1), (65, 1)] }, { coefficient := 1, powers := [(26, 1), (45, 1), (51, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(18, 1), (29, 1), (36, 1), (52, 1), (57, 1), (59, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(18, 1), (29, 1), (36, 1), (48, 1), (57, 1), (59, 1), (61, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (14, 1), (18, 1), (22, 1), (35, 1), (36, 1), (41, 1), (53, 1), (62, 2)] }, { coefficient := -1, powers := [(0, 1), (18, 1), (35, 1), (36, 1), (41, 1), (42, 1), (53, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (24, 1), (36, 1), (59, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(36, 1), (54, 1), (57, 1), (59, 1), (65, 1)] }, { coefficient := -1, powers := [(36, 1), (54, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(36, 1), (48, 1), (57, 1), (59, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (25, 1), (35, 1), (36, 1), (41, 1), (53, 1)] }],
  [{ coefficient := 2, powers := [(12, 1), (24, 1), (26, 1), (27, 1), (36, 1), (59, 1), (62, 1)] }],
  [{ coefficient := -2, powers := [(20, 1), (29, 1), (36, 1), (48, 1), (57, 1), (59, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (24, 1), (36, 1), (54, 1), (57, 1), (59, 1), (65, 1)] }, { coefficient := 1, powers := [(20, 1), (29, 1), (36, 1), (41, 1), (57, 1), (59, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (45, 1), (53, 1), (65, 1)] }, { coefficient := -1, powers := [(20, 1), (45, 1), (53, 1), (65, 1)] }, { coefficient := -1, powers := [(26, 1), (45, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(20, 1), (21, 1), (45, 1), (51, 1), (63, 1)] }, { coefficient := -1, powers := [(20, 1), (21, 1), (45, 1), (61, 1), (63, 1)] }, { coefficient := -1, powers := [(20, 1), (21, 1), (51, 1), (61, 1), (63, 1)] }, { coefficient := -1, powers := [(20, 1), (21, 1), (56, 1), (61, 1), (63, 1)] }, { coefficient := -1, powers := [(21, 1), (51, 1), (63, 1)] }],
  [{ coefficient := 2, powers := [(29, 1), (36, 1), (48, 1), (57, 1), (59, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(35, 1), (36, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (35, 1), (36, 1), (41, 1), (53, 1)] }, { coefficient := -1, powers := [(25, 1), (35, 1), (36, 1), (41, 1), (44, 1), (53, 1)] }, { coefficient := -1, powers := [(35, 1), (36, 1), (41, 1), (42, 1), (53, 1)] }],
  [{ coefficient := 2, powers := [(24, 1), (36, 1), (54, 1), (57, 1), (59, 1), (65, 1)] }, { coefficient := 1, powers := [(29, 1), (36, 1), (41, 1), (57, 1), (59, 1), (65, 1)] }],
  [{ coefficient := -2, powers := [(12, 1), (24, 1), (36, 1), (53, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(20, 1), (45, 1), (50, 1), (51, 1), (63, 1)] }, { coefficient := -1, powers := [(20, 1), (45, 1), (50, 1), (61, 1), (63, 1)] }, { coefficient := -1, powers := [(20, 1), (50, 1), (51, 1), (61, 1), (63, 1)] }, { coefficient := -1, powers := [(20, 1), (50, 1), (56, 1), (61, 1), (63, 1)] }, { coefficient := -1, powers := [(50, 1), (51, 1), (63, 1)] }],
  [{ coefficient := -2, powers := [(12, 1), (24, 1), (26, 1), (36, 1), (59, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(35, 1), (36, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(29, 1), (36, 1), (57, 1), (59, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(35, 1), (36, 1), (41, 1)] }],
  [{ coefficient := -1, powers := [(24, 1), (36, 1), (57, 1), (59, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (35, 1), (36, 1), (41, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(21, 1), (35, 1), (36, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(19, 1), (36, 1), (57, 1), (59, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(25, 1), (45, 1), (51, 1), (65, 1)] }, { coefficient := 1, powers := [(45, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (45, 1), (51, 1), (63, 1)] }, { coefficient := 1, powers := [(20, 1), (45, 1), (61, 1), (63, 1)] }, { coefficient := 1, powers := [(20, 1), (51, 1), (61, 1), (63, 1)] }, { coefficient := 1, powers := [(20, 1), (56, 1), (61, 1), (63, 1)] }, { coefficient := 1, powers := [(51, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (29, 1), (36, 1), (57, 1), (59, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(9, 1), (20, 1), (35, 1), (36, 1), (41, 1), (53, 1)] }, { coefficient := -1, powers := [(9, 1), (25, 1), (35, 1), (36, 1), (41, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (36, 1), (57, 1), (59, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (21, 1), (45, 1), (50, 1), (51, 1), (63, 1)] }, { coefficient := 1, powers := [(20, 1), (21, 1), (45, 1), (50, 1), (61, 1), (63, 1)] }, { coefficient := 1, powers := [(20, 1), (21, 1), (50, 1), (51, 1), (61, 1), (63, 1)] }, { coefficient := 1, powers := [(20, 1), (21, 1), (50, 1), (56, 1), (61, 1), (63, 1)] }, { coefficient := -1, powers := [(20, 1), (61, 1)] }, { coefficient := 1, powers := [(21, 1), (50, 1), (51, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(25, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (18, 1), (35, 1), (36, 1), (41, 1), (53, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(36, 1), (57, 1), (59, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (35, 1), (36, 1), (41, 1), (49, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (25, 1), (35, 1), (36, 1), (41, 1), (44, 1), (53, 1)] }, { coefficient := 1, powers := [(18, 1), (35, 1), (36, 1), (41, 1), (42, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(61, 1)] }],
  [{ coefficient := 2, powers := [(12, 1), (24, 1), (36, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(18, 1), (25, 1), (35, 1), (36, 1), (41, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(18, 1), (35, 1), (36, 1), (41, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(36, 1), (57, 1), (59, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(18, 1), (24, 1), (36, 1), (43, 1), (54, 1), (57, 1), (59, 1), (65, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (36, 1), (48, 1), (50, 1), (57, 1), (59, 1), (65, 1)] }, { coefficient := 1, powers := [(20, 1), (45, 1)] }, { coefficient := 1, powers := [(25, 1), (51, 1)] }, { coefficient := -1, powers := [(36, 1), (59, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (14, 1), (18, 1), (22, 1), (35, 1), (36, 1), (41, 1), (49, 1), (53, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 1), (18, 1), (35, 1), (36, 2), (41, 1), (53, 1), (58, 1)] }, { coefficient := 2, powers := [(12, 1), (24, 1), (26, 1), (36, 1), (46, 1), (59, 1)] }, { coefficient := -1, powers := [(19, 1), (24, 1), (36, 1), (54, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(36, 1), (38, 1), (57, 1), (59, 1), (60, 1), (65, 1)] }, { coefficient := 1, powers := [(36, 1), (41, 1), (56, 1), (57, 1), (59, 1), (64, 1)] }, { coefficient := -1, powers := [(36, 1), (41, 1), (57, 2), (59, 1), (65, 1)] }, { coefficient := 1, powers := [(36, 1), (48, 1), (54, 1), (57, 1), (59, 1), (65, 1)] }, { coefficient := 1, powers := [(36, 1), (48, 1), (54, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (1, 1), (18, 1), (35, 1), (36, 1), (41, 1), (53, 1), (55, 1), (62, 1)] }, { coefficient := 1, powers := [(0, 1), (14, 1), (15, 1), (18, 1), (22, 1), (27, 1), (35, 1), (36, 1), (41, 1), (53, 1), (62, 2)] }, { coefficient := -1, powers := [(0, 1), (14, 1), (18, 1), (27, 1), (35, 1), (36, 1), (41, 1), (53, 1), (62, 1)] }, { coefficient := 1, powers := [(0, 1), (15, 1), (18, 1), (27, 1), (35, 1), (36, 1), (41, 1), (42, 1), (53, 1), (62, 1)] }, { coefficient := 1, powers := [(0, 1), (18, 1), (35, 1), (36, 1), (41, 1), (53, 1), (55, 1)] }, { coefficient := 1, powers := [(6, 1), (18, 1), (33, 1), (35, 1), (36, 1), (41, 1), (53, 1)] }, { coefficient := -1, powers := [(13, 1), (18, 1), (25, 1), (35, 1), (36, 1), (41, 1), (53, 1)] }, { coefficient := 1, powers := [(17, 1), (25, 1), (26, 1), (35, 1), (36, 1), (41, 1), (46, 1), (53, 1), (65, 1)] }, { coefficient := -2, powers := [(18, 1), (25, 1), (26, 1), (35, 1), (36, 1), (41, 1), (42, 1), (46, 1), (53, 1), (65, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (12, 1), (24, 1), (36, 1), (57, 1), (59, 1)] }, { coefficient := 1, powers := [(9, 1), (17, 1), (20, 1), (25, 1), (35, 1), (36, 1), (41, 1), (53, 1)] }, { coefficient := 1, powers := [(9, 1), (17, 1), (25, 2), (35, 1), (36, 1), (41, 1), (53, 1)] }, { coefficient := -2, powers := [(12, 1), (20, 1), (29, 1), (36, 1), (48, 1), (57, 1), (59, 1), (65, 1)] }, { coefficient := 2, powers := [(12, 1), (24, 1), (25, 1), (36, 1), (43, 1), (53, 1), (59, 1)] }, { coefficient := -2, powers := [(12, 1), (24, 1), (26, 1), (36, 1), (43, 1), (59, 1)] }, { coefficient := 2, powers := [(12, 1), (25, 1), (29, 1), (36, 1), (43, 1), (47, 1), (59, 1)] }, { coefficient := 1, powers := [(18, 1), (21, 1), (35, 1), (36, 1), (54, 1)] }, { coefficient := 1, powers := [(18, 1), (26, 1), (35, 1), (36, 1), (41, 1)] }, { coefficient := -1, powers := [(19, 1), (20, 1), (24, 1), (36, 1), (54, 1), (57, 1), (59, 1), (65, 1)] }, { coefficient := -1, powers := [(19, 1), (20, 1), (29, 1), (36, 1), (41, 1), (57, 1), (59, 1), (65, 1)] }, { coefficient := -2, powers := [(19, 1), (24, 1), (25, 1), (36, 1), (54, 1), (57, 1), (59, 1), (65, 1)] }, { coefficient := -1, powers := [(19, 1), (25, 1), (29, 1), (36, 1), (41, 1), (57, 1), (59, 1), (65, 1)] }, { coefficient := -1, powers := [(20, 1), (21, 1), (25, 1), (45, 1), (50, 1), (51, 1), (63, 1)] }, { coefficient := -1, powers := [(20, 1), (21, 1), (25, 1), (45, 1), (50, 1), (61, 1), (63, 1)] }, { coefficient := -1, powers := [(20, 1), (21, 1), (25, 1), (50, 1), (51, 1), (61, 1), (63, 1)] }, { coefficient := -1, powers := [(20, 1), (21, 1), (25, 1), (50, 1), (56, 1), (61, 1), (63, 1)] }, { coefficient := 1, powers := [(20, 1), (25, 1), (61, 1)] }, { coefficient := -1, powers := [(21, 1), (25, 1), (50, 1), (51, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(20, 1), (25, 1), (45, 1), (51, 1)] }, { coefficient := -1, powers := [(20, 1), (25, 1), (45, 1), (61, 1)] }, { coefficient := -1, powers := [(20, 1), (25, 1), (51, 1), (61, 1)] }, { coefficient := -1, powers := [(20, 1), (25, 1), (56, 1), (61, 1)] }, { coefficient := -1, powers := [(25, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (18, 1), (30, 1), (35, 1), (36, 1), (41, 1), (53, 1)] }, { coefficient := 1, powers := [(9, 1), (18, 1), (20, 1), (35, 1), (36, 1), (41, 1), (53, 1)] }, { coefficient := 2, powers := [(9, 1), (18, 1), (25, 1), (35, 1), (36, 1), (41, 1), (53, 1)] }, { coefficient := -1, powers := [(18, 1), (20, 1), (35, 1), (36, 1), (41, 1), (49, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (32, 1), (36, 1), (57, 1), (59, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (36, 1), (57, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (32, 1), (36, 1), (57, 1), (59, 1)] }, { coefficient := -1, powers := [(8, 1), (35, 1), (36, 1), (41, 1), (59, 1)] }, { coefficient := -1, powers := [(9, 1), (17, 1), (25, 1), (35, 1), (36, 1), (41, 1), (53, 1)] }, { coefficient := 2, powers := [(9, 1), (18, 1), (25, 1), (35, 1), (36, 1), (41, 1), (42, 1), (53, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (36, 1), (57, 1), (59, 1)] }, { coefficient := 1, powers := [(20, 1), (25, 1), (45, 1), (51, 1)] }, { coefficient := -1, powers := [(20, 1), (45, 1)] }, { coefficient := 1, powers := [(36, 1), (59, 1)] }]
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
    ¬ ∀ index : Fin 70,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component60.SelectedLeafB6_1_3.selectedHasNoCommonZero

end Krenn.Component60.SelectedLeafB6_1_3
