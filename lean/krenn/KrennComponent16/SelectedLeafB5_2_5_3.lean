import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component16.SelectedLeafB5_2_5_3

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "46281ba2e1138466bec291ce9ac7b2e9d2ba77c751ae3c2701fcfdb32d43d522"
def certificateSHA256 : String := "4ccf0b839d081ab76da79be3cb5ad270f845b411ef918424616823c95e70c4c1"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 47 → Fin 674 := ![
  10,
  13,
  18,
  23,
  26,
  27,
  29,
  142,
  158,
  166,
  170,
  261,
  298,
  299,
  302,
  312,
  316,
  348,
  408,
  431,
  436,
  437,
  440,
  448,
  462,
  473,
  478,
  560,
  585,
  588,
  606,
  607,
  636,
  652,
  655,
  659,
  661,
  662,
  664,
  665,
  667,
  668,
  669,
  670,
  671,
  672,
  673
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 47 → SparsePoly (Fin 69) := ![
  [{ coefficient := 1, powers := [(13, 1), (28, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (28, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(28, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(28, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(28, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (55, 1)] }, { coefficient := 1, powers := [(21, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (50, 1)] }, { coefficient := 1, powers := [(20, 1), (22, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (21, 1)] }, { coefficient := 1, powers := [(19, 1), (26, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (45, 1)] }, { coefficient := 1, powers := [(29, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (24, 1), (54, 1)] }, { coefficient := 1, powers := [(31, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1)] }, { coefficient := 1, powers := [(21, 1), (45, 1)] }, { coefficient := 1, powers := [(26, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (50, 1)] }, { coefficient := 1, powers := [(22, 1), (45, 1)] }, { coefficient := 1, powers := [(26, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (61, 1)] }, { coefficient := 1, powers := [(13, 1), (50, 1)] }, { coefficient := 1, powers := [(20, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (24, 1)] }, { coefficient := 1, powers := [(24, 1), (56, 1)] }, { coefficient := 1, powers := [(29, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (55, 1)] }, { coefficient := 1, powers := [(31, 1), (43, 1)] }, { coefficient := 1, powers := [(34, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (31, 1), (60, 1)] }, { coefficient := 1, powers := [(24, 1), (54, 1)] }, { coefficient := 1, powers := [(31, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (26, 1), (48, 1)] }, { coefficient := 1, powers := [(20, 1), (26, 1), (42, 1)] }, { coefficient := 1, powers := [(20, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (44, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (56, 1)] }, { coefficient := 1, powers := [(19, 1), (29, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (50, 1)] }, { coefficient := 1, powers := [(5, 1), (37, 1)] }, { coefficient := 1, powers := [(19, 1), (29, 1), (50, 1)] }, { coefficient := 1, powers := [(20, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (51, 1)] }, { coefficient := 1, powers := [(12, 1), (29, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (51, 1)] }, { coefficient := 1, powers := [(19, 1), (29, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1)] }, { coefficient := 1, powers := [(13, 1), (31, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (61, 1)] }, { coefficient := 1, powers := [(13, 1), (27, 1), (48, 1)] }, { coefficient := 1, powers := [(13, 1), (58, 1)] }, { coefficient := 1, powers := [(20, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1), (54, 1)] }, { coefficient := 1, powers := [(21, 1), (45, 1), (54, 1)] }, { coefficient := 1, powers := [(21, 1), (58, 1)] }, { coefficient := 1, powers := [(27, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (50, 1), (54, 1)] }, { coefficient := 1, powers := [(22, 1), (45, 1), (54, 1)] }, { coefficient := 1, powers := [(22, 1), (58, 1)] }, { coefficient := 1, powers := [(27, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1)] }, { coefficient := 1, powers := [(19, 1), (29, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (21, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1)] }, { coefficient := 1, powers := [(19, 1), (21, 1), (52, 1)] }, { coefficient := 1, powers := [(19, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (53, 1)] }, { coefficient := 1, powers := [(3, 1), (60, 1)] }, { coefficient := 1, powers := [(21, 1), (53, 1)] }, { coefficient := 1, powers := [(21, 1), (57, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (40, 1), (61, 1)] }, { coefficient := 1, powers := [(0, 1), (43, 1), (58, 1)] }, { coefficient := 1, powers := [(0, 1), (50, 1), (55, 1)] }, { coefficient := 1, powers := [(22, 1), (45, 1), (55, 1)] }, { coefficient := 1, powers := [(27, 1), (43, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1)] }, { coefficient := 1, powers := [(3, 1), (35, 1)] }, { coefficient := 1, powers := [(14, 1), (21, 1)] }, { coefficient := 1, powers := [(21, 1), (56, 1)] }, { coefficient := 1, powers := [(26, 1), (44, 1)] }, { coefficient := 1, powers := [(35, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (51, 1)] }, { coefficient := 1, powers := [(6, 1), (32, 1)] }, { coefficient := 1, powers := [(9, 1), (26, 1)] }, { coefficient := 1, powers := [(21, 1), (51, 1)] }, { coefficient := 1, powers := [(26, 1), (41, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (32, 1), (58, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (50, 1)] }, { coefficient := 1, powers := [(12, 1), (22, 1), (58, 1)] }, { coefficient := 1, powers := [(12, 1), (27, 1), (50, 1)] }, { coefficient := 1, powers := [(20, 1), (22, 1), (27, 1), (52, 1)] }, { coefficient := 1, powers := [(20, 1), (32, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (41, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (44, 1), (51, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (56, 1)] }, { coefficient := 1, powers := [(12, 1), (29, 1), (44, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (51, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (27, 1), (45, 1), (52, 1)] }, { coefficient := 1, powers := [(0, 1), (41, 1), (58, 1)] }, { coefficient := 1, powers := [(3, 1), (32, 1), (58, 1)] }, { coefficient := 1, powers := [(9, 1), (21, 1), (58, 1)] }, { coefficient := 1, powers := [(9, 1), (27, 1), (45, 1)] }, { coefficient := 1, powers := [(21, 1), (27, 1), (45, 1), (52, 1)] }, { coefficient := 1, powers := [(27, 1), (41, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (38, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (41, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (44, 1), (51, 1)] }, { coefficient := 1, powers := [(3, 1), (26, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (32, 1), (56, 1)] }, { coefficient := 1, powers := [(3, 1), (35, 1), (51, 1)] }, { coefficient := 1, powers := [(6, 1), (21, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (32, 1), (44, 1)] }, { coefficient := 1, powers := [(6, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(9, 1), (21, 1), (56, 1)] }, { coefficient := 1, powers := [(9, 1), (26, 1), (44, 1)] }, { coefficient := 1, powers := [(9, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(14, 1), (21, 1), (51, 1)] }, { coefficient := 1, powers := [(14, 1), (26, 1), (41, 1)] }, { coefficient := 1, powers := [(14, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (40, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (43, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (50, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (37, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (25, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (50, 1)] }, { coefficient := 1, powers := [(8, 1), (37, 1), (43, 1)] }, { coefficient := 1, powers := [(13, 1), (25, 1), (58, 1)] }, { coefficient := 1, powers := [(13, 1), (31, 1), (50, 1)] }, { coefficient := 1, powers := [(13, 1), (37, 1), (40, 1)] }, { coefficient := 1, powers := [(20, 1), (25, 1), (55, 1)] }, { coefficient := 1, powers := [(20, 1), (31, 1), (43, 1)] }, { coefficient := 1, powers := [(20, 1), (34, 1), (40, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(41, 1)] }],
  [{ coefficient := 1, powers := [(43, 1)] }],
  [{ coefficient := 1, powers := [(56, 1), (65, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(57, 1)] }],
  [{ coefficient := 1, powers := [(58, 1), (66, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(26, 1)] }],
  [{ coefficient := 1, powers := [(28, 1), (67, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(31, 1), (68, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 47 → SparsePoly (Fin 69) := ![
  [{ coefficient := -2, powers := [(14, 1), (31, 1), (32, 1), (38, 1), (50, 1), (67, 1)] }, { coefficient := 2, powers := [(14, 1), (32, 1), (37, 1), (38, 1), (40, 1), (67, 1)] }],
  [{ coefficient := -2, powers := [(14, 1), (25, 1), (27, 1), (32, 1), (38, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (14, 1), (24, 1), (38, 1), (51, 1), (60, 1), (63, 1), (67, 1)] }, { coefficient := -2, powers := [(0, 1), (24, 1), (38, 1), (59, 1), (63, 1), (67, 1)] }, { coefficient := -2, powers := [(0, 1), (29, 1), (38, 1), (59, 1), (63, 1), (67, 1)] }, { coefficient := -1, powers := [(9, 1), (24, 1), (35, 1), (38, 1), (63, 1), (67, 1)] }, { coefficient := -1, powers := [(9, 1), (29, 1), (35, 1), (38, 1), (63, 1), (67, 1)] }, { coefficient := 2, powers := [(14, 1), (25, 1), (32, 1), (38, 1), (45, 1), (55, 1), (67, 1)] }, { coefficient := 2, powers := [(24, 1), (35, 1), (38, 1), (51, 1), (63, 1), (67, 1)] }],
  [{ coefficient := -2, powers := [(14, 1), (19, 1), (32, 1), (38, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (9, 1), (38, 1), (60, 1), (67, 1)] }, { coefficient := -2, powers := [(0, 1), (51, 1), (67, 1)] }, { coefficient := 1, powers := [(9, 1), (29, 1), (35, 1), (38, 1), (54, 1), (65, 1), (67, 1), (68, 1)] }, { coefficient := -1, powers := [(9, 1), (31, 1), (35, 1), (38, 1), (65, 1), (67, 1), (68, 1)] }, { coefficient := -2, powers := [(21, 1), (51, 1), (67, 1)] }, { coefficient := -2, powers := [(32, 1), (38, 1), (67, 1)] }],
  [{ coefficient := -2, powers := [(2, 1), (14, 1), (22, 1), (32, 1), (38, 1), (55, 1), (62, 1), (67, 1)] }, { coefficient := -2, powers := [(6, 1), (27, 1), (59, 1), (66, 1), (67, 1)] }, { coefficient := -1, powers := [(9, 1), (14, 1), (27, 1), (38, 1), (60, 1), (66, 1), (67, 1)] }, { coefficient := -1, powers := [(9, 1), (27, 1), (38, 1), (56, 1), (60, 1), (66, 1), (67, 1)] }, { coefficient := -2, powers := [(9, 1), (27, 1), (56, 1), (66, 1), (67, 1)] }, { coefficient := 2, powers := [(27, 1), (51, 1), (56, 1), (66, 1), (67, 1)] }],
  [{ coefficient := 2, powers := [(2, 1), (14, 1), (21, 1), (32, 1), (38, 1), (55, 1), (62, 1), (67, 1)] }, { coefficient := -2, powers := [(2, 1), (14, 1), (32, 1), (38, 1), (55, 1), (67, 1)] }, { coefficient := -2, powers := [(8, 1), (14, 1), (32, 1), (34, 1), (38, 1), (67, 1)] }, { coefficient := 2, powers := [(12, 1), (14, 1), (27, 1), (34, 1), (38, 1), (67, 1)] }],
  [{ coefficient := -2, powers := [(2, 1), (14, 1), (32, 1), (38, 1), (50, 1), (62, 1)] }],
  [{ coefficient := -2, powers := [(14, 1), (27, 1), (34, 1), (38, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (14, 1), (24, 1), (38, 1), (52, 1), (60, 1), (63, 1)] }, { coefficient := -2, powers := [(29, 1), (35, 1), (38, 1), (52, 1), (63, 1)] }],
  [{ coefficient := -2, powers := [(14, 1), (19, 1), (32, 1), (38, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (35, 1), (38, 1), (65, 1), (68, 1)] }],
  [{ coefficient := -2, powers := [(6, 1), (54, 1), (59, 1), (66, 1)] }, { coefficient := -1, powers := [(9, 1), (14, 1), (38, 1), (54, 1), (60, 1), (66, 1)] }, { coefficient := -1, powers := [(9, 1), (38, 1), (54, 1), (56, 1), (60, 1), (66, 1)] }, { coefficient := -2, powers := [(27, 1), (52, 1), (56, 1), (66, 1)] }, { coefficient := 2, powers := [(51, 1), (54, 1), (56, 1), (66, 1)] }],
  [{ coefficient := 2, powers := [(12, 1), (14, 1), (34, 1), (38, 1), (54, 1)] }],
  [{ coefficient := 2, powers := [(14, 1), (31, 1), (32, 1), (38, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (12, 1), (38, 1), (60, 1), (63, 1)] }, { coefficient := -2, powers := [(0, 1), (19, 1), (38, 1), (51, 1), (60, 1), (63, 1)] }, { coefficient := -1, powers := [(9, 1), (35, 1), (38, 1), (54, 1), (65, 1), (68, 1)] }],
  [{ coefficient := 2, powers := [(14, 1), (20, 1), (32, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (35, 1), (38, 1), (68, 1)] }],
  [{ coefficient := -4, powers := [(14, 1), (25, 1), (32, 1), (38, 1), (55, 1)] }, { coefficient := -2, powers := [(14, 1), (32, 1), (34, 1), (38, 1), (40, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (38, 1), (51, 1), (60, 1), (63, 1)] }],
  [{ coefficient := 2, powers := [(14, 1), (32, 1), (38, 1), (55, 1)] }],
  [{ coefficient := -2, powers := [(35, 1), (38, 1), (63, 1)] }],
  [{ coefficient := 2, powers := [(14, 1), (32, 1), (38, 1), (50, 1)] }],
  [{ coefficient := 2, powers := [(14, 1), (25, 1), (32, 1), (38, 1)] }],
  [{ coefficient := 2, powers := [(6, 1), (59, 1), (66, 1)] }, { coefficient := 1, powers := [(9, 1), (14, 1), (38, 1), (60, 1), (66, 1)] }, { coefficient := 1, powers := [(9, 1), (38, 1), (56, 1), (60, 1), (66, 1)] }, { coefficient := -2, powers := [(51, 1), (56, 1), (66, 1)] }],
  [{ coefficient := -2, powers := [(12, 1), (14, 1), (34, 1), (38, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (38, 1), (59, 1), (63, 1)] }, { coefficient := 1, powers := [(9, 1), (35, 1), (38, 1), (63, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (14, 1), (24, 1), (38, 1), (60, 1), (63, 1)] }, { coefficient := 2, powers := [(29, 1), (35, 1), (38, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(9, 1), (31, 1), (35, 1), (38, 1), (68, 1)] }, { coefficient := 1, powers := [(9, 1), (35, 1), (38, 1)] }],
  [{ coefficient := 2, powers := [(2, 1), (14, 1), (32, 1), (38, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(9, 1), (38, 1), (60, 1)] }, { coefficient := 2, powers := [(51, 1)] }],
  [{ coefficient := 2, powers := [(44, 1)] }],
  [{ coefficient := 2, powers := [(14, 1), (34, 1), (38, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (38, 1), (60, 1), (63, 1)] }],
  [{ coefficient := 2, powers := [(56, 1), (66, 1)] }],
  [{ coefficient := -2, powers := [] }],
  [{ coefficient := -2, powers := [(14, 1), (32, 1), (38, 1)] }],
  [{ coefficient := -2, powers := [(2, 1), (14, 1), (32, 1), (38, 1), (40, 1), (61, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (38, 1), (59, 1)] }, { coefficient := -1, powers := [(9, 1), (35, 1), (38, 2), (60, 1)] }, { coefficient := -1, powers := [(9, 1), (35, 1), (38, 1)] }, { coefficient := 2, powers := [(35, 1), (38, 1), (51, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (2, 1), (38, 1), (56, 1), (60, 1), (63, 1)] }, { coefficient := 2, powers := [(0, 1), (14, 1), (19, 1), (24, 1), (38, 1), (60, 1), (63, 1)] }, { coefficient := 2, powers := [(0, 1), (18, 1), (29, 1), (38, 1), (60, 1), (63, 1)] }, { coefficient := -2, powers := [(0, 1), (56, 1), (58, 1), (66, 1)] }, { coefficient := 2, powers := [(0, 1), (56, 1)] }, { coefficient := 2, powers := [(6, 1), (35, 1)] }, { coefficient := -2, powers := [(27, 1), (45, 1), (56, 1), (66, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (2, 1), (14, 1), (32, 1), (38, 1), (58, 1), (62, 1)] }, { coefficient := -2, powers := [(2, 1), (14, 1), (27, 1), (32, 1), (38, 1), (45, 1), (62, 1)] }, { coefficient := 2, powers := [(2, 1), (14, 1), (32, 1), (38, 1), (58, 1)] }, { coefficient := 2, powers := [(8, 1), (14, 1), (32, 1), (37, 1), (38, 1)] }, { coefficient := -2, powers := [(14, 1), (20, 1), (31, 1), (32, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (24, 1), (35, 1), (38, 1), (54, 1), (68, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (12, 1), (14, 1), (21, 1), (24, 1), (38, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(9, 1), (21, 1), (31, 1), (35, 1), (38, 1), (68, 1)] }, { coefficient := -1, powers := [(9, 1), (21, 1), (35, 1), (38, 1)] }, { coefficient := -2, powers := [(12, 1), (21, 1), (29, 1), (35, 1), (38, 1), (63, 1)] }],
  [{ coefficient := -2, powers := [(3, 1), (32, 1), (56, 1)] }, { coefficient := -2, powers := [(6, 1), (21, 1), (59, 1)] }, { coefficient := -1, powers := [(9, 1), (14, 1), (21, 1), (38, 1), (60, 1)] }, { coefficient := -1, powers := [(9, 1), (21, 1), (38, 1), (56, 1), (60, 1)] }, { coefficient := -2, powers := [(9, 1), (21, 1), (56, 1)] }, { coefficient := 2, powers := [(21, 1), (51, 1), (56, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (14, 1), (19, 1), (24, 1), (38, 1), (52, 1), (60, 1), (63, 1)] }, { coefficient := 2, powers := [(3, 1), (59, 1)] }, { coefficient := 2, powers := [(6, 1), (45, 1), (54, 1), (59, 1), (66, 1)] }, { coefficient := 1, powers := [(9, 1), (14, 1), (38, 1), (45, 1), (54, 1), (60, 1), (66, 1)] }, { coefficient := 1, powers := [(9, 1), (38, 1), (44, 1), (60, 1)] }, { coefficient := 1, powers := [(9, 1), (38, 1), (45, 1), (54, 1), (56, 1), (60, 1), (66, 1)] }, { coefficient := -2, powers := [(12, 1), (14, 1), (34, 1), (38, 1), (50, 1), (54, 1)] }, { coefficient := 4, powers := [(14, 1), (19, 1), (25, 1), (32, 1), (38, 1), (48, 1), (55, 1)] }, { coefficient := 2, powers := [(14, 1), (19, 1), (32, 1), (34, 1), (38, 1), (40, 1), (48, 1)] }, { coefficient := 4, powers := [(14, 1), (20, 1), (25, 1), (32, 1), (38, 1), (42, 1), (55, 1)] }, { coefficient := 2, powers := [(14, 1), (20, 1), (32, 1), (34, 1), (38, 1), (40, 1), (42, 1)] }, { coefficient := 2, powers := [(14, 1), (41, 1)] }, { coefficient := 2, powers := [(19, 1), (29, 1), (35, 1), (38, 1), (52, 1), (63, 1)] }, { coefficient := 2, powers := [(27, 1), (45, 1), (52, 1), (56, 1), (66, 1)] }, { coefficient := -2, powers := [(41, 1), (44, 1)] }, { coefficient := -2, powers := [(44, 1), (51, 1)] }, { coefficient := -2, powers := [(45, 1), (51, 1), (54, 1), (56, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (9, 1), (38, 1), (44, 1), (60, 1)] }, { coefficient := -2, powers := [(0, 1), (14, 1), (19, 1), (24, 1), (38, 1), (51, 1), (60, 1), (63, 1)] }, { coefficient := 2, powers := [(0, 1), (19, 1), (24, 1), (38, 1), (59, 1), (63, 1)] }, { coefficient := 2, powers := [(0, 1), (19, 1), (29, 1), (38, 1), (59, 1), (63, 1)] }, { coefficient := 2, powers := [(0, 1), (44, 1), (51, 1)] }, { coefficient := -2, powers := [(2, 1), (14, 1), (21, 1), (32, 1), (38, 1), (50, 1), (55, 1), (62, 1)] }, { coefficient := 2, powers := [(2, 1), (14, 1), (22, 1), (32, 1), (38, 1), (45, 1), (55, 1), (62, 1)] }, { coefficient := 2, powers := [(2, 1), (14, 1), (32, 1), (38, 1), (50, 1), (55, 1)] }, { coefficient := 2, powers := [(6, 1), (27, 1), (45, 1), (59, 1), (66, 1)] }, { coefficient := 2, powers := [(8, 1), (14, 1), (32, 1), (34, 1), (38, 1), (50, 1)] }, { coefficient := 1, powers := [(9, 1), (14, 1), (27, 1), (38, 1), (45, 1), (60, 1), (66, 1)] }, { coefficient := 1, powers := [(9, 1), (19, 1), (24, 1), (35, 1), (38, 1), (63, 1)] }, { coefficient := 1, powers := [(9, 1), (19, 1), (29, 1), (35, 1), (38, 1), (63, 1)] }, { coefficient := 1, powers := [(9, 1), (27, 1), (38, 1), (45, 1), (56, 1), (60, 1), (66, 1)] }, { coefficient := 2, powers := [(9, 1), (27, 1), (45, 1), (56, 1), (66, 1)] }, { coefficient := -1, powers := [(9, 1), (29, 1), (35, 1), (38, 1), (44, 1), (54, 1), (65, 1), (68, 1)] }, { coefficient := 1, powers := [(9, 1), (31, 1), (35, 1), (38, 1), (44, 1), (65, 1), (68, 1)] }, { coefficient := -2, powers := [(12, 1), (14, 1), (27, 1), (34, 1), (38, 1), (50, 1)] }, { coefficient := 2, powers := [(13, 1), (14, 1), (31, 1), (32, 1), (38, 1), (50, 1)] }, { coefficient := -2, powers := [(13, 1), (14, 1), (32, 1), (37, 1), (38, 1), (40, 1)] }, { coefficient := -2, powers := [(14, 1), (19, 1), (25, 1), (32, 1), (38, 1), (45, 1), (55, 1)] }, { coefficient := -2, powers := [(19, 1), (24, 1), (35, 1), (38, 1), (51, 1), (63, 1)] }, { coefficient := 2, powers := [(21, 1), (44, 1), (51, 1)] }, { coefficient := -2, powers := [(27, 1), (45, 1), (51, 1), (56, 1), (66, 1)] }, { coefficient := 2, powers := [(32, 1), (38, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (9, 1), (35, 1), (38, 1), (53, 1)] }, { coefficient := 1, powers := [(9, 1), (21, 1), (35, 1), (38, 1), (53, 1)] }]
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
    (values : Fin 69 → R) :
    ¬ ∀ index : Fin 47,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((2 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (2 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (2 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component16.SelectedLeafB5_2_5_3.selectedHasNoCommonZero

end Krenn.Component16.SelectedLeafB5_2_5_3
