import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component60.SelectedLeafB6_3_3

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "cb5fceaac8d59c40e8cc1cdf4e312682180bb6c8860f17f0e99b76554a7ab910"
def certificateSHA256 : String := "fa9197ffc9ebf82ba7a86cd94277ec3e42cb425ddd75b85306919d855952e37d"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 56 → Fin 665 := ![
  9,
  13,
  21,
  22,
  25,
  45,
  143,
  145,
  150,
  165,
  167,
  168,
  172,
  178,
  179,
  198,
  211,
  264,
  272,
  292,
  293,
  294,
  295,
  298,
  301,
  302,
  303,
  407,
  424,
  425,
  433,
  434,
  436,
  442,
  443,
  464,
  469,
  470,
  556,
  587,
  592,
  593,
  600,
  601,
  612,
  621,
  653,
  655,
  656,
  657,
  658,
  659,
  660,
  662,
  663,
  664
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 56 → SparsePoly (Fin 67) := ![
  [{ coefficient := 1, powers := [(9, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(15, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (35, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (47, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (53, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (26, 1)] }, { coefficient := 1, powers := [(26, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (26, 1)] }, { coefficient := 1, powers := [(18, 1), (20, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (43, 1)] }, { coefficient := 1, powers := [(19, 1), (20, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (46, 1)] }, { coefficient := 1, powers := [(19, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (20, 1)] }, { coefficient := 1, powers := [(18, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (53, 1)] }, { coefficient := 1, powers := [(29, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (40, 1)] }, { coefficient := 1, powers := [(29, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (24, 1), (59, 1)] }, { coefficient := 1, powers := [(24, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (26, 1), (46, 1)] }, { coefficient := 1, powers := [(9, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (25, 1), (48, 1)] }, { coefficient := 1, powers := [(19, 1), (21, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (50, 1), (56, 1)] }, { coefficient := 1, powers := [(24, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1)] }, { coefficient := 1, powers := [(20, 1), (43, 1)] }, { coefficient := 1, powers := [(25, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (48, 1)] }, { coefficient := 1, powers := [(21, 1), (43, 1)] }, { coefficient := 1, powers := [(25, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (50, 1)] }, { coefficient := 1, powers := [(20, 1), (50, 1)] }, { coefficient := 1, powers := [(25, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (54, 1)] }, { coefficient := 1, powers := [(20, 1), (54, 1)] }, { coefficient := 1, powers := [(26, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (49, 1)] }, { coefficient := 1, powers := [(15, 1), (22, 1), (49, 1)] }, { coefficient := 1, powers := [(15, 1), (27, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (48, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1)] }, { coefficient := 1, powers := [(12, 1), (29, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (58, 1)] }, { coefficient := 1, powers := [(9, 1), (42, 1)] }, { coefficient := 1, powers := [(13, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (20, 1), (49, 1)] }, { coefficient := 1, powers := [(19, 1), (25, 1), (39, 1)] }, { coefficient := 1, powers := [(19, 1), (30, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (52, 1)] }, { coefficient := 1, powers := [(20, 1), (50, 1), (56, 1)] }, { coefficient := 1, powers := [(20, 1), (52, 1)] }, { coefficient := 1, powers := [(50, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (53, 1)] }, { coefficient := 1, powers := [(3, 1), (26, 1), (59, 1)] }, { coefficient := 1, powers := [(20, 1), (53, 1)] }, { coefficient := 1, powers := [(26, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (59, 1)] }, { coefficient := 1, powers := [(18, 1), (21, 1), (51, 1)] }, { coefficient := 1, powers := [(18, 1), (21, 1), (56, 1)] }, { coefficient := 1, powers := [(18, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (60, 1)] }, { coefficient := 1, powers := [(12, 1), (48, 1)] }, { coefficient := 1, powers := [(19, 1), (21, 1), (52, 1)] }, { coefficient := 1, powers := [(19, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (60, 1)] }, { coefficient := 1, powers := [(12, 1), (26, 1), (46, 1)] }, { coefficient := 1, powers := [(12, 1), (57, 1)] }, { coefficient := 1, powers := [(19, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (40, 1)] }, { coefficient := 1, powers := [(18, 1), (45, 1)] }, { coefficient := 1, powers := [(18, 1), (51, 1)] }, { coefficient := 1, powers := [(18, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (54, 1)] }, { coefficient := 1, powers := [(29, 1), (41, 1)] }, { coefficient := 1, powers := [(29, 1), (47, 1), (50, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1), (54, 1)] }, { coefficient := 1, powers := [(26, 1), (46, 1), (50, 1)] }, { coefficient := 1, powers := [(43, 1), (54, 1)] }, { coefficient := 1, powers := [(50, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (48, 1), (49, 1)] }, { coefficient := 1, powers := [(6, 1), (30, 1), (48, 1)] }, { coefficient := 1, powers := [(9, 1), (25, 1), (48, 1)] }, { coefficient := 1, powers := [(21, 1), (43, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (48, 1), (52, 1)] }, { coefficient := 1, powers := [(21, 1), (43, 1), (52, 1)] }, { coefficient := 1, powers := [(41, 1), (43, 1)] }, { coefficient := 1, powers := [(48, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (43, 1), (53, 1)] }, { coefficient := 1, powers := [(24, 1), (57, 1)] }, { coefficient := 1, powers := [(29, 1), (48, 1)] }, { coefficient := 1, powers := [(35, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (36, 1), (58, 1)] }, { coefficient := 1, powers := [(1, 1), (39, 1), (55, 1)] }, { coefficient := 1, powers := [(1, 1), (42, 1), (49, 1)] }, { coefficient := 1, powers := [(14, 1), (22, 1), (49, 1)] }, { coefficient := 1, powers := [(14, 1), (27, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (46, 1), (53, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (40, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (46, 1)] }, { coefficient := 1, powers := [(19, 1), (29, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (41, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (47, 1), (52, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (56, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (56, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1)] }, { coefficient := 1, powers := [(3, 1), (33, 1)] }, { coefficient := 1, powers := [(13, 1), (20, 1)] }, { coefficient := 1, powers := [(20, 1), (55, 1)] }, { coefficient := 1, powers := [(25, 1), (42, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (49, 1)] }, { coefficient := 1, powers := [(6, 1), (30, 1)] }, { coefficient := 1, powers := [(9, 1), (25, 1)] }, { coefficient := 1, powers := [(20, 1), (49, 1)] }, { coefficient := 1, powers := [(25, 1), (39, 1)] }, { coefficient := 1, powers := [(30, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1), (49, 1)] }, { coefficient := 1, powers := [(6, 1), (30, 1), (44, 1)] }, { coefficient := 1, powers := [(6, 1), (58, 1)] }, { coefficient := 1, powers := [(9, 1), (25, 1), (44, 1)] }, { coefficient := 1, powers := [(9, 1), (55, 1)] }, { coefficient := 1, powers := [(13, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (47, 1), (53, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (59, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (59, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (53, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (36, 1), (58, 1)] }, { coefficient := 1, powers := [(0, 1), (39, 1), (55, 1)] }, { coefficient := 1, powers := [(0, 1), (42, 1), (49, 1)] }, { coefficient := 1, powers := [(3, 1), (25, 1), (58, 1)] }, { coefficient := 1, powers := [(3, 1), (30, 1), (55, 1)] }, { coefficient := 1, powers := [(3, 1), (33, 1), (49, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1), (58, 1)] }, { coefficient := 1, powers := [(6, 1), (30, 1), (42, 1)] }, { coefficient := 1, powers := [(6, 1), (33, 1), (39, 1)] }, { coefficient := 1, powers := [(9, 1), (20, 1), (55, 1)] }, { coefficient := 1, powers := [(9, 1), (25, 1), (42, 1)] }, { coefficient := 1, powers := [(9, 1), (33, 1), (36, 1)] }, { coefficient := 1, powers := [(13, 1), (20, 1), (49, 1)] }, { coefficient := 1, powers := [(13, 1), (25, 1), (39, 1)] }, { coefficient := 1, powers := [(13, 1), (30, 1), (36, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (41, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (48, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (48, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1), (29, 1), (48, 1)] }, { coefficient := 1, powers := [(12, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (54, 1)] }, { coefficient := 1, powers := [(19, 1), (29, 1), (41, 1)] }, { coefficient := 1, powers := [(19, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (61, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(39, 1)] }],
  [{ coefficient := 1, powers := [(40, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(55, 1)] }],
  [{ coefficient := 1, powers := [(56, 1), (65, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(57, 1), (66, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 56 → SparsePoly (Fin 67) := ![
  [{ coefficient := 2, powers := [(12, 1), (25, 1), (29, 1), (42, 1)] }, { coefficient := -2, powers := [(12, 1), (29, 1), (33, 1), (36, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (14, 1), (19, 1), (22, 2), (29, 1), (41, 1), (62, 2)] }, { coefficient := -2, powers := [(0, 1), (19, 1), (22, 1), (29, 1), (41, 1), (42, 1), (62, 1)] }, { coefficient := -4, powers := [(12, 1), (13, 1), (20, 1), (22, 1), (29, 1), (48, 1), (62, 1)] }, { coefficient := 2, powers := [(12, 1), (13, 1), (21, 1), (22, 1), (29, 1), (43, 1), (62, 1)] }, { coefficient := 2, powers := [(12, 1), (14, 1), (21, 1), (22, 2), (29, 1), (43, 1), (62, 2)] }, { coefficient := 2, powers := [(12, 1), (14, 1), (22, 2), (25, 1), (29, 1), (48, 1), (62, 2)] }, { coefficient := 2, powers := [(12, 1), (20, 1), (21, 1), (22, 1), (29, 1), (43, 1), (44, 1), (62, 1)] }, { coefficient := 2, powers := [(12, 1), (21, 1), (22, 1), (29, 1), (42, 1), (43, 1), (62, 1)] }, { coefficient := 2, powers := [(12, 1), (22, 1), (25, 1), (29, 1), (42, 1), (48, 1), (62, 1)] }, { coefficient := -2, powers := [(12, 1), (22, 1), (29, 1), (33, 1), (36, 1), (48, 1), (62, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (29, 1), (41, 1), (42, 1)] }, { coefficient := 4, powers := [(13, 1), (20, 1), (29, 1), (41, 1)] }, { coefficient := 2, powers := [(25, 1), (29, 1), (41, 1), (42, 1)] }, { coefficient := 2, powers := [(29, 1), (33, 1), (36, 1), (41, 1)] }],
  [{ coefficient := -3, powers := [(12, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (47, 1)] }],
  [{ coefficient := -2, powers := [(5, 1), (26, 1), (59, 1)] }],
  [{ coefficient := 2, powers := [(6, 1), (53, 1), (60, 1)] }, { coefficient := -1, powers := [(52, 1), (57, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(41, 1), (46, 1), (63, 1)] }],
  [{ coefficient := -2, powers := [(19, 1), (25, 1), (29, 1), (41, 1), (42, 1), (46, 1), (66, 1)] }, { coefficient := 2, powers := [(19, 1), (29, 1), (33, 1), (36, 1), (41, 1), (46, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(24, 1), (46, 1)] }],
  [{ coefficient := 2, powers := [(24, 1), (53, 1)] }],
  [{ coefficient := 2, powers := [(24, 1), (26, 1)] }],
  [{ coefficient := -1, powers := [(24, 1), (43, 1), (54, 1), (61, 1)] }, { coefficient := -1, powers := [(24, 1), (50, 1), (57, 1), (61, 1)] }, { coefficient := -1, powers := [(29, 1), (41, 1), (43, 1), (61, 1)] }, { coefficient := -1, powers := [(29, 1), (48, 1), (50, 1), (61, 1)] }],
  [{ coefficient := -2, powers := [(19, 1), (50, 1)] }],
  [{ coefficient := 2, powers := [(6, 1), (18, 1), (21, 1), (60, 1)] }],
  [{ coefficient := 2, powers := [(8, 1), (60, 1)] }],
  [{ coefficient := 2, powers := [(19, 1), (25, 1), (29, 1), (41, 1), (42, 1), (66, 1)] }, { coefficient := -2, powers := [(19, 1), (29, 1), (33, 1), (36, 1), (41, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(29, 1), (52, 1)] }],
  [{ coefficient := -2, powers := [(19, 1), (20, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (24, 1), (54, 1), (61, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (41, 1), (61, 1)] }],
  [{ coefficient := -2, powers := [(12, 1), (29, 1), (36, 1), (58, 1)] }, { coefficient := 2, powers := [(12, 1), (29, 1), (42, 1), (49, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (24, 1), (57, 1), (61, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (48, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (24, 1), (46, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (14, 1), (19, 1), (22, 1), (29, 1), (41, 1), (62, 2)] }, { coefficient := 2, powers := [(0, 1), (19, 1), (29, 1), (41, 1), (42, 1), (62, 1)] }, { coefficient := 4, powers := [(12, 1), (13, 1), (20, 1), (29, 1), (48, 1), (62, 1)] }, { coefficient := -2, powers := [(12, 1), (13, 1), (21, 1), (29, 1), (43, 1), (62, 1)] }, { coefficient := -2, powers := [(12, 1), (14, 1), (21, 1), (22, 1), (29, 1), (43, 1), (62, 2)] }, { coefficient := -2, powers := [(12, 1), (14, 1), (22, 1), (25, 1), (29, 1), (48, 1), (62, 2)] }, { coefficient := -2, powers := [(12, 1), (20, 1), (21, 1), (29, 1), (43, 1), (44, 1), (62, 1)] }, { coefficient := -2, powers := [(12, 1), (21, 1), (29, 1), (42, 1), (43, 1), (62, 1)] }, { coefficient := -2, powers := [(12, 1), (25, 1), (29, 1), (42, 1), (48, 1), (62, 1)] }, { coefficient := 2, powers := [(12, 1), (29, 1), (33, 1), (36, 1), (48, 1), (62, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (52, 1), (53, 1)] }, { coefficient := -2, powers := [(20, 1), (52, 1), (53, 1)] }, { coefficient := -2, powers := [(26, 1), (52, 1)] }, { coefficient := 1, powers := [(54, 1)] }],
  [{ coefficient := 1, powers := [(48, 1)] }],
  [{ coefficient := -2, powers := [(12, 1), (25, 1), (29, 1), (48, 1)] }, { coefficient := -2, powers := [(19, 1), (25, 1), (29, 1), (41, 1)] }],
  [{ coefficient := -2, powers := [(13, 1), (29, 1), (41, 1)] }, { coefficient := -2, powers := [(20, 1), (29, 1), (41, 1), (44, 1)] }, { coefficient := 2, powers := [(29, 1), (41, 1), (42, 1)] }],
  [{ coefficient := 2, powers := [(19, 1), (24, 1), (53, 1)] }],
  [{ coefficient := 2, powers := [(5, 1), (35, 1), (52, 1)] }],
  [{ coefficient := 2, powers := [(6, 1), (29, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(29, 1)] }],
  [{ coefficient := -1, powers := [(24, 1)] }],
  [{ coefficient := -2, powers := [(6, 1), (21, 1), (29, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(19, 1)] }],
  [{ coefficient := -1, powers := [(18, 1), (24, 1)] }],
  [{ coefficient := 2, powers := [(12, 1), (13, 1), (29, 1)] }, { coefficient := 2, powers := [(12, 1), (20, 1), (29, 1), (44, 1)] }, { coefficient := -2, powers := [(12, 1), (29, 1), (42, 1)] }],
  [{ coefficient := -1, powers := [(18, 1), (29, 1)] }],
  [{ coefficient := 1, powers := [(12, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (19, 1), (29, 1), (41, 1), (62, 1)] }, { coefficient := 2, powers := [(12, 1), (21, 1), (29, 1), (43, 1), (62, 1)] }, { coefficient := 2, powers := [(12, 1), (25, 1), (29, 1), (48, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(41, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(57, 1), (65, 1)] }],
  [{ coefficient := -2, powers := [(12, 1), (29, 1), (48, 1), (49, 1)] }, { coefficient := -2, powers := [(19, 1), (29, 1), (41, 1), (49, 1)] }],
  [{ coefficient := -2, powers := [(12, 1), (13, 1), (29, 1), (48, 1)] }, { coefficient := 2, powers := [(19, 1), (20, 1), (29, 1), (41, 1), (44, 1)] }, { coefficient := -2, powers := [(19, 1), (29, 1), (41, 1), (42, 1)] }],
  [{ coefficient := -2, powers := [(12, 1), (20, 1), (29, 1), (48, 1)] }, { coefficient := -2, powers := [(19, 1), (20, 1), (29, 1), (41, 1)] }],
  [{ coefficient := -2, powers := [(6, 1), (60, 1)] }],
  [{ coefficient := 2, powers := [(12, 1), (29, 1), (48, 1)] }, { coefficient := 2, powers := [(19, 1), (29, 1), (41, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(18, 1), (24, 1), (43, 1), (54, 1)] }, { coefficient := -1, powers := [(18, 1), (24, 1), (50, 1), (57, 1)] }, { coefficient := -1, powers := [(18, 1), (29, 1), (41, 1), (43, 1)] }, { coefficient := -1, powers := [(18, 1), (29, 1), (48, 1), (50, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (14, 1), (19, 1), (22, 1), (29, 1), (41, 1), (49, 1), (62, 1)] }, { coefficient := 2, powers := [(0, 1), (19, 1), (29, 1), (36, 1), (41, 1), (58, 1)] }, { coefficient := -4, powers := [(12, 1), (13, 1), (20, 1), (29, 1), (48, 1), (49, 1)] }, { coefficient := 2, powers := [(12, 1), (13, 1), (21, 1), (29, 1), (43, 1), (49, 1)] }, { coefficient := 2, powers := [(12, 1), (14, 1), (21, 1), (22, 1), (29, 1), (43, 1), (49, 1), (62, 1)] }, { coefficient := 2, powers := [(12, 1), (14, 1), (22, 1), (25, 1), (29, 1), (48, 1), (49, 1), (62, 1)] }, { coefficient := 2, powers := [(12, 1), (20, 1), (21, 1), (29, 1), (43, 1), (44, 1), (49, 1)] }, { coefficient := -2, powers := [(12, 1), (21, 1), (29, 1), (36, 1), (43, 1), (58, 1)] }, { coefficient := -2, powers := [(12, 1), (25, 1), (29, 1), (36, 1), (48, 1), (58, 1)] }, { coefficient := -2, powers := [(12, 1), (29, 1), (33, 1), (36, 1), (48, 1), (49, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (48, 1), (52, 1), (53, 1)] }, { coefficient := 2, powers := [(6, 1), (38, 1), (59, 1), (60, 1)] }, { coefficient := 2, powers := [(20, 1), (48, 1), (52, 1), (53, 1)] }, { coefficient := 2, powers := [(26, 1), (48, 1), (52, 1)] }, { coefficient := 1, powers := [(38, 1), (60, 1)] }, { coefficient := -1, powers := [(40, 1), (41, 1), (57, 1), (63, 1)] }, { coefficient := -1, powers := [(41, 1), (56, 1), (57, 1), (65, 1)] }, { coefficient := 1, powers := [(41, 1), (57, 1)] }, { coefficient := -1, powers := [(48, 1), (54, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (1, 1), (19, 1), (29, 1), (41, 1), (55, 1), (62, 1)] }, { coefficient := -2, powers := [(0, 1), (12, 1), (29, 1), (48, 1), (55, 1)] }, { coefficient := -2, powers := [(0, 1), (14, 1), (15, 1), (19, 1), (22, 1), (27, 1), (29, 1), (41, 1), (62, 2)] }, { coefficient := 2, powers := [(0, 1), (14, 1), (19, 1), (27, 1), (29, 1), (41, 1), (62, 1)] }, { coefficient := -2, powers := [(0, 1), (15, 1), (19, 1), (27, 1), (29, 1), (41, 1), (42, 1), (62, 1)] }, { coefficient := -2, powers := [(0, 1), (19, 1), (29, 1), (41, 1), (55, 1)] }, { coefficient := -2, powers := [(1, 1), (12, 1), (21, 1), (29, 1), (43, 1), (55, 1), (62, 1)] }, { coefficient := -2, powers := [(1, 1), (12, 1), (25, 1), (29, 1), (48, 1), (55, 1), (62, 1)] }, { coefficient := -2, powers := [(6, 1), (12, 1), (29, 1), (33, 1), (48, 1)] }, { coefficient := -2, powers := [(6, 1), (19, 1), (29, 1), (33, 1), (41, 1)] }, { coefficient := -4, powers := [(12, 1), (13, 1), (15, 1), (20, 1), (27, 1), (29, 1), (48, 1), (62, 1)] }, { coefficient := 2, powers := [(12, 1), (13, 1), (15, 1), (21, 1), (27, 1), (29, 1), (43, 1), (62, 1)] }, { coefficient := 2, powers := [(12, 1), (13, 1), (25, 1), (29, 1), (48, 1)] }, { coefficient := 2, powers := [(12, 1), (14, 1), (15, 1), (21, 1), (22, 1), (27, 1), (29, 1), (43, 1), (62, 2)] }, { coefficient := 2, powers := [(12, 1), (14, 1), (15, 1), (22, 1), (25, 1), (27, 1), (29, 1), (48, 1), (62, 2)] }, { coefficient := -2, powers := [(12, 1), (14, 1), (21, 1), (27, 1), (29, 1), (43, 1), (62, 1)] }, { coefficient := -2, powers := [(12, 1), (14, 1), (25, 1), (27, 1), (29, 1), (48, 1), (62, 1)] }, { coefficient := 2, powers := [(12, 1), (15, 1), (20, 1), (21, 1), (27, 1), (29, 1), (43, 1), (44, 1), (62, 1)] }, { coefficient := 2, powers := [(12, 1), (15, 1), (21, 1), (27, 1), (29, 1), (42, 1), (43, 1), (62, 1)] }, { coefficient := 2, powers := [(12, 1), (15, 1), (25, 1), (27, 1), (29, 1), (42, 1), (48, 1), (62, 1)] }, { coefficient := -2, powers := [(12, 1), (15, 1), (27, 1), (29, 1), (33, 1), (36, 1), (48, 1), (62, 1)] }, { coefficient := 2, powers := [(13, 1), (19, 1), (25, 1), (29, 1), (41, 1)] }, { coefficient := 2, powers := [(19, 1), (25, 1), (26, 1), (29, 1), (41, 1), (42, 1), (46, 1), (66, 1)] }, { coefficient := -2, powers := [(19, 1), (26, 1), (29, 1), (33, 1), (36, 1), (41, 1), (46, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (35, 1), (41, 1)] }, { coefficient := -1, powers := [(19, 1), (29, 1), (41, 1)] }],
  [{ coefficient := -2, powers := [(3, 1), (12, 1), (29, 1), (30, 1), (48, 1)] }, { coefficient := -2, powers := [(3, 1), (19, 1), (29, 1), (30, 1), (41, 1)] }, { coefficient := 2, powers := [(12, 1), (20, 1), (29, 1), (48, 1), (49, 1)] }, { coefficient := 2, powers := [(19, 1), (20, 1), (29, 1), (41, 1), (49, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (32, 1), (57, 1)] }, { coefficient := -1, powers := [(12, 1), (24, 1), (57, 1)] }],
  [{ coefficient := -2, powers := [(9, 1), (19, 1), (25, 1), (29, 1), (41, 1), (42, 1)] }, { coefficient := 2, powers := [(9, 1), (19, 1), (29, 1), (33, 1), (36, 1), (41, 1)] }]
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
    ¬ ∀ index : Fin 56,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component60.SelectedLeafB6_3_3.selectedHasNoCommonZero

end Krenn.Component60.SelectedLeafB6_3_3
