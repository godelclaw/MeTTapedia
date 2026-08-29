import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component37.SelectedLeafB0_3_0

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "3650999451f0bdc3005ea2bfc29c73daa54d587217b160ed72bca948d7a7d57e"
def certificateSHA256 : String := "3d89a9995757b44ee1902427a588b255f331a824b866689d6394b50345744611"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 68 → Fin 667 := ![
  9,
  14,
  17,
  22,
  27,
  171,
  175,
  177,
  178,
  179,
  180,
  181,
  182,
  183,
  256,
  285,
  298,
  299,
  301,
  307,
  310,
  311,
  312,
  316,
  393,
  406,
  411,
  413,
  431,
  433,
  437,
  438,
  446,
  450,
  454,
  458,
  471,
  479,
  487,
  496,
  556,
  566,
  567,
  570,
  583,
  590,
  594,
  602,
  603,
  604,
  605,
  609,
  612,
  625,
  645,
  649,
  655,
  656,
  657,
  658,
  659,
  660,
  661,
  662,
  663,
  664,
  665,
  666
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 68 → SparsePoly (Fin 64) := ![
  [{ coefficient := 1, powers := [(12, 1), (27, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (22, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (20, 1)] }, { coefficient := 1, powers := [(18, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (49, 1)] }, { coefficient := 1, powers := [(19, 1), (21, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (47, 1)] }, { coefficient := -1, powers := [(29, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (55, 1)] }, { coefficient := 1, powers := [(30, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (44, 1)] }, { coefficient := 1, powers := [(28, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (54, 1)] }, { coefficient := 1, powers := [(30, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (42, 1)] }, { coefficient := 1, powers := [(27, 1), (48, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(28, 1), (53, 1)] }, { coefficient := -1, powers := [(29, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (25, 1), (46, 1)] }, { coefficient := 1, powers := [(18, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(29, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (46, 1)] }, { coefficient := 1, powers := [(4, 1), (35, 1)] }, { coefficient := 1, powers := [(15, 1), (22, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (52, 1)] }, { coefficient := 1, powers := [(7, 1), (32, 1)] }, { coefficient := 1, powers := [(10, 1), (27, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (59, 1)] }, { coefficient := 1, powers := [(9, 1), (43, 1)] }, { coefficient := 1, powers := [(13, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (46, 1)] }, { coefficient := 1, powers := [(12, 1), (57, 1)] }, { coefficient := 1, powers := [(18, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (41, 1)] }, { coefficient := 1, powers := [(19, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (52, 1)] }, { coefficient := 1, powers := [(24, 1), (57, 1)] }, { coefficient := 1, powers := [(29, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (54, 1)] }, { coefficient := 1, powers := [(30, 1), (41, 1)] }, { coefficient := 1, powers := [(30, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1), (55, 1)] }, { coefficient := 1, powers := [(26, 1), (46, 1), (51, 1)] }, { coefficient := 1, powers := [(55, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (20, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1)] }, { coefficient := 1, powers := [(18, 1), (20, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (20, 1), (50, 1)] }, { coefficient := 1, powers := [(18, 1), (25, 1), (40, 1)] }, { coefficient := 1, powers := [(18, 1), (31, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (25, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (25, 1), (41, 1)] }, { coefficient := 1, powers := [(19, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (44, 1), (53, 1)] }, { coefficient := 1, powers := [(29, 1), (42, 1), (44, 1)] }, { coefficient := 1, powers := [(29, 1), (49, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (47, 1)] }, { coefficient := 1, powers := [(18, 1), (28, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (28, 1), (41, 1)] }, { coefficient := 1, powers := [(19, 1), (29, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (49, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1)] }, { coefficient := 1, powers := [(18, 1), (28, 1), (49, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (23, 1), (60, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (54, 1)] }, { coefficient := 1, powers := [(18, 1), (30, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1)] }, { coefficient := 1, powers := [(12, 1), (30, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (61, 1)] }, { coefficient := 1, powers := [(12, 1), (49, 1)] }, { coefficient := 1, powers := [(19, 1), (21, 1), (53, 1)] }, { coefficient := 1, powers := [(19, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (61, 1)] }, { coefficient := 1, powers := [(12, 1), (26, 1), (47, 1)] }, { coefficient := 1, powers := [(12, 1), (58, 1)] }, { coefficient := 1, powers := [(19, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (55, 1)] }, { coefficient := 1, powers := [(30, 1), (42, 1)] }, { coefficient := 1, powers := [(30, 1), (48, 1), (51, 1)] }, { coefficient := 1, powers := [(33, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (38, 1), (61, 1)] }, { coefficient := 1, powers := [(0, 1), (47, 1), (53, 1)] }, { coefficient := 1, powers := [(44, 1), (53, 1)] }, { coefficient := 1, powers := [(47, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1), (53, 1)] }, { coefficient := 1, powers := [(46, 1), (51, 1)] }, { coefficient := 1, powers := [(51, 1), (57, 1)] }, { coefficient := 1, powers := [(53, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (48, 1), (52, 1)] }, { coefficient := 1, powers := [(21, 1), (52, 1)] }, { coefficient := 1, powers := [(21, 1), (57, 1)] }, { coefficient := 1, powers := [(48, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (37, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1)] }, { coefficient := 1, powers := [(18, 1), (28, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (48, 1), (51, 1)] }, { coefficient := 1, powers := [(12, 1), (28, 1), (48, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (51, 1)] }, { coefficient := 1, powers := [(18, 1), (28, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (22, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1), (27, 1), (46, 1)] }, { coefficient := 1, powers := [(12, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(18, 1), (22, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (44, 1), (54, 1)] }, { coefficient := 1, powers := [(24, 1), (58, 1)] }, { coefficient := 1, powers := [(30, 1), (49, 1)] }, { coefficient := 1, powers := [(36, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (51, 1), (57, 1)] }, { coefficient := 1, powers := [(24, 1), (53, 1)] }, { coefficient := 1, powers := [(29, 1), (42, 1)] }, { coefficient := 1, powers := [(29, 1), (48, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (44, 1), (54, 1)] }, { coefficient := 1, powers := [(29, 1), (58, 1)] }, { coefficient := 1, powers := [(30, 1), (41, 1), (44, 1)] }, { coefficient := 1, powers := [(30, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (31, 1), (57, 1)] }, { coefficient := 1, powers := [(9, 1), (20, 1), (57, 1)] }, { coefficient := 1, powers := [(9, 1)] }, { coefficient := 1, powers := [(40, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (42, 1), (57, 1)] }, { coefficient := 1, powers := [(1, 1), (48, 1), (53, 1)] }, { coefficient := 1, powers := [(7, 1), (35, 1), (42, 1)] }, { coefficient := 1, powers := [(11, 1), (27, 1), (48, 1)] }, { coefficient := 1, powers := [(15, 1), (27, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (46, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (29, 1), (60, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (54, 1)] }, { coefficient := 1, powers := [(18, 1), (30, 1), (41, 1)] }, { coefficient := 1, powers := [(18, 1), (30, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1)] }, { coefficient := 1, powers := [(3, 1), (34, 1)] }, { coefficient := 1, powers := [(13, 1), (20, 1)] }, { coefficient := 1, powers := [(20, 1), (56, 1)] }, { coefficient := 1, powers := [(25, 1), (43, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (50, 1)] }, { coefficient := 1, powers := [(6, 1), (31, 1)] }, { coefficient := 1, powers := [(9, 1), (25, 1)] }, { coefficient := 1, powers := [(20, 1), (50, 1)] }, { coefficient := 1, powers := [(25, 1), (40, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (60, 1)] }, { coefficient := 1, powers := [(10, 1), (46, 1)] }, { coefficient := 1, powers := [(10, 1), (57, 1)] }, { coefficient := 1, powers := [(15, 1), (41, 1)] }, { coefficient := 1, powers := [(15, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (52, 1)] }, { coefficient := 1, powers := [(22, 1), (57, 1)] }, { coefficient := 1, powers := [(27, 1), (41, 1)] }, { coefficient := 1, powers := [(27, 1), (46, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1)] }, { coefficient := 1, powers := [(35, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (48, 1), (53, 1)] }, { coefficient := 1, powers := [(21, 1), (51, 1), (57, 1)] }, { coefficient := 1, powers := [(21, 1), (53, 1)] }, { coefficient := 1, powers := [(42, 1)] }, { coefficient := 1, powers := [(48, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1), (50, 1)] }, { coefficient := 1, powers := [(6, 1), (31, 1), (45, 1)] }, { coefficient := 1, powers := [(6, 1), (59, 1)] }, { coefficient := 1, powers := [(9, 1), (25, 1), (45, 1)] }, { coefficient := 1, powers := [(9, 1), (56, 1)] }, { coefficient := 1, powers := [(13, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (49, 1), (53, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1), (53, 1)] }, { coefficient := 1, powers := [(12, 1), (29, 1), (49, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (53, 1)] }, { coefficient := 1, powers := [(19, 1), (29, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (38, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (41, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(41, 1)] }, { coefficient := 1, powers := [(46, 1)] }, { coefficient := 1, powers := [(52, 1)] }, { coefficient := 1, powers := [(57, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (41, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (47, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (36, 1), (41, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (58, 1)] }, { coefficient := 1, powers := [(18, 1), (30, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (29, 1), (54, 1)] }, { coefficient := 1, powers := [(19, 1), (30, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (37, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (40, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (43, 1), (50, 1)] }, { coefficient := 1, powers := [(3, 1), (25, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (31, 1), (56, 1)] }, { coefficient := 1, powers := [(3, 1), (34, 1), (50, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (31, 1), (43, 1)] }, { coefficient := 1, powers := [(6, 1), (34, 1), (40, 1)] }, { coefficient := 1, powers := [(9, 1), (20, 1), (56, 1)] }, { coefficient := 1, powers := [(9, 1), (25, 1), (43, 1)] }, { coefficient := 1, powers := [(9, 1), (34, 1), (37, 1)] }, { coefficient := 1, powers := [(13, 1), (20, 1), (50, 1)] }, { coefficient := 1, powers := [(13, 1), (25, 1), (40, 1)] }, { coefficient := 1, powers := [(13, 1), (31, 1), (37, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1), (38, 1), (60, 1)] }, { coefficient := 1, powers := [(1, 1), (41, 1), (57, 1)] }, { coefficient := 1, powers := [(1, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(4, 1), (27, 1), (60, 1)] }, { coefficient := 1, powers := [(4, 1), (32, 1), (57, 1)] }, { coefficient := 1, powers := [(4, 1), (35, 1), (52, 1)] }, { coefficient := 1, powers := [(7, 1), (22, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (32, 1), (46, 1)] }, { coefficient := 1, powers := [(7, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(10, 1), (22, 1), (57, 1)] }, { coefficient := 1, powers := [(10, 1), (27, 1), (46, 1)] }, { coefficient := 1, powers := [(10, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(15, 1), (22, 1), (52, 1)] }, { coefficient := 1, powers := [(15, 1), (27, 1), (41, 1)] }, { coefficient := 1, powers := [(15, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (39, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (42, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (49, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (49, 1)] }, { coefficient := 1, powers := [(8, 1), (36, 1), (42, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (58, 1)] }, { coefficient := 1, powers := [(12, 1), (30, 1), (49, 1)] }, { coefficient := 1, powers := [(12, 1), (36, 1), (39, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (55, 1)] }, { coefficient := 1, powers := [(19, 1), (30, 1), (42, 1)] }, { coefficient := 1, powers := [(19, 1), (33, 1), (39, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1)] }],
  [{ coefficient := 1, powers := [(1, 1)] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(40, 1)] }],
  [{ coefficient := 1, powers := [(41, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(42, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(56, 1)] }],
  [{ coefficient := 1, powers := [(57, 1)] }],
  [{ coefficient := 1, powers := [(58, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 68 → SparsePoly (Fin 64) := ![
  [{ coefficient := -1, powers := [(7, 1), (29, 1), (49, 1), (54, 1), (60, 1), (62, 1)] }, { coefficient := 2, powers := [(10, 1), (29, 1), (41, 1), (49, 1), (54, 1), (62, 1)] }, { coefficient := 2, powers := [(10, 1), (29, 1), (49, 1), (52, 1), (54, 1), (62, 1)] }, { coefficient := -1, powers := [(15, 1), (29, 1), (41, 1), (49, 1), (54, 1), (62, 1)] }, { coefficient := -1, powers := [(15, 1), (29, 1), (49, 1), (52, 1), (54, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(10, 1), (29, 1), (49, 1), (53, 1), (54, 1), (62, 1)] }, { coefficient := 1, powers := [(15, 1), (29, 1), (49, 1), (53, 1), (54, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (20, 1), (24, 1), (47, 1), (55, 1), (62, 1)] }, { coefficient := 1, powers := [(13, 1), (20, 1), (33, 1), (39, 1), (47, 1), (62, 1)] }, { coefficient := -1, powers := [(13, 1), (24, 1), (25, 1), (47, 1), (55, 1), (62, 1)] }, { coefficient := -1, powers := [(13, 1), (25, 1), (33, 1), (39, 1), (47, 1), (62, 1)] }, { coefficient := 1, powers := [(24, 1), (25, 1), (43, 1), (47, 1), (55, 1), (62, 1)] }, { coefficient := 1, powers := [(24, 1), (34, 1), (37, 1), (47, 1), (55, 1), (62, 1)] }, { coefficient := 1, powers := [(25, 1), (33, 1), (39, 1), (43, 1), (47, 1), (62, 1)] }, { coefficient := 1, powers := [(33, 1), (34, 1), (37, 1), (39, 1), (47, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (18, 1), (29, 1), (49, 1), (54, 1), (60, 1), (62, 1)] }, { coefficient := -1, powers := [(15, 1), (18, 1), (29, 1), (49, 1), (52, 1), (54, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (12, 1), (29, 1), (49, 1), (52, 1), (54, 1), (62, 1), (63, 1)] }, { coefficient := -1, powers := [(11, 1), (18, 1), (29, 1), (49, 1), (53, 1), (54, 1), (62, 1), (63, 1)] }, { coefficient := -1, powers := [(12, 1), (15, 1), (29, 1), (49, 1), (51, 1), (52, 1), (54, 1), (62, 1), (63, 1)] }, { coefficient := 1, powers := [(15, 1), (18, 1), (29, 1), (49, 1), (51, 1), (53, 1), (54, 1), (62, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(24, 1), (26, 1), (41, 1), (62, 1)] }, { coefficient := 1, powers := [(24, 1), (54, 1), (62, 1)] }, { coefficient := 2, powers := [(28, 1), (48, 1), (54, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (24, 1), (47, 1), (55, 1), (59, 1), (62, 1)] }, { coefficient := -1, powers := [(6, 1), (33, 1), (39, 1), (47, 1), (59, 1), (62, 1)] }, { coefficient := -1, powers := [(7, 1), (22, 1), (29, 1), (49, 1), (53, 1), (54, 1), (60, 1), (62, 1)] }, { coefficient := 1, powers := [(15, 1), (22, 1), (29, 1), (49, 1), (52, 1), (53, 1), (54, 1), (62, 1)] }, { coefficient := 2, powers := [(29, 1), (49, 1), (53, 1), (54, 1), (62, 1)] }, { coefficient := 2, powers := [(30, 1), (41, 1), (49, 1), (53, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(28, 1), (41, 1), (55, 1), (62, 1)] }, { coefficient := 1, powers := [(29, 1), (51, 1), (54, 1), (62, 1)] }, { coefficient := -1, powers := [(30, 1), (41, 1), (51, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (42, 1), (60, 1), (62, 1)] }, { coefficient := -1, powers := [(18, 1), (42, 1), (54, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(18, 1), (41, 1), (49, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (42, 1), (53, 1), (54, 1), (62, 1), (63, 1)] }, { coefficient := -2, powers := [(18, 1), (53, 1), (54, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (41, 1), (44, 1), (62, 1)] }, { coefficient := -1, powers := [(12, 1), (47, 1), (62, 1)] }, { coefficient := 1, powers := [(19, 1), (51, 1), (52, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (15, 1), (29, 1), (49, 1), (52, 1), (54, 1), (62, 1), (63, 1)] }, { coefficient := -1, powers := [(15, 1), (18, 1), (29, 1), (49, 1), (53, 1), (54, 1), (62, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(18, 1), (42, 1), (49, 1), (54, 1), (62, 1), (63, 1)] }, { coefficient := 3, powers := [(18, 1), (49, 1), (54, 1), (62, 1)] }, { coefficient := -2, powers := [(19, 1), (48, 1), (54, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (22, 1), (29, 1), (49, 1), (54, 1), (60, 1), (62, 1)] }, { coefficient := 1, powers := [(15, 1), (22, 1), (29, 1), (49, 1), (52, 1), (54, 1), (62, 1)] }, { coefficient := 2, powers := [(29, 1), (49, 1), (54, 1), (62, 1)] }, { coefficient := 2, powers := [(30, 1), (41, 1), (49, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (54, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (29, 1), (49, 1), (52, 1), (54, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (29, 1), (46, 1), (49, 1), (54, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(18, 1), (24, 1), (25, 1), (47, 1), (55, 1), (62, 1)] }, { coefficient := -1, powers := [(18, 1), (25, 1), (33, 1), (39, 1), (47, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (22, 1), (25, 1), (29, 1), (49, 1), (54, 1), (60, 1), (62, 1)] }, { coefficient := -1, powers := [(7, 1), (29, 1), (35, 1), (49, 1), (54, 1), (62, 1)] }, { coefficient := -1, powers := [(15, 1), (22, 1), (25, 1), (29, 1), (49, 1), (52, 1), (54, 1), (62, 1)] }, { coefficient := -2, powers := [(25, 1), (29, 1), (49, 1), (54, 1), (62, 1)] }, { coefficient := -2, powers := [(25, 1), (30, 1), (41, 1), (49, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (25, 1), (41, 1), (55, 1), (62, 1)] }, { coefficient := 1, powers := [(24, 1), (55, 1), (62, 1)] }, { coefficient := 1, powers := [(33, 1), (39, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (44, 1), (54, 1), (62, 1)] }, { coefficient := -1, powers := [(19, 1), (25, 1), (41, 1), (55, 1), (62, 1)] }, { coefficient := -1, powers := [(19, 1), (51, 1), (54, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(18, 1), (42, 1), (44, 1), (62, 1)] }, { coefficient := -1, powers := [(19, 1), (42, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(19, 1), (24, 1), (41, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (22, 1), (29, 1), (49, 1), (54, 1), (60, 1), (62, 1)] }, { coefficient := -1, powers := [(15, 1), (22, 1), (29, 1), (49, 1), (52, 1), (54, 1), (62, 1)] }, { coefficient := -2, powers := [(29, 1), (49, 1), (54, 1), (62, 1)] }, { coefficient := -2, powers := [(30, 1), (41, 1), (49, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(13, 1), (24, 1), (47, 1), (55, 1), (62, 1)] }, { coefficient := -1, powers := [(13, 1), (33, 1), (39, 1), (47, 1), (62, 1)] }, { coefficient := 1, powers := [(24, 1), (25, 1), (45, 1), (47, 1), (55, 1), (62, 1)] }, { coefficient := 1, powers := [(24, 1), (43, 1), (47, 1), (55, 1), (62, 1)] }, { coefficient := 1, powers := [(25, 1), (33, 1), (39, 1), (45, 1), (47, 1), (62, 1)] }, { coefficient := 1, powers := [(33, 1), (39, 1), (43, 1), (47, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(24, 1), (41, 1), (55, 1), (62, 1)] }, { coefficient := -1, powers := [(28, 1), (41, 1), (48, 1), (55, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(18, 1), (42, 1), (54, 1), (62, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (41, 1), (48, 1), (55, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(41, 1), (55, 1), (62, 1)] }, { coefficient := -1, powers := [(53, 1), (54, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(42, 1), (47, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(41, 1), (49, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(29, 1), (54, 1), (62, 1)] }, { coefficient := 1, powers := [(30, 1), (41, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (41, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(19, 1), (52, 1), (62, 1)] }],
  [{ coefficient := 2, powers := [(18, 1), (24, 1), (54, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (24, 1), (26, 1), (41, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (28, 1), (41, 1), (55, 1), (62, 1)] }, { coefficient := -1, powers := [(19, 1), (29, 1), (51, 1), (54, 1), (62, 1)] }, { coefficient := 1, powers := [(19, 1), (30, 1), (41, 1), (51, 1), (62, 1)] }],
  [{ coefficient := 2, powers := [(42, 1), (47, 1), (54, 1), (62, 1)] }],
  [{ coefficient := -2, powers := [(47, 1), (54, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (29, 1), (49, 1), (54, 1), (62, 1)] }, { coefficient := -1, powers := [(15, 1), (29, 1), (49, 1), (54, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (41, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(19, 1), (54, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (48, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (24, 1), (25, 1), (43, 1), (47, 1), (55, 1), (62, 1)] }, { coefficient := -1, powers := [(18, 1), (24, 1), (34, 1), (37, 1), (47, 1), (55, 1), (62, 1)] }, { coefficient := 1, powers := [(18, 1), (25, 1), (33, 1), (39, 1), (43, 1), (47, 1), (62, 1)] }, { coefficient := -1, powers := [(18, 1), (33, 1), (34, 1), (37, 1), (39, 1), (47, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (29, 1), (49, 1), (52, 1), (54, 1), (62, 1), (63, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (49, 1), (53, 1), (54, 1), (62, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(42, 1), (44, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(18, 1), (24, 1), (47, 1), (50, 1), (55, 1), (62, 1)] }, { coefficient := -1, powers := [(18, 1), (33, 1), (39, 1), (47, 1), (50, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(18, 1), (24, 1), (25, 1), (45, 1), (47, 1), (55, 1), (62, 1)] }, { coefficient := -1, powers := [(18, 1), (24, 1), (43, 1), (47, 1), (55, 1), (62, 1)] }, { coefficient := -1, powers := [(18, 1), (25, 1), (33, 1), (39, 1), (45, 1), (47, 1), (62, 1)] }, { coefficient := -1, powers := [(18, 1), (33, 1), (39, 1), (43, 1), (47, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (27, 1), (29, 1), (49, 1), (54, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (15, 1), (29, 1), (49, 1), (54, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (29, 1), (54, 1), (62, 1)] }, { coefficient := -1, powers := [(19, 1), (30, 1), (41, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (24, 1), (25, 1), (47, 1), (55, 1), (62, 1)] }, { coefficient := 1, powers := [(18, 1), (25, 1), (33, 1), (39, 1), (47, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(54, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (12, 1), (29, 1), (35, 1), (49, 1), (54, 1), (62, 1)] }, { coefficient := -2, powers := [(10, 1), (12, 1), (27, 1), (29, 1), (49, 1), (54, 1), (62, 1)] }, { coefficient := 1, powers := [(19, 1), (30, 1), (42, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(42, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (24, 1), (47, 1), (55, 1), (62, 1)] }, { coefficient := 1, powers := [(18, 1), (33, 1), (39, 1), (47, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (29, 1), (49, 1), (54, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(41, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (12, 1), (29, 1), (35, 1), (38, 1), (49, 1), (54, 1), (60, 1), (62, 1)] }, { coefficient := -1, powers := [(7, 1), (12, 1), (29, 1), (35, 1), (41, 1), (49, 1), (54, 1), (57, 1), (62, 1)] }, { coefficient := -1, powers := [(7, 1), (12, 1), (29, 1), (35, 1), (46, 1), (49, 1), (52, 1), (54, 1), (62, 1)] }, { coefficient := 2, powers := [(10, 1), (12, 1), (27, 1), (29, 1), (38, 1), (49, 1), (54, 1), (60, 1), (62, 1)] }, { coefficient := 2, powers := [(10, 1), (12, 1), (27, 1), (29, 1), (41, 1), (49, 1), (54, 1), (57, 1), (62, 1)] }, { coefficient := 2, powers := [(10, 1), (12, 1), (27, 1), (29, 1), (46, 1), (49, 1), (52, 1), (54, 1), (62, 1)] }, { coefficient := -1, powers := [(18, 1), (24, 1), (37, 1), (47, 1), (55, 1), (59, 1), (62, 1)] }, { coefficient := -2, powers := [(18, 1), (24, 1), (38, 1), (54, 1), (61, 1), (62, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (43, 1), (47, 1), (50, 1), (55, 1), (62, 1)] }, { coefficient := -2, powers := [(18, 1), (24, 1), (47, 1), (53, 1), (54, 1), (62, 1)] }, { coefficient := -1, powers := [(18, 1), (33, 1), (37, 1), (39, 1), (47, 1), (59, 1), (62, 1)] }, { coefficient := 1, powers := [(18, 1), (33, 1), (39, 1), (43, 1), (47, 1), (50, 1), (62, 1)] }, { coefficient := -1, powers := [(19, 1), (24, 1), (26, 1), (41, 1), (46, 1), (53, 1), (62, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (41, 1), (46, 1), (55, 1), (62, 1)] }, { coefficient := -1, powers := [(19, 1), (28, 1), (41, 1), (48, 1), (52, 1), (55, 1), (62, 1)] }, { coefficient := -1, powers := [(19, 1), (29, 1), (42, 1), (54, 1), (57, 1), (62, 1)] }, { coefficient := 1, powers := [(19, 1), (29, 1), (48, 1), (51, 1), (52, 1), (54, 1), (62, 1)] }, { coefficient := -1, powers := [(19, 1), (29, 1), (48, 1), (53, 1), (54, 1), (62, 1)] }, { coefficient := -1, powers := [(19, 1), (30, 1), (38, 1), (42, 1), (60, 1), (62, 1)] }, { coefficient := -1, powers := [(19, 1), (30, 1), (41, 1), (48, 1), (51, 1), (52, 1), (62, 1)] }, { coefficient := 1, powers := [(19, 1), (30, 1), (41, 1), (48, 1), (53, 1), (62, 1)] }, { coefficient := -1, powers := [(19, 1), (30, 1), (42, 1), (46, 1), (52, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (29, 1), (38, 1), (49, 1), (54, 1), (60, 1), (62, 1)] }, { coefficient := 1, powers := [(12, 1), (29, 1), (41, 1), (49, 1), (54, 1), (57, 1), (62, 1)] }, { coefficient := 1, powers := [(12, 1), (29, 1), (42, 1), (49, 1), (52, 1), (54, 1), (57, 1), (62, 1), (63, 1)] }, { coefficient := -1, powers := [(12, 1), (29, 1), (46, 1), (49, 1), (52, 1), (54, 1), (62, 1)] }, { coefficient := 1, powers := [(12, 1), (29, 1), (48, 1), (49, 1), (52, 1), (53, 1), (54, 1), (62, 1), (63, 1)] }, { coefficient := -1, powers := [(18, 1), (29, 1), (42, 1), (49, 1), (53, 1), (54, 1), (57, 1), (62, 1), (63, 1)] }, { coefficient := -1, powers := [(18, 1), (29, 1), (48, 1), (49, 1), (53, 2), (54, 1), (62, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(25, 1), (41, 1), (47, 1), (48, 1), (55, 1), (62, 1)] }, { coefficient := -2, powers := [(37, 1), (42, 1), (47, 1), (54, 1), (60, 1), (62, 1)] }, { coefficient := 1, powers := [(39, 1), (41, 1), (61, 1), (62, 1)] }, { coefficient := -1, powers := [(41, 1), (49, 1), (55, 1), (62, 1)] }, { coefficient := -1, powers := [(42, 1), (44, 1), (46, 1), (54, 1), (62, 1)] }, { coefficient := -2, powers := [(42, 1), (47, 1), (54, 1), (62, 1)] }, { coefficient := 2, powers := [(47, 1), (48, 1), (51, 1), (54, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (18, 1), (24, 1), (25, 1), (43, 1), (47, 1), (55, 1), (57, 1), (62, 1)] }, { coefficient := 1, powers := [(0, 1), (18, 1), (24, 1), (34, 1), (37, 1), (47, 1), (55, 1), (57, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 1), (18, 1), (24, 1), (47, 1), (55, 1), (56, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 1), (18, 1), (25, 1), (33, 1), (39, 1), (43, 1), (47, 1), (57, 1), (62, 1)] }, { coefficient := 1, powers := [(0, 1), (18, 1), (33, 1), (34, 1), (37, 1), (39, 1), (47, 1), (57, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 1), (18, 1), (33, 1), (39, 1), (47, 1), (56, 1), (62, 1)] }, { coefficient := -1, powers := [(6, 1), (18, 1), (24, 1), (34, 1), (47, 1), (55, 1), (62, 1)] }, { coefficient := -1, powers := [(6, 1), (18, 1), (33, 1), (34, 1), (39, 1), (47, 1), (62, 1)] }, { coefficient := 1, powers := [(13, 1), (18, 1), (24, 1), (25, 1), (47, 1), (55, 1), (62, 1)] }, { coefficient := 1, powers := [(13, 1), (18, 1), (25, 1), (33, 1), (39, 1), (47, 1), (62, 1)] }, { coefficient := -1, powers := [(18, 1), (24, 1), (25, 1), (43, 1), (47, 1), (55, 1), (62, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (34, 1), (37, 1), (47, 1), (55, 1), (62, 1)] }, { coefficient := -1, powers := [(18, 1), (25, 1), (33, 1), (39, 1), (43, 1), (47, 1), (62, 1)] }, { coefficient := 1, powers := [(18, 1), (33, 1), (34, 1), (37, 1), (39, 1), (47, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(7, 1), (12, 1), (29, 1), (35, 1), (49, 1), (52, 1), (54, 1), (62, 1)] }, { coefficient := -1, powers := [(7, 1), (18, 1), (29, 1), (35, 1), (49, 1), (53, 1), (54, 1), (62, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (42, 1), (44, 1), (54, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (18, 1), (24, 1), (31, 1), (47, 1), (55, 1), (62, 1)] }, { coefficient := -1, powers := [(3, 1), (18, 1), (31, 1), (33, 1), (39, 1), (47, 1), (62, 1)] }, { coefficient := -1, powers := [(9, 1), (18, 1), (20, 1), (24, 1), (47, 1), (55, 1), (62, 1)] }, { coefficient := -1, powers := [(9, 1), (18, 1), (20, 1), (33, 1), (39, 1), (47, 1), (62, 1)] }, { coefficient := -1, powers := [(9, 1), (18, 1), (24, 1), (25, 1), (47, 1), (55, 1), (62, 1)] }, { coefficient := -1, powers := [(9, 1), (18, 1), (25, 1), (33, 1), (39, 1), (47, 1), (62, 1)] }, { coefficient := 1, powers := [(18, 1), (20, 1), (24, 1), (47, 1), (50, 1), (55, 1), (62, 1)] }, { coefficient := 1, powers := [(18, 1), (20, 1), (33, 1), (39, 1), (47, 1), (50, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (18, 1), (24, 1), (25, 1), (31, 1), (43, 1), (47, 1), (55, 1), (62, 1)] }, { coefficient := 1, powers := [(3, 1), (18, 1), (24, 1), (31, 1), (34, 1), (37, 1), (47, 1), (55, 1), (62, 1)] }, { coefficient := -1, powers := [(3, 1), (18, 1), (25, 1), (31, 1), (33, 1), (39, 1), (43, 1), (47, 1), (62, 1)] }, { coefficient := 1, powers := [(3, 1), (18, 1), (31, 1), (33, 1), (34, 1), (37, 1), (39, 1), (47, 1), (62, 1)] }, { coefficient := 1, powers := [(4, 1), (12, 1), (29, 1), (32, 1), (49, 1), (54, 1), (62, 1)] }, { coefficient := -1, powers := [(7, 1), (12, 1), (20, 1), (22, 1), (29, 1), (49, 1), (54, 1), (60, 1), (62, 1)] }, { coefficient := -1, powers := [(7, 1), (12, 1), (22, 1), (25, 1), (29, 1), (49, 1), (54, 1), (60, 1), (62, 1)] }, { coefficient := -1, powers := [(9, 1), (18, 1), (20, 1), (24, 1), (25, 1), (43, 1), (47, 1), (55, 1), (62, 1)] }, { coefficient := 1, powers := [(9, 1), (18, 1), (20, 1), (24, 1), (34, 1), (37, 1), (47, 1), (55, 1), (62, 1)] }, { coefficient := -1, powers := [(9, 1), (18, 1), (20, 1), (25, 1), (33, 1), (39, 1), (43, 1), (47, 1), (62, 1)] }, { coefficient := 1, powers := [(9, 1), (18, 1), (20, 1), (33, 1), (34, 1), (37, 1), (39, 1), (47, 1), (62, 1)] }, { coefficient := 1, powers := [(10, 1), (12, 1), (27, 1), (29, 1), (49, 1), (54, 1), (62, 1)] }, { coefficient := 1, powers := [(12, 1), (15, 1), (20, 1), (22, 1), (29, 1), (49, 1), (52, 1), (54, 1), (62, 1)] }, { coefficient := 1, powers := [(12, 1), (15, 1), (22, 1), (25, 1), (29, 1), (49, 1), (52, 1), (54, 1), (62, 1)] }, { coefficient := 2, powers := [(12, 1), (20, 1), (29, 1), (49, 1), (54, 1), (62, 1)] }, { coefficient := 2, powers := [(12, 1), (20, 1), (30, 1), (41, 1), (49, 1), (62, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (44, 1), (54, 1), (62, 1)] }, { coefficient := 2, powers := [(12, 1), (25, 1), (29, 1), (49, 1), (54, 1), (62, 1)] }, { coefficient := 2, powers := [(12, 1), (25, 1), (30, 1), (41, 1), (49, 1), (62, 1)] }, { coefficient := -1, powers := [(19, 1), (21, 1), (28, 1), (41, 1), (55, 1), (62, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (25, 1), (41, 1), (55, 1), (62, 1)] }, { coefficient := -1, powers := [(19, 1), (24, 1), (26, 1), (41, 1), (51, 1), (62, 1)] }, { coefficient := 2, powers := [(19, 1), (24, 1), (51, 1), (54, 1), (62, 1)] }, { coefficient := -1, powers := [(19, 1), (30, 1), (42, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (33, 1), (41, 1), (62, 1)] }, { coefficient := -1, powers := [(12, 1), (24, 1), (41, 1), (62, 1)] }, { coefficient := -1, powers := [(12, 1), (29, 1), (48, 1), (62, 1)] }, { coefficient := -1, powers := [(18, 1), (29, 1), (42, 1), (62, 1)] }]
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
    ¬ ∀ index : Fin 68,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component37.SelectedLeafB0_3_0.selectedHasNoCommonZero

end Krenn.Component37.SelectedLeafB0_3_0
