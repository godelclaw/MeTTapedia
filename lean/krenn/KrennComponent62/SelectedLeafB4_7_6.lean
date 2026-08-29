import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component62.SelectedLeafB4_7_6

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "59ef620c5f3601651a19c709ce27ba6149a82531a288720810f08abcc24955ee"
def certificateSHA256 : String := "8f0e1740caccfc4ec61821959477429e2063208272841e1509bfbbb1bf5d988b"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 42 → Fin 667 := ![
  8,
  16,
  18,
  21,
  97,
  137,
  147,
  151,
  153,
  158,
  160,
  186,
  245,
  252,
  293,
  294,
  295,
  296,
  301,
  302,
  361,
  441,
  444,
  454,
  476,
  483,
  557,
  588,
  602,
  603,
  604,
  605,
  656,
  657,
  658,
  659,
  660,
  662,
  663,
  664,
  665,
  666
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 42 → SparsePoly (Fin 66) := ![
  [{ coefficient := 1, powers := [(10, 1), (27, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (22, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (52, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (24, 1)] }, { coefficient := 1, powers := [(16, 1), (18, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (22, 1)] }, { coefficient := 1, powers := [(22, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (18, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (50, 1)] }, { coefficient := 1, powers := [(22, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (38, 1)] }, { coefficient := 1, powers := [(27, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (27, 1), (58, 1)] }, { coefficient := 1, powers := [(27, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (19, 1), (51, 1)] }, { coefficient := 1, powers := [(14, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (23, 1), (46, 1)] }, { coefficient := 1, powers := [(17, 1), (19, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (41, 1)] }, { coefficient := 1, powers := [(18, 1), (41, 1)] }, { coefficient := 1, powers := [(23, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1)] }, { coefficient := 1, powers := [(19, 1), (41, 1)] }, { coefficient := 1, powers := [(23, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (48, 1)] }, { coefficient := 1, powers := [(18, 1), (48, 1)] }, { coefficient := 1, powers := [(23, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (53, 1)] }, { coefficient := 1, powers := [(18, 1), (53, 1)] }, { coefficient := 1, powers := [(24, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (46, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (53, 1)] }, { coefficient := 1, powers := [(8, 1), (30, 1)] }, { coefficient := 1, powers := [(12, 1), (27, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (27, 1), (58, 1)] }, { coefficient := 1, powers := [(10, 1), (27, 1), (43, 1)] }, { coefficient := 1, powers := [(14, 1), (27, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (59, 1)] }, { coefficient := 1, powers := [(12, 1), (46, 1)] }, { coefficient := 1, powers := [(17, 1), (19, 1), (51, 1)] }, { coefficient := 1, powers := [(17, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (59, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (44, 1)] }, { coefficient := 1, powers := [(12, 1), (56, 1)] }, { coefficient := 1, powers := [(17, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (53, 1)] }, { coefficient := 1, powers := [(27, 1), (39, 1)] }, { coefficient := 1, powers := [(27, 1), (45, 1), (48, 1)] }, { coefficient := 1, powers := [(30, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1), (53, 1)] }, { coefficient := 1, powers := [(24, 1), (44, 1), (48, 1)] }, { coefficient := 1, powers := [(41, 1), (53, 1)] }, { coefficient := 1, powers := [(48, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1), (51, 1)] }, { coefficient := 1, powers := [(19, 1), (41, 1), (51, 1)] }, { coefficient := 1, powers := [(39, 1), (41, 1)] }, { coefficient := 1, powers := [(46, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (41, 1), (52, 1)] }, { coefficient := 1, powers := [(22, 1), (56, 1)] }, { coefficient := 1, powers := [(27, 1), (46, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (38, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1), (44, 1)] }, { coefficient := 1, powers := [(17, 1), (27, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (43, 1)] }, { coefficient := 1, powers := [(4, 1), (25, 1), (58, 1)] }, { coefficient := 1, powers := [(4, 1), (32, 1)] }, { coefficient := 1, powers := [(10, 1), (25, 1), (43, 1)] }, { coefficient := 1, powers := [(14, 1), (21, 1)] }, { coefficient := 1, powers := [(14, 1), (25, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (50, 1)] }, { coefficient := 1, powers := [(7, 1), (20, 1), (58, 1)] }, { coefficient := 1, powers := [(7, 1), (29, 1)] }, { coefficient := 1, powers := [(10, 1), (20, 1), (55, 1)] }, { coefficient := 1, powers := [(10, 1), (26, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (58, 1)] }, { coefficient := 1, powers := [(7, 1), (58, 1)] }, { coefficient := 1, powers := [(10, 1), (43, 1)] }, { coefficient := 1, powers := [(10, 1), (55, 1)] }, { coefficient := 1, powers := [(14, 1), (38, 1)] }, { coefficient := 1, powers := [(14, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (50, 1)] }, { coefficient := 1, powers := [(21, 1), (55, 1)] }, { coefficient := 1, powers := [(26, 1), (38, 1)] }, { coefficient := 1, powers := [(26, 1), (43, 1)] }, { coefficient := 1, powers := [(29, 1), (35, 1)] }, { coefficient := 1, powers := [(32, 1), (35, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (35, 1), (58, 1)] }, { coefficient := 1, powers := [(1, 1), (38, 1), (55, 1)] }, { coefficient := 1, powers := [(1, 1), (43, 1), (50, 1)] }, { coefficient := 1, powers := [(4, 1), (26, 1), (58, 1)] }, { coefficient := 1, powers := [(4, 1), (29, 1), (55, 1)] }, { coefficient := 1, powers := [(4, 1), (32, 1), (50, 1)] }, { coefficient := 1, powers := [(7, 1), (21, 1), (58, 1)] }, { coefficient := 1, powers := [(7, 1), (29, 1), (43, 1)] }, { coefficient := 1, powers := [(7, 1), (32, 1), (38, 1)] }, { coefficient := 1, powers := [(10, 1), (21, 1), (55, 1)] }, { coefficient := 1, powers := [(10, 1), (26, 1), (43, 1)] }, { coefficient := 1, powers := [(10, 1), (32, 1), (35, 1)] }, { coefficient := 1, powers := [(14, 1), (21, 1), (50, 1)] }, { coefficient := 1, powers := [(14, 1), (26, 1), (38, 1)] }, { coefficient := 1, powers := [(14, 1), (29, 1), (35, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (36, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (46, 1), (53, 1)] }, { coefficient := 1, powers := [(5, 1), (27, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (53, 1)] }, { coefficient := 1, powers := [(8, 1), (22, 1), (59, 1)] }, { coefficient := 1, powers := [(8, 1), (30, 1), (46, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (39, 1)] }, { coefficient := 1, powers := [(12, 1), (22, 1), (56, 1)] }, { coefficient := 1, powers := [(12, 1), (27, 1), (46, 1)] }, { coefficient := 1, powers := [(12, 1), (33, 1), (36, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (53, 1)] }, { coefficient := 1, powers := [(17, 1), (27, 1), (39, 1)] }, { coefficient := 1, powers := [(17, 1), (30, 1), (36, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (60, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1)] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(38, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(39, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(54, 1), (64, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(55, 1), (65, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(56, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 42 → SparsePoly (Fin 66) := ![
  [{ coefficient := -2, powers := [(3, 1), (12, 1), (29, 1), (43, 1), (46, 1), (55, 1)] }, { coefficient := 2, powers := [(3, 1), (12, 1), (32, 1), (43, 1), (46, 1), (55, 1)] }, { coefficient := -2, powers := [(3, 1), (17, 1), (29, 1), (39, 1), (43, 1), (55, 1)] }, { coefficient := 2, powers := [(3, 1), (17, 1), (32, 1), (39, 1), (43, 1), (55, 1)] }, { coefficient := 2, powers := [(12, 1), (26, 1), (43, 1), (46, 1)] }, { coefficient := -2, powers := [(12, 1), (32, 1), (35, 1), (46, 1)] }, { coefficient := 2, powers := [(17, 1), (26, 1), (39, 1), (43, 1)] }, { coefficient := -2, powers := [(17, 1), (32, 1), (35, 1), (39, 1)] }],
  [{ coefficient := -2, powers := [(3, 1), (12, 1), (19, 1), (27, 1), (29, 1), (43, 1), (46, 1), (55, 1), (63, 1)] }, { coefficient := -2, powers := [(3, 1), (12, 1), (19, 1), (27, 1), (32, 1), (43, 1), (46, 1), (50, 1), (63, 1)] }, { coefficient := -2, powers := [(3, 1), (17, 1), (19, 1), (27, 1), (29, 1), (39, 1), (43, 1), (55, 1), (63, 1)] }, { coefficient := -2, powers := [(3, 1), (17, 1), (19, 1), (27, 1), (32, 1), (39, 1), (43, 1), (50, 1), (63, 1)] }, { coefficient := -4, powers := [(12, 1), (19, 1), (21, 1), (27, 1), (46, 1), (50, 1), (63, 1)] }, { coefficient := -2, powers := [(12, 1), (19, 1), (21, 1), (27, 1), (46, 1), (55, 1), (63, 1)] }, { coefficient := -2, powers := [(12, 1), (19, 1), (27, 1), (32, 1), (35, 1), (46, 1), (63, 1)] }, { coefficient := -4, powers := [(17, 1), (19, 1), (21, 1), (27, 1), (39, 1), (50, 1), (63, 1)] }, { coefficient := -2, powers := [(17, 1), (19, 1), (21, 1), (27, 1), (39, 1), (55, 1), (63, 1)] }, { coefficient := -2, powers := [(17, 1), (19, 1), (27, 1), (32, 1), (35, 1), (39, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(17, 1), (45, 1)] }],
  [{ coefficient := -2, powers := [(17, 1), (53, 1), (64, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(39, 1), (44, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(22, 1), (44, 1)] }],
  [{ coefficient := -2, powers := [(17, 1), (53, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(22, 1), (41, 1), (53, 1), (60, 1)] }, { coefficient := -1, powers := [(27, 1), (39, 1), (41, 1), (60, 1)] }, { coefficient := -1, powers := [(27, 1), (46, 1), (48, 1), (60, 1)] }],
  [{ coefficient := 2, powers := [(13, 1), (17, 1), (53, 1), (64, 1), (65, 1)] }],
  [{ coefficient := -2, powers := [(3, 1), (12, 1), (14, 1), (29, 1), (46, 1), (55, 1)] }, { coefficient := -2, powers := [(3, 1), (14, 1), (17, 1), (29, 1), (39, 1), (55, 1)] }, { coefficient := -2, powers := [(7, 1), (12, 1), (32, 1), (46, 1)] }, { coefficient := -2, powers := [(7, 1), (17, 1), (32, 1), (39, 1)] }, { coefficient := 2, powers := [(12, 1), (14, 1), (26, 1), (46, 1)] }, { coefficient := 2, powers := [(14, 1), (17, 1), (26, 1), (39, 1)] }],
  [{ coefficient := -2, powers := [(4, 1), (12, 1), (29, 1), (46, 1), (55, 1)] }, { coefficient := -2, powers := [(4, 1), (17, 1), (29, 1), (39, 1), (55, 1)] }, { coefficient := 2, powers := [(7, 1), (12, 1), (32, 1), (43, 1), (46, 1)] }, { coefficient := 2, powers := [(7, 1), (17, 1), (32, 1), (39, 1), (43, 1)] }],
  [{ coefficient := 2, powers := [(3, 1), (12, 1), (27, 1), (29, 1), (43, 1), (46, 1), (55, 1), (63, 1)] }, { coefficient := 2, powers := [(3, 1), (12, 1), (27, 1), (32, 1), (43, 1), (46, 1), (50, 1), (63, 1)] }, { coefficient := 2, powers := [(3, 1), (17, 1), (27, 1), (29, 1), (39, 1), (43, 1), (55, 1), (63, 1)] }, { coefficient := 2, powers := [(3, 1), (17, 1), (27, 1), (32, 1), (39, 1), (43, 1), (50, 1), (63, 1)] }, { coefficient := 4, powers := [(12, 1), (21, 1), (27, 1), (46, 1), (50, 1), (63, 1)] }, { coefficient := 2, powers := [(12, 1), (21, 1), (27, 1), (46, 1), (55, 1), (63, 1)] }, { coefficient := 2, powers := [(12, 1), (27, 1), (32, 1), (35, 1), (46, 1), (63, 1)] }, { coefficient := 4, powers := [(17, 1), (21, 1), (27, 1), (39, 1), (50, 1), (63, 1)] }, { coefficient := 2, powers := [(17, 1), (21, 1), (27, 1), (39, 1), (55, 1), (63, 1)] }, { coefficient := 2, powers := [(17, 1), (27, 1), (32, 1), (35, 1), (39, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(27, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (22, 1), (53, 1), (60, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1), (39, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (27, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (27, 1), (46, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (22, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(53, 1)] }],
  [{ coefficient := 1, powers := [(46, 1)] }],
  [{ coefficient := 2, powers := [(3, 1), (12, 1), (29, 1), (46, 1), (55, 1)] }, { coefficient := 2, powers := [(3, 1), (12, 1), (32, 1), (43, 1), (46, 1)] }, { coefficient := 2, powers := [(3, 1), (17, 1), (29, 1), (39, 1), (55, 1)] }, { coefficient := 2, powers := [(3, 1), (17, 1), (32, 1), (39, 1), (43, 1)] }, { coefficient := -2, powers := [(12, 1), (20, 1), (43, 1), (46, 1)] }, { coefficient := 2, powers := [(12, 1), (21, 1), (46, 1)] }, { coefficient := 2, powers := [(12, 1), (25, 1), (46, 1), (50, 1)] }, { coefficient := -2, powers := [(12, 1), (26, 1), (46, 1)] }, { coefficient := -2, powers := [(17, 1), (20, 1), (39, 1), (43, 1)] }, { coefficient := 2, powers := [(17, 1), (21, 1), (39, 1)] }, { coefficient := 2, powers := [(17, 1), (25, 1), (39, 1), (50, 1)] }, { coefficient := -2, powers := [(17, 1), (26, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(27, 1)] }],
  [{ coefficient := 1, powers := [(22, 1)] }],
  [{ coefficient := 1, powers := [(17, 1)] }],
  [{ coefficient := -1, powers := [(16, 1), (22, 1)] }],
  [{ coefficient := -1, powers := [(16, 1), (27, 1)] }],
  [{ coefficient := 1, powers := [(12, 1)] }],
  [{ coefficient := 1, powers := [(39, 1), (62, 1)] }],
  [{ coefficient := -2, powers := [(12, 1), (27, 1), (46, 1), (50, 1)] }, { coefficient := -2, powers := [(17, 1), (27, 1), (39, 1), (50, 1)] }],
  [{ coefficient := -2, powers := [(12, 1), (27, 1), (43, 1), (46, 1)] }, { coefficient := -2, powers := [(17, 1), (27, 1), (39, 1), (43, 1)] }],
  [{ coefficient := -2, powers := [(3, 1), (12, 1), (27, 1), (32, 1), (43, 1), (46, 1)] }, { coefficient := -2, powers := [(3, 1), (17, 1), (27, 1), (32, 1), (39, 1), (43, 1)] }, { coefficient := 2, powers := [(12, 1), (20, 1), (27, 1), (43, 1), (46, 1)] }, { coefficient := -2, powers := [(12, 1), (21, 1), (27, 1), (46, 1)] }, { coefficient := 2, powers := [(17, 1), (20, 1), (27, 1), (39, 1), (43, 1)] }, { coefficient := -2, powers := [(17, 1), (21, 1), (27, 1), (39, 1)] }],
  [{ coefficient := -2, powers := [(12, 1), (14, 1), (27, 1), (46, 1)] }, { coefficient := -2, powers := [(14, 1), (17, 1), (27, 1), (39, 1)] }],
  [{ coefficient := 2, powers := [(12, 1), (27, 1), (46, 1)] }, { coefficient := 2, powers := [(17, 1), (27, 1), (39, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(16, 1), (22, 1), (41, 1), (53, 1)] }, { coefficient := -1, powers := [(16, 1), (27, 1), (39, 1), (41, 1)] }, { coefficient := -1, powers := [(16, 1), (27, 1), (46, 1), (48, 1)] }],
  [{ coefficient := -2, powers := [(12, 1), (27, 1), (35, 1), (46, 1), (58, 1)] }, { coefficient := -2, powers := [(12, 1), (27, 1), (38, 1), (46, 1), (55, 1)] }, { coefficient := 2, powers := [(12, 1), (27, 1), (43, 1), (46, 1), (50, 1)] }, { coefficient := -2, powers := [(17, 1), (27, 1), (35, 1), (39, 1), (58, 1)] }, { coefficient := -2, powers := [(17, 1), (27, 1), (38, 1), (39, 1), (55, 1)] }, { coefficient := 2, powers := [(17, 1), (27, 1), (39, 1), (43, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(36, 1), (59, 1)] }, { coefficient := -1, powers := [(38, 1), (39, 1), (56, 1), (62, 1)] }, { coefficient := 1, powers := [(39, 1), (56, 1)] }, { coefficient := -1, powers := [(46, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (33, 1), (39, 1)] }, { coefficient := -1, powers := [(17, 1), (27, 1), (39, 1)] }],
  [{ coefficient := -2, powers := [(3, 1), (12, 1), (14, 1), (27, 1), (29, 1), (43, 1), (46, 1), (55, 1)] }, { coefficient := -2, powers := [(3, 1), (12, 1), (14, 1), (27, 1), (32, 1), (43, 1), (46, 1), (50, 1)] }, { coefficient := -2, powers := [(3, 1), (14, 1), (17, 1), (27, 1), (29, 1), (39, 1), (43, 1), (55, 1)] }, { coefficient := -2, powers := [(3, 1), (14, 1), (17, 1), (27, 1), (32, 1), (39, 1), (43, 1), (50, 1)] }, { coefficient := -4, powers := [(12, 1), (14, 1), (21, 1), (27, 1), (46, 1), (50, 1)] }, { coefficient := -2, powers := [(12, 1), (14, 1), (21, 1), (27, 1), (46, 1), (55, 1)] }, { coefficient := -2, powers := [(12, 1), (14, 1), (27, 1), (32, 1), (35, 1), (46, 1)] }, { coefficient := -4, powers := [(14, 1), (17, 1), (21, 1), (27, 1), (39, 1), (50, 1)] }, { coefficient := -2, powers := [(14, 1), (17, 1), (21, 1), (27, 1), (39, 1), (55, 1)] }, { coefficient := -2, powers := [(14, 1), (17, 1), (27, 1), (32, 1), (35, 1), (39, 1)] }],
  [{ coefficient := 2, powers := [(17, 1), (22, 1), (53, 1)] }],
  [{ coefficient := -2, powers := [(13, 1), (17, 1), (22, 1), (53, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (30, 1)] }, { coefficient := -1, powers := [(12, 1), (22, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1), (48, 1)] }]
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
    ¬ ∀ index : Fin 42,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component62.SelectedLeafB4_7_6.selectedHasNoCommonZero

end Krenn.Component62.SelectedLeafB4_7_6
