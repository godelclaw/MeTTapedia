import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component18.SelectedLeafB4_2_6_4

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "0762c2ace93c53a3143732f9b59581082135313f4d210a395cc9403c362aa72a"
def certificateSHA256 : String := "7d7870a5cc432a025b04ba9b6c97235d69690d27156d3b5a2fe25982afdd1dff"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 30 → Fin 670 := ![
  0,
  3,
  10,
  13,
  17,
  19,
  55,
  142,
  146,
  161,
  168,
  187,
  302,
  318,
  322,
  437,
  443,
  455,
  496,
  562,
  603,
  655,
  657,
  660,
  661,
  662,
  663,
  664,
  666,
  669
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 30 → SparsePoly (Fin 66) := ![
  [{ coefficient := 1, powers := [(3, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (35, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (54, 1)] }, { coefficient := 1, powers := [(19, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (35, 1)] }, { coefficient := 1, powers := [(17, 1), (20, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (24, 1)] }, { coefficient := 1, powers := [(24, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (53, 1)] }, { coefficient := 1, powers := [(31, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (35, 1), (51, 1)] }, { coefficient := 1, powers := [(5, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (58, 1)] }, { coefficient := 1, powers := [(9, 1), (55, 1)] }, { coefficient := 1, powers := [(14, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (54, 1)] }, { coefficient := 1, powers := [(31, 1), (43, 1)] }, { coefficient := 1, powers := [(34, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1), (54, 1)] }, { coefficient := 1, powers := [(3, 1), (35, 1), (54, 1)] }, { coefficient := 1, powers := [(14, 1), (19, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1)] }, { coefficient := 1, powers := [(13, 1), (31, 1)] }, { coefficient := 1, powers := [(17, 1), (23, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (60, 1)] }, { coefficient := 1, powers := [(13, 1), (26, 1), (47, 1)] }, { coefficient := 1, powers := [(13, 1), (57, 1)] }, { coefficient := 1, powers := [(18, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(3, 1), (35, 1), (52, 1)] }, { coefficient := 1, powers := [(14, 1), (19, 1), (52, 1)] }, { coefficient := 1, powers := [(44, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (31, 1), (60, 1)] }, { coefficient := 1, powers := [(3, 1), (34, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (37, 1), (54, 1)] }, { coefficient := 1, powers := [(23, 1), (45, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (45, 1), (53, 1)] }, { coefficient := 1, powers := [(24, 1), (57, 1)] }, { coefficient := 1, powers := [(31, 1), (49, 1)] }, { coefficient := 1, powers := [(37, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (50, 1)] }, { coefficient := 1, powers := [(6, 1), (32, 1)] }, { coefficient := 1, powers := [(9, 1), (25, 1)] }, { coefficient := 1, powers := [(19, 1), (50, 1)] }, { coefficient := 1, powers := [(25, 1), (41, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (38, 1), (58, 1)] }, { coefficient := 1, powers := [(0, 1), (41, 1), (55, 1)] }, { coefficient := 1, powers := [(0, 1), (44, 1), (50, 1)] }, { coefficient := 1, powers := [(3, 1), (25, 1), (58, 1)] }, { coefficient := 1, powers := [(3, 1), (32, 1), (55, 1)] }, { coefficient := 1, powers := [(3, 1), (35, 1), (50, 1)] }, { coefficient := 1, powers := [(6, 1), (19, 1), (58, 1)] }, { coefficient := 1, powers := [(6, 1), (32, 1), (44, 1)] }, { coefficient := 1, powers := [(6, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(9, 1), (19, 1), (55, 1)] }, { coefficient := 1, powers := [(9, 1), (25, 1), (44, 1)] }, { coefficient := 1, powers := [(9, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(14, 1), (19, 1), (50, 1)] }, { coefficient := 1, powers := [(14, 1), (25, 1), (41, 1)] }, { coefficient := 1, powers := [(14, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (40, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (43, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (49, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (37, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (49, 1)] }, { coefficient := 1, powers := [(8, 1), (37, 1), (43, 1)] }, { coefficient := 1, powers := [(13, 1), (24, 1), (57, 1)] }, { coefficient := 1, powers := [(13, 1), (31, 1), (49, 1)] }, { coefficient := 1, powers := [(13, 1), (37, 1), (40, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (54, 1)] }, { coefficient := 1, powers := [(18, 1), (31, 1), (43, 1)] }, { coefficient := 1, powers := [(18, 1), (34, 1), (40, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(41, 1)] }],
  [{ coefficient := 1, powers := [(42, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(43, 1)] }],
  [{ coefficient := 1, powers := [(55, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(57, 1)] }],
  [{ coefficient := 1, powers := [(31, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 30 → SparsePoly (Fin 66) := ![
  [{ coefficient := 1, powers := [(8, 1), (24, 1), (25, 1), (58, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (32, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (35, 1), (50, 1)] }],
  [{ coefficient := -1, powers := [(19, 1), (24, 1), (38, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (24, 1), (26, 1), (38, 1), (58, 1)] }, { coefficient := -1, powers := [(19, 1), (24, 1), (26, 1), (38, 1), (58, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (26, 1), (44, 1), (50, 1)] }, { coefficient := 1, powers := [(24, 1), (26, 1), (32, 1), (38, 1), (44, 1)] }, { coefficient := 1, powers := [(24, 1), (26, 1), (32, 1), (38, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (32, 1), (37, 1), (38, 1)] }, { coefficient := -1, powers := [(18, 1), (24, 1), (32, 1), (38, 1), (55, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(9, 1), (20, 1), (37, 1), (38, 1), (54, 1)] }, { coefficient := -1, powers := [(19, 1), (20, 1), (37, 1), (38, 1), (51, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (17, 1), (38, 1), (49, 1), (58, 1)] }, { coefficient := -1, powers := [(3, 1), (17, 1), (25, 1), (49, 1), (58, 1)] }, { coefficient := -1, powers := [(3, 1), (17, 1), (32, 1), (49, 1), (55, 1)] }, { coefficient := -1, powers := [(3, 1), (17, 1), (35, 1), (49, 1), (50, 1)] }, { coefficient := -1, powers := [(5, 1), (25, 1), (45, 1), (58, 1)] }, { coefficient := -1, powers := [(5, 1), (32, 1), (45, 1), (55, 1)] }, { coefficient := -1, powers := [(5, 1), (35, 1), (45, 1), (50, 1)] }, { coefficient := -1, powers := [(9, 1), (17, 1), (35, 1), (38, 1), (49, 1)] }, { coefficient := -1, powers := [(14, 1), (17, 1), (32, 1), (38, 1), (49, 1)] }, { coefficient := 1, powers := [(17, 1), (19, 1), (44, 1), (49, 1), (50, 1)] }, { coefficient := 1, powers := [(17, 1), (32, 1), (38, 1), (44, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (24, 1), (38, 1), (60, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (37, 1), (38, 1), (58, 1)] }, { coefficient := -1, powers := [(18, 1), (24, 1), (38, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (37, 1), (38, 1), (54, 1)] }, { coefficient := 1, powers := [(19, 1), (37, 1), (38, 1), (51, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (32, 1), (38, 1), (60, 1)] }, { coefficient := 1, powers := [(18, 1), (32, 1), (38, 1), (54, 1), (55, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (13, 1), (38, 1), (45, 1), (58, 1)] }, { coefficient := -1, powers := [(3, 1), (13, 1), (25, 1), (45, 1), (58, 1)] }, { coefficient := -1, powers := [(3, 1), (13, 1), (32, 1), (45, 1), (55, 1)] }, { coefficient := -1, powers := [(3, 1), (13, 1), (35, 1), (45, 1), (50, 1)] }, { coefficient := -1, powers := [(9, 1), (13, 1), (35, 1), (38, 1), (45, 1)] }, { coefficient := -1, powers := [(13, 1), (14, 1), (32, 1), (38, 1), (45, 1)] }, { coefficient := 1, powers := [(13, 1), (19, 1), (44, 1), (45, 1), (50, 1)] }, { coefficient := 1, powers := [(13, 1), (32, 1), (38, 1), (44, 1), (45, 1)] }],
  [{ coefficient := -1, powers := [(19, 1), (37, 1), (38, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(19, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (18, 1), (38, 1), (58, 1)] }, { coefficient := 1, powers := [(3, 1), (18, 1), (25, 1), (58, 1)] }, { coefficient := 1, powers := [(3, 1), (18, 1), (32, 1), (55, 1)] }, { coefficient := 1, powers := [(3, 1), (18, 1), (35, 1), (50, 1)] }, { coefficient := 1, powers := [(9, 1), (18, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(14, 1), (18, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [(18, 1), (19, 1), (44, 1), (50, 1)] }, { coefficient := -1, powers := [(18, 1), (32, 1), (38, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (19, 1), (37, 1), (50, 1), (52, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (37, 1), (38, 1), (52, 1)] }, { coefficient := -1, powers := [(18, 1), (19, 1), (24, 1), (50, 1), (52, 1)] }, { coefficient := -1, powers := [(18, 1), (24, 1), (32, 1), (38, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (38, 1), (49, 1), (58, 1)] }, { coefficient := 1, powers := [(3, 1), (25, 1), (49, 1), (58, 1)] }, { coefficient := 1, powers := [(3, 1), (32, 1), (49, 1), (55, 1)] }, { coefficient := 1, powers := [(3, 1), (35, 1), (49, 1), (50, 1)] }, { coefficient := 1, powers := [(9, 1), (35, 1), (38, 1), (49, 1)] }, { coefficient := 1, powers := [(14, 1), (32, 1), (38, 1), (49, 1)] }, { coefficient := -1, powers := [(19, 1), (44, 1), (49, 1), (50, 1)] }, { coefficient := -1, powers := [(32, 1), (38, 1), (44, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (24, 1), (38, 1), (58, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (38, 1), (58, 1)] }, { coefficient := -1, powers := [(19, 1), (24, 1), (44, 1), (50, 1)] }, { coefficient := -1, powers := [(24, 1), (32, 1), (38, 1), (44, 1)] }, { coefficient := -1, powers := [(24, 1), (32, 1), (38, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (19, 1), (37, 1), (50, 1), (54, 1)] }, { coefficient := -1, powers := [(5, 1), (32, 1), (37, 1), (38, 1), (54, 1)] }, { coefficient := 1, powers := [(18, 1), (19, 1), (24, 1), (50, 1), (54, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (32, 1), (38, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (25, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (13, 1), (38, 1), (58, 1)] }, { coefficient := 1, powers := [(3, 1), (13, 1), (25, 1), (58, 1)] }, { coefficient := 1, powers := [(3, 1), (13, 1), (32, 1), (55, 1)] }, { coefficient := 1, powers := [(3, 1), (13, 1), (35, 1), (50, 1)] }, { coefficient := 1, powers := [(9, 1), (13, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(13, 1), (14, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [(13, 1), (19, 1), (44, 1), (50, 1)] }, { coefficient := -1, powers := [(13, 1), (32, 1), (38, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(44, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(0, 1), (38, 1), (58, 1)] }, { coefficient := -1, powers := [(3, 1), (25, 1), (58, 1)] }, { coefficient := -1, powers := [(3, 1), (32, 1), (55, 1)] }, { coefficient := -1, powers := [(3, 1), (35, 1), (50, 1)] }, { coefficient := -1, powers := [(9, 1), (35, 1), (38, 1)] }, { coefficient := -1, powers := [(14, 1), (32, 1), (38, 1)] }, { coefficient := 1, powers := [(19, 1), (44, 1), (50, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (38, 1), (40, 1), (58, 1), (60, 1)] }, { coefficient := 1, powers := [(3, 1), (25, 1), (40, 1), (58, 1), (60, 1)] }, { coefficient := 1, powers := [(3, 1), (32, 1), (40, 1), (55, 1), (60, 1)] }, { coefficient := 1, powers := [(3, 1), (35, 1), (40, 1), (50, 1), (60, 1)] }, { coefficient := 1, powers := [(9, 1), (35, 1), (38, 1), (40, 1), (60, 1)] }, { coefficient := 1, powers := [(14, 1), (32, 1), (38, 1), (40, 1), (60, 1)] }, { coefficient := -1, powers := [(19, 1), (40, 1), (44, 1), (50, 1), (60, 1)] }, { coefficient := -1, powers := [(32, 1), (38, 1), (40, 1), (44, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (55, 1)] }, { coefficient := 1, powers := [(6, 1), (35, 1)] }, { coefficient := 1, powers := [(14, 1), (25, 1)] }, { coefficient := -1, powers := [(25, 1), (44, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (9, 1), (24, 1), (35, 1), (38, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (8, 1), (37, 1), (38, 1), (58, 1)] }, { coefficient := 1, powers := [(3, 1), (8, 1), (25, 1), (37, 1), (58, 1)] }, { coefficient := 1, powers := [(3, 1), (8, 1), (32, 1), (37, 1), (55, 1)] }, { coefficient := 1, powers := [(3, 1), (8, 1), (35, 1), (37, 1), (50, 1)] }, { coefficient := 1, powers := [(8, 1), (9, 1), (35, 1), (37, 1), (38, 1)] }, { coefficient := 1, powers := [(8, 1), (14, 1), (32, 1), (37, 1), (38, 1)] }, { coefficient := -1, powers := [(8, 1), (19, 1), (37, 1), (44, 1), (50, 1)] }, { coefficient := -1, powers := [(8, 1), (32, 1), (37, 1), (38, 1), (44, 1)] }],
  [{ coefficient := -1, powers := [(18, 1), (24, 1), (32, 1), (38, 1), (54, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (2, 1), (38, 1), (43, 1), (58, 1)] }, { coefficient := 1, powers := [(0, 1), (5, 1), (34, 1), (38, 1), (58, 1)] }, { coefficient := -1, powers := [(0, 1), (13, 1), (24, 1), (38, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (3, 1), (25, 1), (43, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (3, 1), (32, 1), (43, 1), (55, 1)] }, { coefficient := 1, powers := [(2, 1), (3, 1), (35, 1), (43, 1), (50, 1)] }, { coefficient := 1, powers := [(2, 1), (9, 1), (35, 1), (38, 1), (43, 1)] }, { coefficient := 1, powers := [(2, 1), (14, 1), (32, 1), (38, 1), (43, 1)] }, { coefficient := -1, powers := [(2, 1), (19, 1), (43, 1), (44, 1), (50, 1)] }, { coefficient := -1, powers := [(2, 1), (32, 1), (38, 1), (43, 1), (44, 1)] }, { coefficient := 1, powers := [(5, 1), (9, 1), (34, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(5, 1), (14, 1), (32, 1), (34, 1), (38, 1)] }, { coefficient := -1, powers := [(5, 1), (19, 1), (34, 1), (44, 1), (50, 1)] }, { coefficient := -1, powers := [(5, 1), (32, 1), (34, 1), (38, 1), (44, 1)] }, { coefficient := -1, powers := [(13, 1), (19, 1), (24, 1), (38, 1), (58, 1)] }, { coefficient := 1, powers := [(13, 1), (19, 1), (24, 1), (44, 1), (50, 1)] }, { coefficient := 1, powers := [(13, 1), (24, 1), (32, 1), (38, 1), (44, 1)] }, { coefficient := 1, powers := [(13, 1), (24, 1), (32, 1), (38, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (5, 1), (38, 1), (58, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (13, 1), (38, 1), (45, 1), (48, 1), (58, 1)] }, { coefficient := -1, powers := [(0, 1), (13, 1), (38, 1), (49, 1), (58, 1)] }, { coefficient := 1, powers := [(3, 1), (13, 1), (25, 1), (45, 1), (48, 1), (58, 1)] }, { coefficient := -1, powers := [(3, 1), (13, 1), (25, 1), (49, 1), (58, 1)] }, { coefficient := 1, powers := [(3, 1), (13, 1), (32, 1), (45, 1), (48, 1), (55, 1)] }, { coefficient := -1, powers := [(3, 1), (13, 1), (32, 1), (49, 1), (55, 1)] }, { coefficient := 1, powers := [(3, 1), (13, 1), (35, 1), (45, 1), (48, 1), (50, 1)] }, { coefficient := -1, powers := [(3, 1), (13, 1), (35, 1), (49, 1), (50, 1)] }, { coefficient := 1, powers := [(5, 1), (9, 1), (35, 1), (38, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (14, 1), (32, 1), (38, 1), (60, 1)] }, { coefficient := -1, powers := [(5, 1), (19, 1), (44, 1), (50, 1), (60, 1)] }, { coefficient := -1, powers := [(5, 1), (32, 1), (38, 1), (44, 1), (60, 1)] }, { coefficient := 1, powers := [(9, 1), (13, 1), (35, 1), (38, 1), (45, 1), (48, 1)] }, { coefficient := -1, powers := [(9, 1), (13, 1), (35, 1), (38, 1), (49, 1)] }, { coefficient := 1, powers := [(13, 1), (14, 1), (32, 1), (38, 1), (45, 1), (48, 1)] }, { coefficient := -1, powers := [(13, 1), (14, 1), (32, 1), (38, 1), (49, 1)] }, { coefficient := -1, powers := [(13, 1), (19, 1), (44, 1), (45, 1), (48, 1), (50, 1)] }, { coefficient := 1, powers := [(13, 1), (19, 1), (44, 1), (49, 1), (50, 1)] }, { coefficient := -1, powers := [(13, 1), (32, 1), (38, 1), (44, 1), (45, 1), (48, 1)] }, { coefficient := 1, powers := [(13, 1), (32, 1), (38, 1), (44, 1), (49, 1)] }]
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
    ¬ ∀ index : Fin 30,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component18.SelectedLeafB4_2_6_4.selectedHasNoCommonZero

end Krenn.Component18.SelectedLeafB4_2_6_4
