import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component60.SelectedLeafB0_3_3

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "a32ac7652eac3318b6b96fec57ca0881a3fb4efe1ed4f05efb2d63fbca5673a0"
def certificateSHA256 : String := "d85b939e609f16effb2735960f8ac912ce1978aaecc112bc0cb6bd1b93844cfa"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 61 → Fin 665 := ![
  19,
  21,
  22,
  25,
  44,
  143,
  145,
  150,
  164,
  165,
  167,
  172,
  173,
  179,
  195,
  211,
  236,
  237,
  263,
  292,
  295,
  301,
  302,
  303,
  310,
  312,
  314,
  316,
  398,
  403,
  407,
  436,
  437,
  443,
  446,
  459,
  460,
  462,
  463,
  464,
  466,
  549,
  556,
  578,
  592,
  593,
  600,
  601,
  608,
  609,
  612,
  653,
  655,
  656,
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
def selectedEquations : Fin 61 → SparsePoly (Fin 65) := ![
  [{ coefficient := 1, powers := [(18, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (35, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (47, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (53, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (26, 1)] }, { coefficient := 1, powers := [(26, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (25, 1)] }, { coefficient := 1, powers := [(18, 1), (20, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (26, 1)] }, { coefficient := 1, powers := [(18, 1), (20, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (43, 1)] }, { coefficient := 1, powers := [(19, 1), (20, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (20, 1)] }, { coefficient := 1, powers := [(18, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (43, 1)] }, { coefficient := 1, powers := [(19, 1), (20, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (40, 1)] }, { coefficient := 1, powers := [(29, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (35, 1), (53, 1)] }, { coefficient := 1, powers := [(29, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (26, 1), (46, 1)] }, { coefficient := 1, powers := [(9, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (25, 1), (45, 1)] }, { coefficient := 1, powers := [(18, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (25, 1), (46, 1)] }, { coefficient := 1, powers := [(19, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (25, 1), (43, 1)] }, { coefficient := 1, powers := [(19, 1), (20, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1)] }, { coefficient := 1, powers := [(20, 1), (43, 1)] }, { coefficient := 1, powers := [(25, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (54, 1)] }, { coefficient := 1, powers := [(20, 1), (54, 1)] }, { coefficient := 1, powers := [(26, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (48, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1)] }, { coefficient := 1, powers := [(12, 1), (29, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (58, 1)] }, { coefficient := 1, powers := [(9, 1), (42, 1)] }, { coefficient := 1, powers := [(13, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (46, 1)] }, { coefficient := 1, powers := [(19, 1), (40, 1)] }, { coefficient := 1, powers := [(19, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1), (51, 1)] }, { coefficient := 1, powers := [(20, 1), (43, 1), (51, 1)] }, { coefficient := 1, powers := [(43, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1), (50, 1)] }, { coefficient := 1, powers := [(25, 1), (45, 1), (50, 1)] }, { coefficient := 1, powers := [(50, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (48, 1), (51, 1)] }, { coefficient := 1, powers := [(21, 1), (43, 1), (51, 1)] }, { coefficient := 1, powers := [(48, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (20, 1), (49, 1)] }, { coefficient := 1, powers := [(18, 1), (25, 1), (39, 1)] }, { coefficient := 1, powers := [(18, 1), (30, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (25, 1), (40, 1)] }, { coefficient := 1, powers := [(18, 1), (25, 1), (45, 1)] }, { coefficient := 1, powers := [(18, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (20, 1), (49, 1)] }, { coefficient := 1, powers := [(19, 1), (25, 1), (39, 1)] }, { coefficient := 1, powers := [(19, 1), (30, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (60, 1)] }, { coefficient := 1, powers := [(12, 1), (26, 1), (46, 1)] }, { coefficient := 1, powers := [(12, 1), (57, 1)] }, { coefficient := 1, powers := [(19, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (20, 1)] }, { coefficient := 1, powers := [(18, 1), (20, 1), (55, 1)] }, { coefficient := 1, powers := [(18, 1), (25, 1), (42, 1)] }, { coefficient := 1, powers := [(18, 1), (33, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (54, 1)] }, { coefficient := 1, powers := [(29, 1), (41, 1)] }, { coefficient := 1, powers := [(29, 1), (47, 1), (50, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (37, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(43, 1), (52, 1)] }, { coefficient := 1, powers := [(46, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1), (52, 1)] }, { coefficient := 1, powers := [(45, 1), (50, 1)] }, { coefficient := 1, powers := [(50, 1), (56, 1)] }, { coefficient := 1, powers := [(52, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1), (53, 1)] }, { coefficient := 1, powers := [(26, 1), (40, 1)] }, { coefficient := 1, powers := [(26, 1), (45, 1)] }, { coefficient := 1, powers := [(53, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1), (50, 1)] }, { coefficient := 1, powers := [(6, 1), (60, 1)] }, { coefficient := 1, powers := [(25, 1), (46, 1), (50, 1)] }, { coefficient := 1, powers := [(43, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1), (51, 1)] }, { coefficient := 1, powers := [(40, 1), (43, 1)] }, { coefficient := 1, powers := [(43, 1), (51, 1)] }, { coefficient := 1, powers := [(46, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1), (54, 1)] }, { coefficient := 1, powers := [(26, 1), (46, 1), (50, 1)] }, { coefficient := 1, powers := [(43, 1), (54, 1)] }, { coefficient := 1, powers := [(50, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1), (50, 1)] }, { coefficient := 1, powers := [(21, 1), (50, 1)] }, { coefficient := 1, powers := [(25, 1), (41, 1)] }, { coefficient := 1, powers := [(25, 1), (47, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (26, 1), (46, 1)] }, { coefficient := 1, powers := [(18, 1), (57, 1)] }, { coefficient := 1, powers := [(19, 1), (26, 1), (40, 1)] }, { coefficient := 1, powers := [(19, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (43, 1), (53, 1)] }, { coefficient := 1, powers := [(24, 1), (57, 1)] }, { coefficient := 1, powers := [(29, 1), (48, 1)] }, { coefficient := 1, powers := [(35, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1)] }, { coefficient := 1, powers := [(6, 1), (59, 1)] }, { coefficient := 1, powers := [(25, 1), (40, 1)] }, { coefficient := 1, powers := [(25, 1), (45, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (46, 1), (53, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (40, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (46, 1)] }, { coefficient := 1, powers := [(19, 1), (29, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (41, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (47, 1), (52, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (56, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (56, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1)] }, { coefficient := 1, powers := [(3, 1), (33, 1)] }, { coefficient := 1, powers := [(13, 1), (20, 1)] }, { coefficient := 1, powers := [(20, 1), (55, 1)] }, { coefficient := 1, powers := [(25, 1), (42, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (49, 1)] }, { coefficient := 1, powers := [(6, 1), (30, 1)] }, { coefficient := 1, powers := [(9, 1), (25, 1)] }, { coefficient := 1, powers := [(20, 1), (49, 1)] }, { coefficient := 1, powers := [(25, 1), (39, 1)] }, { coefficient := 1, powers := [(30, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (46, 1), (53, 1)] }, { coefficient := 1, powers := [(26, 1), (40, 1), (43, 1)] }, { coefficient := 1, powers := [(26, 1), (46, 1)] }, { coefficient := 1, powers := [(43, 1), (53, 1)] }, { coefficient := 1, powers := [(57, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (41, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (47, 1), (52, 1)] }, { coefficient := 1, powers := [(21, 1), (50, 1), (56, 1)] }, { coefficient := 1, powers := [(21, 1), (52, 1)] }, { coefficient := 1, powers := [(41, 1)] }, { coefficient := 1, powers := [(47, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1), (49, 1)] }, { coefficient := 1, powers := [(6, 1), (30, 1), (44, 1)] }, { coefficient := 1, powers := [(6, 1), (58, 1)] }, { coefficient := 1, powers := [(9, 1), (25, 1), (44, 1)] }, { coefficient := 1, powers := [(9, 1), (55, 1)] }, { coefficient := 1, powers := [(13, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (36, 1), (58, 1)] }, { coefficient := 1, powers := [(0, 1), (39, 1), (55, 1)] }, { coefficient := 1, powers := [(0, 1), (42, 1), (49, 1)] }, { coefficient := 1, powers := [(3, 1), (25, 1), (58, 1)] }, { coefficient := 1, powers := [(3, 1), (30, 1), (55, 1)] }, { coefficient := 1, powers := [(3, 1), (33, 1), (49, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1), (58, 1)] }, { coefficient := 1, powers := [(6, 1), (30, 1), (42, 1)] }, { coefficient := 1, powers := [(6, 1), (33, 1), (39, 1)] }, { coefficient := 1, powers := [(9, 1), (20, 1), (55, 1)] }, { coefficient := 1, powers := [(9, 1), (25, 1), (42, 1)] }, { coefficient := 1, powers := [(9, 1), (33, 1), (36, 1)] }, { coefficient := 1, powers := [(13, 1), (20, 1), (49, 1)] }, { coefficient := 1, powers := [(13, 1), (25, 1), (39, 1)] }, { coefficient := 1, powers := [(13, 1), (30, 1), (36, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (41, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (48, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (48, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1), (29, 1), (48, 1)] }, { coefficient := 1, powers := [(12, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (54, 1)] }, { coefficient := 1, powers := [(19, 1), (29, 1), (41, 1)] }, { coefficient := 1, powers := [(19, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1)] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(39, 1)] }],
  [{ coefficient := 1, powers := [(40, 1), (61, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(41, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(55, 1)] }],
  [{ coefficient := 1, powers := [(56, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(57, 1), (64, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 61 → SparsePoly (Fin 65) := ![
  [{ coefficient := 1, powers := [(13, 1), (20, 1), (24, 1), (50, 1), (57, 1)] }, { coefficient := -1, powers := [(13, 1), (24, 1), (25, 1), (50, 1), (57, 1)] }, { coefficient := 1, powers := [(24, 1), (25, 1), (42, 1), (50, 1), (57, 1)] }, { coefficient := 1, powers := [(24, 1), (33, 1), (36, 1), (50, 1), (57, 1)] }],
  [{ coefficient := -2, powers := [(13, 1), (20, 1), (24, 1), (50, 1), (53, 1)] }, { coefficient := 4, powers := [(13, 1), (20, 1), (24, 1), (54, 1)] }, { coefficient := -1, powers := [(24, 1), (25, 1), (42, 1), (50, 1), (53, 1)] }, { coefficient := 2, powers := [(24, 1), (25, 1), (42, 1), (54, 1)] }, { coefficient := -1, powers := [(24, 1), (33, 1), (36, 1), (50, 1), (53, 1)] }, { coefficient := 2, powers := [(24, 1), (33, 1), (36, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (25, 1), (51, 1), (53, 1)] }, { coefficient := -1, powers := [(12, 1), (26, 1), (51, 1)] }, { coefficient := -1, powers := [(12, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (25, 1), (46, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (43, 1), (59, 1)] }, { coefficient := -1, powers := [(19, 1), (21, 1), (45, 1)] }, { coefficient := -1, powers := [(19, 1), (25, 1), (45, 1), (47, 1)] }, { coefficient := -1, powers := [(19, 1), (47, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (21, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(52, 1), (57, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(41, 1), (46, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(17, 1), (20, 1), (24, 1), (46, 1), (50, 1), (57, 1), (64, 1)] }, { coefficient := -2, powers := [(18, 1), (24, 1), (25, 1), (42, 1), (46, 1), (50, 1), (57, 1), (64, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (25, 1), (42, 1), (46, 1), (50, 1), (53, 1), (64, 1)] }, { coefficient := -2, powers := [(19, 1), (24, 1), (25, 1), (42, 1), (46, 1), (54, 1), (64, 1)] }, { coefficient := -1, powers := [(19, 1), (24, 1), (33, 1), (36, 1), (46, 1), (50, 1), (53, 1), (64, 1)] }, { coefficient := 2, powers := [(19, 1), (24, 1), (33, 1), (36, 1), (46, 1), (54, 1), (64, 1)] }],
  [{ coefficient := 2, powers := [(24, 1), (46, 1), (53, 1)] }],
  [{ coefficient := 2, powers := [(24, 1), (40, 1), (43, 1)] }, { coefficient := 2, powers := [(24, 1), (43, 1), (45, 1)] }, { coefficient := -1, powers := [(24, 1), (46, 1)] }],
  [{ coefficient := 2, powers := [(24, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (24, 1), (50, 1), (57, 1), (58, 1)] }, { coefficient := -2, powers := [(24, 1), (40, 1), (43, 1), (54, 1)] }, { coefficient := -2, powers := [(24, 1), (43, 1), (45, 1), (54, 1)] }, { coefficient := -2, powers := [(24, 1), (46, 1), (50, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(24, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (25, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (21, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (20, 1), (24, 1), (50, 1), (57, 1), (64, 1)] }, { coefficient := 2, powers := [(18, 1), (24, 1), (25, 1), (42, 1), (50, 1), (57, 1), (64, 1)] }, { coefficient := -1, powers := [(19, 1), (24, 1), (25, 1), (42, 1), (50, 1), (53, 1), (64, 1)] }, { coefficient := 2, powers := [(19, 1), (24, 1), (25, 1), (42, 1), (54, 1), (64, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (33, 1), (36, 1), (50, 1), (53, 1), (64, 1)] }, { coefficient := -2, powers := [(19, 1), (24, 1), (33, 1), (36, 1), (54, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (57, 1)] }],
  [{ coefficient := -2, powers := [(24, 1), (53, 1)] }],
  [{ coefficient := -2, powers := [(24, 1), (52, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (24, 1), (51, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (24, 1), (46, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(54, 1)] }],
  [{ coefficient := 1, powers := [(48, 1)] }],
  [{ coefficient := -1, powers := [(18, 1), (24, 1), (25, 1), (50, 1), (57, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (25, 1), (50, 1), (53, 1)] }, { coefficient := -2, powers := [(19, 1), (24, 1), (25, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(24, 1), (26, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (24, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (24, 1), (47, 1), (57, 1), (62, 1)] }, { coefficient := 1, powers := [(19, 1), (29, 1), (47, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (29, 1)] }],
  [{ coefficient := -1, powers := [(13, 1), (24, 1), (50, 1), (57, 1)] }, { coefficient := 1, powers := [(24, 1), (25, 1), (44, 1), (50, 1), (57, 1)] }, { coefficient := 1, powers := [(24, 1), (42, 1), (50, 1), (57, 1)] }],
  [{ coefficient := 2, powers := [(24, 1), (43, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (24, 1), (50, 1), (53, 1)] }, { coefficient := -2, powers := [(13, 1), (24, 1), (54, 1)] }, { coefficient := 1, powers := [(20, 1), (24, 1), (44, 1), (50, 1), (53, 1)] }, { coefficient := -2, powers := [(20, 1), (24, 1), (44, 1), (54, 1)] }, { coefficient := -1, powers := [(24, 1), (42, 1), (50, 1), (53, 1)] }, { coefficient := 2, powers := [(24, 1), (42, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(24, 1)] }],
  [{ coefficient := -1, powers := [(9, 1), (24, 1), (50, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(19, 1)] }],
  [{ coefficient := 2, powers := [(18, 1), (24, 1), (25, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (21, 1), (24, 1), (57, 1), (62, 1)] }, { coefficient := 1, powers := [(19, 1), (21, 1), (29, 1)] }],
  [{ coefficient := -2, powers := [(12, 1), (24, 1), (43, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (29, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (24, 1), (26, 1)] }],
  [{ coefficient := -1, powers := [(18, 1), (24, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (24, 1), (45, 1), (57, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(12, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (29, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(41, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(57, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(18, 1), (24, 1), (49, 1), (50, 1), (57, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (49, 1), (50, 1), (53, 1)] }, { coefficient := -2, powers := [(19, 1), (24, 1), (49, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(18, 1), (24, 1), (25, 1), (44, 1), (50, 1), (57, 1)] }, { coefficient := -1, powers := [(18, 1), (24, 1), (42, 1), (50, 1), (57, 1)] }, { coefficient := -1, powers := [(19, 1), (20, 1), (24, 1), (44, 1), (50, 1), (53, 1)] }, { coefficient := 2, powers := [(19, 1), (20, 1), (24, 1), (44, 1), (54, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (42, 1), (50, 1), (53, 1)] }, { coefficient := -2, powers := [(19, 1), (24, 1), (42, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (24, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (24, 1), (57, 1), (62, 1)] }, { coefficient := -1, powers := [(19, 1), (29, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (24, 1), (25, 1), (50, 1), (57, 1)] }, { coefficient := 1, powers := [(19, 1), (20, 1), (24, 1), (50, 1), (53, 1)] }, { coefficient := -2, powers := [(19, 1), (20, 1), (24, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (24, 1), (50, 1), (57, 1)] }, { coefficient := -1, powers := [(19, 1), (24, 1), (50, 1), (53, 1)] }, { coefficient := 2, powers := [(19, 1), (24, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(5, 1), (29, 1), (45, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (46, 1), (50, 1), (59, 1)] }, { coefficient := -1, powers := [(12, 1), (21, 1), (24, 1), (45, 1), (52, 1), (57, 1), (62, 1)] }, { coefficient := -1, powers := [(12, 1), (24, 1), (26, 1), (46, 1), (51, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (41, 1), (56, 1), (57, 1), (62, 1)] }, { coefficient := 2, powers := [(12, 1), (24, 1), (43, 1), (45, 1), (53, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (46, 1), (53, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (47, 1), (52, 1), (57, 1), (62, 1)] }, { coefficient := 1, powers := [(12, 1), (29, 1), (48, 1), (51, 1)] }, { coefficient := -2, powers := [(18, 1), (24, 1), (25, 1), (37, 1), (53, 1), (60, 1)] }, { coefficient := -2, powers := [(18, 1), (24, 1), (25, 1), (46, 1), (52, 1), (53, 1)] }, { coefficient := -1, powers := [(18, 1), (24, 1), (36, 1), (50, 1), (57, 1), (58, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (42, 1), (49, 1), (50, 1), (57, 1)] }, { coefficient := -1, powers := [(19, 1), (21, 1), (29, 1), (45, 1), (52, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (36, 1), (50, 1), (53, 1), (58, 1)] }, { coefficient := -2, powers := [(19, 1), (24, 1), (36, 1), (54, 1), (58, 1)] }, { coefficient := -1, powers := [(19, 1), (24, 1), (42, 1), (49, 1), (50, 1), (53, 1)] }, { coefficient := 2, powers := [(19, 1), (24, 1), (42, 1), (49, 1), (54, 1)] }, { coefficient := -1, powers := [(19, 1), (24, 1), (51, 1), (54, 1)] }, { coefficient := 1, powers := [(19, 1), (29, 1), (41, 1), (56, 1)] }, { coefficient := -1, powers := [(19, 1), (29, 1), (45, 1), (47, 1), (50, 1)] }, { coefficient := 1, powers := [(19, 1), (29, 1), (47, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(38, 1), (60, 1)] }, { coefficient := -1, powers := [(40, 1), (41, 1), (57, 1), (61, 1)] }, { coefficient := -1, powers := [(41, 1), (56, 1), (57, 1), (63, 1)] }, { coefficient := 1, powers := [(41, 1), (57, 1)] }, { coefficient := -1, powers := [(48, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (18, 1), (24, 1), (50, 1), (55, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (19, 1), (24, 1), (50, 1), (53, 1), (55, 1)] }, { coefficient := -2, powers := [(0, 1), (19, 1), (24, 1), (54, 1), (55, 1)] }, { coefficient := -1, powers := [(6, 1), (18, 1), (24, 1), (33, 1), (50, 1), (57, 1)] }, { coefficient := 1, powers := [(6, 1), (19, 1), (24, 1), (33, 1), (50, 1), (53, 1)] }, { coefficient := -2, powers := [(6, 1), (19, 1), (24, 1), (33, 1), (54, 1)] }, { coefficient := 1, powers := [(13, 1), (18, 1), (24, 1), (25, 1), (50, 1), (57, 1)] }, { coefficient := -1, powers := [(13, 1), (19, 1), (24, 1), (25, 1), (50, 1), (53, 1)] }, { coefficient := 2, powers := [(13, 1), (19, 1), (24, 1), (25, 1), (54, 1)] }, { coefficient := 1, powers := [(17, 1), (20, 1), (24, 1), (26, 1), (46, 1), (50, 1), (57, 1), (64, 1)] }, { coefficient := 2, powers := [(18, 1), (24, 1), (25, 1), (26, 1), (42, 1), (46, 1), (50, 1), (57, 1), (64, 1)] }, { coefficient := -1, powers := [(19, 1), (24, 1), (25, 1), (26, 1), (42, 1), (46, 1), (50, 1), (53, 1), (64, 1)] }, { coefficient := 2, powers := [(19, 1), (24, 1), (25, 1), (26, 1), (42, 1), (46, 1), (54, 1), (64, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (26, 1), (33, 1), (36, 1), (46, 1), (50, 1), (53, 1), (64, 1)] }, { coefficient := -2, powers := [(19, 1), (24, 1), (26, 1), (33, 1), (36, 1), (46, 1), (54, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (35, 1), (41, 1)] }, { coefficient := -1, powers := [(19, 1), (29, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (24, 1), (25, 1), (45, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (18, 1), (24, 1), (30, 1), (50, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (19, 1), (24, 1), (30, 1), (50, 1), (53, 1)] }, { coefficient := -2, powers := [(3, 1), (19, 1), (24, 1), (30, 1), (54, 1)] }, { coefficient := -1, powers := [(9, 1), (18, 1), (24, 1), (25, 1), (50, 1), (57, 1)] }, { coefficient := 1, powers := [(18, 1), (20, 1), (24, 1), (49, 1), (50, 1), (57, 1)] }, { coefficient := -1, powers := [(19, 1), (20, 1), (24, 1), (49, 1), (50, 1), (53, 1)] }, { coefficient := 2, powers := [(19, 1), (20, 1), (24, 1), (49, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (32, 1), (57, 1)] }, { coefficient := -1, powers := [(12, 1), (24, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [(9, 1), (17, 1), (20, 1), (24, 1), (50, 1), (57, 1)] }, { coefficient := -2, powers := [(9, 1), (18, 1), (24, 1), (25, 1), (42, 1), (50, 1), (57, 1)] }, { coefficient := 1, powers := [(9, 1), (19, 1), (24, 1), (25, 1), (42, 1), (50, 1), (53, 1)] }, { coefficient := -2, powers := [(9, 1), (19, 1), (24, 1), (25, 1), (42, 1), (54, 1)] }, { coefficient := -1, powers := [(9, 1), (19, 1), (24, 1), (33, 1), (36, 1), (50, 1), (53, 1)] }, { coefficient := 2, powers := [(9, 1), (19, 1), (24, 1), (33, 1), (36, 1), (54, 1)] }]
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
    ¬ ∀ index : Fin 61,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component60.SelectedLeafB0_3_3.selectedHasNoCommonZero

end Krenn.Component60.SelectedLeafB0_3_3
