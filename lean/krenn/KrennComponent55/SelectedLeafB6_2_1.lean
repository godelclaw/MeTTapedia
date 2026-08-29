import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component55.SelectedLeafB6_2_1

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "ef234c27e4ec95c76b15f13a635f24d624e3f9a43fb7b048da41495dbe93ec42"
def certificateSHA256 : String := "d80045066cab6f533c95ea4d0bf9937a91e2b322364daf08724a1c5ac0e615aa"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 41 → Fin 593 := ![
  24,
  25,
  28,
  223,
  225,
  226,
  228,
  232,
  233,
  234,
  235,
  243,
  251,
  257,
  263,
  296,
  341,
  342,
  345,
  348,
  354,
  360,
  361,
  362,
  365,
  375,
  390,
  416,
  450,
  480,
  490,
  542,
  543,
  560,
  583,
  585,
  586,
  588,
  589,
  591,
  592
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 41 → SparsePoly (Fin 62) := ![
  [{ coefficient := 1, powers := [(18, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (29, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (20, 1)] }, { coefficient := 1, powers := [(18, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (46, 1)] }, { coefficient := 1, powers := [(19, 1), (21, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (54, 1)] }, { coefficient := 1, powers := [(26, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (49, 1)] }, { coefficient := 1, powers := [(21, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (49, 1)] }, { coefficient := 1, powers := [(24, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(26, 1), (40, 1)] }, { coefficient := 1, powers := [(26, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (40, 1)] }, { coefficient := 1, powers := [(29, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(31, 1), (38, 1)] }, { coefficient := 1, powers := [(34, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (26, 1), (56, 1)] }, { coefficient := 1, powers := [(26, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (27, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (24, 1), (56, 1)] }, { coefficient := 1, powers := [(24, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (22, 1), (56, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (25, 1), (44, 1)] }, { coefficient := 1, powers := [(18, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (46, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (51, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1)] }, { coefficient := 1, powers := [(13, 1), (29, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (56, 1)] }, { coefficient := 1, powers := [(18, 1), (21, 1), (49, 1)] }, { coefficient := 1, powers := [(18, 1), (21, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (56, 1)] }, { coefficient := 1, powers := [(18, 1), (26, 1), (40, 1)] }, { coefficient := 1, powers := [(18, 1), (26, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (44, 1)] }, { coefficient := 1, powers := [(13, 1), (53, 1)] }, { coefficient := 1, powers := [(18, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (45, 1)] }, { coefficient := 1, powers := [(19, 1), (40, 1)] }, { coefficient := 1, powers := [(19, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (51, 1)] }, { coefficient := 1, powers := [(29, 1), (41, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (54, 1)] }, { coefficient := 1, powers := [(29, 1), (46, 1)] }, { coefficient := 1, powers := [(35, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1), (49, 1)] }, { coefficient := 1, powers := [(20, 1), (43, 1), (49, 1)] }, { coefficient := 1, powers := [(43, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (40, 1), (54, 1)] }, { coefficient := 1, powers := [(4, 1), (31, 1), (54, 1)] }, { coefficient := 1, powers := [(10, 1), (23, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (56, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (31, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1), (46, 1)] }, { coefficient := 1, powers := [(19, 1), (31, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (20, 1), (53, 1)] }, { coefficient := 1, powers := [(13, 1)] }, { coefficient := 1, powers := [(18, 1), (20, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (57, 1)] }, { coefficient := 1, powers := [(13, 1), (46, 1)] }, { coefficient := 1, powers := [(19, 1), (21, 1), (50, 1)] }, { coefficient := 1, powers := [(19, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (41, 1), (53, 1)] }, { coefficient := 1, powers := [(21, 1), (48, 1), (53, 1)] }, { coefficient := 1, powers := [(21, 1), (50, 1)] }, { coefficient := 1, powers := [(41, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1)] }, { coefficient := 1, powers := [(6, 1), (56, 1)] }, { coefficient := 1, powers := [(25, 1), (40, 1)] }, { coefficient := 1, powers := [(25, 1), (44, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (49, 1)] }, { coefficient := 1, powers := [(3, 1), (56, 1)] }, { coefficient := 1, powers := [(20, 1), (49, 1)] }, { coefficient := 1, powers := [(20, 1), (53, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (36, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1)] }, { coefficient := 1, powers := [(3, 1), (25, 1), (56, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1), (56, 1)] }, { coefficient := 1, powers := [(20, 1)] }, { coefficient := 1, powers := [(25, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (41, 1), (54, 1)] }, { coefficient := 1, powers := [(2, 1), (46, 1), (51, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (51, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (57, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (46, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(13, 1), (24, 1), (54, 1)] }, { coefficient := 1, powers := [(13, 1), (29, 1), (46, 1)] }, { coefficient := 1, powers := [(13, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (51, 1)] }, { coefficient := 1, powers := [(19, 1), (29, 1), (41, 1)] }, { coefficient := 1, powers := [(19, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1), (59, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(40, 1), (60, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(41, 1)] }],
  [{ coefficient := 1, powers := [(53, 1)] }],
  [{ coefficient := 1, powers := [(54, 1), (61, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 41 → SparsePoly (Fin 62) := ![
  [{ coefficient := 1, powers := [(0, 1), (36, 1), (44, 1), (45, 1), (51, 1), (56, 1), (60, 1)] }, { coefficient := 1, powers := [(3, 1), (25, 1), (44, 1), (45, 1), (51, 1), (56, 1), (60, 1)] }, { coefficient := 1, powers := [(4, 1), (25, 1), (31, 1), (45, 1), (51, 1), (59, 1), (60, 1)] }, { coefficient := -1, powers := [(6, 1), (45, 1), (51, 1), (56, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (36, 1), (44, 1), (46, 1), (50, 1), (56, 1), (60, 1)] }, { coefficient := -1, powers := [(3, 1), (25, 1), (44, 1), (46, 1), (50, 1), (56, 1), (60, 1)] }, { coefficient := 1, powers := [(6, 1), (46, 1), (50, 1), (56, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (25, 1), (59, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (29, 1), (36, 1), (44, 1), (46, 1), (50, 1), (56, 1)] }, { coefficient := 1, powers := [(3, 1), (25, 1), (29, 1), (44, 1), (46, 1), (50, 1), (56, 1)] }, { coefficient := 1, powers := [(4, 1), (25, 1), (29, 1), (31, 1), (46, 1), (50, 1), (59, 1)] }, { coefficient := -1, powers := [(6, 1), (29, 1), (46, 1), (50, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (29, 1), (36, 1), (44, 1), (48, 1), (56, 1)] }, { coefficient := -1, powers := [(3, 1), (25, 1), (29, 1), (44, 1), (48, 1), (56, 1)] }, { coefficient := -1, powers := [(4, 1), (25, 1), (29, 1), (31, 1), (48, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (29, 1), (48, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (44, 1), (56, 1), (61, 1)] }, { coefficient := 1, powers := [(44, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (6, 1), (18, 1), (29, 1), (36, 1), (44, 1), (56, 1), (57, 1)] }, { coefficient := -1, powers := [(0, 1), (18, 1), (32, 1), (36, 1), (44, 1), (54, 1)] }, { coefficient := 1, powers := [(0, 1), (19, 1), (29, 1), (36, 1), (44, 1), (48, 1), (56, 1)] }, { coefficient := -1, powers := [(3, 1), (6, 1), (18, 1), (25, 1), (29, 1), (44, 1), (56, 1), (57, 1)] }, { coefficient := -1, powers := [(3, 1), (18, 1), (25, 1), (32, 1), (44, 1), (54, 1)] }, { coefficient := 1, powers := [(3, 1), (19, 1), (25, 1), (29, 1), (44, 1), (48, 1), (56, 1)] }, { coefficient := 1, powers := [(4, 1), (18, 1), (25, 1), (27, 1), (35, 1), (51, 1), (59, 1)] }, { coefficient := 1, powers := [(4, 1), (19, 1), (25, 1), (29, 1), (31, 1), (48, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 2), (18, 1), (29, 1), (56, 1), (57, 1)] }, { coefficient := 1, powers := [(6, 1), (18, 1), (32, 1), (54, 1)] }, { coefficient := -1, powers := [(6, 1), (19, 1), (29, 1), (48, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (19, 1), (36, 1), (44, 1), (51, 1), (56, 1), (60, 1)] }, { coefficient := 1, powers := [(3, 1), (19, 1), (25, 1), (44, 1), (51, 1), (56, 1), (60, 1)] }, { coefficient := 1, powers := [(4, 1), (19, 1), (25, 1), (31, 1), (51, 1), (59, 1), (60, 1)] }, { coefficient := -1, powers := [(6, 1), (19, 1), (51, 1), (56, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (18, 1), (22, 1), (24, 1), (25, 1), (57, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (13, 1), (36, 1), (44, 1), (46, 1), (56, 1), (60, 1)] }, { coefficient := -1, powers := [(3, 1), (13, 1), (25, 1), (44, 1), (46, 1), (56, 1), (60, 1)] }, { coefficient := 1, powers := [(6, 1), (13, 1), (46, 1), (56, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (19, 1), (25, 1), (32, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (43, 1), (44, 1), (56, 1), (61, 1)] }, { coefficient := -1, powers := [(43, 1), (44, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (25, 1), (35, 1), (51, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (8, 1), (36, 1), (44, 1), (56, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (8, 1), (25, 1), (44, 1), (56, 1), (57, 1)] }, { coefficient := -1, powers := [(6, 1), (8, 1), (56, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (24, 1), (25, 1), (57, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (29, 1), (36, 1), (44, 1), (46, 1), (56, 1)] }, { coefficient := 1, powers := [(3, 1), (25, 1), (29, 1), (44, 1), (46, 1), (56, 1)] }, { coefficient := 1, powers := [(4, 1), (25, 1), (29, 1), (31, 1), (46, 1), (59, 1)] }, { coefficient := -1, powers := [(6, 1), (29, 1), (46, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (36, 1), (40, 1), (44, 1), (51, 1), (56, 1), (60, 1)] }, { coefficient := 1, powers := [(3, 1), (25, 1), (40, 1), (44, 1), (51, 1), (56, 1), (60, 1)] }, { coefficient := 1, powers := [(4, 1), (25, 1), (31, 1), (40, 1), (51, 1), (59, 1), (60, 1)] }, { coefficient := -1, powers := [(4, 1), (25, 1), (34, 1), (51, 1), (59, 1)] }, { coefficient := -1, powers := [(6, 1), (40, 1), (51, 1), (56, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (36, 1), (40, 1), (44, 1), (46, 1), (56, 1), (60, 1)] }, { coefficient := 1, powers := [(3, 1), (25, 1), (40, 1), (44, 1), (46, 1), (56, 1), (60, 1)] }, { coefficient := -1, powers := [(6, 1), (40, 1), (46, 1), (56, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (6, 1), (29, 1), (36, 1), (44, 1), (56, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (32, 1), (36, 1), (44, 1), (54, 1)] }, { coefficient := 1, powers := [(3, 1), (6, 1), (25, 1), (29, 1), (44, 1), (56, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (25, 1), (32, 1), (44, 1), (54, 1)] }, { coefficient := -1, powers := [(4, 1), (25, 1), (27, 1), (35, 1), (51, 1), (59, 1)] }, { coefficient := -1, powers := [(6, 2), (29, 1), (56, 1), (57, 1)] }, { coefficient := -1, powers := [(6, 1), (32, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (22, 1), (24, 1), (25, 1), (57, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (25, 1), (29, 1), (36, 1), (44, 1), (46, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (29, 1), (36, 1), (44, 1), (46, 1), (56, 1), (60, 1)] }, { coefficient := -1, powers := [(3, 1), (25, 2), (29, 1), (44, 1), (46, 1), (56, 1)] }, { coefficient := 1, powers := [(3, 1), (25, 1), (29, 1), (44, 1), (46, 1), (56, 1), (60, 1)] }, { coefficient := -1, powers := [(4, 1), (25, 2), (29, 1), (31, 1), (46, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (25, 1), (29, 1), (46, 1), (56, 1)] }, { coefficient := -1, powers := [(6, 1), (29, 1), (46, 1), (56, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (24, 1), (36, 1), (44, 1), (51, 1), (56, 1), (60, 1)] }, { coefficient := -1, powers := [(3, 1), (24, 1), (25, 1), (44, 1), (51, 1), (56, 1), (60, 1)] }, { coefficient := -1, powers := [(4, 1), (24, 1), (25, 1), (31, 1), (51, 1), (59, 1), (60, 1)] }, { coefficient := 1, powers := [(6, 1), (24, 1), (51, 1), (56, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (19, 1), (36, 1), (44, 1), (56, 1)] }, { coefficient := 1, powers := [(3, 1), (19, 1), (25, 1), (44, 1), (56, 1)] }, { coefficient := 1, powers := [(4, 1), (19, 1), (25, 1), (31, 1), (59, 1)] }, { coefficient := 1, powers := [(4, 1), (19, 1), (25, 1), (34, 1), (59, 1)] }, { coefficient := -1, powers := [(6, 1), (19, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (13, 1), (36, 1), (44, 1), (56, 1)] }, { coefficient := 1, powers := [(3, 1), (13, 1), (25, 1), (44, 1), (56, 1)] }, { coefficient := 1, powers := [(4, 1), (13, 1), (25, 1), (31, 1), (59, 1)] }, { coefficient := -1, powers := [(6, 1), (13, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (26, 1), (44, 1), (56, 1), (61, 1)] }, { coefficient := -1, powers := [(26, 1), (44, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(25, 1), (59, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (6, 1), (36, 1), (44, 1), (56, 1), (57, 1)] }, { coefficient := -1, powers := [(3, 1), (6, 1), (25, 1), (44, 1), (56, 1), (57, 1)] }, { coefficient := 1, powers := [(6, 2), (56, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (25, 1), (32, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (29, 1), (36, 1), (44, 1), (46, 1), (56, 1)] }, { coefficient := -1, powers := [(3, 1), (25, 1), (29, 1), (44, 1), (46, 1), (56, 1)] }, { coefficient := -1, powers := [(4, 1), (25, 1), (29, 1), (31, 1), (46, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (29, 1), (46, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (29, 1), (36, 1), (44, 1), (56, 1)] }, { coefficient := 1, powers := [(3, 1), (25, 1), (29, 1), (44, 1), (56, 1)] }, { coefficient := 1, powers := [(4, 1), (25, 1), (29, 1), (31, 1), (59, 1)] }, { coefficient := -1, powers := [(6, 1), (29, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (19, 1), (29, 1), (36, 1), (44, 1), (56, 1)] }, { coefficient := -1, powers := [(3, 1), (19, 1), (25, 1), (29, 1), (44, 1), (56, 1)] }, { coefficient := -1, powers := [(4, 1), (19, 1), (25, 1), (29, 1), (31, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (19, 1), (29, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(6, 1), (26, 1), (43, 1), (44, 1), (56, 1), (61, 1)] }, { coefficient := 1, powers := [(26, 1), (43, 1), (44, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(44, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (36, 1), (44, 1), (56, 1)] }, { coefficient := -1, powers := [(3, 1), (25, 1), (44, 1), (56, 1)] }, { coefficient := -1, powers := [(4, 1), (25, 1), (31, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (6, 1), (36, 1), (38, 1), (44, 1), (56, 2), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (36, 1), (38, 1), (44, 1), (56, 1), (57, 1)] }, { coefficient := -2, powers := [(0, 1), (36, 1), (40, 1), (44, 1), (46, 1), (51, 1), (56, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (36, 1), (44, 1), (46, 1), (51, 1), (56, 1)] }, { coefficient := 1, powers := [(3, 1), (6, 1), (25, 1), (38, 1), (44, 1), (56, 2), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (25, 1), (38, 1), (44, 1), (56, 1), (57, 1)] }, { coefficient := -2, powers := [(3, 1), (25, 1), (40, 1), (44, 1), (46, 1), (51, 1), (56, 1), (60, 1)] }, { coefficient := 1, powers := [(3, 1), (25, 1), (44, 1), (46, 1), (51, 1), (56, 1)] }, { coefficient := 1, powers := [(4, 1), (25, 1), (31, 1), (38, 1), (57, 1), (59, 1)] }, { coefficient := -1, powers := [(4, 1), (25, 1), (31, 1), (40, 1), (46, 1), (51, 1), (59, 1), (60, 1)] }, { coefficient := 1, powers := [(4, 1), (25, 1), (31, 1), (46, 1), (51, 1), (59, 1)] }, { coefficient := 1, powers := [(4, 1), (25, 1), (34, 1), (46, 1), (51, 1), (59, 1)] }, { coefficient := -1, powers := [(6, 2), (38, 1), (56, 2), (57, 1)] }, { coefficient := -1, powers := [(6, 1), (38, 1), (56, 1), (57, 1)] }, { coefficient := 2, powers := [(6, 1), (40, 1), (46, 1), (51, 1), (56, 1), (60, 1)] }, { coefficient := -1, powers := [(6, 1), (46, 1), (51, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (5, 1), (35, 1), (36, 1), (44, 1), (51, 1), (56, 1)] }, { coefficient := -1, powers := [(0, 1), (8, 1), (32, 1), (36, 1), (44, 1), (46, 1), (56, 1)] }, { coefficient := -1, powers := [(3, 1), (5, 1), (25, 1), (35, 1), (44, 1), (51, 1), (56, 1)] }, { coefficient := -1, powers := [(3, 1), (8, 1), (25, 1), (32, 1), (44, 1), (46, 1), (56, 1)] }, { coefficient := -1, powers := [(4, 1), (5, 1), (25, 1), (31, 1), (35, 1), (51, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (6, 1), (35, 1), (51, 1), (56, 1)] }, { coefficient := 1, powers := [(6, 1), (8, 1), (32, 1), (46, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (2, 1), (36, 1), (44, 1), (54, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (8, 1), (35, 1), (36, 1), (44, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (3, 1), (25, 1), (44, 1), (54, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (4, 1), (25, 1), (31, 1), (54, 1), (59, 1)] }, { coefficient := -1, powers := [(2, 1), (6, 1), (54, 1), (56, 1)] }, { coefficient := 1, powers := [(3, 1), (8, 1), (25, 1), (35, 1), (44, 1), (56, 1)] }, { coefficient := 1, powers := [(4, 1), (8, 1), (25, 1), (31, 1), (35, 1), (59, 1)] }, { coefficient := -1, powers := [(4, 1), (19, 1), (25, 1), (29, 1), (34, 1), (59, 1)] }, { coefficient := -1, powers := [(6, 1), (8, 1), (35, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(0, 2), (19, 1), (29, 1), (36, 1), (41, 1), (44, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (3, 1), (19, 1), (25, 1), (29, 1), (41, 1), (44, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (4, 1), (19, 1), (25, 1), (29, 1), (31, 1), (41, 1), (59, 1)] }, { coefficient := -1, powers := [(0, 1), (6, 1), (19, 1), (29, 1), (41, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (13, 1), (20, 1), (29, 1), (36, 1), (44, 1), (46, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (13, 1), (25, 1), (29, 1), (36, 1), (44, 1), (46, 1), (56, 1)] }, { coefficient := -1, powers := [(0, 1), (13, 1), (29, 1), (36, 1), (44, 1), (46, 1), (56, 1), (60, 1)] }, { coefficient := -1, powers := [(0, 1), (19, 1), (24, 1), (36, 1), (44, 1), (51, 1), (56, 1), (60, 1)] }, { coefficient := 1, powers := [(3, 1), (13, 1), (20, 1), (25, 1), (29, 1), (44, 1), (46, 1), (56, 1)] }, { coefficient := 1, powers := [(3, 1), (13, 1), (25, 2), (29, 1), (44, 1), (46, 1), (56, 1)] }, { coefficient := -1, powers := [(3, 1), (13, 1), (25, 1), (29, 1), (44, 1), (46, 1), (56, 1), (60, 1)] }, { coefficient := -1, powers := [(3, 1), (19, 1), (24, 1), (25, 1), (44, 1), (51, 1), (56, 1), (60, 1)] }, { coefficient := 1, powers := [(4, 1), (13, 1), (20, 1), (25, 1), (29, 1), (31, 1), (46, 1), (59, 1)] }, { coefficient := 1, powers := [(4, 1), (13, 1), (25, 2), (29, 1), (31, 1), (46, 1), (59, 1)] }, { coefficient := -1, powers := [(4, 1), (19, 1), (24, 1), (25, 1), (31, 1), (51, 1), (59, 1), (60, 1)] }, { coefficient := -1, powers := [(6, 1), (13, 1), (20, 1), (29, 1), (46, 1), (56, 1)] }, { coefficient := -1, powers := [(6, 1), (13, 1), (25, 1), (29, 1), (46, 1), (56, 1)] }, { coefficient := 1, powers := [(6, 1), (13, 1), (29, 1), (46, 1), (56, 1), (60, 1)] }, { coefficient := 1, powers := [(6, 1), (19, 1), (24, 1), (51, 1), (56, 1), (60, 1)] }, { coefficient := -1, powers := [(6, 1), (20, 1), (26, 1), (43, 1), (44, 1), (56, 1), (61, 1)] }, { coefficient := -1, powers := [(20, 1), (26, 1), (43, 1), (44, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (25, 1), (40, 1), (59, 1)] }, { coefficient := 1, powers := [(4, 1), (25, 1), (31, 1), (59, 1)] }, { coefficient := -1, powers := [(6, 1), (20, 1), (44, 1), (56, 1)] }, { coefficient := -1, powers := [(20, 1), (44, 1)] }]
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
    (values : Fin 62 → R) :
    ¬ ∀ index : Fin 41,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component55.SelectedLeafB6_2_1.selectedHasNoCommonZero

end Krenn.Component55.SelectedLeafB6_2_1
