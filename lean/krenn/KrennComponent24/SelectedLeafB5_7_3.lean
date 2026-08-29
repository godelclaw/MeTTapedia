import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component24.SelectedLeafB5_7_3

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "8f939773da399efb450a5a0b8d559ed33a24c3d051708934de3b5a2da50ef95a"
def certificateSHA256 : String := "1eba87b8489cfb722e33a5d28e91fb466c148d59ebe51c4e5585facf81e8610d"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 49 → Fin 673 := ![
  2,
  3,
  8,
  14,
  15,
  17,
  18,
  19,
  23,
  128,
  132,
  149,
  151,
  153,
  161,
  167,
  266,
  305,
  306,
  307,
  308,
  321,
  323,
  417,
  451,
  452,
  453,
  457,
  461,
  462,
  471,
  503,
  504,
  567,
  571,
  590,
  596,
  598,
  606,
  607,
  657,
  661,
  663,
  667,
  668,
  669,
  670,
  671,
  672
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 49 → SparsePoly (Fin 69) := ![
  [{ coefficient := 1, powers := [(8, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(31, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (55, 1)] }, { coefficient := 1, powers := [(20, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (31, 1)] }, { coefficient := 1, powers := [(31, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(15, 1), (21, 1)] }, { coefficient := 1, powers := [(21, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(15, 1), (51, 1)] }, { coefficient := 1, powers := [(51, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (20, 1)] }, { coefficient := 1, powers := [(18, 1), (26, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (45, 1)] }, { coefficient := 1, powers := [(29, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1), (55, 1)] }, { coefficient := 1, powers := [(55, 1)] }],
  [{ coefficient := 1, powers := [(15, 1), (21, 1), (54, 1)] }, { coefficient := 1, powers := [(15, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (44, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (56, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (59, 1)] }, { coefficient := 1, powers := [(9, 1), (56, 1)] }, { coefficient := 1, powers := [(15, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (61, 1)] }, { coefficient := 1, powers := [(14, 1), (58, 1)] }, { coefficient := 1, powers := [(19, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (29, 1)] }, { coefficient := 1, powers := [(24, 1), (50, 1)] }, { coefficient := 1, powers := [(29, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (42, 1)] }, { coefficient := 1, powers := [(19, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (58, 1)] }, { coefficient := 1, powers := [(31, 1), (49, 1)] }, { coefficient := 1, powers := [(37, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (20, 1), (57, 1)] }, { coefficient := 1, powers := [(14, 1)] }, { coefficient := 1, powers := [(18, 1), (20, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (48, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (60, 1)] }, { coefficient := 1, powers := [(18, 1), (25, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (49, 1)] }, { coefficient := 1, powers := [(5, 1), (37, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (49, 1)] }, { coefficient := 1, powers := [(19, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (50, 1)] }, { coefficient := 1, powers := [(13, 1), (29, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (50, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1)] }, { coefficient := 1, powers := [(14, 1), (31, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (60, 1)] }, { coefficient := 1, powers := [(18, 1), (21, 1), (53, 1)] }, { coefficient := 1, powers := [(18, 1), (21, 1), (57, 1)] }, { coefficient := 1, powers := [(18, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (61, 1)] }, { coefficient := 1, powers := [(14, 1), (49, 1)] }, { coefficient := 1, powers := [(19, 1), (21, 1), (54, 1)] }, { coefficient := 1, powers := [(19, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (55, 1)] }, { coefficient := 1, powers := [(31, 1), (43, 1)] }, { coefficient := 1, powers := [(31, 1), (48, 1), (51, 1)] }, { coefficient := 1, powers := [(34, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (40, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (25, 1), (60, 1)] }, { coefficient := 1, powers := [(18, 1), (31, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (20, 1), (57, 1)] }, { coefficient := 1, powers := [(13, 1)] }, { coefficient := 1, powers := [(18, 1), (20, 1), (52, 1)] }, { coefficient := 1, powers := [(18, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (21, 1), (57, 1)] }, { coefficient := 1, powers := [(14, 1), (48, 1)] }, { coefficient := 1, powers := [(18, 1), (21, 1), (54, 1)] }, { coefficient := 1, powers := [(18, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1), (56, 1)] }, { coefficient := 1, powers := [(6, 1), (35, 1), (43, 1)] }, { coefficient := 1, powers := [(15, 1), (21, 1), (51, 1)] }, { coefficient := 1, powers := [(15, 1), (26, 1), (43, 1)] }, { coefficient := 1, powers := [(21, 1), (51, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (41, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (44, 1), (50, 1)] }, { coefficient := 1, powers := [(13, 1), (24, 1), (56, 1)] }, { coefficient := 1, powers := [(13, 1), (29, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (42, 1), (58, 1)] }, { coefficient := 1, powers := [(8, 1), (37, 1), (42, 1)] }, { coefficient := 1, powers := [(18, 1), (30, 1), (58, 1)] }, { coefficient := 1, powers := [(18, 1), (31, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (31, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1)] }, { coefficient := 1, powers := [(3, 1), (35, 1)] }, { coefficient := 1, powers := [(15, 1), (20, 1)] }, { coefficient := 1, powers := [(20, 1), (56, 1)] }, { coefficient := 1, powers := [(26, 1), (44, 1)] }, { coefficient := 1, powers := [(35, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (50, 1)] }, { coefficient := 1, powers := [(6, 1), (32, 1)] }, { coefficient := 1, powers := [(9, 1), (26, 1)] }, { coefficient := 1, powers := [(20, 1), (50, 1)] }, { coefficient := 1, powers := [(26, 1), (41, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (43, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (48, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (57, 1)] }, { coefficient := 1, powers := [(14, 1), (25, 1), (57, 1)] }, { coefficient := 1, powers := [(14, 1), (30, 1), (48, 1)] }, { coefficient := 1, powers := [(18, 1), (25, 1), (54, 1)] }, { coefficient := 1, powers := [(18, 1), (30, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (38, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (41, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (44, 1), (50, 1)] }, { coefficient := 1, powers := [(3, 1), (26, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (32, 1), (56, 1)] }, { coefficient := 1, powers := [(3, 1), (35, 1), (50, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (32, 1), (44, 1)] }, { coefficient := 1, powers := [(6, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(9, 1), (20, 1), (56, 1)] }, { coefficient := 1, powers := [(9, 1), (26, 1), (44, 1)] }, { coefficient := 1, powers := [(9, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(15, 1), (20, 1), (50, 1)] }, { coefficient := 1, powers := [(15, 1), (26, 1), (41, 1)] }, { coefficient := 1, powers := [(15, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (40, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (43, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (49, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (37, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (25, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (49, 1)] }, { coefficient := 1, powers := [(8, 1), (37, 1), (43, 1)] }, { coefficient := 1, powers := [(14, 1), (25, 1), (58, 1)] }, { coefficient := 1, powers := [(14, 1), (31, 1), (49, 1)] }, { coefficient := 1, powers := [(14, 1), (37, 1), (40, 1)] }, { coefficient := 1, powers := [(19, 1), (25, 1), (55, 1)] }, { coefficient := 1, powers := [(19, 1), (31, 1), (43, 1)] }, { coefficient := 1, powers := [(19, 1), (34, 1), (40, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(41, 1), (64, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(42, 1), (65, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(43, 1), (66, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(56, 1)] }],
  [{ coefficient := 1, powers := [(57, 1), (67, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(58, 1), (68, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 49 → SparsePoly (Fin 69) := ![
  [{ coefficient := 1, powers := [(25, 1), (38, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (35, 1), (38, 1), (43, 1), (58, 1), (68, 1)] }, { coefficient := 1, powers := [(14, 1), (31, 1), (49, 1), (64, 1), (68, 1)] }, { coefficient := -1, powers := [(19, 1), (31, 1), (43, 1), (53, 1), (64, 1), (65, 1), (68, 1)] }, { coefficient := 1, powers := [(19, 1), (31, 1), (43, 1), (64, 1), (68, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (29, 1), (43, 1), (58, 1)] }, { coefficient := -1, powers := [(3, 1), (26, 1), (29, 1), (43, 1), (58, 1), (60, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (29, 1), (43, 1), (50, 1), (58, 1)] }, { coefficient := 1, powers := [(3, 1), (26, 1), (29, 1), (43, 1), (50, 1), (58, 1), (60, 1)] }, { coefficient := -1, powers := [(26, 1), (29, 1), (41, 1), (43, 1), (58, 1)] }, { coefficient := -1, powers := [(26, 1), (29, 1), (43, 1), (50, 1), (58, 1)] }, { coefficient := -1, powers := [(29, 1), (32, 1), (38, 1), (43, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(24, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (24, 1), (26, 1), (43, 1), (58, 1), (59, 1), (68, 1)] }, { coefficient := 1, powers := [(3, 1), (26, 1), (29, 1), (43, 1), (58, 1), (59, 1), (68, 1)] }, { coefficient := 1, powers := [(9, 1), (29, 1), (35, 1), (38, 1), (43, 1), (58, 1), (68, 1)] }, { coefficient := -1, powers := [(21, 1), (29, 1), (53, 1), (54, 1), (58, 1), (67, 1), (68, 1)] }, { coefficient := -1, powers := [(21, 1), (29, 1), (54, 1), (57, 1), (58, 1), (67, 1), (68, 1)] }, { coefficient := 1, powers := [(21, 1), (30, 1), (54, 1), (58, 1), (67, 1), (68, 1)] }, { coefficient := -1, powers := [(21, 1), (31, 1), (38, 1), (53, 1), (61, 1), (68, 1)] }, { coefficient := -1, powers := [(21, 1), (31, 1), (38, 1), (57, 1), (61, 1), (68, 1)] }, { coefficient := -1, powers := [(24, 1), (40, 1), (61, 1), (68, 1)] }, { coefficient := -1, powers := [(25, 1), (26, 1), (54, 1), (57, 1), (58, 1), (67, 1), (68, 1)] }, { coefficient := -1, powers := [(25, 1), (26, 1), (54, 1), (58, 1), (68, 1)] }, { coefficient := 1, powers := [(25, 1), (45, 1), (55, 1), (68, 1)] }, { coefficient := -1, powers := [(26, 1), (29, 1), (35, 1), (38, 1), (43, 1), (52, 1), (58, 1), (68, 1)] }, { coefficient := -1, powers := [(26, 1), (31, 1), (49, 1), (54, 1), (68, 1)] }, { coefficient := 1, powers := [(29, 1), (35, 1), (38, 1), (41, 1), (43, 1), (58, 1), (68, 1)] }, { coefficient := -1, powers := [(29, 1), (40, 1), (61, 1), (68, 1)] }, { coefficient := -1, powers := [(30, 1), (43, 1), (65, 1)] }, { coefficient := -1, powers := [(31, 1), (38, 1), (48, 1), (61, 1), (68, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (15, 1), (43, 1), (50, 1), (58, 1), (68, 1)] }, { coefficient := 1, powers := [(2, 1), (43, 1), (44, 1), (50, 1), (58, 1), (68, 1)] }, { coefficient := -1, powers := [(2, 1), (46, 1), (49, 1), (55, 1), (68, 1)] }, { coefficient := 1, powers := [(13, 1), (29, 1), (35, 1), (38, 1), (43, 1), (57, 1), (58, 1), (68, 1)] }, { coefficient := 1, powers := [(14, 1), (25, 1), (57, 2), (58, 1), (67, 1), (68, 1)] }, { coefficient := 1, powers := [(14, 1), (25, 1), (57, 1), (58, 1), (68, 1)] }, { coefficient := 1, powers := [(14, 1), (31, 1), (49, 1), (57, 1), (68, 1)] }, { coefficient := -2, powers := [(19, 1), (25, 1), (46, 1), (55, 1), (68, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (30, 1), (57, 1), (58, 1), (67, 1), (68, 1)] }, { coefficient := -1, powers := [(19, 1), (31, 1), (54, 1), (68, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (38, 1), (61, 1)] }, { coefficient := -1, powers := [(19, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (46, 1), (49, 1)] }, { coefficient := 2, powers := [(19, 1), (25, 1), (46, 1)] }],
  [{ coefficient := -1, powers := [(14, 1), (49, 1), (64, 1)] }, { coefficient := 1, powers := [(19, 1), (43, 1), (53, 1), (64, 1), (65, 1)] }, { coefficient := -1, powers := [(19, 1), (43, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (32, 1), (38, 1), (43, 1), (54, 1), (58, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (21, 1), (41, 1), (43, 1), (58, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (54, 1), (57, 1), (58, 1), (67, 1)] }, { coefficient := 1, powers := [(25, 1), (54, 1), (58, 1)] }, { coefficient := 1, powers := [(29, 1), (35, 1), (38, 1), (43, 1), (52, 1), (58, 1)] }, { coefficient := 1, powers := [(31, 1), (49, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(18, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (49, 1)] }, { coefficient := -2, powers := [(19, 1), (25, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (32, 1), (38, 1), (43, 1), (58, 1), (66, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (43, 1), (50, 1), (58, 1)] }, { coefficient := -1, powers := [(3, 1), (26, 1), (43, 1), (50, 1), (58, 1), (60, 1)] }, { coefficient := 1, powers := [(26, 1), (41, 1), (43, 1), (58, 1)] }, { coefficient := 1, powers := [(26, 1), (43, 1), (50, 1), (58, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1), (43, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (20, 1), (43, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(25, 1)] }],
  [{ coefficient := -1, powers := [(18, 1), (35, 1), (38, 1), (43, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(31, 1), (43, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(14, 1)] }],
  [{ coefficient := -1, powers := [(25, 1), (57, 1), (58, 1), (67, 1)] }, { coefficient := -1, powers := [(25, 1), (58, 1)] }, { coefficient := -1, powers := [(31, 1), (49, 1)] }],
  [{ coefficient := -1, powers := [(54, 1), (58, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(55, 1)] }],
  [{ coefficient := 1, powers := [(35, 1), (38, 1), (43, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(49, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (54, 1), (58, 1), (67, 1)] }, { coefficient := 1, powers := [(31, 1), (38, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(31, 1)] }],
  [{ coefficient := 1, powers := [(19, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (26, 1), (43, 1), (58, 1), (59, 1)] }, { coefficient := 1, powers := [(40, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(38, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(29, 1), (35, 1), (38, 1), (43, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(30, 1), (58, 1), (67, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (41, 1), (43, 1), (58, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (43, 1), (58, 1)] }, { coefficient := 1, powers := [(3, 1), (26, 1), (43, 1), (58, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(43, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (43, 1), (50, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (43, 1), (44, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(58, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (43, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(14, 1), (31, 1), (49, 1)] }, { coefficient := -1, powers := [(19, 1), (31, 1), (43, 1), (53, 1), (65, 1)] }, { coefficient := 1, powers := [(19, 1), (31, 1), (43, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (43, 1), (58, 1)] }, { coefficient := -1, powers := [(8, 1), (37, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (6, 1), (35, 1), (41, 1), (43, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (15, 1), (26, 1), (41, 1), (43, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (15, 1), (32, 1), (38, 1), (43, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (2, 1), (41, 1), (43, 2), (58, 1), (66, 1)] }, { coefficient := 1, powers := [(0, 1), (13, 1), (24, 1), (43, 1), (58, 1)] }, { coefficient := -2, powers := [(0, 1), (18, 1), (24, 1), (43, 1), (50, 1), (58, 1)] }, { coefficient := -1, powers := [(2, 1), (3, 1), (26, 1), (41, 1), (43, 1), (58, 1), (60, 1)] }, { coefficient := -1, powers := [(2, 1), (3, 1), (32, 1), (43, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (20, 1), (43, 1), (50, 1), (58, 1)] }, { coefficient := -1, powers := [(2, 1), (21, 1), (32, 1), (38, 1), (43, 1), (54, 1), (58, 1), (66, 1)] }, { coefficient := -1, powers := [(3, 1), (13, 1), (24, 1), (26, 1), (43, 1), (58, 1), (60, 1)] }, { coefficient := 1, powers := [(3, 1), (18, 1), (24, 1), (26, 1), (43, 1), (50, 1), (58, 1), (60, 1)] }, { coefficient := -1, powers := [(18, 1), (24, 1), (26, 1), (41, 1), (43, 1), (58, 1)] }, { coefficient := -1, powers := [(18, 1), (24, 1), (26, 1), (43, 1), (50, 1), (58, 1)] }, { coefficient := -1, powers := [(18, 1), (24, 1), (32, 1), (38, 1), (43, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (43, 1), (58, 1)] }, { coefficient := -1, powers := [(5, 1), (34, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (9, 1), (35, 1), (38, 1), (43, 1), (58, 1)] }, { coefficient := -1, powers := [(2, 1), (15, 1), (20, 1), (43, 1), (50, 1), (58, 1)] }, { coefficient := -1, powers := [(2, 1), (20, 1), (43, 1), (44, 1), (50, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (20, 1), (46, 1), (49, 1), (55, 1)] }, { coefficient := -1, powers := [(3, 1), (18, 1), (24, 1), (26, 1), (43, 1), (58, 1), (59, 1)] }, { coefficient := -1, powers := [(3, 1), (18, 1), (26, 1), (29, 1), (43, 1), (58, 1), (59, 1)] }, { coefficient := -1, powers := [(9, 1), (14, 1), (31, 1), (49, 1), (64, 1)] }, { coefficient := -1, powers := [(9, 1), (18, 1), (29, 1), (35, 1), (38, 1), (43, 1), (58, 1)] }, { coefficient := 1, powers := [(9, 1), (19, 1), (31, 1), (43, 1), (53, 1), (64, 1), (65, 1)] }, { coefficient := -1, powers := [(9, 1), (19, 1), (31, 1), (43, 1), (64, 1)] }, { coefficient := -1, powers := [(13, 1), (20, 1), (29, 1), (35, 1), (38, 1), (43, 1), (57, 1), (58, 1)] }, { coefficient := -1, powers := [(14, 1), (20, 1), (25, 1), (57, 2), (58, 1), (67, 1)] }, { coefficient := -1, powers := [(14, 1), (20, 1), (25, 1), (57, 1), (58, 1)] }, { coefficient := -1, powers := [(14, 1), (20, 1), (31, 1), (49, 1), (57, 1)] }, { coefficient := -1, powers := [(14, 1), (21, 1), (30, 1), (57, 1), (58, 1), (67, 1)] }, { coefficient := 1, powers := [(18, 1), (21, 1), (29, 1), (53, 1), (54, 1), (58, 1), (67, 1)] }, { coefficient := 1, powers := [(18, 1), (21, 1), (29, 1), (54, 1), (57, 1), (58, 1), (67, 1)] }, { coefficient := -1, powers := [(18, 1), (21, 1), (30, 1), (54, 1), (58, 1), (67, 1)] }, { coefficient := 1, powers := [(18, 1), (21, 1), (31, 1), (38, 1), (53, 1), (61, 1)] }, { coefficient := 1, powers := [(18, 1), (21, 1), (31, 1), (38, 1), (57, 1), (61, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (40, 1), (61, 1)] }, { coefficient := 1, powers := [(18, 1), (25, 1), (26, 1), (54, 1), (57, 1), (58, 1), (67, 1)] }, { coefficient := 1, powers := [(18, 1), (25, 1), (26, 1), (54, 1), (58, 1)] }, { coefficient := -1, powers := [(18, 1), (25, 1), (45, 1), (55, 1)] }, { coefficient := 1, powers := [(18, 1), (26, 1), (29, 1), (35, 1), (38, 1), (43, 1), (52, 1), (58, 1)] }, { coefficient := 1, powers := [(18, 1), (26, 1), (31, 1), (49, 1), (54, 1)] }, { coefficient := -1, powers := [(18, 1), (29, 1), (35, 1), (38, 1), (41, 1), (43, 1), (58, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (40, 1), (61, 1)] }, { coefficient := 1, powers := [(18, 1), (31, 1), (38, 1), (48, 1), (61, 1)] }, { coefficient := 2, powers := [(19, 1), (20, 1), (25, 1), (46, 1), (55, 1)] }, { coefficient := 1, powers := [(19, 1), (21, 1), (31, 1), (54, 1)] }]
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
    (values : Fin 69 → R) :
    ¬ ∀ index : Fin 49,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component24.SelectedLeafB5_7_3.selectedHasNoCommonZero

end Krenn.Component24.SelectedLeafB5_7_3
