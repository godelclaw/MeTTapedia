import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component13.SelectedLeafB4_3

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "4a21215c610638dfc8d9ff342b09ad887b32a5369e031647b516446517fbf791"
def certificateSHA256 : String := "2a7d7709a106cba24dcf9a266ddbc70b65fb8db52b1bab90aa49fa54f65e3668"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 56 → Fin 611 := ![
  0,
  2,
  8,
  12,
  17,
  19,
  23,
  127,
  133,
  150,
  151,
  152,
  158,
  159,
  161,
  162,
  170,
  173,
  183,
  184,
  188,
  189,
  192,
  284,
  327,
  352,
  353,
  360,
  361,
  373,
  376,
  377,
  381,
  389,
  407,
  425,
  426,
  480,
  483,
  485,
  489,
  498,
  525,
  532,
  533,
  548,
  549,
  550,
  551,
  603,
  604,
  605,
  606,
  607,
  609,
  610
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 56 → SparsePoly (Fin 61) := ![
  [{ coefficient := 1, powers := [(4, 1), (33, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (30, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(15, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(30, 1), (35, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (41, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (43, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1)] }, { coefficient := 1, powers := [(23, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1)] }, { coefficient := 1, powers := [(23, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (50, 1)] }, { coefficient := 1, powers := [(18, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (57, 1)] }, { coefficient := 1, powers := [(41, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (57, 1)] }, { coefficient := 1, powers := [(7, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (57, 1)] }, { coefficient := 1, powers := [(41, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (56, 1)] }, { coefficient := 1, powers := [(16, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (43, 1)] }, { coefficient := 1, powers := [(12, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (18, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (51, 1)] }, { coefficient := 1, powers := [(27, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (41, 1)] }, { coefficient := 1, powers := [(26, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (38, 1)] }, { coefficient := 1, powers := [(27, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(38, 1), (41, 1)] }, { coefficient := 1, powers := [(41, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(43, 1), (47, 1)] }, { coefficient := 1, powers := [(47, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (18, 1), (53, 1)] }, { coefficient := 1, powers := [(12, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (47, 1), (53, 1)] }, { coefficient := 1, powers := [(47, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (41, 1)] }, { coefficient := 1, powers := [(18, 1), (41, 1)] }, { coefficient := 1, powers := [(23, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1)] }, { coefficient := 1, powers := [(18, 1), (47, 1)] }, { coefficient := 1, powers := [(23, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1), (45, 1)] }, { coefficient := 1, powers := [(17, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1), (54, 1)] }, { coefficient := 1, powers := [(17, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (39, 1), (53, 1)] }, { coefficient := 1, powers := [(39, 1)] }, { coefficient := 1, powers := [(44, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (41, 1), (49, 1)] }, { coefficient := 1, powers := [(18, 1), (41, 1), (49, 1)] }, { coefficient := 1, powers := [(41, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (41, 1), (50, 1)] }, { coefficient := 1, powers := [(18, 1), (41, 1), (50, 1)] }, { coefficient := 1, powers := [(18, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1), (47, 1)] }, { coefficient := 1, powers := [(23, 1), (39, 1)] }, { coefficient := 1, powers := [(23, 1), (44, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (39, 1), (53, 1)] }, { coefficient := 1, powers := [(7, 1), (32, 1), (39, 1)] }, { coefficient := 1, powers := [(15, 1), (25, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (38, 1)] }, { coefficient := 1, powers := [(17, 1), (27, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (27, 1), (57, 1)] }, { coefficient := 1, powers := [(4, 1), (30, 1), (54, 1)] }, { coefficient := 1, powers := [(4, 1), (33, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (30, 1), (53, 1)] }, { coefficient := 1, powers := [(7, 1), (30, 1), (43, 1)] }, { coefficient := 1, powers := [(15, 1), (30, 1), (35, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (45, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1)] }, { coefficient := 1, powers := [(16, 1), (26, 1), (45, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (51, 1)] }, { coefficient := 1, powers := [(8, 1), (30, 1)] }, { coefficient := 1, powers := [(12, 1), (27, 1)] }, { coefficient := 1, powers := [(16, 1), (21, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (30, 1)] }, { coefficient := 1, powers := [(21, 1), (47, 1)] }, { coefficient := 1, powers := [(26, 1), (47, 1)] }, { coefficient := 1, powers := [(30, 1), (34, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (51, 1)] }, { coefficient := 1, powers := [(27, 1), (39, 1)] }, { coefficient := 1, powers := [(27, 1), (44, 1), (47, 1)] }, { coefficient := 1, powers := [(30, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (34, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1)] }, { coefficient := 1, powers := [(16, 1), (21, 1)] }, { coefficient := 1, powers := [(16, 1), (26, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (41, 1), (50, 1)] }, { coefficient := 1, powers := [(22, 1), (54, 1)] }, { coefficient := 1, powers := [(27, 1), (45, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1)] }, { coefficient := 1, powers := [(6, 1), (56, 1)] }, { coefficient := 1, powers := [(23, 1), (38, 1)] }, { coefficient := 1, powers := [(23, 1), (43, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (49, 1)] }, { coefficient := 1, powers := [(3, 1), (56, 1)] }, { coefficient := 1, powers := [(18, 1), (49, 1)] }, { coefficient := 1, powers := [(18, 1), (53, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(4, 1), (56, 1)] }, { coefficient := 1, powers := [(7, 1), (56, 1)] }, { coefficient := 1, powers := [(11, 1), (43, 1)] }, { coefficient := 1, powers := [(11, 1), (53, 1)] }, { coefficient := 1, powers := [(15, 1), (38, 1)] }, { coefficient := 1, powers := [(15, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (49, 1)] }, { coefficient := 1, powers := [(20, 1), (53, 1)] }, { coefficient := 1, powers := [(25, 1), (38, 1)] }, { coefficient := 1, powers := [(25, 1), (43, 1)] }, { coefficient := 1, powers := [(29, 1), (35, 1)] }, { coefficient := 1, powers := [(32, 1), (35, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (34, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1)] }, { coefficient := 1, powers := [(3, 1), (23, 1), (56, 1)] }, { coefficient := 1, powers := [(6, 1), (18, 1), (56, 1)] }, { coefficient := 1, powers := [(18, 1)] }, { coefficient := 1, powers := [(23, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (34, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (41, 1), (47, 1)] }, { coefficient := 1, powers := [(3, 1), (23, 1), (57, 1)] }, { coefficient := 1, powers := [(6, 1), (18, 1), (57, 1)] }, { coefficient := 1, powers := [(18, 1), (41, 1), (47, 1)] }, { coefficient := 1, powers := [(23, 1), (41, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (35, 1), (56, 1)] }, { coefficient := 1, powers := [(1, 1), (38, 1), (53, 1)] }, { coefficient := 1, powers := [(1, 1), (43, 1), (49, 1)] }, { coefficient := 1, powers := [(4, 1), (25, 1), (56, 1)] }, { coefficient := 1, powers := [(4, 1), (29, 1), (53, 1)] }, { coefficient := 1, powers := [(4, 1), (32, 1), (49, 1)] }, { coefficient := 1, powers := [(7, 1), (20, 1), (56, 1)] }, { coefficient := 1, powers := [(7, 1), (29, 1), (43, 1)] }, { coefficient := 1, powers := [(7, 1), (32, 1), (38, 1)] }, { coefficient := 1, powers := [(11, 1), (20, 1), (53, 1)] }, { coefficient := 1, powers := [(11, 1), (25, 1), (43, 1)] }, { coefficient := 1, powers := [(11, 1), (32, 1), (35, 1)] }, { coefficient := 1, powers := [(15, 1), (20, 1), (49, 1)] }, { coefficient := 1, powers := [(15, 1), (25, 1), (38, 1)] }, { coefficient := 1, powers := [(15, 1), (29, 1), (35, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (36, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (39, 1), (54, 1)] }, { coefficient := 1, powers := [(2, 1), (45, 1), (51, 1)] }, { coefficient := 1, powers := [(5, 1), (27, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (51, 1)] }, { coefficient := 1, powers := [(8, 1), (22, 1), (57, 1)] }, { coefficient := 1, powers := [(8, 1), (30, 1), (45, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (39, 1)] }, { coefficient := 1, powers := [(12, 1), (22, 1), (54, 1)] }, { coefficient := 1, powers := [(12, 1), (27, 1), (45, 1)] }, { coefficient := 1, powers := [(12, 1), (33, 1), (36, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (51, 1)] }, { coefficient := 1, powers := [(17, 1), (27, 1), (39, 1)] }, { coefficient := 1, powers := [(17, 1), (30, 1), (36, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (58, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1)] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(38, 1), (59, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(39, 1), (60, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 56 → SparsePoly (Fin 61) := ![
  [{ coefficient := -2, powers := [(5, 1), (32, 1), (49, 1), (51, 1)] }],
  [{ coefficient := 2, powers := [(5, 1), (20, 1), (54, 1), (56, 1)] }, { coefficient := -2, powers := [(5, 1), (25, 1), (54, 1), (56, 1)] }, { coefficient := 2, powers := [(5, 1), (32, 1), (38, 1), (54, 1)] }],
  [{ coefficient := 2, powers := [(5, 1), (20, 1), (30, 1), (53, 1)] }, { coefficient := -2, powers := [(5, 1), (25, 1), (30, 1), (53, 1)] }],
  [{ coefficient := -2, powers := [(5, 1), (20, 1), (30, 1), (53, 1), (54, 1), (60, 1)] }, { coefficient := -2, powers := [(5, 1), (25, 1), (27, 1), (49, 1), (57, 1), (60, 1)] }, { coefficient := -2, powers := [(5, 1), (25, 1), (30, 1), (38, 1), (54, 1), (60, 1)] }, { coefficient := -2, powers := [(5, 1), (25, 1), (30, 1), (43, 1), (54, 1), (60, 1)] }, { coefficient := -2, powers := [(5, 1), (25, 1), (30, 1), (49, 1), (54, 1), (60, 1)] }, { coefficient := -2, powers := [(5, 1), (30, 1), (32, 1), (35, 1), (54, 1), (60, 1)] }],
  [{ coefficient := -2, powers := [(26, 1), (51, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (21, 1), (45, 1), (53, 1)] }, { coefficient := 1, powers := [(6, 1), (21, 1), (45, 1), (56, 1)] }, { coefficient := -1, powers := [(21, 1), (45, 1)] }],
  [{ coefficient := 2, powers := [(5, 1), (11, 1), (32, 1), (54, 1)] }, { coefficient := -2, powers := [(5, 1), (15, 1), (29, 1), (54, 1)] }],
  [{ coefficient := 2, powers := [(12, 1), (50, 1), (59, 1)] }],
  [{ coefficient := 2, powers := [(17, 1), (44, 1), (59, 1)] }],
  [{ coefficient := 2, powers := [(5, 1), (27, 1), (34, 1), (47, 1), (49, 1), (56, 1), (57, 1), (60, 1)] }, { coefficient := -2, powers := [(5, 1), (27, 1), (47, 1), (49, 1), (57, 1), (60, 1)] }, { coefficient := -4, powers := [(5, 1), (27, 1), (47, 1), (53, 1), (57, 1), (60, 1)] }, { coefficient := 2, powers := [(8, 1), (22, 1), (34, 1), (47, 1), (49, 1), (56, 1), (57, 1), (60, 1)] }, { coefficient := -2, powers := [(8, 1), (22, 1), (47, 1), (49, 1), (57, 1), (60, 1)] }, { coefficient := -4, powers := [(8, 1), (22, 1), (47, 1), (53, 1), (57, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (30, 1), (34, 1), (45, 1), (47, 1), (56, 1), (58, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (30, 1), (45, 1), (47, 1), (53, 1), (60, 1)] }, { coefficient := 2, powers := [(8, 1), (30, 1), (45, 1), (47, 1), (58, 1), (60, 1)] }],
  [{ coefficient := 2, powers := [(8, 1), (30, 1), (58, 1)] }],
  [{ coefficient := 2, powers := [(12, 1), (22, 1), (41, 1), (53, 1)] }, { coefficient := 1, powers := [(16, 1), (30, 1), (34, 1), (45, 1), (58, 1)] }],
  [{ coefficient := -2, powers := [(5, 1), (23, 2), (27, 1), (49, 1), (56, 1), (58, 1)] }, { coefficient := -2, powers := [(5, 1), (27, 1), (56, 1)] }, { coefficient := -2, powers := [(8, 1), (22, 1), (23, 2), (49, 1), (56, 1), (58, 1)] }, { coefficient := -2, powers := [(8, 1), (22, 1), (56, 1)] }],
  [{ coefficient := -2, powers := [(5, 1), (27, 1), (32, 1), (49, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (5, 1), (23, 1), (27, 1), (49, 1), (56, 1), (58, 1)] }, { coefficient := 2, powers := [(0, 1), (5, 1), (27, 1), (43, 1), (56, 1)] }, { coefficient := -2, powers := [(0, 1), (8, 1), (22, 1), (23, 1), (49, 1), (56, 1), (58, 1)] }, { coefficient := 2, powers := [(0, 1), (8, 1), (22, 1), (43, 1), (56, 1)] }, { coefficient := 2, powers := [(5, 1), (6, 1), (27, 1), (56, 2)] }, { coefficient := -2, powers := [(5, 1), (18, 1), (23, 1), (27, 1), (49, 1), (56, 1), (58, 1)] }, { coefficient := 2, powers := [(5, 1), (23, 1), (27, 1), (38, 1), (56, 1)] }, { coefficient := 2, powers := [(5, 1), (23, 1), (27, 1), (43, 1), (56, 1)] }, { coefficient := 2, powers := [(5, 1), (23, 1), (27, 1), (49, 1), (56, 1)] }, { coefficient := 2, powers := [(5, 1), (27, 1), (56, 1)] }, { coefficient := 2, powers := [(6, 1), (8, 1), (22, 1), (56, 2)] }, { coefficient := -2, powers := [(8, 1), (18, 1), (22, 1), (23, 1), (49, 1), (56, 1), (58, 1)] }, { coefficient := 2, powers := [(8, 1), (22, 1), (23, 1), (38, 1), (56, 1)] }, { coefficient := 2, powers := [(8, 1), (22, 1), (23, 1), (43, 1), (56, 1)] }, { coefficient := 2, powers := [(8, 1), (22, 1), (23, 1), (49, 1), (56, 1)] }, { coefficient := 2, powers := [(8, 1), (22, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (30, 1), (34, 1), (45, 1), (58, 1)] }, { coefficient := -1, powers := [(21, 1), (45, 1), (47, 1)] }, { coefficient := 1, powers := [(23, 1), (30, 1), (34, 1), (45, 1), (58, 1)] }, { coefficient := -1, powers := [(26, 1), (45, 1), (47, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (27, 1), (45, 1)] }],
  [{ coefficient := -1, powers := [(30, 1), (34, 1), (45, 1), (50, 1), (58, 1)] }],
  [{ coefficient := 2, powers := [(17, 1), (38, 1), (44, 1), (59, 1)] }, { coefficient := -2, powers := [(17, 1), (44, 1)] }],
  [{ coefficient := 2, powers := [(12, 1), (38, 1), (50, 1), (59, 1)] }, { coefficient := -2, powers := [(12, 1), (50, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (23, 1), (45, 1)] }, { coefficient := -2, powers := [(17, 1), (44, 1), (47, 1), (59, 1)] }],
  [{ coefficient := -2, powers := [(12, 1), (22, 1), (50, 1), (59, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (5, 1), (27, 1), (41, 1), (56, 1)] }, { coefficient := -2, powers := [(0, 1), (8, 1), (22, 1), (41, 1), (56, 1)] }, { coefficient := -2, powers := [(5, 1), (18, 1), (27, 1), (41, 1), (56, 1)] }, { coefficient := -2, powers := [(5, 1), (23, 1), (27, 1), (41, 1), (56, 1)] }, { coefficient := -2, powers := [(8, 1), (18, 1), (22, 1), (41, 1), (56, 1)] }, { coefficient := -2, powers := [(8, 1), (22, 1), (23, 1), (41, 1), (56, 1)] }],
  [{ coefficient := 2, powers := [(22, 1), (54, 1)] }],
  [{ coefficient := -2, powers := [(5, 1), (27, 1), (44, 1), (57, 1), (60, 1)] }, { coefficient := -2, powers := [(8, 1), (22, 1), (44, 1), (57, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (30, 1), (44, 1), (45, 1), (60, 1)] }],
  [{ coefficient := 2, powers := [(5, 1), (27, 1), (43, 1), (47, 1), (56, 1)] }, { coefficient := -2, powers := [(5, 1), (27, 1), (47, 1), (49, 1), (56, 1)] }, { coefficient := 2, powers := [(8, 1), (22, 1), (43, 1), (47, 1), (56, 1)] }, { coefficient := -2, powers := [(8, 1), (22, 1), (47, 1), (49, 1), (56, 1)] }],
  [{ coefficient := -2, powers := [(5, 1), (27, 1), (41, 1), (49, 1), (56, 1)] }, { coefficient := 2, powers := [(5, 1), (27, 1), (44, 1), (53, 1), (57, 1), (60, 1)] }, { coefficient := -2, powers := [(8, 1), (22, 1), (41, 1), (49, 1), (56, 1)] }, { coefficient := 2, powers := [(8, 1), (22, 1), (44, 1), (53, 1), (57, 1), (60, 1)] }, { coefficient := -1, powers := [(8, 1), (30, 1), (44, 1), (45, 1), (53, 1), (60, 1)] }],
  [{ coefficient := -2, powers := [(27, 1)] }],
  [{ coefficient := -2, powers := [(22, 1)] }],
  [{ coefficient := 2, powers := [(5, 1), (27, 1), (57, 1), (60, 1)] }, { coefficient := 2, powers := [(8, 1), (22, 1), (57, 1), (60, 1)] }, { coefficient := -1, powers := [(8, 1), (30, 1), (45, 1), (60, 1)] }],
  [{ coefficient := 2, powers := [(5, 1), (27, 1), (47, 1), (56, 1)] }, { coefficient := 2, powers := [(8, 1), (22, 1), (47, 1), (56, 1)] }],
  [{ coefficient := -2, powers := [(12, 1), (22, 1), (53, 1)] }],
  [{ coefficient := -2, powers := [(5, 1), (27, 1), (34, 1), (49, 1), (56, 1), (57, 1), (60, 1)] }, { coefficient := 2, powers := [(5, 1), (27, 1), (49, 1), (57, 1), (60, 1)] }, { coefficient := 2, powers := [(5, 1), (27, 1), (53, 1), (57, 1), (60, 1)] }, { coefficient := -2, powers := [(8, 1), (22, 1), (34, 1), (49, 1), (56, 1), (57, 1), (60, 1)] }, { coefficient := 2, powers := [(8, 1), (22, 1), (49, 1), (57, 1), (60, 1)] }, { coefficient := 2, powers := [(8, 1), (22, 1), (53, 1), (57, 1), (60, 1)] }, { coefficient := -1, powers := [(8, 1), (30, 1), (34, 1), (45, 1), (56, 1), (58, 1), (60, 1)] }, { coefficient := -2, powers := [(8, 1), (30, 1), (45, 1), (58, 1), (60, 1)] }],
  [{ coefficient := 2, powers := [(5, 1), (27, 1), (49, 1), (57, 1), (60, 1)] }],
  [{ coefficient := 2, powers := [(39, 1), (59, 1)] }],
  [{ coefficient := 2, powers := [(5, 1), (32, 1), (49, 1)] }],
  [{ coefficient := 2, powers := [(5, 1), (29, 1), (54, 1)] }],
  [{ coefficient := 2, powers := [(51, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1), (53, 1)] }, { coefficient := -1, powers := [(6, 1), (45, 1), (56, 1)] }, { coefficient := 1, powers := [(45, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (45, 1), (56, 1)] }],
  [{ coefficient := 2, powers := [(17, 1)] }],
  [{ coefficient := 1, powers := [(45, 1), (47, 1), (50, 1)] }],
  [{ coefficient := 2, powers := [(12, 1)] }],
  [{ coefficient := -2, powers := [(5, 1), (6, 1), (27, 1), (56, 1), (57, 1)] }, { coefficient := -2, powers := [(5, 1), (27, 1), (41, 1), (47, 1), (56, 1)] }, { coefficient := -2, powers := [(6, 1), (8, 1), (22, 1), (56, 1), (57, 1)] }, { coefficient := -2, powers := [(8, 1), (22, 1), (41, 1), (47, 1), (56, 1)] }, { coefficient := 1, powers := [(12, 1), (27, 1), (45, 1)] }],
  [{ coefficient := 2, powers := [(5, 1), (27, 1), (57, 1)] }, { coefficient := 2, powers := [(8, 1), (22, 1), (57, 1)] }],
  [{ coefficient := 2, powers := [(5, 1), (25, 1), (30, 1), (54, 1)] }],
  [{ coefficient := 2, powers := [(5, 1), (15, 1), (30, 1), (54, 1)] }],
  [{ coefficient := -2, powers := [(5, 1), (27, 1), (49, 1), (57, 1)] }, { coefficient := -2, powers := [(5, 1), (27, 1), (53, 1), (57, 1)] }, { coefficient := -2, powers := [(8, 1), (22, 1), (49, 1), (57, 1)] }, { coefficient := -2, powers := [(8, 1), (22, 1), (53, 1), (57, 1)] }],
  [{ coefficient := 2, powers := [(5, 1), (23, 1), (27, 1), (49, 1), (56, 1), (58, 1)] }, { coefficient := 2, powers := [(5, 1), (27, 1), (49, 1), (56, 1)] }, { coefficient := 2, powers := [(5, 1), (27, 1), (53, 1), (56, 1)] }, { coefficient := 2, powers := [(8, 1), (22, 1), (23, 1), (49, 1), (56, 1), (58, 1)] }, { coefficient := 2, powers := [(8, 1), (22, 1), (49, 1), (56, 1)] }, { coefficient := 2, powers := [(8, 1), (22, 1), (53, 1), (56, 1)] }],
  [{ coefficient := -2, powers := [(5, 1), (30, 1), (54, 1)] }],
  [{ coefficient := -2, powers := [] }],
  [{ coefficient := 2, powers := [(5, 1), (6, 1), (23, 1), (27, 1), (49, 1), (56, 1), (57, 1)] }, { coefficient := -2, powers := [(5, 1), (23, 1), (27, 1), (34, 1), (49, 1), (56, 1), (57, 1)] }, { coefficient := 2, powers := [(6, 1), (8, 1), (22, 1), (23, 1), (49, 1), (56, 1), (57, 1)] }, { coefficient := -2, powers := [(8, 1), (22, 1), (23, 1), (34, 1), (49, 1), (56, 1), (57, 1)] }, { coefficient := 1, powers := [(8, 1), (30, 1), (34, 1), (45, 1), (56, 1)] }, { coefficient := -2, powers := [(8, 1), (30, 1), (45, 1)] }],
  [{ coefficient := -2, powers := [(5, 1), (27, 1), (39, 1), (49, 1), (53, 1), (57, 1), (60, 1)] }, { coefficient := 2, powers := [(5, 1), (30, 1), (35, 1), (54, 1), (56, 1)] }, { coefficient := 2, powers := [(5, 1), (30, 1), (38, 1), (53, 1), (54, 1)] }, { coefficient := 2, powers := [(5, 1), (30, 1), (43, 1), (49, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (45, 1), (51, 1), (53, 1)] }, { coefficient := 1, powers := [(6, 1), (45, 1), (51, 1), (56, 1)] }, { coefficient := -1, powers := [(34, 1), (45, 1), (47, 1), (50, 1), (56, 1)] }, { coefficient := 2, powers := [(36, 1), (57, 1)] }, { coefficient := -2, powers := [(38, 1), (39, 1), (54, 1), (59, 1)] }, { coefficient := 2, powers := [(39, 1), (54, 1)] }, { coefficient := -1, powers := [(45, 1), (47, 1), (50, 1)] }, { coefficient := -1, powers := [(45, 1), (51, 1)] }],
  [{ coefficient := -2, powers := [(8, 1), (33, 1), (39, 1)] }, { coefficient := -2, powers := [(12, 1), (26, 1), (45, 1), (50, 1)] }, { coefficient := -2, powers := [(17, 1), (21, 1), (44, 1), (51, 1)] }, { coefficient := -2, powers := [(17, 1), (27, 1), (39, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (5, 1), (27, 1), (53, 1), (57, 1)] }, { coefficient := -2, powers := [(0, 1), (8, 1), (22, 1), (53, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (8, 1), (30, 1), (45, 1), (53, 1)] }, { coefficient := -2, powers := [(5, 1), (7, 1), (27, 1), (32, 1), (49, 1), (57, 1)] }, { coefficient := 2, powers := [(5, 1), (15, 1), (20, 1), (30, 1), (53, 1), (54, 1)] }, { coefficient := 2, powers := [(5, 1), (15, 1), (25, 1), (30, 1), (38, 1), (54, 1)] }, { coefficient := 2, powers := [(5, 1), (15, 1), (25, 1), (30, 1), (43, 1), (54, 1)] }, { coefficient := 2, powers := [(5, 1), (15, 1), (25, 1), (30, 1), (49, 1), (54, 1)] }, { coefficient := 2, powers := [(5, 1), (15, 1), (30, 1), (32, 1), (35, 1), (54, 1)] }, { coefficient := 2, powers := [(5, 1), (23, 1), (27, 1), (34, 1), (49, 1), (56, 1), (57, 1)] }, { coefficient := -2, powers := [(5, 1), (23, 1), (27, 1), (49, 1), (57, 1)] }, { coefficient := -2, powers := [(5, 1), (23, 1), (27, 1), (53, 1), (57, 1)] }, { coefficient := -2, powers := [(5, 1), (27, 1), (57, 1)] }, { coefficient := 2, powers := [(8, 1), (22, 1), (23, 1), (34, 1), (49, 1), (56, 1), (57, 1)] }, { coefficient := -2, powers := [(8, 1), (22, 1), (23, 1), (49, 1), (57, 1)] }, { coefficient := -2, powers := [(8, 1), (22, 1), (23, 1), (53, 1), (57, 1)] }, { coefficient := -2, powers := [(8, 1), (22, 1), (57, 1)] }, { coefficient := 1, powers := [(8, 1), (23, 1), (30, 1), (34, 1), (45, 1), (56, 1), (58, 1)] }, { coefficient := 2, powers := [(8, 1), (23, 1), (30, 1), (45, 1), (58, 1)] }, { coefficient := 1, powers := [(8, 1), (30, 1), (45, 1)] }]
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
    (values : Fin 61 → R) :
    ¬ ∀ index : Fin 56,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((2 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (2 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (2 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component13.SelectedLeafB4_3.selectedHasNoCommonZero

end Krenn.Component13.SelectedLeafB4_3
