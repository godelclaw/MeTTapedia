import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component13.SelectedLeafB4_6

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "748015ecc233332304d2ebcbee560b7215d34fd933e53a8194d961c52961d181"
def certificateSHA256 : String := "a9a66d795295636fd515da459d8594eaa45842afbe8f314c346277f92e097bbd"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 75 → Fin 611 := ![
  0,
  2,
  7,
  8,
  13,
  15,
  17,
  19,
  23,
  25,
  29,
  55,
  66,
  151,
  152,
  160,
  161,
  163,
  165,
  169,
  170,
  171,
  173,
  179,
  180,
  181,
  184,
  185,
  186,
  188,
  190,
  284,
  286,
  290,
  307,
  318,
  352,
  353,
  360,
  361,
  367,
  373,
  376,
  377,
  398,
  409,
  425,
  434,
  437,
  449,
  458,
  464,
  468,
  470,
  480,
  483,
  489,
  507,
  515,
  525,
  532,
  547,
  548,
  549,
  557,
  571,
  581,
  603,
  604,
  605,
  606,
  607,
  608,
  609,
  610
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 75 → SparsePoly (Fin 61) := ![
  [{ coefficient := 1, powers := [(4, 1), (33, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (30, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(15, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(15, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(30, 1), (35, 1)] }],
  [{ coefficient := 1, powers := [(33, 1), (35, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (33, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (27, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1)] }, { coefficient := 1, powers := [(23, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (50, 1)] }, { coefficient := 1, powers := [(18, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (56, 1)] }, { coefficient := 1, powers := [(16, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (57, 1)] }, { coefficient := 1, powers := [(41, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (27, 1)] }, { coefficient := 1, powers := [(27, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (23, 1)] }, { coefficient := 1, powers := [(15, 1), (18, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (23, 1)] }, { coefficient := 1, powers := [(16, 1), (18, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (43, 1)] }, { coefficient := 1, powers := [(12, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (44, 1)] }, { coefficient := 1, powers := [(16, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (18, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (41, 1)] }, { coefficient := 1, powers := [(24, 1), (38, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (47, 1)] }, { coefficient := 1, powers := [(24, 1), (43, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (51, 1)] }, { coefficient := 1, powers := [(24, 1), (43, 1), (47, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (41, 1)] }, { coefficient := 1, powers := [(26, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (49, 1)] }, { coefficient := 1, powers := [(22, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (50, 1)] }, { coefficient := 1, powers := [(27, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (38, 1)] }, { coefficient := 1, powers := [(27, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(39, 1), (41, 1)] }, { coefficient := 1, powers := [(45, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (18, 1), (53, 1)] }, { coefficient := 1, powers := [(12, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (19, 1), (53, 1)] }, { coefficient := 1, powers := [(12, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (23, 1), (43, 1)] }, { coefficient := 1, powers := [(16, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(15, 1), (21, 1), (47, 1)] }, { coefficient := 1, powers := [(15, 1), (30, 1), (34, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (25, 1), (41, 1)] }, { coefficient := 1, powers := [(17, 1), (19, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (41, 1)] }, { coefficient := 1, powers := [(18, 1), (41, 1)] }, { coefficient := 1, powers := [(23, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1)] }, { coefficient := 1, powers := [(18, 1), (47, 1)] }, { coefficient := 1, powers := [(23, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1), (45, 1)] }, { coefficient := 1, powers := [(17, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1), (54, 1)] }, { coefficient := 1, powers := [(17, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (50, 1)] }, { coefficient := 1, powers := [(24, 1), (38, 1), (50, 1)] }, { coefficient := 1, powers := [(24, 1), (43, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (39, 1), (53, 1)] }, { coefficient := 1, powers := [(39, 1)] }, { coefficient := 1, powers := [(44, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (41, 1), (49, 1)] }, { coefficient := 1, powers := [(18, 1), (41, 1), (49, 1)] }, { coefficient := 1, powers := [(41, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (41, 1), (50, 1)] }, { coefficient := 1, powers := [(18, 1), (41, 1), (50, 1)] }, { coefficient := 1, powers := [(18, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (45, 1), (49, 1)] }, { coefficient := 1, powers := [(7, 1), (29, 1), (45, 1)] }, { coefficient := 1, powers := [(11, 1), (25, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (39, 1), (53, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (53, 1)] }, { coefficient := 1, powers := [(12, 1), (22, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (27, 1), (57, 1)] }, { coefficient := 1, powers := [(4, 1), (30, 1), (54, 1)] }, { coefficient := 1, powers := [(4, 1), (33, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (22, 1), (56, 1)] }, { coefficient := 1, powers := [(22, 1)] }, { coefficient := 1, powers := [(26, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (22, 1), (56, 1)] }, { coefficient := 1, powers := [(11, 1), (22, 1), (53, 1)] }, { coefficient := 1, powers := [(15, 1), (22, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (22, 1), (54, 1)] }, { coefficient := 1, powers := [(11, 1), (27, 1), (45, 1)] }, { coefficient := 1, powers := [(11, 1), (33, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(15, 1), (22, 1), (51, 1)] }, { coefficient := 1, powers := [(15, 1), (27, 1), (39, 1)] }, { coefficient := 1, powers := [(15, 1), (30, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (23, 1), (38, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1), (43, 1)] }, { coefficient := 1, powers := [(16, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (44, 1), (49, 1)] }, { coefficient := 1, powers := [(19, 1), (44, 1), (53, 1)] }, { coefficient := 1, powers := [(25, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (41, 1), (50, 1)] }, { coefficient := 1, powers := [(20, 1), (54, 1)] }, { coefficient := 1, powers := [(24, 1), (38, 1), (41, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (45, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1)] }, { coefficient := 1, powers := [(16, 1), (26, 1), (45, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (51, 1)] }, { coefficient := 1, powers := [(8, 1), (30, 1)] }, { coefficient := 1, powers := [(12, 1), (27, 1)] }, { coefficient := 1, powers := [(16, 1), (21, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (51, 1)] }, { coefficient := 1, powers := [(27, 1), (39, 1)] }, { coefficient := 1, powers := [(27, 1), (44, 1), (47, 1)] }, { coefficient := 1, powers := [(30, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (23, 1), (56, 1)] }, { coefficient := 1, powers := [(11, 1), (23, 1), (43, 1)] }, { coefficient := 1, powers := [(15, 1), (23, 1), (38, 1)] }, { coefficient := 1, powers := [(15, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (18, 1), (56, 1)] }, { coefficient := 1, powers := [(11, 1), (18, 1), (53, 1)] }, { coefficient := 1, powers := [(11, 1)] }, { coefficient := 1, powers := [(15, 1), (18, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (41, 1), (50, 1)] }, { coefficient := 1, powers := [(22, 1), (54, 1)] }, { coefficient := 1, powers := [(27, 1), (45, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1)] }, { coefficient := 1, powers := [(6, 1), (56, 1)] }, { coefficient := 1, powers := [(23, 1), (38, 1)] }, { coefficient := 1, powers := [(23, 1), (43, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1), (49, 1)] }, { coefficient := 1, powers := [(7, 1), (19, 1), (56, 1)] }, { coefficient := 1, powers := [(7, 1), (29, 1)] }, { coefficient := 1, powers := [(11, 1), (19, 1), (53, 1)] }, { coefficient := 1, powers := [(11, 1), (25, 1)] }, { coefficient := 1, powers := [(15, 1), (19, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (56, 1)] }, { coefficient := 1, powers := [(7, 1), (56, 1)] }, { coefficient := 1, powers := [(11, 1), (43, 1)] }, { coefficient := 1, powers := [(11, 1), (53, 1)] }, { coefficient := 1, powers := [(15, 1), (38, 1)] }, { coefficient := 1, powers := [(15, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (49, 1)] }, { coefficient := 1, powers := [(20, 1), (53, 1)] }, { coefficient := 1, powers := [(25, 1), (38, 1)] }, { coefficient := 1, powers := [(25, 1), (43, 1)] }, { coefficient := 1, powers := [(29, 1), (35, 1)] }, { coefficient := 1, powers := [(32, 1), (35, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (34, 1), (56, 1)] }, { coefficient := 1, powers := [(1, 1)] }, { coefficient := 1, powers := [(11, 1), (24, 1)] }, { coefficient := 1, powers := [(11, 1), (32, 1), (34, 1)] }, { coefficient := 1, powers := [(15, 1), (19, 1)] }, { coefficient := 1, powers := [(15, 1), (29, 1), (34, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (25, 1), (56, 1)] }, { coefficient := 1, powers := [(3, 1), (29, 1), (53, 1)] }, { coefficient := 1, powers := [(3, 1), (32, 1), (49, 1)] }, { coefficient := 1, powers := [(19, 1), (49, 1)] }, { coefficient := 1, powers := [(19, 1), (53, 1)] }, { coefficient := 1, powers := [(25, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (25, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (53, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (49, 1)] }, { coefficient := 1, powers := [(16, 1), (19, 1), (44, 1), (49, 1)] }, { coefficient := 1, powers := [(16, 1), (19, 1), (44, 1), (53, 1)] }, { coefficient := 1, powers := [(16, 1), (25, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (35, 1), (56, 1)] }, { coefficient := 1, powers := [(1, 1), (38, 1), (53, 1)] }, { coefficient := 1, powers := [(1, 1), (43, 1), (49, 1)] }, { coefficient := 1, powers := [(4, 1), (25, 1), (56, 1)] }, { coefficient := 1, powers := [(4, 1), (29, 1), (53, 1)] }, { coefficient := 1, powers := [(4, 1), (32, 1), (49, 1)] }, { coefficient := 1, powers := [(7, 1), (20, 1), (56, 1)] }, { coefficient := 1, powers := [(7, 1), (29, 1), (43, 1)] }, { coefficient := 1, powers := [(7, 1), (32, 1), (38, 1)] }, { coefficient := 1, powers := [(11, 1), (20, 1), (53, 1)] }, { coefficient := 1, powers := [(11, 1), (25, 1), (43, 1)] }, { coefficient := 1, powers := [(11, 1), (32, 1), (35, 1)] }, { coefficient := 1, powers := [(15, 1), (20, 1), (49, 1)] }, { coefficient := 1, powers := [(15, 1), (25, 1), (38, 1)] }, { coefficient := 1, powers := [(15, 1), (29, 1), (35, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (36, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (39, 1), (54, 1)] }, { coefficient := 1, powers := [(2, 1), (45, 1), (51, 1)] }, { coefficient := 1, powers := [(5, 1), (27, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (51, 1)] }, { coefficient := 1, powers := [(8, 1), (22, 1), (57, 1)] }, { coefficient := 1, powers := [(8, 1), (30, 1), (45, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (39, 1)] }, { coefficient := 1, powers := [(12, 1), (22, 1), (54, 1)] }, { coefficient := 1, powers := [(12, 1), (27, 1), (45, 1)] }, { coefficient := 1, powers := [(12, 1), (33, 1), (36, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (51, 1)] }, { coefficient := 1, powers := [(17, 1), (27, 1), (39, 1)] }, { coefficient := 1, powers := [(17, 1), (30, 1), (36, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (58, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1)] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(37, 1), (59, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(38, 1), (60, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(39, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 75 → SparsePoly (Fin 61) := ![
  [{ coefficient := 1, powers := [(5, 1), (29, 1), (51, 1), (53, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (49, 1), (51, 1)] }, { coefficient := 1, powers := [(12, 1), (29, 1), (36, 1), (53, 1)] }, { coefficient := 1, powers := [(12, 1), (32, 1), (36, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (20, 1), (54, 1), (56, 1)] }, { coefficient := -1, powers := [(5, 1), (25, 1), (54, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (43, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (38, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (20, 1), (45, 1), (56, 1)] }, { coefficient := -1, powers := [(8, 1), (25, 1), (45, 1), (56, 1)] }, { coefficient := 1, powers := [(8, 1), (29, 1), (43, 1), (45, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (38, 1), (45, 1)] }, { coefficient := 2, powers := [(17, 1), (20, 1), (36, 1), (56, 1)] }, { coefficient := -2, powers := [(17, 1), (25, 1), (36, 1), (56, 1)] }, { coefficient := 2, powers := [(17, 1), (29, 1), (36, 1), (43, 1)] }, { coefficient := 2, powers := [(17, 1), (32, 1), (36, 1), (38, 1)] }],
  [{ coefficient := 2, powers := [(12, 1), (20, 1), (27, 1), (49, 1)] }, { coefficient := 2, powers := [(12, 1), (25, 1), (27, 1), (38, 1)] }, { coefficient := 2, powers := [(12, 1), (25, 1), (27, 1), (43, 1)] }, { coefficient := 2, powers := [(12, 1), (25, 1), (27, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (20, 1), (30, 1), (49, 1)] }, { coefficient := -1, powers := [(5, 1), (24, 1), (30, 1), (49, 2)] }, { coefficient := -1, powers := [(5, 1), (25, 1), (30, 1), (38, 1)] }, { coefficient := -1, powers := [(5, 1), (25, 1), (30, 1), (43, 1)] }, { coefficient := -1, powers := [(5, 1), (25, 1), (30, 1), (53, 1)] }, { coefficient := -1, powers := [(5, 1), (30, 1), (32, 1), (34, 1), (49, 2)] }, { coefficient := 1, powers := [(12, 1), (20, 1), (22, 1), (49, 1)] }, { coefficient := 1, powers := [(12, 1), (22, 1), (25, 1), (38, 1)] }, { coefficient := 1, powers := [(12, 1), (22, 1), (25, 1), (43, 1)] }, { coefficient := 1, powers := [(12, 1), (22, 1), (25, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (21, 1), (29, 1), (49, 2), (54, 1)] }],
  [{ coefficient := -2, powers := [(17, 1), (19, 1), (22, 1), (49, 2)] }],
  [{ coefficient := 1, powers := [(4, 1), (26, 1), (29, 1), (51, 1), (53, 1)] }, { coefficient := 1, powers := [(4, 1), (26, 1), (32, 1), (49, 1), (51, 1)] }, { coefficient := -1, powers := [(7, 1), (20, 1), (26, 1), (51, 1), (56, 1)] }, { coefficient := 1, powers := [(7, 1), (25, 1), (26, 1), (51, 1), (56, 1)] }, { coefficient := -1, powers := [(7, 1), (26, 1), (29, 1), (43, 1), (51, 1)] }, { coefficient := -1, powers := [(7, 1), (26, 1), (32, 1), (38, 1), (51, 1)] }, { coefficient := 1, powers := [(11, 1), (20, 1), (26, 1), (49, 1), (51, 1)] }, { coefficient := 1, powers := [(11, 1), (25, 1), (26, 1), (38, 1), (51, 1)] }, { coefficient := 1, powers := [(11, 1), (25, 1), (26, 1), (43, 1), (51, 1)] }, { coefficient := 1, powers := [(11, 1), (25, 1), (26, 1), (51, 1), (53, 1)] }, { coefficient := -1, powers := [(15, 1), (20, 1), (26, 1), (49, 1), (51, 1)] }, { coefficient := 1, powers := [(15, 1), (25, 1), (26, 1), (49, 1), (51, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (21, 1), (29, 1), (45, 1), (53, 1)] }, { coefficient := -1, powers := [(4, 1), (21, 1), (32, 1), (45, 1), (49, 1)] }, { coefficient := 1, powers := [(11, 1), (20, 1), (21, 1), (45, 1), (49, 1)] }, { coefficient := 1, powers := [(11, 1), (21, 1), (25, 1), (38, 1), (45, 1)] }, { coefficient := 1, powers := [(11, 1), (21, 1), (25, 1), (43, 1), (45, 1)] }, { coefficient := 1, powers := [(11, 1), (21, 1), (25, 1), (45, 1), (53, 1)] }, { coefficient := -1, powers := [(15, 1), (20, 1), (21, 1), (45, 1), (49, 1)] }, { coefficient := 1, powers := [(15, 1), (21, 1), (25, 1), (45, 1), (49, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (11, 1), (29, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (15, 1), (29, 1), (54, 1)] }, { coefficient := -1, powers := [(8, 1), (11, 1), (29, 1), (45, 1)] }, { coefficient := 1, powers := [(8, 1), (15, 1), (29, 1), (45, 1)] }, { coefficient := -1, powers := [(11, 1), (17, 1), (29, 1), (36, 1)] }, { coefficient := 1, powers := [(15, 1), (17, 1), (29, 1), (36, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (11, 1), (29, 1), (51, 1)] }, { coefficient := 1, powers := [(5, 1), (15, 1), (29, 1), (51, 1)] }, { coefficient := -1, powers := [(11, 1), (12, 1), (29, 1), (36, 1)] }, { coefficient := 1, powers := [(12, 1), (15, 1), (29, 1), (36, 1)] }],
  [{ coefficient := -2, powers := [(15, 1), (17, 1), (25, 1), (26, 1), (49, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (20, 1), (36, 1), (56, 1), (59, 1)] }, { coefficient := -1, powers := [(12, 1), (25, 1), (36, 1), (56, 1), (59, 1)] }, { coefficient := 1, powers := [(12, 1), (29, 1), (36, 1), (43, 1), (59, 1)] }, { coefficient := 1, powers := [(12, 1), (32, 1), (36, 1), (38, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (15, 1), (19, 1), (45, 1), (49, 2), (59, 1), (60, 1)] }, { coefficient := -1, powers := [(12, 1), (15, 1), (20, 1), (45, 1), (49, 1), (59, 1), (60, 1)] }, { coefficient := 1, powers := [(12, 1), (15, 1), (25, 1), (45, 1), (49, 1), (59, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (15, 1), (19, 1), (27, 1), (43, 1), (49, 2)] }, { coefficient := 1, powers := [(12, 1), (15, 1), (20, 1), (27, 1), (43, 1), (49, 1)] }, { coefficient := -1, powers := [(12, 1), (15, 1), (25, 1), (27, 1), (43, 1), (49, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (15, 1), (19, 1), (22, 1), (41, 1), (49, 3)] }, { coefficient := 1, powers := [(12, 1), (15, 1), (20, 1), (22, 1), (41, 1), (49, 2)] }, { coefficient := -1, powers := [(12, 1), (15, 1), (22, 1), (25, 1), (41, 1), (43, 1), (49, 1)] }, { coefficient := -1, powers := [(12, 1), (15, 1), (22, 1), (25, 1), (41, 1), (49, 2)] }],
  [{ coefficient := 1, powers := [(6, 1), (15, 1), (19, 1), (27, 1), (49, 2), (57, 1)] }, { coefficient := -1, powers := [(6, 1), (15, 1), (20, 1), (27, 1), (49, 1), (57, 1)] }, { coefficient := 1, powers := [(6, 1), (15, 1), (25, 1), (27, 1), (49, 1), (57, 1)] }],
  [{ coefficient := 2, powers := [(8, 1), (15, 1), (22, 1), (25, 1), (49, 1), (56, 1)] }, { coefficient := -1, powers := [(15, 1), (16, 1), (19, 1), (27, 1), (44, 1), (49, 2)] }, { coefficient := 1, powers := [(15, 1), (16, 1), (20, 1), (27, 1), (44, 1), (49, 1)] }, { coefficient := -1, powers := [(15, 1), (16, 1), (25, 1), (27, 1), (44, 1), (49, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (15, 1), (19, 1), (43, 1), (45, 1), (49, 2), (59, 1), (60, 1)] }, { coefficient := 1, powers := [(12, 1), (15, 1), (20, 1), (43, 1), (45, 1), (49, 1), (59, 1), (60, 1)] }, { coefficient := -1, powers := [(12, 1), (15, 1), (25, 1), (43, 1), (45, 1), (49, 1), (59, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (19, 1), (33, 1), (36, 1), (43, 1), (49, 2)] }],
  [{ coefficient := -1, powers := [(15, 1), (19, 1), (27, 1), (38, 1), (45, 1), (49, 2)] }, { coefficient := -1, powers := [(15, 1), (19, 1), (27, 1), (43, 1), (45, 1), (49, 2)] }, { coefficient := 1, powers := [(15, 1), (20, 1), (27, 1), (38, 1), (45, 1), (49, 1)] }, { coefficient := 1, powers := [(15, 1), (20, 1), (27, 1), (43, 1), (45, 1), (49, 1)] }, { coefficient := -1, powers := [(15, 1), (25, 1), (27, 1), (38, 1), (45, 1), (49, 1)] }, { coefficient := -1, powers := [(15, 1), (25, 1), (27, 1), (43, 1), (45, 1), (49, 1)] }],
  [{ coefficient := -1, powers := [(15, 1), (18, 1), (19, 1), (33, 1), (36, 1), (49, 2)] }, { coefficient := -1, powers := [(15, 1), (18, 1), (22, 1), (25, 1), (49, 1), (54, 1)] }],
  [{ coefficient := -2, powers := [(15, 1), (25, 1), (26, 1), (49, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(11, 1), (19, 1), (33, 1), (36, 1), (47, 1), (49, 2), (58, 1)] }, { coefficient := 1, powers := [(15, 1), (19, 1), (27, 1), (38, 1), (45, 1), (47, 1), (49, 2)] }, { coefficient := 1, powers := [(15, 1), (19, 1), (27, 1), (43, 1), (45, 1), (47, 1), (49, 2)] }, { coefficient := -1, powers := [(15, 1), (20, 1), (27, 1), (38, 1), (45, 1), (47, 1), (49, 1)] }, { coefficient := -1, powers := [(15, 1), (20, 1), (27, 1), (43, 1), (45, 1), (47, 1), (49, 1)] }, { coefficient := 2, powers := [(15, 1), (22, 1), (25, 1), (41, 1), (49, 1), (51, 1), (58, 1)] }, { coefficient := 1, powers := [(15, 1), (25, 1), (27, 1), (38, 1), (45, 1), (47, 1), (49, 1)] }, { coefficient := 1, powers := [(15, 1), (25, 1), (27, 1), (43, 1), (45, 1), (47, 1), (49, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (15, 1), (30, 1), (49, 1), (50, 1)] }, { coefficient := 1, powers := [(12, 1), (15, 1), (22, 1), (49, 1), (50, 1)] }],
  [{ coefficient := 2, powers := [(15, 1), (17, 1), (22, 1), (49, 1), (50, 1)] }],
  [{ coefficient := -2, powers := [(15, 1), (17, 1), (22, 1), (49, 1)] }],
  [{ coefficient := -2, powers := [(8, 1), (15, 1), (25, 1), (47, 1), (49, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (15, 1), (19, 1), (49, 1), (54, 1)] }],
  [{ coefficient := 2, powers := [(15, 1), (17, 1), (24, 1), (38, 1), (47, 1), (49, 1)] }, { coefficient := 2, powers := [(15, 1), (17, 1), (24, 1), (43, 1), (47, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (15, 1), (19, 1), (45, 1), (49, 2), (60, 1)] }, { coefficient := -1, powers := [(12, 1), (15, 1), (20, 1), (45, 1), (49, 1), (60, 1)] }, { coefficient := 1, powers := [(12, 1), (15, 1), (25, 1), (45, 1), (49, 1), (60, 1)] }, { coefficient := -2, powers := [(15, 1), (17, 1), (24, 1), (44, 1), (47, 1), (49, 1)] }],
  [{ coefficient := 2, powers := [(8, 1), (15, 1), (25, 1), (26, 1), (49, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(15, 1), (19, 1), (33, 1), (36, 1), (49, 2)] }, { coefficient := 1, powers := [(15, 1), (22, 1), (25, 1), (49, 1), (54, 1)] }],
  [{ coefficient := -2, powers := [(15, 1), (22, 1), (49, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(11, 1), (19, 1), (33, 1), (36, 1), (49, 2)] }, { coefficient := 1, powers := [(15, 1), (19, 1), (27, 1), (45, 1), (49, 2)] }, { coefficient := -1, powers := [(15, 1), (20, 1), (27, 1), (45, 1), (49, 1)] }, { coefficient := 1, powers := [(15, 1), (25, 1), (27, 1), (45, 1), (49, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (29, 1), (49, 2), (54, 1)] }],
  [{ coefficient := 2, powers := [(15, 1), (22, 1), (49, 1), (51, 1)] }],
  [{ coefficient := -2, powers := [(15, 1), (16, 1), (22, 1), (25, 1), (49, 1), (51, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (16, 1), (19, 1), (33, 1), (36, 1), (49, 2), (58, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (15, 1), (19, 1), (27, 1), (49, 2), (56, 1)] }, { coefficient := 1, powers := [(6, 1), (15, 1), (20, 1), (27, 1), (49, 1), (56, 1)] }, { coefficient := -1, powers := [(6, 1), (15, 1), (25, 1), (27, 1), (49, 1), (56, 1)] }, { coefficient := 1, powers := [(7, 1), (20, 1), (27, 1), (56, 1)] }, { coefficient := -1, powers := [(7, 1), (25, 1), (27, 1), (56, 1)] }, { coefficient := 1, powers := [(7, 1), (27, 1), (29, 1), (43, 1)] }, { coefficient := 1, powers := [(7, 1), (27, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [(11, 1), (20, 1), (27, 1), (49, 1)] }, { coefficient := -1, powers := [(11, 1), (25, 1), (27, 1), (38, 1)] }, { coefficient := -1, powers := [(11, 1), (25, 1), (27, 1), (43, 1)] }, { coefficient := -1, powers := [(11, 1), (25, 1), (27, 1), (53, 1)] }, { coefficient := -1, powers := [(11, 1), (27, 1), (29, 1), (35, 1)] }, { coefficient := 1, powers := [(15, 1), (20, 1), (27, 1), (49, 1)] }, { coefficient := -1, powers := [(15, 1), (25, 1), (27, 1), (49, 1)] }, { coefficient := 1, powers := [(15, 1), (27, 1), (29, 1), (35, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (22, 1), (29, 1), (53, 1)] }, { coefficient := 1, powers := [(4, 1), (22, 1), (32, 1), (49, 1)] }, { coefficient := 1, powers := [(7, 1), (20, 1), (22, 1), (56, 1)] }, { coefficient := -1, powers := [(7, 1), (22, 1), (25, 1), (56, 1)] }, { coefficient := 1, powers := [(7, 1), (22, 1), (29, 1), (43, 1)] }, { coefficient := 1, powers := [(7, 1), (22, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [(11, 1), (20, 1), (22, 1), (49, 1)] }, { coefficient := -1, powers := [(11, 1), (22, 1), (25, 1), (38, 1)] }, { coefficient := -1, powers := [(11, 1), (22, 1), (25, 1), (43, 1)] }, { coefficient := -1, powers := [(11, 1), (22, 1), (25, 1), (53, 1)] }, { coefficient := -1, powers := [(11, 1), (22, 1), (29, 1), (35, 1)] }, { coefficient := 1, powers := [(15, 1), (20, 1), (22, 1), (49, 1)] }, { coefficient := 1, powers := [(15, 1), (22, 1), (25, 1), (49, 1)] }, { coefficient := 1, powers := [(15, 1), (22, 1), (29, 1), (35, 1)] }, { coefficient := 2, powers := [(15, 1), (25, 1), (26, 1), (44, 1), (49, 1)] }],
  [{ coefficient := -2, powers := [(15, 1), (17, 1), (22, 1), (47, 1), (49, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (17, 1), (27, 1), (29, 1), (53, 1)] }, { coefficient := -1, powers := [(4, 1), (17, 1), (27, 1), (32, 1), (49, 1)] }, { coefficient := 1, powers := [(7, 1), (17, 1), (20, 1), (27, 1), (56, 1)] }, { coefficient := -1, powers := [(7, 1), (17, 1), (25, 1), (27, 1), (56, 1)] }, { coefficient := 1, powers := [(7, 1), (17, 1), (27, 1), (29, 1), (43, 1)] }, { coefficient := 1, powers := [(7, 1), (17, 1), (27, 1), (32, 1), (38, 1)] }, { coefficient := 1, powers := [(11, 1), (17, 1), (20, 1), (27, 1), (49, 1)] }, { coefficient := 1, powers := [(11, 1), (17, 1), (25, 1), (27, 1), (38, 1)] }, { coefficient := 1, powers := [(11, 1), (17, 1), (25, 1), (27, 1), (43, 1)] }, { coefficient := 1, powers := [(11, 1), (17, 1), (25, 1), (27, 1), (53, 1)] }, { coefficient := 1, powers := [(15, 1), (16, 1), (19, 1), (27, 1), (41, 1), (49, 2)] }, { coefficient := -1, powers := [(15, 1), (16, 1), (20, 1), (27, 1), (41, 1), (49, 1)] }, { coefficient := 1, powers := [(15, 1), (16, 1), (25, 1), (27, 1), (41, 1), (49, 1)] }, { coefficient := 1, powers := [(15, 1), (17, 1), (19, 1), (27, 1), (49, 2)] }, { coefficient := -1, powers := [(15, 1), (17, 1), (20, 1), (27, 1), (49, 1)] }, { coefficient := 1, powers := [(15, 1), (17, 1), (25, 1), (27, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (15, 1), (19, 1), (22, 1), (49, 2), (50, 1)] }, { coefficient := -1, powers := [(12, 1), (15, 1), (20, 1), (22, 1), (49, 1), (50, 1)] }, { coefficient := 1, powers := [(12, 1), (15, 1), (22, 1), (25, 1), (49, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (15, 1), (22, 1), (25, 1), (43, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (23, 1), (27, 1), (49, 2)] }],
  [{ coefficient := 1, powers := [(15, 1), (19, 1), (49, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (29, 1), (53, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (49, 1)] }],
  [{ coefficient := -2, powers := [(8, 1), (15, 1), (25, 1), (49, 1), (57, 1)] }],
  [{ coefficient := -2, powers := [(17, 1), (18, 1), (20, 1), (49, 1), (51, 1)] }, { coefficient := -2, powers := [(17, 1), (18, 1), (25, 1), (38, 1), (51, 1)] }, { coefficient := -2, powers := [(17, 1), (18, 1), (25, 1), (43, 1), (51, 1)] }, { coefficient := -2, powers := [(17, 1), (18, 1), (25, 1), (51, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (20, 1), (49, 1)] }, { coefficient := -1, powers := [(12, 1), (25, 1), (38, 1)] }, { coefficient := -1, powers := [(12, 1), (25, 1), (43, 1)] }, { coefficient := -1, powers := [(12, 1), (25, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (19, 1), (49, 2)] }],
  [{ coefficient := -1, powers := [(15, 1), (19, 1), (27, 1), (45, 1), (47, 1), (49, 2)] }, { coefficient := 1, powers := [(15, 1), (20, 1), (27, 1), (45, 1), (47, 1), (49, 1)] }, { coefficient := -1, powers := [(15, 1), (25, 1), (27, 1), (45, 1), (47, 1), (49, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (15, 1), (16, 1), (30, 1), (49, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (15, 1), (30, 1), (49, 1)] }, { coefficient := -1, powers := [(12, 1), (15, 1), (22, 1), (49, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (29, 1), (51, 1), (53, 1)] }, { coefficient := -1, powers := [(4, 1), (32, 1), (49, 1), (51, 1)] }, { coefficient := 1, powers := [(7, 1), (20, 1), (51, 1), (56, 1)] }, { coefficient := -1, powers := [(7, 1), (25, 1), (51, 1), (56, 1)] }, { coefficient := 1, powers := [(7, 1), (29, 1), (43, 1), (51, 1)] }, { coefficient := 1, powers := [(7, 1), (32, 1), (38, 1), (51, 1)] }, { coefficient := -1, powers := [(11, 1), (20, 1), (49, 1), (51, 1)] }, { coefficient := -1, powers := [(11, 1), (25, 1), (38, 1), (51, 1)] }, { coefficient := -1, powers := [(11, 1), (25, 1), (43, 1), (51, 1)] }, { coefficient := -1, powers := [(11, 1), (25, 1), (51, 1), (53, 1)] }, { coefficient := 1, powers := [(15, 1), (20, 1), (49, 1), (51, 1)] }, { coefficient := -1, powers := [(15, 1), (25, 1), (49, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (29, 1), (45, 1), (53, 1)] }, { coefficient := 1, powers := [(4, 1), (32, 1), (45, 1), (49, 1)] }, { coefficient := -1, powers := [(11, 1), (20, 1), (45, 1), (49, 1)] }, { coefficient := -1, powers := [(11, 1), (25, 1), (38, 1), (45, 1)] }, { coefficient := -1, powers := [(11, 1), (25, 1), (43, 1), (45, 1)] }, { coefficient := -1, powers := [(11, 1), (25, 1), (45, 1), (53, 1)] }, { coefficient := 1, powers := [(15, 1), (20, 1), (45, 1), (49, 1)] }, { coefficient := -1, powers := [(15, 1), (25, 1), (45, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (17, 1), (29, 1), (53, 1)] }, { coefficient := 1, powers := [(4, 1), (17, 1), (32, 1), (49, 1)] }, { coefficient := -1, powers := [(7, 1), (17, 1), (20, 1), (56, 1)] }, { coefficient := 1, powers := [(7, 1), (17, 1), (25, 1), (56, 1)] }, { coefficient := -1, powers := [(7, 1), (17, 1), (29, 1), (43, 1)] }, { coefficient := -1, powers := [(7, 1), (17, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [(11, 1), (17, 1), (20, 1), (49, 1)] }, { coefficient := -1, powers := [(11, 1), (17, 1), (25, 1), (38, 1)] }, { coefficient := -1, powers := [(11, 1), (17, 1), (25, 1), (43, 1)] }, { coefficient := -1, powers := [(11, 1), (17, 1), (25, 1), (53, 1)] }, { coefficient := -1, powers := [(15, 1), (17, 1), (19, 1), (49, 2)] }, { coefficient := 1, powers := [(15, 1), (17, 1), (20, 1), (49, 1)] }, { coefficient := -1, powers := [(15, 1), (17, 1), (25, 1), (49, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (19, 1), (27, 1), (45, 1), (49, 2)] }],
  [{ coefficient := 2, powers := [(17, 1), (20, 1), (22, 1), (49, 1), (51, 1)] }, { coefficient := 2, powers := [(17, 1), (22, 1), (25, 1), (38, 1), (51, 1)] }, { coefficient := 2, powers := [(17, 1), (22, 1), (25, 1), (43, 1), (51, 1)] }, { coefficient := 2, powers := [(17, 1), (22, 1), (25, 1), (51, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (15, 1), (19, 1), (49, 2)] }, { coefficient := 1, powers := [(12, 1), (15, 1), (20, 1), (49, 1)] }, { coefficient := -1, powers := [(12, 1), (15, 1), (25, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (15, 1), (19, 1), (27, 1), (45, 1), (49, 2)] }, { coefficient := -1, powers := [(12, 1), (15, 1), (20, 1), (27, 1), (45, 1), (49, 1)] }, { coefficient := 1, powers := [(12, 1), (15, 1), (25, 1), (27, 1), (45, 1), (49, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (23, 1), (27, 1), (45, 1), (49, 2)] }],
  [{ coefficient := 1, powers := [(12, 1), (19, 1), (23, 1), (27, 1), (45, 1), (49, 2)] }, { coefficient := 1, powers := [(25, 1)] }],
  [{ coefficient := 1, powers := [(11, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (30, 1), (49, 2), (54, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (15, 1), (30, 1), (49, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (15, 1), (30, 1), (49, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(4, 1), (29, 1), (53, 1)] }, { coefficient := -1, powers := [(4, 1), (32, 1), (49, 1)] }, { coefficient := -1, powers := [(7, 1), (20, 1), (56, 1)] }, { coefficient := 1, powers := [(7, 1), (25, 1), (56, 1)] }, { coefficient := -1, powers := [(7, 1), (29, 1), (43, 1)] }, { coefficient := -1, powers := [(7, 1), (32, 1), (38, 1)] }, { coefficient := 1, powers := [(11, 1), (20, 1), (49, 1)] }, { coefficient := 1, powers := [(11, 1), (25, 1), (38, 1)] }, { coefficient := 1, powers := [(11, 1), (25, 1), (43, 1)] }, { coefficient := 1, powers := [(11, 1), (25, 1), (53, 1)] }, { coefficient := 1, powers := [(11, 1), (29, 1), (35, 1)] }, { coefficient := -1, powers := [(15, 1), (20, 1), (49, 1)] }, { coefficient := 1, powers := [(15, 1), (25, 1), (49, 1)] }, { coefficient := -1, powers := [(15, 1), (29, 1), (35, 1)] }],
  [{ coefficient := -1, powers := [(11, 1), (16, 1), (19, 1), (33, 1), (36, 1), (47, 1), (49, 2)] }, { coefficient := 2, powers := [(15, 1), (16, 1), (22, 1), (25, 1), (41, 1), (49, 1), (51, 1)] }, { coefficient := 2, powers := [(15, 1), (17, 1), (25, 1), (26, 1), (44, 1), (49, 1), (51, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (30, 1), (34, 1), (49, 2), (54, 1), (56, 1)] }, { coefficient := -1, powers := [(5, 1), (30, 1), (49, 2), (54, 1)] }, { coefficient := 1, powers := [(35, 1), (56, 1)] }, { coefficient := 1, powers := [(38, 1), (53, 1)] }, { coefficient := 1, powers := [(43, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (29, 1), (36, 1), (53, 1), (57, 1)] }, { coefficient := 1, powers := [(4, 1), (29, 1), (45, 1), (51, 1), (53, 1)] }, { coefficient := 1, powers := [(4, 1), (32, 1), (36, 1), (49, 1), (57, 1)] }, { coefficient := 1, powers := [(4, 1), (32, 1), (45, 1), (49, 1), (51, 1)] }, { coefficient := 1, powers := [(7, 1), (20, 1), (36, 1), (56, 1), (57, 1)] }, { coefficient := -1, powers := [(7, 1), (25, 1), (36, 1), (56, 1), (57, 1)] }, { coefficient := 1, powers := [(7, 1), (29, 1), (36, 1), (43, 1), (57, 1)] }, { coefficient := 1, powers := [(7, 1), (32, 1), (36, 1), (38, 1), (57, 1)] }, { coefficient := -1, powers := [(11, 1), (20, 1), (36, 1), (49, 1), (57, 1)] }, { coefficient := 1, powers := [(11, 1), (20, 1), (45, 1), (49, 1), (51, 1)] }, { coefficient := -1, powers := [(11, 1), (25, 1), (36, 1), (38, 1), (57, 1)] }, { coefficient := -1, powers := [(11, 1), (25, 1), (36, 1), (43, 1), (57, 1)] }, { coefficient := -1, powers := [(11, 1), (25, 1), (36, 1), (53, 1), (57, 1)] }, { coefficient := 1, powers := [(11, 1), (25, 1), (38, 1), (45, 1), (51, 1)] }, { coefficient := 1, powers := [(11, 1), (25, 1), (43, 1), (45, 1), (51, 1)] }, { coefficient := 1, powers := [(11, 1), (25, 1), (45, 1), (51, 1), (53, 1)] }, { coefficient := -1, powers := [(11, 1), (29, 1), (35, 1), (36, 1), (57, 1)] }, { coefficient := -1, powers := [(11, 1), (29, 1), (35, 1), (45, 1), (51, 1)] }, { coefficient := 1, powers := [(15, 1), (20, 1), (36, 1), (49, 1), (57, 1)] }, { coefficient := -1, powers := [(15, 1), (20, 1), (45, 1), (49, 1), (51, 1)] }, { coefficient := -1, powers := [(15, 1), (25, 1), (36, 1), (49, 1), (57, 1)] }, { coefficient := 1, powers := [(15, 1), (25, 1), (45, 1), (49, 1), (51, 1)] }, { coefficient := 1, powers := [(15, 1), (29, 1), (35, 1), (36, 1), (57, 1)] }, { coefficient := 1, powers := [(15, 1), (29, 1), (35, 1), (45, 1), (51, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (12, 1), (20, 1), (33, 1), (36, 1), (56, 1)] }, { coefficient := 1, powers := [(7, 1), (12, 1), (25, 1), (33, 1), (36, 1), (56, 1)] }, { coefficient := -1, powers := [(7, 1), (12, 1), (29, 1), (33, 1), (36, 1), (43, 1)] }, { coefficient := -1, powers := [(7, 1), (12, 1), (32, 1), (33, 1), (36, 1), (38, 1)] }, { coefficient := 1, powers := [(12, 1), (15, 1), (19, 1), (27, 1), (43, 1), (45, 1), (49, 2), (60, 1)] }, { coefficient := -1, powers := [(12, 1), (15, 1), (20, 1), (27, 1), (43, 1), (45, 1), (49, 1), (60, 1)] }, { coefficient := 1, powers := [(12, 1), (15, 1), (25, 1), (27, 1), (43, 1), (45, 1), (49, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (15, 1), (19, 1), (27, 1), (45, 1), (49, 2)] }, { coefficient := 1, powers := [(12, 1), (15, 1), (20, 1), (27, 1), (45, 1), (49, 1)] }, { coefficient := -1, powers := [(12, 1), (15, 1), (25, 1), (27, 1), (45, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (4, 1), (17, 1), (27, 1), (29, 1), (53, 2)] }, { coefficient := 1, powers := [(0, 1), (4, 1), (17, 1), (27, 1), (32, 1), (49, 1), (53, 1)] }, { coefficient := -1, powers := [(0, 1), (7, 1), (17, 1), (20, 1), (27, 1), (53, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (7, 1), (17, 1), (25, 1), (27, 1), (53, 1), (56, 1)] }, { coefficient := -1, powers := [(0, 1), (7, 1), (17, 1), (27, 1), (29, 1), (43, 1), (53, 1)] }, { coefficient := -1, powers := [(0, 1), (7, 1), (17, 1), (27, 1), (32, 1), (38, 1), (53, 1)] }, { coefficient := -1, powers := [(0, 1), (11, 1), (17, 1), (20, 1), (27, 1), (49, 1), (53, 1)] }, { coefficient := -1, powers := [(0, 1), (11, 1), (17, 1), (25, 1), (27, 1), (38, 1), (53, 1)] }, { coefficient := -1, powers := [(0, 1), (11, 1), (17, 1), (25, 1), (27, 1), (43, 1), (53, 1)] }, { coefficient := -1, powers := [(0, 1), (11, 1), (17, 1), (25, 1), (27, 1), (53, 2)] }, { coefficient := -1, powers := [(0, 1), (15, 1), (16, 1), (19, 1), (27, 1), (41, 1), (49, 2), (53, 1)] }, { coefficient := 1, powers := [(0, 1), (15, 1), (16, 1), (20, 1), (27, 1), (41, 1), (49, 1), (53, 1)] }, { coefficient := -1, powers := [(0, 1), (15, 1), (16, 1), (25, 1), (27, 1), (41, 1), (49, 1), (53, 1)] }, { coefficient := -1, powers := [(0, 1), (15, 1), (17, 1), (19, 1), (27, 1), (49, 2), (53, 1)] }, { coefficient := 1, powers := [(0, 1), (15, 1), (17, 1), (20, 1), (27, 1), (49, 1), (53, 1)] }, { coefficient := -1, powers := [(0, 1), (15, 1), (17, 1), (25, 1), (27, 1), (49, 1), (53, 1)] }, { coefficient := 1, powers := [(2, 1), (4, 1), (29, 1), (53, 1), (54, 1)] }, { coefficient := 1, powers := [(2, 1), (4, 1), (32, 1), (49, 1), (54, 1)] }, { coefficient := 1, powers := [(2, 1), (7, 1), (20, 1), (54, 1), (56, 1)] }, { coefficient := -1, powers := [(2, 1), (7, 1), (25, 1), (54, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (7, 1), (29, 1), (43, 1), (54, 1)] }, { coefficient := 1, powers := [(2, 1), (7, 1), (32, 1), (38, 1), (54, 1)] }, { coefficient := -1, powers := [(2, 1), (11, 1), (20, 1), (49, 1), (54, 1)] }, { coefficient := -1, powers := [(2, 1), (11, 1), (25, 1), (38, 1), (54, 1)] }, { coefficient := -1, powers := [(2, 1), (11, 1), (25, 1), (43, 1), (54, 1)] }, { coefficient := -1, powers := [(2, 1), (11, 1), (25, 1), (53, 1), (54, 1)] }, { coefficient := -1, powers := [(2, 1), (11, 1), (29, 1), (35, 1), (54, 1)] }, { coefficient := -1, powers := [(2, 1), (15, 1), (19, 1), (49, 1), (53, 1), (54, 1)] }, { coefficient := 1, powers := [(2, 1), (15, 1), (20, 1), (49, 1), (54, 1)] }, { coefficient := -1, powers := [(2, 1), (15, 1), (25, 1), (49, 1), (54, 1)] }, { coefficient := 1, powers := [(2, 1), (15, 1), (29, 1), (35, 1), (54, 1)] }, { coefficient := 1, powers := [(4, 1), (8, 1), (29, 1), (33, 1), (53, 1)] }, { coefficient := 1, powers := [(4, 1), (8, 1), (32, 1), (33, 1), (49, 1)] }, { coefficient := 1, powers := [(4, 1), (17, 1), (27, 1), (29, 1), (53, 1)] }, { coefficient := 1, powers := [(4, 1), (17, 1), (27, 1), (32, 1), (49, 1)] }, { coefficient := 1, powers := [(6, 1), (15, 1), (17, 1), (19, 1), (27, 1), (49, 2), (56, 1)] }, { coefficient := -1, powers := [(6, 1), (15, 1), (17, 1), (20, 1), (27, 1), (49, 1), (56, 1)] }, { coefficient := 1, powers := [(6, 1), (15, 1), (17, 1), (25, 1), (27, 1), (49, 1), (56, 1)] }, { coefficient := 1, powers := [(7, 1), (8, 1), (20, 1), (33, 1), (56, 1)] }, { coefficient := -1, powers := [(7, 1), (8, 1), (25, 1), (33, 1), (56, 1)] }, { coefficient := 1, powers := [(7, 1), (8, 1), (29, 1), (33, 1), (43, 1)] }, { coefficient := 1, powers := [(7, 1), (8, 1), (32, 1), (33, 1), (38, 1)] }, { coefficient := -1, powers := [(8, 1), (11, 1), (20, 1), (33, 1), (49, 1)] }, { coefficient := -1, powers := [(8, 1), (11, 1), (25, 1), (33, 1), (38, 1)] }, { coefficient := -1, powers := [(8, 1), (11, 1), (25, 1), (33, 1), (43, 1)] }, { coefficient := -1, powers := [(8, 1), (11, 1), (25, 1), (33, 1), (53, 1)] }, { coefficient := -1, powers := [(8, 1), (11, 1), (29, 1), (33, 1), (35, 1)] }, { coefficient := 1, powers := [(8, 1), (15, 1), (20, 1), (33, 1), (49, 1)] }, { coefficient := -2, powers := [(8, 1), (15, 1), (25, 1), (26, 1), (41, 1), (49, 1), (56, 1)] }, { coefficient := -1, powers := [(8, 1), (15, 1), (25, 1), (33, 1), (49, 1)] }, { coefficient := 1, powers := [(8, 1), (15, 1), (29, 1), (33, 1), (35, 1)] }, { coefficient := -1, powers := [(15, 1), (16, 1), (19, 1), (27, 1), (41, 1), (49, 2)] }, { coefficient := 1, powers := [(15, 1), (16, 1), (20, 1), (27, 1), (41, 1), (49, 1)] }, { coefficient := 2, powers := [(15, 1), (16, 1), (25, 1), (26, 1), (49, 1), (54, 1)] }, { coefficient := -1, powers := [(15, 1), (16, 1), (25, 1), (27, 1), (41, 1), (49, 1)] }, { coefficient := -1, powers := [(15, 1), (17, 1), (19, 1), (27, 1), (49, 2)] }]
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
    (values : Fin 61 → R) :
    ¬ ∀ index : Fin 75,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component13.SelectedLeafB4_6.selectedHasNoCommonZero

end Krenn.Component13.SelectedLeafB4_6
