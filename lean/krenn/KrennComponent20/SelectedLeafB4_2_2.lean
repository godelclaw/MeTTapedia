import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component20.SelectedLeafB4_2_2

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "68db4928895b409ffd463c0a2045c2e15233c2a8f97a93f0ab669e5b10b6fa8d"
def certificateSHA256 : String := "031addc19f33eef578952ac76a997caf97bbf5d4871e41c906bf2e9840f26d5f"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 44 → Fin 645 := ![
  6,
  8,
  15,
  18,
  21,
  27,
  28,
  32,
  34,
  35,
  133,
  140,
  146,
  177,
  183,
  185,
  186,
  189,
  196,
  197,
  199,
  345,
  348,
  349,
  352,
  353,
  407,
  408,
  462,
  480,
  484,
  485,
  527,
  534,
  551,
  579,
  634,
  635,
  636,
  637,
  638,
  640,
  641,
  644
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 44 → SparsePoly (Fin 63) := ![
  [{ coefficient := 1, powers := [(4, 1), (35, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (32, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (22, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(32, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(35, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (28, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (43, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (45, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (25, 1)] }, { coefficient := 1, powers := [(18, 1), (20, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (20, 1)] }, { coefficient := 1, powers := [(18, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (21, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (40, 1)] }, { coefficient := 1, powers := [(19, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (43, 1)] }, { coefficient := 1, powers := [(28, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(40, 1), (43, 1)] }, { coefficient := 1, powers := [(43, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(41, 1), (43, 1)] }, { coefficient := 1, powers := [(47, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(45, 1), (49, 1)] }, { coefficient := 1, powers := [(49, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1)] }, { coefficient := 1, powers := [(21, 1), (43, 1)] }, { coefficient := 1, powers := [(25, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (45, 1)] }, { coefficient := 1, powers := [(4, 1), (34, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (51, 1)] }, { coefficient := 1, powers := [(7, 1), (31, 1)] }, { coefficient := 1, powers := [(11, 1), (27, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (59, 1)] }, { coefficient := 1, powers := [(13, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (59, 1)] }, { coefficient := 1, powers := [(13, 1), (56, 1)] }, { coefficient := 1, powers := [(19, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (32, 1), (55, 1)] }, { coefficient := 1, powers := [(7, 1), (32, 1), (45, 1)] }, { coefficient := 1, powers := [(16, 1), (32, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (35, 1), (51, 1)] }, { coefficient := 1, powers := [(7, 1), (35, 1), (40, 1)] }, { coefficient := 1, powers := [(11, 1), (35, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (47, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1)] }, { coefficient := 1, powers := [(18, 1), (28, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (53, 1)] }, { coefficient := 1, powers := [(29, 1), (41, 1)] }, { coefficient := 1, powers := [(29, 1), (46, 1), (49, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (40, 1), (56, 1)] }, { coefficient := 1, powers := [(26, 1), (40, 1), (43, 1)] }, { coefficient := 1, powers := [(43, 1), (52, 1)] }, { coefficient := 1, powers := [(56, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (41, 1), (55, 1)] }, { coefficient := 1, powers := [(21, 1), (49, 1), (55, 1)] }, { coefficient := 1, powers := [(41, 1)] }, { coefficient := 1, powers := [(46, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (22, 1), (58, 1)] }, { coefficient := 1, powers := [(6, 1), (31, 1), (45, 1)] }, { coefficient := 1, powers := [(6, 1), (34, 1), (40, 1)] }, { coefficient := 1, powers := [(22, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (22, 1), (58, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1), (45, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (40, 1)] }, { coefficient := 1, powers := [(18, 1), (22, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (43, 1), (52, 1)] }, { coefficient := 1, powers := [(24, 1), (56, 1)] }, { coefficient := 1, powers := [(29, 1), (47, 1)] }, { coefficient := 1, powers := [(35, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (58, 1)] }, { coefficient := 1, powers := [(7, 1), (58, 1)] }, { coefficient := 1, powers := [(11, 1), (45, 1)] }, { coefficient := 1, powers := [(11, 1), (55, 1)] }, { coefficient := 1, powers := [(16, 1), (40, 1)] }, { coefficient := 1, powers := [(16, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (37, 1), (58, 1)] }, { coefficient := 1, powers := [(1, 1), (40, 1), (55, 1)] }, { coefficient := 1, powers := [(1, 1), (45, 1), (51, 1)] }, { coefficient := 1, powers := [(4, 1), (27, 1), (58, 1)] }, { coefficient := 1, powers := [(4, 1), (31, 1), (55, 1)] }, { coefficient := 1, powers := [(4, 1), (34, 1), (51, 1)] }, { coefficient := 1, powers := [(7, 1), (22, 1), (58, 1)] }, { coefficient := 1, powers := [(7, 1), (31, 1), (45, 1)] }, { coefficient := 1, powers := [(7, 1), (34, 1), (40, 1)] }, { coefficient := 1, powers := [(11, 1), (22, 1), (55, 1)] }, { coefficient := 1, powers := [(11, 1), (27, 1), (45, 1)] }, { coefficient := 1, powers := [(11, 1), (34, 1), (37, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1), (51, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1), (40, 1)] }, { coefficient := 1, powers := [(16, 1), (31, 1), (37, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (41, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (47, 1), (53, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (53, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (59, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (47, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(13, 1), (24, 1), (56, 1)] }, { coefficient := 1, powers := [(13, 1), (29, 1), (47, 1)] }, { coefficient := 1, powers := [(13, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (53, 1)] }, { coefficient := 1, powers := [(19, 1), (29, 1), (41, 1)] }, { coefficient := 1, powers := [(19, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (60, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1)] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(40, 1), (61, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(41, 1)] }],
  [{ coefficient := 1, powers := [(56, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 44 → SparsePoly (Fin 63) := ![
  [{ coefficient := -2, powers := [(5, 1), (22, 1), (51, 1), (53, 1), (58, 1), (61, 1)] }, { coefficient := 2, powers := [(5, 1), (27, 1), (51, 1), (53, 1), (58, 1), (61, 1)] }, { coefficient := -2, powers := [(5, 1), (31, 1), (45, 1), (51, 1), (53, 1), (61, 1)] }, { coefficient := -2, powers := [(5, 1), (31, 1), (51, 1), (53, 1), (55, 1), (61, 1)] }, { coefficient := 2, powers := [(5, 1), (31, 1), (53, 1), (55, 1)] }, { coefficient := -2, powers := [(5, 1), (34, 1), (51, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (22, 1), (47, 1), (58, 1)] }, { coefficient := -1, powers := [(8, 1), (27, 1), (47, 1), (58, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1), (47, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (40, 1), (47, 1)] }],
  [{ coefficient := 2, powers := [(5, 1), (11, 1), (21, 1), (22, 1), (29, 1), (35, 1), (53, 1), (55, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (11, 1), (21, 1), (22, 1), (29, 1), (32, 1), (47, 1), (55, 1), (60, 1)] }, { coefficient := 1, powers := [(21, 1), (29, 1), (60, 1)] }],
  [{ coefficient := -2, powers := [(5, 1), (27, 1), (35, 1), (51, 1)] }],
  [{ coefficient := 2, powers := [(5, 1), (11, 1), (32, 1), (35, 1), (38, 1), (53, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (11, 1), (32, 2), (38, 1), (47, 1), (55, 1)] }],
  [{ coefficient := 2, powers := [(5, 1), (6, 1), (11, 1), (18, 1), (32, 1), (35, 1), (47, 1), (53, 1), (55, 1)] }, { coefficient := 2, powers := [(5, 1), (11, 1), (13, 1), (28, 1), (35, 1), (47, 1), (53, 1), (55, 1)] }, { coefficient := 1, powers := [(6, 1), (8, 1), (11, 1), (18, 1), (32, 2), (47, 2), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (11, 1), (13, 1), (28, 1), (32, 1), (47, 2), (55, 1)] }],
  [{ coefficient := 2, powers := [(5, 2), (11, 1), (35, 2), (53, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (8, 1), (11, 1), (32, 1), (35, 1), (47, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (16, 1), (32, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (11, 1), (34, 1), (47, 1)] }],
  [{ coefficient := -2, powers := [(5, 1), (11, 1), (22, 1), (53, 1), (58, 1), (61, 1)] }, { coefficient := 2, powers := [(5, 1), (11, 1), (27, 1), (53, 1), (58, 1), (61, 1)] }, { coefficient := -2, powers := [(5, 1), (11, 1), (31, 1), (45, 1), (53, 1), (61, 1)] }, { coefficient := -2, powers := [(5, 1), (11, 1), (31, 1), (53, 1), (55, 1), (61, 1)] }, { coefficient := 2, powers := [(5, 1), (16, 1), (31, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(13, 1), (26, 1)] }],
  [{ coefficient := -1, powers := [(19, 1), (21, 1)] }],
  [{ coefficient := 2, powers := [(5, 1), (11, 1), (22, 1), (29, 1), (35, 1), (47, 1), (53, 1), (55, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (11, 1), (22, 1), (29, 1), (32, 1), (47, 2), (55, 1), (60, 1)] }, { coefficient := 1, powers := [(29, 1), (47, 1), (60, 1)] }],
  [{ coefficient := -2, powers := [(5, 1), (11, 1), (22, 1), (29, 1), (35, 1), (47, 1), (49, 1), (53, 1), (55, 1), (60, 1)] }, { coefficient := -1, powers := [(8, 1), (11, 1), (22, 1), (29, 1), (32, 1), (47, 2), (49, 1), (55, 1), (60, 1)] }, { coefficient := -1, powers := [(29, 1), (47, 1), (49, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(28, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(21, 1), (28, 1), (53, 1)] }],
  [{ coefficient := -2, powers := [(5, 1), (11, 1), (13, 1), (22, 1), (35, 1), (52, 1), (53, 1), (55, 1)] }, { coefficient := -1, powers := [(8, 1), (11, 1), (13, 1), (22, 1), (32, 1), (47, 1), (52, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (24, 1), (26, 1)] }],
  [{ coefficient := 2, powers := [(5, 1), (11, 1), (18, 1), (22, 1), (25, 1), (29, 1), (35, 1), (53, 1), (55, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (11, 1), (18, 1), (22, 1), (25, 1), (29, 1), (32, 1), (47, 1), (55, 1), (60, 1)] }, { coefficient := 1, powers := [(18, 1), (25, 1), (29, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (21, 1), (29, 1)] }],
  [{ coefficient := -2, powers := [(5, 1), (11, 1), (13, 1), (22, 1), (29, 1), (35, 1), (53, 1), (55, 1), (60, 1)] }, { coefficient := -1, powers := [(8, 1), (11, 1), (13, 1), (22, 1), (29, 1), (32, 1), (47, 1), (55, 1), (60, 1)] }, { coefficient := -1, powers := [(13, 1), (29, 1), (60, 1)] }],
  [{ coefficient := 2, powers := [(5, 1), (35, 1), (51, 1), (53, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (47, 1), (51, 1)] }],
  [{ coefficient := -2, powers := [(5, 1), (35, 1), (53, 1), (55, 1)] }, { coefficient := -1, powers := [(8, 1), (32, 1), (47, 1), (55, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (5, 1), (11, 1), (22, 1), (29, 1), (35, 1), (53, 1), (55, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (8, 1), (11, 1), (22, 1), (29, 1), (32, 1), (47, 1), (55, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (29, 1), (60, 1)] }],
  [{ coefficient := 2, powers := [(5, 1), (11, 1), (22, 1), (24, 1), (35, 1), (53, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (11, 1), (22, 1), (24, 1), (32, 1), (47, 1), (55, 1)] }, { coefficient := 1, powers := [(24, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (31, 1), (47, 1)] }],
  [{ coefficient := 2, powers := [(5, 1), (22, 1), (53, 1), (58, 1), (61, 1)] }, { coefficient := -2, powers := [(5, 1), (27, 1), (53, 1), (58, 1), (61, 1)] }, { coefficient := 2, powers := [(5, 1), (31, 1), (45, 1), (53, 1), (61, 1)] }, { coefficient := 2, powers := [(5, 1), (31, 1), (53, 1), (55, 1), (61, 1)] }, { coefficient := 2, powers := [(5, 1), (34, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(53, 1)] }],
  [{ coefficient := 1, powers := [(19, 1)] }],
  [{ coefficient := -1, powers := [(13, 1), (24, 1)] }],
  [{ coefficient := -1, powers := [(19, 1), (29, 1)] }],
  [{ coefficient := 2, powers := [(5, 1), (8, 1), (11, 1), (32, 1), (35, 1), (47, 1), (53, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 2), (11, 1), (32, 2), (47, 2), (55, 1)] }],
  [{ coefficient := -2, powers := [(5, 1), (6, 1), (11, 1), (32, 1), (35, 1), (47, 1), (53, 1), (55, 1)] }, { coefficient := -1, powers := [(6, 1), (8, 1), (11, 1), (32, 2), (47, 2), (55, 1)] }],
  [{ coefficient := 2, powers := [(5, 1), (11, 1), (13, 1), (22, 1), (35, 1), (53, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (11, 1), (13, 1), (22, 1), (32, 1), (47, 1), (55, 1)] }, { coefficient := 1, powers := [(13, 1)] }],
  [{ coefficient := 2, powers := [(5, 1), (27, 1), (35, 1), (53, 1)] }, { coefficient := 1, powers := [(8, 1), (27, 1), (32, 1), (47, 1)] }],
  [{ coefficient := -2, powers := [(5, 1), (35, 1), (53, 1)] }, { coefficient := -1, powers := [(8, 1), (32, 1), (47, 1)] }],
  [{ coefficient := -2, powers := [(5, 1), (11, 1), (22, 1), (35, 1), (53, 1), (55, 1)] }, { coefficient := -1, powers := [(8, 1), (11, 1), (22, 1), (32, 1), (47, 1), (55, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := -2, powers := [(5, 2), (11, 1), (22, 1), (29, 1), (35, 1), (53, 1), (55, 1), (59, 1)] }, { coefficient := -1, powers := [(5, 1), (8, 1), (11, 1), (22, 1), (29, 1), (32, 1), (47, 1), (55, 1), (59, 1)] }, { coefficient := -1, powers := [(5, 1), (29, 1), (59, 1)] }],
  [{ coefficient := 2, powers := [(5, 1), (35, 1), (37, 1), (53, 1), (58, 1)] }, { coefficient := 2, powers := [(5, 1), (35, 1), (40, 1), (53, 1), (55, 1)] }, { coefficient := 2, powers := [(5, 1), (35, 1), (51, 1), (53, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (37, 1), (47, 1), (58, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (40, 1), (47, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (47, 1), (51, 1), (55, 1)] }],
  [{ coefficient := 2, powers := [(5, 1), (11, 1), (22, 1), (35, 1), (38, 1), (53, 1), (55, 1), (59, 1)] }, { coefficient := 2, powers := [(5, 1), (11, 1), (22, 1), (35, 1), (47, 1), (53, 2), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (11, 1), (22, 1), (32, 1), (38, 1), (47, 1), (55, 1), (59, 1)] }, { coefficient := 1, powers := [(8, 1), (11, 1), (22, 1), (32, 1), (47, 2), (53, 1), (55, 1)] }, { coefficient := 1, powers := [(38, 1), (59, 1)] }, { coefficient := 2, powers := [(47, 1), (53, 1)] }],
  [{ coefficient := -2, powers := [(5, 1), (7, 1), (22, 1), (35, 1), (53, 1), (58, 1)] }, { coefficient := 2, powers := [(5, 1), (7, 1), (27, 1), (35, 1), (53, 1), (58, 1)] }, { coefficient := -2, powers := [(5, 1), (7, 1), (31, 1), (35, 1), (45, 1), (53, 1)] }, { coefficient := -2, powers := [(5, 1), (7, 1), (31, 1), (35, 1), (53, 1), (55, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (5, 1), (11, 1), (19, 1), (22, 1), (29, 1), (35, 1), (53, 1), (55, 1), (60, 1)] }, { coefficient := -1, powers := [(0, 1), (8, 1), (11, 1), (19, 1), (22, 1), (29, 1), (32, 1), (47, 1), (55, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (19, 1), (29, 1), (55, 1)] }, { coefficient := -1, powers := [(0, 1), (19, 1), (29, 1), (60, 1)] }, { coefficient := 2, powers := [(5, 1), (8, 1), (11, 1), (22, 1), (35, 2), (53, 1), (55, 1)] }, { coefficient := -2, powers := [(5, 1), (11, 1), (18, 1), (22, 1), (25, 1), (29, 1), (35, 1), (43, 1), (53, 1), (55, 1), (60, 1)] }, { coefficient := 2, powers := [(5, 1), (11, 1), (19, 1), (22, 1), (29, 1), (35, 1), (53, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 2), (11, 1), (22, 1), (32, 1), (35, 1), (47, 1), (55, 1)] }, { coefficient := -1, powers := [(8, 1), (11, 1), (18, 1), (22, 1), (25, 1), (29, 1), (32, 1), (43, 1), (47, 1), (55, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (11, 1), (19, 1), (22, 1), (29, 1), (32, 1), (47, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1)] }, { coefficient := -1, powers := [(18, 1), (25, 1), (29, 1), (43, 1), (60, 1)] }, { coefficient := 1, powers := [(19, 1), (29, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (13, 1), (24, 1), (40, 1)] }, { coefficient := 2, powers := [(2, 1), (5, 1), (11, 1), (22, 1), (35, 1), (41, 1), (53, 1), (55, 1)] }, { coefficient := 1, powers := [(2, 1), (8, 1), (11, 1), (22, 1), (32, 1), (41, 1), (47, 1), (55, 1)] }, { coefficient := 1, powers := [(2, 1), (41, 1)] }, { coefficient := 2, powers := [(5, 2), (11, 1), (22, 1), (32, 1), (35, 1), (53, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (8, 1), (11, 1), (22, 1), (32, 2), (47, 1), (55, 1)] }, { coefficient := -2, powers := [(5, 1), (11, 1), (13, 1), (22, 1), (24, 1), (35, 1), (53, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1)] }, { coefficient := -1, powers := [(8, 1), (11, 1), (13, 1), (22, 1), (24, 1), (32, 1), (47, 1), (55, 1)] }]
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
    (values : Fin 63 → R) :
    ¬ ∀ index : Fin 44,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component20.SelectedLeafB4_2_2.selectedHasNoCommonZero

end Krenn.Component20.SelectedLeafB4_2_2
