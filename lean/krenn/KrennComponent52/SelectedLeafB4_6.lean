import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component52.SelectedLeafB4_6

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "18415b00b08f13dd58e5cbeec877eb6e23e1ed17478f08430efa43d5883e73e3"
def certificateSHA256 : String := "547793afa48618656a485e2b27238cb02748db121796f4105e4787ae4e61b213"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 57 → Fin 640 := ![
  8,
  9,
  10,
  11,
  15,
  16,
  17,
  19,
  21,
  23,
  24,
  26,
  28,
  34,
  36,
  161,
  162,
  165,
  166,
  168,
  170,
  184,
  185,
  193,
  196,
  197,
  198,
  205,
  207,
  221,
  234,
  235,
  236,
  258,
  293,
  307,
  310,
  346,
  347,
  352,
  353,
  354,
  459,
  460,
  461,
  494,
  499,
  560,
  570,
  579,
  604,
  632,
  633,
  635,
  636,
  637,
  639
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 57 → SparsePoly (Fin 63) := ![
  [{ coefficient := 1, powers := [(5, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (30, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (29, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (23, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (19, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (19, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (20, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(28, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(28, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1)] }, { coefficient := 1, powers := [(24, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1)] }, { coefficient := 1, powers := [(24, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (45, 1)] }, { coefficient := 1, powers := [(18, 1), (28, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (51, 1)] }, { coefficient := 1, powers := [(13, 1), (28, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (35, 1)] }, { coefficient := 1, powers := [(17, 1), (28, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (32, 1)] }, { coefficient := 1, powers := [(12, 1), (28, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (44, 1)] }, { coefficient := 1, powers := [(13, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (45, 1)] }, { coefficient := 1, powers := [(18, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (56, 1)] }, { coefficient := 1, powers := [(26, 1), (45, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(28, 1), (45, 1)] }, { coefficient := 1, powers := [(35, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(28, 1), (51, 1)] }, { coefficient := 1, powers := [(32, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(28, 1), (56, 1)] }, { coefficient := 1, powers := [(29, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1), (50, 1)] }, { coefficient := 1, powers := [(45, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1), (50, 1)] }, { coefficient := 1, powers := [(47, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (29, 1), (58, 1)] }, { coefficient := 1, powers := [(29, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (28, 1), (58, 1)] }, { coefficient := 1, powers := [(28, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (28, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (32, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (31, 1), (45, 1)] }, { coefficient := 1, powers := [(26, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (24, 1), (45, 1)] }, { coefficient := 1, powers := [(17, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (19, 1), (55, 1)] }, { coefficient := 1, powers := [(13, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (19, 1), (49, 1)] }, { coefficient := 1, powers := [(17, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (19, 1), (49, 1)] }, { coefficient := 1, powers := [(18, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (47, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (53, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1)] }, { coefficient := 1, powers := [(13, 1), (29, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (50, 1)] }, { coefficient := 1, powers := [(23, 1), (55, 1)] }, { coefficient := 1, powers := [(28, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (53, 1)] }, { coefficient := 1, powers := [(29, 1), (41, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (56, 1)] }, { coefficient := 1, powers := [(29, 1), (47, 1)] }, { coefficient := 1, powers := [(35, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (59, 1)] }, { coefficient := 1, powers := [(12, 1), (45, 1)] }, { coefficient := 1, powers := [(17, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (59, 1)] }, { coefficient := 1, powers := [(13, 1), (47, 1)] }, { coefficient := 1, powers := [(18, 1), (20, 1), (51, 1)] }, { coefficient := 1, powers := [(18, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (59, 1)] }, { coefficient := 1, powers := [(13, 1), (25, 1), (45, 1)] }, { coefficient := 1, powers := [(13, 1), (56, 1)] }, { coefficient := 1, powers := [(18, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (30, 1), (56, 1)] }, { coefficient := 1, powers := [(10, 1), (25, 1), (45, 1)] }, { coefficient := 1, powers := [(10, 1), (56, 1)] }, { coefficient := 1, powers := [(17, 1), (25, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (30, 1), (56, 1)] }, { coefficient := 1, powers := [(8, 1), (30, 1), (47, 1)] }, { coefficient := 1, powers := [(18, 1), (20, 1), (25, 1), (49, 1)] }, { coefficient := 1, powers := [(18, 1), (30, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (30, 1)] }, { coefficient := 1, powers := [(10, 1), (19, 1), (55, 1)] }, { coefficient := 1, powers := [(10, 1)] }, { coefficient := 1, powers := [(16, 1), (19, 1), (49, 1)] }, { coefficient := 1, powers := [(16, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (41, 1), (55, 1)] }, { coefficient := 1, powers := [(2, 1), (46, 1), (51, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (55, 1)] }, { coefficient := 1, powers := [(13, 1), (23, 1), (55, 1)] }, { coefficient := 1, powers := [(13, 1), (28, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (58, 1)] }, { coefficient := 1, powers := [(7, 1), (58, 1)] }, { coefficient := 1, powers := [(11, 1), (44, 1)] }, { coefficient := 1, powers := [(11, 1), (55, 1)] }, { coefficient := 1, powers := [(16, 1), (40, 1)] }, { coefficient := 1, powers := [(16, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (29, 1), (59, 1)] }, { coefficient := 1, powers := [(4, 1), (32, 1), (56, 1)] }, { coefficient := 1, powers := [(4, 1), (35, 1), (53, 1)] }, { coefficient := 1, powers := [(12, 1), (28, 1), (56, 1)] }, { coefficient := 1, powers := [(12, 1), (29, 1), (45, 1)] }, { coefficient := 1, powers := [(17, 1), (28, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (37, 1), (58, 1)] }, { coefficient := 1, powers := [(1, 1), (40, 1), (55, 1)] }, { coefficient := 1, powers := [(1, 1), (44, 1), (50, 1)] }, { coefficient := 1, powers := [(4, 1), (27, 1), (58, 1)] }, { coefficient := 1, powers := [(4, 1), (31, 1), (55, 1)] }, { coefficient := 1, powers := [(4, 1), (34, 1), (50, 1)] }, { coefficient := 1, powers := [(7, 1), (22, 1), (58, 1)] }, { coefficient := 1, powers := [(7, 1), (31, 1), (44, 1)] }, { coefficient := 1, powers := [(7, 1), (34, 1), (40, 1)] }, { coefficient := 1, powers := [(11, 1), (22, 1), (55, 1)] }, { coefficient := 1, powers := [(11, 1), (27, 1), (44, 1)] }, { coefficient := 1, powers := [(11, 1), (34, 1), (37, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1), (50, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1), (40, 1)] }, { coefficient := 1, powers := [(16, 1), (31, 1), (37, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (41, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (47, 1), (53, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (53, 1)] }, { coefficient := 1, powers := [(8, 1), (23, 1), (59, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (47, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(13, 1), (23, 1), (56, 1)] }, { coefficient := 1, powers := [(13, 1), (29, 1), (47, 1)] }, { coefficient := 1, powers := [(13, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (53, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (41, 1)] }, { coefficient := 1, powers := [(18, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1)] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(39, 1), (61, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(41, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 57 → SparsePoly (Fin 63) := ![
  [{ coefficient := -1, powers := [(3, 1), (17, 1), (29, 1), (34, 1), (50, 1), (51, 1)] }, { coefficient := 1, powers := [(6, 1), (11, 1), (28, 1), (34, 1), (51, 1), (56, 1)] }, { coefficient := 1, powers := [(6, 1), (16, 1), (28, 1), (31, 1), (51, 1), (56, 1)] }, { coefficient := 1, powers := [(7, 1), (22, 1), (32, 1), (56, 1)] }, { coefficient := 2, powers := [(7, 1), (22, 1), (35, 1), (53, 1)] }, { coefficient := -1, powers := [(7, 1), (27, 1), (32, 1), (56, 1)] }, { coefficient := -2, powers := [(7, 1), (27, 1), (35, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (11, 1), (28, 1), (31, 1), (52, 1), (55, 1)] }, { coefficient := -1, powers := [(5, 1), (16, 1), (28, 1), (31, 1), (50, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (27, 1), (32, 1), (47, 1), (50, 1), (61, 1)] }, { coefficient := -1, powers := [(7, 1), (27, 1), (32, 1), (47, 1), (50, 1), (61, 1)] }],
  [{ coefficient := 2, powers := [(7, 1), (22, 1), (32, 1), (47, 1)] }, { coefficient := -2, powers := [(7, 1), (27, 1), (32, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (31, 1), (44, 1), (45, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (40, 1), (45, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (45, 1), (50, 1)] }],
  [{ coefficient := 2, powers := [(4, 1), (29, 1), (31, 1), (44, 1), (47, 1), (50, 1)] }, { coefficient := -1, powers := [(4, 1), (29, 1), (34, 1), (47, 1), (50, 2)] }, { coefficient := -2, powers := [(11, 1), (22, 1), (29, 1), (47, 1), (50, 1), (55, 1)] }, { coefficient := -2, powers := [(11, 1), (27, 1), (29, 1), (44, 1), (47, 1), (50, 1)] }, { coefficient := -2, powers := [(16, 1), (22, 1), (29, 1), (47, 1), (50, 2)] }, { coefficient := 2, powers := [(16, 1), (27, 1), (29, 1), (47, 1), (50, 2)] }],
  [{ coefficient := -1, powers := [(4, 1), (23, 1), (31, 1), (45, 1), (55, 1)] }, { coefficient := -1, powers := [(4, 1), (23, 1), (34, 1), (45, 1), (50, 1)] }, { coefficient := -1, powers := [(7, 1), (22, 1), (23, 1), (45, 1), (58, 1)] }, { coefficient := 1, powers := [(7, 1), (23, 1), (27, 1), (45, 1), (58, 1)] }, { coefficient := -1, powers := [(7, 1), (23, 1), (31, 1), (44, 1), (45, 1)] }, { coefficient := -1, powers := [(7, 1), (23, 1), (34, 1), (40, 1), (45, 1)] }, { coefficient := -1, powers := [(11, 1), (22, 1), (23, 1), (45, 1), (55, 1)] }, { coefficient := 1, powers := [(11, 1), (23, 1), (27, 1), (45, 1), (55, 1)] }, { coefficient := -1, powers := [(11, 1), (23, 1), (34, 1), (37, 1), (45, 1)] }, { coefficient := -1, powers := [(16, 1), (22, 1), (23, 1), (45, 1), (50, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1), (27, 1), (45, 1), (50, 1)] }, { coefficient := -1, powers := [(16, 1), (23, 1), (31, 1), (37, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (27, 1), (50, 1), (56, 1)] }, { coefficient := 2, powers := [(18, 1), (27, 1), (50, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (25, 1), (27, 1), (32, 1), (48, 1), (49, 1), (50, 2), (61, 2)] }, { coefficient := 1, powers := [(5, 1), (25, 1), (27, 1), (32, 1), (49, 2), (50, 1), (61, 2)] }],
  [{ coefficient := -2, powers := [(4, 1), (23, 1), (31, 1), (49, 1), (50, 1), (53, 1), (61, 1)] }, { coefficient := -1, powers := [(4, 1), (27, 1), (30, 1), (32, 1), (38, 1), (49, 1), (50, 1), (61, 2)] }, { coefficient := 1, powers := [(7, 1), (27, 1), (30, 1), (32, 1), (38, 1), (49, 1), (50, 1), (61, 2)] }, { coefficient := 2, powers := [(11, 1), (23, 1), (27, 1), (49, 1), (50, 1), (53, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (25, 1), (27, 1), (32, 1), (49, 1), (50, 1), (61, 1)] }, { coefficient := -1, powers := [(4, 1), (29, 1), (31, 1), (51, 1), (55, 1)] }, { coefficient := -1, powers := [(4, 1), (29, 1), (34, 1), (50, 1), (51, 1)] }, { coefficient := -1, powers := [(7, 1), (22, 1), (29, 1), (51, 1), (58, 1)] }, { coefficient := -1, powers := [(7, 1), (25, 1), (27, 1), (32, 1), (49, 1), (50, 1), (61, 1)] }, { coefficient := 1, powers := [(7, 1), (27, 1), (29, 1), (51, 1), (58, 1)] }, { coefficient := -1, powers := [(7, 1), (29, 1), (31, 1), (44, 1), (51, 1)] }, { coefficient := -1, powers := [(7, 1), (29, 1), (34, 1), (40, 1), (51, 1)] }, { coefficient := -1, powers := [(7, 1), (29, 1), (34, 1), (50, 1), (51, 1)] }, { coefficient := -1, powers := [(11, 1), (22, 1), (29, 1), (51, 1), (55, 1)] }, { coefficient := 1, powers := [(11, 1), (27, 1), (29, 1), (51, 1), (55, 1)] }, { coefficient := -1, powers := [(11, 1), (29, 1), (34, 1), (37, 1), (51, 1)] }, { coefficient := -1, powers := [(16, 1), (22, 1), (29, 1), (50, 1), (51, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1), (29, 1), (50, 1), (51, 1)] }, { coefficient := -1, powers := [(16, 1), (29, 1), (31, 1), (37, 1), (51, 1)] }],
  [{ coefficient := 2, powers := [(4, 1), (13, 1), (23, 1), (31, 1), (44, 1), (50, 1)] }, { coefficient := 1, powers := [(5, 1), (10, 1), (27, 1), (32, 1), (50, 1), (55, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (16, 1), (27, 1), (32, 1), (49, 1), (50, 1), (61, 1)] }, { coefficient := -1, powers := [(7, 1), (13, 1), (22, 1), (23, 1), (44, 1), (58, 1)] }, { coefficient := 1, powers := [(7, 1), (13, 1), (23, 1), (27, 1), (44, 1), (58, 1)] }, { coefficient := -1, powers := [(7, 1), (13, 1), (23, 1), (31, 1), (44, 2)] }, { coefficient := -1, powers := [(7, 1), (13, 1), (23, 1), (34, 1), (40, 1), (44, 1)] }, { coefficient := -1, powers := [(11, 1), (13, 1), (22, 1), (23, 1), (44, 1), (55, 1)] }, { coefficient := -2, powers := [(11, 1), (13, 1), (23, 1), (27, 1), (44, 1), (50, 1)] }, { coefficient := -1, powers := [(13, 1), (16, 1), (22, 1), (23, 1), (44, 1), (50, 1)] }],
  [{ coefficient := -2, powers := [(11, 1), (18, 1), (23, 1), (55, 1)] }, { coefficient := -2, powers := [(16, 1), (18, 1), (23, 1), (50, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (11, 1), (34, 1), (51, 1)] }, { coefficient := -2, powers := [(8, 1), (12, 1), (31, 1), (44, 1)] }, { coefficient := -2, powers := [(8, 1), (12, 1), (34, 1), (40, 1)] }, { coefficient := -1, powers := [(8, 1), (12, 1), (34, 1), (50, 1)] }, { coefficient := -1, powers := [(8, 1), (16, 1), (31, 1), (51, 1)] }],
  [{ coefficient := 2, powers := [(4, 1), (18, 1), (31, 1), (46, 1)] }, { coefficient := -2, powers := [(5, 1), (11, 1), (34, 1), (45, 1)] }, { coefficient := -2, powers := [(5, 1), (16, 1), (31, 1), (45, 1)] }, { coefficient := -2, powers := [(5, 1), (17, 1), (34, 1), (50, 1)] }, { coefficient := -2, powers := [(11, 1), (18, 1), (27, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (10, 1), (25, 1), (27, 1), (32, 1), (50, 2), (61, 1)] }],
  [{ coefficient := -2, powers := [(4, 1), (13, 1), (29, 1), (31, 1), (44, 1), (50, 1)] }, { coefficient := 1, powers := [(4, 1), (13, 1), (29, 1), (34, 1), (50, 2)] }, { coefficient := 2, powers := [(11, 1), (13, 1), (22, 1), (29, 1), (50, 1), (55, 1)] }, { coefficient := 2, powers := [(11, 1), (13, 1), (27, 1), (29, 1), (44, 1), (50, 1)] }, { coefficient := 2, powers := [(13, 1), (16, 1), (22, 1), (29, 1), (50, 2)] }, { coefficient := -2, powers := [(13, 1), (16, 1), (27, 1), (29, 1), (50, 2)] }],
  [{ coefficient := 1, powers := [(11, 1), (34, 1), (38, 1), (51, 1)] }, { coefficient := -2, powers := [(12, 1), (31, 1), (38, 1), (44, 1)] }, { coefficient := -2, powers := [(12, 1), (34, 1), (38, 1), (40, 1)] }, { coefficient := 1, powers := [(16, 1), (31, 1), (38, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (31, 1), (46, 1), (56, 1)] }, { coefficient := -1, powers := [(11, 1), (27, 1), (46, 1), (56, 1)] }, { coefficient := -1, powers := [(17, 1), (34, 1), (38, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (34, 1), (50, 1), (53, 1)] }, { coefficient := 1, powers := [(13, 1), (34, 1), (38, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (31, 1), (44, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (40, 1), (56, 1)] }, { coefficient := 2, powers := [(8, 1), (31, 1), (44, 1), (47, 1)] }, { coefficient := 2, powers := [(8, 1), (34, 1), (40, 1), (47, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (47, 1), (50, 1)] }, { coefficient := 2, powers := [(18, 1), (31, 1), (38, 1), (44, 1)] }, { coefficient := 2, powers := [(18, 1), (34, 1), (38, 1), (40, 1)] }],
  [{ coefficient := -2, powers := [(4, 1), (19, 1), (23, 1), (31, 1), (50, 1), (56, 1)] }, { coefficient := -2, powers := [(4, 1), (29, 1), (31, 1), (47, 1)] }, { coefficient := 1, powers := [(7, 1), (19, 1), (22, 1), (23, 1), (56, 1), (58, 1)] }, { coefficient := -1, powers := [(7, 1), (19, 1), (23, 1), (27, 1), (56, 1), (58, 1)] }, { coefficient := 1, powers := [(7, 1), (19, 1), (23, 1), (31, 1), (44, 1), (56, 1)] }, { coefficient := 1, powers := [(7, 1), (19, 1), (23, 1), (34, 1), (40, 1), (56, 1)] }, { coefficient := 1, powers := [(11, 1), (19, 1), (22, 1), (23, 1), (55, 1), (56, 1)] }, { coefficient := 2, powers := [(11, 1), (19, 1), (23, 1), (27, 1), (50, 1), (56, 1)] }, { coefficient := 2, powers := [(11, 1), (27, 1), (29, 1), (47, 1)] }, { coefficient := 1, powers := [(16, 1), (19, 1), (22, 1), (23, 1), (50, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [(11, 1), (28, 1), (34, 1), (38, 1)] }, { coefficient := -1, powers := [(16, 1), (28, 1), (31, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (11, 1), (32, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (16, 1), (32, 1), (50, 1)] }],
  [{ coefficient := 2, powers := [(5, 1), (11, 1), (34, 1), (53, 1)] }, { coefficient := 2, powers := [(5, 1), (16, 1), (31, 1), (53, 1)] }, { coefficient := 1, powers := [(11, 1), (13, 1), (34, 1), (38, 1)] }, { coefficient := 1, powers := [(13, 1), (16, 1), (31, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (11, 1), (34, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (16, 1), (31, 1), (56, 1)] }, { coefficient := 1, powers := [(8, 1), (11, 1), (34, 1), (47, 1)] }, { coefficient := 1, powers := [(8, 1), (16, 1), (31, 1), (47, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (12, 1), (31, 1), (44, 1)] }, { coefficient := -1, powers := [(5, 1), (12, 1), (34, 1), (40, 1)] }, { coefficient := -1, powers := [(5, 1), (12, 1), (34, 1), (50, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (10, 1), (25, 1), (27, 1), (32, 1), (50, 1), (61, 1)] }],
  [{ coefficient := 2, powers := [(4, 1), (13, 1), (29, 1), (31, 1), (44, 1)] }, { coefficient := -1, powers := [(4, 1), (13, 1), (29, 1), (34, 1), (50, 1)] }, { coefficient := -2, powers := [(11, 1), (13, 1), (22, 1), (29, 1), (55, 1)] }, { coefficient := -2, powers := [(11, 1), (13, 1), (27, 1), (29, 1), (44, 1)] }, { coefficient := -2, powers := [(13, 1), (16, 1), (22, 1), (29, 1), (50, 1)] }, { coefficient := 2, powers := [(13, 1), (16, 1), (27, 1), (29, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (17, 1), (34, 1), (50, 1), (51, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (11, 1), (34, 1), (51, 1), (56, 1)] }, { coefficient := -1, powers := [(5, 1), (16, 1), (31, 1), (51, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (11, 1), (31, 1), (52, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (16, 1), (31, 1), (50, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (11, 1), (32, 1), (52, 1), (55, 1)] }, { coefficient := -1, powers := [(5, 1), (16, 1), (32, 1), (50, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (25, 1), (27, 1), (32, 1), (50, 2), (61, 1)] }],
  [{ coefficient := 2, powers := [(4, 1), (23, 1), (31, 1), (50, 1), (56, 1)] }, { coefficient := -1, powers := [(7, 1), (22, 1), (23, 1), (56, 1), (58, 1)] }, { coefficient := 1, powers := [(7, 1), (23, 1), (27, 1), (56, 1), (58, 1)] }, { coefficient := -1, powers := [(7, 1), (23, 1), (31, 1), (44, 1), (56, 1)] }, { coefficient := -1, powers := [(7, 1), (23, 1), (34, 1), (40, 1), (56, 1)] }, { coefficient := -1, powers := [(11, 1), (22, 1), (23, 1), (55, 1), (56, 1)] }, { coefficient := -2, powers := [(11, 1), (23, 1), (27, 1), (50, 1), (56, 1)] }, { coefficient := -1, powers := [(16, 1), (22, 1), (23, 1), (50, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (25, 1), (27, 1), (32, 1), (48, 1), (50, 2), (61, 2)] }, { coefficient := -1, powers := [(5, 1), (25, 1), (27, 1), (32, 1), (49, 1), (50, 1), (61, 2)] }],
  [{ coefficient := 2, powers := [(4, 1), (23, 1), (31, 1), (50, 1), (53, 1), (61, 1)] }, { coefficient := 1, powers := [(4, 1), (27, 1), (30, 1), (32, 1), (38, 1), (50, 1), (61, 2)] }, { coefficient := -1, powers := [(7, 1), (27, 1), (30, 1), (32, 1), (38, 1), (50, 1), (61, 2)] }, { coefficient := -2, powers := [(11, 1), (23, 1), (27, 1), (50, 1), (53, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (31, 1), (53, 1), (55, 1)] }, { coefficient := -1, powers := [(4, 1), (34, 1), (50, 1), (53, 1)] }, { coefficient := -1, powers := [(7, 1), (22, 1), (53, 1), (58, 1)] }, { coefficient := 1, powers := [(7, 1), (27, 1), (53, 1), (58, 1)] }, { coefficient := 1, powers := [(7, 1), (31, 1), (44, 1), (53, 1)] }, { coefficient := 1, powers := [(7, 1), (34, 1), (40, 1), (53, 1)] }, { coefficient := 1, powers := [(11, 1), (22, 1), (53, 1), (55, 1)] }, { coefficient := -1, powers := [(11, 1), (27, 1), (53, 1), (55, 1)] }, { coefficient := -1, powers := [(11, 1), (34, 1), (37, 1), (53, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1), (50, 1), (53, 1)] }, { coefficient := -1, powers := [(16, 1), (27, 1), (50, 1), (53, 1)] }, { coefficient := -1, powers := [(16, 1), (31, 1), (37, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (31, 1), (47, 1), (55, 1)] }, { coefficient := 1, powers := [(4, 1), (34, 1), (47, 1), (50, 1)] }, { coefficient := -1, powers := [(7, 1), (22, 1), (47, 1), (58, 1)] }, { coefficient := 1, powers := [(7, 1), (27, 1), (47, 1), (58, 1)] }, { coefficient := -1, powers := [(7, 1), (31, 1), (44, 1), (47, 1)] }, { coefficient := -1, powers := [(7, 1), (34, 1), (40, 1), (47, 1)] }, { coefficient := -1, powers := [(7, 1), (34, 1), (47, 1), (50, 1)] }, { coefficient := 1, powers := [(11, 1), (22, 1), (47, 1), (55, 1)] }, { coefficient := -1, powers := [(11, 1), (27, 1), (47, 1), (55, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1), (47, 1), (50, 1)] }, { coefficient := -1, powers := [(16, 1), (27, 1), (47, 1), (50, 1)] }],
  [{ coefficient := -2, powers := [(4, 1), (13, 1), (31, 1), (56, 1)] }, { coefficient := -2, powers := [(4, 1), (18, 1), (31, 1), (53, 1)] }, { coefficient := 2, powers := [(11, 1), (13, 1), (27, 1), (56, 1)] }, { coefficient := 2, powers := [(11, 1), (18, 1), (27, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (18, 1), (31, 1), (55, 1)] }, { coefficient := 1, powers := [(4, 1), (18, 1), (34, 1), (50, 1)] }, { coefficient := 1, powers := [(7, 1), (18, 1), (22, 1), (58, 1)] }, { coefficient := -1, powers := [(7, 1), (18, 1), (27, 1), (58, 1)] }, { coefficient := -1, powers := [(7, 1), (18, 1), (31, 1), (44, 1)] }, { coefficient := -1, powers := [(7, 1), (18, 1), (34, 1), (40, 1)] }, { coefficient := 1, powers := [(11, 1), (18, 1), (22, 1), (55, 1)] }, { coefficient := -1, powers := [(11, 1), (18, 1), (27, 1), (55, 1)] }, { coefficient := 1, powers := [(11, 1), (18, 1), (34, 1), (37, 1)] }, { coefficient := 1, powers := [(16, 1), (18, 1), (22, 1), (50, 1)] }, { coefficient := -1, powers := [(16, 1), (18, 1), (27, 1), (50, 1)] }, { coefficient := 1, powers := [(16, 1), (18, 1), (31, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (13, 1), (31, 1), (55, 1)] }, { coefficient := 1, powers := [(7, 1), (13, 1), (22, 1), (58, 1)] }, { coefficient := -1, powers := [(7, 1), (13, 1), (27, 1), (58, 1)] }, { coefficient := 1, powers := [(7, 1), (13, 1), (31, 1), (44, 1)] }, { coefficient := 1, powers := [(7, 1), (13, 1), (34, 1), (40, 1)] }, { coefficient := 1, powers := [(11, 1), (13, 1), (22, 1), (55, 1)] }, { coefficient := -1, powers := [(11, 1), (13, 1), (27, 1), (55, 1)] }, { coefficient := 1, powers := [(13, 1), (16, 1), (22, 1), (50, 1)] }, { coefficient := -1, powers := [(13, 1), (16, 1), (27, 1), (50, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (29, 1), (34, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (29, 1), (31, 1), (55, 1)] }, { coefficient := 1, powers := [(4, 1), (29, 1), (34, 1), (50, 1)] }, { coefficient := 1, powers := [(7, 1), (22, 1), (29, 1), (58, 1)] }, { coefficient := -1, powers := [(7, 1), (27, 1), (29, 1), (58, 1)] }, { coefficient := 1, powers := [(7, 1), (29, 1), (31, 1), (44, 1)] }, { coefficient := 1, powers := [(7, 1), (29, 1), (34, 1), (40, 1)] }, { coefficient := 1, powers := [(7, 1), (29, 1), (34, 1), (50, 1)] }, { coefficient := 1, powers := [(11, 1), (22, 1), (29, 1), (55, 1)] }, { coefficient := -1, powers := [(11, 1), (27, 1), (29, 1), (55, 1)] }, { coefficient := 1, powers := [(11, 1), (29, 1), (34, 1), (37, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1), (29, 1), (50, 1)] }, { coefficient := -1, powers := [(16, 1), (27, 1), (29, 1), (50, 1)] }, { coefficient := 1, powers := [(16, 1), (29, 1), (31, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (23, 1), (31, 1), (55, 1)] }, { coefficient := 1, powers := [(4, 1), (23, 1), (34, 1), (50, 1)] }, { coefficient := 1, powers := [(7, 1), (22, 1), (23, 1), (58, 1)] }, { coefficient := -1, powers := [(7, 1), (23, 1), (27, 1), (58, 1)] }, { coefficient := 1, powers := [(7, 1), (23, 1), (31, 1), (44, 1)] }, { coefficient := 1, powers := [(7, 1), (23, 1), (34, 1), (40, 1)] }, { coefficient := 1, powers := [(11, 1), (22, 1), (23, 1), (55, 1)] }, { coefficient := -1, powers := [(11, 1), (23, 1), (27, 1), (55, 1)] }, { coefficient := 1, powers := [(11, 1), (23, 1), (34, 1), (37, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1), (23, 1), (50, 1)] }, { coefficient := -1, powers := [(16, 1), (23, 1), (27, 1), (50, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1), (31, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (27, 1), (32, 1), (50, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (27, 1), (32, 1), (50, 1), (61, 1)] }, { coefficient := 1, powers := [(7, 1), (27, 1), (32, 1), (50, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (27, 1), (32, 1), (50, 1), (56, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (31, 1), (56, 1)] }, { coefficient := -1, powers := [(11, 1), (27, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(27, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (34, 1), (50, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(4, 1), (31, 1), (55, 1)] }, { coefficient := -1, powers := [(4, 1), (34, 1), (50, 1)] }, { coefficient := -1, powers := [(7, 1), (22, 1), (58, 1)] }, { coefficient := 1, powers := [(7, 1), (27, 1), (58, 1)] }, { coefficient := -1, powers := [(7, 1), (31, 1), (44, 1)] }, { coefficient := -1, powers := [(7, 1), (34, 1), (40, 1)] }, { coefficient := -1, powers := [(11, 1), (22, 1), (55, 1)] }, { coefficient := 1, powers := [(11, 1), (27, 1), (55, 1)] }, { coefficient := -1, powers := [(11, 1), (34, 1), (37, 1)] }, { coefficient := -1, powers := [(16, 1), (22, 1), (50, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1), (50, 1)] }, { coefficient := -1, powers := [(16, 1), (31, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(37, 1), (58, 1)] }, { coefficient := 1, powers := [(40, 1), (55, 1)] }, { coefficient := 1, powers := [(44, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (31, 1), (38, 1), (55, 1), (59, 1)] }, { coefficient := -2, powers := [(4, 1), (31, 1), (46, 1), (51, 1), (56, 1)] }, { coefficient := -1, powers := [(4, 1), (31, 1), (47, 1), (53, 1), (55, 1)] }, { coefficient := 1, powers := [(4, 1), (34, 1), (38, 1), (50, 1), (59, 1)] }, { coefficient := 1, powers := [(4, 1), (34, 1), (41, 1), (50, 1), (56, 1)] }, { coefficient := 1, powers := [(4, 1), (34, 1), (47, 1), (50, 1), (53, 1)] }, { coefficient := 1, powers := [(7, 1), (22, 1), (38, 1), (58, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (22, 1), (41, 1), (56, 1), (58, 1)] }, { coefficient := 3, powers := [(7, 1), (22, 1), (47, 1), (53, 1), (58, 1)] }, { coefficient := -1, powers := [(7, 1), (27, 1), (38, 1), (58, 1), (59, 1)] }, { coefficient := -1, powers := [(7, 1), (27, 1), (41, 1), (56, 1), (58, 1)] }, { coefficient := -3, powers := [(7, 1), (27, 1), (47, 1), (53, 1), (58, 1)] }, { coefficient := 1, powers := [(7, 1), (31, 1), (38, 1), (44, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (31, 1), (41, 1), (44, 1), (56, 1)] }, { coefficient := 1, powers := [(7, 1), (31, 1), (44, 1), (47, 1), (53, 1)] }, { coefficient := 1, powers := [(7, 1), (34, 1), (38, 1), (40, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (34, 1), (40, 1), (41, 1), (56, 1)] }, { coefficient := 1, powers := [(7, 1), (34, 1), (40, 1), (47, 1), (53, 1)] }, { coefficient := 1, powers := [(7, 1), (34, 1), (47, 1), (50, 1), (53, 1)] }, { coefficient := 1, powers := [(11, 1), (22, 1), (38, 1), (55, 1), (59, 1)] }, { coefficient := 1, powers := [(11, 1), (22, 1), (41, 1), (55, 1), (56, 1)] }, { coefficient := -1, powers := [(11, 1), (22, 1), (47, 1), (53, 1), (55, 1)] }, { coefficient := -1, powers := [(11, 1), (27, 1), (38, 1), (55, 1), (59, 1)] }, { coefficient := 2, powers := [(11, 1), (27, 1), (46, 1), (51, 1), (56, 1)] }, { coefficient := 1, powers := [(11, 1), (27, 1), (47, 1), (53, 1), (55, 1)] }, { coefficient := 1, powers := [(11, 1), (34, 1), (37, 1), (38, 1), (59, 1)] }, { coefficient := 1, powers := [(11, 1), (34, 1), (37, 1), (41, 1), (56, 1)] }, { coefficient := 2, powers := [(11, 1), (34, 1), (37, 1), (47, 1), (53, 1)] }, { coefficient := -1, powers := [(11, 1), (34, 1), (38, 1), (45, 1), (51, 1)] }, { coefficient := 2, powers := [(12, 1), (31, 1), (38, 1), (44, 1), (45, 1)] }, { coefficient := 2, powers := [(12, 1), (34, 1), (38, 1), (40, 1), (45, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1), (38, 1), (50, 1), (59, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1), (41, 1), (50, 1), (56, 1)] }, { coefficient := -1, powers := [(16, 1), (22, 1), (47, 1), (50, 1), (53, 1)] }, { coefficient := -1, powers := [(16, 1), (27, 1), (38, 1), (50, 1), (59, 1)] }, { coefficient := -1, powers := [(16, 1), (27, 1), (41, 1), (50, 1), (56, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1), (47, 1), (50, 1), (53, 1)] }, { coefficient := 1, powers := [(16, 1), (31, 1), (37, 1), (38, 1), (59, 1)] }, { coefficient := 1, powers := [(16, 1), (31, 1), (37, 1), (41, 1), (56, 1)] }, { coefficient := 2, powers := [(16, 1), (31, 1), (37, 1), (47, 1), (53, 1)] }, { coefficient := -1, powers := [(16, 1), (31, 1), (38, 1), (45, 1), (51, 1)] }, { coefficient := 1, powers := [(17, 1), (34, 1), (38, 1), (50, 1), (51, 1)] }],
  [{ coefficient := -2, powers := [(4, 1), (18, 1), (23, 1), (31, 1), (50, 1), (53, 1)] }, { coefficient := -1, powers := [(4, 1), (18, 1), (27, 1), (30, 1), (32, 1), (38, 1), (50, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (16, 1), (27, 1), (32, 1), (50, 1), (56, 1)] }, { coefficient := -1, powers := [(5, 1), (17, 1), (25, 1), (27, 1), (32, 1), (48, 1), (50, 2), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (17, 1), (25, 1), (27, 1), (32, 1), (49, 1), (50, 1), (61, 1)] }, { coefficient := 1, powers := [(7, 1), (18, 1), (27, 1), (30, 1), (32, 1), (38, 1), (50, 1), (61, 1)] }, { coefficient := 2, powers := [(11, 1), (18, 1), (23, 1), (27, 1), (50, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (8, 1), (31, 1), (35, 1), (55, 1)] }, { coefficient := 1, powers := [(4, 1), (8, 1), (34, 1), (35, 1), (50, 1)] }, { coefficient := -1, powers := [(4, 1), (18, 1), (29, 1), (31, 1), (55, 1)] }, { coefficient := -1, powers := [(4, 1), (18, 1), (29, 1), (34, 1), (50, 1)] }, { coefficient := 1, powers := [(7, 1), (8, 1), (22, 1), (35, 1), (58, 1)] }, { coefficient := -1, powers := [(7, 1), (8, 1), (27, 1), (35, 1), (58, 1)] }, { coefficient := 1, powers := [(7, 1), (8, 1), (31, 1), (35, 1), (44, 1)] }, { coefficient := 1, powers := [(7, 1), (8, 1), (34, 1), (35, 1), (40, 1)] }, { coefficient := -1, powers := [(7, 1), (18, 1), (22, 1), (29, 1), (58, 1)] }, { coefficient := 1, powers := [(7, 1), (18, 1), (27, 1), (29, 1), (58, 1)] }, { coefficient := 1, powers := [(7, 1), (18, 1), (29, 1), (31, 1), (44, 1)] }, { coefficient := 1, powers := [(7, 1), (18, 1), (29, 1), (34, 1), (40, 1)] }, { coefficient := -1, powers := [(7, 1), (18, 1), (29, 1), (34, 1), (50, 1)] }, { coefficient := 1, powers := [(8, 1), (11, 1), (22, 1), (35, 1), (55, 1)] }, { coefficient := -1, powers := [(8, 1), (11, 1), (27, 1), (35, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (11, 1), (34, 1), (35, 1), (37, 1)] }, { coefficient := 1, powers := [(8, 1), (16, 1), (22, 1), (35, 1), (50, 1)] }, { coefficient := -1, powers := [(8, 1), (16, 1), (27, 1), (35, 1), (50, 1)] }, { coefficient := 1, powers := [(8, 1), (16, 1), (31, 1), (35, 1), (37, 1)] }, { coefficient := -1, powers := [(11, 1), (18, 1), (22, 1), (29, 1), (55, 1)] }, { coefficient := 1, powers := [(11, 1), (18, 1), (27, 1), (29, 1), (55, 1)] }, { coefficient := -1, powers := [(11, 1), (18, 1), (29, 1), (34, 1), (37, 1)] }, { coefficient := -1, powers := [(16, 1), (18, 1), (22, 1), (29, 1), (50, 1)] }, { coefficient := 1, powers := [(16, 1), (18, 1), (27, 1), (29, 1), (50, 1)] }, { coefficient := -1, powers := [(16, 1), (18, 1), (29, 1), (31, 1), (37, 1)] }]
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
    ¬ ∀ index : Fin 57,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component52.SelectedLeafB4_6.selectedHasNoCommonZero

end Krenn.Component52.SelectedLeafB4_6
