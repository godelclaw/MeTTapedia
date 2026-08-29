import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component62.SelectedLeafB0_3_0

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "e4935079619c6630ecb7695bfa360cd24e7c0c3345c2d8be1db4884b5a5e05ef"
def certificateSHA256 : String := "fd62f0ea03d3f639e6d6735c28772380362122003cf083fadd26ebb3b42cd295"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 38 → Fin 667 := ![
  18,
  21,
  158,
  295,
  301,
  311,
  315,
  408,
  437,
  454,
  457,
  459,
  460,
  466,
  469,
  470,
  473,
  477,
  478,
  479,
  480,
  515,
  557,
  558,
  600,
  601,
  610,
  612,
  648,
  655,
  657,
  658,
  660,
  661,
  663,
  664,
  665,
  666
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 38 → SparsePoly (Fin 62) := ![
  [{ coefficient := 1, powers := [(22, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (50, 1)] }, { coefficient := 1, powers := [(22, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (48, 1)] }, { coefficient := 1, powers := [(18, 1), (48, 1)] }, { coefficient := 1, powers := [(23, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (46, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (44, 1)] }, { coefficient := 1, powers := [(17, 1), (38, 1)] }, { coefficient := 1, powers := [(17, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1), (48, 1)] }, { coefficient := 1, powers := [(23, 1), (43, 1), (48, 1)] }, { coefficient := 1, powers := [(48, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (23, 1), (44, 1)] }, { coefficient := 1, powers := [(17, 1), (23, 1), (38, 1)] }, { coefficient := 1, powers := [(17, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (51, 1)] }, { coefficient := 1, powers := [(18, 1), (48, 1), (55, 1)] }, { coefficient := 1, powers := [(18, 1), (51, 1)] }, { coefficient := 1, powers := [(48, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (53, 1)] }, { coefficient := 1, powers := [(27, 1), (39, 1)] }, { coefficient := 1, powers := [(27, 1), (45, 1), (48, 1)] }, { coefficient := 1, powers := [(30, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (35, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (44, 1), (51, 1)] }, { coefficient := 1, powers := [(41, 1), (51, 1)] }, { coefficient := 1, powers := [(44, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (40, 1), (50, 1)] }, { coefficient := 1, powers := [(3, 1), (31, 1), (50, 1)] }, { coefficient := 1, powers := [(13, 1), (18, 1), (50, 1)] }, { coefficient := 1, powers := [(40, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (40, 1), (51, 1)] }, { coefficient := 1, powers := [(3, 1), (31, 1), (51, 1)] }, { coefficient := 1, powers := [(13, 1), (18, 1), (51, 1)] }, { coefficient := 1, powers := [(40, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1), (48, 1)] }, { coefficient := 1, powers := [(13, 1), (48, 1)] }, { coefficient := 1, powers := [(23, 1), (42, 1), (48, 1)] }, { coefficient := 1, powers := [(48, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1), (47, 1)] }, { coefficient := 1, powers := [(6, 1), (28, 1), (43, 1)] }, { coefficient := 1, powers := [(9, 1), (23, 1), (43, 1)] }, { coefficient := 1, powers := [(47, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1), (51, 1)] }, { coefficient := 1, powers := [(43, 1), (48, 1)] }, { coefficient := 1, powers := [(48, 1), (55, 1)] }, { coefficient := 1, powers := [(51, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1), (48, 1)] }, { coefficient := 1, powers := [(6, 1), (59, 1)] }, { coefficient := 1, powers := [(23, 1), (44, 1), (48, 1)] }, { coefficient := 1, powers := [(41, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1), (47, 1)] }, { coefficient := 1, powers := [(6, 1), (28, 1), (45, 1)] }, { coefficient := 1, powers := [(9, 1), (23, 1), (45, 1)] }, { coefficient := 1, powers := [(19, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1), (48, 1)] }, { coefficient := 1, powers := [(19, 1), (48, 1)] }, { coefficient := 1, powers := [(23, 1), (39, 1)] }, { coefficient := 1, powers := [(23, 1), (45, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1), (49, 1)] }, { coefficient := 1, powers := [(9, 1), (19, 1), (55, 1)] }, { coefficient := 1, powers := [(9, 1), (45, 1)] }, { coefficient := 1, powers := [(19, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1), (50, 1)] }, { coefficient := 1, powers := [(19, 1), (50, 1)] }, { coefficient := 1, powers := [(19, 1), (55, 1)] }, { coefficient := 1, powers := [(45, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (22, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (30, 1), (46, 1)] }, { coefficient := 1, powers := [(6, 1), (33, 1), (39, 1)] }, { coefficient := 1, powers := [(22, 1), (41, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (41, 1), (52, 1)] }, { coefficient := 1, powers := [(22, 1), (56, 1)] }, { coefficient := 1, powers := [(27, 1), (46, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (19, 1), (42, 1), (51, 1)] }, { coefficient := 1, powers := [(13, 1), (19, 1), (51, 1)] }, { coefficient := 1, powers := [(13, 1), (39, 1)] }, { coefficient := 1, powers := [(19, 1), (42, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (40, 1)] }, { coefficient := 1, powers := [(3, 1), (31, 1)] }, { coefficient := 1, powers := [(13, 1), (18, 1)] }, { coefficient := 1, powers := [(18, 1), (54, 1)] }, { coefficient := 1, powers := [(23, 1), (40, 1)] }, { coefficient := 1, powers := [(31, 1), (34, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1)] }, { coefficient := 1, powers := [(6, 1), (28, 1)] }, { coefficient := 1, powers := [(9, 1), (23, 1)] }, { coefficient := 1, powers := [(18, 1), (47, 1)] }, { coefficient := 1, powers := [(23, 1), (37, 1)] }, { coefficient := 1, powers := [(28, 1), (34, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (39, 1), (55, 1)] }, { coefficient := 1, powers := [(0, 1), (45, 1), (51, 1)] }, { coefficient := 1, powers := [(19, 1), (48, 1), (55, 1)] }, { coefficient := 1, powers := [(19, 1), (51, 1)] }, { coefficient := 1, powers := [(39, 1)] }, { coefficient := 1, powers := [(45, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (40, 1), (49, 1)] }, { coefficient := 1, powers := [(3, 1), (31, 1), (49, 1)] }, { coefficient := 1, powers := [(3, 1), (57, 1)] }, { coefficient := 1, powers := [(9, 1), (40, 1)] }, { coefficient := 1, powers := [(13, 1), (18, 1), (49, 1)] }, { coefficient := 1, powers := [(13, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (37, 1), (55, 1)] }, { coefficient := 1, powers := [(0, 1), (49, 1)] }, { coefficient := 1, powers := [(3, 1), (28, 1), (55, 1)] }, { coefficient := 1, powers := [(9, 1), (18, 1), (55, 1)] }, { coefficient := 1, powers := [(9, 1)] }, { coefficient := 1, powers := [(18, 1), (49, 1)] }, { coefficient := 1, powers := [(37, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (34, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (37, 1), (54, 1)] }, { coefficient := 1, powers := [(0, 1), (40, 1), (47, 1)] }, { coefficient := 1, powers := [(3, 1), (23, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (28, 1), (54, 1)] }, { coefficient := 1, powers := [(3, 1), (31, 1), (47, 1)] }, { coefficient := 1, powers := [(6, 1), (18, 1), (57, 1)] }, { coefficient := 1, powers := [(6, 1), (28, 1), (40, 1)] }, { coefficient := 1, powers := [(6, 1), (31, 1), (37, 1)] }, { coefficient := 1, powers := [(9, 1), (18, 1), (54, 1)] }, { coefficient := 1, powers := [(9, 1), (23, 1), (40, 1)] }, { coefficient := 1, powers := [(9, 1), (31, 1), (34, 1)] }, { coefficient := 1, powers := [(13, 1), (18, 1), (47, 1)] }, { coefficient := 1, powers := [(13, 1), (23, 1), (37, 1)] }, { coefficient := 1, powers := [(13, 1), (28, 1), (34, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (36, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (46, 1), (53, 1)] }, { coefficient := 1, powers := [(5, 1), (27, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (53, 1)] }, { coefficient := 1, powers := [(8, 1), (22, 1), (59, 1)] }, { coefficient := 1, powers := [(8, 1), (30, 1), (46, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (39, 1)] }, { coefficient := 1, powers := [(12, 1), (22, 1), (56, 1)] }, { coefficient := 1, powers := [(12, 1), (27, 1), (46, 1)] }, { coefficient := 1, powers := [(12, 1), (33, 1), (36, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (53, 1)] }, { coefficient := 1, powers := [(17, 1), (27, 1), (39, 1)] }, { coefficient := 1, powers := [(17, 1), (30, 1), (36, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1)] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(37, 1)] }],
  [{ coefficient := 1, powers := [(39, 1), (61, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(54, 1)] }],
  [{ coefficient := 1, powers := [(55, 1)] }],
  [{ coefficient := 1, powers := [(56, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 38 → SparsePoly (Fin 62) := ![
  [{ coefficient := 1, powers := [(6, 1), (12, 1), (23, 1), (52, 1), (57, 1)] }, { coefficient := -1, powers := [(6, 1), (12, 1), (28, 1), (40, 1), (52, 1)] }, { coefficient := 1, powers := [(8, 1), (23, 1), (48, 1), (57, 1)] }, { coefficient := -1, powers := [(8, 1), (28, 1), (40, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (17, 1), (23, 1), (45, 1), (57, 1)] }, { coefficient := -1, powers := [(6, 1), (17, 1), (28, 1), (40, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (17, 1), (23, 2), (53, 1), (57, 1)] }, { coefficient := -1, powers := [(6, 1), (17, 1), (23, 1), (28, 1), (40, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (45, 1), (57, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (23, 1), (27, 1), (44, 1), (57, 1)] }, { coefficient := -1, powers := [(5, 1), (27, 1), (28, 1), (40, 1), (44, 1)] }, { coefficient := -1, powers := [(6, 1), (45, 1), (57, 1), (61, 1)] }, { coefficient := 1, powers := [(9, 1), (40, 1), (45, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (23, 1), (53, 1), (57, 1)] }, { coefficient := 1, powers := [(6, 1), (28, 1), (40, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (22, 1), (23, 2), (53, 1), (57, 1)] }, { coefficient := 1, powers := [(6, 1), (22, 1), (23, 1), (28, 1), (40, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (19, 1), (28, 1), (42, 1), (61, 1)] }, { coefficient := 1, powers := [(9, 1), (19, 1), (23, 1), (42, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (22, 1), (23, 1), (53, 1), (57, 1)] }, { coefficient := -1, powers := [(6, 1), (22, 1), (28, 1), (40, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (19, 1), (57, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (23, 1), (27, 1), (41, 1), (57, 1)] }, { coefficient := -1, powers := [(5, 1), (27, 1), (28, 1), (40, 1), (41, 1)] }, { coefficient := -1, powers := [(6, 1), (19, 1), (57, 1), (61, 1)] }, { coefficient := 1, powers := [(9, 1), (19, 1), (40, 1), (61, 1)] }, { coefficient := -1, powers := [(19, 1), (23, 1), (40, 1), (49, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (17, 1), (23, 1), (57, 1)] }, { coefficient := 1, powers := [(6, 1), (17, 1), (28, 1), (40, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (18, 1), (23, 1), (27, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (18, 1), (27, 1), (28, 1), (40, 1)] }],
  [{ coefficient := -2, powers := [(19, 1), (23, 1), (48, 1), (49, 1), (61, 1)] }],
  [{ coefficient := 2, powers := [(19, 1), (23, 1), (49, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (19, 1), (28, 1), (43, 1), (61, 1)] }, { coefficient := -1, powers := [(9, 1), (19, 1), (23, 1), (43, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (31, 1), (45, 1), (48, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (19, 1), (31, 1), (47, 1), (61, 1)] }, { coefficient := 1, powers := [(6, 1), (13, 1), (19, 1), (28, 1), (61, 1)] }, { coefficient := 1, powers := [(9, 1), (13, 1), (19, 1), (23, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (23, 1), (27, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (27, 1), (28, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (31, 1), (43, 1), (48, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (57, 1), (61, 1)] }, { coefficient := 1, powers := [(6, 1), (57, 1), (61, 1)] }, { coefficient := -1, powers := [(9, 1), (40, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (40, 1), (48, 1), (61, 1)] }],
  [{ coefficient := -2, powers := [(3, 1), (23, 1), (48, 1), (57, 1), (61, 1)] }, { coefficient := -2, powers := [(9, 1), (23, 1), (40, 1), (48, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (23, 1), (57, 1)] }, { coefficient := 1, powers := [(8, 1), (28, 1), (40, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (12, 1), (23, 1), (57, 1)] }, { coefficient := 1, powers := [(6, 1), (12, 1), (28, 1), (40, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (28, 1), (61, 1)] }, { coefficient := -1, powers := [(9, 1), (23, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(9, 1)] }],
  [{ coefficient := 1, powers := [(13, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (18, 1), (57, 1), (61, 1)] }, { coefficient := 2, powers := [(3, 1), (23, 1), (57, 1), (61, 1)] }, { coefficient := 1, powers := [(3, 1), (31, 1), (47, 1), (61, 1)] }, { coefficient := 1, powers := [(6, 1), (18, 1), (57, 1), (61, 1)] }, { coefficient := -1, powers := [(9, 1), (18, 1), (40, 1), (61, 1)] }, { coefficient := 1, powers := [(9, 1), (23, 1), (40, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(18, 1)] }, { coefficient := 2, powers := [(19, 1), (23, 1), (48, 1), (50, 1), (61, 1)] }, { coefficient := -2, powers := [(19, 1), (23, 1), (51, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (31, 1)] }, { coefficient := -1, powers := [(13, 1), (18, 1)] }, { coefficient := 1, powers := [(19, 1), (23, 1), (40, 1), (51, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(6, 1), (23, 1), (57, 1)] }, { coefficient := -1, powers := [(6, 1), (28, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (18, 1), (39, 1), (55, 1), (57, 1), (61, 1)] }, { coefficient := 1, powers := [(3, 1), (18, 1), (45, 1), (51, 1), (57, 1), (61, 1)] }, { coefficient := 1, powers := [(3, 1), (19, 1), (31, 1), (43, 1), (47, 1), (51, 1), (61, 1)] }, { coefficient := -1, powers := [(3, 1), (19, 1), (51, 1), (57, 1), (61, 1)] }, { coefficient := -2, powers := [(3, 1), (23, 1), (39, 1), (55, 1), (57, 1), (61, 1)] }, { coefficient := 2, powers := [(3, 1), (23, 1), (45, 1), (48, 1), (50, 1), (57, 1), (61, 1)] }, { coefficient := -2, powers := [(3, 1), (23, 1), (45, 1), (51, 1), (57, 1), (61, 1)] }, { coefficient := 1, powers := [(3, 1), (31, 1), (37, 1), (55, 1)] }, { coefficient := -1, powers := [(3, 1), (31, 1), (39, 1), (47, 1), (55, 1), (61, 1)] }, { coefficient := -1, powers := [(3, 1), (31, 1), (45, 1), (47, 1), (51, 1), (61, 1)] }, { coefficient := 1, powers := [(3, 1), (31, 1), (49, 1)] }, { coefficient := 1, powers := [(5, 1), (18, 1), (23, 1), (27, 1), (35, 1), (57, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (18, 1), (23, 1), (27, 1), (44, 1), (51, 1), (57, 1)] }, { coefficient := -1, powers := [(5, 1), (18, 1), (27, 1), (28, 1), (35, 1), (40, 1), (59, 1)] }, { coefficient := -1, powers := [(5, 1), (18, 1), (27, 1), (28, 1), (40, 1), (44, 1), (51, 1)] }, { coefficient := -1, powers := [(5, 1), (23, 1), (27, 1), (41, 1), (51, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (27, 1), (28, 1), (40, 1), (41, 1), (51, 1)] }, { coefficient := -1, powers := [(6, 1), (13, 1), (19, 1), (28, 1), (43, 1), (51, 1), (61, 1)] }, { coefficient := -1, powers := [(6, 1), (18, 1), (39, 1), (55, 1), (57, 1), (61, 1)] }, { coefficient := -1, powers := [(6, 1), (18, 1), (45, 1), (51, 1), (57, 1), (61, 1)] }, { coefficient := 1, powers := [(6, 1), (19, 1), (28, 1), (42, 1), (51, 1), (61, 1)] }, { coefficient := 1, powers := [(6, 1), (19, 1), (51, 1), (57, 1), (61, 1)] }, { coefficient := -1, powers := [(9, 1), (13, 1), (19, 1), (23, 1), (43, 1), (51, 1), (61, 1)] }, { coefficient := 1, powers := [(9, 1), (18, 1), (39, 1), (40, 1), (55, 1), (61, 1)] }, { coefficient := 1, powers := [(9, 1), (18, 1), (40, 1), (45, 1), (51, 1), (61, 1)] }, { coefficient := 1, powers := [(9, 1), (19, 1), (23, 1), (42, 1), (51, 1), (61, 1)] }, { coefficient := -1, powers := [(9, 1), (19, 1), (40, 1), (51, 1), (61, 1)] }, { coefficient := -1, powers := [(9, 1), (23, 1), (39, 1), (40, 1), (55, 1), (61, 1)] }, { coefficient := 2, powers := [(9, 1), (23, 1), (40, 1), (45, 1), (48, 1), (50, 1), (61, 1)] }, { coefficient := -1, powers := [(9, 1), (23, 1), (40, 1), (45, 1), (51, 1), (61, 1)] }, { coefficient := -1, powers := [(9, 1), (40, 1)] }, { coefficient := 1, powers := [(13, 1), (18, 1), (37, 1), (55, 1)] }, { coefficient := 1, powers := [(13, 1), (18, 1), (49, 1)] }, { coefficient := -1, powers := [(13, 1), (47, 1)] }, { coefficient := -1, powers := [(18, 1), (40, 1), (49, 1)] }, { coefficient := -1, powers := [(19, 1), (23, 1), (37, 1), (40, 1), (51, 1), (55, 1), (61, 1)] }, { coefficient := -1, powers := [(23, 1), (40, 1), (45, 1), (48, 1), (49, 1), (61, 1)] }, { coefficient := 1, powers := [(34, 1), (57, 1)] }, { coefficient := 1, powers := [(37, 1), (54, 1)] }, { coefficient := 1, powers := [(40, 1), (47, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (23, 1), (36, 1), (57, 1), (59, 1)] }, { coefficient := -1, powers := [(6, 1), (23, 1), (39, 1), (56, 1), (57, 1)] }, { coefficient := 1, powers := [(6, 1), (28, 1), (36, 1), (40, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (28, 1), (39, 1), (40, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (31, 1)] }, { coefficient := 1, powers := [(6, 1), (31, 1)] }, { coefficient := -2, powers := [(13, 1), (19, 1), (23, 1), (48, 1), (50, 1), (61, 1)] }, { coefficient := 2, powers := [(13, 1), (19, 1), (23, 1), (51, 1), (61, 1)] }, { coefficient := -1, powers := [(19, 1), (23, 1), (40, 1), (51, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (18, 1), (57, 1)] }, { coefficient := -1, powers := [(3, 1), (23, 1), (57, 1)] }, { coefficient := -1, powers := [(3, 1), (31, 1), (47, 1)] }, { coefficient := 1, powers := [(6, 1), (13, 1), (28, 1)] }, { coefficient := -1, powers := [(6, 1), (18, 1), (57, 1)] }, { coefficient := -1, powers := [(6, 1), (23, 1), (57, 1)] }, { coefficient := 1, powers := [(9, 1), (13, 1), (23, 1)] }, { coefficient := 1, powers := [(9, 1), (18, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (28, 1)] }, { coefficient := 1, powers := [(6, 1), (19, 1), (28, 1), (43, 1), (48, 1), (61, 1)] }, { coefficient := 1, powers := [(9, 1), (19, 1), (23, 1), (43, 1), (48, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(3, 2), (28, 1), (31, 1)] }, { coefficient := 1, powers := [(3, 1), (9, 1), (18, 1), (31, 1)] }, { coefficient := 1, powers := [(3, 1), (13, 1), (18, 1), (28, 1)] }, { coefficient := -1, powers := [(3, 1), (19, 1), (23, 1), (28, 1), (40, 1), (51, 1), (61, 1)] }, { coefficient := -1, powers := [(5, 1), (18, 1), (23, 1), (27, 1), (41, 1), (48, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (18, 1), (27, 1), (28, 1), (40, 1), (41, 1), (48, 1)] }, { coefficient := -1, powers := [(6, 1), (13, 1), (19, 1), (28, 1), (48, 1), (61, 1)] }, { coefficient := -1, powers := [(6, 1), (17, 1), (22, 1), (23, 2), (53, 1), (57, 1)] }, { coefficient := 1, powers := [(6, 1), (17, 1), (22, 1), (23, 1), (28, 1), (40, 1), (53, 1)] }, { coefficient := 1, powers := [(9, 1), (13, 1), (18, 2)] }, { coefficient := -1, powers := [(9, 1), (13, 1), (19, 1), (23, 1), (48, 1), (61, 1)] }, { coefficient := -1, powers := [(9, 1), (18, 1), (19, 1), (23, 1), (40, 1), (51, 1), (61, 1)] }, { coefficient := 1, powers := [(18, 1), (19, 1), (23, 1), (40, 1), (48, 1), (49, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (6, 1), (23, 1), (30, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (6, 1), (28, 1), (30, 1), (40, 1)] }]
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
    ¬ ∀ index : Fin 38,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component62.SelectedLeafB0_3_0.selectedHasNoCommonZero

end Krenn.Component62.SelectedLeafB0_3_0
