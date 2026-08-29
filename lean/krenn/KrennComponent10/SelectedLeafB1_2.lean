import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component10.SelectedLeafB1_2

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "ed1ed4e7887fbffa29296dca61672275bddddde5bafb2bb3e414c862375b5aa2"
def certificateSHA256 : String := "f29d023ee73ec90ca726df6a5d1376d1842fa7952df98e59e84e58fa08c52eb6"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 51 → Fin 641 := ![
  0,
  2,
  8,
  9,
  10,
  11,
  20,
  22,
  55,
  168,
  180,
  184,
  188,
  189,
  196,
  197,
  202,
  230,
  284,
  290,
  348,
  349,
  350,
  356,
  359,
  397,
  431,
  442,
  449,
  460,
  464,
  467,
  471,
  473,
  476,
  491,
  502,
  519,
  550,
  556,
  557,
  576,
  577,
  582,
  621,
  632,
  634,
  635,
  638,
  639,
  640
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 51 → SparsePoly (Fin 62) := ![
  [{ coefficient := 1, powers := [(3, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (32, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (32, 1)] }, { coefficient := 1, powers := [(32, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (45, 1)] }, { coefficient := 1, powers := [(12, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (19, 1)] }, { coefficient := 1, powers := [(17, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (46, 1)] }, { coefficient := -1, powers := [(28, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (43, 1)] }, { coefficient := 1, powers := [(27, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1), (52, 1)] }, { coefficient := 1, powers := [(52, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1), (53, 1)] }, { coefficient := 1, powers := [(53, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (48, 1), (51, 1)] }, { coefficient := 1, powers := [(48, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (28, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (32, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (19, 1), (55, 1)] }, { coefficient := 1, powers := [(12, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (24, 1), (44, 1)] }, { coefficient := 1, powers := [(12, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (49, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (49, 1)] }, { coefficient := 1, powers := [(17, 1), (27, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (59, 1)] }, { coefficient := 1, powers := [(12, 1), (48, 1)] }, { coefficient := 1, powers := [(18, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (59, 1)] }, { coefficient := 1, powers := [(12, 1), (56, 1)] }, { coefficient := 1, powers := [(18, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (46, 1)] }, { coefficient := 1, powers := [(18, 1), (40, 1)] }, { coefficient := 1, powers := [(18, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (53, 1)] }, { coefficient := 1, powers := [(29, 1), (41, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (35, 1), (51, 1)] }, { coefficient := 1, powers := [(22, 1), (43, 1), (51, 1)] }, { coefficient := 1, powers := [(28, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (19, 1), (54, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (42, 1)] }, { coefficient := 1, powers := [(12, 1), (33, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (19, 1), (51, 1)] }, { coefficient := 1, powers := [(17, 1), (19, 1), (55, 1)] }, { coefficient := 1, powers := [(17, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (19, 1), (49, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (39, 1)] }, { coefficient := 1, powers := [(18, 1), (30, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (45, 1)] }, { coefficient := 1, powers := [(17, 1), (27, 1), (40, 1)] }, { coefficient := 1, powers := [(17, 1), (27, 1), (45, 1)] }, { coefficient := 1, powers := [(17, 1), (28, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (51, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (51, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (55, 1)] }, { coefficient := 1, powers := [(17, 1), (28, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (35, 1)] }, { coefficient := 1, powers := [(22, 1), (43, 1)] }, { coefficient := 1, powers := [(27, 1), (43, 1)] }, { coefficient := 1, powers := [(35, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (40, 1)] }, { coefficient := 1, powers := [(17, 1), (45, 1)] }, { coefficient := 1, powers := [(17, 1), (51, 1)] }, { coefficient := 1, powers := [(17, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (40, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(43, 1), (52, 1)] }, { coefficient := 1, powers := [(56, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1), (49, 1)] }, { coefficient := 1, powers := [(6, 1), (30, 1), (45, 1)] }, { coefficient := 1, powers := [(9, 1), (24, 1), (45, 1)] }, { coefficient := 1, powers := [(49, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (36, 1), (59, 1)] }, { coefficient := 1, powers := [(12, 1), (27, 1), (43, 1)] }, { coefficient := 1, powers := [(12, 1), (35, 1), (36, 1)] }, { coefficient := 1, powers := [(18, 1), (32, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (28, 1), (58, 1)] }, { coefficient := 1, powers := [(22, 1), (51, 1)] }, { coefficient := 1, powers := [(22, 1), (55, 1)] }, { coefficient := 1, powers := [(28, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (28, 1), (58, 1)] }, { coefficient := 1, powers := [(27, 1), (40, 1)] }, { coefficient := 1, powers := [(27, 1), (45, 1)] }, { coefficient := 1, powers := [(28, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (43, 1), (52, 1)] }, { coefficient := 1, powers := [(23, 1), (56, 1)] }, { coefficient := 1, powers := [(29, 1), (48, 1)] }, { coefficient := 1, powers := [(35, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1)] }, { coefficient := 1, powers := [(6, 1), (58, 1)] }, { coefficient := 1, powers := [(24, 1), (40, 1)] }, { coefficient := 1, powers := [(24, 1), (45, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (51, 1)] }, { coefficient := 1, powers := [(3, 1), (58, 1)] }, { coefficient := 1, powers := [(19, 1), (51, 1)] }, { coefficient := 1, powers := [(19, 1), (55, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1)] }, { coefficient := 1, powers := [(3, 1), (33, 1)] }, { coefficient := 1, powers := [(13, 1), (19, 1)] }, { coefficient := 1, powers := [(19, 1), (54, 1)] }, { coefficient := 1, powers := [(24, 1), (42, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (49, 1)] }, { coefficient := 1, powers := [(6, 1), (30, 1)] }, { coefficient := 1, powers := [(9, 1), (24, 1)] }, { coefficient := 1, powers := [(19, 1), (49, 1)] }, { coefficient := 1, powers := [(24, 1), (39, 1)] }, { coefficient := 1, powers := [(30, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (36, 1), (58, 1)] }, { coefficient := 1, powers := [(0, 1)] }, { coefficient := 1, powers := [(3, 1), (24, 1), (58, 1)] }, { coefficient := 1, powers := [(6, 1), (19, 1), (58, 1)] }, { coefficient := 1, powers := [(19, 1)] }, { coefficient := 1, powers := [(24, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (39, 1), (55, 1)] }, { coefficient := 1, powers := [(0, 1), (50, 1)] }, { coefficient := 1, powers := [(3, 1), (30, 1), (55, 1)] }, { coefficient := 1, powers := [(9, 1), (19, 1), (55, 1)] }, { coefficient := 1, powers := [(9, 1)] }, { coefficient := 1, powers := [(19, 1), (50, 1)] }, { coefficient := 1, powers := [(39, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (36, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (39, 1), (54, 1)] }, { coefficient := 1, powers := [(0, 1), (42, 1), (49, 1)] }, { coefficient := 1, powers := [(3, 1), (24, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (30, 1), (54, 1)] }, { coefficient := 1, powers := [(3, 1), (33, 1), (49, 1)] }, { coefficient := 1, powers := [(6, 1), (19, 1), (57, 1)] }, { coefficient := 1, powers := [(6, 1), (30, 1), (42, 1)] }, { coefficient := 1, powers := [(6, 1), (33, 1), (39, 1)] }, { coefficient := 1, powers := [(9, 1), (19, 1), (54, 1)] }, { coefficient := 1, powers := [(9, 1), (24, 1), (42, 1)] }, { coefficient := 1, powers := [(9, 1), (33, 1), (36, 1)] }, { coefficient := 1, powers := [(13, 1), (19, 1), (49, 1)] }, { coefficient := 1, powers := [(13, 1), (24, 1), (39, 1)] }, { coefficient := 1, powers := [(13, 1), (30, 1), (36, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (41, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (48, 1), (53, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (53, 1)] }, { coefficient := 1, powers := [(8, 1), (23, 1), (59, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (48, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(12, 1), (23, 1), (56, 1)] }, { coefficient := 1, powers := [(12, 1), (29, 1), (48, 1)] }, { coefficient := 1, powers := [(12, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (53, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (41, 1)] }, { coefficient := 1, powers := [(18, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1)] }],
  [{ coefficient := 1, powers := [(39, 1)] }],
  [{ coefficient := 1, powers := [(40, 1), (61, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(41, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 51 → SparsePoly (Fin 62) := ![
  [{ coefficient := -1, powers := [(2, 1), (9, 1), (24, 1), (38, 1), (54, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (24, 1), (38, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (30, 1), (38, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (9, 1), (19, 1), (38, 1), (54, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (19, 1), (38, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (30, 1), (38, 1), (54, 1)] }, { coefficient := 1, powers := [(9, 1), (17, 1), (28, 1), (33, 1), (38, 1), (61, 1)] }, { coefficient := -1, powers := [(17, 1), (28, 1), (30, 1), (38, 1), (42, 1), (61, 1)] }, { coefficient := 2, powers := [(17, 1), (28, 1), (30, 1), (38, 1), (54, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (19, 1), (35, 1), (38, 1), (55, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (35, 1), (38, 1), (57, 1)] }, { coefficient := 1, powers := [(9, 1), (19, 2), (35, 1), (38, 1), (44, 1), (55, 1)] }, { coefficient := 1, powers := [(9, 1), (19, 1), (35, 1), (38, 1), (44, 1)] }, { coefficient := -1, powers := [(19, 2), (35, 1), (38, 1), (44, 1), (49, 1), (55, 1)] }, { coefficient := 1, powers := [(19, 2), (35, 1), (38, 1), (44, 1), (50, 1)] }, { coefficient := -1, powers := [(19, 1), (35, 1), (38, 1), (44, 1), (49, 1)] }],
  [{ coefficient := -1, powers := [(9, 1), (19, 1), (24, 1), (35, 1), (38, 1), (55, 1)] }, { coefficient := -1, powers := [(9, 1), (24, 1), (35, 1), (38, 1)] }, { coefficient := -1, powers := [(19, 2), (35, 1), (38, 1), (49, 1), (55, 1)] }, { coefficient := -1, powers := [(19, 1), (30, 1), (35, 1), (36, 1), (38, 1), (55, 1)] }, { coefficient := -1, powers := [(19, 1), (35, 1), (38, 1), (49, 1)] }, { coefficient := -1, powers := [(30, 1), (35, 1), (36, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (19, 1), (27, 1), (33, 1), (38, 1), (45, 1)] }, { coefficient := -1, powers := [(9, 1), (27, 1), (33, 1), (38, 1)] }, { coefficient := -1, powers := [(13, 1), (27, 1), (30, 1), (38, 1)] }, { coefficient := -1, powers := [(19, 1), (27, 1), (30, 1), (38, 1), (42, 1), (45, 1)] }, { coefficient := 2, powers := [(19, 1), (27, 1), (30, 1), (38, 1), (45, 1), (54, 1)] }, { coefficient := -1, powers := [(22, 1), (30, 1), (38, 1), (54, 1)] }, { coefficient := 1, powers := [(27, 1), (30, 1), (38, 1), (42, 1)] }, { coefficient := -2, powers := [(27, 1), (30, 1), (38, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(9, 1), (22, 1), (33, 1), (38, 1), (61, 1)] }, { coefficient := 1, powers := [(22, 1), (30, 1), (38, 1), (42, 1), (61, 1)] }, { coefficient := -2, powers := [(22, 1), (30, 1), (38, 1), (54, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (22, 1), (38, 1), (42, 1), (59, 1)] }, { coefficient := 1, powers := [(22, 1), (24, 1), (38, 1), (42, 1), (59, 1)] }, { coefficient := 1, powers := [(22, 1), (33, 1), (36, 1), (38, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (19, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [(19, 1), (32, 1), (38, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(9, 1), (18, 1), (19, 1), (33, 1), (38, 1)] }, { coefficient := 1, powers := [(18, 1), (19, 1), (30, 1), (38, 1), (42, 1)] }, { coefficient := -2, powers := [(18, 1), (19, 1), (30, 1), (38, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (17, 1), (33, 1), (38, 1), (46, 1), (61, 1)] }, { coefficient := 1, powers := [(9, 1), (18, 1), (19, 1), (33, 1), (38, 1), (45, 1)] }, { coefficient := -1, powers := [(17, 1), (30, 1), (38, 1), (42, 1), (46, 1), (61, 1)] }, { coefficient := 2, powers := [(17, 1), (30, 1), (38, 1), (46, 1), (54, 1), (61, 1)] }, { coefficient := -1, powers := [(18, 1), (19, 1), (30, 1), (38, 1), (42, 1), (45, 1)] }, { coefficient := 2, powers := [(18, 1), (19, 1), (30, 1), (38, 1), (45, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (19, 1), (33, 1), (35, 1), (36, 1), (38, 1)] }, { coefficient := 1, powers := [(13, 1), (19, 2), (35, 1), (38, 1), (49, 1)] }, { coefficient := 1, powers := [(13, 1), (19, 1), (30, 1), (35, 1), (36, 1), (38, 1)] }, { coefficient := -1, powers := [(19, 1), (30, 1), (35, 1), (36, 1), (38, 1), (42, 1)] }, { coefficient := 2, powers := [(19, 1), (30, 1), (35, 1), (36, 1), (38, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(9, 1), (19, 1), (28, 1), (33, 1), (36, 1), (38, 1), (40, 1), (59, 1)] }, { coefficient := -1, powers := [(9, 1), (19, 1), (28, 1), (33, 1), (36, 1), (38, 1), (45, 1), (59, 1)] }, { coefficient := 1, powers := [(19, 1), (28, 1), (30, 1), (36, 1), (38, 1), (40, 1), (42, 1), (59, 1)] }, { coefficient := -2, powers := [(19, 1), (28, 1), (30, 1), (36, 1), (38, 1), (40, 1), (54, 1), (59, 1)] }, { coefficient := 1, powers := [(19, 1), (28, 1), (30, 1), (36, 1), (38, 1), (42, 1), (45, 1), (59, 1)] }, { coefficient := -2, powers := [(19, 1), (28, 1), (30, 1), (36, 1), (38, 1), (45, 1), (54, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (12, 1), (33, 1), (38, 1), (61, 1)] }, { coefficient := -1, powers := [(12, 1), (30, 1), (38, 1), (42, 1), (61, 1)] }, { coefficient := 2, powers := [(12, 1), (30, 1), (38, 1), (54, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (32, 1), (43, 1)] }, { coefficient := 1, powers := [(12, 1), (23, 1), (43, 1)] }, { coefficient := 1, powers := [(12, 1), (27, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (48, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1)] }, { coefficient := -1, powers := [(18, 1), (23, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (32, 1)] }, { coefficient := -1, powers := [(12, 1), (29, 1)] }],
  [{ coefficient := -1, powers := [(9, 1), (17, 1), (33, 1), (38, 1), (61, 1)] }, { coefficient := 1, powers := [(17, 1), (30, 1), (38, 1), (42, 1), (61, 1)] }, { coefficient := -2, powers := [(17, 1), (30, 1), (38, 1), (54, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (19, 1), (35, 1), (38, 1), (57, 1)] }, { coefficient := -1, powers := [(9, 1), (33, 1), (35, 1), (36, 1), (38, 1)] }, { coefficient := -1, powers := [(13, 1), (19, 1), (35, 1), (38, 1), (49, 1)] }, { coefficient := -1, powers := [(19, 1), (35, 1), (38, 1), (49, 1), (54, 1)] }, { coefficient := 1, powers := [(30, 1), (35, 1), (36, 1), (38, 1), (42, 1)] }, { coefficient := -2, powers := [(30, 1), (35, 1), (36, 1), (38, 1), (54, 1)] }, { coefficient := -1, powers := [(35, 1), (38, 1)] }],
  [{ coefficient := -1, powers := [(9, 1), (19, 2), (35, 1), (38, 1), (55, 1)] }, { coefficient := -1, powers := [(9, 1), (19, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(19, 2), (35, 1), (38, 1), (49, 1), (55, 1)] }, { coefficient := -1, powers := [(19, 2), (35, 1), (38, 1), (50, 1)] }, { coefficient := 1, powers := [(19, 1), (35, 1), (38, 1), (49, 1)] }],
  [{ coefficient := -1, powers := [(19, 1), (38, 1), (42, 1), (59, 1)] }, { coefficient := -1, powers := [(24, 1), (38, 1), (42, 1), (59, 1)] }, { coefficient := -1, powers := [(33, 1), (36, 1), (38, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(29, 1)] }],
  [{ coefficient := 1, powers := [(23, 1)] }],
  [{ coefficient := -1, powers := [(9, 1), (32, 1), (33, 1), (36, 1), (38, 1), (61, 1)] }, { coefficient := 1, powers := [(30, 1), (32, 1), (36, 1), (38, 1), (42, 1), (61, 1)] }, { coefficient := -2, powers := [(30, 1), (32, 1), (36, 1), (38, 1), (54, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(18, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (12, 1), (33, 1), (38, 1), (61, 1)] }, { coefficient := -1, powers := [(12, 1), (30, 1), (38, 1), (42, 1), (61, 1)] }, { coefficient := 2, powers := [(12, 1), (30, 1), (38, 1), (54, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (19, 1), (35, 1), (38, 1), (55, 1)] }, { coefficient := 1, powers := [(9, 1), (35, 1), (38, 1)] }, { coefficient := -1, powers := [(19, 1), (35, 1), (38, 1), (49, 1), (55, 1)] }, { coefficient := -1, powers := [(35, 1), (38, 1), (49, 1)] }],
  [{ coefficient := -1, powers := [(9, 1), (19, 1), (28, 1), (33, 1), (36, 1), (38, 1), (59, 1)] }, { coefficient := 1, powers := [(9, 1), (28, 1), (33, 1), (36, 1), (38, 1), (59, 1), (61, 1)] }, { coefficient := 1, powers := [(19, 1), (28, 1), (30, 1), (36, 1), (38, 1), (42, 1), (59, 1)] }, { coefficient := -2, powers := [(19, 1), (28, 1), (30, 1), (36, 1), (38, 1), (54, 1), (59, 1)] }, { coefficient := -1, powers := [(28, 1), (30, 1), (36, 1), (38, 1), (42, 1), (59, 1), (61, 1)] }, { coefficient := 2, powers := [(28, 1), (30, 1), (36, 1), (38, 1), (54, 1), (59, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(13, 1), (32, 1), (38, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (19, 1), (33, 1), (36, 1), (38, 1), (59, 1)] }, { coefficient := -1, powers := [(19, 1), (30, 1), (36, 1), (38, 1), (42, 1), (59, 1)] }, { coefficient := 2, powers := [(19, 1), (30, 1), (36, 1), (38, 1), (54, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(9, 1), (33, 1), (36, 1), (38, 1), (59, 1), (61, 1)] }, { coefficient := 1, powers := [(30, 1), (36, 1), (38, 1), (42, 1), (59, 1), (61, 1)] }, { coefficient := -2, powers := [(30, 1), (36, 1), (38, 1), (54, 1), (59, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(9, 1), (12, 1), (33, 1), (38, 1), (51, 1), (61, 1)] }, { coefficient := 1, powers := [(12, 1), (30, 1), (38, 1), (42, 1), (51, 1), (61, 1)] }, { coefficient := -2, powers := [(12, 1), (30, 1), (38, 1), (51, 1), (54, 1), (61, 1)] }, { coefficient := 1, powers := [(12, 1), (30, 1), (38, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (19, 2), (28, 1), (33, 1), (36, 1), (38, 1), (59, 1)] }, { coefficient := -1, powers := [(19, 2), (28, 1), (30, 1), (36, 1), (38, 1), (42, 1), (59, 1)] }, { coefficient := 2, powers := [(19, 2), (28, 1), (30, 1), (36, 1), (38, 1), (54, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (32, 1)] }, { coefficient := -1, powers := [(12, 1), (23, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (13, 1), (19, 1), (35, 1), (38, 1)] }],
  [{ coefficient := -1, powers := [(9, 1), (19, 1), (33, 1), (38, 1), (45, 1)] }, { coefficient := 1, powers := [(9, 1), (33, 1), (38, 1), (51, 1), (61, 1)] }, { coefficient := 1, powers := [(9, 1), (33, 1), (38, 1)] }, { coefficient := 1, powers := [(13, 1), (30, 1), (38, 1)] }, { coefficient := 1, powers := [(19, 1), (30, 1), (38, 1), (42, 1), (45, 1)] }, { coefficient := -2, powers := [(19, 1), (30, 1), (38, 1), (45, 1), (54, 1)] }, { coefficient := -1, powers := [(30, 1), (38, 1), (42, 1), (51, 1), (61, 1)] }, { coefficient := -1, powers := [(30, 1), (38, 1), (42, 1)] }, { coefficient := 2, powers := [(30, 1), (38, 1), (51, 1), (54, 1), (61, 1)] }, { coefficient := 1, powers := [(30, 1), (38, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (17, 1), (33, 1), (36, 1), (38, 1), (59, 1), (61, 1)] }, { coefficient := -1, powers := [(17, 1), (30, 1), (36, 1), (38, 1), (42, 1), (59, 1), (61, 1)] }, { coefficient := 2, powers := [(17, 1), (30, 1), (36, 1), (38, 1), (54, 1), (59, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(9, 1), (17, 1), (19, 1), (33, 1), (36, 1), (38, 1), (59, 1)] }, { coefficient := 1, powers := [(17, 1), (19, 1), (30, 1), (36, 1), (38, 1), (42, 1), (59, 1)] }, { coefficient := -2, powers := [(17, 1), (19, 1), (30, 1), (36, 1), (38, 1), (54, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(12, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (17, 1), (19, 1), (28, 1), (33, 1), (36, 1), (38, 1), (59, 1)] }, { coefficient := -1, powers := [(17, 1), (19, 1), (28, 1), (30, 1), (36, 1), (38, 1), (42, 1), (59, 1)] }, { coefficient := 2, powers := [(17, 1), (19, 1), (28, 1), (30, 1), (36, 1), (38, 1), (54, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(9, 1), (17, 1), (28, 1), (33, 1), (36, 1), (38, 1), (59, 1), (61, 1)] }, { coefficient := 1, powers := [(17, 1), (28, 1), (30, 1), (36, 1), (38, 1), (42, 1), (59, 1), (61, 1)] }, { coefficient := -2, powers := [(17, 1), (28, 1), (30, 1), (36, 1), (38, 1), (54, 1), (59, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (49, 1), (59, 1)] }, { coefficient := 1, powers := [(12, 1), (19, 1), (35, 1), (38, 1), (49, 1), (55, 1)] }, { coefficient := 1, powers := [(12, 1), (35, 1), (38, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (42, 1), (59, 1)] }, { coefficient := -1, powers := [(2, 1), (38, 1), (54, 1), (59, 1)] }, { coefficient := -1, powers := [(12, 1), (13, 1), (19, 1), (35, 1), (38, 1), (45, 1)] }, { coefficient := 1, powers := [(12, 1), (19, 1), (35, 1), (38, 1), (42, 1), (55, 1)] }, { coefficient := 1, powers := [(12, 1), (35, 1), (38, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (9, 1), (38, 1), (54, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (19, 1), (35, 1), (38, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (38, 1), (59, 1)] }, { coefficient := -1, powers := [(12, 1), (19, 1), (35, 1), (38, 1), (55, 1)] }, { coefficient := -1, powers := [(12, 1), (35, 1), (38, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(2, 1), (9, 1), (36, 1), (38, 1), (54, 1), (58, 1), (59, 1)] }, { coefficient := -1, powers := [(2, 1), (9, 1), (38, 1), (54, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (36, 1), (38, 1), (57, 1), (59, 1)] }, { coefficient := -1, powers := [(2, 1), (38, 1), (42, 1), (49, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (38, 1), (49, 1), (54, 1), (59, 1)] }, { coefficient := -1, powers := [(2, 1), (45, 1), (48, 1), (53, 1)] }, { coefficient := -1, powers := [(5, 1), (32, 1), (40, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (43, 1), (45, 1), (52, 1)] }, { coefficient := -1, powers := [(5, 1), (32, 1), (46, 1), (52, 1)] }, { coefficient := -1, powers := [(5, 1), (35, 1), (45, 1), (53, 1)] }, { coefficient := -1, powers := [(8, 1), (32, 1), (48, 1), (51, 1)] }, { coefficient := -1, powers := [(9, 1), (17, 1), (19, 1), (28, 1), (33, 1), (36, 1), (38, 1), (45, 1), (59, 1)] }, { coefficient := 1, powers := [(9, 1), (17, 1), (28, 1), (33, 1), (36, 1), (38, 1), (51, 1), (59, 1), (61, 1)] }, { coefficient := 1, powers := [(12, 1), (19, 1), (35, 1), (36, 1), (38, 1), (55, 1), (57, 1)] }, { coefficient := -1, powers := [(12, 1), (19, 1), (35, 1), (38, 1), (42, 1), (49, 1), (55, 1)] }, { coefficient := -1, powers := [(12, 1), (19, 1), (35, 1), (38, 1), (50, 1), (54, 1)] }, { coefficient := 1, powers := [(12, 1), (23, 1), (40, 1), (56, 1)] }, { coefficient := -1, powers := [(12, 1), (23, 1), (43, 1), (45, 1), (52, 1)] }, { coefficient := 1, powers := [(12, 1), (23, 1), (46, 1), (52, 1)] }, { coefficient := -1, powers := [(12, 1), (27, 1), (45, 1), (48, 1), (52, 1)] }, { coefficient := 1, powers := [(12, 1), (29, 1), (48, 1), (51, 1)] }, { coefficient := 1, powers := [(12, 1), (35, 1), (36, 1), (38, 1), (57, 1)] }, { coefficient := -1, powers := [(12, 1), (35, 1), (38, 1), (42, 1), (49, 1)] }, { coefficient := 1, powers := [(17, 1), (19, 1), (28, 1), (30, 1), (36, 1), (38, 1), (42, 1), (45, 1), (59, 1)] }, { coefficient := -2, powers := [(17, 1), (19, 1), (28, 1), (30, 1), (36, 1), (38, 1), (45, 1), (54, 1), (59, 1)] }, { coefficient := -1, powers := [(17, 1), (28, 1), (30, 1), (36, 1), (38, 1), (42, 1), (51, 1), (59, 1), (61, 1)] }, { coefficient := 2, powers := [(17, 1), (28, 1), (30, 1), (36, 1), (38, 1), (51, 1), (54, 1), (59, 1), (61, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (45, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (2, 1), (38, 1), (54, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (12, 1), (35, 1), (38, 1), (54, 1)] }, { coefficient := 1, powers := [(2, 1), (6, 1), (33, 1), (38, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (13, 1), (24, 1), (38, 1), (59, 1)] }, { coefficient := -1, powers := [(2, 1), (24, 1), (38, 1), (42, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (24, 1), (38, 1), (54, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (12, 1), (19, 1), (33, 1), (35, 1), (38, 1), (55, 1)] }, { coefficient := 1, powers := [(6, 1), (12, 1), (33, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(12, 1), (13, 1), (19, 1), (24, 1), (35, 1), (38, 1), (45, 1)] }, { coefficient := 1, powers := [(12, 1), (13, 1), (19, 1), (24, 1), (35, 1), (38, 1), (55, 1)] }, { coefficient := 1, powers := [(12, 1), (13, 1), (24, 1), (35, 1), (38, 1)] }, { coefficient := -1, powers := [(12, 1), (19, 1), (24, 1), (35, 1), (38, 1), (42, 1), (55, 1)] }, { coefficient := -1, powers := [(12, 1), (19, 1), (35, 1), (38, 1), (54, 1)] }, { coefficient := -1, powers := [(12, 1), (24, 1), (35, 1), (38, 1), (42, 1)] }, { coefficient := 1, powers := [(13, 1), (18, 1), (24, 1), (32, 1), (38, 1)] }, { coefficient := 1, powers := [(17, 1), (19, 1), (27, 1), (38, 1), (42, 1), (59, 1)] }, { coefficient := 1, powers := [(17, 1), (24, 1), (27, 1), (38, 1), (42, 1), (59, 1)] }, { coefficient := 1, powers := [(17, 1), (27, 1), (33, 1), (36, 1), (38, 1), (59, 1)] }, { coefficient := -1, powers := [(18, 1), (24, 1), (32, 1), (38, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (18, 1), (32, 1), (33, 1), (36, 1), (38, 1)] }, { coefficient := -1, powers := [(18, 1), (30, 1), (32, 1), (36, 1), (38, 1), (42, 1)] }, { coefficient := 2, powers := [(18, 1), (30, 1), (32, 1), (36, 1), (38, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (56, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1)] }, { coefficient := -1, powers := [(18, 1), (29, 1)] }]
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
    ¬ ∀ index : Fin 51,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component10.SelectedLeafB1_2.selectedHasNoCommonZero

end Krenn.Component10.SelectedLeafB1_2
