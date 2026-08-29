import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component10.SelectedLeafB4_2

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "1b75edeaadc34a35f1ab2722ce3932be28b4016ff78da285f1d08a349029b86d"
def certificateSHA256 : String := "53407bb12ae339fb1e7abaa6ea069b2420cfe072fbe4b04b848beab2570e9fb9"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 61 → Fin 641 := ![
  0,
  1,
  4,
  5,
  8,
  19,
  21,
  22,
  29,
  31,
  162,
  163,
  164,
  168,
  170,
  180,
  181,
  182,
  184,
  185,
  186,
  189,
  190,
  195,
  226,
  241,
  257,
  258,
  284,
  290,
  309,
  310,
  343,
  349,
  350,
  356,
  358,
  359,
  362,
  368,
  369,
  386,
  406,
  409,
  416,
  446,
  463,
  466,
  550,
  556,
  557,
  576,
  577,
  599,
  632,
  634,
  635,
  637,
  638,
  639,
  640
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 61 → SparsePoly (Fin 62) := ![
  [{ coefficient := 1, powers := [(3, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (33, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (30, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(30, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(33, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (48, 1)] }, { coefficient := 1, powers := [(24, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (52, 1)] }, { coefficient := 1, powers := [(19, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (53, 1)] }, { coefficient := 1, powers := [(19, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (32, 1)] }, { coefficient := 1, powers := [(32, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (29, 1)] }, { coefficient := 1, powers := [(29, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (45, 1)] }, { coefficient := 1, powers := [(12, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (47, 1)] }, { coefficient := 1, powers := [(17, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (23, 1)] }, { coefficient := 1, powers := [(23, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (19, 1)] }, { coefficient := 1, powers := [(17, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (43, 1)] }, { coefficient := 1, powers := [(18, 1), (19, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (56, 1)] }, { coefficient := 1, powers := [(18, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (43, 1)] }, { coefficient := 1, powers := [(27, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (52, 1)] }, { coefficient := 1, powers := [(29, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1), (53, 1)] }, { coefficient := 1, powers := [(13, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (33, 1), (50, 1)] }, { coefficient := 1, powers := [(5, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (30, 1), (44, 1)] }, { coefficient := 1, powers := [(8, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (27, 1), (47, 1)] }, { coefficient := 1, powers := [(23, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (27, 1), (48, 1)] }, { coefficient := 1, powers := [(23, 1), (43, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (19, 1), (55, 1)] }, { coefficient := 1, powers := [(12, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (24, 1), (44, 1)] }, { coefficient := 1, powers := [(12, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (24, 1), (43, 1)] }, { coefficient := 1, powers := [(18, 1), (19, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (24, 1), (44, 1)] }, { coefficient := 1, powers := [(17, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1)] }, { coefficient := 1, powers := [(19, 1), (43, 1)] }, { coefficient := 1, powers := [(24, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (59, 1)] }, { coefficient := 1, powers := [(12, 1), (48, 1)] }, { coefficient := 1, powers := [(18, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (59, 1)] }, { coefficient := 1, powers := [(12, 1), (56, 1)] }, { coefficient := 1, powers := [(18, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (46, 1)] }, { coefficient := 1, powers := [(18, 1), (40, 1)] }, { coefficient := 1, powers := [(18, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (51, 1)] }, { coefficient := 1, powers := [(23, 1), (55, 1)] }, { coefficient := 1, powers := [(28, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (53, 1)] }, { coefficient := 1, powers := [(29, 1), (41, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (38, 1), (57, 1)] }, { coefficient := 1, powers := [(9, 1), (33, 1), (38, 1)] }, { coefficient := 1, powers := [(13, 1), (30, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1), (51, 1)] }, { coefficient := 1, powers := [(19, 1), (43, 1), (51, 1)] }, { coefficient := 1, powers := [(43, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1), (52, 1)] }, { coefficient := 1, powers := [(19, 1), (43, 1), (52, 1)] }, { coefficient := 1, powers := [(19, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (41, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (54, 1)] }, { coefficient := 1, powers := [(12, 1), (23, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (30, 1), (56, 1)] }, { coefficient := 1, powers := [(8, 1), (30, 1), (48, 1)] }, { coefficient := 1, powers := [(18, 1), (30, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (23, 1), (58, 1)] }, { coefficient := 1, powers := [(23, 1)] }, { coefficient := 1, powers := [(27, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (23, 1), (56, 1)] }, { coefficient := 1, powers := [(9, 1), (29, 1), (48, 1)] }, { coefficient := 1, powers := [(9, 1), (35, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (24, 1), (46, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (40, 1)] }, { coefficient := 1, powers := [(18, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (48, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1)] }, { coefficient := 1, powers := [(17, 1), (27, 1), (48, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (53, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1)] }, { coefficient := 1, powers := [(12, 1), (29, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (43, 1), (52, 1)] }, { coefficient := 1, powers := [(23, 1), (56, 1)] }, { coefficient := 1, powers := [(29, 1), (48, 1)] }, { coefficient := 1, powers := [(35, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1)] }, { coefficient := 1, powers := [(6, 1), (58, 1)] }, { coefficient := 1, powers := [(24, 1), (40, 1)] }, { coefficient := 1, powers := [(24, 1), (45, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (51, 1)] }, { coefficient := 1, powers := [(3, 1), (58, 1)] }, { coefficient := 1, powers := [(19, 1), (51, 1)] }, { coefficient := 1, powers := [(19, 1), (55, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1)] }, { coefficient := 1, powers := [(3, 1), (33, 1)] }, { coefficient := 1, powers := [(13, 1), (19, 1)] }, { coefficient := 1, powers := [(19, 1), (54, 1)] }, { coefficient := 1, powers := [(24, 1), (42, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (49, 1)] }, { coefficient := 1, powers := [(6, 1), (30, 1)] }, { coefficient := 1, powers := [(9, 1), (24, 1)] }, { coefficient := 1, powers := [(19, 1), (49, 1)] }, { coefficient := 1, powers := [(24, 1), (39, 1)] }, { coefficient := 1, powers := [(30, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (48, 1), (52, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (52, 1)] }, { coefficient := 1, powers := [(17, 1), (23, 1), (56, 1)] }, { coefficient := 1, powers := [(17, 1), (29, 1), (48, 1)] }, { coefficient := 1, powers := [(17, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (36, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (39, 1), (54, 1)] }, { coefficient := 1, powers := [(0, 1), (42, 1), (49, 1)] }, { coefficient := 1, powers := [(3, 1), (24, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (30, 1), (54, 1)] }, { coefficient := 1, powers := [(3, 1), (33, 1), (49, 1)] }, { coefficient := 1, powers := [(6, 1), (19, 1), (57, 1)] }, { coefficient := 1, powers := [(6, 1), (30, 1), (42, 1)] }, { coefficient := 1, powers := [(6, 1), (33, 1), (39, 1)] }, { coefficient := 1, powers := [(9, 1), (19, 1), (54, 1)] }, { coefficient := 1, powers := [(9, 1), (24, 1), (42, 1)] }, { coefficient := 1, powers := [(9, 1), (33, 1), (36, 1)] }, { coefficient := 1, powers := [(13, 1), (19, 1), (49, 1)] }, { coefficient := 1, powers := [(13, 1), (24, 1), (39, 1)] }, { coefficient := 1, powers := [(13, 1), (30, 1), (36, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (41, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (48, 1), (53, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (53, 1)] }, { coefficient := 1, powers := [(8, 1), (23, 1), (59, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (48, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(12, 1), (23, 1), (56, 1)] }, { coefficient := 1, powers := [(12, 1), (29, 1), (48, 1)] }, { coefficient := 1, powers := [(12, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (53, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (41, 1)] }, { coefficient := 1, powers := [(18, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (60, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(39, 1)] }],
  [{ coefficient := 1, powers := [(40, 1), (61, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(41, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 61 → SparsePoly (Fin 62) := ![
  [{ coefficient := -2, powers := [(8, 1), (13, 1), (19, 1), (23, 1), (49, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (32, 1), (36, 1), (50, 1), (56, 1)] }, { coefficient := -2, powers := [(0, 1), (35, 1), (36, 1), (50, 1), (53, 1)] }, { coefficient := -1, powers := [(3, 1), (24, 1), (32, 1), (50, 1), (56, 1)] }, { coefficient := -2, powers := [(3, 1), (24, 1), (35, 1), (50, 1), (53, 1)] }, { coefficient := -1, powers := [(6, 1), (19, 1), (32, 1), (50, 1), (56, 1)] }, { coefficient := -2, powers := [(6, 1), (19, 1), (35, 1), (50, 1), (53, 1)] }, { coefficient := 1, powers := [(9, 1), (29, 1), (36, 1), (59, 1)] }, { coefficient := 1, powers := [(9, 1), (32, 1), (36, 1), (56, 1)] }, { coefficient := -1, powers := [(29, 1), (36, 1), (49, 1), (59, 1)] }, { coefficient := -1, powers := [(32, 1), (36, 1), (49, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (32, 1), (36, 1), (44, 1), (48, 1)] }, { coefficient := -1, powers := [(3, 1), (24, 1), (32, 1), (44, 1), (48, 1)] }, { coefficient := -1, powers := [(6, 1), (19, 1), (32, 1), (44, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (13, 1), (19, 1), (24, 1), (32, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (24, 2), (32, 1), (42, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (24, 1), (32, 1), (42, 1)] }, { coefficient := -1, powers := [(12, 1), (13, 1), (19, 1), (27, 1), (47, 1)] }, { coefficient := -1, powers := [(12, 1), (23, 1), (24, 1), (42, 1)] }, { coefficient := -1, powers := [(12, 1), (24, 1), (27, 1), (42, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (19, 1), (23, 1), (44, 1), (56, 1)] }, { coefficient := 1, powers := [(9, 1), (19, 1), (29, 1), (44, 1), (48, 1)] }, { coefficient := -1, powers := [(9, 1), (19, 1), (35, 1), (38, 1), (44, 1)] }, { coefficient := -2, powers := [(13, 1), (19, 1), (23, 1), (40, 1), (49, 1), (56, 1)] }, { coefficient := -2, powers := [(13, 1), (19, 1), (23, 1), (45, 1), (49, 1), (56, 1)] }, { coefficient := -1, powers := [(19, 1), (23, 1), (44, 1), (49, 1), (56, 1)] }, { coefficient := -1, powers := [(19, 1), (29, 1), (44, 1), (48, 1), (49, 1)] }, { coefficient := 1, powers := [(19, 1), (35, 1), (38, 1), (44, 1), (49, 1)] }, { coefficient := -2, powers := [(24, 1), (29, 1), (42, 1), (48, 1), (49, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (27, 1), (36, 1), (53, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (24, 1), (27, 1), (53, 1), (57, 1)] }, { coefficient := -1, powers := [(3, 1), (27, 1), (30, 1), (53, 1), (54, 1)] }, { coefficient := 1, powers := [(6, 1), (19, 1), (27, 1), (53, 1), (57, 1)] }, { coefficient := -1, powers := [(6, 1), (27, 1), (30, 1), (42, 1), (53, 1)] }, { coefficient := -1, powers := [(9, 1), (19, 1), (27, 1), (53, 1), (54, 1)] }, { coefficient := -1, powers := [(9, 1), (24, 1), (27, 1), (42, 1), (53, 1)] }, { coefficient := -1, powers := [(9, 1), (27, 1), (33, 1), (36, 1), (53, 1)] }, { coefficient := 2, powers := [(12, 1), (13, 1), (19, 1), (23, 1), (24, 1), (27, 1), (46, 1), (49, 1), (52, 1), (53, 1), (55, 1), (61, 1)] }, { coefficient := -4, powers := [(12, 1), (13, 1), (19, 1), (23, 1), (24, 1), (29, 1), (46, 1), (49, 1), (53, 1), (55, 1), (61, 1)] }, { coefficient := -2, powers := [(13, 1), (17, 1), (19, 1), (23, 1), (24, 1), (27, 1), (46, 1), (49, 1), (53, 2), (55, 1), (61, 1)] }, { coefficient := -1, powers := [(13, 1), (27, 1), (30, 1), (36, 1), (53, 1)] }, { coefficient := 1, powers := [(19, 1), (27, 1), (49, 1), (53, 1), (54, 1)] }, { coefficient := 1, powers := [(24, 1), (27, 1), (42, 1), (49, 1), (53, 1)] }, { coefficient := 1, powers := [(27, 1), (33, 1), (36, 1), (49, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(9, 1), (19, 1), (22, 1), (48, 1), (54, 1)] }, { coefficient := -1, powers := [(9, 1), (22, 1), (24, 1), (42, 1), (48, 1)] }, { coefficient := -1, powers := [(9, 1), (22, 1), (33, 1), (36, 1), (48, 1)] }, { coefficient := -2, powers := [(13, 1), (17, 1), (19, 1), (22, 1), (23, 1), (24, 1), (46, 1), (48, 1), (49, 1), (53, 1), (55, 1), (61, 1)] }, { coefficient := -4, powers := [(13, 1), (18, 1), (19, 1), (23, 2), (24, 1), (46, 1), (49, 1), (53, 1), (55, 1), (61, 1)] }, { coefficient := 1, powers := [(19, 1), (22, 1), (48, 1), (49, 1), (54, 1)] }, { coefficient := 1, powers := [(22, 1), (24, 1), (42, 1), (48, 1), (49, 1)] }, { coefficient := 1, powers := [(22, 1), (33, 1), (36, 1), (48, 1), (49, 1)] }],
  [{ coefficient := 2, powers := [(13, 1), (19, 1), (23, 1), (53, 1)] }, { coefficient := 2, powers := [(23, 1), (24, 1), (42, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (12, 1), (13, 1), (35, 1), (36, 1), (60, 1)] }, { coefficient := -1, powers := [(3, 1), (12, 1), (13, 1), (24, 1), (35, 1), (60, 1)] }, { coefficient := 1, powers := [(3, 1), (12, 1), (35, 1), (54, 1)] }, { coefficient := 1, powers := [(3, 1), (18, 1), (32, 1), (54, 1)] }, { coefficient := -1, powers := [(6, 1), (12, 1), (13, 1), (19, 1), (35, 1), (60, 1)] }, { coefficient := 1, powers := [(6, 1), (12, 1), (35, 1), (42, 1)] }, { coefficient := 1, powers := [(6, 1), (18, 1), (32, 1), (42, 1)] }, { coefficient := 1, powers := [(12, 1), (13, 1), (35, 1), (36, 1)] }, { coefficient := 1, powers := [(13, 1), (18, 1), (32, 1), (36, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (9, 1), (12, 1), (35, 1), (36, 1), (60, 1)] }, { coefficient := -1, powers := [(3, 1), (9, 1), (12, 1), (24, 1), (35, 1), (60, 1)] }, { coefficient := -1, powers := [(6, 1), (9, 1), (12, 1), (19, 1), (35, 1), (60, 1)] }, { coefficient := 1, powers := [(9, 1), (12, 1), (35, 1), (36, 1)] }, { coefficient := 2, powers := [(9, 1), (18, 1), (32, 1), (36, 1)] }, { coefficient := -1, powers := [(12, 1), (35, 1), (36, 1), (49, 1)] }, { coefficient := -2, powers := [(18, 1), (32, 1), (36, 1), (49, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (13, 1), (27, 1), (49, 1), (52, 1)] }, { coefficient := 2, powers := [(12, 1), (24, 1), (29, 1), (42, 1), (49, 1), (60, 1)] }],
  [{ coefficient := 2, powers := [(5, 1), (13, 1), (17, 1), (19, 1), (23, 1), (24, 1), (32, 1), (43, 1), (46, 1), (49, 1), (51, 1), (53, 1), (55, 1), (61, 1)] }, { coefficient := -1, powers := [(5, 1), (13, 1), (19, 1), (32, 1), (43, 1), (49, 1), (60, 1)] }, { coefficient := -1, powers := [(5, 1), (13, 1), (32, 1), (43, 1), (49, 1)] }, { coefficient := -1, powers := [(5, 1), (24, 1), (32, 1), (42, 1), (43, 1), (49, 1), (60, 1)] }, { coefficient := -2, powers := [(12, 1), (13, 1), (19, 1), (23, 1), (43, 1), (49, 1), (51, 1)] }, { coefficient := 1, powers := [(12, 1), (13, 1), (23, 1), (43, 1), (49, 1)] }],
  [{ coefficient := -2, powers := [(9, 1), (18, 1), (19, 1), (23, 1), (44, 1)] }, { coefficient := 2, powers := [(13, 1), (18, 1), (19, 1), (23, 1), (49, 1), (51, 1)] }, { coefficient := 2, powers := [(18, 1), (19, 1), (23, 1), (44, 1), (49, 1)] }, { coefficient := 2, powers := [(18, 1), (23, 1), (42, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (13, 1), (19, 1), (30, 1), (56, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (24, 1), (30, 1), (42, 1), (56, 1), (60, 1)] }, { coefficient := -2, powers := [(18, 1), (30, 1), (38, 1), (42, 1)] }],
  [{ coefficient := -2, powers := [(12, 1), (24, 1), (42, 1), (48, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (13, 1), (19, 1), (23, 1), (49, 1), (56, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (13, 1), (19, 1), (28, 1), (49, 1), (56, 1)] }, { coefficient := -2, powers := [(13, 1), (18, 1), (19, 1), (23, 1), (24, 1), (29, 1), (46, 1), (49, 1), (53, 1), (55, 1), (61, 1)] }, { coefficient := 2, powers := [(13, 1), (19, 1), (27, 1), (49, 1), (56, 1)] }],
  [{ coefficient := -2, powers := [(9, 1), (18, 1), (19, 1), (53, 1)] }, { coefficient := 2, powers := [(18, 1), (19, 1), (49, 1), (53, 1)] }],
  [{ coefficient := 2, powers := [(5, 1), (13, 1), (19, 1), (23, 1), (24, 1), (32, 1), (46, 1), (49, 1), (51, 1), (53, 1), (55, 1), (56, 1), (61, 1)] }, { coefficient := -2, powers := [(9, 1), (19, 1), (23, 1), (43, 1), (53, 1), (54, 1), (60, 1)] }, { coefficient := -2, powers := [(13, 1), (19, 1), (23, 1), (43, 1), (49, 1), (53, 1), (55, 1), (60, 1), (61, 1)] }, { coefficient := -2, powers := [(13, 1), (19, 1), (23, 1), (46, 1), (49, 1), (53, 1), (55, 1), (61, 1)] }, { coefficient := 2, powers := [(19, 1), (23, 1), (43, 1), (49, 1), (53, 1), (54, 1), (60, 1)] }],
  [{ coefficient := 2, powers := [(5, 1), (13, 1), (19, 1), (23, 1), (24, 1), (32, 1), (46, 1), (49, 1), (52, 1), (53, 1), (55, 1), (61, 1)] }, { coefficient := -2, powers := [(13, 1), (19, 1), (23, 1), (49, 1), (53, 1), (55, 1), (61, 1)] }],
  [{ coefficient := -2, powers := [(5, 1), (13, 1), (19, 2), (23, 1), (24, 1), (32, 1), (46, 1), (49, 1), (51, 1), (53, 1), (55, 1), (61, 1)] }, { coefficient := -2, powers := [(5, 1), (13, 1), (19, 1), (23, 1), (24, 2), (32, 1), (46, 1), (49, 1), (51, 1), (53, 1), (55, 1), (61, 1)] }, { coefficient := 2, powers := [(5, 1), (13, 1), (19, 1), (23, 1), (24, 1), (32, 1), (46, 1), (49, 1), (53, 1), (55, 1), (61, 1)] }, { coefficient := -2, powers := [(12, 1), (13, 1), (19, 1), (23, 2), (24, 1), (46, 1), (49, 1), (53, 1), (55, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (12, 1), (13, 1), (49, 1), (52, 1)] }, { coefficient := -1, powers := [(9, 1), (12, 1), (13, 1), (19, 1), (52, 1)] }, { coefficient := -1, powers := [(9, 1), (12, 1), (24, 1), (42, 1), (52, 1)] }, { coefficient := 1, powers := [(12, 1), (13, 1), (24, 1), (49, 1), (52, 1)] }],
  [{ coefficient := 2, powers := [(12, 1), (13, 1), (18, 1), (19, 1), (23, 1), (24, 1), (46, 1), (49, 1), (53, 1), (55, 1), (61, 1)] }],
  [{ coefficient := 2, powers := [(9, 1), (18, 1), (19, 1), (23, 1)] }, { coefficient := -2, powers := [(18, 1), (19, 1), (23, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (32, 1), (36, 1), (56, 1)] }, { coefficient := 2, powers := [(0, 1), (35, 1), (36, 1), (53, 1)] }, { coefficient := 1, powers := [(3, 1), (24, 1), (32, 1), (56, 1)] }, { coefficient := 2, powers := [(3, 1), (24, 1), (35, 1), (53, 1)] }, { coefficient := 1, powers := [(6, 1), (19, 1), (32, 1), (56, 1)] }, { coefficient := 2, powers := [(6, 1), (19, 1), (35, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (32, 1), (36, 1), (48, 1)] }, { coefficient := 1, powers := [(3, 1), (24, 1), (32, 1), (48, 1)] }, { coefficient := 1, powers := [(6, 1), (19, 1), (32, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (13, 1), (19, 1), (56, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (42, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (13, 1), (19, 1), (52, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (42, 1), (52, 1)] }],
  [{ coefficient := 2, powers := [(13, 1), (19, 1), (23, 1), (49, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [(9, 1), (19, 1), (23, 1), (56, 1)] }, { coefficient := -1, powers := [(9, 1), (19, 1), (29, 1), (48, 1)] }, { coefficient := 1, powers := [(9, 1), (19, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(19, 1), (23, 1), (49, 1), (56, 1)] }, { coefficient := 1, powers := [(19, 1), (29, 1), (48, 1), (49, 1)] }, { coefficient := -1, powers := [(19, 1), (35, 1), (38, 1), (49, 1)] }],
  [{ coefficient := 2, powers := [(9, 1), (19, 1), (23, 1), (44, 1), (53, 1)] }, { coefficient := -2, powers := [(19, 1), (23, 1), (44, 1), (49, 1), (53, 1)] }],
  [{ coefficient := -2, powers := [(9, 1), (19, 1), (23, 1), (43, 1), (53, 1)] }, { coefficient := 2, powers := [(19, 1), (23, 1), (43, 1), (49, 1), (53, 1)] }],
  [{ coefficient := 2, powers := [(9, 1), (17, 1), (19, 1), (23, 1), (53, 1), (54, 1), (60, 1)] }, { coefficient := -1, powers := [(12, 1), (13, 1), (23, 1), (49, 1), (52, 1)] }, { coefficient := 2, powers := [(13, 1), (17, 1), (19, 1), (23, 1), (49, 1), (53, 1), (55, 1), (60, 1), (61, 1)] }, { coefficient := -2, powers := [(17, 1), (19, 1), (23, 1), (49, 1), (53, 1), (54, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (29, 1), (36, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (24, 1), (29, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (29, 1), (30, 1), (54, 1)] }, { coefficient := 1, powers := [(6, 1), (19, 1), (29, 1), (57, 1)] }, { coefficient := 1, powers := [(6, 1), (29, 1), (30, 1), (42, 1)] }, { coefficient := 1, powers := [(9, 1), (19, 1), (29, 1), (54, 1)] }, { coefficient := 1, powers := [(9, 1), (24, 1), (29, 1), (42, 1)] }, { coefficient := 2, powers := [(13, 1), (17, 1), (19, 1), (23, 1), (24, 1), (29, 1), (46, 1), (49, 1), (53, 1), (55, 1), (61, 1)] }, { coefficient := 1, powers := [(13, 1), (29, 1), (30, 1), (36, 1)] }, { coefficient := -1, powers := [(19, 1), (29, 1), (49, 1), (54, 1)] }, { coefficient := -1, powers := [(24, 1), (29, 1), (42, 1), (49, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (13, 1), (19, 1), (23, 1), (49, 1), (51, 1)] }, { coefficient := 1, powers := [(0, 1), (23, 1), (36, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (23, 1), (24, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (23, 1), (30, 1), (54, 1)] }, { coefficient := 1, powers := [(6, 1), (19, 1), (23, 1), (57, 1)] }, { coefficient := 1, powers := [(6, 1), (23, 1), (30, 1), (42, 1)] }, { coefficient := 1, powers := [(9, 1), (19, 1), (23, 1), (54, 1)] }, { coefficient := 1, powers := [(9, 1), (23, 1), (24, 1), (42, 1)] }, { coefficient := 1, powers := [(9, 1), (23, 1), (33, 1), (36, 1)] }, { coefficient := 2, powers := [(13, 1), (17, 1), (19, 1), (23, 2), (24, 1), (46, 1), (49, 1), (53, 1), (55, 1), (61, 1)] }, { coefficient := -2, powers := [(13, 1), (19, 2), (23, 1), (49, 1), (51, 1)] }, { coefficient := -2, powers := [(13, 1), (19, 2), (23, 1), (49, 1), (55, 1)] }, { coefficient := -2, powers := [(13, 1), (19, 1), (23, 1), (49, 1)] }, { coefficient := 1, powers := [(13, 1), (23, 1), (30, 1), (36, 1)] }, { coefficient := -1, powers := [(19, 1), (23, 1), (49, 1), (54, 1)] }, { coefficient := -1, powers := [(23, 1), (24, 1), (42, 1), (49, 1)] }, { coefficient := -1, powers := [(23, 1), (33, 1), (36, 1), (49, 1)] }],
  [{ coefficient := 2, powers := [(5, 1), (13, 1), (19, 1), (23, 1), (24, 2), (32, 1), (46, 1), (49, 1), (52, 1), (53, 1), (55, 1), (61, 1)] }, { coefficient := 2, powers := [(13, 1), (19, 2), (23, 1), (49, 1), (53, 1), (55, 1), (61, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (12, 1), (13, 1), (19, 1), (49, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (18, 1), (36, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (18, 1), (24, 1), (57, 1)] }, { coefficient := -1, powers := [(3, 1), (18, 1), (30, 1), (54, 1)] }, { coefficient := 1, powers := [(6, 1), (18, 1), (19, 1), (57, 1)] }, { coefficient := 1, powers := [(6, 1), (18, 1), (30, 1), (42, 1)] }, { coefficient := 1, powers := [(9, 1), (18, 1), (19, 1), (54, 1)] }, { coefficient := 1, powers := [(9, 1), (18, 1), (24, 1), (42, 1)] }, { coefficient := -1, powers := [(9, 1), (18, 1), (33, 1), (36, 1)] }, { coefficient := 2, powers := [(13, 1), (17, 1), (18, 1), (19, 1), (23, 1), (24, 1), (46, 1), (49, 1), (53, 1), (55, 1), (61, 1)] }, { coefficient := -1, powers := [(13, 1), (18, 1), (30, 1), (36, 1)] }, { coefficient := -1, powers := [(18, 1), (19, 1), (49, 1), (54, 1)] }, { coefficient := -1, powers := [(18, 1), (24, 1), (42, 1), (49, 1)] }, { coefficient := 2, powers := [(18, 1), (30, 1), (36, 1), (42, 1)] }, { coefficient := 1, powers := [(18, 1), (33, 1), (36, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (12, 1), (35, 1), (36, 1), (60, 1)] }, { coefficient := 1, powers := [(3, 1), (12, 1), (24, 1), (35, 1), (60, 1)] }, { coefficient := 1, powers := [(6, 1), (12, 1), (19, 1), (35, 1), (60, 1)] }],
  [{ coefficient := -2, powers := [(5, 1), (13, 1), (17, 1), (19, 1), (23, 1), (24, 1), (32, 1), (46, 1), (49, 1), (52, 1), (53, 1), (55, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (13, 1), (19, 1), (32, 1), (49, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (13, 1), (32, 1), (49, 1)] }, { coefficient := 1, powers := [(5, 1), (24, 1), (32, 1), (42, 1), (49, 1), (60, 1)] }, { coefficient := 2, powers := [(12, 1), (13, 1), (19, 1), (23, 1), (49, 1), (51, 1)] }, { coefficient := -1, powers := [(12, 1), (13, 1), (23, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (19, 1), (56, 1)] }, { coefficient := -1, powers := [(19, 1), (49, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (32, 1), (54, 1)] }, { coefficient := 1, powers := [(6, 1), (32, 1), (42, 1)] }, { coefficient := 1, powers := [(13, 1), (32, 1), (36, 1)] }],
  [{ coefficient := -2, powers := [(12, 1), (13, 1), (19, 1), (49, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (13, 1), (19, 1)] }],
  [{ coefficient := -2, powers := [(5, 1), (13, 1), (19, 1), (23, 1), (24, 1), (32, 1), (46, 1), (49, 1), (52, 1), (53, 1), (55, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (36, 1), (53, 1), (57, 1)] }, { coefficient := -1, powers := [(3, 1), (24, 1), (53, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (30, 1), (53, 1), (54, 1)] }, { coefficient := -1, powers := [(6, 1), (19, 1), (53, 1), (57, 1)] }, { coefficient := 1, powers := [(6, 1), (30, 1), (42, 1), (53, 1)] }, { coefficient := 1, powers := [(9, 1), (19, 1), (53, 1), (54, 1)] }, { coefficient := 1, powers := [(9, 1), (24, 1), (42, 1), (53, 1)] }, { coefficient := 1, powers := [(9, 1), (33, 1), (36, 1), (53, 1)] }, { coefficient := -2, powers := [(12, 1), (13, 1), (19, 1), (23, 1), (24, 1), (46, 1), (49, 1), (52, 1), (53, 1), (55, 1), (61, 1)] }, { coefficient := 2, powers := [(13, 1), (17, 1), (19, 1), (23, 1), (24, 1), (46, 1), (49, 1), (53, 2), (55, 1), (61, 1)] }, { coefficient := 1, powers := [(13, 1), (30, 1), (36, 1), (53, 1)] }, { coefficient := -1, powers := [(19, 1), (49, 1), (53, 1), (54, 1)] }, { coefficient := -1, powers := [(24, 1), (42, 1), (49, 1), (53, 1)] }, { coefficient := -1, powers := [(33, 1), (36, 1), (49, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (19, 1), (48, 1), (54, 1)] }, { coefficient := 1, powers := [(9, 1), (24, 1), (42, 1), (48, 1)] }, { coefficient := 1, powers := [(9, 1), (33, 1), (36, 1), (48, 1)] }, { coefficient := 2, powers := [(13, 1), (17, 1), (19, 1), (23, 1), (24, 1), (46, 1), (48, 1), (49, 1), (53, 1), (55, 1), (61, 1)] }, { coefficient := -1, powers := [(19, 1), (48, 1), (49, 1), (54, 1)] }, { coefficient := -1, powers := [(24, 1), (42, 1), (48, 1), (49, 1)] }, { coefficient := -1, powers := [(33, 1), (36, 1), (48, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (12, 1), (13, 1), (19, 1)] }, { coefficient := 1, powers := [(9, 1), (12, 1), (24, 1), (42, 1)] }, { coefficient := -1, powers := [(12, 1), (24, 1), (42, 1), (49, 1)] }],
  [{ coefficient := 2, powers := [(12, 1), (13, 1), (19, 1), (23, 1), (49, 1), (56, 1)] }],
  [{ coefficient := 2, powers := [(8, 1), (13, 1), (19, 1), (23, 1), (49, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(49, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (13, 1), (19, 1), (32, 1), (56, 1), (60, 1)] }, { coefficient := -1, powers := [(5, 1), (24, 1), (32, 1), (42, 1), (56, 1), (60, 1)] }, { coefficient := -2, powers := [(18, 1), (23, 1), (42, 1), (53, 1)] }],
  [{ coefficient := 2, powers := [(12, 1), (13, 1), (19, 1), (23, 1), (24, 1), (46, 1), (49, 1), (53, 1), (55, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(0, 1), (36, 1), (57, 1)] }, { coefficient := -1, powers := [(3, 1), (24, 1), (57, 1)] }, { coefficient := -1, powers := [(3, 1), (30, 1), (54, 1)] }, { coefficient := -1, powers := [(6, 1), (19, 1), (57, 1)] }, { coefficient := -1, powers := [(6, 1), (30, 1), (42, 1)] }, { coefficient := -1, powers := [(9, 1), (19, 1), (54, 1)] }, { coefficient := -1, powers := [(9, 1), (24, 1), (42, 1)] }, { coefficient := -1, powers := [(9, 1), (33, 1), (36, 1)] }, { coefficient := -2, powers := [(13, 1), (17, 1), (19, 1), (23, 1), (24, 1), (46, 1), (49, 1), (53, 1), (55, 1), (61, 1)] }, { coefficient := -1, powers := [(13, 1), (30, 1), (36, 1)] }, { coefficient := 1, powers := [(19, 1), (49, 1), (54, 1)] }, { coefficient := 1, powers := [(24, 1), (42, 1), (49, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1), (49, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (12, 1), (35, 1), (36, 1), (38, 1), (57, 1)] }, { coefficient := -1, powers := [(3, 1), (12, 1), (24, 1), (35, 1), (38, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (13, 1), (19, 1), (32, 1), (49, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (24, 1), (32, 1), (42, 1), (49, 1), (56, 1)] }, { coefficient := -1, powers := [(6, 1), (12, 1), (19, 1), (35, 1), (38, 1), (57, 1)] }, { coefficient := -2, powers := [(9, 1), (17, 1), (19, 1), (23, 1), (43, 1), (53, 1), (54, 1)] }, { coefficient := -2, powers := [(12, 1), (24, 1), (29, 1), (42, 1), (48, 1), (49, 1)] }, { coefficient := -2, powers := [(13, 1), (17, 1), (19, 1), (23, 1), (43, 1), (49, 1), (53, 1), (55, 1), (61, 1)] }, { coefficient := 2, powers := [(17, 1), (19, 1), (23, 1), (43, 1), (49, 1), (53, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (36, 1), (38, 1), (57, 1), (59, 1)] }, { coefficient := 2, powers := [(0, 1), (36, 1), (48, 1), (53, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (24, 1), (38, 1), (57, 1), (59, 1)] }, { coefficient := 2, powers := [(3, 1), (24, 1), (48, 1), (53, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (30, 1), (38, 1), (54, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (19, 1), (38, 1), (57, 1), (59, 1)] }, { coefficient := 2, powers := [(6, 1), (19, 1), (48, 1), (53, 1), (57, 1)] }, { coefficient := 1, powers := [(6, 1), (30, 1), (38, 1), (42, 1), (59, 1)] }, { coefficient := 1, powers := [(9, 1), (19, 1), (38, 1), (54, 1), (59, 1)] }, { coefficient := -1, powers := [(9, 1), (19, 1), (48, 1), (53, 1), (54, 1)] }, { coefficient := 1, powers := [(9, 1), (24, 1), (38, 1), (42, 1), (59, 1)] }, { coefficient := -1, powers := [(9, 1), (24, 1), (42, 1), (48, 1), (53, 1)] }, { coefficient := 1, powers := [(9, 1), (33, 1), (36, 1), (38, 1), (59, 1)] }, { coefficient := -1, powers := [(9, 1), (33, 1), (36, 1), (48, 1), (53, 1)] }, { coefficient := 2, powers := [(13, 1), (17, 1), (19, 1), (23, 1), (24, 1), (38, 1), (46, 1), (49, 1), (53, 1), (55, 1), (59, 1), (61, 1)] }, { coefficient := -2, powers := [(13, 1), (17, 1), (19, 1), (23, 1), (24, 1), (46, 1), (48, 1), (49, 1), (53, 2), (55, 1), (61, 1)] }, { coefficient := 1, powers := [(13, 1), (30, 1), (36, 1), (38, 1), (59, 1)] }, { coefficient := -1, powers := [(19, 1), (38, 1), (49, 1), (54, 1), (59, 1)] }, { coefficient := 1, powers := [(19, 1), (48, 1), (49, 1), (53, 1), (54, 1)] }, { coefficient := -1, powers := [(24, 1), (38, 1), (42, 1), (49, 1), (59, 1)] }, { coefficient := 1, powers := [(24, 1), (42, 1), (48, 1), (49, 1), (53, 1)] }, { coefficient := -1, powers := [(33, 1), (36, 1), (38, 1), (49, 1), (59, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1), (48, 1), (49, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (13, 1), (19, 1), (24, 1), (32, 1), (56, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (24, 2), (32, 1), (42, 1), (56, 1), (60, 1)] }, { coefficient := 1, powers := [(6, 1), (33, 1)] }, { coefficient := 2, powers := [(12, 1), (24, 1), (29, 1), (42, 1), (48, 1)] }, { coefficient := 1, powers := [(13, 1), (24, 1)] }, { coefficient := 2, powers := [(18, 1), (23, 1), (24, 1), (42, 1), (53, 1)] }],
  [{ coefficient := -2, powers := [(13, 1), (18, 1), (19, 2), (23, 1), (49, 1), (53, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (2, 1), (36, 1), (56, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (8, 1), (35, 1), (36, 1), (57, 1)] }, { coefficient := 2, powers := [(0, 1), (13, 1), (17, 1), (19, 1), (28, 1), (49, 1), (56, 1)] }, { coefficient := -1, powers := [(0, 1), (18, 1), (29, 1), (36, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (3, 1), (24, 1), (56, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (3, 1), (30, 1), (54, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (6, 1), (19, 1), (56, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (6, 1), (30, 1), (42, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (9, 1), (24, 1), (42, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (9, 1), (33, 1), (36, 1), (56, 1)] }, { coefficient := 2, powers := [(2, 1), (13, 1), (17, 1), (19, 1), (23, 1), (24, 1), (46, 1), (49, 1), (53, 1), (55, 1), (56, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (13, 1), (30, 1), (36, 1), (56, 1)] }, { coefficient := -1, powers := [(2, 1), (24, 1), (42, 1), (49, 1), (56, 1)] }, { coefficient := -1, powers := [(2, 1), (33, 1), (36, 1), (49, 1), (56, 1)] }, { coefficient := 1, powers := [(3, 1), (8, 1), (24, 1), (35, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (8, 1), (30, 1), (35, 1), (54, 1)] }, { coefficient := -1, powers := [(3, 1), (18, 1), (24, 1), (29, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (18, 1), (29, 1), (30, 1), (54, 1)] }, { coefficient := 1, powers := [(6, 1), (8, 1), (19, 1), (35, 1), (57, 1)] }, { coefficient := 1, powers := [(6, 1), (8, 1), (30, 1), (35, 1), (42, 1)] }, { coefficient := -1, powers := [(6, 1), (18, 1), (19, 1), (29, 1), (57, 1)] }, { coefficient := -1, powers := [(6, 1), (18, 1), (29, 1), (30, 1), (42, 1)] }, { coefficient := 1, powers := [(8, 1), (9, 1), (19, 1), (35, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (9, 1), (24, 1), (35, 1), (42, 1)] }, { coefficient := 1, powers := [(8, 1), (9, 1), (33, 1), (35, 1), (36, 1)] }, { coefficient := 2, powers := [(8, 1), (13, 1), (17, 1), (19, 1), (23, 1), (24, 1), (35, 1), (46, 1), (49, 1), (53, 1), (55, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (13, 1), (30, 1), (35, 1), (36, 1)] }, { coefficient := -1, powers := [(8, 1), (19, 1), (35, 1), (49, 1), (54, 1)] }, { coefficient := -1, powers := [(8, 1), (24, 1), (35, 1), (42, 1), (49, 1)] }, { coefficient := -1, powers := [(8, 1), (33, 1), (35, 1), (36, 1), (49, 1)] }, { coefficient := -1, powers := [(9, 1), (18, 1), (19, 1), (29, 1), (54, 1)] }, { coefficient := -1, powers := [(9, 1), (18, 1), (24, 1), (29, 1), (42, 1)] }, { coefficient := 2, powers := [(9, 1), (18, 1), (29, 1), (33, 1), (36, 1)] }, { coefficient := -2, powers := [(13, 1), (17, 1), (19, 1), (27, 1), (49, 1), (56, 1)] }, { coefficient := 1, powers := [(13, 1), (18, 1), (29, 1), (30, 1), (36, 1)] }, { coefficient := 1, powers := [(18, 1), (19, 1), (29, 1), (49, 1), (54, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (29, 1), (42, 1), (49, 1)] }, { coefficient := -2, powers := [(18, 1), (29, 1), (30, 1), (36, 1), (42, 1)] }, { coefficient := -2, powers := [(18, 1), (29, 1), (33, 1), (36, 1), (49, 1)] }]
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
    ¬ ∀ index : Fin 61,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component10.SelectedLeafB4_2.selectedHasNoCommonZero

end Krenn.Component10.SelectedLeafB4_2
