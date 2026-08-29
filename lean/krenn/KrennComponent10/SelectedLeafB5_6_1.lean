import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component10.SelectedLeafB5_6_1

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "5f8295d666c7c4a8cf98c5ae413ed61626684550591dd64f807d185f5d841aed"
def certificateSHA256 : String := "6b08e7a6537ee4beedcd8afa68ef399232734e7546fc18e55abd33c063bf6650"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 33 → Fin 644 := ![
  4,
  5,
  18,
  21,
  24,
  29,
  31,
  164,
  167,
  182,
  241,
  284,
  347,
  349,
  359,
  362,
  364,
  406,
  411,
  466,
  557,
  576,
  577,
  584,
  632,
  634,
  635,
  637,
  638,
  640,
  641,
  642,
  643
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 33 → SparsePoly (Fin 65) := ![
  [{ coefficient := 1, powers := [(8, 1), (30, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(30, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(33, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (53, 1)] }, { coefficient := 1, powers := [(19, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (58, 1)] }, { coefficient := 1, powers := [(17, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (23, 1)] }, { coefficient := 1, powers := [(23, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (30, 1), (44, 1)] }, { coefficient := 1, powers := [(8, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (19, 1), (55, 1)] }, { coefficient := 1, powers := [(12, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (42, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (54, 1)] }, { coefficient := 1, powers := [(17, 1), (27, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (59, 1)] }, { coefficient := 1, powers := [(12, 1), (48, 1)] }, { coefficient := 1, powers := [(18, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (53, 1)] }, { coefficient := 1, powers := [(29, 1), (41, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (38, 1), (57, 1)] }, { coefficient := 1, powers := [(9, 1), (33, 1), (38, 1)] }, { coefficient := 1, powers := [(13, 1), (30, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(3, 1), (30, 1), (56, 1)] }, { coefficient := 1, powers := [(9, 1), (19, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (30, 1), (56, 1)] }, { coefficient := 1, powers := [(8, 1), (30, 1), (48, 1)] }, { coefficient := 1, powers := [(18, 1), (30, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (19, 1), (57, 1)] }, { coefficient := 1, powers := [(8, 1), (30, 1), (42, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (53, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1)] }, { coefficient := 1, powers := [(12, 1), (29, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (51, 1)] }, { coefficient := 1, powers := [(3, 1), (58, 1)] }, { coefficient := 1, powers := [(19, 1), (51, 1)] }, { coefficient := 1, powers := [(19, 1), (55, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1)] }, { coefficient := 1, powers := [(3, 1), (33, 1)] }, { coefficient := 1, powers := [(13, 1), (19, 1)] }, { coefficient := 1, powers := [(19, 1), (54, 1)] }, { coefficient := 1, powers := [(24, 1), (42, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (49, 1)] }, { coefficient := 1, powers := [(6, 1), (30, 1)] }, { coefficient := 1, powers := [(9, 1), (24, 1)] }, { coefficient := 1, powers := [(19, 1), (49, 1)] }, { coefficient := 1, powers := [(24, 1), (39, 1)] }, { coefficient := 1, powers := [(30, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1), (50, 1)] }, { coefficient := 1, powers := [(3, 1), (33, 1), (50, 1)] }, { coefficient := 1, powers := [(3, 1), (57, 1)] }, { coefficient := 1, powers := [(9, 1), (42, 1)] }, { coefficient := 1, powers := [(13, 1), (19, 1), (50, 1)] }, { coefficient := 1, powers := [(13, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (36, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (39, 1), (54, 1)] }, { coefficient := 1, powers := [(0, 1), (42, 1), (49, 1)] }, { coefficient := 1, powers := [(3, 1), (24, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (30, 1), (54, 1)] }, { coefficient := 1, powers := [(3, 1), (33, 1), (49, 1)] }, { coefficient := 1, powers := [(6, 1), (19, 1), (57, 1)] }, { coefficient := 1, powers := [(6, 1), (30, 1), (42, 1)] }, { coefficient := 1, powers := [(6, 1), (33, 1), (39, 1)] }, { coefficient := 1, powers := [(9, 1), (19, 1), (54, 1)] }, { coefficient := 1, powers := [(9, 1), (24, 1), (42, 1)] }, { coefficient := 1, powers := [(9, 1), (33, 1), (36, 1)] }, { coefficient := 1, powers := [(13, 1), (19, 1), (49, 1)] }, { coefficient := 1, powers := [(13, 1), (24, 1), (39, 1)] }, { coefficient := 1, powers := [(13, 1), (30, 1), (36, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (41, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (48, 1), (53, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (53, 1)] }, { coefficient := 1, powers := [(8, 1), (23, 1), (59, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (48, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(12, 1), (23, 1), (56, 1)] }, { coefficient := 1, powers := [(12, 1), (29, 1), (48, 1)] }, { coefficient := 1, powers := [(12, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (53, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (41, 1)] }, { coefficient := 1, powers := [(18, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (60, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (61, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(39, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(41, 1)] }],
  [{ coefficient := 1, powers := [(54, 1)] }],
  [{ coefficient := 1, powers := [(55, 1)] }],
  [{ coefficient := 1, powers := [(56, 1), (64, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 33 → SparsePoly (Fin 65) := ![
  [{ coefficient := -1, powers := [(0, 1), (23, 1), (36, 1), (39, 1), (44, 1), (59, 1), (62, 1)] }, { coefficient := -1, powers := [(3, 1), (23, 1), (24, 1), (39, 1), (44, 1), (59, 1), (62, 1)] }, { coefficient := 1, powers := [(3, 1), (32, 1), (48, 1), (60, 1), (62, 1)] }, { coefficient := -1, powers := [(6, 1), (23, 1), (39, 1), (42, 1), (59, 1), (62, 1)] }, { coefficient := 1, powers := [(13, 1), (23, 1), (36, 1), (39, 1), (59, 1), (62, 1)] }, { coefficient := -1, powers := [(19, 1), (23, 1), (36, 1), (39, 1), (44, 1), (49, 1), (59, 1), (62, 2)] }, { coefficient := 1, powers := [(23, 1), (36, 1), (39, 1), (42, 1), (49, 1), (59, 1), (62, 2)] }, { coefficient := -1, powers := [(23, 1), (36, 1), (39, 1), (42, 1), (59, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (24, 1), (38, 1), (39, 1), (42, 1), (59, 1), (62, 1), (64, 1)] }, { coefficient := 1, powers := [(2, 1), (33, 1), (36, 1), (38, 1), (39, 1), (59, 1), (62, 1), (64, 1)] }, { coefficient := -1, powers := [(5, 1), (19, 1), (32, 1), (60, 1), (62, 1)] }, { coefficient := 1, powers := [(8, 1), (23, 1), (33, 1), (36, 1), (39, 1), (59, 1), (62, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (2, 1), (27, 1), (38, 1), (39, 1), (49, 1), (59, 1), (61, 1), (62, 1)] }, { coefficient := 1, powers := [(0, 1), (8, 1), (23, 1), (27, 1), (39, 1), (49, 1), (59, 1), (61, 1), (62, 1)] }, { coefficient := 1, powers := [(2, 1), (19, 1), (27, 1), (38, 1), (39, 1), (49, 1), (59, 1), (61, 1), (62, 1)] }, { coefficient := -1, powers := [(2, 1), (24, 2), (27, 1), (38, 1), (39, 1), (50, 1), (59, 1), (61, 1), (62, 1)] }, { coefficient := 1, powers := [(2, 1), (24, 1), (27, 1), (38, 1), (39, 2), (59, 1), (61, 1), (62, 1)] }, { coefficient := 1, powers := [(2, 1), (24, 1), (27, 1), (38, 1), (39, 1), (49, 1), (59, 1), (61, 1), (62, 1)] }, { coefficient := 1, powers := [(8, 1), (19, 1), (23, 1), (27, 1), (39, 1), (49, 1), (59, 1), (61, 1), (62, 1)] }, { coefficient := 1, powers := [(8, 1), (23, 1), (24, 1), (27, 1), (39, 2), (59, 1), (61, 1), (62, 1)] }, { coefficient := 1, powers := [(8, 1), (23, 1), (24, 1), (27, 1), (39, 1), (49, 1), (59, 1), (61, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (35, 1), (39, 1), (47, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(17, 1), (39, 1), (48, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (6, 1), (13, 1), (19, 1), (39, 1), (59, 1), (60, 1), (62, 1)] }, { coefficient := -1, powers := [(2, 1), (36, 1), (39, 1), (42, 1), (59, 1), (62, 1)] }, { coefficient := 1, powers := [(3, 1), (18, 1), (32, 1), (60, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (6, 1), (9, 1), (19, 1), (39, 1), (59, 1), (60, 1), (62, 1)] }, { coefficient := 1, powers := [(2, 1), (6, 1), (39, 2), (59, 1), (62, 1)] }, { coefficient := -1, powers := [(2, 1), (9, 1), (36, 1), (39, 1), (59, 1), (62, 1)] }, { coefficient := 1, powers := [(2, 1), (24, 1), (36, 1), (39, 1), (50, 1), (59, 1), (62, 1)] }, { coefficient := -1, powers := [(2, 1), (36, 1), (39, 1), (49, 1), (59, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (35, 1), (39, 1), (51, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (35, 1), (39, 1), (53, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (24, 1), (39, 2), (59, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (23, 1), (36, 1), (39, 1), (59, 1), (62, 1)] }, { coefficient := 1, powers := [(3, 1), (23, 1), (24, 1), (39, 1), (59, 1), (62, 1)] }, { coefficient := 1, powers := [(19, 1), (23, 1), (36, 1), (39, 1), (49, 1), (59, 1), (62, 2)] }],
  [{ coefficient := 1, powers := [(23, 1), (39, 1), (56, 1), (62, 1)] }, { coefficient := -1, powers := [(29, 1), (39, 1), (48, 1), (62, 1)] }, { coefficient := 1, powers := [(35, 1), (38, 1), (39, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (2, 1), (38, 1), (39, 1), (49, 1), (59, 1), (61, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 1), (8, 1), (23, 1), (39, 1), (49, 1), (59, 1), (61, 1), (62, 1)] }, { coefficient := -1, powers := [(2, 1), (19, 1), (38, 1), (39, 1), (49, 1), (59, 1), (61, 1), (62, 1)] }, { coefficient := 1, powers := [(2, 1), (24, 2), (38, 1), (39, 1), (50, 1), (59, 1), (61, 1), (62, 1)] }, { coefficient := -1, powers := [(2, 1), (24, 1), (38, 1), (39, 2), (59, 1), (61, 1), (62, 1)] }, { coefficient := -1, powers := [(2, 1), (24, 1), (38, 1), (39, 1), (49, 1), (59, 1), (61, 1), (62, 1)] }, { coefficient := -1, powers := [(8, 1), (19, 1), (23, 1), (39, 1), (49, 1), (59, 1), (61, 1), (62, 1)] }, { coefficient := -1, powers := [(8, 1), (23, 1), (24, 1), (39, 2), (59, 1), (61, 1), (62, 1)] }, { coefficient := -1, powers := [(8, 1), (23, 1), (24, 1), (39, 1), (49, 1), (59, 1), (61, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (39, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (39, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (6, 1), (19, 1), (39, 1), (59, 1), (60, 1), (62, 1)] }, { coefficient := 1, powers := [(2, 1), (36, 1), (39, 1), (59, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (32, 1), (60, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (32, 1), (60, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (23, 1), (39, 1), (59, 1), (62, 1)] }, { coefficient := -1, powers := [(23, 1), (36, 1), (39, 1), (49, 1), (59, 1), (62, 2)] }],
  [{ coefficient := 1, powers := [(39, 1), (48, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (35, 1), (39, 1), (53, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (24, 1), (38, 1), (39, 1), (50, 1), (59, 1), (62, 1)] }, { coefficient := 1, powers := [(2, 1), (38, 1), (39, 1), (49, 1), (59, 1), (62, 1)] }, { coefficient := 1, powers := [(8, 1), (23, 1), (39, 1), (49, 1), (59, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (39, 1), (42, 1), (59, 1), (62, 1)] }, { coefficient := 1, powers := [(8, 1), (23, 1), (39, 1), (42, 1), (59, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (24, 1), (38, 1), (39, 1), (59, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (38, 1), (39, 1), (59, 1), (62, 1)] }, { coefficient := -1, powers := [(8, 1), (23, 1), (39, 1), (59, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(39, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (6, 1), (19, 1), (38, 1), (39, 1), (57, 1), (59, 1), (62, 1)] }, { coefficient := -1, powers := [(5, 1), (32, 1), (39, 1), (56, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (2, 1), (38, 1), (39, 1), (42, 1), (49, 1), (59, 1), (62, 1)] }, { coefficient := 1, powers := [(0, 1), (8, 1), (23, 1), (39, 1), (42, 1), (49, 1), (59, 1), (62, 1)] }, { coefficient := 1, powers := [(2, 1), (19, 1), (38, 1), (39, 1), (42, 1), (49, 1), (59, 1), (62, 1)] }, { coefficient := -1, powers := [(2, 1), (24, 2), (38, 1), (39, 1), (42, 1), (50, 1), (59, 1), (62, 1)] }, { coefficient := 1, powers := [(2, 1), (24, 1), (38, 1), (39, 2), (42, 1), (59, 1), (62, 1)] }, { coefficient := 1, powers := [(2, 1), (24, 1), (38, 1), (39, 1), (42, 1), (49, 1), (59, 1), (62, 1)] }, { coefficient := 1, powers := [(8, 1), (19, 1), (23, 1), (39, 1), (42, 1), (49, 1), (59, 1), (62, 1)] }, { coefficient := 1, powers := [(8, 1), (23, 1), (24, 1), (39, 2), (42, 1), (59, 1), (62, 1)] }, { coefficient := 1, powers := [(8, 1), (23, 1), (24, 1), (39, 1), (42, 1), (49, 1), (59, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (23, 1), (33, 1), (36, 1), (39, 1), (49, 1), (59, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (39, 1), (56, 1), (62, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (39, 1), (62, 1)] }, { coefficient := -1, powers := [(18, 1), (29, 1), (39, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (2, 1), (17, 1), (22, 1), (38, 1), (39, 1), (49, 1), (59, 1), (61, 1), (62, 1)] }, { coefficient := 1, powers := [(0, 1), (2, 1), (38, 1), (39, 2), (59, 1), (62, 1)] }, { coefficient := 1, powers := [(0, 1), (8, 1), (17, 1), (22, 1), (23, 1), (39, 1), (49, 1), (59, 1), (61, 1), (62, 1)] }, { coefficient := 1, powers := [(0, 1), (8, 1), (23, 1), (39, 2), (59, 1), (62, 1)] }, { coefficient := 1, powers := [(2, 1), (3, 1), (30, 1), (38, 1), (39, 1), (59, 1), (62, 1)] }, { coefficient := 1, powers := [(2, 1), (9, 1), (19, 1), (38, 1), (39, 1), (59, 1), (62, 1)] }, { coefficient := 1, powers := [(2, 1), (17, 1), (19, 1), (22, 1), (38, 1), (39, 1), (49, 1), (59, 1), (61, 1), (62, 1)] }, { coefficient := -1, powers := [(2, 1), (17, 1), (22, 1), (24, 2), (38, 1), (39, 1), (50, 1), (59, 1), (61, 1), (62, 1)] }, { coefficient := 1, powers := [(2, 1), (17, 1), (22, 1), (24, 1), (38, 1), (39, 2), (59, 1), (61, 1), (62, 1)] }, { coefficient := 1, powers := [(2, 1), (17, 1), (22, 1), (24, 1), (38, 1), (39, 1), (49, 1), (59, 1), (61, 1), (62, 1)] }, { coefficient := 1, powers := [(2, 1), (19, 1), (24, 1), (38, 1), (39, 1), (50, 1), (59, 1), (62, 1)] }, { coefficient := -1, powers := [(2, 1), (19, 1), (38, 1), (39, 1), (49, 1), (59, 1), (62, 1)] }, { coefficient := 1, powers := [(3, 1), (8, 1), (23, 1), (30, 1), (39, 1), (59, 1), (62, 1)] }, { coefficient := 1, powers := [(8, 1), (9, 1), (19, 1), (23, 1), (39, 1), (59, 1), (62, 1)] }, { coefficient := 1, powers := [(8, 1), (17, 1), (19, 1), (22, 1), (23, 1), (39, 1), (49, 1), (59, 1), (61, 1), (62, 1)] }, { coefficient := 1, powers := [(8, 1), (17, 1), (22, 1), (23, 1), (24, 1), (39, 2), (59, 1), (61, 1), (62, 1)] }, { coefficient := 1, powers := [(8, 1), (17, 1), (22, 1), (23, 1), (24, 1), (39, 1), (49, 1), (59, 1), (61, 1), (62, 1)] }, { coefficient := -1, powers := [(8, 1), (19, 1), (23, 1), (39, 1), (49, 1), (59, 1), (62, 1)] }, { coefficient := -1, powers := [(8, 1), (23, 1), (24, 1), (39, 2), (59, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (19, 1), (35, 1), (39, 1), (53, 1), (62, 1)] }, { coefficient := -1, powers := [(12, 1), (19, 1), (23, 1), (39, 1), (56, 1), (62, 1)] }, { coefficient := 1, powers := [(12, 1), (19, 1), (29, 1), (39, 1), (48, 1), (62, 1)] }, { coefficient := -1, powers := [(12, 1), (19, 1), (35, 1), (38, 1), (39, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (9, 1), (24, 1), (38, 1), (39, 1), (42, 1), (59, 1), (62, 1)] }, { coefficient := -1, powers := [(2, 1), (9, 1), (33, 1), (36, 1), (38, 1), (39, 1), (59, 1), (62, 1)] }, { coefficient := -1, powers := [(8, 1), (9, 1), (23, 1), (33, 1), (36, 1), (39, 1), (59, 1), (62, 1)] }]
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
    ¬ ∀ index : Fin 33,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component10.SelectedLeafB5_6_1.selectedHasNoCommonZero

end Krenn.Component10.SelectedLeafB5_6_1
