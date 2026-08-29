import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component13.SelectedLeafB4_2

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "36fdd5d4137630e37f4c8b3523a8eed4f90e27cf8715df1b99bd9ace1f8beacd"
def certificateSHA256 : String := "0464344b6ffdd4a532ebefcf1a66cc1170b2bede6503f36a6a63da1e51044141"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 48 → Fin 611 := ![
  1,
  4,
  10,
  17,
  19,
  20,
  21,
  22,
  24,
  133,
  152,
  153,
  163,
  171,
  177,
  183,
  188,
  191,
  234,
  264,
  325,
  360,
  361,
  368,
  373,
  376,
  377,
  382,
  431,
  444,
  480,
  483,
  484,
  485,
  489,
  493,
  525,
  544,
  545,
  564,
  573,
  602,
  604,
  605,
  607,
  608,
  609,
  610
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 48 → SparsePoly (Fin 60) := ![
  [{ coefficient := 1, powers := [(5, 1), (31, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(28, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(31, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (43, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (50, 1)] }, { coefficient := 1, powers := [(18, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (51, 1)] }, { coefficient := 1, powers := [(18, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (27, 1)] }, { coefficient := 1, powers := [(27, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (44, 1)] }, { coefficient := 1, powers := [(16, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (38, 1)] }, { coefficient := 1, powers := [(17, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (51, 1)] }, { coefficient := 1, powers := [(27, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (38, 1)] }, { coefficient := 1, powers := [(27, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(41, 1), (51, 1)] }, { coefficient := 1, powers := [(47, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (31, 1), (48, 1)] }, { coefficient := 1, powers := [(5, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (26, 1), (44, 1)] }, { coefficient := 1, powers := [(22, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (23, 1), (38, 1)] }, { coefficient := 1, powers := [(17, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1), (45, 1)] }, { coefficient := 1, powers := [(17, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1), (54, 1)] }, { coefficient := 1, powers := [(17, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (36, 1), (55, 1)] }, { coefficient := 1, powers := [(9, 1), (31, 1), (36, 1)] }, { coefficient := 1, powers := [(13, 1), (28, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (39, 1), (53, 1)] }, { coefficient := 1, powers := [(39, 1)] }, { coefficient := 1, powers := [(44, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (41, 1), (49, 1)] }, { coefficient := 1, powers := [(18, 1), (41, 1), (49, 1)] }, { coefficient := 1, powers := [(41, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (41, 1), (50, 1)] }, { coefficient := 1, powers := [(18, 1), (41, 1), (50, 1)] }, { coefficient := 1, powers := [(18, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1), (46, 1)] }, { coefficient := 1, powers := [(6, 1), (28, 1), (45, 1)] }, { coefficient := 1, powers := [(9, 1), (23, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (28, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (28, 1), (45, 1)] }, { coefficient := 1, powers := [(17, 1), (28, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (22, 1), (54, 1)] }, { coefficient := 1, powers := [(9, 1), (27, 1), (45, 1)] }, { coefficient := 1, powers := [(9, 1), (33, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (45, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1)] }, { coefficient := 1, powers := [(16, 1), (26, 1), (45, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (51, 1)] }, { coefficient := 1, powers := [(8, 1), (30, 1)] }, { coefficient := 1, powers := [(12, 1), (27, 1)] }, { coefficient := 1, powers := [(16, 1), (21, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (33, 1)] }, { coefficient := 1, powers := [(21, 1), (41, 1)] }, { coefficient := 1, powers := [(26, 1), (41, 1)] }, { coefficient := 1, powers := [(33, 1), (34, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (30, 1)] }, { coefficient := 1, powers := [(21, 1), (47, 1)] }, { coefficient := 1, powers := [(26, 1), (47, 1)] }, { coefficient := 1, powers := [(30, 1), (34, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (51, 1)] }, { coefficient := 1, powers := [(27, 1), (39, 1)] }, { coefficient := 1, powers := [(27, 1), (44, 1), (47, 1)] }, { coefficient := 1, powers := [(30, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1), (46, 1)] }, { coefficient := 1, powers := [(6, 1), (28, 1), (43, 1)] }, { coefficient := 1, powers := [(9, 1), (23, 1), (43, 1)] }, { coefficient := 1, powers := [(46, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (41, 1), (50, 1)] }, { coefficient := 1, powers := [(22, 1), (54, 1)] }, { coefficient := 1, powers := [(27, 1), (45, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (40, 1)] }, { coefficient := 1, powers := [(3, 1), (31, 1)] }, { coefficient := 1, powers := [(13, 1), (18, 1)] }, { coefficient := 1, powers := [(18, 1), (52, 1)] }, { coefficient := 1, powers := [(23, 1), (40, 1)] }, { coefficient := 1, powers := [(31, 1), (34, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1)] }, { coefficient := 1, powers := [(6, 1), (28, 1)] }, { coefficient := 1, powers := [(9, 1), (23, 1)] }, { coefficient := 1, powers := [(18, 1), (46, 1)] }, { coefficient := 1, powers := [(23, 1), (37, 1)] }, { coefficient := 1, powers := [(28, 1), (34, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (34, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (41, 1), (47, 1)] }, { coefficient := 1, powers := [(12, 1), (26, 1), (41, 1)] }, { coefficient := 1, powers := [(12, 1), (33, 1), (34, 1)] }, { coefficient := 1, powers := [(17, 1), (21, 1), (47, 1)] }, { coefficient := 1, powers := [(17, 1), (30, 1), (34, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (27, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (30, 1), (54, 1)] }, { coefficient := 1, powers := [(3, 1), (33, 1), (51, 1)] }, { coefficient := 1, powers := [(21, 1), (41, 1), (51, 1)] }, { coefficient := 1, powers := [(21, 1), (47, 1), (54, 1)] }, { coefficient := 1, powers := [(27, 1), (41, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (34, 1), (55, 1)] }, { coefficient := 1, powers := [(0, 1), (37, 1), (52, 1)] }, { coefficient := 1, powers := [(0, 1), (40, 1), (46, 1)] }, { coefficient := 1, powers := [(3, 1), (23, 1), (55, 1)] }, { coefficient := 1, powers := [(3, 1), (28, 1), (52, 1)] }, { coefficient := 1, powers := [(3, 1), (31, 1), (46, 1)] }, { coefficient := 1, powers := [(6, 1), (18, 1), (55, 1)] }, { coefficient := 1, powers := [(6, 1), (28, 1), (40, 1)] }, { coefficient := 1, powers := [(6, 1), (31, 1), (37, 1)] }, { coefficient := 1, powers := [(9, 1), (18, 1), (52, 1)] }, { coefficient := 1, powers := [(9, 1), (23, 1), (40, 1)] }, { coefficient := 1, powers := [(9, 1), (31, 1), (34, 1)] }, { coefficient := 1, powers := [(13, 1), (18, 1), (46, 1)] }, { coefficient := 1, powers := [(13, 1), (23, 1), (37, 1)] }, { coefficient := 1, powers := [(13, 1), (28, 1), (34, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (36, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (39, 1), (54, 1)] }, { coefficient := 1, powers := [(2, 1), (45, 1), (51, 1)] }, { coefficient := 1, powers := [(5, 1), (27, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (51, 1)] }, { coefficient := 1, powers := [(8, 1), (22, 1), (57, 1)] }, { coefficient := 1, powers := [(8, 1), (30, 1), (45, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (39, 1)] }, { coefficient := 1, powers := [(12, 1), (22, 1), (54, 1)] }, { coefficient := 1, powers := [(12, 1), (27, 1), (45, 1)] }, { coefficient := 1, powers := [(12, 1), (33, 1), (36, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (51, 1)] }, { coefficient := 1, powers := [(17, 1), (27, 1), (39, 1)] }, { coefficient := 1, powers := [(17, 1), (30, 1), (36, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (58, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(37, 1)] }],
  [{ coefficient := 1, powers := [(38, 1), (59, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(39, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 48 → SparsePoly (Fin 60) := ![
  [{ coefficient := -1, powers := [(0, 1), (27, 1), (34, 1), (48, 1), (57, 1)] }, { coefficient := -1, powers := [(0, 1), (30, 1), (34, 1), (48, 1), (54, 1)] }, { coefficient := -1, powers := [(0, 1), (33, 1), (34, 1), (48, 1), (51, 1)] }, { coefficient := -1, powers := [(3, 1), (23, 1), (27, 1), (48, 1), (57, 1)] }, { coefficient := -1, powers := [(3, 1), (23, 1), (30, 1), (48, 1), (54, 1)] }, { coefficient := -1, powers := [(3, 1), (23, 1), (33, 1), (48, 1), (51, 1)] }, { coefficient := -1, powers := [(6, 1), (18, 1), (27, 1), (48, 1), (57, 1)] }, { coefficient := -1, powers := [(6, 1), (18, 1), (30, 1), (48, 1), (54, 1)] }, { coefficient := -1, powers := [(6, 1), (18, 1), (33, 1), (48, 1), (51, 1)] }, { coefficient := 1, powers := [(9, 1), (27, 1), (34, 1), (57, 1)] }, { coefficient := 1, powers := [(9, 1), (30, 1), (34, 1), (54, 1)] }, { coefficient := 1, powers := [(9, 1), (33, 1), (34, 1), (51, 1)] }, { coefficient := -1, powers := [(27, 1), (34, 1), (46, 1), (57, 1)] }, { coefficient := -1, powers := [(30, 1), (34, 1), (46, 1), (54, 1)] }, { coefficient := -1, powers := [(33, 1), (34, 1), (46, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (5, 1), (23, 1), (30, 1), (40, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (18, 1), (23, 1), (30, 1), (40, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (18, 1), (23, 1), (30, 1), (52, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (18, 1), (30, 1), (52, 1)] }, { coefficient := 1, powers := [(5, 1), (23, 2), (30, 1), (40, 1), (58, 1)] }, { coefficient := -1, powers := [(12, 1), (18, 1), (22, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(21, 1), (28, 1), (36, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (26, 1), (40, 1), (46, 1), (51, 1)] }, { coefficient := 1, powers := [(3, 1), (26, 1), (28, 1), (51, 1), (52, 1)] }, { coefficient := -1, powers := [(9, 1), (18, 1), (26, 1), (51, 1), (52, 1)] }, { coefficient := -1, powers := [(13, 1), (26, 1), (28, 1), (34, 1), (51, 1)] }, { coefficient := 1, powers := [(18, 1), (26, 1), (40, 1), (46, 1), (51, 1)] }, { coefficient := 1, powers := [(18, 1), (26, 1), (46, 1), (51, 1), (52, 1)] }, { coefficient := 1, powers := [(23, 1), (26, 1), (40, 1), (46, 1), (51, 1)] }, { coefficient := 1, powers := [(26, 1), (28, 1), (34, 1), (40, 1), (51, 1)] }, { coefficient := 1, powers := [(26, 1), (28, 1), (34, 1), (51, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (21, 1), (34, 1), (45, 1), (55, 1)] }, { coefficient := 1, powers := [(0, 1), (21, 1), (40, 1), (45, 1), (46, 1)] }, { coefficient := -1, powers := [(3, 1), (21, 1), (23, 1), (45, 1), (55, 1)] }, { coefficient := -1, powers := [(3, 1), (21, 1), (28, 1), (45, 1), (52, 1)] }, { coefficient := -1, powers := [(6, 1), (18, 1), (21, 1), (45, 1), (55, 1)] }, { coefficient := -1, powers := [(9, 1), (18, 1), (21, 1), (45, 1), (52, 1)] }, { coefficient := -1, powers := [(9, 1), (21, 1), (31, 1), (34, 1), (45, 1)] }, { coefficient := 1, powers := [(18, 1), (21, 1), (40, 1), (45, 1), (46, 1)] }, { coefficient := 1, powers := [(18, 1), (21, 1), (45, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(21, 1), (23, 1), (40, 1), (45, 1), (46, 1)] }, { coefficient := 1, powers := [(21, 1), (31, 1), (34, 1), (45, 1), (46, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (18, 1), (30, 1), (36, 1), (49, 1), (52, 1)] }, { coefficient := 1, powers := [(0, 1), (22, 1), (40, 1), (51, 1)] }, { coefficient := -1, powers := [(0, 1), (30, 1), (36, 1), (40, 1)] }, { coefficient := -2, powers := [(18, 2), (30, 1), (36, 1), (49, 1), (52, 1)] }, { coefficient := 1, powers := [(18, 1), (22, 1), (40, 1), (51, 1)] }, { coefficient := 1, powers := [(18, 1), (22, 1), (51, 1), (52, 1)] }, { coefficient := -1, powers := [(18, 1), (30, 1), (36, 1), (40, 1)] }, { coefficient := -1, powers := [(18, 1), (30, 1), (36, 1), (52, 1)] }, { coefficient := 1, powers := [(22, 1), (23, 1), (40, 1), (51, 1)] }, { coefficient := -1, powers := [(23, 1), (30, 1), (36, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (28, 1), (36, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (12, 1), (13, 1), (33, 1), (34, 1), (58, 1)] }, { coefficient := -1, powers := [(0, 1), (13, 1), (17, 1), (30, 1), (34, 1), (58, 1)] }, { coefficient := -1, powers := [(3, 1), (12, 1), (13, 1), (23, 1), (33, 1), (58, 1)] }, { coefficient := -1, powers := [(3, 1), (13, 1), (17, 1), (23, 1), (30, 1), (58, 1)] }, { coefficient := -1, powers := [(6, 1), (12, 1), (13, 1), (18, 1), (33, 1), (58, 1)] }, { coefficient := -1, powers := [(6, 1), (13, 1), (17, 1), (18, 1), (30, 1), (58, 1)] }, { coefficient := -2, powers := [(6, 1), (17, 1), (18, 1), (30, 1), (49, 1), (52, 1)] }, { coefficient := 1, powers := [(12, 1), (13, 1), (33, 1), (34, 1)] }, { coefficient := -1, powers := [(12, 1), (33, 1), (34, 1), (40, 1)] }, { coefficient := 1, powers := [(13, 1), (17, 1), (30, 1), (34, 1)] }, { coefficient := -2, powers := [(17, 1), (18, 1), (30, 1), (34, 1), (49, 1), (52, 1)] }, { coefficient := -1, powers := [(17, 1), (30, 1), (34, 1), (40, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (9, 1), (12, 1), (33, 1), (34, 1), (58, 1)] }, { coefficient := -1, powers := [(0, 1), (9, 1), (17, 1), (30, 1), (34, 1), (58, 1)] }, { coefficient := -1, powers := [(3, 1), (9, 1), (12, 1), (23, 1), (33, 1), (58, 1)] }, { coefficient := -1, powers := [(3, 1), (9, 1), (17, 1), (23, 1), (30, 1), (58, 1)] }, { coefficient := -1, powers := [(6, 1), (9, 1), (12, 1), (18, 1), (33, 1), (58, 1)] }, { coefficient := -1, powers := [(6, 1), (9, 1), (17, 1), (18, 1), (30, 1), (58, 1)] }, { coefficient := 1, powers := [(9, 1), (12, 1), (33, 1), (34, 1)] }, { coefficient := 1, powers := [(9, 1), (17, 1), (30, 1), (34, 1)] }, { coefficient := -1, powers := [(12, 1), (33, 1), (34, 1), (46, 1)] }, { coefficient := -1, powers := [(17, 1), (30, 1), (34, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (5, 1), (28, 1), (40, 1), (41, 1), (58, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (18, 1), (28, 1), (40, 1), (41, 1), (58, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (18, 1), (28, 1), (41, 1), (52, 1), (58, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (23, 1), (28, 1), (40, 1), (41, 1), (58, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (5, 1), (30, 1), (40, 1), (41, 1), (46, 1), (58, 1)] }, { coefficient := -1, powers := [(0, 1), (12, 1), (22, 1), (40, 1), (41, 1), (46, 1), (49, 1)] }, { coefficient := -1, powers := [(5, 1), (18, 1), (30, 1), (40, 1), (41, 1), (46, 1), (58, 1)] }, { coefficient := -1, powers := [(5, 1), (18, 1), (30, 1), (41, 1), (46, 1), (52, 1), (58, 1)] }, { coefficient := -1, powers := [(5, 1), (23, 1), (30, 1), (40, 1), (41, 1), (46, 1), (58, 1)] }, { coefficient := -1, powers := [(12, 1), (18, 1), (22, 1), (40, 1), (41, 1), (46, 1), (49, 1)] }, { coefficient := -1, powers := [(12, 1), (18, 1), (22, 1), (41, 1), (46, 1), (49, 1), (52, 1)] }, { coefficient := -1, powers := [(12, 1), (22, 1), (23, 1), (40, 1), (41, 1), (46, 1), (49, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (5, 1), (26, 1), (28, 1), (40, 1), (41, 1), (49, 1), (58, 1)] }, { coefficient := -1, powers := [(5, 1), (18, 1), (26, 1), (28, 1), (40, 1), (41, 1), (49, 1), (58, 1)] }, { coefficient := -1, powers := [(5, 1), (18, 1), (26, 1), (28, 1), (41, 1), (49, 1), (52, 1), (58, 1)] }, { coefficient := -1, powers := [(5, 1), (23, 1), (26, 1), (28, 1), (40, 1), (41, 1), (49, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (26, 1), (28, 1), (41, 1), (49, 1), (52, 1)] }],
  [{ coefficient := -2, powers := [(12, 1), (18, 1), (45, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (9, 1), (26, 1), (40, 1), (54, 1)] }, { coefficient := -1, powers := [(9, 1), (18, 1), (26, 1), (40, 1), (54, 1)] }, { coefficient := -1, powers := [(9, 1), (18, 1), (26, 1), (52, 1), (54, 1)] }, { coefficient := -1, powers := [(9, 1), (23, 1), (26, 1), (40, 1), (54, 1)] }],
  [{ coefficient := -2, powers := [(9, 1), (18, 1), (23, 1), (30, 1), (36, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (5, 1), (28, 1), (40, 1), (41, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (18, 1), (28, 1), (40, 1), (41, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (18, 1), (28, 1), (41, 1), (52, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (23, 1), (28, 1), (40, 1), (41, 1), (58, 1)] }, { coefficient := -1, powers := [(5, 1), (28, 1), (41, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (5, 1), (28, 1), (40, 1), (41, 1), (47, 1), (58, 1), (59, 1)] }, { coefficient := -1, powers := [(5, 1), (18, 1), (28, 1), (40, 1), (41, 1), (47, 1), (58, 1), (59, 1)] }, { coefficient := -1, powers := [(5, 1), (18, 1), (28, 1), (41, 1), (47, 1), (52, 1), (58, 1), (59, 1)] }, { coefficient := -1, powers := [(5, 1), (23, 1), (28, 1), (40, 1), (41, 1), (47, 1), (58, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (5, 1), (21, 1), (28, 1), (40, 1), (58, 1)] }, { coefficient := -1, powers := [(0, 1), (5, 1), (26, 1), (28, 1), (40, 1), (58, 1)] }, { coefficient := -1, powers := [(5, 1), (18, 1), (21, 1), (28, 1), (40, 1), (58, 1)] }, { coefficient := -1, powers := [(5, 1), (18, 1), (21, 1), (28, 1), (52, 1), (58, 1)] }, { coefficient := -1, powers := [(5, 1), (18, 1), (26, 1), (28, 1), (40, 1), (58, 1)] }, { coefficient := -1, powers := [(5, 1), (18, 1), (26, 1), (28, 1), (52, 1), (58, 1)] }, { coefficient := -1, powers := [(5, 1), (21, 1), (23, 1), (28, 1), (40, 1), (58, 1)] }, { coefficient := -1, powers := [(5, 1), (21, 1), (28, 1), (52, 1)] }, { coefficient := -1, powers := [(5, 1), (23, 1), (26, 1), (28, 1), (40, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (27, 1), (34, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (30, 1), (34, 1), (54, 1)] }, { coefficient := 1, powers := [(0, 1), (33, 1), (34, 1), (51, 1)] }, { coefficient := 1, powers := [(3, 1), (23, 1), (27, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (23, 1), (30, 1), (54, 1)] }, { coefficient := 1, powers := [(3, 1), (23, 1), (33, 1), (51, 1)] }, { coefficient := 1, powers := [(6, 1), (18, 1), (27, 1), (57, 1)] }, { coefficient := 1, powers := [(6, 1), (18, 1), (30, 1), (54, 1)] }, { coefficient := 1, powers := [(6, 1), (18, 1), (33, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (12, 1), (40, 1), (54, 1)] }, { coefficient := 1, powers := [(12, 1), (18, 1), (40, 1), (54, 1)] }, { coefficient := 1, powers := [(12, 1), (18, 1), (52, 1), (54, 1)] }, { coefficient := 1, powers := [(12, 1), (23, 1), (40, 1), (54, 1)] }],
  [{ coefficient := 2, powers := [(9, 1), (18, 1), (30, 1), (36, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (27, 1), (40, 1), (46, 1)] }, { coefficient := 1, powers := [(9, 1), (18, 1), (27, 1), (52, 1)] }, { coefficient := 1, powers := [(13, 1), (27, 1), (28, 1), (34, 1)] }, { coefficient := -1, powers := [(18, 1), (27, 1), (40, 1), (46, 1)] }, { coefficient := -1, powers := [(18, 1), (27, 1), (46, 1), (52, 1)] }, { coefficient := -1, powers := [(23, 1), (27, 1), (40, 1), (46, 1)] }, { coefficient := -1, powers := [(27, 1), (28, 1), (34, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (22, 1), (34, 1), (55, 1)] }, { coefficient := -1, powers := [(0, 1), (22, 1), (40, 1), (46, 1)] }, { coefficient := 1, powers := [(3, 1), (22, 1), (23, 1), (55, 1)] }, { coefficient := 1, powers := [(3, 1), (22, 1), (28, 1), (52, 1)] }, { coefficient := 1, powers := [(6, 1), (18, 1), (22, 1), (55, 1)] }, { coefficient := 1, powers := [(9, 1), (18, 1), (22, 1), (52, 1)] }, { coefficient := 1, powers := [(9, 1), (22, 1), (31, 1), (34, 1)] }, { coefficient := 1, powers := [(13, 1), (22, 1), (28, 1), (34, 1)] }, { coefficient := -1, powers := [(18, 1), (22, 1), (40, 1), (46, 1)] }, { coefficient := -1, powers := [(18, 1), (22, 1), (46, 1), (52, 1)] }, { coefficient := -1, powers := [(22, 1), (23, 1), (40, 1), (46, 1)] }, { coefficient := -1, powers := [(22, 1), (28, 1), (34, 1), (40, 1)] }, { coefficient := -1, powers := [(22, 1), (31, 1), (34, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (12, 1), (33, 1), (34, 1), (58, 1)] }, { coefficient := 1, powers := [(0, 1), (17, 1), (30, 1), (34, 1), (58, 1)] }, { coefficient := 1, powers := [(3, 1), (12, 1), (23, 1), (33, 1), (58, 1)] }, { coefficient := 1, powers := [(3, 1), (17, 1), (23, 1), (30, 1), (58, 1)] }, { coefficient := 1, powers := [(6, 1), (12, 1), (18, 1), (33, 1), (58, 1)] }, { coefficient := 1, powers := [(6, 1), (17, 1), (18, 1), (30, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (17, 1), (27, 1), (28, 1), (52, 1)] }, { coefficient := 1, powers := [(9, 1), (17, 1), (18, 1), (27, 1), (52, 1)] }, { coefficient := 1, powers := [(13, 1), (17, 1), (27, 1), (28, 1), (34, 1)] }, { coefficient := -1, powers := [(17, 1), (27, 1), (28, 1), (34, 1), (40, 1)] }, { coefficient := -1, powers := [(17, 1), (27, 1), (28, 1), (34, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (5, 1), (26, 1), (28, 1), (40, 1), (51, 1), (58, 1)] }, { coefficient := 1, powers := [(0, 1), (12, 1), (22, 1), (40, 1), (46, 1), (50, 1)] }, { coefficient := 1, powers := [(5, 1), (18, 1), (26, 1), (28, 1), (40, 1), (51, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (18, 1), (26, 1), (28, 1), (51, 1), (52, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (23, 1), (26, 1), (28, 1), (40, 1), (51, 1), (58, 1)] }, { coefficient := -1, powers := [(5, 1), (26, 1), (28, 1), (51, 1), (52, 1)] }, { coefficient := 1, powers := [(12, 1), (18, 1), (22, 1), (40, 1), (46, 1), (50, 1)] }, { coefficient := 1, powers := [(12, 1), (18, 1), (22, 1), (46, 1), (50, 1), (52, 1)] }, { coefficient := 1, powers := [(12, 1), (22, 1), (23, 1), (40, 1), (46, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (5, 1), (30, 1), (40, 1), (46, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (18, 1), (30, 1), (40, 1), (46, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (18, 1), (30, 1), (46, 1), (52, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (23, 1), (30, 1), (40, 1), (46, 1), (58, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (12, 1), (27, 1), (40, 1), (43, 1)] }, { coefficient := -2, powers := [(12, 1), (18, 1), (27, 1), (40, 1), (43, 1)] }, { coefficient := -2, powers := [(12, 1), (18, 1), (27, 1), (43, 1), (52, 1)] }, { coefficient := -2, powers := [(12, 1), (23, 1), (27, 1), (40, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (30, 1), (34, 1)] }, { coefficient := -1, powers := [(30, 1), (34, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (18, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (40, 1), (46, 1), (51, 1)] }, { coefficient := -1, powers := [(3, 1), (28, 1), (51, 1), (52, 1)] }, { coefficient := 1, powers := [(9, 1), (18, 1), (51, 1), (52, 1)] }, { coefficient := 1, powers := [(13, 1), (28, 1), (34, 1), (51, 1)] }, { coefficient := -1, powers := [(18, 1), (40, 1), (46, 1), (51, 1)] }, { coefficient := -1, powers := [(18, 1), (46, 1), (51, 1), (52, 1)] }, { coefficient := -1, powers := [(23, 1), (40, 1), (46, 1), (51, 1)] }, { coefficient := -1, powers := [(28, 1), (34, 1), (40, 1), (51, 1)] }, { coefficient := -1, powers := [(28, 1), (34, 1), (51, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (34, 1), (45, 1), (55, 1)] }, { coefficient := -1, powers := [(0, 1), (40, 1), (45, 1), (46, 1)] }, { coefficient := 1, powers := [(3, 1), (23, 1), (45, 1), (55, 1)] }, { coefficient := 1, powers := [(3, 1), (28, 1), (45, 1), (52, 1)] }, { coefficient := 1, powers := [(6, 1), (18, 1), (45, 1), (55, 1)] }, { coefficient := 1, powers := [(9, 1), (18, 1), (45, 1), (52, 1)] }, { coefficient := 1, powers := [(9, 1), (31, 1), (34, 1), (45, 1)] }, { coefficient := -1, powers := [(18, 1), (40, 1), (45, 1), (46, 1)] }, { coefficient := -1, powers := [(18, 1), (45, 1), (46, 1), (52, 1)] }, { coefficient := -1, powers := [(23, 1), (40, 1), (45, 1), (46, 1)] }, { coefficient := -1, powers := [(31, 1), (34, 1), (45, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (28, 1), (51, 1), (52, 1)] }, { coefficient := 1, powers := [(12, 1), (28, 1), (36, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (5, 1), (28, 1), (40, 1), (54, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (18, 1), (28, 1), (40, 1), (54, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (18, 1), (28, 1), (52, 1), (54, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (23, 1), (28, 1), (40, 1), (54, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (17, 1), (28, 1), (52, 1)] }, { coefficient := -1, powers := [(9, 1), (17, 1), (18, 1), (52, 1)] }, { coefficient := -1, powers := [(13, 1), (17, 1), (28, 1), (34, 1)] }, { coefficient := 1, powers := [(17, 1), (28, 1), (34, 1), (40, 1)] }, { coefficient := 1, powers := [(17, 1), (28, 1), (34, 1), (52, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (12, 1), (27, 1), (40, 1), (45, 1)] }, { coefficient := 2, powers := [(12, 1), (18, 1), (27, 1), (40, 1), (45, 1)] }, { coefficient := 2, powers := [(12, 1), (18, 1), (27, 1), (45, 1), (52, 1)] }, { coefficient := 2, powers := [(12, 1), (23, 1), (27, 1), (40, 1), (45, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (12, 1), (40, 1), (46, 1)] }, { coefficient := -1, powers := [(12, 1), (18, 1), (40, 1), (46, 1)] }, { coefficient := -1, powers := [(12, 1), (18, 1), (46, 1), (52, 1)] }, { coefficient := -1, powers := [(12, 1), (23, 1), (40, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(46, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (5, 1), (30, 1), (40, 1), (54, 1), (58, 1)] }, { coefficient := -1, powers := [(5, 1), (18, 1), (30, 1), (40, 1), (54, 1), (58, 1)] }, { coefficient := -1, powers := [(5, 1), (18, 1), (30, 1), (52, 1), (54, 1), (58, 1)] }, { coefficient := -1, powers := [(5, 1), (23, 1), (30, 1), (40, 1), (54, 1), (58, 1)] }, { coefficient := 2, powers := [(17, 1), (18, 1), (30, 1), (36, 1), (49, 1), (52, 1)] }, { coefficient := 1, powers := [(40, 1)] }],
  [{ coefficient := -1, powers := [(28, 1), (36, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (28, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(0, 1), (34, 1), (55, 1)] }, { coefficient := 1, powers := [(0, 1), (40, 1), (46, 1)] }, { coefficient := -1, powers := [(3, 1), (23, 1), (55, 1)] }, { coefficient := -1, powers := [(3, 1), (28, 1), (52, 1)] }, { coefficient := -1, powers := [(6, 1), (18, 1), (55, 1)] }, { coefficient := -1, powers := [(9, 1), (18, 1), (52, 1)] }, { coefficient := -1, powers := [(9, 1), (31, 1), (34, 1)] }, { coefficient := -1, powers := [(13, 1), (28, 1), (34, 1)] }, { coefficient := 1, powers := [(18, 1), (40, 1), (46, 1)] }, { coefficient := 1, powers := [(18, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(23, 1), (40, 1), (46, 1)] }, { coefficient := 1, powers := [(28, 1), (34, 1), (40, 1)] }, { coefficient := 1, powers := [(31, 1), (34, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (5, 1), (30, 1), (40, 1), (46, 1), (54, 1)] }, { coefficient := -1, powers := [(0, 1), (12, 1), (33, 1), (34, 1), (36, 1), (55, 1)] }, { coefficient := -1, powers := [(0, 1), (17, 1), (30, 1), (34, 1), (36, 1), (55, 1)] }, { coefficient := -1, powers := [(3, 1), (12, 1), (23, 1), (33, 1), (36, 1), (55, 1)] }, { coefficient := -1, powers := [(3, 1), (17, 1), (23, 1), (30, 1), (36, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (18, 1), (30, 1), (40, 1), (46, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (18, 1), (30, 1), (46, 1), (52, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (23, 1), (30, 1), (40, 1), (46, 1), (54, 1)] }, { coefficient := -1, powers := [(6, 1), (12, 1), (18, 1), (33, 1), (36, 1), (55, 1)] }, { coefficient := -1, powers := [(6, 1), (17, 1), (18, 1), (30, 1), (36, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (34, 1), (36, 1), (55, 1), (57, 1)] }, { coefficient := -1, powers := [(0, 1), (36, 1), (40, 1), (46, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (40, 1), (45, 1), (46, 1), (51, 1)] }, { coefficient := 1, powers := [(3, 1), (23, 1), (36, 1), (55, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (28, 1), (36, 1), (52, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (28, 1), (45, 1), (51, 1), (52, 1)] }, { coefficient := 1, powers := [(6, 1), (18, 1), (36, 1), (55, 1), (57, 1)] }, { coefficient := 1, powers := [(9, 1), (18, 1), (36, 1), (52, 1), (57, 1)] }, { coefficient := -1, powers := [(9, 1), (18, 1), (45, 1), (51, 1), (52, 1)] }, { coefficient := 1, powers := [(9, 1), (31, 1), (34, 1), (36, 1), (57, 1)] }, { coefficient := 1, powers := [(13, 1), (28, 1), (34, 1), (36, 1), (57, 1)] }, { coefficient := -1, powers := [(18, 1), (36, 1), (40, 1), (46, 1), (57, 1)] }, { coefficient := -1, powers := [(18, 1), (36, 1), (46, 1), (52, 1), (57, 1)] }, { coefficient := 1, powers := [(18, 1), (40, 1), (45, 1), (46, 1), (51, 1)] }, { coefficient := 1, powers := [(18, 1), (45, 1), (46, 1), (51, 1), (52, 1)] }, { coefficient := -1, powers := [(23, 1), (36, 1), (40, 1), (46, 1), (57, 1)] }, { coefficient := 1, powers := [(23, 1), (40, 1), (45, 1), (46, 1), (51, 1)] }, { coefficient := -1, powers := [(28, 1), (34, 1), (36, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(28, 1), (34, 1), (36, 1), (52, 1), (57, 1)] }, { coefficient := 1, powers := [(28, 1), (34, 1), (45, 1), (51, 1), (52, 1)] }, { coefficient := 1, powers := [(28, 1), (36, 1), (41, 1), (47, 1), (52, 1)] }, { coefficient := -1, powers := [(31, 1), (34, 1), (36, 1), (46, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (5, 1), (23, 1), (30, 1), (40, 1), (54, 1), (58, 1)] }, { coefficient := 1, powers := [(0, 1), (52, 1)] }, { coefficient := 1, powers := [(5, 1), (18, 1), (23, 1), (30, 1), (40, 1), (54, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (18, 1), (23, 1), (30, 1), (52, 1), (54, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (23, 2), (30, 1), (40, 1), (54, 1), (58, 1)] }, { coefficient := 1, powers := [(6, 1), (31, 1)] }, { coefficient := 2, powers := [(12, 1), (18, 1), (27, 1), (45, 1), (52, 1)] }, { coefficient := 1, powers := [(13, 1), (23, 1)] }, { coefficient := -2, powers := [(17, 1), (18, 1), (23, 1), (30, 1), (36, 1), (49, 1), (52, 1)] }, { coefficient := -1, powers := [(23, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (5, 1), (27, 1), (28, 1), (40, 1), (41, 1), (47, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (18, 1), (27, 1), (28, 1), (40, 1), (41, 1), (47, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (18, 1), (27, 1), (28, 1), (41, 1), (47, 1), (52, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (23, 1), (27, 1), (28, 1), (40, 1), (41, 1), (47, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (2, 1), (34, 1), (54, 1), (55, 1)] }, { coefficient := -1, powers := [(0, 1), (2, 1), (40, 1), (46, 1), (54, 1)] }, { coefficient := 1, powers := [(0, 1), (3, 1), (17, 1), (27, 1), (28, 1), (52, 1), (53, 1)] }, { coefficient := 1, powers := [(0, 1), (8, 1), (33, 1), (34, 1), (55, 1)] }, { coefficient := -1, powers := [(0, 1), (8, 1), (33, 1), (40, 1), (46, 1)] }, { coefficient := 1, powers := [(0, 1), (9, 1), (16, 1), (26, 1), (40, 1), (54, 1)] }, { coefficient := -1, powers := [(0, 1), (9, 1), (17, 1), (18, 1), (27, 1), (52, 1), (53, 1)] }, { coefficient := -1, powers := [(0, 1), (13, 1), (17, 1), (27, 1), (28, 1), (34, 1), (53, 1)] }, { coefficient := 1, powers := [(0, 1), (17, 1), (27, 1), (28, 1), (34, 1), (40, 1), (53, 1)] }, { coefficient := 1, powers := [(0, 1), (17, 1), (27, 1), (28, 1), (34, 1), (52, 1), (53, 1)] }, { coefficient := 1, powers := [(0, 1), (17, 1), (27, 1), (34, 1), (55, 1)] }, { coefficient := 1, powers := [(2, 1), (3, 1), (23, 1), (54, 1), (55, 1)] }, { coefficient := 1, powers := [(2, 1), (3, 1), (28, 1), (52, 1), (54, 1)] }, { coefficient := 1, powers := [(2, 1), (6, 1), (18, 1), (54, 1), (55, 1)] }, { coefficient := 1, powers := [(2, 1), (9, 1), (18, 1), (52, 1), (54, 1)] }, { coefficient := 1, powers := [(2, 1), (9, 1), (31, 1), (34, 1), (54, 1)] }, { coefficient := 1, powers := [(2, 1), (13, 1), (28, 1), (34, 1), (54, 1)] }, { coefficient := -1, powers := [(2, 1), (18, 1), (40, 1), (46, 1), (54, 1)] }, { coefficient := -1, powers := [(2, 1), (18, 1), (46, 1), (52, 1), (54, 1)] }, { coefficient := -1, powers := [(2, 1), (23, 1), (40, 1), (46, 1), (54, 1)] }, { coefficient := -1, powers := [(2, 1), (28, 1), (34, 1), (40, 1), (54, 1)] }, { coefficient := -1, powers := [(2, 1), (31, 1), (34, 1), (46, 1), (54, 1)] }, { coefficient := 1, powers := [(3, 1), (8, 1), (23, 1), (33, 1), (55, 1)] }, { coefficient := 1, powers := [(3, 1), (8, 1), (28, 1), (33, 1), (52, 1)] }, { coefficient := 1, powers := [(3, 1), (17, 1), (23, 1), (27, 1), (55, 1)] }, { coefficient := 1, powers := [(3, 1), (17, 1), (27, 1), (28, 1), (52, 1)] }, { coefficient := 1, powers := [(6, 1), (8, 1), (18, 1), (33, 1), (55, 1)] }, { coefficient := 1, powers := [(6, 1), (17, 1), (18, 1), (27, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (9, 1), (18, 1), (33, 1), (52, 1)] }, { coefficient := 1, powers := [(8, 1), (9, 1), (31, 1), (33, 1), (34, 1)] }, { coefficient := 1, powers := [(8, 1), (13, 1), (28, 1), (33, 1), (34, 1)] }, { coefficient := -1, powers := [(8, 1), (18, 1), (33, 1), (40, 1), (46, 1)] }, { coefficient := -1, powers := [(8, 1), (18, 1), (33, 1), (46, 1), (52, 1)] }, { coefficient := -1, powers := [(8, 1), (23, 1), (33, 1), (40, 1), (46, 1)] }, { coefficient := -1, powers := [(8, 1), (28, 1), (33, 1), (34, 1), (40, 1)] }, { coefficient := -1, powers := [(8, 1), (31, 1), (33, 1), (34, 1), (46, 1)] }, { coefficient := 1, powers := [(9, 1), (16, 1), (18, 1), (26, 1), (40, 1), (54, 1)] }, { coefficient := 1, powers := [(9, 1), (16, 1), (18, 1), (26, 1), (52, 1), (54, 1)] }, { coefficient := 1, powers := [(9, 1), (16, 1), (23, 1), (26, 1), (40, 1), (54, 1)] }, { coefficient := 1, powers := [(9, 1), (17, 1), (27, 1), (31, 1), (34, 1)] }, { coefficient := -1, powers := [(17, 1), (27, 1), (31, 1), (34, 1), (46, 1)] }]
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
    (values : Fin 60 → R) :
    ¬ ∀ index : Fin 48,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component13.SelectedLeafB4_2.selectedHasNoCommonZero

end Krenn.Component13.SelectedLeafB4_2
