import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component20.SelectedLeafB0

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "d11f8a664559cd543241888c0551d9f87db21f325ca7bc68671b17cc4110b157"
def certificateSHA256 : String := "17f74fb5944c1564ff2a41939ffd75ff8f56a71faa9200bd7ebac83d0bc92ff6"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 44 → Fin 639 := ![
  6,
  7,
  15,
  16,
  18,
  21,
  24,
  26,
  27,
  28,
  31,
  35,
  146,
  189,
  190,
  191,
  199,
  215,
  291,
  318,
  348,
  349,
  352,
  353,
  369,
  408,
  466,
  470,
  480,
  485,
  498,
  506,
  513,
  522,
  551,
  558,
  580,
  592,
  621,
  634,
  635,
  636,
  637,
  638
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 44 → SparsePoly (Fin 60) := ![
  [{ coefficient := 1, powers := [(4, 1), (35, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (34, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (22, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(35, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (45, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (43, 1)] }, { coefficient := 1, powers := [(28, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (51, 1)] }, { coefficient := 1, powers := [(24, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (52, 1)] }, { coefficient := 1, powers := [(29, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(45, 1), (49, 1)] }, { coefficient := 1, powers := [(49, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (45, 1), (49, 1)] }, { coefficient := 1, powers := [(13, 1), (28, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (26, 1), (45, 1)] }, { coefficient := 1, powers := [(18, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (43, 1), (52, 1)] }, { coefficient := 1, powers := [(22, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (45, 1)] }, { coefficient := 1, powers := [(4, 1), (34, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (51, 1)] }, { coefficient := 1, powers := [(7, 1), (31, 1)] }, { coefficient := 1, powers := [(11, 1), (27, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (59, 1)] }, { coefficient := 1, powers := [(13, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (59, 1)] }, { coefficient := 1, powers := [(13, 1), (56, 1)] }, { coefficient := 1, powers := [(19, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1), (51, 1)] }, { coefficient := 1, powers := [(21, 1), (43, 1), (51, 1)] }, { coefficient := 1, powers := [(47, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (35, 1), (51, 1)] }, { coefficient := 1, powers := [(7, 1), (35, 1), (40, 1)] }, { coefficient := 1, powers := [(11, 1), (35, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (53, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1)] }, { coefficient := 1, powers := [(13, 1), (29, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (58, 1)] }, { coefficient := 1, powers := [(18, 1), (21, 1), (51, 1)] }, { coefficient := 1, powers := [(18, 1), (21, 1), (55, 1)] }, { coefficient := 1, powers := [(18, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (53, 1)] }, { coefficient := 1, powers := [(29, 1), (41, 1)] }, { coefficient := 1, powers := [(29, 1), (46, 1), (49, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (41, 1), (55, 1)] }, { coefficient := 1, powers := [(21, 1), (49, 1), (55, 1)] }, { coefficient := 1, powers := [(41, 1)] }, { coefficient := 1, powers := [(46, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1), (51, 1)] }, { coefficient := 1, powers := [(21, 1), (51, 1)] }, { coefficient := 1, powers := [(21, 1), (55, 1)] }, { coefficient := 1, powers := [(46, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (36, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1)] }, { coefficient := 1, powers := [(18, 1), (28, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (27, 1), (58, 1)] }, { coefficient := 1, powers := [(3, 1), (31, 1), (55, 1)] }, { coefficient := 1, powers := [(3, 1), (34, 1), (51, 1)] }, { coefficient := 1, powers := [(27, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (27, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (51, 1)] }, { coefficient := 1, powers := [(18, 1), (27, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (43, 1), (52, 1)] }, { coefficient := 1, powers := [(24, 1), (56, 1)] }, { coefficient := 1, powers := [(29, 1), (47, 1)] }, { coefficient := 1, powers := [(35, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (51, 1)] }, { coefficient := 1, powers := [(3, 1), (58, 1)] }, { coefficient := 1, powers := [(20, 1), (51, 1)] }, { coefficient := 1, powers := [(20, 1), (55, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(22, 1), (51, 1)] }, { coefficient := 1, powers := [(22, 1), (55, 1)] }, { coefficient := 1, powers := [(27, 1), (40, 1)] }, { coefficient := 1, powers := [(27, 1), (45, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (58, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (58, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (52, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (37, 1), (58, 1)] }, { coefficient := 1, powers := [(0, 1), (40, 1), (55, 1)] }, { coefficient := 1, powers := [(0, 1), (45, 1), (51, 1)] }, { coefficient := 1, powers := [(40, 1)] }, { coefficient := 1, powers := [(45, 1)] }, { coefficient := 1, powers := [(51, 1)] }, { coefficient := 1, powers := [(55, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (37, 1), (58, 1)] }, { coefficient := 1, powers := [(1, 1), (40, 1), (55, 1)] }, { coefficient := 1, powers := [(1, 1), (45, 1), (51, 1)] }, { coefficient := 1, powers := [(4, 1), (27, 1), (58, 1)] }, { coefficient := 1, powers := [(4, 1), (31, 1), (55, 1)] }, { coefficient := 1, powers := [(4, 1), (34, 1), (51, 1)] }, { coefficient := 1, powers := [(7, 1), (22, 1), (58, 1)] }, { coefficient := 1, powers := [(7, 1), (31, 1), (45, 1)] }, { coefficient := 1, powers := [(7, 1), (34, 1), (40, 1)] }, { coefficient := 1, powers := [(11, 1), (22, 1), (55, 1)] }, { coefficient := 1, powers := [(11, 1), (27, 1), (45, 1)] }, { coefficient := 1, powers := [(11, 1), (34, 1), (37, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1), (51, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1), (40, 1)] }, { coefficient := 1, powers := [(16, 1), (31, 1), (37, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (41, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (47, 1), (53, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (53, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (59, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (47, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(13, 1), (24, 1), (56, 1)] }, { coefficient := 1, powers := [(13, 1), (29, 1), (47, 1)] }, { coefficient := 1, powers := [(13, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (53, 1)] }, { coefficient := 1, powers := [(19, 1), (29, 1), (41, 1)] }, { coefficient := 1, powers := [(19, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1)] }],
  [{ coefficient := 1, powers := [(1, 1)] }],
  [{ coefficient := 1, powers := [(2, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 44 → SparsePoly (Fin 60) := ![
  [{ coefficient := 1, powers := [(5, 1), (27, 1), (53, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (53, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (53, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (27, 1), (41, 1), (58, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1), (41, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (41, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (32, 1), (55, 1), (56, 1)] }, { coefficient := -1, powers := [(7, 1), (32, 1), (45, 1), (56, 1)] }, { coefficient := -1, powers := [(7, 1), (32, 1), (51, 1), (56, 1)] }, { coefficient := -1, powers := [(7, 1), (32, 1), (55, 1), (56, 1)] }, { coefficient := 1, powers := [(11, 1), (32, 1), (37, 1), (56, 1)] }, { coefficient := -1, powers := [(16, 1), (32, 1), (37, 1), (56, 1)] }],
  [{ coefficient := 2, powers := [(21, 1), (29, 1), (51, 1)] }, { coefficient := -1, powers := [(24, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (27, 1), (35, 1), (45, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (27, 1), (35, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (7, 1), (32, 1), (35, 1), (38, 1), (53, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (11, 1), (32, 2), (38, 1), (55, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (11, 1), (32, 1), (35, 1), (38, 1), (53, 1), (55, 1)] }, { coefficient := 1, powers := [(7, 1), (8, 1), (32, 1), (35, 1), (38, 1), (41, 1), (58, 1)] }, { coefficient := 1, powers := [(8, 1), (11, 1), (32, 1), (35, 1), (38, 1), (41, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (7, 1), (8, 1), (21, 1), (32, 1), (35, 1), (51, 1), (53, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (7, 1), (13, 1), (21, 1), (29, 1), (35, 1), (51, 1), (53, 1), (58, 1)] }, { coefficient := -1, powers := [(5, 1), (8, 1), (11, 1), (21, 1), (32, 2), (51, 1), (55, 1), (56, 1)] }, { coefficient := -1, powers := [(5, 1), (8, 1), (11, 1), (21, 1), (32, 1), (35, 1), (51, 1), (53, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (11, 1), (13, 1), (21, 1), (29, 1), (32, 1), (51, 1), (55, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (11, 1), (13, 1), (21, 1), (29, 1), (35, 1), (51, 1), (53, 1), (55, 1)] }, { coefficient := -1, powers := [(7, 1), (8, 2), (21, 1), (32, 1), (35, 1), (41, 1), (51, 1), (58, 1)] }, { coefficient := 1, powers := [(7, 1), (8, 1), (13, 1), (21, 1), (29, 1), (35, 1), (41, 1), (51, 1), (58, 1)] }, { coefficient := -1, powers := [(8, 2), (11, 1), (21, 1), (32, 1), (35, 1), (41, 1), (51, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (11, 1), (13, 1), (21, 1), (29, 1), (35, 1), (41, 1), (51, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (7, 1), (8, 1), (21, 1), (35, 2), (53, 1), (55, 1), (58, 1)] }, { coefficient := -1, powers := [(5, 1), (7, 1), (8, 1), (35, 2), (46, 1), (53, 1), (58, 1)] }, { coefficient := -1, powers := [(5, 1), (8, 1), (11, 1), (21, 1), (32, 1), (35, 1), (55, 2), (56, 1)] }, { coefficient := -1, powers := [(5, 1), (8, 1), (11, 1), (21, 1), (35, 2), (53, 1), (55, 2)] }, { coefficient := -1, powers := [(5, 1), (8, 1), (11, 1), (32, 1), (35, 1), (46, 1), (55, 1), (56, 1)] }, { coefficient := -1, powers := [(5, 1), (8, 1), (11, 1), (35, 2), (46, 1), (53, 1), (55, 1)] }, { coefficient := -1, powers := [(7, 1), (8, 2), (21, 1), (35, 2), (41, 1), (55, 1), (58, 1)] }, { coefficient := -1, powers := [(7, 1), (8, 2), (35, 2), (41, 1), (46, 1), (58, 1)] }, { coefficient := -1, powers := [(8, 2), (11, 1), (21, 1), (35, 2), (41, 1), (55, 2)] }, { coefficient := -1, powers := [(8, 2), (11, 1), (35, 2), (41, 1), (46, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(5, 2), (7, 1), (32, 1), (35, 1), (43, 1), (53, 1), (58, 1)] }, { coefficient := -1, powers := [(5, 2), (11, 1), (32, 2), (43, 1), (55, 1), (56, 1)] }, { coefficient := -1, powers := [(5, 2), (11, 1), (32, 1), (35, 1), (43, 1), (53, 1), (55, 1)] }, { coefficient := -1, powers := [(5, 1), (7, 1), (8, 1), (32, 1), (35, 1), (41, 1), (43, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (7, 1), (13, 1), (24, 1), (35, 1), (43, 1), (53, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (7, 1), (13, 1), (28, 1), (35, 1), (47, 1), (53, 1), (58, 1)] }, { coefficient := -1, powers := [(5, 1), (8, 1), (11, 1), (32, 1), (35, 1), (41, 1), (43, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (11, 1), (13, 1), (24, 1), (32, 1), (43, 1), (55, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (11, 1), (13, 1), (24, 1), (35, 1), (43, 1), (53, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (11, 1), (13, 1), (28, 1), (32, 1), (47, 1), (55, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (11, 1), (13, 1), (28, 1), (35, 1), (47, 1), (53, 1), (55, 1)] }, { coefficient := 1, powers := [(7, 1), (8, 1), (13, 1), (24, 1), (35, 1), (41, 1), (43, 1), (58, 1)] }, { coefficient := 1, powers := [(7, 1), (8, 1), (13, 1), (28, 1), (35, 1), (41, 1), (47, 1), (58, 1)] }, { coefficient := 1, powers := [(8, 1), (11, 1), (13, 1), (24, 1), (35, 1), (41, 1), (43, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (11, 1), (13, 1), (28, 1), (35, 1), (41, 1), (47, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(5, 2), (7, 1), (35, 2), (53, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 2), (11, 1), (32, 1), (35, 1), (55, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 2), (11, 1), (35, 2), (53, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (7, 1), (8, 1), (35, 2), (41, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (8, 1), (11, 1), (35, 2), (41, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (16, 1), (18, 1), (32, 1), (45, 1), (56, 1)] }, { coefficient := -1, powers := [(4, 1), (18, 1), (32, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (16, 1), (34, 1), (53, 1)] }, { coefficient := -1, powers := [(8, 1), (16, 1), (34, 1), (41, 1)] }],
  [{ coefficient := -1, powers := [(19, 1), (21, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (7, 1), (13, 1), (22, 1), (35, 1), (52, 1), (53, 1), (58, 1)] }, { coefficient := -1, powers := [(5, 1), (11, 1), (13, 1), (22, 1), (32, 1), (52, 1), (55, 1), (56, 1)] }, { coefficient := -1, powers := [(5, 1), (11, 1), (13, 1), (22, 1), (35, 1), (52, 1), (53, 1), (55, 1)] }, { coefficient := -1, powers := [(7, 1), (8, 1), (13, 1), (22, 1), (35, 1), (41, 1), (52, 1), (58, 1)] }, { coefficient := -1, powers := [(8, 1), (11, 1), (13, 1), (22, 1), (35, 1), (41, 1), (52, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (20, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (18, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (21, 1), (29, 1)] }],
  [{ coefficient := -1, powers := [(26, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(28, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(5, 2), (7, 1), (32, 1), (35, 1), (53, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 2), (11, 1), (32, 2), (55, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 2), (11, 1), (32, 1), (35, 1), (53, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (7, 1), (8, 1), (32, 1), (35, 1), (41, 1), (58, 1)] }, { coefficient := -1, powers := [(5, 1), (7, 1), (13, 1), (24, 1), (35, 1), (53, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (8, 1), (11, 1), (32, 1), (35, 1), (41, 1), (55, 1)] }, { coefficient := -1, powers := [(5, 1), (11, 1), (13, 1), (24, 1), (32, 1), (55, 1), (56, 1)] }, { coefficient := -1, powers := [(5, 1), (11, 1), (13, 1), (24, 1), (35, 1), (53, 1), (55, 1)] }, { coefficient := -1, powers := [(7, 1), (8, 1), (13, 1), (24, 1), (35, 1), (41, 1), (58, 1)] }, { coefficient := -1, powers := [(8, 1), (11, 1), (13, 1), (24, 1), (35, 1), (41, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (32, 1), (55, 1), (56, 1)] }, { coefficient := -1, powers := [(5, 1), (35, 1), (53, 1), (55, 1)] }, { coefficient := -1, powers := [(8, 1), (35, 1), (41, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (32, 1), (45, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (45, 1), (53, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (41, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (7, 1), (22, 1), (29, 1), (35, 1), (53, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (11, 1), (22, 1), (29, 1), (32, 1), (55, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (11, 1), (22, 1), (29, 1), (35, 1), (53, 1), (55, 1)] }, { coefficient := 1, powers := [(7, 1), (8, 1), (22, 1), (29, 1), (35, 1), (41, 1), (58, 1)] }, { coefficient := 1, powers := [(8, 1), (11, 1), (22, 1), (29, 1), (35, 1), (41, 1), (55, 1)] }, { coefficient := 1, powers := [(29, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (7, 1), (22, 1), (24, 1), (35, 1), (53, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (11, 1), (22, 1), (24, 1), (32, 1), (55, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (11, 1), (22, 1), (24, 1), (35, 1), (53, 1), (55, 1)] }, { coefficient := 1, powers := [(7, 1), (8, 1), (22, 1), (24, 1), (35, 1), (41, 1), (58, 1)] }, { coefficient := 1, powers := [(8, 1), (11, 1), (22, 1), (24, 1), (35, 1), (41, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (7, 1), (8, 1), (22, 1), (32, 1), (35, 1), (53, 1), (58, 1)] }, { coefficient := -1, powers := [(5, 1), (7, 1), (13, 1), (22, 1), (29, 1), (35, 1), (53, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (8, 1), (11, 1), (22, 1), (32, 2), (55, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (8, 1), (11, 1), (22, 1), (32, 1), (35, 1), (53, 1), (55, 1)] }, { coefficient := -1, powers := [(5, 1), (11, 1), (13, 1), (22, 1), (29, 1), (32, 1), (55, 1), (56, 1)] }, { coefficient := -1, powers := [(5, 1), (11, 1), (13, 1), (22, 1), (29, 1), (35, 1), (53, 1), (55, 1)] }, { coefficient := 1, powers := [(7, 1), (8, 2), (22, 1), (32, 1), (35, 1), (41, 1), (58, 1)] }, { coefficient := -1, powers := [(7, 1), (8, 1), (13, 1), (22, 1), (29, 1), (35, 1), (41, 1), (58, 1)] }, { coefficient := 1, powers := [(8, 2), (11, 1), (22, 1), (32, 1), (35, 1), (41, 1), (55, 1)] }, { coefficient := -1, powers := [(8, 1), (11, 1), (13, 1), (22, 1), (29, 1), (35, 1), (41, 1), (55, 1)] }, { coefficient := -2, powers := [(13, 1), (29, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (34, 1), (53, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(47, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (29, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (22, 1), (32, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(19, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (7, 1), (8, 1), (22, 1), (35, 2), (53, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (8, 1), (11, 1), (22, 1), (32, 1), (35, 1), (55, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (8, 1), (11, 1), (22, 1), (35, 2), (53, 1), (55, 1)] }, { coefficient := 1, powers := [(7, 1), (8, 2), (22, 1), (35, 2), (41, 1), (58, 1)] }, { coefficient := 1, powers := [(8, 2), (11, 1), (22, 1), (35, 2), (41, 1), (55, 1)] }, { coefficient := -1, powers := [(19, 1), (29, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (18, 1), (29, 1), (59, 1)] }, { coefficient := -1, powers := [(7, 1), (18, 1), (22, 1), (32, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [(47, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (16, 1), (32, 1), (45, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (16, 1), (32, 1), (45, 1), (56, 1)] }, { coefficient := 1, powers := [(4, 1), (32, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (7, 1), (13, 1), (22, 1), (35, 1), (53, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (11, 1), (13, 1), (22, 1), (32, 1), (55, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (11, 1), (13, 1), (22, 1), (35, 1), (53, 1), (55, 1)] }, { coefficient := 1, powers := [(7, 1), (8, 1), (13, 1), (22, 1), (35, 1), (41, 1), (58, 1)] }, { coefficient := 1, powers := [(8, 1), (11, 1), (13, 1), (22, 1), (35, 1), (41, 1), (55, 1)] }, { coefficient := 1, powers := [(13, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (24, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (16, 1), (32, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (16, 1), (35, 1), (53, 1)] }, { coefficient := 1, powers := [(8, 1), (16, 1), (35, 1), (41, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (7, 1), (32, 1), (34, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (32, 1), (56, 1)] }, { coefficient := -1, powers := [(5, 1), (35, 1), (53, 1)] }, { coefficient := -1, powers := [(8, 1), (35, 1), (41, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (7, 1), (22, 1), (35, 1), (53, 1), (58, 1)] }, { coefficient := -1, powers := [(5, 1), (11, 1), (22, 1), (32, 1), (55, 1), (56, 1)] }, { coefficient := -1, powers := [(5, 1), (11, 1), (22, 1), (35, 1), (53, 1), (55, 1)] }, { coefficient := -1, powers := [(7, 1), (8, 1), (22, 1), (35, 1), (41, 1), (58, 1)] }, { coefficient := -1, powers := [(8, 1), (11, 1), (22, 1), (35, 1), (41, 1), (55, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(3, 1), (18, 1), (29, 1), (46, 1), (51, 1), (59, 1)] }, { coefficient := -1, powers := [(5, 1), (7, 1), (8, 1), (22, 1), (32, 1), (35, 1), (47, 1), (51, 1), (53, 1), (58, 1)] }, { coefficient := -1, powers := [(5, 1), (7, 1), (8, 1), (22, 1), (35, 2), (41, 1), (53, 1), (55, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (7, 1), (13, 1), (22, 1), (29, 1), (35, 1), (47, 1), (51, 1), (53, 1), (58, 1)] }, { coefficient := -1, powers := [(5, 1), (7, 1), (32, 1), (34, 1), (37, 1), (56, 1), (58, 1)] }, { coefficient := -1, powers := [(5, 1), (7, 1), (32, 1), (34, 1), (40, 1), (55, 1), (56, 1)] }, { coefficient := -1, powers := [(5, 1), (7, 1), (32, 1), (34, 1), (45, 1), (51, 1), (56, 1)] }, { coefficient := -1, powers := [(5, 1), (8, 1), (11, 1), (22, 1), (32, 2), (47, 1), (51, 1), (55, 1), (56, 1)] }, { coefficient := -1, powers := [(5, 1), (8, 1), (11, 1), (22, 1), (32, 1), (35, 1), (41, 1), (55, 2), (56, 1)] }, { coefficient := -1, powers := [(5, 1), (8, 1), (11, 1), (22, 1), (32, 1), (35, 1), (47, 1), (51, 1), (53, 1), (55, 1)] }, { coefficient := -1, powers := [(5, 1), (8, 1), (11, 1), (22, 1), (35, 2), (41, 1), (53, 1), (55, 2)] }, { coefficient := 1, powers := [(5, 1), (11, 1), (13, 1), (22, 1), (29, 1), (32, 1), (47, 1), (51, 1), (55, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (11, 1), (13, 1), (22, 1), (29, 1), (35, 1), (47, 1), (51, 1), (53, 1), (55, 1)] }, { coefficient := -1, powers := [(7, 1), (8, 2), (22, 1), (32, 1), (35, 1), (41, 1), (47, 1), (51, 1), (58, 1)] }, { coefficient := -1, powers := [(7, 1), (8, 2), (22, 1), (35, 2), (41, 2), (55, 1), (58, 1)] }, { coefficient := 1, powers := [(7, 1), (8, 1), (13, 1), (22, 1), (29, 1), (35, 1), (41, 1), (47, 1), (51, 1), (58, 1)] }, { coefficient := 1, powers := [(7, 1), (18, 1), (22, 1), (32, 1), (46, 1), (51, 1), (56, 1)] }, { coefficient := -1, powers := [(8, 2), (11, 1), (22, 1), (32, 1), (35, 1), (41, 1), (47, 1), (51, 1), (55, 1)] }, { coefficient := -1, powers := [(8, 2), (11, 1), (22, 1), (35, 2), (41, 2), (55, 2)] }, { coefficient := 1, powers := [(8, 1), (11, 1), (13, 1), (22, 1), (29, 1), (35, 1), (41, 1), (47, 1), (51, 1), (55, 1)] }, { coefficient := -1, powers := [(8, 1), (24, 1), (51, 1), (59, 1)] }, { coefficient := 2, powers := [(13, 1), (29, 1), (47, 1), (51, 1)] }, { coefficient := 1, powers := [(19, 1), (29, 1), (41, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (32, 1), (37, 1), (56, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (40, 1), (55, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (45, 1), (55, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (37, 1), (53, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (40, 1), (53, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (45, 1), (53, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (37, 1), (41, 1), (58, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (40, 1), (41, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (41, 1), (45, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (38, 1), (58, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (46, 1), (52, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (7, 1), (22, 1), (35, 1), (38, 1), (53, 1), (58, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (7, 1), (22, 1), (35, 1), (41, 1), (53, 1), (56, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (7, 1), (22, 1), (35, 1), (47, 1), (53, 2), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (11, 1), (22, 1), (32, 1), (38, 1), (55, 1), (56, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (11, 1), (22, 1), (32, 1), (41, 1), (55, 1), (56, 2)] }, { coefficient := 1, powers := [(5, 1), (11, 1), (22, 1), (32, 1), (47, 1), (53, 1), (55, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (11, 1), (22, 1), (35, 1), (38, 1), (53, 1), (55, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (11, 1), (22, 1), (35, 1), (41, 1), (53, 1), (55, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (11, 1), (22, 1), (35, 1), (47, 1), (53, 2), (55, 1)] }, { coefficient := 1, powers := [(7, 1), (8, 1), (22, 1), (35, 1), (38, 1), (41, 1), (58, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (8, 1), (22, 1), (35, 1), (41, 2), (56, 1), (58, 1)] }, { coefficient := 1, powers := [(7, 1), (8, 1), (22, 1), (35, 1), (41, 1), (47, 1), (53, 1), (58, 1)] }, { coefficient := 1, powers := [(8, 1), (11, 1), (22, 1), (35, 1), (38, 1), (41, 1), (55, 1), (59, 1)] }, { coefficient := 1, powers := [(8, 1), (11, 1), (22, 1), (35, 1), (41, 2), (55, 1), (56, 1)] }, { coefficient := 1, powers := [(8, 1), (11, 1), (22, 1), (35, 1), (41, 1), (47, 1), (53, 1), (55, 1)] }, { coefficient := 1, powers := [(26, 1), (45, 1), (47, 1), (49, 1)] }, { coefficient := 1, powers := [(36, 1), (47, 1), (53, 1), (58, 1)] }, { coefficient := 1, powers := [(38, 1), (59, 1)] }, { coefficient := 1, powers := [(41, 1), (56, 1)] }, { coefficient := 1, powers := [(47, 1), (53, 1)] }]
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
    ¬ ∀ index : Fin 44,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component20.SelectedLeafB0.selectedHasNoCommonZero

end Krenn.Component20.SelectedLeafB0
