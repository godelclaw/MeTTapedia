import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component20.SelectedLeafB5_6

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "499a4422bc00f12c7a59029b26237f0708e08e86aeedf6704ab5892e60c570d4"
def certificateSHA256 : String := "5b1a2371de4bab86ba92b991628fb21533573b74c33de7dec56abf05b9209be1"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 50 → Fin 642 := ![
  6,
  8,
  15,
  24,
  34,
  35,
  146,
  163,
  165,
  186,
  187,
  188,
  193,
  196,
  197,
  198,
  199,
  234,
  284,
  346,
  348,
  349,
  350,
  351,
  352,
  353,
  367,
  369,
  407,
  408,
  466,
  467,
  468,
  480,
  485,
  527,
  557,
  558,
  579,
  580,
  581,
  582,
  622,
  634,
  635,
  636,
  637,
  638,
  640,
  641
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 50 → SparsePoly (Fin 64) := ![
  [{ coefficient := 1, powers := [(4, 1), (35, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (32, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(32, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(35, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (45, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (59, 1)] }, { coefficient := 1, powers := [(43, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (59, 1)] }, { coefficient := 1, powers := [(43, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (40, 1)] }, { coefficient := 1, powers := [(19, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (51, 1)] }, { coefficient := 1, powers := [(23, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (53, 1)] }, { coefficient := 1, powers := [(29, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(28, 1), (40, 1)] }, { coefficient := 1, powers := [(28, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(40, 1), (43, 1)] }, { coefficient := 1, powers := [(43, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(41, 1), (43, 1)] }, { coefficient := 1, powers := [(47, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(43, 1), (53, 1)] }, { coefficient := 1, powers := [(49, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(45, 1), (49, 1)] }, { coefficient := 1, powers := [(49, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (35, 1), (40, 1)] }, { coefficient := 1, powers := [(28, 1), (40, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (20, 1), (55, 1)] }, { coefficient := 1, powers := [(13, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (49, 1)] }, { coefficient := 1, powers := [(20, 1), (49, 1)] }, { coefficient := 1, powers := [(25, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (45, 1)] }, { coefficient := 1, powers := [(4, 1), (34, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (51, 1)] }, { coefficient := 1, powers := [(7, 1), (31, 1)] }, { coefficient := 1, powers := [(11, 1), (27, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (45, 1)] }, { coefficient := 1, powers := [(18, 1), (28, 1), (40, 1)] }, { coefficient := 1, powers := [(18, 1), (28, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (51, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (51, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (59, 1)] }, { coefficient := 1, powers := [(13, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (59, 1)] }, { coefficient := 1, powers := [(13, 1), (56, 1)] }, { coefficient := 1, powers := [(19, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1), (53, 1)] }, { coefficient := 1, powers := [(26, 1), (45, 1), (49, 1)] }, { coefficient := 1, powers := [(53, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1), (51, 1)] }, { coefficient := 1, powers := [(21, 1), (43, 1), (51, 1)] }, { coefficient := 1, powers := [(47, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (32, 1), (55, 1)] }, { coefficient := 1, powers := [(7, 1), (32, 1), (45, 1)] }, { coefficient := 1, powers := [(16, 1), (32, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (35, 1), (51, 1)] }, { coefficient := 1, powers := [(7, 1), (35, 1), (40, 1)] }, { coefficient := 1, powers := [(11, 1), (35, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (53, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1)] }, { coefficient := 1, powers := [(13, 1), (29, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (34, 1)] }, { coefficient := 1, powers := [(6, 1), (31, 1)] }, { coefficient := 1, powers := [(31, 1), (36, 1)] }, { coefficient := 1, powers := [(34, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (35, 1)] }, { coefficient := 1, powers := [(23, 1), (43, 1)] }, { coefficient := 1, powers := [(28, 1), (43, 1)] }, { coefficient := 1, powers := [(35, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (53, 1)] }, { coefficient := 1, powers := [(29, 1), (41, 1)] }, { coefficient := 1, powers := [(29, 1), (46, 1), (49, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (41, 1), (55, 1)] }, { coefficient := 1, powers := [(21, 1), (49, 1), (55, 1)] }, { coefficient := 1, powers := [(41, 1)] }, { coefficient := 1, powers := [(46, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (22, 1), (58, 1)] }, { coefficient := 1, powers := [(6, 1), (31, 1), (45, 1)] }, { coefficient := 1, powers := [(6, 1), (34, 1), (40, 1)] }, { coefficient := 1, powers := [(22, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1)] }, { coefficient := 1, powers := [(6, 1), (58, 1)] }, { coefficient := 1, powers := [(25, 1), (40, 1)] }, { coefficient := 1, powers := [(25, 1), (45, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (51, 1)] }, { coefficient := 1, powers := [(3, 1), (58, 1)] }, { coefficient := 1, powers := [(20, 1), (51, 1)] }, { coefficient := 1, powers := [(20, 1), (55, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(4, 1), (58, 1)] }, { coefficient := 1, powers := [(7, 1), (58, 1)] }, { coefficient := 1, powers := [(11, 1), (45, 1)] }, { coefficient := 1, powers := [(11, 1), (55, 1)] }, { coefficient := 1, powers := [(16, 1), (40, 1)] }, { coefficient := 1, powers := [(16, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (51, 1)] }, { coefficient := 1, powers := [(22, 1), (55, 1)] }, { coefficient := 1, powers := [(27, 1), (40, 1)] }, { coefficient := 1, powers := [(27, 1), (45, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (36, 1), (58, 1)] }, { coefficient := 1, powers := [(0, 1)] }, { coefficient := 1, powers := [(3, 1), (25, 1), (58, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1), (58, 1)] }, { coefficient := 1, powers := [(20, 1)] }, { coefficient := 1, powers := [(25, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (36, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (43, 1), (49, 1)] }, { coefficient := 1, powers := [(3, 1), (25, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1), (59, 1)] }, { coefficient := 1, powers := [(20, 1), (43, 1), (49, 1)] }, { coefficient := 1, powers := [(25, 1), (43, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (38, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (41, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (47, 1), (53, 1)] }, { coefficient := 1, powers := [(21, 1), (43, 1), (53, 1)] }, { coefficient := 1, powers := [(21, 1), (49, 1), (56, 1)] }, { coefficient := 1, powers := [(26, 1), (41, 1), (43, 1)] }, { coefficient := 1, powers := [(26, 1), (47, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (37, 1), (58, 1)] }, { coefficient := 1, powers := [(1, 1), (40, 1), (55, 1)] }, { coefficient := 1, powers := [(1, 1), (45, 1), (51, 1)] }, { coefficient := 1, powers := [(4, 1), (27, 1), (58, 1)] }, { coefficient := 1, powers := [(4, 1), (31, 1), (55, 1)] }, { coefficient := 1, powers := [(4, 1), (34, 1), (51, 1)] }, { coefficient := 1, powers := [(7, 1), (22, 1), (58, 1)] }, { coefficient := 1, powers := [(7, 1), (31, 1), (45, 1)] }, { coefficient := 1, powers := [(7, 1), (34, 1), (40, 1)] }, { coefficient := 1, powers := [(11, 1), (22, 1), (55, 1)] }, { coefficient := 1, powers := [(11, 1), (27, 1), (45, 1)] }, { coefficient := 1, powers := [(11, 1), (34, 1), (37, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1), (51, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1), (40, 1)] }, { coefficient := 1, powers := [(16, 1), (31, 1), (37, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (41, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (47, 1), (53, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (53, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (59, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (47, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(13, 1), (24, 1), (56, 1)] }, { coefficient := 1, powers := [(13, 1), (29, 1), (47, 1)] }, { coefficient := 1, powers := [(13, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (53, 1)] }, { coefficient := 1, powers := [(19, 1), (29, 1), (41, 1)] }, { coefficient := 1, powers := [(19, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (60, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (61, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(40, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(41, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 50 → SparsePoly (Fin 64) := ![
  [{ coefficient := -1, powers := [(5, 1), (22, 1), (51, 1), (53, 1), (58, 1), (63, 1)] }, { coefficient := 1, powers := [(5, 1), (27, 1), (53, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (53, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (53, 1), (55, 1)] }, { coefficient := -1, powers := [(13, 1), (22, 1), (38, 1), (51, 1), (58, 1), (63, 1)] }, { coefficient := 1, powers := [(13, 1), (27, 1), (38, 1), (58, 1)] }, { coefficient := 1, powers := [(13, 1), (31, 1), (38, 1), (55, 1)] }, { coefficient := 1, powers := [(13, 1), (34, 1), (38, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (22, 1), (56, 1), (58, 1)] }, { coefficient := -1, powers := [(5, 1), (27, 1), (56, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (40, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (45, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (55, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (40, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [(21, 1), (29, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (11, 1), (28, 1), (53, 1), (55, 1), (58, 1)] }, { coefficient := 1, powers := [(11, 1), (13, 1), (28, 1), (38, 1), (55, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (11, 1), (31, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (11, 1), (22, 1), (53, 1), (58, 1), (63, 1)] }, { coefficient := -1, powers := [(5, 1), (16, 1), (34, 1), (53, 1)] }, { coefficient := -1, powers := [(11, 1), (13, 1), (22, 1), (38, 1), (58, 1), (63, 1)] }, { coefficient := -1, powers := [(13, 1), (16, 1), (34, 1), (38, 1)] }],
  [{ coefficient := -1, powers := [(19, 1), (21, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (29, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (29, 1), (40, 1), (58, 1), (63, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (51, 1), (58, 1), (63, 1)] }, { coefficient := -1, powers := [(5, 1), (29, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(24, 1), (53, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (6, 1), (18, 1), (29, 1), (58, 1), (59, 1), (61, 1), (63, 1)] }, { coefficient := 1, powers := [(5, 1), (11, 1), (18, 1), (22, 1), (32, 1), (56, 1), (61, 1)] }, { coefficient := 2, powers := [(5, 1), (11, 1), (18, 1), (28, 1), (34, 1), (43, 1), (53, 1), (55, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (16, 1), (18, 1), (27, 1), (32, 1), (56, 1), (61, 1)] }, { coefficient := -1, powers := [(5, 1), (18, 1), (20, 1), (29, 1), (59, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (18, 1), (24, 1), (59, 1), (61, 1), (63, 1)] }, { coefficient := 2, powers := [(11, 1), (13, 1), (18, 1), (28, 1), (34, 1), (38, 1), (43, 1), (55, 1), (61, 1)] }, { coefficient := 1, powers := [(13, 1), (18, 1), (24, 1), (56, 1), (61, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(18, 1), (47, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (18, 1), (20, 1), (38, 1), (59, 1), (61, 1)] }, { coefficient := -1, powers := [(2, 1), (18, 1), (25, 1), (38, 1), (59, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (11, 1), (18, 1), (23, 1), (34, 1), (43, 1), (53, 1), (55, 1), (61, 1)] }, { coefficient := -1, powers := [(5, 1), (11, 1), (18, 1), (31, 1), (35, 1), (36, 1), (53, 1), (55, 1), (61, 1)] }, { coefficient := -1, powers := [(5, 1), (11, 1), (34, 1), (43, 1), (53, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (16, 1), (18, 1), (27, 1), (35, 1), (53, 1), (61, 1)] }, { coefficient := 1, powers := [(11, 1), (13, 1), (18, 1), (23, 1), (34, 1), (38, 1), (43, 1), (55, 1), (61, 1)] }, { coefficient := -1, powers := [(11, 1), (13, 1), (18, 1), (31, 1), (35, 1), (36, 1), (38, 1), (55, 1), (61, 1)] }, { coefficient := -1, powers := [(11, 1), (13, 1), (34, 1), (38, 1), (43, 1), (55, 1)] }, { coefficient := 1, powers := [(13, 1), (16, 1), (18, 1), (27, 1), (35, 1), (38, 1), (61, 1)] }],
  [{ coefficient := 2, powers := [(5, 1), (11, 1), (28, 1), (34, 1), (53, 1), (55, 1)] }, { coefficient := -1, powers := [(5, 1), (29, 1), (49, 1), (58, 1), (63, 1)] }, { coefficient := 2, powers := [(11, 1), (13, 1), (28, 1), (34, 1), (38, 1), (55, 1)] }, { coefficient := 1, powers := [(13, 1), (21, 1), (29, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (26, 1), (60, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (21, 1), (45, 1)] }, { coefficient := -1, powers := [(2, 1), (21, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (21, 1), (29, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (11, 1), (22, 1), (53, 1), (55, 1), (58, 1), (63, 1)] }, { coefficient := -1, powers := [(5, 1), (11, 1), (34, 1), (53, 1), (55, 1)] }, { coefficient := -1, powers := [(11, 1), (13, 1), (22, 1), (38, 1), (55, 1), (58, 1), (63, 1)] }, { coefficient := -1, powers := [(11, 1), (13, 1), (34, 1), (38, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(29, 1), (47, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (38, 1), (43, 1), (45, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (32, 1), (51, 1), (56, 1)] }, { coefficient := -1, powers := [(5, 1), (35, 1), (53, 1), (55, 1)] }, { coefficient := -1, powers := [(13, 1), (35, 1), (38, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (32, 1), (40, 1), (56, 1)] }, { coefficient := -1, powers := [(5, 1), (32, 1), (45, 1), (56, 1)] }, { coefficient := -1, powers := [(5, 1), (32, 1), (55, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (45, 1), (53, 1)] }, { coefficient := 1, powers := [(13, 1), (35, 1), (38, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (20, 1), (38, 1), (59, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (25, 1), (38, 1), (59, 1), (61, 1)] }, { coefficient := -1, powers := [(5, 1), (11, 1), (23, 1), (34, 1), (43, 1), (53, 1), (55, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (11, 1), (31, 1), (35, 1), (36, 1), (53, 1), (55, 1), (61, 1)] }, { coefficient := -1, powers := [(5, 1), (16, 1), (27, 1), (35, 1), (53, 1), (61, 1)] }, { coefficient := -1, powers := [(11, 1), (13, 1), (23, 1), (34, 1), (38, 1), (43, 1), (55, 1), (61, 1)] }, { coefficient := 1, powers := [(11, 1), (13, 1), (31, 1), (35, 1), (36, 1), (38, 1), (55, 1), (61, 1)] }, { coefficient := -1, powers := [(13, 1), (16, 1), (27, 1), (35, 1), (38, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (6, 1), (29, 1), (58, 1), (59, 1), (61, 1), (63, 1)] }, { coefficient := -1, powers := [(5, 1), (11, 1), (22, 1), (32, 1), (56, 1), (61, 1)] }, { coefficient := -2, powers := [(5, 1), (11, 1), (28, 1), (34, 1), (43, 1), (53, 1), (55, 1), (61, 1)] }, { coefficient := -1, powers := [(5, 1), (16, 1), (27, 1), (32, 1), (56, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (20, 1), (29, 1), (59, 1), (61, 1)] }, { coefficient := -1, powers := [(8, 1), (24, 1), (59, 1), (61, 1), (63, 1)] }, { coefficient := -2, powers := [(11, 1), (13, 1), (28, 1), (34, 1), (38, 1), (43, 1), (55, 1), (61, 1)] }, { coefficient := -1, powers := [(13, 1), (24, 1), (56, 1), (61, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (29, 1), (45, 1)] }, { coefficient := -1, powers := [(3, 1), (29, 1), (58, 1)] }, { coefficient := -1, powers := [(6, 1), (29, 1), (58, 1)] }, { coefficient := -1, powers := [(20, 1), (29, 1), (51, 1)] }, { coefficient := -1, powers := [(25, 1), (29, 1), (40, 1)] }, { coefficient := -1, powers := [(25, 1), (29, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (40, 1), (63, 1)] }, { coefficient := 1, powers := [(24, 1), (51, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (47, 1)] }],
  [{ coefficient := -1, powers := [(13, 1), (29, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (31, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (22, 1), (53, 1), (58, 1), (63, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (53, 1)] }, { coefficient := 1, powers := [(13, 1), (22, 1), (38, 1), (58, 1), (63, 1)] }, { coefficient := 1, powers := [(13, 1), (34, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(47, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (11, 1), (35, 1), (45, 1), (53, 1), (55, 1)] }, { coefficient := -1, powers := [(11, 1), (13, 1), (35, 1), (38, 1), (45, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (11, 1), (34, 1), (45, 1), (53, 1), (55, 1)] }, { coefficient := 1, powers := [(11, 1), (13, 1), (34, 1), (38, 1), (45, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(19, 1)] }],
  [{ coefficient := -1, powers := [(19, 1), (29, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (11, 1), (35, 1), (53, 1), (55, 1)] }, { coefficient := 1, powers := [(11, 1), (13, 1), (35, 1), (38, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (29, 1), (59, 1)] }, { coefficient := 1, powers := [(13, 1), (29, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (29, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (27, 1), (32, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (11, 1), (32, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (16, 1), (35, 1), (53, 1)] }, { coefficient := 1, powers := [(13, 1), (16, 1), (35, 1), (38, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (38, 1), (45, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (45, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (45, 1)] }, { coefficient := 1, powers := [(2, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (32, 1), (56, 1)] }, { coefficient := -1, powers := [(5, 1), (35, 1), (53, 1)] }, { coefficient := -1, powers := [(13, 1), (35, 1), (38, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(2, 1), (38, 1), (59, 1)] }, { coefficient := -1, powers := [(2, 1), (47, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (32, 1), (37, 1), (56, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (40, 1), (51, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (40, 1), (55, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (45, 1), (51, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (51, 1), (55, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (37, 1), (53, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (40, 1), (53, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (45, 1), (53, 1), (55, 1)] }, { coefficient := 1, powers := [(13, 1), (35, 1), (37, 1), (38, 1), (58, 1)] }, { coefficient := 1, powers := [(13, 1), (35, 1), (38, 1), (40, 1), (55, 1)] }, { coefficient := 1, powers := [(13, 1), (35, 1), (38, 1), (45, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (20, 1), (38, 1), (45, 1), (59, 1)] }, { coefficient := -1, powers := [(2, 1), (25, 1), (38, 1), (45, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (6, 1), (29, 1), (51, 1), (58, 1), (59, 1), (63, 1)] }, { coefficient := 1, powers := [(5, 1), (11, 1), (22, 1), (32, 1), (51, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (11, 1), (23, 1), (34, 1), (43, 1), (45, 1), (53, 1), (55, 1)] }, { coefficient := 2, powers := [(5, 1), (11, 1), (28, 1), (34, 1), (43, 1), (51, 1), (53, 1), (55, 1)] }, { coefficient := -1, powers := [(5, 1), (11, 1), (31, 1), (35, 1), (36, 1), (45, 1), (53, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (16, 1), (27, 1), (32, 1), (51, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (16, 1), (27, 1), (35, 1), (45, 1), (53, 1)] }, { coefficient := -1, powers := [(5, 1), (20, 1), (29, 1), (51, 1), (59, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (51, 1), (59, 1), (63, 1)] }, { coefficient := 1, powers := [(11, 1), (13, 1), (23, 1), (34, 1), (38, 1), (43, 1), (45, 1), (55, 1)] }, { coefficient := 2, powers := [(11, 1), (13, 1), (28, 1), (34, 1), (38, 1), (43, 1), (51, 1), (55, 1)] }, { coefficient := -1, powers := [(11, 1), (13, 1), (31, 1), (35, 1), (36, 1), (38, 1), (45, 1), (55, 1)] }, { coefficient := 1, powers := [(13, 1), (16, 1), (27, 1), (35, 1), (38, 1), (45, 1)] }, { coefficient := 1, powers := [(13, 1), (24, 1), (51, 1), (56, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (6, 1), (11, 1), (22, 1), (35, 1), (53, 1), (55, 1), (58, 1)] }, { coefficient := -1, powers := [(5, 1), (6, 1), (29, 1), (58, 1), (59, 1)] }, { coefficient := -1, powers := [(5, 1), (7, 1), (22, 1), (35, 1), (53, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (11, 1), (22, 1), (28, 1), (43, 1), (53, 1), (55, 1), (58, 1)] }, { coefficient := 1, powers := [(6, 1), (11, 1), (13, 1), (22, 1), (35, 1), (38, 1), (55, 1), (58, 1)] }, { coefficient := -1, powers := [(7, 1), (13, 1), (22, 1), (35, 1), (38, 1), (58, 1)] }, { coefficient := -1, powers := [(8, 1), (24, 1), (59, 1)] }, { coefficient := 1, powers := [(11, 1), (13, 1), (22, 1), (28, 1), (38, 1), (43, 1), (55, 1), (58, 1)] }, { coefficient := -1, powers := [(13, 1), (24, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (2, 1), (45, 1), (56, 1)] }, { coefficient := -1, powers := [(0, 1), (2, 1), (56, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (19, 1), (29, 1), (45, 1)] }, { coefficient := 1, powers := [(0, 1), (19, 1), (29, 1), (55, 1)] }, { coefficient := -1, powers := [(2, 1), (26, 1), (43, 1), (45, 1)] }, { coefficient := 1, powers := [(2, 1), (56, 1)] }, { coefficient := 1, powers := [(3, 1), (19, 1), (29, 1), (58, 1)] }, { coefficient := 1, powers := [(6, 1), (19, 1), (29, 1), (58, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1)] }, { coefficient := -1, powers := [(18, 1), (29, 1), (43, 1)] }, { coefficient := 1, powers := [(19, 1), (20, 1), (29, 1), (51, 1)] }, { coefficient := 1, powers := [(19, 1), (25, 1), (29, 1), (40, 1)] }, { coefficient := 1, powers := [(19, 1), (25, 1), (29, 1), (45, 1)] }, { coefficient := 1, powers := [(19, 1), (29, 1)] }]
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
    (values : Fin 64 → R) :
    ¬ ∀ index : Fin 50,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component20.SelectedLeafB5_6.selectedHasNoCommonZero

end Krenn.Component20.SelectedLeafB5_6
