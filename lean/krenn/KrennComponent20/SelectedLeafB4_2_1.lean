import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component20.SelectedLeafB4_2_1

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "0a53ec88b75220757b498ab10c0bab523a5c8692a99e676c9ab5fe615f012640"
def certificateSHA256 : String := "9404d624efdb7d14bcf43725b3d79026bb3e8a669a8d5e71cdb4a6c26d48b6a3"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 49 → Fin 645 := ![
  8,
  12,
  17,
  18,
  34,
  36,
  133,
  163,
  168,
  179,
  185,
  186,
  189,
  190,
  191,
  197,
  198,
  257,
  284,
  291,
  307,
  315,
  317,
  348,
  352,
  361,
  462,
  466,
  468,
  471,
  474,
  480,
  506,
  558,
  577,
  578,
  579,
  598,
  599,
  633,
  634,
  635,
  637,
  638,
  639,
  641,
  642,
  643,
  644
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 49 → SparsePoly (Fin 63) := ![
  [{ coefficient := 1, powers := [(7, 1), (32, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(32, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(42, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (28, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (59, 1)] }, { coefficient := 1, powers := [(43, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (25, 1)] }, { coefficient := 1, powers := [(16, 1), (20, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (45, 1)] }, { coefficient := 1, powers := [(13, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (21, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (40, 1)] }, { coefficient := 1, powers := [(19, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (43, 1)] }, { coefficient := 1, powers := [(28, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (51, 1)] }, { coefficient := 1, powers := [(24, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (52, 1)] }, { coefficient := 1, powers := [(29, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(41, 1), (43, 1)] }, { coefficient := 1, powers := [(47, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(43, 1), (53, 1)] }, { coefficient := 1, powers := [(49, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (25, 1), (45, 1)] }, { coefficient := 1, powers := [(16, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (20, 1), (55, 1)] }, { coefficient := 1, powers := [(13, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (26, 1), (45, 1)] }, { coefficient := 1, powers := [(18, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (23, 1), (49, 1)] }, { coefficient := 1, powers := [(16, 1), (32, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (25, 1), (40, 1)] }, { coefficient := 1, powers := [(19, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (49, 1), (55, 1)] }, { coefficient := 1, powers := [(49, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (45, 1)] }, { coefficient := 1, powers := [(4, 1), (34, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (59, 1)] }, { coefficient := 1, powers := [(13, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (23, 1)] }, { coefficient := 1, powers := [(23, 1), (54, 1)] }, { coefficient := 1, powers := [(28, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (47, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1)] }, { coefficient := 1, powers := [(18, 1), (28, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (53, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1)] }, { coefficient := 1, powers := [(13, 1), (29, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (35, 1)] }, { coefficient := 1, powers := [(23, 1), (43, 1)] }, { coefficient := 1, powers := [(28, 1), (43, 1)] }, { coefficient := 1, powers := [(35, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (32, 1)] }, { coefficient := 1, powers := [(23, 1), (49, 1)] }, { coefficient := 1, powers := [(28, 1), (49, 1)] }, { coefficient := 1, powers := [(32, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (25, 1)] }, { coefficient := 1, powers := [(16, 1), (20, 1), (48, 1)] }, { coefficient := 1, powers := [(16, 1), (25, 1), (39, 1)] }, { coefficient := 1, powers := [(16, 1), (30, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (53, 1)] }, { coefficient := 1, powers := [(29, 1), (41, 1)] }, { coefficient := 1, powers := [(29, 1), (46, 1), (49, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (36, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1)] }, { coefficient := 1, powers := [(18, 1), (28, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (51, 1)] }, { coefficient := 1, powers := [(3, 1), (58, 1)] }, { coefficient := 1, powers := [(20, 1), (51, 1)] }, { coefficient := 1, powers := [(20, 1), (55, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1)] }, { coefficient := 1, powers := [(3, 1), (33, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1)] }, { coefficient := 1, powers := [(20, 1), (54, 1)] }, { coefficient := 1, powers := [(25, 1), (42, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (48, 1)] }, { coefficient := 1, powers := [(6, 1), (30, 1)] }, { coefficient := 1, powers := [(9, 1), (25, 1)] }, { coefficient := 1, powers := [(20, 1), (48, 1)] }, { coefficient := 1, powers := [(25, 1), (39, 1)] }, { coefficient := 1, powers := [(30, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (58, 1)] }, { coefficient := 1, powers := [(7, 1), (58, 1)] }, { coefficient := 1, powers := [(11, 1), (45, 1)] }, { coefficient := 1, powers := [(11, 1), (55, 1)] }, { coefficient := 1, powers := [(16, 1), (40, 1)] }, { coefficient := 1, powers := [(16, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (29, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (32, 1), (56, 1)] }, { coefficient := 1, powers := [(3, 1), (35, 1), (53, 1)] }, { coefficient := 1, powers := [(23, 1), (43, 1), (53, 1)] }, { coefficient := 1, powers := [(23, 1), (49, 1), (56, 1)] }, { coefficient := 1, powers := [(29, 1), (43, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (32, 1), (54, 1)] }, { coefficient := 1, powers := [(6, 1), (32, 1), (42, 1)] }, { coefficient := 1, powers := [(14, 1), (23, 1), (49, 1)] }, { coefficient := 1, powers := [(14, 1), (32, 1), (36, 1)] }, { coefficient := 1, powers := [(23, 1), (49, 1), (54, 1)] }, { coefficient := 1, powers := [(28, 1), (42, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (36, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (39, 1), (54, 1)] }, { coefficient := 1, powers := [(0, 1), (42, 1), (48, 1)] }, { coefficient := 1, powers := [(3, 1), (25, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (30, 1), (54, 1)] }, { coefficient := 1, powers := [(3, 1), (33, 1), (48, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1), (57, 1)] }, { coefficient := 1, powers := [(6, 1), (30, 1), (42, 1)] }, { coefficient := 1, powers := [(6, 1), (33, 1), (39, 1)] }, { coefficient := 1, powers := [(9, 1), (20, 1), (54, 1)] }, { coefficient := 1, powers := [(9, 1), (25, 1), (42, 1)] }, { coefficient := 1, powers := [(9, 1), (33, 1), (36, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1), (48, 1)] }, { coefficient := 1, powers := [(14, 1), (25, 1), (39, 1)] }, { coefficient := 1, powers := [(14, 1), (30, 1), (36, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1), (37, 1), (58, 1)] }, { coefficient := 1, powers := [(1, 1), (40, 1), (55, 1)] }, { coefficient := 1, powers := [(1, 1), (45, 1), (51, 1)] }, { coefficient := 1, powers := [(4, 1), (27, 1), (58, 1)] }, { coefficient := 1, powers := [(4, 1), (31, 1), (55, 1)] }, { coefficient := 1, powers := [(4, 1), (34, 1), (51, 1)] }, { coefficient := 1, powers := [(7, 1), (22, 1), (58, 1)] }, { coefficient := 1, powers := [(7, 1), (31, 1), (45, 1)] }, { coefficient := 1, powers := [(7, 1), (34, 1), (40, 1)] }, { coefficient := 1, powers := [(11, 1), (22, 1), (55, 1)] }, { coefficient := 1, powers := [(11, 1), (27, 1), (45, 1)] }, { coefficient := 1, powers := [(11, 1), (34, 1), (37, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1), (51, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1), (40, 1)] }, { coefficient := 1, powers := [(16, 1), (31, 1), (37, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (41, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (47, 1), (53, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (53, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (59, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (47, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(13, 1), (24, 1), (56, 1)] }, { coefficient := 1, powers := [(13, 1), (29, 1), (47, 1)] }, { coefficient := 1, powers := [(13, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (53, 1)] }, { coefficient := 1, powers := [(19, 1), (29, 1), (41, 1)] }, { coefficient := 1, powers := [(19, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1)] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(39, 1)] }],
  [{ coefficient := 1, powers := [(41, 1)] }],
  [{ coefficient := 1, powers := [(54, 1)] }],
  [{ coefficient := 1, powers := [(55, 1)] }],
  [{ coefficient := 1, powers := [(56, 1), (62, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 49 → SparsePoly (Fin 63) := ![
  [{ coefficient := 1, powers := [(5, 1), (22, 1), (56, 1), (58, 1)] }, { coefficient := -1, powers := [(5, 1), (27, 1), (56, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (45, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (40, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (5, 1), (25, 1), (27, 1), (32, 1), (42, 1), (45, 1), (48, 1), (51, 1), (56, 1), (62, 1)] }, { coefficient := -1, powers := [(5, 1), (25, 2), (27, 1), (32, 1), (42, 1), (45, 1), (48, 1), (51, 1), (56, 1), (62, 1)] }, { coefficient := -1, powers := [(5, 1), (25, 1), (27, 1), (32, 1), (42, 1), (48, 1), (51, 1), (56, 1), (62, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (34, 1), (37, 1), (56, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (5, 1), (23, 1), (27, 1), (30, 1), (42, 1), (45, 1), (51, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (5, 1), (23, 1), (27, 1), (51, 1), (56, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (9, 1), (23, 1), (27, 1), (33, 1), (51, 1), (56, 1)] }, { coefficient := -1, powers := [(5, 1), (20, 1), (23, 1), (27, 1), (51, 1), (56, 1), (57, 1)] }, { coefficient := -1, powers := [(5, 1), (23, 1), (25, 1), (27, 1), (30, 1), (42, 1), (45, 1), (51, 1), (56, 1)] }, { coefficient := -1, powers := [(5, 1), (23, 1), (27, 1), (33, 1), (48, 1), (51, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (25, 1), (27, 1), (35, 1), (36, 1), (51, 1), (56, 1), (57, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (16, 1), (31, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (16, 1), (23, 1), (27, 1), (30, 1), (51, 1), (56, 1)] }, { coefficient := -1, powers := [(5, 1), (16, 1), (27, 1), (28, 1), (30, 1), (51, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [(21, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (16, 1), (25, 1), (27, 1), (29, 1), (51, 1), (56, 1), (57, 1), (62, 1)] }, { coefficient := -1, powers := [(8, 1), (24, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (5, 1), (27, 1), (32, 1), (42, 1), (45, 1), (48, 1), (51, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (25, 1), (27, 1), (32, 1), (42, 1), (45, 1), (48, 1), (51, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (27, 1), (32, 1), (42, 1), (48, 1), (51, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [(26, 1), (28, 1), (47, 1)] }],
  [{ coefficient := -1, powers := [(28, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (28, 1), (53, 1)] }, { coefficient := 1, powers := [(24, 1), (25, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (49, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (8, 1), (59, 1)] }, { coefficient := -1, powers := [(8, 1), (20, 1), (59, 1)] }, { coefficient := -1, powers := [(19, 1), (25, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(19, 1), (49, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (28, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (16, 1), (25, 1), (27, 1), (28, 1), (51, 1), (56, 1), (57, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (5, 1), (27, 1), (32, 1), (42, 1), (51, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (25, 1), (27, 1), (32, 1), (42, 1), (51, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (56, 1)] }, { coefficient := -1, powers := [(29, 1), (47, 1)] }, { coefficient := 1, powers := [(35, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(28, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (5, 1), (27, 1), (30, 1), (42, 1), (45, 1), (51, 1), (56, 1)] }, { coefficient := -1, powers := [(0, 1), (5, 1), (27, 1), (51, 1), (56, 1), (57, 1)] }, { coefficient := -1, powers := [(5, 1), (9, 1), (27, 1), (33, 1), (51, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (20, 1), (27, 1), (51, 1), (56, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (25, 1), (27, 1), (30, 1), (42, 1), (45, 1), (51, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (27, 1), (33, 1), (48, 1), (51, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [(24, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (16, 1), (20, 1), (23, 1), (27, 1), (51, 1), (56, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (16, 1), (20, 1), (27, 1), (28, 1), (51, 1), (56, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (16, 1), (23, 1), (25, 1), (27, 1), (51, 1), (56, 2), (57, 1), (62, 1)] }, { coefficient := 1, powers := [(5, 1), (16, 1), (25, 1), (27, 1), (28, 1), (51, 1), (56, 2), (57, 1), (62, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (32, 1), (51, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(29, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (16, 1), (27, 1), (30, 1), (49, 1), (51, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(53, 1)] }],
  [{ coefficient := 1, powers := [(47, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (16, 1), (25, 1), (27, 1), (51, 1), (53, 1), (56, 1), (57, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (16, 1), (20, 1), (27, 1), (51, 1), (56, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (16, 1), (27, 1), (30, 1), (42, 1), (51, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (5, 1), (27, 1), (32, 1), (42, 1), (45, 1), (51, 1), (56, 1)] }, { coefficient := -1, powers := [(5, 1), (25, 1), (27, 1), (32, 1), (42, 1), (45, 1), (51, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(19, 1)] }],
  [{ coefficient := -1, powers := [(47, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (24, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (16, 1), (27, 1), (32, 1), (48, 1), (51, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (16, 1), (27, 1), (32, 1), (42, 1), (51, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (27, 1), (32, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (16, 1), (25, 1), (27, 1), (51, 1), (56, 1), (57, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (16, 1), (27, 1), (30, 1), (51, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (16, 1), (27, 1), (32, 1), (51, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (32, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(5, 1), (32, 1), (37, 1), (56, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(36, 1), (47, 1), (53, 1), (58, 1)] }, { coefficient := 1, powers := [(38, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (5, 1), (16, 1), (25, 1), (27, 1), (32, 1), (42, 1), (45, 1), (51, 1), (56, 1)] }, { coefficient := -1, powers := [(5, 1), (6, 1), (16, 1), (27, 1), (32, 1), (33, 1), (51, 1), (56, 1)] }, { coefficient := -1, powers := [(5, 1), (14, 1), (16, 1), (25, 1), (27, 1), (32, 1), (51, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (16, 1), (25, 2), (27, 1), (32, 1), (42, 1), (45, 1), (51, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (16, 1), (25, 1), (27, 1), (32, 1), (42, 1), (51, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (56, 1)] }, { coefficient := 1, powers := [(8, 1), (28, 1), (43, 1), (58, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1)] }, { coefficient := -1, powers := [(19, 1), (29, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (5, 1), (16, 1), (27, 1), (32, 1), (39, 1), (51, 1), (56, 1)] }, { coefficient := -1, powers := [(5, 1), (9, 1), (16, 1), (20, 1), (27, 1), (32, 1), (51, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (16, 1), (20, 1), (27, 1), (32, 1), (48, 1), (51, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (8, 1), (24, 1), (59, 1)] }, { coefficient := 1, powers := [(1, 1), (5, 1), (32, 1), (40, 1), (56, 1)] }, { coefficient := 1, powers := [(4, 1), (5, 1), (31, 1), (32, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (11, 1), (22, 1), (32, 1), (56, 1)] }, { coefficient := -1, powers := [(5, 1), (11, 1), (27, 1), (32, 1), (56, 1)] }, { coefficient := -1, powers := [(5, 1), (16, 1), (20, 2), (23, 1), (27, 1), (49, 1), (51, 1), (56, 1), (57, 1)] }, { coefficient := -1, powers := [(5, 1), (16, 1), (20, 2), (27, 1), (28, 1), (49, 1), (51, 1), (56, 1), (57, 1)] }, { coefficient := -1, powers := [(5, 1), (16, 1), (20, 1), (23, 1), (25, 1), (27, 1), (49, 1), (51, 1), (56, 2), (57, 1), (62, 1)] }, { coefficient := -1, powers := [(5, 1), (16, 1), (20, 1), (25, 1), (27, 1), (28, 1), (49, 1), (51, 1), (56, 2), (57, 1), (62, 1)] }, { coefficient := -1, powers := [(13, 1), (20, 1), (24, 1), (56, 1)] }, { coefficient := 1, powers := [(13, 1), (20, 1), (29, 1), (47, 1)] }, { coefficient := -1, powers := [(13, 1), (20, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(13, 1), (26, 1), (28, 1), (47, 1)] }, { coefficient := -1, powers := [(19, 1), (20, 1), (24, 1), (49, 1), (52, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (25, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (5, 1), (11, 1), (25, 1), (27, 1), (32, 1), (42, 1), (45, 1), (48, 1), (51, 1), (56, 1)] }, { coefficient := 1, powers := [(3, 1), (5, 1), (16, 1), (25, 1), (27, 1), (32, 1), (51, 1), (56, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (11, 1), (25, 2), (27, 1), (32, 1), (42, 1), (45, 1), (48, 1), (51, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (11, 1), (25, 1), (27, 1), (32, 1), (42, 1), (48, 1), (51, 1), (56, 1)] }, { coefficient := -1, powers := [(5, 1), (11, 1), (32, 1), (34, 1), (37, 1), (56, 1)] }]
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
    ¬ ∀ index : Fin 49,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component20.SelectedLeafB4_2_1.selectedHasNoCommonZero

end Krenn.Component20.SelectedLeafB4_2_1
