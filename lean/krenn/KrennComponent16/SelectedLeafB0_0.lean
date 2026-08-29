import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component16.SelectedLeafB0_0

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "c96e6b34d2a2b140f91164402d8ad4b095c85a8354df292862b6c6f1ca12594d"
def certificateSHA256 : String := "83828e33f7082e296a3efa6aa6bd74ce7c82186ad2553754032f224a73977420"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 51 → Fin 668 := ![
  5,
  6,
  7,
  9,
  10,
  12,
  13,
  23,
  32,
  142,
  150,
  151,
  156,
  160,
  172,
  175,
  176,
  274,
  300,
  301,
  302,
  308,
  316,
  362,
  364,
  387,
  440,
  441,
  442,
  448,
  465,
  468,
  479,
  481,
  497,
  503,
  557,
  558,
  571,
  584,
  608,
  609,
  612,
  649,
  660,
  661,
  662,
  663,
  664,
  666,
  667
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 51 → SparsePoly (Fin 62) := ![
  [{ coefficient := 1, powers := [(5, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (34, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (26, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (28, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(34, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (55, 1)] }, { coefficient := 1, powers := [(21, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (26, 1)] }, { coefficient := 1, powers := [(16, 1), (21, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (27, 1)] }, { coefficient := 1, powers := [(16, 1), (21, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (50, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (27, 1)] }, { coefficient := 1, powers := [(19, 1), (21, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(33, 1), (40, 1)] }, { coefficient := 1, powers := [(36, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1), (55, 1)] }, { coefficient := 1, powers := [(55, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (48, 1), (55, 1)] }, { coefficient := 1, powers := [(45, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (45, 1), (53, 1)] }, { coefficient := 1, powers := [(30, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (47, 1)] }, { coefficient := 1, powers := [(4, 1), (36, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (53, 1)] }, { coefficient := 1, powers := [(7, 1), (33, 1)] }, { coefficient := 1, powers := [(11, 1), (28, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (61, 1)] }, { coefficient := 1, powers := [(13, 1), (50, 1)] }, { coefficient := 1, powers := [(20, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (48, 1)] }, { coefficient := 1, powers := [(17, 1), (42, 1)] }, { coefficient := 1, powers := [(17, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (55, 1)] }, { coefficient := 1, powers := [(31, 1), (43, 1)] }, { coefficient := 1, powers := [(34, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (33, 1), (58, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (50, 1)] }, { coefficient := 1, powers := [(20, 1), (33, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (36, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (36, 1), (43, 1)] }, { coefficient := 1, powers := [(13, 1), (36, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (26, 1), (48, 1)] }, { coefficient := 1, powers := [(17, 1), (26, 1), (42, 1)] }, { coefficient := 1, powers := [(17, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1)] }, { coefficient := 1, powers := [(13, 1), (31, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (36, 1)] }, { coefficient := 1, powers := [(6, 1), (33, 1)] }, { coefficient := 1, powers := [(33, 1), (38, 1)] }, { coefficient := 1, powers := [(36, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (37, 1)] }, { coefficient := 1, powers := [(24, 1), (45, 1)] }, { coefficient := 1, powers := [(29, 1), (45, 1)] }, { coefficient := 1, powers := [(37, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (61, 1)] }, { coefficient := 1, powers := [(13, 1), (27, 1), (48, 1)] }, { coefficient := 1, powers := [(13, 1), (58, 1)] }, { coefficient := 1, powers := [(20, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1), (54, 1)] }, { coefficient := 1, powers := [(27, 1), (42, 1)] }, { coefficient := 1, powers := [(27, 1), (47, 1)] }, { coefficient := 1, powers := [(54, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (48, 1), (53, 1)] }, { coefficient := 1, powers := [(42, 1), (45, 1)] }, { coefficient := 1, powers := [(45, 1), (53, 1)] }, { coefficient := 1, powers := [(48, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (61, 1)] }, { coefficient := 1, powers := [(13, 1), (29, 1), (45, 1)] }, { coefficient := 1, powers := [(13, 1), (37, 1), (38, 1)] }, { coefficient := 1, powers := [(20, 1), (34, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (39, 1), (61, 1)] }, { coefficient := 1, powers := [(13, 1), (30, 1), (48, 1)] }, { coefficient := 1, powers := [(13, 1), (37, 1), (39, 1)] }, { coefficient := 1, powers := [(20, 1), (34, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (28, 1), (60, 1)] }, { coefficient := 1, powers := [(3, 1), (33, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (36, 1), (53, 1)] }, { coefficient := 1, powers := [(28, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (31, 1), (61, 1)] }, { coefficient := 1, powers := [(3, 1), (34, 1), (58, 1)] }, { coefficient := 1, powers := [(3, 1), (37, 1), (55, 1)] }, { coefficient := 1, powers := [(24, 1), (45, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (25, 1), (58, 1)] }, { coefficient := 1, powers := [(11, 1), (31, 1), (50, 1)] }, { coefficient := 1, powers := [(11, 1), (37, 1), (40, 1)] }, { coefficient := 1, powers := [(17, 1), (25, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (27, 1), (48, 1)] }, { coefficient := 1, powers := [(11, 1), (58, 1)] }, { coefficient := 1, powers := [(17, 1), (27, 1), (42, 1)] }, { coefficient := 1, powers := [(17, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (45, 1), (54, 1)] }, { coefficient := 1, powers := [(25, 1), (58, 1)] }, { coefficient := 1, powers := [(31, 1), (50, 1)] }, { coefficient := 1, powers := [(37, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1)] }, { coefficient := 1, powers := [(6, 1), (60, 1)] }, { coefficient := 1, powers := [(26, 1), (42, 1)] }, { coefficient := 1, powers := [(26, 1), (47, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(4, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (60, 1)] }, { coefficient := 1, powers := [(11, 1), (47, 1)] }, { coefficient := 1, powers := [(11, 1), (57, 1)] }, { coefficient := 1, powers := [(16, 1), (42, 1)] }, { coefficient := 1, powers := [(16, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (53, 1)] }, { coefficient := 1, powers := [(23, 1), (57, 1)] }, { coefficient := 1, powers := [(28, 1), (42, 1)] }, { coefficient := 1, powers := [(28, 1), (47, 1)] }, { coefficient := 1, powers := [(33, 1), (39, 1)] }, { coefficient := 1, powers := [(36, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1), (58, 1)] }, { coefficient := 1, powers := [(0, 1), (48, 1), (54, 1)] }, { coefficient := 1, powers := [(27, 1), (42, 1), (45, 1)] }, { coefficient := 1, powers := [(27, 1), (48, 1)] }, { coefficient := 1, powers := [(45, 1), (54, 1)] }, { coefficient := 1, powers := [(58, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (39, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (42, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (47, 1), (53, 1)] }, { coefficient := 1, powers := [(42, 1)] }, { coefficient := 1, powers := [(47, 1)] }, { coefficient := 1, powers := [(53, 1)] }, { coefficient := 1, powers := [(57, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (39, 1), (60, 1)] }, { coefficient := 1, powers := [(1, 1), (42, 1), (57, 1)] }, { coefficient := 1, powers := [(1, 1), (47, 1), (53, 1)] }, { coefficient := 1, powers := [(4, 1), (28, 1), (60, 1)] }, { coefficient := 1, powers := [(4, 1), (33, 1), (57, 1)] }, { coefficient := 1, powers := [(4, 1), (36, 1), (53, 1)] }, { coefficient := 1, powers := [(7, 1), (23, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (33, 1), (47, 1)] }, { coefficient := 1, powers := [(7, 1), (36, 1), (42, 1)] }, { coefficient := 1, powers := [(11, 1), (23, 1), (57, 1)] }, { coefficient := 1, powers := [(11, 1), (28, 1), (47, 1)] }, { coefficient := 1, powers := [(11, 1), (36, 1), (39, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1), (53, 1)] }, { coefficient := 1, powers := [(16, 1), (28, 1), (42, 1)] }, { coefficient := 1, powers := [(16, 1), (33, 1), (39, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (40, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (43, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (50, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (37, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (25, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (50, 1)] }, { coefficient := 1, powers := [(8, 1), (37, 1), (43, 1)] }, { coefficient := 1, powers := [(13, 1), (25, 1), (58, 1)] }, { coefficient := 1, powers := [(13, 1), (31, 1), (50, 1)] }, { coefficient := 1, powers := [(13, 1), (37, 1), (40, 1)] }, { coefficient := 1, powers := [(20, 1), (25, 1), (55, 1)] }, { coefficient := 1, powers := [(20, 1), (31, 1), (43, 1)] }, { coefficient := 1, powers := [(20, 1), (34, 1), (40, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1)] }],
  [{ coefficient := 1, powers := [(1, 1)] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(42, 1)] }],
  [{ coefficient := 1, powers := [(43, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 51 → SparsePoly (Fin 62) := ![
  [{ coefficient := -1, powers := [(4, 1), (37, 1), (47, 1), (55, 1)] }, { coefficient := -1, powers := [(4, 1), (37, 1), (53, 1), (55, 1)] }, { coefficient := -1, powers := [(6, 1), (16, 1), (37, 1), (53, 2), (55, 1)] }, { coefficient := 1, powers := [(7, 1), (37, 1), (47, 1), (55, 1)] }, { coefficient := -1, powers := [(7, 1), (37, 1), (53, 1), (55, 1)] }, { coefficient := -1, powers := [(16, 1), (31, 1), (38, 1), (53, 2), (61, 1)] }, { coefficient := -1, powers := [(16, 1), (34, 1), (38, 1), (53, 2), (58, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (7, 1), (23, 1), (31, 1), (60, 2)] }],
  [{ coefficient := -1, powers := [(5, 1), (6, 1), (23, 1), (58, 1), (60, 2)] }, { coefficient := -1, powers := [(5, 1), (23, 1), (26, 1), (47, 1), (58, 1), (60, 1)] }, { coefficient := -1, powers := [(5, 1), (28, 1), (58, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (47, 1), (58, 1)] }, { coefficient := -1, powers := [(5, 1), (33, 1), (53, 1), (58, 1)] }, { coefficient := -1, powers := [(6, 1), (8, 1), (23, 1), (50, 1), (60, 2)] }, { coefficient := -1, powers := [(8, 1), (23, 1), (26, 1), (47, 1), (50, 1), (60, 1)] }, { coefficient := -1, powers := [(8, 1), (28, 1), (50, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (47, 1), (50, 1)] }, { coefficient := -1, powers := [(8, 1), (33, 1), (50, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (23, 1), (31, 1), (47, 1), (50, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (37, 1), (40, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(11, 1), (23, 1), (25, 1), (53, 1), (54, 1)] }, { coefficient := -1, powers := [(16, 1), (24, 1), (28, 1), (40, 1), (53, 1), (60, 1)] }, { coefficient := 1, powers := [(16, 1), (24, 1), (33, 1), (40, 1), (47, 1), (53, 1)] }, { coefficient := 1, powers := [(16, 1), (24, 1), (33, 1), (40, 1), (53, 2)] }],
  [{ coefficient := -1, powers := [(3, 1), (16, 1), (25, 1), (27, 1), (28, 1), (53, 1), (60, 1)] }, { coefficient := 1, powers := [(3, 1), (16, 1), (25, 1), (27, 1), (33, 1), (47, 1), (53, 1)] }, { coefficient := 1, powers := [(3, 1), (16, 1), (25, 1), (27, 1), (33, 1), (53, 2)] }, { coefficient := 1, powers := [(4, 1), (25, 1), (27, 1), (33, 1), (47, 1)] }, { coefficient := 1, powers := [(4, 1), (25, 1), (27, 1), (33, 1), (53, 1)] }, { coefficient := 1, powers := [(6, 1), (7, 1), (23, 1), (25, 1), (27, 1), (60, 2)] }, { coefficient := 1, powers := [(6, 1), (16, 1), (25, 1), (27, 1), (33, 1), (53, 2)] }, { coefficient := 1, powers := [(7, 1), (23, 1), (25, 1), (26, 1), (27, 1), (47, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (25, 1), (27, 1), (28, 1), (60, 1)] }, { coefficient := -1, powers := [(7, 1), (25, 1), (27, 1), (33, 1), (47, 1)] }, { coefficient := 1, powers := [(7, 1), (25, 1), (27, 1), (33, 1), (53, 1)] }, { coefficient := 2, powers := [(11, 1), (22, 1), (23, 1), (31, 1), (53, 1)] }, { coefficient := 1, powers := [(11, 1), (25, 1), (27, 1), (33, 1), (39, 1)] }, { coefficient := 1, powers := [(11, 1), (30, 1), (33, 1), (40, 1)] }, { coefficient := 1, powers := [(16, 1), (25, 1), (27, 1), (33, 1), (38, 1), (53, 2)] }, { coefficient := -1, powers := [(16, 1), (25, 1), (27, 1), (33, 1), (39, 1)] }, { coefficient := 1, powers := [(16, 1), (25, 1), (27, 1), (36, 1), (38, 1), (53, 2)] }, { coefficient := -1, powers := [(16, 1), (30, 1), (33, 1), (40, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (16, 1), (19, 1), (28, 1), (50, 1), (53, 1), (60, 1)] }, { coefficient := 1, powers := [(3, 1), (16, 1), (19, 1), (33, 1), (47, 1), (50, 1), (53, 1)] }, { coefficient := 1, powers := [(3, 1), (16, 1), (19, 1), (33, 1), (50, 1), (53, 2)] }, { coefficient := 1, powers := [(11, 1), (19, 1), (23, 1), (50, 1), (53, 1)] }, { coefficient := 1, powers := [(16, 1), (19, 1), (36, 1), (38, 1), (50, 1), (53, 2)] }],
  [{ coefficient := -1, powers := [(5, 1), (11, 1), (33, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (16, 1), (33, 1), (58, 1)] }, { coefficient := -1, powers := [(8, 1), (11, 1), (33, 1), (50, 1)] }, { coefficient := 1, powers := [(8, 1), (16, 1), (33, 1), (50, 1)] }, { coefficient := 1, powers := [(11, 1), (20, 1), (33, 1), (40, 1)] }, { coefficient := -1, powers := [(16, 1), (20, 1), (33, 1), (40, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (19, 1), (23, 1), (30, 1), (50, 1), (60, 1)] }, { coefficient := 1, powers := [(17, 1), (19, 1), (23, 1), (25, 1), (47, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (23, 1), (34, 1), (48, 1), (53, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (23, 1), (34, 1), (48, 1), (53, 1)] }],
  [{ coefficient := 2, powers := [(13, 1), (23, 1), (31, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (23, 1), (30, 1), (50, 1), (60, 1)] }, { coefficient := -1, powers := [(17, 1), (23, 1), (25, 1), (47, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (13, 1), (37, 1), (47, 1)] }, { coefficient := -1, powers := [(4, 1), (13, 1), (37, 1), (53, 1)] }, { coefficient := -1, powers := [(6, 1), (13, 1), (16, 1), (37, 1), (53, 2)] }, { coefficient := 1, powers := [(7, 1), (13, 1), (37, 1), (47, 1)] }, { coefficient := -1, powers := [(7, 1), (13, 1), (37, 1), (53, 1)] }, { coefficient := -1, powers := [(13, 1), (16, 1), (37, 1), (38, 1), (53, 2)] }],
  [{ coefficient := 1, powers := [(3, 1), (5, 1), (16, 1), (28, 1), (37, 1), (53, 1), (60, 1)] }, { coefficient := -1, powers := [(3, 1), (5, 1), (16, 1), (33, 1), (37, 1), (47, 1), (53, 1)] }, { coefficient := -1, powers := [(3, 1), (5, 1), (16, 1), (33, 1), (37, 1), (53, 2)] }, { coefficient := -1, powers := [(3, 1), (16, 1), (20, 1), (25, 1), (28, 1), (53, 1), (60, 1)] }, { coefficient := 1, powers := [(3, 1), (16, 1), (20, 1), (25, 1), (33, 1), (47, 1), (53, 1)] }, { coefficient := 1, powers := [(3, 1), (16, 1), (20, 1), (25, 1), (33, 1), (53, 2)] }, { coefficient := -1, powers := [(4, 1), (5, 1), (33, 1), (37, 1), (47, 1)] }, { coefficient := -1, powers := [(4, 1), (5, 1), (33, 1), (37, 1), (53, 1)] }, { coefficient := -1, powers := [(5, 1), (6, 1), (7, 1), (23, 1), (37, 1), (60, 2)] }, { coefficient := -1, powers := [(5, 1), (6, 1), (16, 1), (33, 1), (37, 1), (53, 2)] }, { coefficient := -1, powers := [(5, 1), (7, 1), (23, 1), (26, 1), (37, 1), (47, 1), (60, 1)] }, { coefficient := -1, powers := [(5, 1), (7, 1), (28, 1), (37, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (7, 1), (33, 1), (37, 1), (47, 1)] }, { coefficient := -1, powers := [(5, 1), (7, 1), (33, 1), (37, 1), (53, 1)] }, { coefficient := -1, powers := [(5, 1), (11, 1), (23, 1), (37, 1), (53, 1)] }, { coefficient := -1, powers := [(5, 1), (11, 1), (33, 1), (37, 1), (39, 1)] }, { coefficient := 1, powers := [(5, 1), (16, 1), (28, 1), (37, 1), (38, 1), (53, 1), (60, 1)] }, { coefficient := -1, powers := [(5, 1), (16, 1), (33, 1), (37, 1), (38, 1), (47, 1), (53, 1)] }, { coefficient := -2, powers := [(5, 1), (16, 1), (33, 1), (37, 1), (38, 1), (53, 2)] }, { coefficient := 1, powers := [(5, 1), (16, 1), (33, 1), (37, 1), (39, 1)] }, { coefficient := -1, powers := [(5, 1), (16, 1), (36, 1), (37, 1), (38, 1), (53, 2)] }, { coefficient := 1, powers := [(6, 1), (7, 1), (20, 1), (23, 1), (25, 1), (60, 2)] }, { coefficient := 1, powers := [(7, 1), (20, 1), (23, 1), (25, 1), (26, 1), (47, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (20, 1), (25, 1), (28, 1), (60, 1)] }, { coefficient := -1, powers := [(7, 1), (20, 1), (25, 1), (33, 1), (47, 1)] }, { coefficient := 1, powers := [(7, 1), (20, 1), (25, 1), (33, 1), (53, 1)] }, { coefficient := 1, powers := [(11, 1), (20, 1), (23, 1), (25, 1), (53, 1)] }, { coefficient := 1, powers := [(11, 1), (20, 1), (25, 1), (33, 1), (39, 1)] }, { coefficient := -1, powers := [(16, 1), (20, 1), (25, 1), (28, 1), (38, 1), (53, 1), (60, 1)] }, { coefficient := 1, powers := [(16, 1), (20, 1), (25, 1), (33, 1), (38, 1), (47, 1), (53, 1)] }, { coefficient := 1, powers := [(16, 1), (20, 1), (25, 1), (33, 1), (38, 1), (53, 2)] }, { coefficient := -1, powers := [(16, 1), (20, 1), (25, 1), (33, 1), (39, 1)] }, { coefficient := 1, powers := [(16, 1), (20, 1), (25, 1), (36, 1), (38, 1), (53, 2)] }],
  [{ coefficient := 1, powers := [(5, 1), (16, 1), (28, 1), (29, 1), (53, 1), (60, 1)] }, { coefficient := -1, powers := [(5, 1), (16, 1), (29, 1), (33, 1), (47, 1), (53, 1)] }, { coefficient := -1, powers := [(5, 1), (16, 1), (29, 1), (33, 1), (53, 2)] }],
  [{ coefficient := -1, powers := [(7, 1), (13, 1), (23, 1), (27, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(53, 1)] }],
  [{ coefficient := 1, powers := [(53, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (31, 1), (33, 1), (47, 1)] }, { coefficient := -1, powers := [(4, 1), (31, 1), (33, 1), (53, 1)] }, { coefficient := -1, powers := [(6, 1), (16, 1), (31, 1), (33, 1), (53, 2)] }, { coefficient := -1, powers := [(7, 1), (23, 1), (26, 1), (31, 1), (47, 1), (60, 1)] }, { coefficient := -1, powers := [(7, 1), (28, 1), (31, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (31, 1), (33, 1), (47, 1)] }, { coefficient := -1, powers := [(7, 1), (31, 1), (33, 1), (53, 1)] }, { coefficient := -1, powers := [(11, 1), (23, 1), (31, 1), (53, 1)] }, { coefficient := -1, powers := [(11, 1), (31, 1), (33, 1), (39, 1)] }, { coefficient := -1, powers := [(16, 1), (31, 1), (33, 1), (38, 1), (53, 2)] }, { coefficient := 1, powers := [(16, 1), (31, 1), (33, 1), (39, 1)] }],
  [{ coefficient := -2, powers := [(13, 1), (22, 1), (23, 1), (31, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (16, 1), (20, 1), (28, 1), (53, 1), (60, 1)] }, { coefficient := -1, powers := [(3, 1), (16, 1), (20, 1), (33, 1), (47, 1), (53, 1)] }, { coefficient := -1, powers := [(3, 1), (16, 1), (20, 1), (33, 1), (53, 2)] }, { coefficient := -1, powers := [(6, 1), (7, 1), (20, 1), (23, 1), (60, 2)] }, { coefficient := -1, powers := [(7, 1), (20, 1), (23, 1), (26, 1), (47, 1), (60, 1)] }, { coefficient := -1, powers := [(7, 1), (20, 1), (28, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (20, 1), (33, 1), (47, 1)] }, { coefficient := -1, powers := [(7, 1), (20, 1), (33, 1), (53, 1)] }, { coefficient := -1, powers := [(11, 1), (20, 1), (23, 1), (53, 1)] }, { coefficient := -1, powers := [(11, 1), (20, 1), (33, 1), (39, 1)] }, { coefficient := 1, powers := [(16, 1), (20, 1), (28, 1), (38, 1), (53, 1), (60, 1)] }, { coefficient := -1, powers := [(16, 1), (20, 1), (33, 1), (38, 1), (47, 1), (53, 1)] }, { coefficient := -1, powers := [(16, 1), (20, 1), (33, 1), (38, 1), (53, 2)] }, { coefficient := 1, powers := [(16, 1), (20, 1), (33, 1), (39, 1)] }, { coefficient := -1, powers := [(16, 1), (20, 1), (36, 1), (38, 1), (53, 2)] }],
  [{ coefficient := -1, powers := [(4, 1), (34, 1), (47, 1)] }, { coefficient := -1, powers := [(4, 1), (34, 1), (53, 1)] }, { coefficient := -1, powers := [(6, 1), (16, 1), (34, 1), (53, 2)] }, { coefficient := -1, powers := [(16, 1), (34, 1), (38, 1), (53, 2)] }],
  [{ coefficient := 1, powers := [(4, 1), (37, 1), (47, 1)] }, { coefficient := 1, powers := [(4, 1), (37, 1), (53, 1)] }, { coefficient := 1, powers := [(6, 1), (16, 1), (37, 1), (53, 2)] }, { coefficient := -1, powers := [(7, 1), (37, 1), (47, 1)] }, { coefficient := 1, powers := [(7, 1), (37, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (23, 1), (34, 1), (53, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (16, 1), (28, 1), (50, 1), (53, 1), (60, 1)] }, { coefficient := -1, powers := [(3, 1), (16, 1), (33, 1), (47, 1), (50, 1), (53, 1)] }, { coefficient := -1, powers := [(3, 1), (16, 1), (33, 1), (50, 1), (53, 2)] }, { coefficient := -1, powers := [(11, 1), (23, 1), (50, 1), (53, 1)] }, { coefficient := -1, powers := [(16, 1), (36, 1), (38, 1), (50, 1), (53, 2)] }],
  [{ coefficient := 1, powers := [(16, 1), (53, 2)] }],
  [{ coefficient := -1, powers := [(5, 1), (16, 1), (28, 1), (53, 1), (55, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (16, 1), (33, 1), (47, 1), (53, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (16, 1), (33, 1), (53, 2), (55, 1)] }, { coefficient := 1, powers := [(13, 1), (16, 1), (28, 1), (40, 1), (53, 1), (60, 1)] }, { coefficient := -1, powers := [(13, 1), (16, 1), (33, 1), (40, 1), (47, 1), (53, 1)] }, { coefficient := -1, powers := [(13, 1), (16, 1), (33, 1), (40, 1), (53, 2)] }],
  [{ coefficient := 1, powers := [(3, 1), (16, 1), (25, 1), (28, 1), (53, 1), (60, 1)] }, { coefficient := -1, powers := [(3, 1), (16, 1), (25, 1), (33, 1), (47, 1), (53, 1)] }, { coefficient := -1, powers := [(3, 1), (16, 1), (25, 1), (33, 1), (53, 2)] }, { coefficient := -1, powers := [(4, 1), (25, 1), (33, 1), (47, 1)] }, { coefficient := -1, powers := [(4, 1), (25, 1), (33, 1), (53, 1)] }, { coefficient := -1, powers := [(6, 1), (7, 1), (23, 1), (25, 1), (60, 2)] }, { coefficient := -1, powers := [(6, 1), (16, 1), (25, 1), (33, 1), (53, 2)] }, { coefficient := -1, powers := [(7, 1), (23, 1), (25, 1), (26, 1), (47, 1), (60, 1)] }, { coefficient := -1, powers := [(7, 1), (25, 1), (28, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (25, 1), (33, 1), (47, 1)] }, { coefficient := -1, powers := [(7, 1), (25, 1), (33, 1), (53, 1)] }, { coefficient := -1, powers := [(11, 1), (23, 1), (25, 1), (53, 1)] }, { coefficient := -1, powers := [(11, 1), (25, 1), (33, 1), (39, 1)] }, { coefficient := -1, powers := [(16, 1), (25, 1), (33, 1), (38, 1), (53, 2)] }, { coefficient := 1, powers := [(16, 1), (25, 1), (33, 1), (39, 1)] }, { coefficient := -1, powers := [(16, 1), (25, 1), (36, 1), (38, 1), (53, 2)] }],
  [{ coefficient := 1, powers := [(13, 1), (17, 1), (23, 1), (25, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (13, 1), (23, 1), (25, 1), (27, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(16, 1), (28, 1), (40, 1), (53, 1), (60, 1)] }, { coefficient := 1, powers := [(16, 1), (33, 1), (40, 1), (47, 1), (53, 1)] }, { coefficient := 1, powers := [(16, 1), (33, 1), (40, 1), (53, 2)] }],
  [{ coefficient := -1, powers := [(11, 1), (33, 1), (40, 1)] }, { coefficient := 1, powers := [(16, 1), (33, 1), (40, 1)] }],
  [{ coefficient := -1, powers := [(16, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (16, 1), (28, 1), (53, 1), (60, 1)] }, { coefficient := -1, powers := [(5, 1), (16, 1), (33, 1), (47, 1), (53, 1)] }, { coefficient := -1, powers := [(5, 1), (16, 1), (33, 1), (53, 2)] }],
  [{ coefficient := -1, powers := [(13, 1), (23, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (23, 1), (34, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (13, 1), (23, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (13, 1), (23, 1), (31, 1), (50, 1), (60, 1)] }, { coefficient := -1, powers := [(7, 1), (13, 1), (23, 1), (37, 1), (40, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (23, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(28, 1)] }],
  [{ coefficient := 1, powers := [(11, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (13, 1), (23, 1), (25, 1), (60, 1)] }, { coefficient := 1, powers := [(11, 1), (13, 1), (23, 1), (25, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (16, 1), (33, 1), (53, 1)] }, { coefficient := 1, powers := [(4, 1), (33, 1)] }, { coefficient := -1, powers := [(11, 1), (28, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(3, 1), (16, 1), (28, 1), (53, 1), (60, 1)] }, { coefficient := 1, powers := [(3, 1), (16, 1), (33, 1), (47, 1), (53, 1)] }, { coefficient := 1, powers := [(3, 1), (16, 1), (33, 1), (53, 2)] }, { coefficient := 1, powers := [(4, 1), (33, 1), (47, 1)] }, { coefficient := 1, powers := [(4, 1), (33, 1), (53, 1)] }, { coefficient := 1, powers := [(6, 1), (7, 1), (23, 1), (60, 2)] }, { coefficient := 1, powers := [(6, 1), (16, 1), (33, 1), (53, 2)] }, { coefficient := 1, powers := [(7, 1), (23, 1), (26, 1), (47, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (28, 1), (60, 1)] }, { coefficient := -1, powers := [(7, 1), (33, 1), (47, 1)] }, { coefficient := 1, powers := [(7, 1), (33, 1), (53, 1)] }, { coefficient := 1, powers := [(11, 1), (23, 1), (53, 1)] }, { coefficient := 1, powers := [(11, 1), (33, 1), (39, 1)] }, { coefficient := 1, powers := [(16, 1), (33, 1), (38, 1), (53, 2)] }, { coefficient := -1, powers := [(16, 1), (33, 1), (39, 1)] }, { coefficient := 1, powers := [(16, 1), (36, 1), (38, 1), (53, 2)] }],
  [{ coefficient := -1, powers := [(3, 1), (5, 1), (16, 1), (28, 1), (37, 1), (47, 1), (53, 1), (55, 1), (60, 1)] }, { coefficient := 1, powers := [(3, 1), (5, 1), (16, 1), (33, 1), (37, 1), (47, 2), (53, 1), (55, 1)] }, { coefficient := 1, powers := [(3, 1), (5, 1), (16, 1), (33, 1), (37, 1), (47, 1), (53, 2), (55, 1)] }, { coefficient := 1, powers := [(3, 1), (16, 1), (20, 1), (25, 1), (28, 1), (47, 1), (53, 1), (55, 1), (60, 1)] }, { coefficient := -1, powers := [(3, 1), (16, 1), (20, 1), (25, 1), (33, 1), (47, 2), (53, 1), (55, 1)] }, { coefficient := -1, powers := [(3, 1), (16, 1), (20, 1), (25, 1), (33, 1), (47, 1), (53, 2), (55, 1)] }, { coefficient := -1, powers := [(3, 1), (16, 1), (33, 1), (39, 1), (53, 1), (60, 1)] }, { coefficient := -1, powers := [(3, 1), (16, 1), (33, 1), (47, 1), (53, 2)] }, { coefficient := 1, powers := [(4, 1), (5, 1), (33, 1), (37, 1), (47, 2), (55, 1)] }, { coefficient := 1, powers := [(4, 1), (5, 1), (33, 1), (37, 1), (47, 1), (53, 1), (55, 1)] }, { coefficient := -1, powers := [(4, 1), (33, 1), (39, 1), (60, 1)] }, { coefficient := -1, powers := [(4, 1), (33, 1), (47, 1), (53, 1)] }, { coefficient := 1, powers := [(5, 1), (6, 1), (7, 1), (23, 1), (37, 1), (47, 1), (55, 1), (60, 2)] }, { coefficient := 1, powers := [(5, 1), (6, 1), (16, 1), (33, 1), (37, 1), (47, 1), (53, 2), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (7, 1), (23, 1), (26, 1), (37, 1), (47, 2), (55, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (7, 1), (28, 1), (37, 1), (47, 1), (55, 1), (60, 1)] }, { coefficient := -1, powers := [(5, 1), (7, 1), (33, 1), (37, 1), (47, 2), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (7, 1), (33, 1), (37, 1), (47, 1), (53, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (11, 1), (23, 1), (37, 1), (47, 1), (53, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (11, 1), (33, 1), (37, 1), (39, 1), (47, 1), (55, 1)] }, { coefficient := -1, powers := [(5, 1), (16, 1), (28, 1), (29, 1), (48, 1), (53, 1), (55, 1), (60, 1)] }, { coefficient := -1, powers := [(5, 1), (16, 1), (28, 1), (37, 1), (38, 1), (47, 1), (53, 1), (55, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (16, 1), (29, 1), (33, 1), (47, 1), (48, 1), (53, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (16, 1), (29, 1), (33, 1), (48, 1), (53, 2), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (16, 1), (33, 1), (37, 1), (38, 1), (47, 2), (53, 1), (55, 1)] }, { coefficient := 2, powers := [(5, 1), (16, 1), (33, 1), (37, 1), (38, 1), (47, 1), (53, 2), (55, 1)] }, { coefficient := -1, powers := [(5, 1), (16, 1), (33, 1), (37, 1), (39, 1), (47, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (16, 1), (36, 1), (37, 1), (38, 1), (47, 1), (53, 2), (55, 1)] }, { coefficient := -1, powers := [(6, 1), (7, 1), (20, 1), (23, 1), (25, 1), (47, 1), (55, 1), (60, 2)] }, { coefficient := -1, powers := [(7, 1), (13, 1), (23, 1), (25, 1), (27, 1), (48, 1), (53, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (13, 1), (23, 1), (25, 1), (48, 1), (54, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (13, 1), (23, 1), (31, 1), (47, 1), (50, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (13, 1), (23, 1), (37, 1), (40, 1), (47, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (19, 1), (23, 1), (30, 1), (50, 1), (55, 1), (60, 1)] }, { coefficient := -1, powers := [(7, 1), (20, 1), (23, 1), (25, 1), (26, 1), (47, 2), (55, 1), (60, 1)] }, { coefficient := -1, powers := [(7, 1), (20, 1), (25, 1), (28, 1), (47, 1), (55, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (20, 1), (25, 1), (33, 1), (47, 2), (55, 1)] }, { coefficient := -1, powers := [(7, 1), (20, 1), (25, 1), (33, 1), (47, 1), (53, 1), (55, 1)] }, { coefficient := -1, powers := [(7, 1), (23, 1), (47, 1), (60, 1)] }, { coefficient := -1, powers := [(11, 1), (13, 1), (23, 1), (25, 1), (48, 1), (53, 1), (54, 1)] }, { coefficient := -1, powers := [(11, 1), (20, 1), (23, 1), (25, 1), (47, 1), (53, 1), (55, 1)] }, { coefficient := -1, powers := [(11, 1), (20, 1), (25, 1), (33, 1), (39, 1), (47, 1), (55, 1)] }, { coefficient := 1, powers := [(11, 1), (28, 1), (39, 1), (60, 1)] }, { coefficient := 1, powers := [(11, 1), (28, 1), (47, 1), (53, 1)] }, { coefficient := -1, powers := [(13, 1), (17, 1), (23, 1), (25, 1), (47, 1), (53, 1), (54, 1)] }, { coefficient := 1, powers := [(16, 1), (20, 1), (25, 1), (28, 1), (38, 1), (47, 1), (53, 1), (55, 1), (60, 1)] }, { coefficient := -1, powers := [(16, 1), (20, 1), (25, 1), (33, 1), (38, 1), (47, 2), (53, 1), (55, 1)] }, { coefficient := -1, powers := [(16, 1), (20, 1), (25, 1), (33, 1), (38, 1), (47, 1), (53, 2), (55, 1)] }, { coefficient := 1, powers := [(16, 1), (20, 1), (25, 1), (33, 1), (39, 1), (47, 1), (55, 1)] }, { coefficient := -1, powers := [(16, 1), (20, 1), (25, 1), (36, 1), (38, 1), (47, 1), (53, 2), (55, 1)] }, { coefficient := -1, powers := [(17, 1), (19, 1), (23, 1), (25, 1), (47, 1), (53, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(39, 1), (60, 1)] }, { coefficient := -1, powers := [(53, 2)] }],
  [{ coefficient := 1, powers := [(3, 1), (16, 1), (28, 1), (40, 1), (53, 1), (60, 1), (61, 1)] }, { coefficient := -1, powers := [(3, 1), (16, 1), (33, 1), (40, 1), (47, 1), (53, 1), (61, 1)] }, { coefficient := -1, powers := [(3, 1), (16, 1), (33, 1), (40, 1), (53, 2), (61, 1)] }, { coefficient := -1, powers := [(4, 1), (33, 1), (40, 1), (47, 1), (61, 1)] }, { coefficient := -1, powers := [(4, 1), (33, 1), (40, 1), (53, 1), (61, 1)] }, { coefficient := -1, powers := [(4, 1), (33, 1), (47, 1), (50, 1), (55, 1)] }, { coefficient := -1, powers := [(4, 1), (33, 1), (50, 1), (53, 1), (55, 1)] }, { coefficient := -1, powers := [(6, 1), (7, 1), (23, 1), (40, 1), (60, 2), (61, 1)] }, { coefficient := -1, powers := [(6, 1), (7, 1), (23, 1), (50, 1), (55, 1), (60, 2)] }, { coefficient := -1, powers := [(6, 1), (16, 1), (33, 1), (40, 1), (53, 2), (61, 1)] }, { coefficient := -1, powers := [(6, 1), (16, 1), (33, 1), (50, 1), (53, 2), (55, 1)] }, { coefficient := -1, powers := [(7, 1), (23, 1), (26, 1), (40, 1), (47, 1), (60, 1), (61, 1)] }, { coefficient := -1, powers := [(7, 1), (23, 1), (26, 1), (47, 1), (50, 1), (55, 1), (60, 1)] }, { coefficient := -1, powers := [(7, 1), (28, 1), (40, 1), (60, 1), (61, 1)] }, { coefficient := -1, powers := [(7, 1), (28, 1), (50, 1), (55, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (33, 1), (40, 1), (47, 1), (61, 1)] }, { coefficient := -1, powers := [(7, 1), (33, 1), (40, 1), (53, 1), (61, 1)] }, { coefficient := 1, powers := [(7, 1), (33, 1), (47, 1), (50, 1), (55, 1)] }, { coefficient := -1, powers := [(7, 1), (33, 1), (50, 1), (53, 1), (55, 1)] }, { coefficient := -1, powers := [(11, 1), (23, 1), (40, 1), (53, 1), (61, 1)] }, { coefficient := -1, powers := [(11, 1), (33, 1), (39, 1), (50, 1), (55, 1)] }, { coefficient := 1, powers := [(16, 1), (28, 1), (38, 1), (40, 1), (53, 1), (60, 1), (61, 1)] }, { coefficient := -1, powers := [(16, 1), (33, 1), (38, 1), (40, 1), (47, 1), (53, 1), (61, 1)] }, { coefficient := -2, powers := [(16, 1), (33, 1), (38, 1), (40, 1), (53, 2), (61, 1)] }, { coefficient := -1, powers := [(16, 1), (33, 1), (38, 1), (50, 1), (53, 2), (55, 1)] }, { coefficient := 1, powers := [(16, 1), (33, 1), (39, 1), (50, 1), (55, 1)] }, { coefficient := -1, powers := [(16, 1), (36, 1), (38, 1), (40, 1), (53, 2), (61, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (3, 1), (16, 1), (33, 1), (53, 1), (57, 1)] }, { coefficient := -1, powers := [(0, 1), (4, 1), (33, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (7, 1), (13, 1), (23, 1), (25, 1), (58, 1), (60, 1)] }, { coefficient := -1, powers := [(0, 1), (11, 1), (13, 1), (23, 1), (25, 1), (53, 1), (58, 1)] }, { coefficient := 1, powers := [(0, 1), (11, 1), (28, 1), (57, 1)] }, { coefficient := 1, powers := [(1, 1), (57, 1)] }, { coefficient := -1, powers := [(3, 1), (16, 1), (33, 1), (53, 1)] }, { coefficient := -1, powers := [(4, 1), (33, 1)] }, { coefficient := -1, powers := [(5, 1), (17, 1), (23, 1), (26, 1), (34, 1), (53, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (17, 1), (23, 1), (27, 1), (34, 1), (53, 1)] }, { coefficient := 1, powers := [(7, 1), (13, 1), (23, 1), (26, 1), (31, 1), (50, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (13, 1), (23, 1), (26, 1), (37, 1), (40, 1), (60, 1)] }, { coefficient := -1, powers := [(7, 1), (23, 1), (26, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (36, 1)] }, { coefficient := -1, powers := [(11, 1), (13, 1), (23, 1), (25, 1), (27, 1), (45, 1), (53, 1)] }, { coefficient := 2, powers := [(13, 1), (17, 1), (22, 1), (23, 1), (31, 1), (53, 1)] }, { coefficient := -1, powers := [(13, 1), (17, 1), (23, 1), (25, 1), (27, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (3, 1), (16, 1), (28, 1), (53, 1), (58, 1), (60, 1)] }, { coefficient := -1, powers := [(2, 1), (3, 1), (16, 1), (33, 1), (47, 1), (53, 1), (58, 1)] }, { coefficient := -1, powers := [(2, 1), (3, 1), (16, 1), (33, 1), (53, 2), (58, 1)] }, { coefficient := -1, powers := [(2, 1), (4, 1), (33, 1), (47, 1), (58, 1)] }, { coefficient := -1, powers := [(2, 1), (4, 1), (33, 1), (53, 1), (58, 1)] }, { coefficient := -1, powers := [(2, 1), (6, 1), (7, 1), (23, 1), (58, 1), (60, 2)] }, { coefficient := -1, powers := [(2, 1), (6, 1), (16, 1), (33, 1), (53, 2), (58, 1)] }, { coefficient := -1, powers := [(2, 1), (7, 1), (23, 1), (26, 1), (47, 1), (58, 1), (60, 1)] }, { coefficient := -1, powers := [(2, 1), (7, 1), (28, 1), (58, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (7, 1), (33, 1), (47, 1), (58, 1)] }, { coefficient := -1, powers := [(2, 1), (7, 1), (33, 1), (53, 1), (58, 1)] }, { coefficient := -1, powers := [(2, 1), (11, 1), (23, 1), (53, 1), (58, 1)] }, { coefficient := -1, powers := [(2, 1), (11, 1), (33, 1), (39, 1), (58, 1)] }, { coefficient := -1, powers := [(2, 1), (16, 1), (33, 1), (38, 1), (53, 2), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (16, 1), (33, 1), (39, 1), (58, 1)] }, { coefficient := -1, powers := [(2, 1), (16, 1), (36, 1), (38, 1), (53, 2), (58, 1)] }, { coefficient := 1, powers := [(3, 1), (8, 1), (16, 1), (28, 1), (37, 1), (53, 1), (60, 1)] }, { coefficient := -1, powers := [(3, 1), (8, 1), (16, 1), (33, 1), (37, 1), (47, 1), (53, 1)] }, { coefficient := -1, powers := [(3, 1), (8, 1), (16, 1), (33, 1), (37, 1), (53, 2)] }, { coefficient := -1, powers := [(4, 1), (8, 1), (33, 1), (37, 1), (47, 1)] }, { coefficient := -1, powers := [(4, 1), (8, 1), (33, 1), (37, 1), (53, 1)] }, { coefficient := -1, powers := [(4, 1), (8, 1), (36, 1), (37, 1), (47, 1)] }, { coefficient := -1, powers := [(4, 1), (8, 1), (36, 1), (37, 1), (53, 1)] }, { coefficient := -1, powers := [(6, 1), (7, 1), (8, 1), (23, 1), (37, 1), (60, 2)] }, { coefficient := -1, powers := [(6, 1), (8, 1), (16, 1), (33, 1), (37, 1), (53, 2)] }, { coefficient := -1, powers := [(6, 1), (8, 1), (16, 1), (36, 1), (37, 1), (53, 2)] }, { coefficient := -1, powers := [(7, 1), (8, 1), (23, 1), (26, 1), (37, 1), (47, 1), (60, 1)] }, { coefficient := -1, powers := [(7, 1), (8, 1), (28, 1), (37, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (8, 1), (33, 1), (37, 1), (47, 1)] }, { coefficient := -1, powers := [(7, 1), (8, 1), (33, 1), (37, 1), (53, 1)] }, { coefficient := 1, powers := [(7, 1), (8, 1), (36, 1), (37, 1), (47, 1)] }, { coefficient := -1, powers := [(7, 1), (8, 1), (36, 1), (37, 1), (53, 1)] }, { coefficient := 1, powers := [(7, 1), (20, 1), (23, 1), (26, 1), (31, 1), (47, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (20, 1), (28, 1), (31, 1), (60, 1)] }, { coefficient := -1, powers := [(7, 1), (20, 1), (31, 1), (33, 1), (47, 1)] }, { coefficient := 1, powers := [(7, 1), (20, 1), (31, 1), (33, 1), (53, 1)] }, { coefficient := -1, powers := [(8, 1), (11, 1), (23, 1), (37, 1), (53, 1)] }, { coefficient := -1, powers := [(8, 1), (11, 1), (33, 1), (37, 1), (39, 1)] }, { coefficient := -1, powers := [(8, 1), (16, 1), (33, 1), (37, 1), (38, 1), (53, 2)] }, { coefficient := 1, powers := [(8, 1), (16, 1), (33, 1), (37, 1), (39, 1)] }, { coefficient := -1, powers := [(8, 1), (16, 1), (36, 1), (37, 1), (38, 1), (53, 2)] }, { coefficient := 1, powers := [(11, 1), (20, 1), (23, 1), (31, 1), (53, 1)] }, { coefficient := 1, powers := [(11, 1), (20, 1), (31, 1), (33, 1), (39, 1)] }, { coefficient := -1, powers := [(16, 1), (20, 1), (28, 1), (31, 1), (38, 1), (53, 1), (60, 1)] }, { coefficient := 1, powers := [(16, 1), (20, 1), (31, 1), (33, 1), (38, 1), (47, 1), (53, 1)] }, { coefficient := 1, powers := [(16, 1), (20, 1), (31, 1), (33, 1), (38, 1), (53, 2)] }, { coefficient := -1, powers := [(16, 1), (20, 1), (31, 1), (33, 1), (39, 1)] }]
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

#print axioms Krenn.Component16.SelectedLeafB0_0.selectedHasNoCommonZero

end Krenn.Component16.SelectedLeafB0_0
