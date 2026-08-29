import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component16.SelectedLeafB4_2_7_1

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "79c6f7aef06c043f44260692aa9c423cc9cbc7aaf7897191d2d5acfd630eafc0"
def certificateSHA256 : String := "4e08994ddbea4ce85331fd7f3c2d90e7c2cc32ba28f9a2216b47cbcaac9ac22f"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 47 → Fin 674 := ![
  5,
  8,
  13,
  21,
  23,
  150,
  151,
  153,
  170,
  172,
  273,
  298,
  299,
  300,
  301,
  302,
  316,
  317,
  321,
  325,
  362,
  364,
  407,
  408,
  436,
  440,
  448,
  462,
  506,
  507,
  512,
  532,
  584,
  593,
  608,
  609,
  610,
  660,
  661,
  662,
  663,
  664,
  667,
  670,
  671,
  672,
  673
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 47 → SparsePoly (Fin 68) := ![
  [{ coefficient := 1, powers := [(5, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (33, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (26, 1)] }, { coefficient := 1, powers := [(16, 1), (21, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (27, 1)] }, { coefficient := 1, powers := [(16, 1), (21, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (31, 1)] }, { coefficient := 1, powers := [(16, 1), (24, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (45, 1)] }, { coefficient := 1, powers := [(29, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(33, 1), (40, 1)] }, { coefficient := 1, powers := [(36, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (45, 1), (54, 1)] }, { coefficient := 1, powers := [(23, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1)] }, { coefficient := 1, powers := [(21, 1), (45, 1)] }, { coefficient := 1, powers := [(26, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (50, 1)] }, { coefficient := 1, powers := [(22, 1), (45, 1)] }, { coefficient := 1, powers := [(26, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (47, 1)] }, { coefficient := 1, powers := [(4, 1), (36, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (53, 1)] }, { coefficient := 1, powers := [(7, 1), (33, 1)] }, { coefficient := 1, powers := [(11, 1), (28, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (61, 1)] }, { coefficient := 1, powers := [(13, 1), (50, 1)] }, { coefficient := 1, powers := [(20, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (55, 1)] }, { coefficient := 1, powers := [(31, 1), (43, 1)] }, { coefficient := 1, powers := [(34, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(30, 1), (54, 1)] }, { coefficient := 1, powers := [(31, 1), (42, 1)] }, { coefficient := 1, powers := [(31, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1), (53, 1)] }, { coefficient := 1, powers := [(21, 1), (45, 1), (53, 1)] }, { coefficient := 1, powers := [(45, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (50, 1), (53, 1)] }, { coefficient := 1, powers := [(22, 1), (45, 1), (53, 1)] }, { coefficient := 1, powers := [(50, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (33, 1), (58, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (50, 1)] }, { coefficient := 1, powers := [(20, 1), (33, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (36, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (36, 1), (43, 1)] }, { coefficient := 1, powers := [(13, 1), (36, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (26, 1), (42, 1)] }, { coefficient := 1, powers := [(19, 1), (26, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (26, 1), (48, 1)] }, { coefficient := 1, powers := [(20, 1), (26, 1), (42, 1)] }, { coefficient := 1, powers := [(20, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (50, 1)] }, { coefficient := 1, powers := [(5, 1), (37, 1)] }, { coefficient := 1, powers := [(19, 1), (29, 1), (50, 1)] }, { coefficient := 1, powers := [(20, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1)] }, { coefficient := 1, powers := [(13, 1), (31, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (61, 1)] }, { coefficient := 1, powers := [(13, 1), (27, 1), (48, 1)] }, { coefficient := 1, powers := [(13, 1), (58, 1)] }, { coefficient := 1, powers := [(20, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1), (54, 1)] }, { coefficient := 1, powers := [(21, 1), (45, 1), (54, 1)] }, { coefficient := 1, powers := [(21, 1), (58, 1)] }, { coefficient := 1, powers := [(27, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (26, 1), (60, 1)] }, { coefficient := 1, powers := [(11, 1), (26, 1), (47, 1)] }, { coefficient := 1, powers := [(16, 1), (26, 1), (42, 1)] }, { coefficient := 1, powers := [(16, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (27, 1), (60, 1)] }, { coefficient := 1, powers := [(11, 1), (27, 1), (47, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1), (42, 1)] }, { coefficient := 1, powers := [(16, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (31, 1), (60, 1)] }, { coefficient := 1, powers := [(11, 1), (31, 1), (47, 1)] }, { coefficient := 1, powers := [(16, 1), (30, 1), (54, 1)] }, { coefficient := 1, powers := [(16, 1), (31, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (24, 1), (60, 1)] }, { coefficient := 1, powers := [(11, 1), (24, 1), (57, 1)] }, { coefficient := 1, powers := [(11, 1), (30, 1)] }, { coefficient := 1, powers := [(16, 1), (24, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1)] }, { coefficient := 1, powers := [(6, 1), (60, 1)] }, { coefficient := 1, powers := [(26, 1), (42, 1)] }, { coefficient := 1, powers := [(26, 1), (47, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1), (42, 1), (58, 1)] }, { coefficient := 1, powers := [(1, 1), (48, 1), (54, 1)] }, { coefficient := 1, powers := [(4, 1), (33, 1), (58, 1)] }, { coefficient := 1, powers := [(11, 1), (23, 1), (58, 1)] }, { coefficient := 1, powers := [(17, 1), (23, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (60, 1)] }, { coefficient := 1, powers := [(11, 1), (47, 1)] }, { coefficient := 1, powers := [(11, 1), (57, 1)] }, { coefficient := 1, powers := [(16, 1), (42, 1)] }, { coefficient := 1, powers := [(16, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (53, 1)] }, { coefficient := 1, powers := [(23, 1), (57, 1)] }, { coefficient := 1, powers := [(28, 1), (42, 1)] }, { coefficient := 1, powers := [(28, 1), (47, 1)] }, { coefficient := 1, powers := [(33, 1), (39, 1)] }, { coefficient := 1, powers := [(36, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (38, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1)] }, { coefficient := 1, powers := [(3, 1), (26, 1), (60, 1)] }, { coefficient := 1, powers := [(6, 1), (21, 1), (60, 1)] }, { coefficient := 1, powers := [(21, 1)] }, { coefficient := 1, powers := [(26, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (39, 1), (60, 1)] }, { coefficient := 1, powers := [(1, 1), (42, 1), (57, 1)] }, { coefficient := 1, powers := [(1, 1), (47, 1), (53, 1)] }, { coefficient := 1, powers := [(4, 1), (28, 1), (60, 1)] }, { coefficient := 1, powers := [(4, 1), (33, 1), (57, 1)] }, { coefficient := 1, powers := [(4, 1), (36, 1), (53, 1)] }, { coefficient := 1, powers := [(7, 1), (23, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (33, 1), (47, 1)] }, { coefficient := 1, powers := [(7, 1), (36, 1), (42, 1)] }, { coefficient := 1, powers := [(11, 1), (23, 1), (57, 1)] }, { coefficient := 1, powers := [(11, 1), (28, 1), (47, 1)] }, { coefficient := 1, powers := [(11, 1), (36, 1), (39, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1), (53, 1)] }, { coefficient := 1, powers := [(16, 1), (28, 1), (42, 1)] }, { coefficient := 1, powers := [(16, 1), (33, 1), (39, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (40, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (43, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (50, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (37, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (25, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (50, 1)] }, { coefficient := 1, powers := [(8, 1), (37, 1), (43, 1)] }, { coefficient := 1, powers := [(13, 1), (25, 1), (58, 1)] }, { coefficient := 1, powers := [(13, 1), (31, 1), (50, 1)] }, { coefficient := 1, powers := [(13, 1), (37, 1), (40, 1)] }, { coefficient := 1, powers := [(20, 1), (25, 1), (55, 1)] }, { coefficient := 1, powers := [(20, 1), (31, 1), (43, 1)] }, { coefficient := 1, powers := [(20, 1), (34, 1), (40, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1)] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(43, 1)] }],
  [{ coefficient := 1, powers := [(58, 1), (66, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(26, 1)] }],
  [{ coefficient := 1, powers := [(28, 1)] }],
  [{ coefficient := 1, powers := [(31, 1), (67, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 47 → SparsePoly (Fin 68) := ![
  [{ coefficient := -1, powers := [(11, 1), (37, 1), (39, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (34, 1), (39, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (25, 1), (27, 1), (33, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (45, 1), (53, 1), (66, 1)] }, { coefficient := 2, powers := [(11, 1), (45, 1), (57, 1), (66, 1)] }, { coefficient := -1, powers := [(17, 1), (57, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (19, 1), (33, 1), (39, 1), (50, 1)] }],
  [{ coefficient := -1, powers := [(30, 1), (36, 1), (38, 1), (42, 1), (54, 1), (57, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(30, 1), (36, 1), (38, 1), (42, 1), (57, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(36, 1), (38, 1), (42, 1), (57, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (19, 1), (33, 1), (39, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(11, 1), (13, 1), (37, 1), (39, 1)] }],
  [{ coefficient := -1, powers := [(11, 1), (53, 1), (66, 1)] }, { coefficient := -2, powers := [(11, 1), (57, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (27, 1), (36, 1), (42, 1), (47, 1), (53, 1), (66, 1)] }, { coefficient := -1, powers := [(7, 1), (36, 1), (42, 1), (47, 1), (54, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(11, 1), (13, 1), (31, 1), (33, 1), (39, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(53, 1)] }],
  [{ coefficient := 1, powers := [(47, 1)] }],
  [{ coefficient := -1, powers := [(11, 1), (31, 1), (33, 1), (39, 1)] }],
  [{ coefficient := -1, powers := [(11, 1), (20, 1), (33, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (23, 1), (67, 1)] }, { coefficient := -1, powers := [(16, 1), (36, 1), (38, 1), (42, 1), (67, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (27, 1), (36, 1), (42, 1), (47, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (13, 1), (31, 1), (33, 1), (39, 1)] }],
  [{ coefficient := -1, powers := [(11, 1), (34, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (37, 1), (39, 1)] }],
  [{ coefficient := -1, powers := [(11, 1), (25, 1), (33, 1), (39, 1), (45, 1), (55, 1)] }],
  [{ coefficient := 2, powers := [(11, 1), (25, 1), (33, 1), (39, 1), (55, 1)] }, { coefficient := 1, powers := [(11, 1), (33, 1), (34, 1), (39, 1), (40, 1)] }],
  [{ coefficient := -1, powers := [(11, 1), (33, 1), (39, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(11, 1), (33, 1), (39, 1), (50, 1)] }],
  [{ coefficient := -1, powers := [(11, 1), (25, 1), (33, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (36, 1), (42, 1), (47, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(23, 1), (42, 1)] }, { coefficient := -1, powers := [(23, 1), (47, 1)] }, { coefficient := -1, powers := [(23, 1), (53, 1)] }, { coefficient := 1, powers := [(33, 1), (39, 1)] }, { coefficient := 1, powers := [(36, 1), (38, 1), (42, 2)] }, { coefficient := 1, powers := [(36, 1), (38, 1), (42, 1), (47, 1)] }, { coefficient := 1, powers := [(36, 1), (38, 1), (42, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(24, 1), (36, 1), (38, 1), (42, 1), (57, 1), (67, 1)] }],
  [{ coefficient := -1, powers := [(23, 1), (67, 1)] }, { coefficient := 1, powers := [(36, 1), (38, 1), (42, 1), (67, 1)] }],
  [{ coefficient := -1, powers := [(27, 1), (36, 1), (38, 1), (42, 1), (57, 1), (67, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (21, 1), (36, 1), (42, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(57, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (31, 1), (67, 1)] }, { coefficient := 1, powers := [(24, 1), (27, 1), (36, 1), (38, 1), (42, 1), (57, 1), (67, 1)] }, { coefficient := -1, powers := [(31, 1), (36, 1), (38, 1), (42, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(11, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (36, 1), (42, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(11, 1), (33, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (21, 1), (36, 1), (42, 1), (47, 1)] }, { coefficient := -1, powers := [(7, 1), (36, 1), (38, 1), (42, 1), (60, 1)] }, { coefficient := -1, powers := [(7, 1), (36, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(39, 1), (60, 1)] }, { coefficient := -1, powers := [(42, 1), (57, 1), (58, 1), (66, 1)] }, { coefficient := 1, powers := [(42, 1), (57, 1)] }, { coefficient := -1, powers := [(47, 1), (53, 1)] }, { coefficient := -1, powers := [(48, 1), (54, 1), (57, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(11, 1), (33, 1), (39, 1), (40, 1), (61, 1)] }, { coefficient := 1, powers := [(11, 1), (33, 1), (39, 1), (50, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (11, 1), (33, 1), (39, 1), (58, 1)] }, { coefficient := -1, powers := [(8, 1), (11, 1), (33, 1), (37, 1), (39, 1)] }, { coefficient := -1, powers := [(8, 1), (11, 1), (36, 1), (37, 1), (39, 1)] }, { coefficient := 1, powers := [(11, 1), (20, 1), (31, 1), (33, 1), (39, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (33, 1), (57, 1)] }, { coefficient := -1, powers := [(7, 1), (21, 1), (36, 1), (42, 1), (47, 1)] }, { coefficient := 1, powers := [(11, 1), (23, 1), (53, 1)] }, { coefficient := 1, powers := [(11, 1), (23, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (7, 1), (36, 1), (42, 1), (60, 1), (62, 1)] }, { coefficient := 1, powers := [(4, 1), (23, 1), (42, 1), (60, 1)] }, { coefficient := 1, powers := [(4, 1), (23, 1), (47, 1), (60, 1)] }, { coefficient := 1, powers := [(4, 1), (23, 1), (53, 1), (60, 1)] }, { coefficient := -1, powers := [(4, 1), (33, 1), (39, 1), (60, 1)] }, { coefficient := -1, powers := [(4, 1), (36, 1), (38, 1), (42, 2), (60, 1)] }, { coefficient := -1, powers := [(4, 1), (36, 1), (38, 1), (42, 1), (47, 1), (60, 1)] }, { coefficient := -1, powers := [(4, 1), (36, 1), (38, 1), (42, 1), (53, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (21, 1), (36, 1), (42, 2), (62, 1)] }, { coefficient := 1, powers := [(7, 1), (21, 1), (36, 1), (42, 1), (47, 1), (62, 1)] }, { coefficient := -1, powers := [(7, 1), (27, 1), (36, 1), (42, 1), (45, 1), (47, 1), (53, 1), (66, 1)] }, { coefficient := 1, powers := [(7, 1), (36, 1), (42, 1), (45, 1), (47, 1), (54, 1), (66, 1)] }, { coefficient := -1, powers := [(7, 1), (36, 1), (42, 1), (62, 1)] }, { coefficient := 1, powers := [(11, 1), (13, 1), (31, 1), (33, 1), (39, 1), (50, 1), (53, 1)] }, { coefficient := 1, powers := [(11, 1), (19, 1), (25, 1), (33, 1), (39, 1), (42, 1), (45, 1), (55, 1)] }, { coefficient := 1, powers := [(11, 1), (19, 1), (25, 1), (33, 1), (39, 1), (45, 1), (47, 1), (55, 1)] }, { coefficient := -2, powers := [(11, 1), (19, 1), (25, 1), (33, 1), (39, 1), (48, 1), (55, 1)] }, { coefficient := -1, powers := [(11, 1), (19, 1), (33, 1), (34, 1), (39, 1), (40, 1), (48, 1)] }, { coefficient := -2, powers := [(11, 1), (20, 1), (25, 1), (33, 1), (39, 1), (42, 1), (55, 1)] }, { coefficient := -1, powers := [(11, 1), (20, 1), (33, 1), (34, 1), (39, 1), (40, 1), (42, 1)] }, { coefficient := 1, powers := [(11, 1), (23, 1), (42, 1), (47, 1)] }, { coefficient := 1, powers := [(11, 1), (23, 1), (47, 2)] }, { coefficient := 1, powers := [(11, 1), (23, 1), (47, 1), (53, 1)] }, { coefficient := 1, powers := [(11, 1), (30, 1), (36, 1), (38, 1), (42, 1), (54, 1), (57, 1), (67, 1)] }, { coefficient := -1, powers := [(11, 1), (33, 1), (39, 1), (47, 1)] }, { coefficient := -1, powers := [(11, 1), (36, 1), (38, 1), (42, 2), (47, 1)] }, { coefficient := -1, powers := [(11, 1), (36, 1), (38, 1), (42, 1), (47, 2)] }, { coefficient := -1, powers := [(11, 1), (36, 1), (38, 1), (42, 1), (47, 1), (53, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1), (42, 2)] }, { coefficient := 1, powers := [(16, 1), (23, 1), (42, 1), (47, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1), (42, 1), (53, 1)] }, { coefficient := -1, powers := [(16, 1), (33, 1), (39, 1), (42, 1)] }, { coefficient := -1, powers := [(16, 1), (36, 1), (38, 1), (42, 3)] }, { coefficient := -1, powers := [(16, 1), (36, 1), (38, 1), (42, 2), (47, 1)] }, { coefficient := -1, powers := [(16, 1), (36, 1), (38, 1), (42, 2), (53, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (60, 1)] }, { coefficient := -1, powers := [(11, 1), (42, 1)] }, { coefficient := -1, powers := [(11, 1), (47, 1)] }, { coefficient := 1, powers := [(16, 1), (42, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (23, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (36, 1), (38, 1), (42, 1), (60, 1)] }, { coefficient := -1, powers := [(11, 1), (23, 1), (57, 1)] }, { coefficient := -1, powers := [(16, 1), (23, 1), (42, 1)] }, { coefficient := -1, powers := [(16, 1), (23, 1), (47, 1)] }, { coefficient := -1, powers := [(16, 1), (23, 1), (53, 1)] }, { coefficient := 1, powers := [(16, 1), (36, 1), (38, 1), (42, 2)] }, { coefficient := 1, powers := [(16, 1), (36, 1), (38, 1), (42, 1), (47, 1)] }, { coefficient := 1, powers := [(16, 1), (36, 1), (38, 1), (42, 1), (53, 1)] }]
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
    (values : Fin 68 → R) :
    ¬ ∀ index : Fin 47,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component16.SelectedLeafB4_2_7_1.selectedHasNoCommonZero

end Krenn.Component16.SelectedLeafB4_2_7_1
