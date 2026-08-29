import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component16.SelectedLeafB7_2_5

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "7bf990bd3fd770b783ac9a28588056c396ff91f48cb5ba6ed2a1f5d670fdf4a7"
def certificateSHA256 : String := "c0c26130ebe89a87f2b8e8a224a13c31f4df220983775d30d1b51f28810f7c0f"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 39 → Fin 671 := ![
  1,
  3,
  4,
  7,
  13,
  18,
  21,
  23,
  32,
  142,
  247,
  273,
  300,
  301,
  302,
  316,
  433,
  438,
  440,
  442,
  448,
  454,
  455,
  481,
  503,
  585,
  588,
  608,
  609,
  649,
  653,
  660,
  661,
  662,
  663,
  664,
  667,
  669,
  670
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 39 → SparsePoly (Fin 68) := ![
  [{ coefficient := 1, powers := [(1, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (34, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (28, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(34, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (55, 1)] }, { coefficient := 1, powers := [(21, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (21, 1), (57, 1)] }, { coefficient := 1, powers := [(13, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (45, 1), (54, 1)] }, { coefficient := 1, powers := [(23, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (47, 1)] }, { coefficient := 1, powers := [(4, 1), (36, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (53, 1)] }, { coefficient := 1, powers := [(7, 1), (33, 1)] }, { coefficient := 1, powers := [(11, 1), (28, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (61, 1)] }, { coefficient := 1, powers := [(13, 1), (50, 1)] }, { coefficient := 1, powers := [(20, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (55, 1)] }, { coefficient := 1, powers := [(31, 1), (43, 1)] }, { coefficient := 1, powers := [(34, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (29, 1), (42, 1)] }, { coefficient := 1, powers := [(19, 1), (29, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (30, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (53, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (53, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (57, 1)] }, { coefficient := 1, powers := [(19, 1), (30, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1)] }, { coefficient := 1, powers := [(13, 1), (31, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (37, 1)] }, { coefficient := 1, powers := [(24, 1), (45, 1)] }, { coefficient := 1, powers := [(29, 1), (45, 1)] }, { coefficient := 1, powers := [(37, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (61, 1)] }, { coefficient := 1, powers := [(13, 1), (27, 1), (48, 1)] }, { coefficient := 1, powers := [(13, 1), (58, 1)] }, { coefficient := 1, powers := [(20, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (42, 1)] }, { coefficient := 1, powers := [(19, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (53, 1)] }, { coefficient := 1, powers := [(19, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(30, 1), (42, 1)] }, { coefficient := 1, powers := [(30, 1), (47, 1)] }, { coefficient := 1, powers := [(30, 1), (53, 1)] }, { coefficient := 1, powers := [(30, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (39, 1), (61, 1)] }, { coefficient := 1, powers := [(13, 1), (30, 1), (48, 1)] }, { coefficient := 1, powers := [(13, 1), (37, 1), (39, 1)] }, { coefficient := 1, powers := [(20, 1), (34, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (31, 1), (61, 1)] }, { coefficient := 1, powers := [(3, 1), (34, 1), (58, 1)] }, { coefficient := 1, powers := [(3, 1), (37, 1), (55, 1)] }, { coefficient := 1, powers := [(24, 1), (45, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (53, 1)] }, { coefficient := 1, powers := [(3, 1), (60, 1)] }, { coefficient := 1, powers := [(21, 1), (53, 1)] }, { coefficient := 1, powers := [(21, 1), (57, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (40, 1), (61, 1)] }, { coefficient := 1, powers := [(0, 1), (43, 1), (58, 1)] }, { coefficient := 1, powers := [(0, 1), (50, 1), (55, 1)] }, { coefficient := 1, powers := [(22, 1), (45, 1), (55, 1)] }, { coefficient := 1, powers := [(27, 1), (43, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (60, 1)] }, { coefficient := 1, powers := [(11, 1), (47, 1)] }, { coefficient := 1, powers := [(11, 1), (57, 1)] }, { coefficient := 1, powers := [(16, 1), (42, 1)] }, { coefficient := 1, powers := [(16, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (53, 1)] }, { coefficient := 1, powers := [(23, 1), (57, 1)] }, { coefficient := 1, powers := [(28, 1), (42, 1)] }, { coefficient := 1, powers := [(28, 1), (47, 1)] }, { coefficient := 1, powers := [(33, 1), (39, 1)] }, { coefficient := 1, powers := [(36, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (39, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (42, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (47, 1), (53, 1)] }, { coefficient := 1, powers := [(42, 1)] }, { coefficient := 1, powers := [(47, 1)] }, { coefficient := 1, powers := [(53, 1)] }, { coefficient := 1, powers := [(57, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (39, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (42, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (47, 1), (53, 1)] }, { coefficient := 1, powers := [(19, 1), (30, 1), (42, 1)] }, { coefficient := 1, powers := [(19, 1), (30, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (30, 1), (53, 1)] }, { coefficient := 1, powers := [(19, 1), (30, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (39, 1), (60, 1)] }, { coefficient := 1, powers := [(1, 1), (42, 1), (57, 1)] }, { coefficient := 1, powers := [(1, 1), (47, 1), (53, 1)] }, { coefficient := 1, powers := [(4, 1), (28, 1), (60, 1)] }, { coefficient := 1, powers := [(4, 1), (33, 1), (57, 1)] }, { coefficient := 1, powers := [(4, 1), (36, 1), (53, 1)] }, { coefficient := 1, powers := [(7, 1), (23, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (33, 1), (47, 1)] }, { coefficient := 1, powers := [(7, 1), (36, 1), (42, 1)] }, { coefficient := 1, powers := [(11, 1), (23, 1), (57, 1)] }, { coefficient := 1, powers := [(11, 1), (28, 1), (47, 1)] }, { coefficient := 1, powers := [(11, 1), (36, 1), (39, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1), (53, 1)] }, { coefficient := 1, powers := [(16, 1), (28, 1), (42, 1)] }, { coefficient := 1, powers := [(16, 1), (33, 1), (39, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (40, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (43, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (50, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (37, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (25, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (50, 1)] }, { coefficient := 1, powers := [(8, 1), (37, 1), (43, 1)] }, { coefficient := 1, powers := [(13, 1), (25, 1), (58, 1)] }, { coefficient := 1, powers := [(13, 1), (31, 1), (50, 1)] }, { coefficient := 1, powers := [(13, 1), (37, 1), (40, 1)] }, { coefficient := 1, powers := [(20, 1), (25, 1), (55, 1)] }, { coefficient := 1, powers := [(20, 1), (31, 1), (43, 1)] }, { coefficient := 1, powers := [(20, 1), (34, 1), (40, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (64, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(43, 1)] }],
  [{ coefficient := 1, powers := [(57, 1)] }],
  [{ coefficient := 1, powers := [(58, 1), (67, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 39 → SparsePoly (Fin 68) := ![
  [{ coefficient := -2, powers := [(1, 1), (13, 1), (31, 1), (39, 1), (60, 1), (63, 1)] }, { coefficient := -1, powers := [(3, 1), (7, 1), (13, 1), (28, 1), (31, 1), (60, 2), (63, 1)] }, { coefficient := -1, powers := [(7, 1), (13, 1), (31, 1), (36, 1), (42, 1), (63, 1)] }, { coefficient := 1, powers := [(11, 1), (13, 1), (31, 1), (33, 1), (39, 1), (63, 1)] }, { coefficient := -1, powers := [(13, 1), (16, 1), (31, 1), (33, 1), (39, 1), (63, 1)] }],
  [{ coefficient := 2, powers := [(1, 1), (5, 1), (37, 1), (39, 1), (60, 1), (63, 1)] }, { coefficient := -2, powers := [(1, 1), (20, 1), (25, 1), (39, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(2, 1), (7, 1), (21, 1), (36, 1), (42, 1), (50, 1), (62, 1), (63, 1)] }, { coefficient := -1, powers := [(2, 1), (7, 1), (22, 1), (36, 1), (42, 1), (45, 1), (62, 1), (63, 1)] }, { coefficient := 1, powers := [(3, 1), (5, 1), (7, 1), (28, 1), (37, 1), (60, 2), (63, 1)] }, { coefficient := -1, powers := [(3, 1), (7, 1), (20, 1), (25, 1), (28, 1), (60, 2), (63, 1)] }, { coefficient := 1, powers := [(5, 1), (7, 1), (28, 1), (29, 1), (45, 1), (60, 2), (63, 1)] }, { coefficient := 1, powers := [(5, 1), (7, 1), (28, 1), (37, 1), (38, 1), (60, 2), (63, 1)] }, { coefficient := 1, powers := [(5, 1), (7, 1), (36, 1), (37, 1), (42, 1), (63, 1)] }, { coefficient := -1, powers := [(5, 1), (11, 1), (33, 1), (37, 1), (39, 1), (63, 1)] }, { coefficient := 1, powers := [(5, 1), (16, 1), (33, 1), (37, 1), (39, 1), (63, 1)] }, { coefficient := -1, powers := [(7, 1), (20, 1), (25, 1), (36, 1), (42, 1), (63, 1)] }, { coefficient := 1, powers := [(11, 1), (20, 1), (25, 1), (33, 1), (39, 1), (63, 1)] }, { coefficient := -1, powers := [(16, 1), (20, 1), (25, 1), (33, 1), (39, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (7, 1), (28, 1), (40, 1), (60, 2)] }, { coefficient := -1, powers := [(5, 1), (7, 1), (28, 1), (31, 1), (60, 2)] }],
  [{ coefficient := 1, powers := [(5, 1), (36, 1), (42, 1), (58, 1)] }],
  [{ coefficient := -2, powers := [(1, 1), (25, 1), (27, 1), (39, 1), (60, 1)] }, { coefficient := -2, powers := [(1, 1), (30, 1), (40, 1), (60, 1)] }, { coefficient := -1, powers := [(3, 1), (7, 1), (25, 1), (27, 1), (28, 1), (60, 2)] }, { coefficient := -1, powers := [(7, 1), (25, 1), (27, 1), (36, 1), (42, 1)] }, { coefficient := 1, powers := [(11, 1), (25, 1), (27, 1), (33, 1), (39, 1)] }, { coefficient := 1, powers := [(11, 1), (30, 1), (33, 1), (40, 1)] }, { coefficient := -1, powers := [(16, 1), (25, 1), (27, 1), (33, 1), (39, 1)] }, { coefficient := -1, powers := [(16, 1), (30, 1), (33, 1), (40, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (7, 1), (24, 1), (53, 1), (60, 1), (64, 1)] }, { coefficient := -1, powers := [(0, 1), (7, 1), (30, 1), (60, 1), (64, 1)] }, { coefficient := -1, powers := [(7, 1), (21, 1), (24, 1), (53, 1), (60, 1), (64, 1)] }, { coefficient := -1, powers := [(7, 1), (21, 1), (30, 1), (60, 1), (64, 1)] }, { coefficient := -1, powers := [(11, 1), (24, 1), (53, 1), (64, 1)] }, { coefficient := -1, powers := [(11, 1), (29, 1), (53, 1), (64, 1)] }, { coefficient := 1, powers := [(16, 1), (24, 1), (53, 1), (64, 1)] }, { coefficient := 1, powers := [(16, 1), (30, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (45, 1), (60, 1), (67, 1)] }, { coefficient := 1, powers := [(11, 1), (45, 1), (53, 1), (67, 1)] }],
  [{ coefficient := -2, powers := [(1, 1), (19, 1), (39, 1), (50, 1), (60, 1)] }, { coefficient := -1, powers := [(3, 1), (7, 1), (19, 1), (28, 1), (50, 1), (60, 2)] }, { coefficient := -1, powers := [(7, 1), (19, 1), (36, 1), (42, 1), (50, 1)] }, { coefficient := 1, powers := [(11, 1), (19, 1), (33, 1), (39, 1), (50, 1)] }, { coefficient := -1, powers := [(16, 1), (19, 1), (33, 1), (39, 1), (50, 1)] }],
  [{ coefficient := 2, powers := [(1, 1), (5, 1), (58, 1), (60, 1)] }, { coefficient := -2, powers := [(1, 1), (20, 1), (40, 1), (60, 1)] }, { coefficient := -1, powers := [(5, 1), (11, 1), (33, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (16, 1), (33, 1), (58, 1)] }, { coefficient := 1, powers := [(11, 1), (20, 1), (33, 1), (40, 1)] }, { coefficient := -1, powers := [(16, 1), (20, 1), (33, 1), (40, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (7, 1), (36, 1), (42, 1), (50, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (7, 1), (28, 1), (37, 1), (40, 1), (60, 2)] }, { coefficient := 1, powers := [(7, 1), (36, 1), (37, 1), (40, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (60, 1), (67, 1)] }, { coefficient := -1, powers := [(11, 1), (53, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(53, 1)] }],
  [{ coefficient := 1, powers := [(47, 1)] }],
  [{ coefficient := 2, powers := [(1, 1), (31, 1), (39, 1), (60, 1)] }, { coefficient := 1, powers := [(3, 1), (7, 1), (28, 1), (31, 1), (60, 2)] }, { coefficient := 1, powers := [(7, 1), (31, 1), (36, 1), (42, 1)] }, { coefficient := -1, powers := [(11, 1), (31, 1), (33, 1), (39, 1)] }, { coefficient := 1, powers := [(16, 1), (31, 1), (33, 1), (39, 1)] }],
  [{ coefficient := 2, powers := [(1, 1), (20, 1), (39, 1), (60, 1)] }, { coefficient := 1, powers := [(3, 1), (7, 1), (20, 1), (28, 1), (60, 2)] }, { coefficient := 1, powers := [(7, 1), (20, 1), (36, 1), (42, 1)] }, { coefficient := -1, powers := [(11, 1), (20, 1), (33, 1), (39, 1)] }, { coefficient := 1, powers := [(16, 1), (20, 1), (33, 1), (39, 1)] }],
  [{ coefficient := -1, powers := [(11, 1), (28, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (7, 1), (28, 1), (60, 1), (64, 1)] }, { coefficient := 1, powers := [(7, 1), (21, 1), (28, 1), (60, 1), (64, 1)] }, { coefficient := 1, powers := [(11, 1), (28, 1), (64, 1)] }, { coefficient := -1, powers := [(16, 1), (28, 1), (64, 1)] }],
  [{ coefficient := 2, powers := [(1, 1), (39, 1), (50, 1), (60, 1)] }, { coefficient := 1, powers := [(3, 1), (7, 1), (28, 1), (50, 1), (60, 2)] }, { coefficient := 1, powers := [(7, 1), (36, 1), (42, 1), (50, 1)] }, { coefficient := -1, powers := [(11, 1), (33, 1), (39, 1), (50, 1)] }, { coefficient := 1, powers := [(16, 1), (33, 1), (39, 1), (50, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (7, 1), (28, 1), (55, 1), (60, 2)] }],
  [{ coefficient := 2, powers := [(1, 1), (25, 1), (39, 1), (60, 1)] }, { coefficient := 1, powers := [(3, 1), (7, 1), (25, 1), (28, 1), (60, 2)] }, { coefficient := 1, powers := [(7, 1), (25, 1), (36, 1), (42, 1)] }, { coefficient := -1, powers := [(11, 1), (25, 1), (33, 1), (39, 1)] }, { coefficient := 1, powers := [(16, 1), (25, 1), (33, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (28, 1), (29, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (11, 1), (19, 1), (28, 1), (64, 1)] }, { coefficient := 1, powers := [(1, 1), (19, 1), (64, 1)] }],
  [{ coefficient := 2, powers := [(1, 1), (40, 1), (60, 1)] }, { coefficient := -1, powers := [(11, 1), (33, 1), (40, 1)] }, { coefficient := 1, powers := [(16, 1), (33, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (7, 1), (28, 1), (60, 2)] }],
  [{ coefficient := -1, powers := [(7, 1), (28, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (7, 1), (36, 1), (42, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(28, 1)] }],
  [{ coefficient := 1, powers := [(11, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (11, 1), (28, 1), (64, 1)] }, { coefficient := -2, powers := [(11, 1), (28, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (11, 1), (28, 1), (64, 1)] }, { coefficient := -1, powers := [(1, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -2, powers := [(1, 1), (39, 1), (60, 1)] }, { coefficient := -1, powers := [(3, 1), (7, 1), (28, 1), (60, 2)] }, { coefficient := -1, powers := [(7, 1), (36, 1), (42, 1)] }, { coefficient := 1, powers := [(11, 1), (33, 1), (39, 1)] }, { coefficient := -1, powers := [(16, 1), (33, 1), (39, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (7, 1), (36, 1), (40, 1), (42, 1), (61, 1)] }],
  [{ coefficient := -2, powers := [(1, 1), (5, 1), (37, 1), (39, 1), (55, 1), (60, 1)] }, { coefficient := 2, powers := [(1, 1), (13, 1), (31, 1), (39, 1), (50, 1), (60, 1)] }, { coefficient := 2, powers := [(1, 1), (20, 1), (25, 1), (39, 1), (55, 1), (60, 1)] }, { coefficient := -1, powers := [(2, 1), (7, 1), (21, 1), (36, 1), (42, 1), (50, 1), (55, 1), (62, 1)] }, { coefficient := 1, powers := [(2, 1), (7, 1), (22, 1), (36, 1), (42, 1), (45, 1), (55, 1), (62, 1)] }, { coefficient := -1, powers := [(3, 1), (5, 1), (7, 1), (28, 1), (37, 1), (55, 1), (60, 2)] }, { coefficient := 1, powers := [(3, 1), (7, 1), (13, 1), (28, 1), (31, 1), (50, 1), (60, 2)] }, { coefficient := 1, powers := [(3, 1), (7, 1), (20, 1), (25, 1), (28, 1), (55, 1), (60, 2)] }, { coefficient := -1, powers := [(5, 1), (7, 1), (28, 1), (29, 1), (45, 1), (55, 1), (60, 2)] }, { coefficient := -1, powers := [(5, 1), (7, 1), (28, 1), (37, 1), (38, 1), (55, 1), (60, 2)] }, { coefficient := -1, powers := [(5, 1), (7, 1), (36, 1), (37, 1), (42, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (11, 1), (33, 1), (37, 1), (39, 1), (55, 1)] }, { coefficient := -1, powers := [(5, 1), (16, 1), (33, 1), (37, 1), (39, 1), (55, 1)] }, { coefficient := 1, powers := [(7, 1), (13, 1), (31, 1), (36, 1), (42, 1), (50, 1)] }, { coefficient := 1, powers := [(7, 1), (20, 1), (25, 1), (36, 1), (42, 1), (55, 1)] }, { coefficient := -1, powers := [(11, 1), (13, 1), (31, 1), (33, 1), (39, 1), (50, 1)] }, { coefficient := -1, powers := [(11, 1), (20, 1), (25, 1), (33, 1), (39, 1), (55, 1)] }, { coefficient := 1, powers := [(13, 1), (16, 1), (31, 1), (33, 1), (39, 1), (50, 1)] }, { coefficient := 1, powers := [(16, 1), (20, 1), (25, 1), (33, 1), (39, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (7, 1), (28, 1), (53, 1), (60, 1)] }, { coefficient := -2, powers := [(0, 1), (11, 1), (28, 1), (39, 1), (60, 1)] }, { coefficient := -2, powers := [(0, 1), (11, 1), (28, 1), (47, 1), (53, 1)] }, { coefficient := 1, powers := [(1, 1), (39, 1), (60, 1)] }, { coefficient := 1, powers := [(1, 1), (47, 1), (53, 1)] }, { coefficient := -1, powers := [(7, 1), (21, 1), (28, 1), (53, 1), (60, 1)] }, { coefficient := -1, powers := [(11, 1), (28, 1), (42, 1)] }, { coefficient := -2, powers := [(11, 1), (28, 1), (53, 1)] }, { coefficient := 1, powers := [(16, 1), (28, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (2, 1), (7, 1), (36, 1), (42, 1), (58, 1), (62, 1)] }, { coefficient := 2, powers := [(1, 1), (2, 1), (39, 1), (58, 1), (60, 1)] }, { coefficient := 2, powers := [(1, 1), (8, 1), (37, 1), (39, 1), (60, 1)] }, { coefficient := -2, powers := [(1, 1), (20, 1), (31, 1), (39, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (3, 1), (7, 1), (28, 1), (58, 1), (60, 2)] }, { coefficient := -1, powers := [(2, 1), (7, 1), (27, 1), (36, 1), (42, 1), (45, 1), (62, 1)] }, { coefficient := 1, powers := [(2, 1), (7, 1), (36, 1), (42, 1), (58, 1)] }, { coefficient := -1, powers := [(2, 1), (11, 1), (33, 1), (39, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (16, 1), (33, 1), (39, 1), (58, 1)] }, { coefficient := 1, powers := [(3, 1), (7, 1), (8, 1), (28, 1), (37, 1), (60, 2)] }, { coefficient := -1, powers := [(3, 1), (7, 1), (20, 1), (28, 1), (31, 1), (60, 2)] }, { coefficient := 1, powers := [(7, 1), (8, 1), (36, 1), (37, 1), (42, 1)] }, { coefficient := -1, powers := [(7, 1), (20, 1), (31, 1), (36, 1), (42, 1)] }, { coefficient := -1, powers := [(8, 1), (11, 1), (33, 1), (37, 1), (39, 1)] }, { coefficient := 1, powers := [(8, 1), (16, 1), (33, 1), (37, 1), (39, 1)] }, { coefficient := 1, powers := [(11, 1), (20, 1), (31, 1), (33, 1), (39, 1)] }, { coefficient := -1, powers := [(16, 1), (20, 1), (31, 1), (33, 1), (39, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (2, 1), (11, 1), (28, 1), (42, 1), (64, 1)] }, { coefficient := -1, powers := [(0, 1), (7, 1), (19, 1), (24, 1), (28, 1), (60, 1), (64, 1)] }, { coefficient := 2, powers := [(0, 1), (11, 1), (28, 1), (42, 1)] }, { coefficient := 1, powers := [(1, 1), (2, 1), (42, 1), (64, 1)] }, { coefficient := 1, powers := [(1, 1), (42, 1)] }, { coefficient := -1, powers := [(2, 1), (11, 1), (28, 1), (64, 1)] }, { coefficient := -1, powers := [(3, 1), (7, 1), (13, 1), (21, 1), (28, 1), (37, 1), (40, 1), (60, 2)] }, { coefficient := 1, powers := [(4, 1), (33, 1)] }, { coefficient := -1, powers := [(7, 1), (13, 1), (21, 1), (36, 1), (37, 1), (40, 1), (42, 1)] }, { coefficient := -1, powers := [(7, 1), (19, 1), (21, 1), (24, 1), (28, 1), (60, 1), (64, 1)] }, { coefficient := 1, powers := [(7, 1), (21, 1), (28, 1), (60, 1)] }, { coefficient := -1, powers := [(11, 1), (19, 1), (24, 1), (28, 1), (64, 1)] }, { coefficient := -1, powers := [(11, 1), (19, 1), (28, 1), (29, 1), (64, 1)] }, { coefficient := 1, powers := [(11, 1), (28, 1)] }, { coefficient := 1, powers := [(16, 1), (19, 1), (24, 1), (28, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (23, 1), (60, 1)] }, { coefficient := 1, powers := [(11, 1), (23, 1), (53, 1)] }]
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
    ¬ ∀ index : Fin 39,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component16.SelectedLeafB7_2_5.selectedHasNoCommonZero

end Krenn.Component16.SelectedLeafB7_2_5
