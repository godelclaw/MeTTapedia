import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component37.SelectedLeafB4_5_0

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "5c445db37fe3d7a8c821b6b014d3bdb762f9ba6762ab4c031909a3a4b39ce4ac"
def certificateSHA256 : String := "38cbe0fe593359546a8de3b49d89fb26cfe8b3831f1483c460f3e6150a692b12"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 29 → Fin 667 := ![
  21,
  27,
  147,
  154,
  182,
  234,
  298,
  299,
  301,
  319,
  373,
  385,
  531,
  549,
  583,
  588,
  602,
  603,
  604,
  605,
  614,
  655,
  656,
  659,
  661,
  662,
  663,
  664,
  665
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 29 → SparsePoly (Fin 65) := ![
  [{ coefficient := 1, powers := [(22, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (31, 1)] }, { coefficient := 1, powers := [(15, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (25, 1)] }, { coefficient := 1, powers := [(15, 1), (20, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (42, 1)] }, { coefficient := 1, powers := [(27, 1), (48, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (25, 1), (48, 1)] }, { coefficient := 1, powers := [(15, 1), (21, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (46, 1)] }, { coefficient := 1, powers := [(4, 1), (35, 1)] }, { coefficient := 1, powers := [(15, 1), (22, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (52, 1)] }, { coefficient := 1, powers := [(7, 1), (32, 1)] }, { coefficient := 1, powers := [(10, 1), (27, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (59, 1)] }, { coefficient := 1, powers := [(9, 1), (43, 1)] }, { coefficient := 1, powers := [(13, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (38, 1), (59, 1)] }, { coefficient := 1, powers := [(4, 1), (27, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (22, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (22, 1), (57, 1)] }, { coefficient := 1, powers := [(9, 1), (27, 1), (46, 1)] }, { coefficient := 1, powers := [(9, 1), (35, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (20, 1), (57, 1)] }, { coefficient := 1, powers := [(11, 1)] }, { coefficient := 1, powers := [(15, 1), (20, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (20, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (31, 1), (43, 1)] }, { coefficient := 1, powers := [(7, 1), (34, 1), (40, 1)] }, { coefficient := 1, powers := [(14, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (21, 1), (57, 1)] }, { coefficient := 1, powers := [(11, 1), (48, 1)] }, { coefficient := 1, powers := [(15, 1), (21, 1), (53, 1)] }, { coefficient := 1, powers := [(15, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (31, 1), (57, 1)] }, { coefficient := 1, powers := [(9, 1), (20, 1), (57, 1)] }, { coefficient := 1, powers := [(9, 1)] }, { coefficient := 1, powers := [(40, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (41, 1), (56, 1)] }, { coefficient := 1, powers := [(1, 1), (45, 1)] }, { coefficient := 1, powers := [(4, 1), (32, 1), (56, 1)] }, { coefficient := 1, powers := [(10, 1), (22, 1), (56, 1)] }, { coefficient := 1, powers := [(14, 1), (22, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1)] }, { coefficient := 1, powers := [(3, 1), (34, 1)] }, { coefficient := 1, powers := [(13, 1), (20, 1)] }, { coefficient := 1, powers := [(20, 1), (56, 1)] }, { coefficient := 1, powers := [(25, 1), (43, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (50, 1)] }, { coefficient := 1, powers := [(6, 1), (31, 1)] }, { coefficient := 1, powers := [(9, 1), (25, 1)] }, { coefficient := 1, powers := [(20, 1), (50, 1)] }, { coefficient := 1, powers := [(25, 1), (40, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (60, 1)] }, { coefficient := 1, powers := [(10, 1), (46, 1)] }, { coefficient := 1, powers := [(10, 1), (57, 1)] }, { coefficient := 1, powers := [(15, 1), (41, 1)] }, { coefficient := 1, powers := [(15, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (52, 1)] }, { coefficient := 1, powers := [(22, 1), (57, 1)] }, { coefficient := 1, powers := [(27, 1), (41, 1)] }, { coefficient := 1, powers := [(27, 1), (46, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1)] }, { coefficient := 1, powers := [(35, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (45, 1), (52, 1)] }, { coefficient := 1, powers := [(7, 1), (32, 1), (45, 1)] }, { coefficient := 1, powers := [(10, 1), (27, 1), (45, 1)] }, { coefficient := 1, powers := [(14, 1), (22, 1), (52, 1)] }, { coefficient := 1, powers := [(14, 1), (27, 1), (41, 1)] }, { coefficient := 1, powers := [(14, 1), (32, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (37, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (40, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (43, 1), (50, 1)] }, { coefficient := 1, powers := [(3, 1), (25, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (31, 1), (56, 1)] }, { coefficient := 1, powers := [(3, 1), (34, 1), (50, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (31, 1), (43, 1)] }, { coefficient := 1, powers := [(6, 1), (34, 1), (40, 1)] }, { coefficient := 1, powers := [(9, 1), (20, 1), (56, 1)] }, { coefficient := 1, powers := [(9, 1), (25, 1), (43, 1)] }, { coefficient := 1, powers := [(9, 1), (34, 1), (37, 1)] }, { coefficient := 1, powers := [(13, 1), (20, 1), (50, 1)] }, { coefficient := 1, powers := [(13, 1), (25, 1), (40, 1)] }, { coefficient := 1, powers := [(13, 1), (31, 1), (37, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1), (38, 1), (60, 1)] }, { coefficient := 1, powers := [(1, 1), (41, 1), (57, 1)] }, { coefficient := 1, powers := [(1, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(4, 1), (27, 1), (60, 1)] }, { coefficient := 1, powers := [(4, 1), (32, 1), (57, 1)] }, { coefficient := 1, powers := [(4, 1), (35, 1), (52, 1)] }, { coefficient := 1, powers := [(7, 1), (22, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (32, 1), (46, 1)] }, { coefficient := 1, powers := [(7, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(10, 1), (22, 1), (57, 1)] }, { coefficient := 1, powers := [(10, 1), (27, 1), (46, 1)] }, { coefficient := 1, powers := [(10, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(15, 1), (22, 1), (52, 1)] }, { coefficient := 1, powers := [(15, 1), (27, 1), (41, 1)] }, { coefficient := 1, powers := [(15, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1)] }],
  [{ coefficient := 1, powers := [(40, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(41, 1)] }],
  [{ coefficient := 1, powers := [(42, 1), (64, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(56, 1)] }],
  [{ coefficient := 1, powers := [(57, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 29 → SparsePoly (Fin 65) := ![
  [{ coefficient := -1, powers := [(0, 1), (7, 1), (43, 1), (60, 1)] }, { coefficient := -1, powers := [(7, 1), (20, 1), (43, 1), (60, 1)] }, { coefficient := -1, powers := [(7, 1), (25, 1), (43, 1), (60, 1)] }, { coefficient := -1, powers := [(7, 1), (34, 1), (37, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (4, 1), (37, 1), (51, 1), (59, 1), (60, 1), (64, 1)] }, { coefficient := 1, powers := [(4, 1), (20, 1), (37, 1), (51, 1), (59, 1), (60, 1), (64, 1)] }, { coefficient := 1, powers := [(6, 1), (7, 1), (9, 1), (14, 1), (22, 1), (51, 1), (60, 2), (64, 1)] }, { coefficient := 2, powers := [(6, 1), (9, 1), (10, 1), (14, 1), (22, 1), (46, 1), (51, 1), (60, 1), (64, 1)] }, { coefficient := 1, powers := [(6, 1), (9, 1), (14, 1), (15, 1), (22, 1), (51, 1), (52, 1), (60, 1), (64, 1)] }, { coefficient := -1, powers := [(7, 1), (9, 1), (14, 1), (22, 1), (37, 1), (51, 1), (60, 2), (64, 1)] }, { coefficient := 1, powers := [(7, 1), (51, 1), (60, 1), (64, 1)] }, { coefficient := -2, powers := [(9, 1), (10, 1), (14, 1), (22, 1), (37, 1), (46, 1), (51, 1), (60, 1), (64, 1)] }, { coefficient := -1, powers := [(9, 1), (14, 1), (15, 1), (22, 1), (37, 1), (51, 1), (52, 1), (60, 1), (64, 1)] }, { coefficient := 2, powers := [(10, 1), (46, 1), (51, 1), (64, 1)] }, { coefficient := 1, powers := [(15, 1), (51, 1), (52, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (22, 1), (43, 1), (60, 1)] }, { coefficient := 1, powers := [(13, 1), (22, 1), (37, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (9, 1), (22, 1), (43, 1), (48, 1), (53, 1), (60, 1), (64, 1)] }, { coefficient := 1, powers := [(9, 1), (13, 1), (22, 1), (37, 1), (48, 1), (53, 1), (60, 1), (64, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1), (48, 1), (53, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (4, 1), (37, 1), (59, 1), (60, 1), (64, 1)] }, { coefficient := -1, powers := [(4, 1), (20, 1), (37, 1), (59, 1), (60, 1), (64, 1)] }, { coefficient := -1, powers := [(6, 1), (7, 1), (9, 1), (14, 1), (22, 1), (60, 2), (64, 1)] }, { coefficient := -2, powers := [(6, 1), (9, 1), (10, 1), (14, 1), (22, 1), (46, 1), (60, 1), (64, 1)] }, { coefficient := -1, powers := [(6, 1), (9, 1), (14, 1), (15, 1), (22, 1), (52, 1), (60, 1), (64, 1)] }, { coefficient := 1, powers := [(7, 1), (9, 1), (14, 1), (22, 1), (37, 1), (60, 2), (64, 1)] }, { coefficient := -1, powers := [(7, 1), (60, 1), (64, 1)] }, { coefficient := 2, powers := [(9, 1), (10, 1), (14, 1), (22, 1), (37, 1), (46, 1), (60, 1), (64, 1)] }, { coefficient := 1, powers := [(9, 1), (14, 1), (15, 1), (22, 1), (37, 1), (52, 1), (60, 1), (64, 1)] }, { coefficient := -2, powers := [(10, 1), (46, 1), (64, 1)] }, { coefficient := -1, powers := [(15, 1), (52, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (9, 1), (22, 1), (43, 1), (53, 1), (60, 1), (64, 1)] }, { coefficient := -1, powers := [(9, 1), (13, 1), (22, 1), (37, 1), (53, 1), (60, 1), (64, 1)] }, { coefficient := -1, powers := [(32, 1), (38, 1), (53, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (9, 1), (14, 1), (22, 1), (52, 1), (60, 1)] }, { coefficient := -1, powers := [(9, 1), (14, 1), (22, 1), (37, 1), (52, 1), (60, 1)] }, { coefficient := 1, powers := [(52, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (9, 1), (10, 1), (22, 1), (45, 1), (60, 1)] }, { coefficient := 1, powers := [(6, 1), (9, 1), (14, 1), (22, 1), (46, 1), (60, 1)] }, { coefficient := -1, powers := [(6, 1), (9, 1), (15, 1), (22, 1), (45, 1), (60, 1)] }, { coefficient := -1, powers := [(9, 1), (10, 1), (22, 1), (37, 1), (45, 1), (60, 1)] }, { coefficient := -1, powers := [(9, 1), (14, 1), (22, 1), (37, 1), (46, 1), (60, 1)] }, { coefficient := 1, powers := [(9, 1), (15, 1), (22, 1), (37, 1), (45, 1), (60, 1)] }, { coefficient := 1, powers := [(46, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (22, 1), (25, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (37, 1), (60, 1)] }, { coefficient := 1, powers := [(20, 1), (37, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(10, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (9, 1), (22, 1), (43, 1), (48, 1), (60, 1), (64, 1)] }, { coefficient := -1, powers := [(9, 1), (13, 1), (22, 1), (37, 1), (48, 1), (60, 1), (64, 1)] }, { coefficient := -1, powers := [(32, 1), (38, 1), (48, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (22, 1), (60, 1)] }, { coefficient := -1, powers := [(22, 1), (37, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (9, 1), (22, 1), (43, 1), (60, 1), (64, 1)] }, { coefficient := 1, powers := [(9, 1), (13, 1), (22, 1), (37, 1), (60, 1), (64, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (14, 1), (22, 1), (60, 1)] }, { coefficient := 1, powers := [(6, 1), (15, 1), (22, 1), (43, 1), (60, 1)] }, { coefficient := -1, powers := [(7, 1), (22, 1), (25, 1), (43, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (22, 1), (34, 1), (37, 1), (60, 1)] }, { coefficient := -1, powers := [(10, 1), (22, 1), (52, 1), (63, 1)] }, { coefficient := -1, powers := [(10, 1), (32, 1), (38, 1), (63, 1)] }, { coefficient := -1, powers := [(13, 1), (15, 1), (22, 1), (37, 1), (60, 1)] }, { coefficient := 1, powers := [(14, 1), (22, 1), (37, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (7, 1), (9, 1), (22, 1), (60, 2)] }, { coefficient := -1, powers := [(6, 1), (9, 1), (15, 1), (22, 1), (52, 1), (60, 1)] }, { coefficient := -1, powers := [(7, 1), (9, 1), (22, 1), (37, 1), (60, 2)] }, { coefficient := 1, powers := [(9, 1), (15, 1), (22, 1), (37, 1), (52, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (22, 1), (50, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (22, 1), (43, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (9, 1), (14, 1), (22, 1), (27, 1), (60, 1)] }, { coefficient := -1, powers := [(9, 1), (14, 1), (22, 1), (27, 1), (37, 1), (60, 1)] }, { coefficient := 1, powers := [(27, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (9, 1), (10, 1), (14, 1), (22, 1), (60, 1)] }, { coefficient := -1, powers := [(9, 1), (10, 1), (14, 1), (22, 1), (37, 1), (60, 1)] }, { coefficient := 1, powers := [(9, 1), (10, 1), (63, 1)] }, { coefficient := 1, powers := [(10, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (9, 1), (10, 1), (22, 1), (60, 1)] }, { coefficient := 1, powers := [(6, 1), (9, 1), (15, 1), (22, 1), (60, 1)] }, { coefficient := 1, powers := [(9, 1), (10, 1), (22, 1), (37, 1), (60, 1)] }, { coefficient := -1, powers := [(9, 1), (15, 1), (22, 1), (37, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (22, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (9, 1), (14, 1), (22, 1), (60, 1)] }, { coefficient := 1, powers := [(9, 1), (14, 1), (22, 1), (37, 1), (60, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(0, 1), (37, 1), (38, 1), (59, 1), (60, 1)] }, { coefficient := -1, powers := [(6, 1), (7, 1), (9, 1), (22, 1), (45, 1), (60, 2)] }, { coefficient := 1, powers := [(6, 1), (9, 1), (14, 1), (22, 1), (38, 1), (60, 2)] }, { coefficient := -1, powers := [(6, 1), (9, 1), (14, 1), (22, 1), (46, 1), (52, 1), (60, 1)] }, { coefficient := 1, powers := [(6, 1), (9, 1), (15, 1), (22, 1), (45, 1), (52, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (9, 1), (22, 1), (37, 1), (45, 1), (60, 2)] }, { coefficient := -1, powers := [(9, 1), (14, 1), (22, 1), (37, 1), (38, 1), (60, 2)] }, { coefficient := 1, powers := [(9, 1), (14, 1), (22, 1), (37, 1), (46, 1), (52, 1), (60, 1)] }, { coefficient := -1, powers := [(9, 1), (15, 1), (22, 1), (37, 1), (45, 1), (52, 1), (60, 1)] }, { coefficient := -1, powers := [(20, 1), (37, 1), (38, 1), (59, 1), (60, 1)] }, { coefficient := 1, powers := [(38, 1), (60, 1)] }, { coefficient := -1, powers := [(46, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (22, 1), (52, 1)] }, { coefficient := 1, powers := [(10, 1), (32, 1), (38, 1)] }],
  [{ coefficient := -1, powers := [(1, 1), (6, 1), (7, 1), (9, 1), (22, 1), (56, 1), (60, 2)] }, { coefficient := 1, powers := [(1, 1), (6, 1), (9, 1), (14, 1), (22, 1), (57, 1), (60, 1)] }, { coefficient := 1, powers := [(1, 1), (6, 1), (9, 1), (15, 1), (22, 1), (52, 1), (56, 1), (60, 1)] }, { coefficient := 1, powers := [(1, 1), (7, 1), (9, 1), (22, 1), (37, 1), (56, 1), (60, 2)] }, { coefficient := -1, powers := [(1, 1), (9, 1), (14, 1), (22, 1), (37, 1), (57, 1), (60, 1)] }, { coefficient := -1, powers := [(1, 1), (9, 1), (15, 1), (22, 1), (37, 1), (52, 1), (56, 1), (60, 1)] }, { coefficient := 1, powers := [(1, 1), (57, 1)] }, { coefficient := 1, powers := [(6, 1), (7, 1), (9, 1), (14, 1), (22, 1), (35, 1), (60, 1)] }, { coefficient := -1, powers := [(6, 1), (9, 1), (14, 1), (15, 1), (22, 1), (27, 1), (60, 1)] }, { coefficient := -1, powers := [(7, 1), (9, 1), (14, 1), (22, 1), (35, 1), (37, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (35, 1)] }, { coefficient := -1, powers := [(9, 1), (10, 1), (27, 1), (63, 1)] }, { coefficient := 1, powers := [(9, 1), (14, 1), (15, 1), (22, 1), (27, 1), (37, 1), (60, 1)] }, { coefficient := -1, powers := [(10, 1), (27, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (4, 1), (27, 1), (37, 1), (59, 1), (60, 1)] }, { coefficient := 1, powers := [(4, 1), (20, 1), (27, 1), (37, 1), (59, 1), (60, 1)] }, { coefficient := 1, powers := [(6, 1), (7, 1), (9, 1), (14, 1), (22, 1), (27, 1), (60, 2)] }, { coefficient := 2, powers := [(6, 1), (9, 1), (10, 1), (14, 1), (22, 1), (27, 1), (46, 1), (60, 1)] }, { coefficient := 1, powers := [(6, 1), (9, 1), (14, 1), (15, 1), (22, 1), (27, 1), (52, 1), (60, 1)] }, { coefficient := 1, powers := [(6, 1), (9, 1), (15, 1), (22, 1), (43, 1), (60, 1)] }, { coefficient := -1, powers := [(7, 1), (9, 1), (14, 1), (22, 1), (27, 1), (37, 1), (60, 2)] }, { coefficient := 1, powers := [(7, 1), (27, 1), (60, 1)] }, { coefficient := -2, powers := [(9, 1), (10, 1), (14, 1), (22, 1), (27, 1), (37, 1), (46, 1), (60, 1)] }, { coefficient := -1, powers := [(9, 1), (13, 1), (15, 1), (22, 1), (37, 1), (60, 1)] }, { coefficient := -1, powers := [(9, 1), (14, 1), (15, 1), (22, 1), (27, 1), (37, 1), (52, 1), (60, 1)] }, { coefficient := 2, powers := [(10, 1), (27, 1), (46, 1)] }, { coefficient := 1, powers := [(15, 1), (27, 1), (52, 1)] }, { coefficient := -1, powers := [(15, 1), (32, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (7, 1), (22, 1), (40, 1), (60, 1)] }, { coefficient := 1, powers := [(3, 1), (7, 1), (22, 1), (31, 1), (60, 1)] }, { coefficient := -1, powers := [(4, 1), (6, 1), (7, 1), (9, 1), (22, 1), (32, 1), (60, 2)] }, { coefficient := 1, powers := [(4, 1), (6, 1), (9, 1), (15, 1), (22, 1), (32, 1), (52, 1), (60, 1)] }, { coefficient := 1, powers := [(4, 1), (7, 1), (9, 1), (22, 1), (32, 1), (37, 1), (60, 2)] }, { coefficient := -1, powers := [(4, 1), (9, 1), (15, 1), (22, 1), (32, 1), (37, 1), (52, 1), (60, 1)] }, { coefficient := -1, powers := [(6, 1), (7, 1), (9, 1), (10, 1), (22, 2), (60, 2)] }, { coefficient := 1, powers := [(6, 1), (9, 1), (10, 1), (15, 1), (22, 2), (52, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (9, 1), (10, 1), (22, 2), (37, 1), (60, 2)] }, { coefficient := 1, powers := [(7, 1), (9, 1), (20, 1), (22, 1), (60, 1)] }, { coefficient := -1, powers := [(7, 1), (20, 1), (22, 1), (50, 1), (60, 1)] }, { coefficient := -1, powers := [(9, 1), (10, 1), (15, 1), (22, 2), (37, 1), (52, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (6, 1), (14, 1), (22, 1), (40, 1), (60, 1)] }, { coefficient := -1, powers := [(0, 1), (6, 1), (15, 1), (22, 1), (40, 1), (43, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (7, 1), (22, 1), (25, 1), (40, 1), (43, 1), (60, 1)] }, { coefficient := -1, powers := [(0, 1), (7, 1), (22, 1), (34, 1), (37, 1), (40, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (10, 1), (22, 1), (40, 1), (52, 1), (63, 1)] }, { coefficient := 1, powers := [(0, 1), (10, 1), (32, 1), (38, 1), (40, 1), (63, 1)] }, { coefficient := 1, powers := [(0, 1), (13, 1), (15, 1), (22, 1), (37, 1), (40, 1), (60, 1)] }, { coefficient := -1, powers := [(0, 1), (14, 1), (22, 1), (37, 1), (40, 1), (60, 1)] }, { coefficient := 1, powers := [(3, 1), (6, 1), (14, 1), (22, 1), (31, 1), (60, 1)] }, { coefficient := -1, powers := [(3, 1), (6, 1), (15, 1), (22, 1), (31, 1), (43, 1), (60, 1)] }, { coefficient := 1, powers := [(3, 1), (7, 1), (22, 1), (25, 1), (31, 1), (43, 1), (60, 1)] }, { coefficient := -1, powers := [(3, 1), (7, 1), (22, 1), (31, 1), (34, 1), (37, 1), (60, 1)] }, { coefficient := 1, powers := [(3, 1), (10, 1), (22, 1), (31, 1), (52, 1), (63, 1)] }, { coefficient := 1, powers := [(3, 1), (10, 1), (31, 1), (32, 1), (38, 1), (63, 1)] }, { coefficient := 1, powers := [(3, 1), (13, 1), (15, 1), (22, 1), (31, 1), (37, 1), (60, 1)] }, { coefficient := -1, powers := [(3, 1), (14, 1), (22, 1), (31, 1), (37, 1), (60, 1)] }, { coefficient := 1, powers := [(4, 1), (6, 1), (9, 1), (14, 1), (22, 1), (32, 1), (60, 1)] }, { coefficient := -1, powers := [(4, 1), (9, 1), (14, 1), (22, 1), (32, 1), (37, 1), (60, 1)] }, { coefficient := 1, powers := [(4, 1), (32, 1)] }, { coefficient := -1, powers := [(6, 1), (9, 1), (10, 1), (14, 1), (22, 1), (27, 1), (60, 1)] }, { coefficient := -1, powers := [(6, 1), (9, 1), (11, 1), (20, 1), (22, 1), (43, 1), (48, 1), (60, 1), (64, 1)] }, { coefficient := 1, powers := [(6, 1), (9, 1), (11, 1), (21, 1), (22, 1), (43, 1), (60, 1), (64, 1)] }, { coefficient := 1, powers := [(6, 1), (9, 1), (14, 1), (20, 1), (22, 1), (60, 1)] }, { coefficient := -1, powers := [(6, 1), (9, 1), (15, 1), (20, 1), (22, 1), (43, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (9, 1), (20, 1), (22, 1), (25, 1), (43, 1), (60, 1)] }, { coefficient := -1, powers := [(7, 1), (9, 1), (20, 1), (22, 1), (34, 1), (37, 1), (60, 1)] }, { coefficient := 1, powers := [(9, 1), (10, 1), (14, 1), (22, 1), (27, 1), (37, 1), (60, 1)] }, { coefficient := 1, powers := [(9, 1), (10, 1), (20, 1), (22, 1), (52, 1), (63, 1)] }, { coefficient := 1, powers := [(9, 1), (10, 1), (20, 1), (32, 1), (38, 1), (63, 1)] }, { coefficient := 1, powers := [(9, 1), (11, 1), (13, 1), (20, 1), (22, 1), (37, 1), (48, 1), (60, 1), (64, 1)] }, { coefficient := -1, powers := [(9, 1), (11, 1), (13, 1), (21, 1), (22, 1), (37, 1), (60, 1), (64, 1)] }, { coefficient := 1, powers := [(9, 1), (13, 1), (15, 1), (20, 1), (22, 1), (37, 1), (60, 1)] }, { coefficient := -1, powers := [(9, 1), (14, 1), (20, 1), (22, 1), (37, 1), (60, 1)] }, { coefficient := -1, powers := [(10, 1), (27, 1)] }, { coefficient := 1, powers := [(11, 1), (20, 1), (32, 1), (38, 1), (48, 1), (64, 1)] }, { coefficient := -1, powers := [(11, 1), (21, 1), (32, 1), (38, 1), (64, 1)] }]
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
    ¬ ∀ index : Fin 29,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component37.SelectedLeafB4_5_0.selectedHasNoCommonZero

end Krenn.Component37.SelectedLeafB4_5_0
