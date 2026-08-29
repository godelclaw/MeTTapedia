import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component24.SelectedLeafB5_3_2_4_2

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "f02dea715f540d033d58cfebbf799d92e2ce1aab965994e2234858d04630bfa2"
def certificateSHA256 : String := "d1fe37b6fa9b398e497d80760aca33cbf6d89dbffabfd59a30f6b5c3fb58f91f"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 34 → Fin 679 := ![
  5,
  14,
  38,
  130,
  135,
  139,
  149,
  232,
  266,
  305,
  400,
  408,
  447,
  472,
  475,
  525,
  548,
  606,
  607,
  610,
  611,
  652,
  655,
  656,
  661,
  662,
  665,
  666,
  667,
  669,
  670,
  673,
  674,
  676
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 34 → SparsePoly (Fin 69) := ![
  [{ coefficient := 1, powers := [(11, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (35, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (35, 1)] }, { coefficient := 1, powers := [(11, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (26, 1)] }, { coefficient := 1, powers := [(16, 1), (20, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (26, 1)] }, { coefficient := 1, powers := [(16, 1), (20, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(15, 1), (21, 1)] }, { coefficient := 1, powers := [(21, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (26, 1), (48, 1)] }, { coefficient := 1, powers := [(16, 1), (21, 1)] }],
  [{ coefficient := 1, powers := [(15, 1), (21, 1), (54, 1)] }, { coefficient := 1, powers := [(15, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (44, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (56, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (20, 1), (56, 1)] }, { coefficient := 1, powers := [(11, 1), (26, 1), (44, 1)] }, { coefficient := 1, powers := [(11, 1), (35, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (26, 1), (48, 1)] }, { coefficient := 1, powers := [(16, 1), (21, 1), (51, 1)] }, { coefficient := 1, powers := [(16, 1), (26, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (54, 1)] }, { coefficient := 1, powers := [(12, 1), (22, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1), (28, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(30, 1), (42, 1)] }, { coefficient := 1, powers := [(30, 1), (46, 1)] }, { coefficient := 1, powers := [(30, 1), (53, 1)] }, { coefficient := 1, powers := [(30, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1), (53, 1)] }, { coefficient := 1, powers := [(3, 1), (35, 1), (53, 1)] }, { coefficient := 1, powers := [(15, 1), (20, 1), (53, 1)] }, { coefficient := 1, powers := [(44, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (26, 1), (60, 1)] }, { coefficient := 1, powers := [(11, 1), (26, 1), (46, 1)] }, { coefficient := 1, powers := [(16, 1), (26, 1), (42, 1)] }, { coefficient := 1, powers := [(16, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (20, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (32, 1), (44, 1)] }, { coefficient := 1, powers := [(7, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(10, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1)] }, { coefficient := 1, powers := [(3, 1), (35, 1)] }, { coefficient := 1, powers := [(15, 1), (20, 1)] }, { coefficient := 1, powers := [(20, 1), (56, 1)] }, { coefficient := 1, powers := [(26, 1), (44, 1)] }, { coefficient := 1, powers := [(35, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (50, 1)] }, { coefficient := 1, powers := [(6, 1), (32, 1)] }, { coefficient := 1, powers := [(9, 1), (26, 1)] }, { coefficient := 1, powers := [(20, 1), (50, 1)] }, { coefficient := 1, powers := [(26, 1), (41, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (60, 1)] }, { coefficient := 1, powers := [(11, 1), (46, 1)] }, { coefficient := 1, powers := [(11, 1), (57, 1)] }, { coefficient := 1, powers := [(16, 1), (42, 1)] }, { coefficient := 1, powers := [(16, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (53, 1)] }, { coefficient := 1, powers := [(23, 1), (57, 1)] }, { coefficient := 1, powers := [(28, 1), (42, 1)] }, { coefficient := 1, powers := [(28, 1), (46, 1)] }, { coefficient := 1, powers := [(33, 1), (39, 1)] }, { coefficient := 1, powers := [(36, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (39, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (42, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (46, 1), (53, 1)] }, { coefficient := 1, powers := [(42, 1)] }, { coefficient := 1, powers := [(46, 1)] }, { coefficient := 1, powers := [(53, 1)] }, { coefficient := 1, powers := [(57, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (43, 1), (57, 1)] }, { coefficient := 1, powers := [(1, 1), (48, 1), (54, 1)] }, { coefficient := 1, powers := [(7, 1), (36, 1), (43, 1)] }, { coefficient := 1, powers := [(12, 1), (22, 1), (48, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1), (28, 1), (48, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1), (48, 1), (54, 1)] }, { coefficient := 1, powers := [(16, 1), (28, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (39, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (42, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (46, 1), (53, 1)] }, { coefficient := 1, powers := [(18, 1), (30, 1), (42, 1)] }, { coefficient := 1, powers := [(18, 1), (30, 1), (46, 1)] }, { coefficient := 1, powers := [(18, 1), (30, 1), (53, 1)] }, { coefficient := 1, powers := [(18, 1), (30, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (38, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (41, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (44, 1), (50, 1)] }, { coefficient := 1, powers := [(3, 1), (26, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (32, 1), (56, 1)] }, { coefficient := 1, powers := [(3, 1), (35, 1), (50, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (32, 1), (44, 1)] }, { coefficient := 1, powers := [(6, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(9, 1), (20, 1), (56, 1)] }, { coefficient := 1, powers := [(9, 1), (26, 1), (44, 1)] }, { coefficient := 1, powers := [(9, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(15, 1), (20, 1), (50, 1)] }, { coefficient := 1, powers := [(15, 1), (26, 1), (41, 1)] }, { coefficient := 1, powers := [(15, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1), (39, 1), (60, 1)] }, { coefficient := 1, powers := [(1, 1), (42, 1), (57, 1)] }, { coefficient := 1, powers := [(1, 1), (46, 1), (53, 1)] }, { coefficient := 1, powers := [(4, 1), (28, 1), (60, 1)] }, { coefficient := 1, powers := [(4, 1), (33, 1), (57, 1)] }, { coefficient := 1, powers := [(4, 1), (36, 1), (53, 1)] }, { coefficient := 1, powers := [(7, 1), (23, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (33, 1), (46, 1)] }, { coefficient := 1, powers := [(7, 1), (36, 1), (42, 1)] }, { coefficient := 1, powers := [(11, 1), (23, 1), (57, 1)] }, { coefficient := 1, powers := [(11, 1), (28, 1), (46, 1)] }, { coefficient := 1, powers := [(11, 1), (36, 1), (39, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1), (53, 1)] }, { coefficient := 1, powers := [(16, 1), (28, 1), (42, 1)] }, { coefficient := 1, powers := [(16, 1), (33, 1), (39, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(41, 1)] }],
  [{ coefficient := 1, powers := [(43, 1), (65, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(56, 1)] }],
  [{ coefficient := 1, powers := [(26, 1), (67, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(28, 1)] }],
  [{ coefficient := 1, powers := [(59, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 34 → SparsePoly (Fin 69) := ![
  [{ coefficient := -1, powers := [(0, 1), (36, 1), (39, 1), (50, 1)] }, { coefficient := -1, powers := [(9, 1), (26, 1), (36, 1), (39, 1)] }, { coefficient := -1, powers := [(20, 1), (36, 1), (39, 1), (50, 1)] }, { coefficient := -1, powers := [(32, 1), (36, 1), (38, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (4, 1), (29, 1), (33, 1), (50, 1), (57, 1), (63, 1)] }, { coefficient := 1, powers := [(0, 1), (4, 1), (29, 1), (36, 1), (50, 1), (53, 1), (63, 1)] }, { coefficient := 1, powers := [(0, 1), (7, 1), (29, 1), (33, 1), (46, 1), (50, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (7, 1), (29, 1), (36, 1), (50, 1), (53, 1), (63, 1)] }, { coefficient := 1, powers := [(4, 1), (20, 1), (29, 1), (33, 1), (50, 1), (57, 1), (63, 1)] }, { coefficient := 1, powers := [(4, 1), (20, 1), (29, 1), (36, 1), (50, 1), (53, 1), (63, 1)] }, { coefficient := 1, powers := [(4, 1), (26, 1), (29, 1), (33, 1), (50, 1), (57, 1), (63, 1)] }, { coefficient := 1, powers := [(4, 1), (26, 1), (29, 1), (36, 1), (50, 1), (53, 1), (63, 1)] }, { coefficient := 1, powers := [(4, 1), (29, 1), (32, 1), (33, 1), (38, 1), (57, 1), (63, 1)] }, { coefficient := 1, powers := [(4, 1), (29, 1), (32, 1), (36, 1), (38, 1), (53, 1), (63, 1)] }, { coefficient := -1, powers := [(7, 1), (9, 1), (26, 1), (29, 1), (36, 1), (53, 1), (63, 1)] }, { coefficient := 1, powers := [(7, 1), (9, 1), (29, 1), (36, 1), (63, 1)] }, { coefficient := 1, powers := [(7, 1), (20, 1), (29, 1), (33, 1), (46, 1), (50, 1), (63, 1)] }, { coefficient := -1, powers := [(7, 1), (20, 1), (29, 1), (36, 1), (50, 1), (53, 1), (63, 1)] }, { coefficient := 1, powers := [(7, 1), (26, 1), (29, 1), (33, 1), (46, 1), (50, 1), (63, 1)] }, { coefficient := -1, powers := [(7, 1), (29, 1), (32, 1), (36, 1), (38, 1), (53, 1), (63, 1)] }, { coefficient := -1, powers := [(7, 1), (29, 1), (36, 1), (50, 1), (63, 1)] }, { coefficient := -1, powers := [(10, 1), (29, 1), (33, 1), (38, 1), (46, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (33, 1), (38, 1), (46, 1), (65, 1)] }, { coefficient := -1, powers := [(33, 1), (38, 1), (46, 1), (50, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (33, 1), (38, 1), (57, 1)] }, { coefficient := 1, powers := [(9, 1), (36, 1), (38, 1), (53, 1)] }, { coefficient := -1, powers := [(33, 1), (38, 1), (50, 1), (57, 1)] }, { coefficient := -1, powers := [(36, 1), (38, 1), (50, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(23, 1), (48, 1), (51, 1), (53, 1), (65, 1), (67, 1)] }, { coefficient := -1, powers := [(23, 1), (48, 1), (51, 1), (57, 1), (65, 1), (67, 1)] }, { coefficient := 1, powers := [(23, 1), (48, 1), (51, 1), (65, 1), (67, 2)] }, { coefficient := -1, powers := [(36, 1), (39, 1), (48, 1), (51, 1), (65, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (48, 1), (53, 1), (65, 1), (67, 1)] }, { coefficient := 1, powers := [(23, 1), (48, 1), (57, 1), (65, 1), (67, 1)] }, { coefficient := -1, powers := [(23, 1), (48, 1), (65, 1), (67, 2)] }, { coefficient := 1, powers := [(36, 1), (39, 1), (48, 1), (65, 1), (67, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (32, 1), (33, 1), (38, 1), (54, 1), (57, 1), (65, 1)] }, { coefficient := -1, powers := [(4, 1), (32, 1), (36, 1), (38, 1), (53, 1), (54, 1), (65, 1)] }, { coefficient := -1, powers := [(7, 1), (32, 1), (33, 1), (38, 1), (46, 1), (54, 1), (65, 1)] }, { coefficient := 1, powers := [(7, 1), (32, 1), (36, 1), (38, 1), (53, 1), (54, 1), (65, 1)] }, { coefficient := -1, powers := [(11, 1), (32, 1), (36, 1), (38, 1), (39, 1), (54, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (51, 1), (53, 1), (65, 1), (67, 1)] }, { coefficient := 1, powers := [(23, 1), (51, 1), (57, 1), (65, 1), (67, 1)] }, { coefficient := -1, powers := [(23, 1), (51, 1), (65, 1), (67, 2)] }, { coefficient := 1, powers := [(36, 1), (39, 1), (51, 1), (65, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (32, 1), (33, 1), (38, 1), (57, 1), (65, 1)] }, { coefficient := 1, powers := [(4, 1), (32, 1), (36, 1), (38, 1), (53, 1), (65, 1)] }, { coefficient := 1, powers := [(7, 1), (32, 1), (33, 1), (38, 1), (46, 1), (65, 1)] }, { coefficient := -1, powers := [(7, 1), (32, 1), (36, 1), (38, 1), (53, 1), (65, 1)] }, { coefficient := 1, powers := [(11, 1), (32, 1), (36, 1), (38, 1), (39, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (4, 1), (33, 1), (50, 1), (57, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (4, 1), (36, 1), (50, 1), (53, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (7, 1), (33, 1), (46, 1), (50, 1), (63, 1)] }, { coefficient := 1, powers := [(0, 1), (7, 1), (36, 1), (50, 1), (53, 1), (63, 1)] }, { coefficient := -1, powers := [(4, 1), (20, 1), (33, 1), (50, 1), (57, 1), (63, 1)] }, { coefficient := -1, powers := [(4, 1), (20, 1), (36, 1), (50, 1), (53, 1), (63, 1)] }, { coefficient := -1, powers := [(4, 1), (26, 1), (33, 1), (50, 1), (57, 1), (63, 1)] }, { coefficient := -1, powers := [(4, 1), (26, 1), (36, 1), (50, 1), (53, 1), (63, 1)] }, { coefficient := -1, powers := [(4, 1), (32, 1), (33, 1), (38, 1), (57, 1), (63, 1)] }, { coefficient := -1, powers := [(4, 1), (32, 1), (36, 1), (38, 1), (53, 1), (63, 1)] }, { coefficient := 1, powers := [(7, 1), (9, 1), (26, 1), (36, 1), (53, 1), (63, 1)] }, { coefficient := -1, powers := [(7, 1), (9, 1), (36, 1), (63, 1)] }, { coefficient := -1, powers := [(7, 1), (20, 1), (33, 1), (46, 1), (50, 1), (63, 1)] }, { coefficient := 1, powers := [(7, 1), (20, 1), (36, 1), (50, 1), (53, 1), (63, 1)] }, { coefficient := -1, powers := [(7, 1), (26, 1), (33, 1), (46, 1), (50, 1), (63, 1)] }, { coefficient := 1, powers := [(7, 1), (32, 1), (36, 1), (38, 1), (53, 1), (63, 1)] }, { coefficient := 1, powers := [(7, 1), (36, 1), (50, 1), (63, 1)] }, { coefficient := 1, powers := [(10, 1), (33, 1), (38, 1), (46, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (36, 1), (39, 1)] }, { coefficient := -1, powers := [(36, 1), (39, 1), (50, 1)] }],
  [{ coefficient := -1, powers := [(23, 1), (53, 1), (65, 1), (67, 1)] }, { coefficient := -1, powers := [(23, 1), (57, 1), (65, 1), (67, 1)] }, { coefficient := 1, powers := [(23, 1), (65, 1), (67, 2)] }, { coefficient := -1, powers := [(36, 1), (39, 1), (65, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(46, 1), (48, 1), (65, 1)] }, { coefficient := 1, powers := [(48, 1), (57, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (7, 1), (18, 1), (36, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (9, 1), (36, 1)] }, { coefficient := -1, powers := [(7, 1), (36, 1), (50, 1)] }],
  [{ coefficient := -1, powers := [(23, 1), (67, 1)] }],
  [{ coefficient := -1, powers := [(33, 1), (38, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (33, 1), (50, 1), (57, 1)] }, { coefficient := 1, powers := [(4, 1), (36, 1), (50, 1), (53, 1)] }, { coefficient := -1, powers := [(7, 1), (9, 1), (36, 1), (53, 1)] }, { coefficient := 1, powers := [(7, 1), (33, 1), (46, 1), (50, 1)] }, { coefficient := 1, powers := [(11, 1), (36, 1), (39, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (33, 1), (44, 1), (57, 1)] }, { coefficient := 1, powers := [(4, 1), (36, 1), (44, 1), (53, 1)] }, { coefficient := 1, powers := [(7, 1), (33, 1), (44, 1), (46, 1)] }, { coefficient := -1, powers := [(7, 1), (36, 1), (44, 1), (53, 1)] }, { coefficient := 1, powers := [(11, 1), (36, 1), (39, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (26, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(16, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (36, 1)] }],
  [{ coefficient := -1, powers := [(46, 1), (65, 1)] }, { coefficient := -1, powers := [(57, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (7, 1), (36, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (33, 1), (57, 1)] }, { coefficient := -1, powers := [(4, 1), (36, 1), (53, 1)] }, { coefficient := -1, powers := [(7, 1), (33, 1), (46, 1)] }, { coefficient := 1, powers := [(7, 1), (36, 1), (53, 1)] }, { coefficient := -1, powers := [(11, 1), (36, 1), (39, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(39, 1), (60, 1)] }, { coefficient := 1, powers := [(42, 1), (57, 1)] }, { coefficient := 1, powers := [(43, 1), (46, 1), (57, 1), (65, 1)] }, { coefficient := 1, powers := [(43, 1), (57, 2), (65, 1)] }, { coefficient := 1, powers := [(46, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (4, 1), (33, 1), (44, 1), (50, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (4, 1), (36, 1), (44, 1), (50, 1), (53, 1)] }, { coefficient := 1, powers := [(0, 1), (7, 1), (33, 1), (44, 1), (46, 1), (50, 1)] }, { coefficient := 1, powers := [(0, 1), (7, 1), (36, 1), (39, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (7, 1), (36, 1), (42, 1), (57, 1)] }, { coefficient := -1, powers := [(0, 1), (7, 1), (36, 1), (44, 1), (50, 1), (53, 1)] }, { coefficient := 1, powers := [(0, 1), (7, 1), (36, 1), (46, 1), (53, 1)] }, { coefficient := 1, powers := [(4, 1), (20, 1), (33, 1), (44, 1), (50, 1), (57, 1)] }, { coefficient := 1, powers := [(4, 1), (20, 1), (36, 1), (44, 1), (50, 1), (53, 1)] }, { coefficient := 1, powers := [(4, 1), (26, 1), (33, 1), (44, 1), (50, 1), (57, 1)] }, { coefficient := 1, powers := [(4, 1), (26, 1), (36, 1), (44, 1), (50, 1), (53, 1)] }, { coefficient := 1, powers := [(4, 1), (32, 1), (33, 1), (38, 1), (44, 1), (57, 1)] }, { coefficient := 1, powers := [(4, 1), (32, 1), (36, 1), (38, 1), (44, 1), (53, 1)] }, { coefficient := -1, powers := [(7, 1), (9, 1), (26, 1), (36, 1), (44, 1), (53, 1)] }, { coefficient := 1, powers := [(7, 1), (9, 1), (36, 1), (44, 1)] }, { coefficient := 1, powers := [(7, 1), (20, 1), (33, 1), (44, 1), (46, 1), (50, 1)] }, { coefficient := -1, powers := [(7, 1), (20, 1), (36, 1), (44, 1), (50, 1), (53, 1)] }, { coefficient := 1, powers := [(7, 1), (26, 1), (33, 1), (44, 1), (46, 1), (50, 1)] }, { coefficient := -1, powers := [(7, 1), (32, 1), (36, 1), (38, 1), (44, 1), (53, 1)] }, { coefficient := -1, powers := [(7, 1), (36, 1), (44, 1), (50, 1)] }, { coefficient := -1, powers := [(10, 1), (33, 1), (38, 1), (44, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (6, 1), (33, 1), (35, 1), (57, 1)] }, { coefficient := 1, powers := [(4, 1), (6, 1), (35, 1), (36, 1), (53, 1)] }, { coefficient := 1, powers := [(4, 1), (15, 1), (26, 1), (33, 1), (57, 1)] }, { coefficient := 1, powers := [(4, 1), (15, 1), (26, 1), (36, 1), (53, 1)] }, { coefficient := -1, powers := [(4, 1), (26, 1), (33, 1), (44, 1), (57, 1)] }, { coefficient := -1, powers := [(4, 1), (26, 1), (36, 1), (44, 1), (53, 1)] }, { coefficient := 1, powers := [(6, 1), (7, 1), (33, 1), (35, 1), (46, 1)] }, { coefficient := -1, powers := [(6, 1), (7, 1), (35, 1), (36, 1), (53, 1)] }, { coefficient := 1, powers := [(6, 1), (11, 1), (35, 1), (36, 1), (39, 1)] }, { coefficient := 1, powers := [(7, 1), (15, 1), (26, 1), (33, 1), (46, 1)] }, { coefficient := -1, powers := [(7, 1), (15, 1), (26, 1), (36, 1), (53, 1)] }, { coefficient := -1, powers := [(7, 1), (26, 1), (33, 1), (44, 1), (46, 1)] }, { coefficient := 1, powers := [(7, 1), (26, 1), (36, 1), (44, 1), (53, 1)] }, { coefficient := 1, powers := [(7, 1), (33, 1), (35, 1), (38, 1), (46, 1)] }, { coefficient := 1, powers := [(11, 1), (15, 1), (26, 1), (36, 1), (39, 1)] }, { coefficient := -1, powers := [(11, 1), (26, 1), (36, 1), (39, 1), (44, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (15, 1), (32, 1), (33, 1), (38, 1), (57, 1)] }, { coefficient := -1, powers := [(4, 1), (15, 1), (32, 1), (36, 1), (38, 1), (53, 1)] }, { coefficient := -1, powers := [(7, 1), (9, 1), (33, 1), (35, 1), (38, 1), (46, 1)] }, { coefficient := -1, powers := [(7, 1), (15, 1), (32, 1), (33, 1), (38, 1), (46, 1)] }, { coefficient := 1, powers := [(7, 1), (15, 1), (32, 1), (36, 1), (38, 1), (53, 1)] }, { coefficient := 1, powers := [(7, 1), (33, 1), (35, 1), (38, 1), (46, 1), (50, 1)] }, { coefficient := 1, powers := [(7, 1), (36, 1), (46, 1)] }, { coefficient := 1, powers := [(7, 1), (36, 1), (57, 1)] }, { coefficient := -1, powers := [(11, 1), (15, 1), (32, 1), (36, 1), (38, 1), (39, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1), (53, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1), (57, 1)] }, { coefficient := -1, powers := [(16, 1), (23, 1), (67, 1)] }, { coefficient := 1, powers := [(16, 1), (36, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (4, 1), (18, 1), (24, 1), (33, 1), (50, 1), (57, 1), (63, 1)] }, { coefficient := 1, powers := [(0, 1), (4, 1), (18, 1), (24, 1), (36, 1), (50, 1), (53, 1), (63, 1)] }, { coefficient := 1, powers := [(0, 1), (4, 1), (33, 1), (41, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (4, 1), (36, 1), (41, 1), (53, 1)] }, { coefficient := 1, powers := [(0, 1), (7, 1), (18, 1), (24, 1), (33, 1), (46, 1), (50, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (7, 1), (18, 1), (24, 1), (36, 1), (50, 1), (53, 1), (63, 1)] }, { coefficient := 1, powers := [(0, 1), (7, 1), (33, 1), (41, 1), (46, 1)] }, { coefficient := -1, powers := [(0, 1), (7, 1), (36, 1), (41, 1), (53, 1)] }, { coefficient := 1, powers := [(0, 1), (11, 1), (36, 1), (39, 1), (41, 1)] }, { coefficient := 1, powers := [(3, 1), (4, 1), (32, 1), (33, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (4, 1), (32, 1), (36, 1), (53, 1)] }, { coefficient := 1, powers := [(3, 1), (7, 1), (32, 1), (33, 1), (46, 1)] }, { coefficient := -1, powers := [(3, 1), (7, 1), (32, 1), (36, 1), (53, 1)] }, { coefficient := 1, powers := [(3, 1), (11, 1), (32, 1), (36, 1), (39, 1)] }, { coefficient := 1, powers := [(4, 1), (9, 1), (20, 1), (33, 1), (57, 1)] }, { coefficient := 1, powers := [(4, 1), (9, 1), (20, 1), (36, 1), (53, 1)] }, { coefficient := 1, powers := [(4, 1), (18, 1), (20, 1), (24, 1), (33, 1), (50, 1), (57, 1), (63, 1)] }, { coefficient := 1, powers := [(4, 1), (18, 1), (20, 1), (24, 1), (36, 1), (50, 1), (53, 1), (63, 1)] }, { coefficient := 1, powers := [(4, 1), (18, 1), (24, 1), (26, 1), (33, 1), (50, 1), (57, 1), (63, 1)] }, { coefficient := 1, powers := [(4, 1), (18, 1), (24, 1), (26, 1), (36, 1), (50, 1), (53, 1), (63, 1)] }, { coefficient := 1, powers := [(4, 1), (18, 1), (24, 1), (32, 1), (33, 1), (38, 1), (57, 1), (63, 1)] }, { coefficient := 1, powers := [(4, 1), (18, 1), (24, 1), (32, 1), (36, 1), (38, 1), (53, 1), (63, 1)] }, { coefficient := -1, powers := [(4, 1), (20, 1), (33, 1), (50, 1), (57, 1)] }, { coefficient := -1, powers := [(4, 1), (20, 1), (36, 1), (50, 1), (53, 1)] }, { coefficient := 1, powers := [(4, 1), (21, 1), (32, 1), (33, 1), (38, 1), (54, 1), (57, 1), (65, 1)] }, { coefficient := 1, powers := [(4, 1), (21, 1), (32, 1), (36, 1), (38, 1), (53, 1), (54, 1), (65, 1)] }, { coefficient := -1, powers := [(7, 1), (9, 1), (18, 1), (24, 1), (26, 1), (36, 1), (53, 1), (63, 1)] }, { coefficient := 1, powers := [(7, 1), (9, 1), (18, 1), (24, 1), (36, 1), (63, 1)] }, { coefficient := 1, powers := [(7, 1), (9, 1), (20, 1), (33, 1), (46, 1)] }, { coefficient := 1, powers := [(7, 1), (18, 1), (20, 1), (24, 1), (33, 1), (46, 1), (50, 1), (63, 1)] }, { coefficient := -1, powers := [(7, 1), (18, 1), (20, 1), (24, 1), (36, 1), (50, 1), (53, 1), (63, 1)] }, { coefficient := 1, powers := [(7, 1), (18, 1), (24, 1), (26, 1), (33, 1), (46, 1), (50, 1), (63, 1)] }, { coefficient := -1, powers := [(7, 1), (18, 1), (24, 1), (32, 1), (36, 1), (38, 1), (53, 1), (63, 1)] }, { coefficient := -1, powers := [(7, 1), (18, 1), (24, 1), (36, 1), (50, 1), (63, 1)] }, { coefficient := -1, powers := [(7, 1), (20, 1), (33, 1), (46, 1), (50, 1)] }, { coefficient := 1, powers := [(7, 1), (21, 1), (32, 1), (33, 1), (38, 1), (46, 1), (54, 1), (65, 1)] }, { coefficient := -1, powers := [(7, 1), (21, 1), (32, 1), (36, 1), (38, 1), (53, 1), (54, 1), (65, 1)] }, { coefficient := -1, powers := [(9, 1), (11, 1), (33, 1), (38, 1), (57, 1)] }, { coefficient := -1, powers := [(9, 1), (11, 1), (36, 1), (38, 1), (53, 1)] }, { coefficient := -1, powers := [(10, 1), (18, 1), (24, 1), (33, 1), (38, 1), (46, 1), (63, 1)] }, { coefficient := 1, powers := [(11, 1), (21, 1), (32, 1), (36, 1), (38, 1), (39, 1), (54, 1), (65, 1)] }, { coefficient := 1, powers := [(11, 1), (33, 1), (38, 1), (50, 1), (57, 1)] }, { coefficient := 1, powers := [(11, 1), (36, 1), (38, 1), (50, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (23, 1), (60, 1)] }, { coefficient := -1, powers := [(11, 1), (23, 1), (57, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1), (43, 1), (53, 1), (65, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1), (43, 1), (57, 1), (65, 1)] }, { coefficient := -1, powers := [(16, 1), (23, 1), (43, 1), (65, 1), (67, 1)] }, { coefficient := -1, powers := [(16, 1), (23, 1), (53, 1)] }, { coefficient := 1, powers := [(16, 1), (36, 1), (39, 1), (43, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (60, 1)] }, { coefficient := 1, powers := [(11, 1), (46, 1)] }, { coefficient := 1, powers := [(16, 1), (43, 1), (46, 1), (65, 1)] }, { coefficient := 1, powers := [(16, 1), (43, 1), (57, 1), (65, 1)] }, { coefficient := -1, powers := [(16, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (4, 1), (33, 1), (38, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (4, 1), (36, 1), (38, 1), (53, 1)] }, { coefficient := 1, powers := [(0, 1), (7, 1), (33, 1), (38, 1), (46, 1)] }, { coefficient := -1, powers := [(0, 1), (7, 1), (36, 1), (38, 1), (53, 1)] }, { coefficient := 1, powers := [(0, 1), (11, 1), (36, 1), (38, 1), (39, 1)] }, { coefficient := 1, powers := [(3, 1), (4, 1), (26, 1), (33, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (4, 1), (26, 1), (36, 1), (53, 1)] }, { coefficient := 1, powers := [(3, 1), (7, 1), (26, 1), (33, 1), (46, 1)] }, { coefficient := -1, powers := [(3, 1), (7, 1), (26, 1), (36, 1), (53, 1)] }, { coefficient := 1, powers := [(3, 1), (11, 1), (26, 1), (36, 1), (39, 1)] }, { coefficient := 1, powers := [(4, 1), (6, 1), (20, 1), (33, 1), (57, 1)] }, { coefficient := 1, powers := [(4, 1), (6, 1), (20, 1), (36, 1), (53, 1)] }, { coefficient := 1, powers := [(6, 1), (7, 1), (20, 1), (33, 1), (46, 1)] }, { coefficient := -1, powers := [(6, 1), (7, 1), (20, 1), (36, 1), (53, 1)] }, { coefficient := 1, powers := [(6, 1), (11, 1), (20, 1), (36, 1), (39, 1)] }, { coefficient := 1, powers := [(7, 1), (20, 1), (33, 1), (38, 1), (46, 1)] }]
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
    (values : Fin 69 → R) :
    ¬ ∀ index : Fin 34,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component24.SelectedLeafB5_3_2_4_2.selectedHasNoCommonZero

end Krenn.Component24.SelectedLeafB5_3_2_4_2
