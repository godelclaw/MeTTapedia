import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component37.SelectedLeafB5_3_6_4_2_6

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "6aec90ea1f9f2413ed8e8b1c010292a26b23509877d8ecf30f285c4b435f32a9"
def certificateSHA256 : String := "39cdd8239270d94b7350c4a4f26f5a6b25f49c54f4fe6037d085997aae323ad3"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 30 → Fin 676 := ![
  17,
  21,
  147,
  298,
  299,
  300,
  301,
  303,
  354,
  363,
  373,
  504,
  583,
  588,
  590,
  602,
  603,
  605,
  655,
  656,
  659,
  660,
  661,
  663,
  664,
  665,
  668,
  670,
  673,
  674
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 30 → SparsePoly (Fin 72) := ![
  [{ coefficient := 1, powers := [(18, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (31, 1)] }, { coefficient := 1, powers := [(15, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (46, 1)] }, { coefficient := 1, powers := [(4, 1), (35, 1)] }, { coefficient := 1, powers := [(15, 1), (22, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (52, 1)] }, { coefficient := 1, powers := [(7, 1), (32, 1)] }, { coefficient := 1, powers := [(10, 1), (27, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (50, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (50, 1)] }, { coefficient := 1, powers := [(18, 1), (28, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (59, 1)] }, { coefficient := 1, powers := [(9, 1), (43, 1)] }, { coefficient := 1, powers := [(13, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (46, 1)] }, { coefficient := 1, powers := [(9, 1), (57, 1)] }, { coefficient := 1, powers := [(31, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (31, 1), (57, 1)] }, { coefficient := 1, powers := [(7, 1), (31, 1), (46, 1)] }, { coefficient := 1, powers := [(15, 1), (31, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (22, 1), (59, 1)] }, { coefficient := 1, powers := [(9, 1), (22, 1), (56, 1)] }, { coefficient := 1, powers := [(13, 1), (22, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (22, 1), (57, 1)] }, { coefficient := 1, powers := [(9, 1), (27, 1), (46, 1)] }, { coefficient := 1, powers := [(9, 1), (35, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (25, 1), (59, 1)] }, { coefficient := 1, powers := [(4, 1), (31, 1), (56, 1)] }, { coefficient := 1, powers := [(4, 1), (34, 1), (50, 1)] }, { coefficient := 1, powers := [(14, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (31, 1), (57, 1)] }, { coefficient := 1, powers := [(9, 1), (20, 1), (57, 1)] }, { coefficient := 1, powers := [(9, 1)] }, { coefficient := 1, powers := [(40, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (41, 1), (56, 1)] }, { coefficient := 1, powers := [(1, 1), (45, 1)] }, { coefficient := 1, powers := [(4, 1), (32, 1), (56, 1)] }, { coefficient := 1, powers := [(10, 1), (22, 1), (56, 1)] }, { coefficient := 1, powers := [(14, 1), (22, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (42, 1), (57, 1)] }, { coefficient := 1, powers := [(1, 1), (48, 1), (53, 1)] }, { coefficient := 1, powers := [(7, 1), (35, 1), (42, 1)] }, { coefficient := 1, powers := [(11, 1), (27, 1), (48, 1)] }, { coefficient := 1, powers := [(15, 1), (27, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1)] }, { coefficient := 1, powers := [(3, 1), (34, 1)] }, { coefficient := 1, powers := [(13, 1), (20, 1)] }, { coefficient := 1, powers := [(20, 1), (56, 1)] }, { coefficient := 1, powers := [(25, 1), (43, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (50, 1)] }, { coefficient := 1, powers := [(6, 1), (31, 1)] }, { coefficient := 1, powers := [(9, 1), (25, 1)] }, { coefficient := 1, powers := [(20, 1), (50, 1)] }, { coefficient := 1, powers := [(25, 1), (40, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (52, 1)] }, { coefficient := 1, powers := [(22, 1), (57, 1)] }, { coefficient := 1, powers := [(27, 1), (41, 1)] }, { coefficient := 1, powers := [(27, 1), (46, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1)] }, { coefficient := 1, powers := [(35, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (37, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (40, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (43, 1), (50, 1)] }, { coefficient := 1, powers := [(3, 1), (25, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (31, 1), (56, 1)] }, { coefficient := 1, powers := [(3, 1), (34, 1), (50, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (31, 1), (43, 1)] }, { coefficient := 1, powers := [(6, 1), (34, 1), (40, 1)] }, { coefficient := 1, powers := [(9, 1), (20, 1), (56, 1)] }, { coefficient := 1, powers := [(9, 1), (25, 1), (43, 1)] }, { coefficient := 1, powers := [(9, 1), (34, 1), (37, 1)] }, { coefficient := 1, powers := [(13, 1), (20, 1), (50, 1)] }, { coefficient := 1, powers := [(13, 1), (25, 1), (40, 1)] }, { coefficient := 1, powers := [(13, 1), (31, 1), (37, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1), (38, 1), (60, 1)] }, { coefficient := 1, powers := [(1, 1), (41, 1), (57, 1)] }, { coefficient := 1, powers := [(1, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(4, 1), (27, 1), (60, 1)] }, { coefficient := 1, powers := [(4, 1), (32, 1), (57, 1)] }, { coefficient := 1, powers := [(4, 1), (35, 1), (52, 1)] }, { coefficient := 1, powers := [(7, 1), (22, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (32, 1), (46, 1)] }, { coefficient := 1, powers := [(7, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(10, 1), (22, 1), (57, 1)] }, { coefficient := 1, powers := [(10, 1), (27, 1), (46, 1)] }, { coefficient := 1, powers := [(10, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(15, 1), (22, 1), (52, 1)] }, { coefficient := 1, powers := [(15, 1), (27, 1), (41, 1)] }, { coefficient := 1, powers := [(15, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(40, 1)] }],
  [{ coefficient := 1, powers := [(42, 1), (65, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(56, 1), (66, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(57, 1), (67, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(27, 1)] }],
  [{ coefficient := 1, powers := [(59, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (70, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(4, 1), (71, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 30 → SparsePoly (Fin 72) := ![
  [{ coefficient := 1, powers := [(0, 1), (23, 1), (43, 1), (63, 1)] }, { coefficient := 1, powers := [(3, 1), (14, 1), (23, 1), (63, 1), (71, 1)] }, { coefficient := 1, powers := [(3, 1), (23, 1), (34, 1), (63, 1)] }, { coefficient := 1, powers := [(13, 1), (14, 1), (23, 1), (37, 1), (63, 1), (66, 1), (71, 1)] }, { coefficient := 1, powers := [(13, 1), (23, 1), (34, 1), (37, 1), (63, 1), (66, 1)] }, { coefficient := 1, powers := [(20, 1), (23, 1), (43, 1), (63, 1)] }, { coefficient := 1, powers := [(20, 1), (23, 1), (56, 1), (63, 1)] }, { coefficient := 1, powers := [(23, 1), (25, 1), (43, 1), (63, 1)] }, { coefficient := 1, powers := [(23, 1), (34, 1), (37, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (20, 1), (34, 1), (52, 1)] }, { coefficient := -1, powers := [(4, 1), (34, 2), (37, 1), (52, 1), (66, 1)] }, { coefficient := -1, powers := [(7, 1), (13, 1), (20, 1), (56, 1), (60, 1), (66, 1)] }, { coefficient := -1, powers := [(7, 1), (13, 1), (34, 1), (37, 1), (56, 1), (60, 1), (66, 2)] }, { coefficient := -1, powers := [(10, 1), (13, 1), (20, 1), (46, 1)] }, { coefficient := -1, powers := [(10, 1), (13, 1), (34, 1), (37, 1), (46, 1), (66, 1)] }, { coefficient := -1, powers := [(13, 1), (14, 1), (20, 1), (46, 1), (66, 1)] }, { coefficient := -1, powers := [(13, 1), (14, 1), (34, 1), (37, 1), (46, 1), (66, 2)] }, { coefficient := -2, powers := [(13, 1), (15, 1), (20, 1), (46, 1), (56, 1), (66, 1)] }, { coefficient := 1, powers := [(13, 1), (15, 1), (20, 1), (52, 1), (56, 1), (66, 1)] }, { coefficient := -2, powers := [(13, 1), (15, 1), (20, 1), (56, 1), (57, 1), (66, 1)] }, { coefficient := -2, powers := [(13, 1), (15, 1), (34, 1), (37, 1), (46, 1), (56, 1), (66, 2)] }, { coefficient := 1, powers := [(13, 1), (15, 1), (34, 1), (37, 1), (52, 1), (56, 1), (66, 2)] }, { coefficient := -2, powers := [(13, 1), (15, 1), (34, 1), (37, 1), (56, 1), (57, 1), (66, 2)] }, { coefficient := -1, powers := [(14, 1), (20, 1), (52, 1)] }, { coefficient := -1, powers := [(14, 1), (34, 1), (37, 1), (52, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(20, 1), (22, 1), (46, 1), (56, 1)] }, { coefficient := -1, powers := [(22, 1), (34, 1), (37, 1), (46, 1), (56, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (20, 1), (52, 1), (56, 1)] }, { coefficient := 1, powers := [(9, 1), (34, 1), (37, 1), (52, 1), (56, 1), (66, 1)] }, { coefficient := 1, powers := [(20, 1), (31, 1), (38, 1), (56, 1)] }, { coefficient := 1, powers := [(31, 1), (34, 1), (37, 1), (38, 1), (56, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (20, 1), (46, 1), (56, 1)] }, { coefficient := 1, powers := [(9, 1), (34, 1), (37, 1), (46, 1), (56, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (43, 1), (63, 1)] }, { coefficient := -1, powers := [(3, 1), (14, 1), (63, 1), (71, 1)] }, { coefficient := -1, powers := [(3, 1), (34, 1), (63, 1)] }, { coefficient := -1, powers := [(13, 1), (14, 1), (37, 1), (63, 1), (66, 1), (71, 1)] }, { coefficient := -1, powers := [(13, 1), (34, 1), (37, 1), (63, 1), (66, 1)] }, { coefficient := -1, powers := [(20, 1), (43, 1), (63, 1)] }, { coefficient := -1, powers := [(20, 1), (56, 1), (63, 1)] }, { coefficient := -1, powers := [(25, 1), (43, 1), (63, 1)] }, { coefficient := -1, powers := [(34, 1), (37, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (37, 1), (70, 1)] }, { coefficient := 1, powers := [(37, 1), (67, 1), (70, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (20, 1), (32, 1), (56, 1)] }, { coefficient := 1, powers := [(4, 1), (32, 1), (34, 1), (37, 1), (56, 1), (66, 1)] }, { coefficient := -2, powers := [(15, 1), (20, 1), (22, 1), (56, 1)] }, { coefficient := -2, powers := [(15, 1), (22, 1), (34, 1), (37, 1), (56, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (22, 1), (56, 1)] }, { coefficient := 1, powers := [(22, 1), (34, 1), (37, 1), (56, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (20, 1), (56, 1), (60, 1), (66, 1)] }, { coefficient := 1, powers := [(7, 1), (34, 1), (37, 1), (56, 1), (60, 1), (66, 2)] }, { coefficient := 1, powers := [(10, 1), (20, 1), (46, 1)] }, { coefficient := 1, powers := [(10, 1), (34, 1), (37, 1), (46, 1), (66, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1), (46, 1), (66, 1)] }, { coefficient := 1, powers := [(14, 1), (34, 1), (37, 1), (46, 1), (66, 2)] }, { coefficient := 2, powers := [(15, 1), (20, 1), (46, 1), (56, 1), (66, 1)] }, { coefficient := -1, powers := [(15, 1), (20, 1), (52, 1), (56, 1), (66, 1)] }, { coefficient := 2, powers := [(15, 1), (20, 1), (56, 1), (57, 1), (66, 1)] }, { coefficient := 2, powers := [(15, 1), (34, 1), (37, 1), (46, 1), (56, 1), (66, 2)] }, { coefficient := -1, powers := [(15, 1), (34, 1), (37, 1), (52, 1), (56, 1), (66, 2)] }, { coefficient := 2, powers := [(15, 1), (34, 1), (37, 1), (56, 1), (57, 1), (66, 2)] }],
  [{ coefficient := 1, powers := [(10, 1), (20, 1), (56, 1)] }, { coefficient := 1, powers := [(10, 1), (34, 1), (37, 1), (56, 1), (66, 1)] }, { coefficient := -1, powers := [(15, 1), (20, 1), (56, 1)] }, { coefficient := -1, powers := [(15, 1), (34, 1), (37, 1), (56, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (71, 1)] }, { coefficient := 1, powers := [(13, 1), (37, 1), (66, 1), (71, 1)] }, { coefficient := 1, powers := [(20, 1), (22, 1), (52, 1)] }, { coefficient := 1, powers := [(22, 1), (34, 1), (37, 1), (52, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(37, 1), (43, 1), (67, 1), (70, 1)] }],
  [{ coefficient := -1, powers := [(9, 1), (20, 1), (46, 1)] }, { coefficient := -1, powers := [(9, 1), (34, 1), (37, 1), (46, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (20, 1), (41, 1), (56, 1), (65, 1)] }, { coefficient := 1, powers := [(9, 1), (34, 1), (37, 1), (41, 1), (56, 1), (65, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(50, 1)] }],
  [{ coefficient := 1, powers := [(43, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (20, 1), (31, 1), (56, 1)] }, { coefficient := -1, powers := [(4, 1), (31, 1), (34, 1), (37, 1), (56, 1), (66, 1)] }, { coefficient := 1, powers := [(9, 1), (15, 1), (20, 1), (56, 1)] }, { coefficient := 1, powers := [(9, 1), (15, 1), (34, 1), (37, 1), (56, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(9, 1), (20, 1), (56, 1)] }, { coefficient := -1, powers := [(9, 1), (34, 1), (37, 1), (56, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (20, 1), (38, 1), (56, 1), (60, 1)] }, { coefficient := -1, powers := [(9, 1), (20, 1), (41, 1), (42, 1), (56, 1), (57, 1), (65, 1)] }, { coefficient := 1, powers := [(9, 1), (20, 1), (41, 1), (46, 1), (56, 1)] }, { coefficient := -1, powers := [(9, 1), (20, 1), (41, 1), (48, 1), (53, 1), (56, 1), (65, 1)] }, { coefficient := 1, powers := [(9, 1), (20, 1), (41, 1), (56, 1), (57, 1)] }, { coefficient := 1, powers := [(9, 1), (20, 1), (45, 1), (46, 1)] }, { coefficient := -1, powers := [(9, 1), (20, 1), (46, 1), (52, 1), (56, 1)] }, { coefficient := 1, powers := [(9, 1), (34, 1), (37, 1), (38, 1), (56, 1), (60, 1), (66, 1)] }, { coefficient := -1, powers := [(9, 1), (34, 1), (37, 1), (41, 1), (42, 1), (56, 1), (57, 1), (65, 1), (66, 1)] }, { coefficient := 1, powers := [(9, 1), (34, 1), (37, 1), (41, 1), (46, 1), (56, 1), (66, 1)] }, { coefficient := -1, powers := [(9, 1), (34, 1), (37, 1), (41, 1), (48, 1), (53, 1), (56, 1), (65, 1), (66, 1)] }, { coefficient := 1, powers := [(9, 1), (34, 1), (37, 1), (41, 1), (56, 1), (57, 1), (66, 1)] }, { coefficient := 1, powers := [(9, 1), (34, 1), (37, 1), (45, 1), (46, 1), (66, 1)] }, { coefficient := -1, powers := [(9, 1), (34, 1), (37, 1), (46, 1), (52, 1), (56, 1), (66, 1)] }, { coefficient := -1, powers := [(20, 1), (31, 1), (38, 1), (46, 1), (56, 1)] }, { coefficient := -1, powers := [(31, 1), (34, 1), (37, 1), (38, 1), (46, 1), (56, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1), (50, 1)] }, { coefficient := 1, powers := [(3, 1), (14, 1), (50, 1), (71, 1)] }, { coefficient := 1, powers := [(3, 1), (34, 1), (50, 1)] }, { coefficient := 1, powers := [(13, 1), (14, 1), (37, 1), (50, 1), (66, 1), (71, 1)] }, { coefficient := 1, powers := [(13, 1), (34, 1), (37, 1), (50, 1), (66, 1)] }, { coefficient := 1, powers := [(20, 1), (43, 1), (50, 1)] }, { coefficient := 1, powers := [(20, 1), (50, 1), (56, 1)] }, { coefficient := 1, powers := [(25, 1), (43, 1), (50, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (18, 1), (28, 1), (43, 1), (63, 1)] }, { coefficient := 1, powers := [(0, 1), (37, 1), (43, 1), (57, 1), (67, 1), (70, 1)] }, { coefficient := 1, powers := [(0, 1), (56, 1)] }, { coefficient := 1, powers := [(3, 1), (14, 1), (18, 1), (28, 1), (63, 1), (71, 1)] }, { coefficient := 1, powers := [(3, 1), (18, 1), (28, 1), (34, 1), (63, 1)] }, { coefficient := 1, powers := [(6, 1), (34, 1)] }, { coefficient := 1, powers := [(13, 1), (14, 1), (18, 1), (28, 1), (37, 1), (63, 1), (66, 1), (71, 1)] }, { coefficient := 1, powers := [(13, 1), (18, 1), (28, 1), (34, 1), (37, 1), (63, 1), (66, 1)] }, { coefficient := -1, powers := [(13, 1), (20, 1), (37, 1), (70, 1)] }, { coefficient := 1, powers := [(13, 1), (25, 1)] }, { coefficient := -1, powers := [(13, 1), (37, 1), (67, 1), (70, 1)] }, { coefficient := 1, powers := [(15, 1), (20, 1), (22, 1), (46, 1), (56, 1)] }, { coefficient := 1, powers := [(15, 1), (22, 1), (34, 1), (37, 1), (46, 1), (56, 1), (66, 1)] }, { coefficient := 1, powers := [(18, 1), (20, 1), (28, 1), (43, 1), (63, 1)] }, { coefficient := 1, powers := [(18, 1), (20, 1), (28, 1), (56, 1), (63, 1)] }, { coefficient := 1, powers := [(18, 1), (25, 1), (28, 1), (43, 1), (63, 1)] }, { coefficient := 1, powers := [(18, 1), (28, 1), (34, 1), (37, 1), (63, 1)] }, { coefficient := -1, powers := [(25, 1), (43, 1)] }, { coefficient := 1, powers := [(37, 1), (43, 1), (67, 1), (70, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (9, 1), (20, 1), (35, 1), (41, 1), (56, 1)] }, { coefficient := -1, powers := [(7, 1), (9, 1), (34, 1), (35, 1), (37, 1), (41, 1), (56, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (9, 1), (20, 1), (22, 1), (56, 1), (60, 1)] }, { coefficient := -1, powers := [(7, 1), (9, 1), (22, 1), (34, 1), (37, 1), (56, 1), (60, 1), (66, 1)] }, { coefficient := -1, powers := [(9, 1), (14, 1), (20, 1), (22, 1), (46, 1)] }, { coefficient := -1, powers := [(9, 1), (14, 1), (22, 1), (34, 1), (37, 1), (46, 1), (66, 1)] }, { coefficient := -2, powers := [(9, 1), (15, 1), (20, 1), (22, 1), (46, 1), (56, 1)] }, { coefficient := 1, powers := [(9, 1), (15, 1), (20, 1), (22, 1), (52, 1), (56, 1)] }, { coefficient := -2, powers := [(9, 1), (15, 1), (20, 1), (22, 1), (56, 1), (57, 1)] }, { coefficient := -2, powers := [(9, 1), (15, 1), (22, 1), (34, 1), (37, 1), (46, 1), (56, 1), (66, 1)] }, { coefficient := 1, powers := [(9, 1), (15, 1), (22, 1), (34, 1), (37, 1), (52, 1), (56, 1), (66, 1)] }, { coefficient := -2, powers := [(9, 1), (15, 1), (22, 1), (34, 1), (37, 1), (56, 1), (57, 1), (66, 1)] }, { coefficient := -1, powers := [(9, 1), (34, 1), (37, 1)] }, { coefficient := -1, powers := [(13, 1), (31, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (31, 1), (37, 1), (43, 1), (70, 1)] }, { coefficient := 1, powers := [(9, 1), (20, 1), (37, 1), (43, 1), (70, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (9, 1), (20, 1), (56, 1), (60, 1)] }, { coefficient := 1, powers := [(4, 1), (9, 1), (34, 1), (37, 1), (56, 1), (60, 1), (66, 1)] }, { coefficient := 1, powers := [(4, 1), (20, 1), (31, 1), (41, 1), (56, 1)] }, { coefficient := 1, powers := [(4, 1), (20, 1), (31, 1), (46, 1), (56, 1)] }, { coefficient := 1, powers := [(4, 1), (31, 1), (34, 1), (37, 1), (41, 1), (56, 1), (66, 1)] }, { coefficient := 1, powers := [(4, 1), (31, 1), (34, 1), (37, 1), (46, 1), (56, 1), (66, 1)] }, { coefficient := -1, powers := [(9, 1), (10, 1), (20, 1), (46, 1), (56, 1)] }, { coefficient := -1, powers := [(9, 1), (10, 1), (34, 1), (37, 1), (46, 1), (56, 1), (66, 1)] }, { coefficient := -1, powers := [(9, 1), (11, 1), (20, 1), (41, 1), (48, 1), (56, 1), (65, 1)] }, { coefficient := -1, powers := [(9, 1), (11, 1), (34, 1), (37, 1), (41, 1), (48, 1), (56, 1), (65, 1), (66, 1)] }, { coefficient := -1, powers := [(9, 1), (15, 1), (20, 1), (41, 1), (42, 1), (56, 1), (65, 1)] }, { coefficient := -1, powers := [(9, 1), (15, 1), (34, 1), (37, 1), (41, 1), (42, 1), (56, 1), (65, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (37, 1)] }, { coefficient := -1, powers := [(3, 1), (4, 1), (25, 1), (71, 1)] }, { coefficient := -1, powers := [(3, 1), (20, 1), (37, 1), (70, 1)] }, { coefficient := 1, powers := [(3, 1), (25, 1)] }, { coefficient := -1, powers := [(3, 1), (37, 1), (67, 1), (70, 1)] }, { coefficient := -1, powers := [(4, 1), (13, 1), (25, 1), (37, 1), (66, 1), (71, 1)] }, { coefficient := -1, powers := [(4, 1), (20, 1), (22, 1), (25, 1), (52, 1)] }, { coefficient := -1, powers := [(4, 1), (22, 1), (25, 1), (34, 1), (37, 1), (52, 1), (66, 1)] }, { coefficient := -1, powers := [(6, 1), (7, 1), (20, 1), (22, 1), (56, 1), (60, 1), (66, 1)] }, { coefficient := -1, powers := [(6, 1), (7, 1), (22, 1), (34, 1), (37, 1), (56, 1), (60, 1), (66, 2)] }, { coefficient := -1, powers := [(6, 1), (10, 1), (20, 1), (22, 1), (46, 1)] }, { coefficient := -1, powers := [(6, 1), (10, 1), (22, 1), (34, 1), (37, 1), (46, 1), (66, 1)] }, { coefficient := -1, powers := [(6, 1), (14, 1), (20, 1), (22, 1), (46, 1), (66, 1)] }, { coefficient := -1, powers := [(6, 1), (14, 1), (22, 1), (34, 1), (37, 1), (46, 1), (66, 2)] }, { coefficient := -2, powers := [(6, 1), (15, 1), (20, 1), (22, 1), (46, 1), (56, 1), (66, 1)] }, { coefficient := 1, powers := [(6, 1), (15, 1), (20, 1), (22, 1), (52, 1), (56, 1), (66, 1)] }, { coefficient := -2, powers := [(6, 1), (15, 1), (20, 1), (22, 1), (56, 1), (57, 1), (66, 1)] }, { coefficient := -2, powers := [(6, 1), (15, 1), (22, 1), (34, 1), (37, 1), (46, 1), (56, 1), (66, 2)] }, { coefficient := 1, powers := [(6, 1), (15, 1), (22, 1), (34, 1), (37, 1), (52, 1), (56, 1), (66, 2)] }, { coefficient := -2, powers := [(6, 1), (15, 1), (22, 1), (34, 1), (37, 1), (56, 1), (57, 1), (66, 2)] }, { coefficient := 1, powers := [(6, 1), (20, 1)] }],
  [{ coefficient := 1, powers := [(31, 1), (37, 1), (43, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (31, 1), (56, 1)] }, { coefficient := -1, powers := [(3, 1), (34, 1), (50, 1)] }, { coefficient := -1, powers := [(13, 1), (31, 1), (37, 1), (56, 1), (66, 1)] }, { coefficient := -1, powers := [(13, 1), (34, 1), (37, 1), (50, 1), (66, 1)] }]
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
    (values : Fin 72 → R) :
    ¬ ∀ index : Fin 30,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component37.SelectedLeafB5_3_6_4_2_6.selectedHasNoCommonZero

end Krenn.Component37.SelectedLeafB5_3_6_4_2_6
