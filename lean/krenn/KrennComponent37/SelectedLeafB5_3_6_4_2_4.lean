import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component37.SelectedLeafB5_3_6_4_2_4

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "b2df332c99521767ca49fdc0ad99ed6ca55da08c223bb2a9359a4c8ffff4cfbd"
def certificateSHA256 : String := "c4833b8835d750ad2aa4694dc224d3703799fc6426d90ccec2f9c7e835f23eb3"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 27 → Fin 676 := ![
  17,
  21,
  154,
  298,
  299,
  300,
  363,
  373,
  484,
  583,
  590,
  602,
  603,
  604,
  605,
  655,
  656,
  659,
  660,
  661,
  663,
  664,
  665,
  667,
  668,
  670,
  674
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 27 → SparsePoly (Fin 71) := ![
  [{ coefficient := 1, powers := [(18, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (25, 1)] }, { coefficient := 1, powers := [(15, 1), (20, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (46, 1)] }, { coefficient := 1, powers := [(4, 1), (35, 1)] }, { coefficient := 1, powers := [(15, 1), (22, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (52, 1)] }, { coefficient := 1, powers := [(7, 1), (32, 1)] }, { coefficient := 1, powers := [(10, 1), (27, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (50, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (50, 1)] }, { coefficient := 1, powers := [(18, 1), (28, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (22, 1), (59, 1)] }, { coefficient := 1, powers := [(9, 1), (22, 1), (56, 1)] }, { coefficient := 1, powers := [(13, 1), (22, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (22, 1), (57, 1)] }, { coefficient := 1, powers := [(9, 1), (27, 1), (46, 1)] }, { coefficient := 1, powers := [(9, 1), (35, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (37, 1), (60, 1)] }, { coefficient := 1, powers := [(1, 1)] }, { coefficient := 1, powers := [(10, 1), (35, 1), (37, 1)] }, { coefficient := 1, powers := [(15, 1), (32, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (31, 1), (57, 1)] }, { coefficient := 1, powers := [(9, 1), (20, 1), (57, 1)] }, { coefficient := 1, powers := [(9, 1)] }, { coefficient := 1, powers := [(40, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (42, 1), (57, 1)] }, { coefficient := 1, powers := [(1, 1), (48, 1), (53, 1)] }, { coefficient := 1, powers := [(7, 1), (35, 1), (42, 1)] }, { coefficient := 1, powers := [(11, 1), (27, 1), (48, 1)] }, { coefficient := 1, powers := [(15, 1), (27, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1)] }, { coefficient := 1, powers := [(3, 1), (34, 1)] }, { coefficient := 1, powers := [(13, 1), (20, 1)] }, { coefficient := 1, powers := [(20, 1), (56, 1)] }, { coefficient := 1, powers := [(25, 1), (43, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (50, 1)] }, { coefficient := 1, powers := [(6, 1), (31, 1)] }, { coefficient := 1, powers := [(9, 1), (25, 1)] }, { coefficient := 1, powers := [(20, 1), (50, 1)] }, { coefficient := 1, powers := [(25, 1), (40, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (60, 1)] }, { coefficient := 1, powers := [(10, 1), (46, 1)] }, { coefficient := 1, powers := [(10, 1), (57, 1)] }, { coefficient := 1, powers := [(15, 1), (41, 1)] }, { coefficient := 1, powers := [(15, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (52, 1)] }, { coefficient := 1, powers := [(22, 1), (57, 1)] }, { coefficient := 1, powers := [(27, 1), (41, 1)] }, { coefficient := 1, powers := [(27, 1), (46, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1)] }, { coefficient := 1, powers := [(35, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (37, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (40, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (43, 1), (50, 1)] }, { coefficient := 1, powers := [(3, 1), (25, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (31, 1), (56, 1)] }, { coefficient := 1, powers := [(3, 1), (34, 1), (50, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (31, 1), (43, 1)] }, { coefficient := 1, powers := [(6, 1), (34, 1), (40, 1)] }, { coefficient := 1, powers := [(9, 1), (20, 1), (56, 1)] }, { coefficient := 1, powers := [(9, 1), (25, 1), (43, 1)] }, { coefficient := 1, powers := [(9, 1), (34, 1), (37, 1)] }, { coefficient := 1, powers := [(13, 1), (20, 1), (50, 1)] }, { coefficient := 1, powers := [(13, 1), (25, 1), (40, 1)] }, { coefficient := 1, powers := [(13, 1), (31, 1), (37, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1), (38, 1), (60, 1)] }, { coefficient := 1, powers := [(1, 1), (41, 1), (57, 1)] }, { coefficient := 1, powers := [(1, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(4, 1), (27, 1), (60, 1)] }, { coefficient := 1, powers := [(4, 1), (32, 1), (57, 1)] }, { coefficient := 1, powers := [(4, 1), (35, 1), (52, 1)] }, { coefficient := 1, powers := [(7, 1), (22, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (32, 1), (46, 1)] }, { coefficient := 1, powers := [(7, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(10, 1), (22, 1), (57, 1)] }, { coefficient := 1, powers := [(10, 1), (27, 1), (46, 1)] }, { coefficient := 1, powers := [(10, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(15, 1), (22, 1), (52, 1)] }, { coefficient := 1, powers := [(15, 1), (27, 1), (41, 1)] }, { coefficient := 1, powers := [(15, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(40, 1)] }],
  [{ coefficient := 1, powers := [(42, 1), (65, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(56, 1), (66, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(57, 1), (67, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(25, 1), (68, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(27, 1)] }],
  [{ coefficient := 1, powers := [(59, 1)] }],
  [{ coefficient := 1, powers := [(4, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 27 → SparsePoly (Fin 71) := ![
  [{ coefficient := 1, powers := [(0, 1), (23, 1), (43, 1), (63, 1)] }, { coefficient := 1, powers := [(20, 1), (23, 1), (43, 1), (63, 1)] }, { coefficient := 1, powers := [(20, 1), (23, 1), (56, 1), (63, 1)] }, { coefficient := 1, powers := [(23, 1), (25, 1), (43, 1), (63, 1)] }, { coefficient := 1, powers := [(23, 1), (34, 1), (37, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(10, 1), (13, 1), (46, 1), (56, 1), (66, 1), (67, 1)] }, { coefficient := -1, powers := [(10, 1), (13, 1), (56, 1), (57, 1), (66, 1), (67, 1)] }],
  [{ coefficient := -1, powers := [(9, 1), (22, 1), (34, 1), (37, 1), (46, 1), (68, 1)] }, { coefficient := -1, powers := [(13, 1), (22, 1), (31, 1), (37, 1), (46, 1), (68, 1)] }, { coefficient := 1, powers := [(22, 1), (31, 1), (37, 1), (43, 1), (46, 1), (68, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (20, 1), (34, 1), (37, 1), (46, 1), (68, 1)] }, { coefficient := -1, powers := [(9, 1), (34, 1), (37, 1), (41, 1)] }, { coefficient := 1, powers := [(9, 1), (41, 1), (56, 1), (67, 1)] }, { coefficient := 1, powers := [(9, 1), (52, 1), (56, 1), (67, 1)] }, { coefficient := 1, powers := [(13, 1), (20, 1), (31, 1), (37, 1), (46, 1), (68, 1)] }, { coefficient := -1, powers := [(13, 1), (31, 1), (37, 1), (41, 1)] }, { coefficient := -1, powers := [(20, 1), (31, 1), (37, 1), (43, 1), (46, 1), (68, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1), (41, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (34, 1), (37, 1), (46, 1)] }, { coefficient := -1, powers := [(9, 1), (46, 1), (56, 1), (67, 1)] }, { coefficient := 1, powers := [(13, 1), (31, 1), (37, 1), (46, 1)] }, { coefficient := -1, powers := [(31, 1), (37, 1), (43, 1), (46, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (43, 1), (63, 1)] }, { coefficient := -1, powers := [(20, 1), (43, 1), (63, 1)] }, { coefficient := -1, powers := [(20, 1), (56, 1), (63, 1)] }, { coefficient := -1, powers := [(25, 1), (43, 1), (63, 1)] }, { coefficient := -1, powers := [(34, 1), (37, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (46, 1), (56, 1), (66, 1), (67, 1)] }, { coefficient := 1, powers := [(10, 1), (56, 1), (57, 1), (66, 1), (67, 1)] }],
  [{ coefficient := -1, powers := [(10, 1), (56, 1), (67, 1)] }, { coefficient := 1, powers := [(15, 1), (56, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (34, 1), (38, 1)] }, { coefficient := 1, powers := [(13, 1), (31, 1), (38, 1)] }, { coefficient := -1, powers := [(31, 1), (38, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(56, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (34, 1), (37, 1), (41, 1), (65, 1)] }, { coefficient := -1, powers := [(9, 1), (41, 1), (56, 1), (65, 1), (67, 1)] }, { coefficient := 1, powers := [(13, 1), (31, 1), (37, 1), (41, 1), (65, 1)] }, { coefficient := -1, powers := [(31, 1), (37, 1), (41, 1), (43, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(50, 1)] }],
  [{ coefficient := 1, powers := [(43, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (22, 1), (34, 1), (37, 1)] }, { coefficient := -1, powers := [(9, 1), (22, 1), (56, 1), (67, 1)] }, { coefficient := 1, powers := [(13, 1), (22, 1), (31, 1), (37, 1)] }, { coefficient := -1, powers := [(22, 1), (31, 1), (37, 1), (43, 1)] }],
  [{ coefficient := -1, powers := [(9, 1), (15, 1), (56, 1), (67, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(9, 1), (34, 1), (37, 1)] }, { coefficient := 1, powers := [(9, 1), (56, 1), (67, 1)] }, { coefficient := -1, powers := [(13, 1), (31, 1), (37, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1), (43, 1)] }],
  [{ coefficient := -1, powers := [(9, 1), (20, 1), (34, 1), (37, 1), (46, 2), (68, 1)] }, { coefficient := -1, powers := [(9, 1), (34, 1), (37, 1), (41, 1), (42, 1), (57, 1), (65, 1)] }, { coefficient := 1, powers := [(9, 1), (34, 1), (37, 1), (41, 1), (46, 1)] }, { coefficient := -1, powers := [(9, 1), (34, 1), (37, 1), (41, 1), (48, 1), (53, 1), (65, 1)] }, { coefficient := 1, powers := [(9, 1), (34, 1), (37, 1), (41, 1), (57, 1)] }, { coefficient := -1, powers := [(9, 1), (34, 1), (38, 1)] }, { coefficient := -1, powers := [(9, 1), (38, 1), (56, 1), (60, 1), (67, 1)] }, { coefficient := 1, powers := [(9, 1), (41, 1), (42, 1), (56, 1), (57, 1), (65, 1), (67, 1)] }, { coefficient := -1, powers := [(9, 1), (41, 1), (46, 1), (56, 1), (67, 1)] }, { coefficient := 1, powers := [(9, 1), (41, 1), (48, 1), (53, 1), (56, 1), (65, 1), (67, 1)] }, { coefficient := -1, powers := [(9, 1), (41, 1), (56, 1), (57, 1), (67, 1)] }, { coefficient := -1, powers := [(9, 1), (46, 1), (52, 1), (56, 1), (67, 1)] }, { coefficient := -1, powers := [(13, 1), (20, 1), (31, 1), (37, 1), (46, 2), (68, 1)] }, { coefficient := -1, powers := [(13, 1), (31, 1), (37, 1), (41, 1), (42, 1), (57, 1), (65, 1)] }, { coefficient := 1, powers := [(13, 1), (31, 1), (37, 1), (41, 1), (46, 1)] }, { coefficient := -1, powers := [(13, 1), (31, 1), (37, 1), (41, 1), (48, 1), (53, 1), (65, 1)] }, { coefficient := 1, powers := [(13, 1), (31, 1), (37, 1), (41, 1), (57, 1)] }, { coefficient := -1, powers := [(13, 1), (31, 1), (38, 1)] }, { coefficient := 1, powers := [(20, 1), (31, 1), (37, 1), (43, 1), (46, 2), (68, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1), (41, 1), (42, 1), (43, 1), (57, 1), (65, 1)] }, { coefficient := -1, powers := [(31, 1), (37, 1), (41, 1), (43, 1), (46, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1), (41, 1), (43, 1), (48, 1), (53, 1), (65, 1)] }, { coefficient := -1, powers := [(31, 1), (37, 1), (41, 1), (43, 1), (57, 1)] }, { coefficient := 1, powers := [(31, 1), (38, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1), (50, 1)] }, { coefficient := 1, powers := [(20, 1), (43, 1), (50, 1)] }, { coefficient := 1, powers := [(20, 1), (50, 1), (56, 1)] }, { coefficient := 1, powers := [(25, 1), (43, 1), (50, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (18, 1), (28, 1), (43, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (56, 1), (57, 1), (67, 1)] }, { coefficient := 1, powers := [(0, 1), (56, 1)] }, { coefficient := 1, powers := [(6, 1), (34, 1)] }, { coefficient := 1, powers := [(13, 1), (25, 1)] }, { coefficient := 1, powers := [(18, 1), (20, 1), (28, 1), (43, 1), (63, 1)] }, { coefficient := 1, powers := [(18, 1), (20, 1), (28, 1), (56, 1), (63, 1)] }, { coefficient := 1, powers := [(18, 1), (25, 1), (28, 1), (43, 1), (63, 1)] }, { coefficient := 1, powers := [(18, 1), (28, 1), (34, 1), (37, 1), (63, 1)] }, { coefficient := -1, powers := [(25, 1), (43, 1)] }, { coefficient := -1, powers := [(56, 1), (67, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (9, 1), (34, 1), (35, 1), (37, 1), (41, 1)] }, { coefficient := 1, powers := [(7, 1), (9, 1), (35, 1), (41, 1), (56, 1), (67, 1)] }, { coefficient := -1, powers := [(7, 1), (13, 1), (31, 1), (35, 1), (37, 1), (41, 1)] }, { coefficient := 1, powers := [(7, 1), (31, 1), (35, 1), (37, 1), (41, 1), (43, 1)] }],
  [{ coefficient := -1, powers := [(9, 1), (10, 1), (22, 1), (46, 1), (56, 1), (67, 1)] }, { coefficient := -1, powers := [(9, 1), (10, 1), (22, 1), (56, 1), (57, 1), (67, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (31, 1), (56, 1)] }, { coefficient := -1, powers := [(9, 1), (20, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (10, 1), (22, 1), (34, 1), (37, 1), (46, 1)] }, { coefficient := 1, powers := [(10, 1), (13, 1), (22, 1), (31, 1), (37, 1), (46, 1)] }, { coefficient := -1, powers := [(10, 1), (22, 1), (31, 1), (37, 1), (43, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (9, 1), (34, 1), (37, 1), (60, 1)] }, { coefficient := -1, powers := [(4, 1), (9, 1), (56, 1), (60, 1), (67, 1)] }, { coefficient := 1, powers := [(4, 1), (13, 1), (31, 1), (37, 1), (60, 1)] }, { coefficient := -1, powers := [(4, 1), (31, 1), (37, 1), (43, 1), (60, 1)] }, { coefficient := 1, powers := [(9, 1), (10, 1), (46, 1), (56, 1), (67, 1)] }, { coefficient := -1, powers := [(9, 1), (11, 1), (34, 1), (37, 1), (41, 1), (48, 1), (65, 1)] }, { coefficient := 1, powers := [(9, 1), (11, 1), (41, 1), (48, 1), (56, 1), (65, 1), (67, 1)] }, { coefficient := -1, powers := [(9, 1), (15, 1), (34, 1), (37, 1), (41, 1), (42, 1), (65, 1)] }, { coefficient := 1, powers := [(9, 1), (15, 1), (34, 1), (37, 1), (41, 1)] }, { coefficient := 1, powers := [(9, 1), (15, 1), (41, 1), (42, 1), (56, 1), (65, 1), (67, 1)] }, { coefficient := -1, powers := [(11, 1), (13, 1), (31, 1), (37, 1), (41, 1), (48, 1), (65, 1)] }, { coefficient := 1, powers := [(11, 1), (31, 1), (37, 1), (41, 1), (43, 1), (48, 1), (65, 1)] }, { coefficient := -1, powers := [(13, 1), (15, 1), (31, 1), (37, 1), (41, 1), (42, 1), (65, 1)] }, { coefficient := 1, powers := [(13, 1), (15, 1), (31, 1), (37, 1), (41, 1)] }, { coefficient := 1, powers := [(15, 1), (31, 1), (37, 1), (41, 1), (42, 1), (43, 1), (65, 1)] }, { coefficient := -1, powers := [(15, 1), (31, 1), (37, 1), (41, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (37, 1)] }, { coefficient := 1, powers := [(3, 1), (25, 1)] }, { coefficient := -1, powers := [(6, 1), (10, 1), (22, 1), (46, 1), (56, 1), (66, 1), (67, 1)] }, { coefficient := -1, powers := [(6, 1), (10, 1), (22, 1), (56, 1), (57, 1), (66, 1), (67, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1)] }],
  [{ coefficient := -1, powers := [(9, 1), (20, 1), (34, 1), (35, 1), (37, 1), (46, 1), (68, 1)] }, { coefficient := -1, powers := [(9, 1), (22, 1), (34, 1), (37, 1), (60, 1)] }, { coefficient := 1, powers := [(9, 1), (22, 1), (56, 1), (60, 1), (67, 1)] }, { coefficient := 1, powers := [(9, 1), (32, 1), (34, 1), (37, 1), (57, 1)] }, { coefficient := -1, powers := [(9, 1), (32, 1), (56, 1), (57, 1), (67, 1)] }, { coefficient := 1, powers := [(9, 1), (34, 1), (35, 1), (37, 1), (41, 1)] }, { coefficient := 1, powers := [(9, 1), (34, 1), (35, 1), (37, 1), (52, 1)] }, { coefficient := -1, powers := [(9, 1), (35, 1), (41, 1), (56, 1), (67, 1)] }, { coefficient := -2, powers := [(9, 1), (35, 1), (52, 1), (56, 1), (67, 1)] }, { coefficient := -1, powers := [(13, 1), (20, 1), (31, 1), (35, 1), (37, 1), (46, 1), (68, 1)] }, { coefficient := -1, powers := [(13, 1), (22, 1), (31, 1), (37, 1), (60, 1)] }, { coefficient := 1, powers := [(13, 1), (31, 1), (32, 1), (37, 1), (57, 1)] }, { coefficient := 1, powers := [(13, 1), (31, 1), (35, 1), (37, 1), (41, 1)] }, { coefficient := 1, powers := [(13, 1), (31, 1), (35, 1), (37, 1), (52, 1)] }, { coefficient := 1, powers := [(20, 1), (31, 1), (35, 1), (37, 1), (43, 1), (46, 1), (68, 1)] }, { coefficient := 1, powers := [(22, 1), (31, 1), (37, 1), (43, 1), (60, 1)] }, { coefficient := -1, powers := [(31, 1), (32, 1), (37, 1), (43, 1), (57, 1)] }, { coefficient := -1, powers := [(31, 1), (35, 1), (37, 1), (41, 1), (43, 1)] }, { coefficient := -1, powers := [(31, 1), (35, 1), (37, 1), (43, 1), (52, 1)] }]
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
    (values : Fin 71 → R) :
    ¬ ∀ index : Fin 27,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component37.SelectedLeafB5_3_6_4_2_4.selectedHasNoCommonZero

end Krenn.Component37.SelectedLeafB5_3_6_4_2_4
