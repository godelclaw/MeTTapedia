import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component24.SelectedLeafB7_3_3

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "f425bdcccdc9a683215463a9e0dc580395ed7e3752c0e92c44af23b6c52650b5"
def certificateSHA256 : String := "42aa519d0a41b7f38221672bc1a17dd5760f37cf64b5951154d41e61e4e6a0cf"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 30 → Fin 673 := ![
  3,
  5,
  8,
  14,
  17,
  18,
  19,
  149,
  151,
  266,
  302,
  305,
  306,
  326,
  443,
  503,
  584,
  590,
  596,
  606,
  607,
  612,
  614,
  661,
  665,
  666,
  667,
  669,
  670,
  672
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 30 → SparsePoly (Fin 69) := ![
  [{ coefficient := 1, powers := [(9, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(15, 1), (21, 1)] }, { coefficient := 1, powers := [(21, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(15, 1), (51, 1)] }, { coefficient := 1, powers := [(51, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(15, 1), (21, 1), (54, 1)] }, { coefficient := 1, powers := [(15, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (44, 1)] }, { coefficient := 1, powers := [(11, 1), (22, 1), (56, 1)] }, { coefficient := 1, powers := [(11, 1), (27, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (44, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (56, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (59, 1)] }, { coefficient := 1, powers := [(9, 1), (56, 1)] }, { coefficient := 1, powers := [(15, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (41, 1), (58, 1)] }, { coefficient := 1, powers := [(3, 1), (32, 1), (58, 1)] }, { coefficient := 1, powers := [(9, 1), (20, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (54, 1)] }, { coefficient := 1, powers := [(20, 1), (51, 1), (57, 1)] }, { coefficient := 1, powers := [(20, 1), (54, 1)] }, { coefficient := 1, powers := [(51, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1)] }, { coefficient := 1, powers := [(6, 1), (60, 1)] }, { coefficient := 1, powers := [(26, 1), (42, 1)] }, { coefficient := 1, powers := [(26, 1), (46, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1), (56, 1)] }, { coefficient := 1, powers := [(6, 1), (35, 1), (43, 1)] }, { coefficient := 1, powers := [(15, 1), (21, 1), (51, 1)] }, { coefficient := 1, powers := [(15, 1), (26, 1), (43, 1)] }, { coefficient := 1, powers := [(21, 1), (51, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (41, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (44, 1), (50, 1)] }, { coefficient := 1, powers := [(13, 1), (24, 1), (56, 1)] }, { coefficient := 1, powers := [(13, 1), (29, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1)] }, { coefficient := 1, powers := [(3, 1), (35, 1)] }, { coefficient := 1, powers := [(15, 1), (20, 1)] }, { coefficient := 1, powers := [(20, 1), (56, 1)] }, { coefficient := 1, powers := [(26, 1), (44, 1)] }, { coefficient := 1, powers := [(35, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (50, 1)] }, { coefficient := 1, powers := [(6, 1), (32, 1)] }, { coefficient := 1, powers := [(9, 1), (26, 1)] }, { coefficient := 1, powers := [(20, 1), (50, 1)] }, { coefficient := 1, powers := [(26, 1), (41, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (38, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1)] }, { coefficient := 1, powers := [(3, 1), (26, 1), (60, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1), (60, 1)] }, { coefficient := 1, powers := [(20, 1)] }, { coefficient := 1, powers := [(26, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (48, 1), (54, 1)] }, { coefficient := 1, powers := [(21, 1), (51, 1), (57, 1)] }, { coefficient := 1, powers := [(21, 1), (54, 1)] }, { coefficient := 1, powers := [(43, 1)] }, { coefficient := 1, powers := [(48, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (38, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (41, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (44, 1), (50, 1)] }, { coefficient := 1, powers := [(3, 1), (26, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (32, 1), (56, 1)] }, { coefficient := 1, powers := [(3, 1), (35, 1), (50, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (32, 1), (44, 1)] }, { coefficient := 1, powers := [(6, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(9, 1), (20, 1), (56, 1)] }, { coefficient := 1, powers := [(9, 1), (26, 1), (44, 1)] }, { coefficient := 1, powers := [(9, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(15, 1), (20, 1), (50, 1)] }, { coefficient := 1, powers := [(15, 1), (26, 1), (41, 1)] }, { coefficient := 1, powers := [(15, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (64, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(41, 1)] }],
  [{ coefficient := 1, powers := [(43, 1), (66, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(56, 1)] }],
  [{ coefficient := 1, powers := [(58, 1), (68, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 30 → SparsePoly (Fin 69) := ![
  [{ coefficient := 1, powers := [(15, 1), (26, 1), (38, 1), (60, 1), (68, 1)] }, { coefficient := -1, powers := [(26, 1), (35, 1), (38, 1), (57, 1), (68, 1)] }, { coefficient := -1, powers := [(26, 1), (38, 1), (44, 1), (60, 1), (68, 1)] }, { coefficient := -1, powers := [(35, 1), (38, 2), (60, 1), (68, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (27, 1), (32, 1), (38, 1), (46, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (27, 1), (32, 1), (38, 1), (57, 1), (63, 1)] }, { coefficient := -1, powers := [(26, 1), (27, 1), (32, 1), (38, 1), (42, 1), (63, 1)] }, { coefficient := -1, powers := [(26, 1), (27, 1), (32, 1), (38, 1), (46, 1), (63, 1)] }, { coefficient := -1, powers := [(26, 1), (27, 1), (32, 1), (38, 1), (57, 1), (63, 1)] }, { coefficient := -1, powers := [(26, 1), (27, 1), (38, 1), (50, 1), (60, 1), (63, 1)] }, { coefficient := -1, powers := [(27, 1), (32, 1), (38, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (29, 1), (38, 1), (60, 1), (64, 1)] }, { coefficient := 1, powers := [(26, 1), (29, 1), (38, 1), (60, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (29, 1), (38, 1), (50, 1), (60, 1), (64, 1)] }, { coefficient := -1, powers := [(26, 1), (29, 1), (38, 1), (50, 1), (60, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (24, 1), (38, 1), (59, 1), (64, 1), (68, 1)] }, { coefficient := -1, powers := [(0, 1), (29, 1), (38, 1), (59, 1), (64, 1), (68, 1)] }, { coefficient := -1, powers := [(24, 1), (26, 1), (38, 1), (59, 1), (64, 1), (68, 1)] }, { coefficient := -1, powers := [(24, 1), (35, 1), (38, 1), (50, 1), (64, 1), (68, 1)] }, { coefficient := -1, powers := [(24, 1), (64, 1), (68, 1)] }, { coefficient := -1, powers := [(26, 1), (29, 1), (38, 1), (59, 1), (64, 1), (68, 1)] }, { coefficient := -1, powers := [(29, 1), (35, 1), (38, 1), (50, 1), (64, 1), (68, 1)] }, { coefficient := -1, powers := [(29, 1), (64, 1), (68, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (38, 1), (46, 1), (59, 1), (68, 1)] }, { coefficient := -1, powers := [(9, 1), (35, 1), (38, 1), (57, 1), (68, 1)] }, { coefficient := 1, powers := [(15, 1), (32, 1), (38, 1), (57, 1), (68, 1)] }, { coefficient := 2, powers := [(15, 1), (38, 1), (50, 1), (60, 1), (68, 1)] }, { coefficient := -1, powers := [(26, 1), (38, 1), (42, 1), (59, 1), (68, 1)] }, { coefficient := -1, powers := [(26, 1), (38, 1), (46, 1), (59, 1), (68, 1)] }, { coefficient := -1, powers := [(35, 1), (38, 1), (48, 1), (50, 1), (51, 1), (57, 1), (66, 1), (68, 1)] }, { coefficient := -1, powers := [(35, 1), (38, 1), (48, 1), (50, 1), (54, 1), (66, 1), (68, 1)] }, { coefficient := -1, powers := [(35, 1), (38, 1), (50, 1), (57, 1), (68, 1)] }],
  [{ coefficient := 1, powers := [(35, 1), (38, 1), (50, 1), (51, 1), (57, 1), (66, 1), (68, 1)] }, { coefficient := 1, powers := [(35, 1), (38, 1), (50, 1), (54, 1), (66, 1), (68, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (32, 1), (38, 1), (46, 1), (54, 1), (66, 1)] }, { coefficient := -1, powers := [(0, 1), (38, 1), (50, 1), (54, 1), (60, 1), (66, 1)] }, { coefficient := 1, powers := [(26, 1), (32, 1), (38, 1), (42, 1), (54, 1), (66, 1)] }, { coefficient := 1, powers := [(26, 1), (32, 1), (38, 1), (46, 1), (54, 1), (66, 1)] }, { coefficient := -1, powers := [(26, 1), (32, 1), (38, 1), (54, 1), (57, 1), (66, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1), (54, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (32, 1), (38, 1), (57, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (32, 1), (38, 1), (46, 1), (66, 1)] }, { coefficient := 1, powers := [(0, 1), (38, 1), (50, 1), (60, 1), (66, 1)] }, { coefficient := -1, powers := [(26, 1), (32, 1), (38, 1), (42, 1), (66, 1)] }, { coefficient := -1, powers := [(26, 1), (32, 1), (38, 1), (46, 1), (66, 1)] }, { coefficient := 1, powers := [(26, 1), (32, 1), (38, 1), (57, 1), (66, 1)] }, { coefficient := -1, powers := [(32, 1), (38, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (32, 1), (38, 1), (46, 1), (63, 1)] }, { coefficient := 1, powers := [(0, 1), (32, 1), (38, 1), (57, 1), (63, 1)] }, { coefficient := 1, powers := [(26, 1), (32, 1), (38, 1), (42, 1), (63, 1)] }, { coefficient := 1, powers := [(26, 1), (32, 1), (38, 1), (46, 1), (63, 1)] }, { coefficient := 1, powers := [(26, 1), (32, 1), (38, 1), (57, 1), (63, 1)] }, { coefficient := 1, powers := [(26, 1), (38, 1), (50, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (38, 1), (50, 1), (60, 1), (64, 1)] }, { coefficient := 1, powers := [(26, 1), (38, 1), (50, 1), (60, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(20, 1), (38, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(35, 1), (38, 1), (57, 1), (68, 1)] }],
  [{ coefficient := 1, powers := [(35, 1), (38, 1), (48, 1), (50, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (38, 1), (59, 1), (64, 1)] }, { coefficient := 1, powers := [(26, 1), (38, 1), (59, 1), (64, 1)] }, { coefficient := 1, powers := [(35, 1), (38, 1), (50, 1), (64, 1)] }, { coefficient := 1, powers := [(64, 1)] }],
  [{ coefficient := 1, powers := [(15, 1), (32, 1), (38, 1)] }, { coefficient := 1, powers := [(20, 1), (38, 1), (59, 1)] }, { coefficient := -1, powers := [(32, 1), (38, 1), (44, 1)] }],
  [{ coefficient := -1, powers := [(32, 1), (38, 1), (57, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (38, 1), (60, 1), (64, 1)] }, { coefficient := -1, powers := [(26, 1), (38, 1), (60, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(32, 1), (38, 1), (57, 1)] }, { coefficient := -1, powers := [(38, 1), (50, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(15, 1), (38, 1), (60, 1)] }, { coefficient := 1, powers := [(35, 1), (38, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [(38, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(35, 1), (38, 1), (50, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(38, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (32, 1), (38, 1), (44, 1), (46, 1)] }, { coefficient := -1, powers := [(0, 1), (32, 1), (38, 1), (44, 1), (57, 1)] }, { coefficient := -1, powers := [(26, 1), (32, 1), (38, 1), (42, 1), (44, 1)] }, { coefficient := -1, powers := [(26, 1), (32, 1), (38, 1), (44, 1), (46, 1)] }, { coefficient := -1, powers := [(26, 1), (32, 1), (38, 1), (44, 1), (57, 1)] }, { coefficient := -1, powers := [(26, 1), (38, 1), (44, 1), (50, 1), (60, 1)] }, { coefficient := -1, powers := [(32, 1), (38, 1), (44, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (38, 1), (59, 1)] }, { coefficient := -1, powers := [(26, 1), (38, 1), (59, 1)] }, { coefficient := -1, powers := [(35, 1), (38, 2), (50, 1), (60, 1)] }, { coefficient := -1, powers := [(35, 1), (38, 1), (50, 1)] }, { coefficient := -1, powers := [(38, 1), (60, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(0, 1), (35, 1), (38, 1), (57, 1), (58, 1), (68, 1)] }, { coefficient := -1, powers := [(6, 1), (35, 1), (38, 1), (60, 1)] }, { coefficient := -1, powers := [(26, 1), (35, 1), (38, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (15, 1), (32, 1), (38, 1), (46, 1)] }, { coefficient := -1, powers := [(0, 1), (15, 1), (38, 1), (50, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (35, 1), (38, 1), (50, 1), (57, 1)] }, { coefficient := 1, powers := [(6, 1), (32, 1), (35, 1), (38, 1), (57, 1)] }, { coefficient := 1, powers := [(15, 1), (26, 1), (32, 1), (38, 1), (42, 1)] }, { coefficient := 1, powers := [(15, 1), (26, 1), (32, 1), (38, 1), (46, 1)] }, { coefficient := 1, powers := [(15, 1), (32, 1), (38, 1)] }, { coefficient := 1, powers := [(35, 1), (38, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (2, 1), (38, 1), (41, 1), (60, 1), (64, 1)] }, { coefficient := -1, powers := [(0, 1), (11, 1), (22, 1), (32, 1), (38, 1), (46, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (11, 1), (22, 1), (32, 1), (38, 1), (57, 1), (63, 1)] }, { coefficient := 1, powers := [(0, 1), (13, 1), (24, 1), (38, 1), (60, 1), (64, 1)] }, { coefficient := -1, powers := [(0, 1), (18, 1), (24, 1), (38, 1), (50, 1), (60, 1), (64, 1)] }, { coefficient := -1, powers := [(0, 1), (21, 1), (32, 1), (38, 1), (46, 1), (54, 1), (66, 1)] }, { coefficient := 1, powers := [(0, 1), (21, 1), (38, 1), (50, 1), (54, 1), (60, 1), (66, 1)] }, { coefficient := 1, powers := [(0, 1), (32, 1), (38, 1), (43, 1), (57, 1), (66, 1)] }, { coefficient := -1, powers := [(0, 1), (38, 1), (41, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (26, 1), (38, 1), (41, 1), (60, 1), (64, 1)] }, { coefficient := -1, powers := [(3, 1), (32, 1), (38, 1), (60, 1)] }, { coefficient := -1, powers := [(11, 1), (22, 1), (26, 1), (32, 1), (38, 1), (42, 1), (63, 1)] }, { coefficient := -1, powers := [(11, 1), (22, 1), (26, 1), (32, 1), (38, 1), (46, 1), (63, 1)] }, { coefficient := -1, powers := [(11, 1), (22, 1), (26, 1), (32, 1), (38, 1), (57, 1), (63, 1)] }, { coefficient := -1, powers := [(11, 1), (22, 1), (26, 1), (38, 1), (50, 1), (60, 1), (63, 1)] }, { coefficient := -1, powers := [(11, 1), (22, 1), (32, 1), (38, 1), (63, 1)] }, { coefficient := 1, powers := [(13, 1), (24, 1), (26, 1), (38, 1), (60, 1), (64, 1)] }, { coefficient := -1, powers := [(18, 1), (24, 1), (26, 1), (38, 1), (50, 1), (60, 1), (64, 1)] }, { coefficient := 1, powers := [(20, 1), (32, 1), (38, 1), (57, 1)] }, { coefficient := 1, powers := [(20, 1), (38, 1), (50, 1), (60, 1)] }, { coefficient := -1, powers := [(21, 1), (26, 1), (32, 1), (38, 1), (42, 1), (54, 1), (66, 1)] }, { coefficient := -1, powers := [(21, 1), (26, 1), (32, 1), (38, 1), (46, 1), (54, 1), (66, 1)] }, { coefficient := 1, powers := [(21, 1), (26, 1), (32, 1), (38, 1), (54, 1), (57, 1), (66, 1)] }, { coefficient := -1, powers := [(21, 1), (32, 1), (38, 1), (54, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (18, 1), (24, 1), (38, 1), (59, 1), (64, 1)] }, { coefficient := 1, powers := [(0, 1), (18, 1), (29, 1), (38, 1), (59, 1), (64, 1)] }, { coefficient := 1, powers := [(0, 1), (20, 1), (38, 1), (46, 1), (59, 1)] }, { coefficient := -1, powers := [(3, 1), (32, 1), (35, 1), (38, 1), (57, 1)] }, { coefficient := -1, powers := [(9, 1), (15, 1), (26, 1), (38, 1), (60, 1)] }, { coefficient := 1, powers := [(9, 1), (26, 1), (35, 1), (38, 1), (57, 1)] }, { coefficient := 1, powers := [(9, 1), (26, 1), (38, 1), (44, 1), (60, 1)] }, { coefficient := 1, powers := [(9, 1), (35, 1), (38, 2), (60, 1)] }, { coefficient := -1, powers := [(15, 1), (20, 1), (32, 1), (38, 1), (57, 1)] }, { coefficient := -2, powers := [(15, 1), (20, 1), (38, 1), (50, 1), (60, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (26, 1), (38, 1), (59, 1), (64, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (35, 1), (38, 1), (50, 1), (64, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (64, 1)] }, { coefficient := 1, powers := [(18, 1), (26, 1), (29, 1), (38, 1), (59, 1), (64, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (35, 1), (38, 1), (50, 1), (64, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (64, 1)] }, { coefficient := 1, powers := [(20, 1), (26, 1), (38, 1), (42, 1), (59, 1)] }, { coefficient := 1, powers := [(20, 1), (26, 1), (38, 1), (46, 1), (59, 1)] }, { coefficient := 1, powers := [(20, 1), (35, 1), (38, 1), (48, 1), (50, 1), (51, 1), (57, 1), (66, 1)] }, { coefficient := 1, powers := [(20, 1), (35, 1), (38, 1), (48, 1), (50, 1), (54, 1), (66, 1)] }, { coefficient := 1, powers := [(20, 1), (35, 1), (38, 1), (50, 1), (57, 1)] }, { coefficient := -1, powers := [(21, 1), (35, 1), (38, 1), (50, 1), (51, 1), (57, 1), (66, 1)] }, { coefficient := -1, powers := [(21, 1), (35, 1), (38, 1), (50, 1), (54, 1), (66, 1)] }]
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
    ¬ ∀ index : Fin 30,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component24.SelectedLeafB7_3_3.selectedHasNoCommonZero

end Krenn.Component24.SelectedLeafB7_3_3
