import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component37.SelectedLeafB6_3_1

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "7ec2237d885528af6058bf38b01409c312bcc02d27f9384e72ce0e446af6f3fd"
def certificateSHA256 : String := "33352bdadfe51634414521040420df94b6b712838f054e993b1041be11c8ae87"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 35 → Fin 667 := ![
  0,
  1,
  3,
  4,
  23,
  27,
  182,
  185,
  283,
  295,
  296,
  297,
  298,
  299,
  313,
  427,
  460,
  476,
  480,
  482,
  484,
  485,
  581,
  604,
  605,
  606,
  607,
  608,
  646,
  656,
  658,
  659,
  663,
  665,
  666
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 35 → SparsePoly (Fin 67) := ![
  [{ coefficient := 1, powers := [(1, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (42, 1)] }, { coefficient := 1, powers := [(27, 1), (48, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(32, 1), (39, 1)] }, { coefficient := 1, powers := [(35, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (44, 1), (54, 1)] }, { coefficient := 1, powers := [(22, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (49, 1)] }, { coefficient := 1, powers := [(21, 1), (44, 1)] }, { coefficient := 1, powers := [(25, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (51, 1)] }, { coefficient := 1, powers := [(20, 1), (51, 1)] }, { coefficient := 1, powers := [(25, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (55, 1)] }, { coefficient := 1, powers := [(20, 1), (55, 1)] }, { coefficient := 1, powers := [(26, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (46, 1)] }, { coefficient := 1, powers := [(4, 1), (35, 1)] }, { coefficient := 1, powers := [(15, 1), (22, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (52, 1)] }, { coefficient := 1, powers := [(7, 1), (32, 1)] }, { coefficient := 1, powers := [(10, 1), (27, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(20, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(44, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (54, 1)] }, { coefficient := 1, powers := [(3, 1), (26, 1), (60, 1)] }, { coefficient := 1, powers := [(20, 1), (54, 1)] }, { coefficient := 1, powers := [(26, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (39, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (48, 1), (54, 1)] }, { coefficient := 1, powers := [(21, 1), (54, 1)] }, { coefficient := 1, powers := [(26, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1), (55, 1)] }, { coefficient := 1, powers := [(26, 1), (47, 1), (51, 1)] }, { coefficient := 1, powers := [(44, 1), (55, 1)] }, { coefficient := 1, powers := [(51, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (48, 1), (55, 1)] }, { coefficient := 1, powers := [(21, 1), (55, 1)] }, { coefficient := 1, powers := [(26, 1), (42, 1)] }, { coefficient := 1, powers := [(26, 1), (48, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (49, 1), (53, 1)] }, { coefficient := 1, powers := [(21, 1), (44, 1), (53, 1)] }, { coefficient := 1, powers := [(42, 1), (44, 1)] }, { coefficient := 1, powers := [(49, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (37, 1), (60, 1)] }, { coefficient := 1, powers := [(1, 1)] }, { coefficient := 1, powers := [(10, 1), (35, 1), (37, 1)] }, { coefficient := 1, powers := [(15, 1), (32, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (39, 1), (60, 1)] }, { coefficient := 1, powers := [(1, 1), (48, 1), (54, 1)] }, { coefficient := 1, powers := [(10, 1), (35, 1), (39, 1)] }, { coefficient := 1, powers := [(15, 1), (32, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (52, 1)] }, { coefficient := 1, powers := [(3, 1), (60, 1)] }, { coefficient := 1, powers := [(20, 1), (52, 1)] }, { coefficient := 1, powers := [(20, 1), (57, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(4, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (60, 1)] }, { coefficient := 1, powers := [(10, 1), (46, 1)] }, { coefficient := 1, powers := [(10, 1), (57, 1)] }, { coefficient := 1, powers := [(15, 1), (41, 1)] }, { coefficient := 1, powers := [(15, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (52, 1)] }, { coefficient := 1, powers := [(22, 1), (57, 1)] }, { coefficient := 1, powers := [(27, 1), (41, 1)] }, { coefficient := 1, powers := [(27, 1), (46, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1)] }, { coefficient := 1, powers := [(35, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (37, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1)] }, { coefficient := 1, powers := [(3, 1), (25, 1), (60, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1), (60, 1)] }, { coefficient := 1, powers := [(20, 1)] }, { coefficient := 1, powers := [(25, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (37, 1), (61, 1)] }, { coefficient := 1, powers := [(0, 1), (44, 1), (51, 1)] }, { coefficient := 1, powers := [(3, 1), (25, 1), (61, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1), (61, 1)] }, { coefficient := 1, powers := [(20, 1), (44, 1), (51, 1)] }, { coefficient := 1, powers := [(25, 1), (44, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (41, 1), (58, 1)] }, { coefficient := 1, powers := [(0, 1), (47, 1), (54, 1)] }, { coefficient := 1, powers := [(26, 1), (41, 1), (44, 1)] }, { coefficient := 1, powers := [(26, 1), (47, 1)] }, { coefficient := 1, powers := [(44, 1), (54, 1)] }, { coefficient := 1, powers := [(58, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (39, 1), (61, 1)] }, { coefficient := 1, powers := [(0, 1), (42, 1), (58, 1)] }, { coefficient := 1, powers := [(0, 1), (49, 1), (55, 1)] }, { coefficient := 1, powers := [(21, 1), (44, 1), (55, 1)] }, { coefficient := 1, powers := [(21, 1), (51, 1), (58, 1)] }, { coefficient := 1, powers := [(26, 1), (42, 1), (44, 1)] }, { coefficient := 1, powers := [(26, 1), (49, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (38, 1), (60, 1)] }, { coefficient := 1, powers := [(1, 1), (41, 1), (57, 1)] }, { coefficient := 1, powers := [(1, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(4, 1), (27, 1), (60, 1)] }, { coefficient := 1, powers := [(4, 1), (32, 1), (57, 1)] }, { coefficient := 1, powers := [(4, 1), (35, 1), (52, 1)] }, { coefficient := 1, powers := [(7, 1), (22, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (32, 1), (46, 1)] }, { coefficient := 1, powers := [(7, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(10, 1), (22, 1), (57, 1)] }, { coefficient := 1, powers := [(10, 1), (27, 1), (46, 1)] }, { coefficient := 1, powers := [(10, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(15, 1), (22, 1), (52, 1)] }, { coefficient := 1, powers := [(15, 1), (27, 1), (41, 1)] }, { coefficient := 1, powers := [(15, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(42, 1), (65, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(57, 1)] }],
  [{ coefficient := 1, powers := [(58, 1), (66, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 35 → SparsePoly (Fin 67) := ![
  [{ coefficient := 1, powers := [(7, 1), (20, 1), (22, 1), (26, 1), (41, 1), (61, 1), (62, 1), (63, 1), (65, 1), (66, 1)] }, { coefficient := -1, powers := [(7, 1), (20, 1), (26, 1), (27, 1), (41, 1), (61, 1), (62, 1), (63, 1), (65, 1), (66, 1)] }, { coefficient := 1, powers := [(7, 1), (22, 1), (25, 1), (26, 1), (41, 1), (61, 1), (62, 1), (63, 1), (65, 1), (66, 1)] }, { coefficient := -1, powers := [(7, 1), (25, 1), (26, 1), (27, 1), (41, 1), (61, 1), (62, 1), (63, 1), (65, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (26, 1), (41, 1), (53, 1), (63, 1), (65, 1), (66, 1)] }, { coefficient := -1, powers := [(26, 1), (41, 1), (51, 1), (63, 1), (65, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (7, 1), (20, 1), (22, 1), (41, 1), (48, 1), (61, 1), (62, 1), (63, 1), (65, 1), (66, 1)] }, { coefficient := -1, powers := [(0, 1), (7, 1), (20, 1), (27, 1), (41, 1), (48, 1), (61, 1), (62, 1), (63, 1), (65, 1), (66, 1)] }, { coefficient := 1, powers := [(0, 1), (7, 1), (22, 1), (25, 1), (41, 1), (48, 1), (61, 1), (62, 1), (63, 1), (65, 1), (66, 1)] }, { coefficient := -1, powers := [(0, 1), (7, 1), (25, 1), (27, 1), (41, 1), (48, 1), (61, 1), (62, 1), (63, 1), (65, 1), (66, 1)] }, { coefficient := 1, powers := [(0, 1), (41, 1), (42, 1), (44, 1), (63, 1), (65, 1), (66, 1)] }, { coefficient := -1, powers := [(0, 1), (42, 1), (47, 1), (63, 1), (65, 1), (66, 1)] }, { coefficient := 1, powers := [(7, 1), (20, 1), (21, 1), (22, 1), (41, 1), (61, 1), (62, 1), (63, 1), (65, 1), (66, 1)] }, { coefficient := -1, powers := [(7, 1), (20, 1), (21, 1), (27, 1), (41, 1), (61, 1), (62, 1), (63, 1), (65, 1), (66, 1)] }, { coefficient := 1, powers := [(7, 1), (21, 1), (22, 1), (25, 1), (41, 1), (61, 1), (62, 1), (63, 1), (65, 1), (66, 1)] }, { coefficient := -1, powers := [(7, 1), (21, 1), (25, 1), (27, 1), (41, 1), (61, 1), (62, 1), (63, 1), (65, 1), (66, 1)] }, { coefficient := -1, powers := [(20, 1), (37, 1), (41, 2), (48, 1), (52, 1), (61, 1), (65, 1), (66, 1)] }, { coefficient := 1, powers := [(20, 1), (37, 1), (41, 1), (46, 1), (48, 1), (52, 1), (61, 1), (65, 1), (66, 1)] }, { coefficient := 1, powers := [(20, 1), (38, 1), (41, 1), (48, 1), (61, 1), (65, 1), (66, 1)] }, { coefficient := 1, powers := [(20, 1), (41, 1), (42, 1), (44, 1), (63, 1), (65, 1), (66, 1)] }, { coefficient := -1, powers := [(25, 1), (37, 1), (41, 2), (48, 1), (52, 1), (61, 1), (65, 1), (66, 1)] }, { coefficient := 1, powers := [(25, 1), (37, 1), (41, 1), (46, 1), (48, 1), (52, 1), (61, 1), (65, 1), (66, 1)] }, { coefficient := 1, powers := [(25, 1), (38, 1), (41, 1), (48, 1), (61, 1), (65, 1), (66, 1)] }, { coefficient := -1, powers := [(42, 1), (44, 1), (63, 1), (65, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (21, 1), (41, 1), (47, 1), (63, 1), (65, 1), (66, 1)] }, { coefficient := -1, powers := [(20, 1), (41, 1), (49, 1), (63, 1), (65, 1), (66, 1)] }, { coefficient := -1, powers := [(20, 1), (47, 1), (48, 1), (63, 1), (65, 1), (66, 1)] }, { coefficient := 1, powers := [(21, 1), (47, 1), (63, 1), (65, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (20, 1), (39, 1), (41, 1), (44, 1), (52, 1), (61, 1), (65, 1), (66, 2)] }, { coefficient := 1, powers := [(10, 1), (25, 1), (39, 1), (41, 1), (44, 1), (52, 1), (61, 1), (65, 1), (66, 2)] }],
  [{ coefficient := 2, powers := [(10, 1), (20, 1), (39, 1), (41, 2), (51, 1), (61, 1), (65, 2), (66, 1)] }, { coefficient := 2, powers := [(10, 1), (25, 1), (39, 1), (41, 2), (51, 1), (61, 1), (65, 2), (66, 1)] }, { coefficient := -1, powers := [(15, 1), (20, 1), (39, 1), (41, 1), (51, 1), (52, 1), (61, 1), (65, 2), (66, 1)] }, { coefficient := -1, powers := [(15, 1), (25, 1), (39, 1), (41, 1), (51, 1), (52, 1), (61, 1), (65, 2), (66, 1)] }],
  [{ coefficient := -2, powers := [(10, 1), (20, 1), (39, 1), (41, 2), (61, 1), (65, 2), (66, 1)] }, { coefficient := -2, powers := [(10, 1), (25, 1), (39, 1), (41, 2), (61, 1), (65, 2), (66, 1)] }, { coefficient := 1, powers := [(15, 1), (20, 1), (39, 1), (41, 1), (52, 1), (61, 1), (65, 2), (66, 1)] }, { coefficient := 1, powers := [(15, 1), (25, 1), (39, 1), (41, 1), (52, 1), (61, 1), (65, 2), (66, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (20, 1), (41, 2), (61, 1), (65, 1), (66, 1)] }, { coefficient := -1, powers := [(7, 1), (25, 1), (41, 2), (61, 1), (65, 1), (66, 1)] }, { coefficient := -1, powers := [(10, 1), (20, 1), (38, 1), (41, 1), (61, 1), (65, 1), (66, 1)] }, { coefficient := -1, powers := [(10, 1), (25, 1), (38, 1), (41, 1), (61, 1), (65, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(10, 1), (20, 1), (39, 1), (41, 1), (52, 1), (61, 1), (65, 1), (66, 2)] }, { coefficient := -1, powers := [(10, 1), (25, 1), (39, 1), (41, 1), (52, 1), (61, 1), (65, 1), (66, 2)] }],
  [{ coefficient := -1, powers := [(26, 1), (41, 1), (53, 1), (65, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(39, 1), (41, 1), (44, 1), (60, 1), (65, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(21, 1), (41, 1), (47, 1), (65, 1), (66, 1)] }, { coefficient := 1, powers := [(41, 1), (49, 1), (65, 1), (66, 1)] }, { coefficient := 1, powers := [(47, 1), (48, 1), (65, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(20, 1), (39, 1), (41, 1), (52, 1), (61, 1), (65, 1), (66, 1)] }, { coefficient := -1, powers := [(25, 1), (39, 1), (41, 1), (52, 1), (61, 1), (65, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (39, 1), (41, 2), (61, 1), (65, 1), (66, 1)] }, { coefficient := -1, powers := [(20, 1), (39, 1), (41, 1), (46, 1), (61, 1), (65, 1), (66, 1)] }, { coefficient := 1, powers := [(25, 1), (39, 1), (41, 2), (61, 1), (65, 1), (66, 1)] }, { coefficient := -1, powers := [(25, 1), (39, 1), (41, 1), (46, 1), (61, 1), (65, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(26, 1), (41, 1), (42, 1), (65, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(41, 1), (42, 1), (44, 1), (65, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (20, 1), (22, 1), (41, 1), (61, 1), (62, 1), (65, 1), (66, 1)] }, { coefficient := 1, powers := [(7, 1), (20, 1), (27, 1), (41, 1), (61, 1), (62, 1), (65, 1), (66, 1)] }, { coefficient := -1, powers := [(7, 1), (22, 1), (25, 1), (41, 1), (61, 1), (62, 1), (65, 1), (66, 1)] }, { coefficient := 1, powers := [(7, 1), (25, 1), (27, 1), (41, 1), (61, 1), (62, 1), (65, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (41, 1), (65, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(47, 1), (65, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(26, 1), (41, 1), (65, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(20, 1), (39, 1), (41, 2), (52, 1), (61, 1), (65, 1), (66, 1)] }, { coefficient := 1, powers := [(20, 1), (39, 1), (41, 1), (46, 1), (52, 1), (61, 1), (65, 1), (66, 1)] }, { coefficient := -1, powers := [(25, 1), (39, 1), (41, 2), (52, 1), (61, 1), (65, 1), (66, 1)] }, { coefficient := 1, powers := [(25, 1), (39, 1), (41, 1), (46, 1), (52, 1), (61, 1), (65, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (37, 1), (41, 2), (52, 1), (61, 1), (65, 1), (66, 1)] }, { coefficient := -1, powers := [(20, 1), (37, 1), (41, 1), (46, 1), (52, 1), (61, 1), (65, 1), (66, 1)] }, { coefficient := -1, powers := [(20, 1), (38, 1), (41, 1), (61, 1), (65, 1), (66, 1)] }, { coefficient := 1, powers := [(25, 1), (37, 1), (41, 2), (52, 1), (61, 1), (65, 1), (66, 1)] }, { coefficient := -1, powers := [(25, 1), (37, 1), (41, 1), (46, 1), (52, 1), (61, 1), (65, 1), (66, 1)] }, { coefficient := -1, powers := [(25, 1), (38, 1), (41, 1), (61, 1), (65, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(26, 1), (41, 1), (42, 1), (44, 1), (65, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(20, 1), (27, 1), (39, 1), (41, 1), (61, 1), (65, 1), (66, 1)] }, { coefficient := -1, powers := [(25, 1), (27, 1), (39, 1), (41, 1), (61, 1), (65, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (20, 1), (39, 1), (41, 1), (61, 1), (65, 1), (66, 1)] }, { coefficient := 1, powers := [(10, 1), (25, 1), (39, 1), (41, 1), (61, 1), (65, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(39, 1), (41, 1), (61, 1), (65, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(39, 1), (41, 1), (60, 1), (65, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(42, 1), (65, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(41, 1), (65, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (39, 1), (41, 1), (61, 1), (65, 1), (66, 1)] }, { coefficient := 1, powers := [(25, 1), (39, 1), (41, 1), (61, 1), (65, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (20, 1), (22, 1), (39, 1), (41, 1), (60, 1), (61, 1), (65, 1), (66, 1)] }, { coefficient := -1, powers := [(7, 1), (20, 1), (27, 1), (39, 1), (41, 1), (60, 1), (61, 1), (65, 1), (66, 1)] }, { coefficient := 1, powers := [(7, 1), (22, 1), (25, 1), (39, 1), (41, 1), (60, 1), (61, 1), (65, 1), (66, 1)] }, { coefficient := -1, powers := [(7, 1), (25, 1), (27, 1), (39, 1), (41, 1), (60, 1), (61, 1), (65, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (7, 1), (20, 1), (22, 1), (41, 1), (48, 1), (54, 1), (61, 1), (62, 1), (65, 1), (66, 1)] }, { coefficient := 1, powers := [(0, 1), (7, 1), (20, 1), (27, 1), (41, 1), (48, 1), (54, 1), (61, 1), (62, 1), (65, 1), (66, 1)] }, { coefficient := -1, powers := [(0, 1), (7, 1), (22, 1), (25, 1), (41, 1), (48, 1), (54, 1), (61, 1), (62, 1), (65, 1), (66, 1)] }, { coefficient := 1, powers := [(0, 1), (7, 1), (25, 1), (27, 1), (41, 1), (48, 1), (54, 1), (61, 1), (62, 1), (65, 1), (66, 1)] }, { coefficient := -1, powers := [(0, 1), (41, 1), (42, 1), (44, 1), (54, 1), (65, 1), (66, 1)] }, { coefficient := 1, powers := [(0, 1), (42, 1), (47, 1), (54, 1), (65, 1), (66, 1)] }, { coefficient := -1, powers := [(7, 1), (20, 1), (21, 1), (22, 1), (41, 1), (54, 1), (61, 1), (62, 1), (65, 1), (66, 1)] }, { coefficient := 1, powers := [(7, 1), (20, 1), (21, 1), (27, 1), (41, 1), (54, 1), (61, 1), (62, 1), (65, 1), (66, 1)] }, { coefficient := -1, powers := [(7, 1), (20, 1), (22, 1), (26, 1), (41, 1), (48, 1), (61, 1), (62, 1), (65, 1), (66, 1)] }, { coefficient := 1, powers := [(7, 1), (20, 1), (26, 1), (27, 1), (41, 1), (48, 1), (61, 1), (62, 1), (65, 1), (66, 1)] }, { coefficient := -1, powers := [(7, 1), (21, 1), (22, 1), (25, 1), (41, 1), (54, 1), (61, 1), (62, 1), (65, 1), (66, 1)] }, { coefficient := 1, powers := [(7, 1), (21, 1), (25, 1), (27, 1), (41, 1), (54, 1), (61, 1), (62, 1), (65, 1), (66, 1)] }, { coefficient := -1, powers := [(7, 1), (22, 1), (25, 1), (26, 1), (41, 1), (48, 1), (61, 1), (62, 1), (65, 1), (66, 1)] }, { coefficient := 1, powers := [(7, 1), (25, 1), (26, 1), (27, 1), (41, 1), (48, 1), (61, 1), (62, 1), (65, 1), (66, 1)] }, { coefficient := -1, powers := [(20, 1), (21, 1), (41, 1), (47, 1), (55, 1), (65, 1), (66, 1)] }, { coefficient := -1, powers := [(20, 1), (41, 1), (42, 1), (44, 1), (54, 1), (65, 1), (66, 1)] }, { coefficient := 1, powers := [(20, 1), (41, 1), (49, 1), (55, 1), (65, 1), (66, 1)] }, { coefficient := 1, powers := [(20, 1), (47, 1), (48, 1), (55, 1), (65, 1), (66, 1)] }, { coefficient := -1, powers := [(21, 1), (47, 1), (55, 1), (65, 1), (66, 1)] }, { coefficient := -1, powers := [(25, 1), (26, 1), (41, 1), (49, 1), (53, 1), (65, 1), (66, 1)] }, { coefficient := 1, powers := [(26, 1), (41, 1), (49, 1), (51, 1), (65, 1), (66, 1)] }, { coefficient := 1, powers := [(42, 1), (44, 1), (54, 1), (65, 1), (66, 1)] }],
  [{ coefficient := 2, powers := [(10, 1), (20, 1), (27, 1), (39, 1), (41, 2), (61, 1), (65, 1), (66, 1)] }, { coefficient := 2, powers := [(10, 1), (25, 1), (27, 1), (39, 1), (41, 2), (61, 1), (65, 1), (66, 1)] }, { coefficient := -1, powers := [(15, 1), (20, 1), (27, 1), (39, 1), (41, 1), (52, 1), (61, 1), (65, 1), (66, 1)] }, { coefficient := -1, powers := [(15, 1), (25, 1), (27, 1), (39, 1), (41, 1), (52, 1), (61, 1), (65, 1), (66, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(1, 1), (20, 1), (39, 1), (41, 2), (61, 1), (65, 1), (66, 1)] }, { coefficient := -1, powers := [(1, 1), (25, 1), (39, 1), (41, 2), (61, 1), (65, 1), (66, 1)] }, { coefficient := -1, powers := [(4, 1), (20, 1), (32, 1), (39, 1), (41, 1), (61, 1), (65, 1), (66, 1)] }, { coefficient := -1, powers := [(4, 1), (25, 1), (32, 1), (39, 1), (41, 1), (61, 1), (65, 1), (66, 1)] }, { coefficient := -2, powers := [(10, 1), (20, 1), (22, 1), (39, 1), (41, 1), (61, 1), (65, 1), (66, 1)] }, { coefficient := 1, powers := [(10, 1), (20, 1), (27, 1), (39, 1), (41, 1), (61, 1), (65, 1), (66, 1)] }, { coefficient := -2, powers := [(10, 1), (22, 1), (25, 1), (39, 1), (41, 1), (61, 1), (65, 1), (66, 1)] }, { coefficient := 1, powers := [(10, 1), (25, 1), (27, 1), (39, 1), (41, 1), (61, 1), (65, 1), (66, 1)] }, { coefficient := -1, powers := [(20, 1), (26, 1), (41, 1), (42, 1), (44, 1), (65, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (20, 1), (22, 1), (39, 1), (41, 1), (52, 1), (61, 1), (65, 1), (66, 1)] }, { coefficient := 1, powers := [(10, 1), (22, 1), (25, 1), (39, 1), (41, 1), (52, 1), (61, 1), (65, 1), (66, 1)] }, { coefficient := -1, powers := [(42, 1), (65, 1)] }]
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
    (values : Fin 67 → R) :
    ¬ ∀ index : Fin 35,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component37.SelectedLeafB6_3_1.selectedHasNoCommonZero

end Krenn.Component37.SelectedLeafB6_3_1
