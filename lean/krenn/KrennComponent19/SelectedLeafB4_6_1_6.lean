import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component19.SelectedLeafB4_6_1_6

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "a7008cadaf7aad577a883aad04b2d4f10315a0b395a4794832060e342b6fa192"
def certificateSHA256 : String := "c3ce73cb62014d68b717918517971bf8b84f39f7e04a15dc449dedd6b11d7e4d"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 30 → Fin 675 := ![
  2,
  7,
  10,
  18,
  20,
  22,
  302,
  318,
  324,
  412,
  413,
  420,
  424,
  429,
  446,
  452,
  565,
  582,
  583,
  608,
  610,
  646,
  662,
  663,
  665,
  668,
  670,
  671,
  672,
  674
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 30 → SparsePoly (Fin 68) := ![
  [{ coefficient := 1, powers := [(5, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (26, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1)] }, { coefficient := 1, powers := [(21, 1), (46, 1)] }, { coefficient := 1, powers := [(26, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (55, 1)] }, { coefficient := 1, powers := [(32, 1), (44, 1)] }, { coefficient := 1, powers := [(35, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1), (53, 1)] }, { coefficient := 1, powers := [(21, 1), (46, 1), (53, 1)] }, { coefficient := 1, powers := [(46, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (49, 1)] }, { coefficient := 1, powers := [(26, 1), (43, 1), (46, 1)] }, { coefficient := 1, powers := [(26, 1), (49, 1)] }, { coefficient := 1, powers := [(46, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (54, 1)] }, { coefficient := 1, powers := [(3, 1), (27, 1), (60, 1)] }, { coefficient := 1, powers := [(21, 1), (54, 1)] }, { coefficient := 1, powers := [(27, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (50, 1)] }, { coefficient := 1, powers := [(5, 1), (38, 1)] }, { coefficient := 1, powers := [(19, 1), (30, 1), (50, 1)] }, { coefficient := 1, powers := [(20, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1)] }, { coefficient := 1, powers := [(13, 1), (32, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (61, 1)] }, { coefficient := 1, powers := [(13, 1), (27, 1), (49, 1)] }, { coefficient := 1, powers := [(13, 1), (58, 1)] }, { coefficient := 1, powers := [(20, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1), (54, 1)] }, { coefficient := 1, powers := [(21, 1), (46, 1), (54, 1)] }, { coefficient := 1, powers := [(21, 1), (58, 1)] }, { coefficient := 1, powers := [(27, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (49, 1), (53, 1)] }, { coefficient := 1, powers := [(43, 1), (46, 1)] }, { coefficient := 1, powers := [(46, 1), (53, 1)] }, { coefficient := 1, powers := [(49, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (46, 1), (54, 1)] }, { coefficient := 1, powers := [(25, 1), (58, 1)] }, { coefficient := 1, powers := [(32, 1), (50, 1)] }, { coefficient := 1, powers := [(38, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (48, 1)] }, { coefficient := 1, powers := [(6, 1), (60, 1)] }, { coefficient := 1, powers := [(26, 1), (43, 1)] }, { coefficient := 1, powers := [(26, 1), (48, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (53, 1)] }, { coefficient := 1, powers := [(3, 1), (60, 1)] }, { coefficient := 1, powers := [(21, 1), (53, 1)] }, { coefficient := 1, powers := [(21, 1), (57, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (39, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1)] }, { coefficient := 1, powers := [(3, 1), (26, 1), (60, 1)] }, { coefficient := 1, powers := [(6, 1), (21, 1), (60, 1)] }, { coefficient := 1, powers := [(21, 1)] }, { coefficient := 1, powers := [(26, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1), (58, 1)] }, { coefficient := 1, powers := [(0, 1), (49, 1), (54, 1)] }, { coefficient := 1, powers := [(27, 1), (43, 1), (46, 1)] }, { coefficient := 1, powers := [(27, 1), (49, 1)] }, { coefficient := 1, powers := [(46, 1), (54, 1)] }, { coefficient := 1, powers := [(58, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (40, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (43, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (48, 1), (53, 1)] }, { coefficient := 1, powers := [(43, 1)] }, { coefficient := 1, powers := [(48, 1)] }, { coefficient := 1, powers := [(53, 1)] }, { coefficient := 1, powers := [(57, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (41, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (44, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (50, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (38, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (25, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (50, 1)] }, { coefficient := 1, powers := [(8, 1), (38, 1), (44, 1)] }, { coefficient := 1, powers := [(13, 1), (25, 1), (58, 1)] }, { coefficient := 1, powers := [(13, 1), (32, 1), (50, 1)] }, { coefficient := 1, powers := [(13, 1), (38, 1), (41, 1)] }, { coefficient := 1, powers := [(20, 1), (25, 1), (55, 1)] }, { coefficient := 1, powers := [(20, 1), (32, 1), (44, 1)] }, { coefficient := 1, powers := [(20, 1), (35, 1), (41, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(44, 1)] }],
  [{ coefficient := 1, powers := [(57, 1)] }],
  [{ coefficient := 1, powers := [(58, 1), (65, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(26, 1), (66, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(32, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 30 → SparsePoly (Fin 68) := ![
  [{ coefficient := 1, powers := [(0, 1), (26, 1), (35, 1), (40, 1), (58, 1)] }, { coefficient := 2, powers := [(0, 1), (26, 1), (38, 1), (40, 1), (55, 1)] }, { coefficient := 2, powers := [(0, 1), (35, 1), (39, 1), (48, 1), (58, 1)] }, { coefficient := 4, powers := [(0, 1), (38, 1), (39, 1), (48, 1), (55, 1)] }, { coefficient := 1, powers := [(3, 1), (26, 1), (35, 1), (48, 1), (58, 1)] }, { coefficient := -1, powers := [(3, 1), (26, 1), (35, 1), (58, 1), (62, 1)] }, { coefficient := 2, powers := [(3, 1), (26, 1), (38, 1), (48, 1), (55, 1)] }, { coefficient := -2, powers := [(3, 1), (26, 1), (38, 1), (55, 1), (62, 1)] }, { coefficient := -2, powers := [(6, 1), (35, 1), (58, 1)] }, { coefficient := -4, powers := [(6, 1), (38, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (25, 1), (26, 1), (40, 1), (58, 1), (60, 1), (66, 1)] }, { coefficient := -2, powers := [(0, 1), (25, 1), (39, 1), (48, 1), (58, 1), (60, 1), (66, 1)] }, { coefficient := -1, powers := [(3, 1), (25, 1), (26, 1), (48, 1), (58, 1), (60, 1), (66, 1)] }, { coefficient := 1, powers := [(3, 1), (25, 1), (26, 1), (58, 1), (60, 1), (62, 1), (66, 1)] }, { coefficient := 2, powers := [(6, 1), (25, 1), (58, 1), (60, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (25, 1), (26, 1), (27, 1), (40, 1), (60, 1)] }, { coefficient := -2, powers := [(0, 1), (25, 1), (27, 1), (39, 1), (48, 1), (60, 1)] }, { coefficient := -1, powers := [(3, 1), (25, 1), (26, 1), (27, 1), (48, 1), (60, 1)] }, { coefficient := 1, powers := [(3, 1), (25, 1), (26, 1), (27, 1), (60, 1), (62, 1)] }, { coefficient := 2, powers := [(6, 1), (25, 1), (27, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (26, 1), (30, 1), (40, 1), (55, 1), (60, 1)] }, { coefficient := 2, powers := [(0, 1), (30, 1), (39, 1), (48, 1), (55, 1), (60, 1)] }, { coefficient := 1, powers := [(3, 1), (26, 1), (30, 1), (48, 1), (55, 1), (60, 1)] }, { coefficient := -1, powers := [(3, 1), (26, 1), (30, 1), (55, 1), (60, 1), (62, 1)] }, { coefficient := -2, powers := [(6, 1), (30, 1), (55, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (19, 1), (26, 1), (40, 1), (50, 1), (60, 1)] }, { coefficient := -2, powers := [(0, 1), (19, 1), (39, 1), (48, 1), (50, 1), (60, 1)] }, { coefficient := -1, powers := [(3, 1), (19, 1), (26, 1), (48, 1), (50, 1), (60, 1)] }, { coefficient := 1, powers := [(3, 1), (19, 1), (26, 1), (50, 1), (60, 1), (62, 1)] }, { coefficient := 2, powers := [(6, 1), (19, 1), (50, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (13, 1), (26, 1), (40, 1), (46, 1), (60, 1)] }, { coefficient := -2, powers := [(0, 1), (13, 1), (39, 1), (46, 1), (48, 1), (60, 1)] }, { coefficient := -1, powers := [(3, 1), (13, 1), (26, 1), (46, 1), (48, 1), (60, 1)] }, { coefficient := 1, powers := [(3, 1), (13, 1), (26, 1), (46, 1), (60, 1), (62, 1)] }, { coefficient := 2, powers := [(6, 1), (13, 1), (46, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(26, 1), (43, 1), (54, 1), (65, 1), (66, 1)] }, { coefficient := 1, powers := [(26, 1), (54, 1), (62, 1), (65, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (20, 1), (26, 1), (40, 1), (60, 1)] }, { coefficient := 2, powers := [(0, 1), (20, 1), (39, 1), (48, 1), (60, 1)] }, { coefficient := 1, powers := [(3, 1), (20, 1), (26, 1), (48, 1), (60, 1)] }, { coefficient := -1, powers := [(3, 1), (20, 1), (26, 1), (60, 1), (62, 1)] }, { coefficient := -2, powers := [(6, 1), (20, 1), (60, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (27, 1), (48, 2), (65, 1)] }, { coefficient := 2, powers := [(26, 1), (27, 1), (43, 1), (48, 1), (65, 1)] }, { coefficient := 2, powers := [(26, 1), (27, 1), (43, 1), (65, 1), (66, 1)] }, { coefficient := 2, powers := [(26, 1), (27, 1), (48, 2), (65, 1)] }, { coefficient := 1, powers := [(26, 1), (27, 1), (48, 1), (53, 1), (65, 1)] }, { coefficient := 1, powers := [(26, 1), (27, 1), (53, 1), (62, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(26, 1), (27, 1), (62, 1), (65, 1), (66, 1)] }, { coefficient := 1, powers := [(26, 1), (54, 1), (65, 1), (66, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (46, 1), (48, 2), (65, 1)] }, { coefficient := 2, powers := [(26, 1), (43, 1), (46, 1), (48, 1), (65, 1)] }, { coefficient := 2, powers := [(26, 1), (43, 1), (46, 1), (65, 1), (66, 1)] }, { coefficient := 2, powers := [(26, 1), (46, 1), (48, 2), (65, 1)] }, { coefficient := 1, powers := [(26, 1), (46, 1), (48, 1), (53, 1), (65, 1)] }, { coefficient := 1, powers := [(26, 1), (46, 1), (53, 1), (62, 1), (65, 1)] }, { coefficient := -1, powers := [(26, 1), (46, 1), (62, 1), (65, 1), (66, 1)] }, { coefficient := -1, powers := [(26, 1), (49, 1), (65, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (26, 1), (40, 1), (55, 1), (60, 1)] }, { coefficient := -2, powers := [(0, 1), (39, 1), (48, 1), (55, 1), (60, 1)] }, { coefficient := -1, powers := [(3, 1), (26, 1), (48, 1), (55, 1), (60, 1)] }, { coefficient := 1, powers := [(3, 1), (26, 1), (55, 1), (60, 1), (62, 1)] }, { coefficient := 2, powers := [(6, 1), (55, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (26, 1), (40, 1), (50, 1), (60, 1)] }, { coefficient := 2, powers := [(0, 1), (39, 1), (48, 1), (50, 1), (60, 1)] }, { coefficient := 1, powers := [(3, 1), (26, 1), (48, 1), (50, 1), (60, 1)] }, { coefficient := -1, powers := [(3, 1), (26, 1), (50, 1), (60, 1), (62, 1)] }, { coefficient := -2, powers := [(6, 1), (50, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (25, 1), (26, 1), (40, 1), (60, 1)] }, { coefficient := 2, powers := [(0, 1), (25, 1), (39, 1), (48, 1), (60, 1)] }, { coefficient := 1, powers := [(3, 1), (25, 1), (26, 1), (48, 1), (60, 1)] }, { coefficient := -1, powers := [(3, 1), (25, 1), (26, 1), (60, 1), (62, 1)] }, { coefficient := -2, powers := [(6, 1), (25, 1), (60, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (48, 2), (65, 1)] }, { coefficient := -2, powers := [(26, 1), (43, 1), (48, 1), (65, 1)] }, { coefficient := -1, powers := [(26, 1), (43, 1), (65, 1), (66, 1)] }, { coefficient := -2, powers := [(26, 1), (48, 2), (65, 1)] }, { coefficient := -1, powers := [(26, 1), (48, 1), (53, 1), (65, 1)] }, { coefficient := -1, powers := [(26, 1), (53, 1), (62, 1), (65, 1)] }, { coefficient := -1, powers := [(26, 1), (62, 1), (65, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(21, 1), (26, 1), (27, 1), (62, 1), (65, 1), (66, 1)] }, { coefficient := -1, powers := [(26, 1), (27, 1), (65, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (13, 1), (26, 1), (40, 1), (60, 1)] }, { coefficient := 2, powers := [(0, 1), (13, 1), (39, 1), (48, 1), (60, 1)] }, { coefficient := 1, powers := [(3, 1), (13, 1), (26, 1), (48, 1), (60, 1)] }, { coefficient := -1, powers := [(3, 1), (13, 1), (26, 1), (60, 1), (62, 1)] }, { coefficient := -2, powers := [(6, 1), (13, 1), (60, 1)] }],
  [{ coefficient := 2, powers := [(21, 1), (48, 1)] }, { coefficient := 2, powers := [] }],
  [{ coefficient := -2, powers := [(0, 1), (27, 1), (46, 1), (48, 2), (65, 1)] }, { coefficient := -2, powers := [(26, 1), (27, 1), (43, 1), (46, 1), (48, 1), (65, 1)] }, { coefficient := -2, powers := [(26, 1), (27, 1), (43, 1), (46, 1), (65, 1), (66, 1)] }, { coefficient := -2, powers := [(26, 1), (27, 1), (46, 1), (48, 2), (65, 1)] }, { coefficient := -1, powers := [(26, 1), (27, 1), (46, 1), (48, 1), (53, 1), (65, 1)] }, { coefficient := -1, powers := [(26, 1), (27, 1), (46, 1), (53, 1), (62, 1), (65, 1)] }, { coefficient := 1, powers := [(26, 1), (27, 1), (46, 1), (62, 1), (65, 1), (66, 1)] }, { coefficient := 1, powers := [(26, 1), (27, 1), (49, 1), (65, 1), (66, 1)] }, { coefficient := 1, powers := [(26, 1), (48, 1)] }, { coefficient := 1, powers := [(26, 1), (62, 1)] }],
  [{ coefficient := -2, powers := [(48, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (26, 1), (62, 1), (65, 1), (66, 1)] }, { coefficient := -1, powers := [(26, 2), (62, 1), (65, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(26, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (26, 1), (40, 1), (60, 1)] }, { coefficient := -2, powers := [(0, 1), (39, 1), (48, 1), (60, 1)] }, { coefficient := -1, powers := [(3, 1), (26, 1), (48, 1), (60, 1)] }, { coefficient := 1, powers := [(3, 1), (26, 1), (60, 1), (62, 1)] }, { coefficient := 2, powers := [(6, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (26, 1), (27, 1), (49, 1), (53, 1), (65, 1), (66, 1)] }, { coefficient := -1, powers := [(21, 1), (26, 1), (43, 1), (58, 1), (65, 1), (66, 1)] }, { coefficient := -1, powers := [(21, 1), (26, 1), (49, 1), (54, 1), (65, 1), (66, 1)] }, { coefficient := 1, powers := [(26, 2), (43, 1), (58, 1), (65, 1), (66, 1)] }, { coefficient := 1, powers := [(26, 2), (49, 1), (54, 1), (65, 1), (66, 1)] }, { coefficient := -1, powers := [(26, 1), (27, 1), (46, 1), (53, 1), (65, 1), (66, 1)] }, { coefficient := -1, powers := [(26, 1), (27, 1), (49, 1), (65, 1), (66, 1)] }, { coefficient := 1, powers := [(26, 1), (46, 1), (54, 1), (65, 1), (66, 1)] }, { coefficient := -1, powers := [(26, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (26, 1), (40, 1), (41, 1), (60, 1), (61, 1)] }, { coefficient := 1, powers := [(0, 1), (26, 1), (40, 1), (50, 1), (55, 1), (60, 1)] }, { coefficient := 2, powers := [(0, 1), (39, 1), (41, 1), (48, 1), (60, 1), (61, 1)] }, { coefficient := 2, powers := [(0, 1), (39, 1), (48, 1), (50, 1), (55, 1), (60, 1)] }, { coefficient := 1, powers := [(3, 1), (26, 1), (41, 1), (48, 1), (60, 1), (61, 1)] }, { coefficient := -1, powers := [(3, 1), (26, 1), (41, 1), (60, 1), (61, 1), (62, 1)] }, { coefficient := 1, powers := [(3, 1), (26, 1), (48, 1), (50, 1), (55, 1), (60, 1)] }, { coefficient := -1, powers := [(3, 1), (26, 1), (50, 1), (55, 1), (60, 1), (62, 1)] }, { coefficient := -2, powers := [(6, 1), (41, 1), (60, 1), (61, 1)] }, { coefficient := -2, powers := [(6, 1), (50, 1), (55, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (2, 1), (26, 1), (40, 1), (58, 1), (60, 1)] }, { coefficient := 2, powers := [(0, 1), (2, 1), (39, 1), (48, 1), (58, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (8, 1), (26, 1), (38, 1), (40, 1), (60, 1)] }, { coefficient := 2, powers := [(0, 1), (8, 1), (38, 1), (39, 1), (48, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (3, 1), (26, 1), (48, 1), (58, 1), (60, 1)] }, { coefficient := -1, powers := [(2, 1), (3, 1), (26, 1), (58, 1), (60, 1), (62, 1)] }, { coefficient := -2, powers := [(2, 1), (6, 1), (58, 1), (60, 1)] }, { coefficient := 1, powers := [(3, 1), (8, 1), (26, 1), (38, 1), (48, 1), (60, 1)] }, { coefficient := -1, powers := [(3, 1), (8, 1), (26, 1), (38, 1), (60, 1), (62, 1)] }, { coefficient := -2, powers := [(6, 1), (8, 1), (38, 1), (60, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (21, 1), (27, 1), (46, 1), (48, 2), (65, 1)] }, { coefficient := 1, powers := [(0, 1), (26, 1), (43, 1)] }, { coefficient := 2, powers := [(21, 1), (26, 1), (27, 1), (43, 1), (46, 1), (48, 1), (65, 1)] }, { coefficient := 2, powers := [(21, 1), (26, 1), (27, 1), (43, 1), (46, 1), (65, 1), (66, 1)] }, { coefficient := 2, powers := [(21, 1), (26, 1), (27, 1), (46, 1), (48, 2), (65, 1)] }, { coefficient := 1, powers := [(21, 1), (26, 1), (27, 1), (46, 1), (48, 1), (53, 1), (65, 1)] }, { coefficient := 1, powers := [(21, 1), (26, 1), (27, 1), (46, 1), (53, 1), (62, 1), (65, 1)] }, { coefficient := -1, powers := [(21, 1), (26, 1), (27, 1), (46, 1), (62, 1), (65, 1), (66, 1)] }, { coefficient := -1, powers := [(21, 1), (26, 1), (27, 1), (49, 1), (65, 1), (66, 1)] }, { coefficient := -1, powers := [(21, 1), (26, 1), (48, 1)] }, { coefficient := -1, powers := [(21, 1), (26, 1), (62, 1)] }, { coefficient := 1, powers := [(26, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (21, 1), (48, 2)] }, { coefficient := 2, powers := [(21, 1), (26, 1), (43, 1), (48, 1)] }, { coefficient := 2, powers := [(21, 1), (26, 1), (48, 2)] }, { coefficient := 1, powers := [(21, 1), (26, 1), (48, 1), (53, 1)] }, { coefficient := 1, powers := [(21, 1), (26, 1), (53, 1), (62, 1)] }, { coefficient := 1, powers := [(26, 1), (43, 1)] }, { coefficient := 1, powers := [(26, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (13, 1), (25, 1), (26, 1), (40, 1), (58, 1), (60, 1)] }, { coefficient := 2, powers := [(0, 1), (13, 1), (25, 1), (39, 1), (48, 1), (58, 1), (60, 1)] }, { coefficient := 1, powers := [(3, 1), (13, 1), (25, 1), (26, 1), (48, 1), (58, 1), (60, 1)] }, { coefficient := -1, powers := [(3, 1), (13, 1), (25, 1), (26, 1), (58, 1), (60, 1), (62, 1)] }, { coefficient := -2, powers := [(6, 1), (13, 1), (25, 1), (58, 1), (60, 1)] }, { coefficient := 1, powers := [(26, 1), (43, 1), (58, 1), (65, 1)] }, { coefficient := 1, powers := [(26, 1), (58, 1), (62, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (5, 1), (26, 1), (40, 1), (60, 1), (61, 1)] }, { coefficient := 2, powers := [(0, 1), (5, 1), (39, 1), (48, 1), (60, 1), (61, 1)] }, { coefficient := -1, powers := [(0, 1), (13, 1), (26, 1), (40, 1), (50, 1), (60, 1)] }, { coefficient := -2, powers := [(0, 1), (13, 1), (39, 1), (48, 1), (50, 1), (60, 1)] }, { coefficient := 1, powers := [(3, 1), (5, 1), (26, 1), (48, 1), (60, 1), (61, 1)] }, { coefficient := -1, powers := [(3, 1), (5, 1), (26, 1), (60, 1), (61, 1), (62, 1)] }, { coefficient := -1, powers := [(3, 1), (13, 1), (26, 1), (48, 1), (50, 1), (60, 1)] }, { coefficient := 1, powers := [(3, 1), (13, 1), (26, 1), (50, 1), (60, 1), (62, 1)] }, { coefficient := -2, powers := [(5, 1), (6, 1), (60, 1), (61, 1)] }, { coefficient := 2, powers := [(6, 1), (13, 1), (50, 1), (60, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
/-- Lean replays the exact selected-row integer certificate. -/
theorem constantIdentity :
    ∑ index, (multipliers index).toPoly *
      (selectedEquations index).toPoly = C (2 : ℤ) := by
  simp (config := { maxSteps := 1000000 })
    [Fin.sum_univ_succ, multipliers, selectedEquations,
    SparsePoly.toPoly, SparseTerm.toPoly]
  ring

/-- The selected rows have no common zero in a characteristic-zero ring. -/
theorem selectedHasNoCommonZero {R : Type*} [CommRing R] [Nontrivial R] [CharZero R]
    (values : Fin 68 → R) :
    ¬ ∀ index : Fin 30,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((2 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (2 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (2 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component19.SelectedLeafB4_6_1_6.selectedHasNoCommonZero

end Krenn.Component19.SelectedLeafB4_6_1_6
