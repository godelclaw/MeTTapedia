import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component19.SelectedLeafB5_6_6_4

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "2cca8ed933ff3d5e520a1bcaa585094c022f667d2fc942f604c5a9508c81037b"
def certificateSHA256 : String := "194d854b1e55af7c4dcf0d6a78b98bf29f2ff59119b4ee04bd66f73c9fd8d064"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 39 → Fin 675 := ![
  0,
  2,
  3,
  10,
  18,
  20,
  22,
  29,
  170,
  171,
  195,
  196,
  200,
  203,
  220,
  318,
  418,
  420,
  422,
  424,
  429,
  439,
  440,
  442,
  468,
  484,
  489,
  565,
  582,
  608,
  646,
  654,
  662,
  663,
  665,
  668,
  671,
  672,
  674
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 39 → SparsePoly (Fin 69) := ![
  [{ coefficient := 1, powers := [(3, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(31, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (50, 1)] }, { coefficient := 1, powers := [(26, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (55, 1)] }, { coefficient := 1, powers := [(21, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (46, 1)] }, { coefficient := 1, powers := [(30, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (53, 1)] }, { coefficient := 1, powers := [(25, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (48, 1), (55, 1)] }, { coefficient := 1, powers := [(55, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (50, 1), (53, 1)] }, { coefficient := 1, powers := [(50, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (25, 1), (60, 1)] }, { coefficient := 1, powers := [(25, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (55, 1)] }, { coefficient := 1, powers := [(32, 1), (44, 1)] }, { coefficient := 1, powers := [(35, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (48, 1)] }, { coefficient := 1, powers := [(19, 1), (30, 1), (43, 1)] }, { coefficient := 1, powers := [(19, 1), (30, 1), (48, 1)] }, { coefficient := 1, powers := [(19, 1), (31, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (50, 1)] }, { coefficient := 1, powers := [(5, 1), (38, 1)] }, { coefficient := 1, powers := [(19, 1), (30, 1), (50, 1)] }, { coefficient := 1, powers := [(20, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (53, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (53, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (57, 1)] }, { coefficient := 1, powers := [(19, 1), (31, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1)] }, { coefficient := 1, powers := [(13, 1), (32, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (61, 1)] }, { coefficient := 1, powers := [(13, 1), (27, 1), (49, 1)] }, { coefficient := 1, powers := [(13, 1), (58, 1)] }, { coefficient := 1, powers := [(20, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (43, 1)] }, { coefficient := 1, powers := [(19, 1), (48, 1)] }, { coefficient := 1, powers := [(19, 1), (53, 1)] }, { coefficient := 1, powers := [(19, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(31, 1), (43, 1)] }, { coefficient := 1, powers := [(31, 1), (48, 1)] }, { coefficient := 1, powers := [(31, 1), (53, 1)] }, { coefficient := 1, powers := [(31, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (41, 1), (61, 1)] }, { coefficient := 1, powers := [(0, 1), (44, 1), (58, 1)] }, { coefficient := 1, powers := [(0, 1), (50, 1), (55, 1)] }, { coefficient := 1, powers := [(27, 1), (44, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (41, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (25, 1), (60, 1)] }, { coefficient := 1, powers := [(19, 1), (25, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (50, 1), (53, 1)] }, { coefficient := 1, powers := [(5, 1), (38, 1), (53, 1)] }, { coefficient := 1, powers := [(19, 1), (31, 1), (50, 1)] }, { coefficient := 1, powers := [(20, 1), (25, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (31, 1), (60, 1)] }, { coefficient := 1, powers := [(24, 1), (53, 1)] }, { coefficient := 1, powers := [(24, 1), (57, 1)] }, { coefficient := 1, powers := [(31, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (46, 1), (54, 1)] }, { coefficient := 1, powers := [(25, 1), (58, 1)] }, { coefficient := 1, powers := [(32, 1), (50, 1)] }, { coefficient := 1, powers := [(38, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (48, 1)] }, { coefficient := 1, powers := [(6, 1), (60, 1)] }, { coefficient := 1, powers := [(26, 1), (43, 1)] }, { coefficient := 1, powers := [(26, 1), (48, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (39, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1)] }, { coefficient := 1, powers := [(3, 1), (26, 1), (60, 1)] }, { coefficient := 1, powers := [(6, 1), (21, 1), (60, 1)] }, { coefficient := 1, powers := [(21, 1)] }, { coefficient := 1, powers := [(26, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (40, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (43, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (48, 1), (53, 1)] }, { coefficient := 1, powers := [(43, 1)] }, { coefficient := 1, powers := [(48, 1)] }, { coefficient := 1, powers := [(53, 1)] }, { coefficient := 1, powers := [(57, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (40, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (43, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (48, 1), (53, 1)] }, { coefficient := 1, powers := [(19, 1), (31, 1), (43, 1)] }, { coefficient := 1, powers := [(19, 1), (31, 1), (48, 1)] }, { coefficient := 1, powers := [(19, 1), (31, 1), (53, 1)] }, { coefficient := 1, powers := [(19, 1), (31, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (41, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (44, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (50, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (38, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (25, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (50, 1)] }, { coefficient := 1, powers := [(8, 1), (38, 1), (44, 1)] }, { coefficient := 1, powers := [(13, 1), (25, 1), (58, 1)] }, { coefficient := 1, powers := [(13, 1), (32, 1), (50, 1)] }, { coefficient := 1, powers := [(13, 1), (38, 1), (41, 1)] }, { coefficient := 1, powers := [(20, 1), (25, 1), (55, 1)] }, { coefficient := 1, powers := [(20, 1), (32, 1), (44, 1)] }, { coefficient := 1, powers := [(20, 1), (35, 1), (41, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(44, 1)] }],
  [{ coefficient := 1, powers := [(58, 1)] }],
  [{ coefficient := 1, powers := [(26, 1), (68, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(32, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 39 → SparsePoly (Fin 69) := ![
  [{ coefficient := 1, powers := [(19, 1), (21, 1), (31, 1), (41, 1), (60, 1)] }, { coefficient := 1, powers := [(19, 1), (26, 1), (31, 1), (41, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (38, 1), (39, 1), (55, 1), (57, 1)] }, { coefficient := -1, powers := [(3, 1), (26, 1), (38, 1), (55, 1), (57, 1)] }, { coefficient := -1, powers := [(6, 1), (21, 1), (38, 1), (55, 1), (57, 1)] }, { coefficient := -1, powers := [(6, 1), (38, 1), (55, 1)] }],
  [{ coefficient := -2, powers := [(8, 1), (21, 1), (25, 1), (48, 1), (60, 1)] }, { coefficient := 2, powers := [(8, 1), (25, 1), (26, 1), (57, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (25, 1), (27, 1), (48, 1)] }, { coefficient := 1, powers := [(0, 1), (25, 1), (27, 1), (57, 1)] }, { coefficient := 2, powers := [(21, 1), (25, 1), (27, 1), (48, 1)] }, { coefficient := 1, powers := [(21, 1), (25, 1), (27, 1), (57, 1)] }, { coefficient := -1, powers := [(25, 1), (26, 1), (27, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [(21, 1), (30, 1), (48, 1), (55, 1)] }, { coefficient := 1, powers := [(21, 1), (31, 1), (55, 1)] }, { coefficient := -1, powers := [(26, 1), (31, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (19, 1), (39, 1), (50, 1), (57, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (19, 1), (48, 1), (50, 1)] }, { coefficient := 1, powers := [(0, 1), (19, 1), (50, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (19, 1), (26, 1), (50, 1), (57, 1), (60, 1)] }, { coefficient := 1, powers := [(6, 1), (19, 1), (21, 1), (50, 1), (57, 1), (60, 1)] }, { coefficient := 1, powers := [(6, 1), (19, 1), (50, 1), (60, 1)] }, { coefficient := 1, powers := [(19, 1), (21, 1), (50, 1), (57, 1)] }, { coefficient := 1, powers := [(19, 1), (26, 1), (50, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (13, 1), (39, 1), (46, 1), (57, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (13, 1), (46, 1), (48, 1)] }, { coefficient := 1, powers := [(0, 1), (13, 1), (46, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (19, 1), (39, 1), (57, 1), (61, 1)] }, { coefficient := 1, powers := [(3, 1), (13, 1), (26, 1), (46, 1), (57, 1), (60, 1)] }, { coefficient := 1, powers := [(3, 1), (19, 1), (26, 1), (57, 1), (61, 1)] }, { coefficient := 1, powers := [(6, 1), (13, 1), (21, 1), (46, 1), (57, 1), (60, 1)] }, { coefficient := 1, powers := [(6, 1), (13, 1), (46, 1), (60, 1)] }, { coefficient := 1, powers := [(6, 1), (19, 1), (21, 1), (57, 1), (61, 1)] }, { coefficient := 1, powers := [(6, 1), (19, 1), (61, 1)] }, { coefficient := 1, powers := [(13, 1), (21, 1), (46, 1), (57, 1)] }, { coefficient := -1, powers := [(13, 1), (26, 1), (46, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (26, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (21, 1), (53, 1), (55, 1), (68, 1)] }, { coefficient := 1, powers := [(2, 1), (21, 1), (55, 1), (62, 1), (68, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (48, 1), (50, 1)] }, { coefficient := 1, powers := [(2, 1), (50, 1), (57, 1)] }, { coefficient := -1, powers := [(5, 1), (38, 1), (48, 1)] }, { coefficient := -1, powers := [(5, 1), (38, 1), (57, 1)] }, { coefficient := 1, powers := [(20, 1), (25, 1), (48, 1)] }, { coefficient := 1, powers := [(20, 1), (25, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [(19, 1), (21, 1), (53, 1), (55, 1)] }, { coefficient := -1, powers := [(19, 1), (21, 1), (55, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (26, 1), (61, 1)] }, { coefficient := 1, powers := [(19, 1), (21, 1), (46, 1), (55, 1)] }, { coefficient := -1, powers := [(20, 1), (26, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (21, 1), (50, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (21, 1), (55, 1), (68, 1)] }],
  [{ coefficient := 2, powers := [(8, 1), (21, 1), (48, 1), (61, 1)] }, { coefficient := -2, powers := [(8, 1), (26, 1), (57, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (20, 1), (39, 1), (57, 1), (60, 1)] }, { coefficient := -1, powers := [(0, 1), (20, 1), (48, 1)] }, { coefficient := -1, powers := [(0, 1), (20, 1), (57, 1)] }, { coefficient := -1, powers := [(3, 1), (20, 1), (26, 1), (57, 1), (60, 1)] }, { coefficient := -1, powers := [(6, 1), (20, 1), (21, 1), (57, 1), (60, 1)] }, { coefficient := -1, powers := [(6, 1), (20, 1), (60, 1)] }, { coefficient := -1, powers := [(20, 1), (21, 1), (57, 1)] }, { coefficient := 1, powers := [(20, 1), (26, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(21, 1), (50, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (48, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (41, 1), (61, 1)] }, { coefficient := 1, powers := [(26, 1), (41, 1), (61, 1)] }, { coefficient := -1, powers := [(26, 1), (50, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (39, 1), (50, 1), (57, 1), (60, 1)] }, { coefficient := -1, powers := [(0, 1), (48, 1), (50, 1)] }, { coefficient := -1, powers := [(0, 1), (50, 1), (57, 1)] }, { coefficient := -1, powers := [(3, 1), (26, 1), (50, 1), (57, 1), (60, 1)] }, { coefficient := -1, powers := [(6, 1), (21, 1), (50, 1), (57, 1), (60, 1)] }, { coefficient := -1, powers := [(6, 1), (50, 1), (60, 1)] }, { coefficient := -1, powers := [(21, 1), (50, 1), (57, 1)] }, { coefficient := 1, powers := [(26, 1), (50, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (25, 1), (48, 1)] }, { coefficient := -1, powers := [(0, 1), (25, 1), (57, 1)] }, { coefficient := -2, powers := [(21, 1), (25, 1), (48, 1)] }, { coefficient := -1, powers := [(21, 1), (25, 1), (57, 1)] }, { coefficient := 1, powers := [(25, 1), (26, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (30, 1), (50, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (19, 1), (26, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (21, 1), (53, 1), (62, 1)] }, { coefficient := -1, powers := [(2, 1), (21, 1), (57, 1), (62, 1)] }, { coefficient := -1, powers := [(2, 1), (48, 1)] }, { coefficient := -1, powers := [(2, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (39, 1), (57, 1), (61, 1)] }, { coefficient := -1, powers := [(3, 1), (26, 1), (57, 1), (61, 1)] }, { coefficient := -1, powers := [(6, 1), (21, 1), (57, 1), (61, 1)] }, { coefficient := -1, powers := [(6, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(26, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(19, 1), (21, 1), (41, 1), (61, 1)] }, { coefficient := -1, powers := [(19, 1), (26, 1), (41, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (13, 1), (39, 1), (57, 1), (60, 1)] }, { coefficient := -1, powers := [(0, 1), (13, 1), (48, 1)] }, { coefficient := -1, powers := [(0, 1), (13, 1), (57, 1)] }, { coefficient := -1, powers := [(3, 1), (13, 1), (26, 1), (57, 1), (60, 1)] }, { coefficient := -1, powers := [(6, 1), (13, 1), (21, 1), (57, 1), (60, 1)] }, { coefficient := -1, powers := [(6, 1), (13, 1), (60, 1)] }, { coefficient := -1, powers := [(13, 1), (21, 1), (57, 1)] }, { coefficient := 1, powers := [(13, 1), (26, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(57, 1)] }],
  [{ coefficient := -1, powers := [(26, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (26, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (39, 1), (57, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (48, 1)] }, { coefficient := 1, powers := [(0, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (26, 1), (57, 1), (60, 1)] }, { coefficient := 1, powers := [(6, 1), (21, 1), (57, 1), (60, 1)] }, { coefficient := 1, powers := [(6, 1), (60, 1)] }, { coefficient := 1, powers := [(21, 1), (57, 1)] }, { coefficient := -1, powers := [(26, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (21, 1), (41, 1), (53, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (21, 1), (41, 1), (57, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (21, 1), (48, 1), (50, 1), (55, 1)] }, { coefficient := 1, powers := [(2, 1), (21, 1), (50, 1), (53, 1), (55, 1)] }, { coefficient := 1, powers := [(2, 1), (21, 1), (50, 1), (55, 1), (57, 1)] }, { coefficient := -1, powers := [(2, 1), (21, 1), (50, 1), (55, 1), (68, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (26, 1), (40, 1), (60, 1)] }, { coefficient := -1, powers := [(0, 1), (26, 1), (43, 1), (57, 1)] }, { coefficient := -1, powers := [(0, 1), (26, 1), (48, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (8, 1), (38, 1), (39, 1), (57, 1), (60, 1)] }, { coefficient := -1, powers := [(0, 1), (8, 1), (38, 1), (48, 1)] }, { coefficient := -1, powers := [(0, 1), (8, 1), (38, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (21, 1), (27, 1), (46, 1), (53, 1), (62, 1)] }, { coefficient := 1, powers := [(2, 1), (21, 1), (27, 1), (46, 1), (57, 1), (62, 1)] }, { coefficient := 1, powers := [(2, 1), (27, 1), (46, 1), (48, 1)] }, { coefficient := 1, powers := [(2, 1), (27, 1), (46, 1), (57, 1)] }, { coefficient := -1, powers := [(3, 1), (8, 1), (26, 1), (38, 1), (57, 1), (60, 1)] }, { coefficient := -1, powers := [(6, 1), (8, 1), (21, 1), (38, 1), (57, 1), (60, 1)] }, { coefficient := -1, powers := [(6, 1), (8, 1), (38, 1), (60, 1)] }, { coefficient := -1, powers := [(8, 1), (21, 1), (38, 1), (57, 1)] }, { coefficient := 1, powers := [(8, 1), (26, 1), (38, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (2, 1), (21, 1), (44, 1), (53, 1), (62, 1)] }, { coefficient := 1, powers := [(0, 1), (2, 1), (21, 1), (44, 1), (57, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 1), (2, 1), (39, 1), (44, 1), (57, 1), (60, 1)] }, { coefficient := -1, powers := [(0, 1), (5, 1), (35, 1), (39, 1), (57, 1), (60, 1)] }, { coefficient := -1, powers := [(0, 1), (5, 1), (35, 1), (48, 1)] }, { coefficient := -1, powers := [(0, 1), (5, 1), (35, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (13, 1), (25, 1), (48, 1)] }, { coefficient := 1, powers := [(0, 1), (13, 1), (25, 1), (57, 1)] }, { coefficient := -1, powers := [(2, 1), (3, 1), (26, 1), (44, 1), (57, 1), (60, 1)] }, { coefficient := -1, powers := [(2, 1), (6, 1), (21, 1), (44, 1), (57, 1), (60, 1)] }, { coefficient := -1, powers := [(2, 1), (6, 1), (44, 1), (60, 1)] }, { coefficient := -1, powers := [(2, 1), (21, 1), (44, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (26, 1), (44, 1), (53, 1)] }, { coefficient := -1, powers := [(3, 1), (5, 1), (26, 1), (35, 1), (57, 1), (60, 1)] }, { coefficient := -1, powers := [(5, 1), (6, 1), (21, 1), (35, 1), (57, 1), (60, 1)] }, { coefficient := -1, powers := [(5, 1), (6, 1), (35, 1), (60, 1)] }, { coefficient := -1, powers := [(5, 1), (21, 1), (35, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (26, 1), (35, 1), (53, 1)] }, { coefficient := 2, powers := [(13, 1), (21, 1), (25, 1), (48, 1)] }, { coefficient := 1, powers := [(13, 1), (21, 1), (25, 1), (57, 1)] }, { coefficient := -1, powers := [(13, 1), (25, 1), (26, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (21, 1), (50, 1), (53, 1), (55, 1)] }, { coefficient := -1, powers := [(2, 1), (21, 1), (50, 1), (55, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (5, 1), (48, 1), (61, 1)] }, { coefficient := -1, powers := [(0, 1), (5, 1), (57, 1), (61, 1)] }, { coefficient := 1, powers := [(0, 1), (13, 1), (39, 1), (50, 1), (57, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (13, 1), (48, 1), (50, 1)] }, { coefficient := 1, powers := [(0, 1), (13, 1), (50, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (13, 1), (26, 1), (50, 1), (57, 1), (60, 1)] }, { coefficient := -1, powers := [(5, 1), (21, 1), (57, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (26, 1), (53, 1), (61, 1)] }, { coefficient := 1, powers := [(6, 1), (13, 1), (21, 1), (50, 1), (57, 1), (60, 1)] }, { coefficient := 1, powers := [(6, 1), (13, 1), (50, 1), (60, 1)] }, { coefficient := 1, powers := [(13, 1), (21, 1), (50, 1), (57, 1)] }, { coefficient := -1, powers := [(13, 1), (26, 1), (50, 1), (53, 1)] }]
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
    ¬ ∀ index : Fin 39,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component19.SelectedLeafB5_6_6_4.selectedHasNoCommonZero

end Krenn.Component19.SelectedLeafB5_6_6_4
