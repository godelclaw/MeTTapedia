import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component19.SelectedLeafB7_4

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "f0e8692dcc36853b96249a28fd08f149a6c6fb958e9abb42445e97d9fd4ed916"
def certificateSHA256 : String := "cc580ee1d309e083e5bae536661a3b431128e7079870c19cfd879370ae57fdf2"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 40 → Fin 669 := ![
  2,
  5,
  10,
  14,
  18,
  20,
  22,
  172,
  173,
  187,
  191,
  196,
  216,
  304,
  316,
  318,
  319,
  402,
  418,
  420,
  422,
  424,
  429,
  439,
  440,
  442,
  463,
  468,
  470,
  565,
  582,
  583,
  646,
  654,
  662,
  663,
  664,
  665,
  667,
  668
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 40 → SparsePoly (Fin 66) := ![
  [{ coefficient := 1, powers := [(5, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (50, 1)] }, { coefficient := 1, powers := [(11, 1), (28, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (55, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (48, 1)] }, { coefficient := 1, powers := [(13, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (21, 1)] }, { coefficient := 1, powers := [(19, 1), (26, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (53, 1)] }, { coefficient := 1, powers := [(25, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (30, 1), (60, 1)] }, { coefficient := 1, powers := [(19, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (61, 1)] }, { coefficient := 1, powers := [(13, 1), (50, 1)] }, { coefficient := 1, powers := [(20, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (49, 1)] }, { coefficient := 1, powers := [(20, 1), (43, 1)] }, { coefficient := 1, powers := [(20, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (55, 1)] }, { coefficient := 1, powers := [(32, 1), (44, 1)] }, { coefficient := 1, powers := [(35, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(31, 1), (54, 1)] }, { coefficient := 1, powers := [(32, 1), (43, 1)] }, { coefficient := 1, powers := [(32, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (26, 1), (43, 1)] }, { coefficient := 1, powers := [(19, 1), (26, 1), (48, 1)] }, { coefficient := 1, powers := [(19, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (48, 1)] }, { coefficient := 1, powers := [(19, 1), (30, 1), (43, 1)] }, { coefficient := 1, powers := [(19, 1), (30, 1), (48, 1)] }, { coefficient := 1, powers := [(19, 1), (31, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (50, 1)] }, { coefficient := 1, powers := [(5, 1), (38, 1)] }, { coefficient := 1, powers := [(19, 1), (30, 1), (50, 1)] }, { coefficient := 1, powers := [(20, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (53, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (53, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (57, 1)] }, { coefficient := 1, powers := [(19, 1), (31, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1)] }, { coefficient := 1, powers := [(13, 1), (32, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (61, 1)] }, { coefficient := 1, powers := [(13, 1), (27, 1), (49, 1)] }, { coefficient := 1, powers := [(13, 1), (58, 1)] }, { coefficient := 1, powers := [(20, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (43, 1)] }, { coefficient := 1, powers := [(19, 1), (48, 1)] }, { coefficient := 1, powers := [(19, 1), (53, 1)] }, { coefficient := 1, powers := [(19, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(31, 1), (43, 1)] }, { coefficient := 1, powers := [(31, 1), (48, 1)] }, { coefficient := 1, powers := [(31, 1), (53, 1)] }, { coefficient := 1, powers := [(31, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (41, 1), (61, 1)] }, { coefficient := 1, powers := [(0, 1), (44, 1), (58, 1)] }, { coefficient := 1, powers := [(0, 1), (50, 1), (55, 1)] }, { coefficient := 1, powers := [(27, 1), (44, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (39, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1)] }, { coefficient := 1, powers := [(19, 1), (30, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (41, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (25, 1), (60, 1)] }, { coefficient := 1, powers := [(19, 1), (25, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (44, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (57, 1)] }, { coefficient := 1, powers := [(13, 1), (25, 1), (57, 1)] }, { coefficient := 1, powers := [(19, 1), (31, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (46, 1), (54, 1)] }, { coefficient := 1, powers := [(25, 1), (58, 1)] }, { coefficient := 1, powers := [(32, 1), (50, 1)] }, { coefficient := 1, powers := [(38, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (48, 1)] }, { coefficient := 1, powers := [(6, 1), (60, 1)] }, { coefficient := 1, powers := [(26, 1), (43, 1)] }, { coefficient := 1, powers := [(26, 1), (48, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (53, 1)] }, { coefficient := 1, powers := [(3, 1), (60, 1)] }, { coefficient := 1, powers := [(21, 1), (53, 1)] }, { coefficient := 1, powers := [(21, 1), (57, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (40, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (43, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (48, 1), (53, 1)] }, { coefficient := 1, powers := [(43, 1)] }, { coefficient := 1, powers := [(48, 1)] }, { coefficient := 1, powers := [(53, 1)] }, { coefficient := 1, powers := [(57, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (40, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (43, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (48, 1), (53, 1)] }, { coefficient := 1, powers := [(19, 1), (31, 1), (43, 1)] }, { coefficient := 1, powers := [(19, 1), (31, 1), (48, 1)] }, { coefficient := 1, powers := [(19, 1), (31, 1), (53, 1)] }, { coefficient := 1, powers := [(19, 1), (31, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (41, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (44, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (50, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (38, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (25, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (50, 1)] }, { coefficient := 1, powers := [(8, 1), (38, 1), (44, 1)] }, { coefficient := 1, powers := [(13, 1), (25, 1), (58, 1)] }, { coefficient := 1, powers := [(13, 1), (32, 1), (50, 1)] }, { coefficient := 1, powers := [(13, 1), (38, 1), (41, 1)] }, { coefficient := 1, powers := [(20, 1), (25, 1), (55, 1)] }, { coefficient := 1, powers := [(20, 1), (32, 1), (44, 1)] }, { coefficient := 1, powers := [(20, 1), (35, 1), (41, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (64, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(43, 1)] }],
  [{ coefficient := 1, powers := [(44, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 40 → SparsePoly (Fin 66) := ![
  [{ coefficient := 2, powers := [(0, 1), (13, 1), (30, 1), (31, 1), (58, 1), (64, 1)] }, { coefficient := 2, powers := [(0, 1), (30, 1), (49, 1), (55, 1)] }, { coefficient := -1, powers := [(3, 1), (32, 1), (61, 1)] }, { coefficient := -1, powers := [(3, 1), (35, 1), (58, 1)] }, { coefficient := -1, powers := [(6, 1), (32, 1), (61, 1)] }, { coefficient := -1, powers := [(6, 1), (35, 1), (58, 1)] }, { coefficient := -2, powers := [(13, 1), (21, 1), (30, 1), (31, 1), (58, 1), (64, 1)] }, { coefficient := -2, powers := [(21, 1), (30, 1), (49, 1), (55, 1)] }, { coefficient := 1, powers := [(32, 1), (39, 1), (61, 1)] }, { coefficient := 1, powers := [(35, 1), (39, 1), (58, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (13, 1), (28, 1), (31, 1), (54, 1), (63, 1)] }, { coefficient := -2, powers := [(13, 1), (21, 1), (28, 1), (31, 1), (54, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (25, 1), (27, 1), (57, 1)] }, { coefficient := 1, powers := [(21, 1), (25, 1), (27, 1), (57, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (2, 1), (22, 1), (48, 1), (50, 1), (63, 1)] }, { coefficient := -2, powers := [(0, 1), (2, 1), (22, 1), (50, 1), (53, 1), (63, 1)] }, { coefficient := -1, powers := [(2, 1), (3, 1), (22, 1), (50, 1), (60, 1), (63, 1)] }, { coefficient := -1, powers := [(2, 1), (6, 1), (22, 1), (50, 1), (60, 1), (63, 1)] }, { coefficient := 2, powers := [(2, 1), (21, 1), (22, 1), (48, 1), (50, 1), (63, 1)] }, { coefficient := 2, powers := [(2, 1), (21, 1), (22, 1), (50, 1), (53, 1), (63, 1)] }, { coefficient := 1, powers := [(2, 1), (22, 1), (39, 1), (50, 1), (60, 1), (63, 1)] }, { coefficient := -1, powers := [(3, 1), (20, 1), (22, 1), (25, 1), (60, 1), (63, 1)] }, { coefficient := -1, powers := [(6, 1), (20, 1), (22, 1), (25, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(20, 1), (22, 1), (25, 1), (39, 1), (60, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (30, 1), (55, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (30, 1), (55, 1), (60, 1)] }, { coefficient := 1, powers := [(6, 1), (30, 1), (55, 1), (60, 1)] }, { coefficient := 1, powers := [(21, 1), (30, 1), (55, 1), (57, 1)] }, { coefficient := -1, powers := [(30, 1), (39, 1), (55, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (19, 1), (50, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (19, 1), (50, 1), (60, 1)] }, { coefficient := 1, powers := [(6, 1), (19, 1), (50, 1), (60, 1)] }, { coefficient := 1, powers := [(19, 1), (21, 1), (50, 1), (57, 1)] }, { coefficient := -1, powers := [(19, 1), (39, 1), (50, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (13, 1), (46, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (13, 1), (46, 1), (60, 1)] }, { coefficient := 1, powers := [(3, 1), (19, 1), (61, 1)] }, { coefficient := 1, powers := [(6, 1), (13, 1), (46, 1), (60, 1)] }, { coefficient := 1, powers := [(6, 1), (19, 1), (61, 1)] }, { coefficient := 1, powers := [(13, 1), (21, 1), (46, 1), (57, 1)] }, { coefficient := -1, powers := [(13, 1), (39, 1), (46, 1), (60, 1)] }, { coefficient := -1, powers := [(19, 1), (39, 1), (61, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (13, 1), (31, 1), (54, 1), (63, 1)] }, { coefficient := 2, powers := [(13, 1), (21, 1), (31, 1), (54, 1), (63, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (2, 1), (48, 1), (50, 1), (63, 1)] }, { coefficient := 2, powers := [(0, 1), (2, 1), (50, 1), (53, 1), (63, 1)] }, { coefficient := 1, powers := [(2, 1), (3, 1), (50, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(2, 1), (6, 1), (50, 1), (60, 1), (63, 1)] }, { coefficient := -2, powers := [(2, 1), (21, 1), (48, 1), (50, 1), (63, 1)] }, { coefficient := -2, powers := [(2, 1), (21, 1), (50, 1), (53, 1), (63, 1)] }, { coefficient := -1, powers := [(2, 1), (39, 1), (50, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(3, 1), (20, 1), (25, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1), (25, 1), (60, 1), (63, 1)] }, { coefficient := -1, powers := [(20, 1), (25, 1), (39, 1), (60, 1), (63, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (32, 1), (50, 1)] }, { coefficient := 2, powers := [(21, 1), (32, 1), (50, 1)] }],
  [{ coefficient := -1, powers := [(24, 1), (48, 1), (64, 1)] }, { coefficient := 1, powers := [(31, 1), (64, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (13, 1), (19, 1), (24, 1), (58, 1), (64, 1)] }, { coefficient := -2, powers := [(0, 1), (13, 1), (58, 1)] }, { coefficient := -2, powers := [(0, 1), (20, 1), (55, 1)] }, { coefficient := 2, powers := [(13, 1), (19, 1), (21, 1), (24, 1), (58, 1), (64, 1)] }, { coefficient := 2, powers := [(13, 1), (21, 1), (58, 1)] }, { coefficient := 2, powers := [(20, 1), (21, 1), (55, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (13, 1), (31, 1), (58, 1), (64, 1)] }, { coefficient := -2, powers := [(0, 1), (49, 1), (55, 1)] }, { coefficient := 2, powers := [(13, 1), (21, 1), (31, 1), (58, 1), (64, 1)] }, { coefficient := 2, powers := [(21, 1), (49, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (32, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (32, 1), (60, 1)] }, { coefficient := 1, powers := [(6, 1), (32, 1), (60, 1)] }, { coefficient := -1, powers := [(21, 1), (32, 1), (57, 1)] }, { coefficient := -1, powers := [(32, 1), (39, 1), (60, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (25, 1), (55, 1)] }, { coefficient := -2, powers := [(21, 1), (25, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (20, 1), (57, 1)] }, { coefficient := -1, powers := [(3, 1), (20, 1), (60, 1)] }, { coefficient := -1, powers := [(6, 1), (20, 1), (60, 1)] }, { coefficient := -1, powers := [(20, 1), (21, 1), (57, 1)] }, { coefficient := 1, powers := [(20, 1), (39, 1), (60, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (13, 1), (50, 1)] }, { coefficient := -2, powers := [(13, 1), (21, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (64, 1)] }, { coefficient := 1, powers := [(30, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(26, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (55, 1), (57, 1)] }, { coefficient := -1, powers := [(3, 1), (55, 1), (60, 1)] }, { coefficient := -1, powers := [(6, 1), (55, 1), (60, 1)] }, { coefficient := -1, powers := [(21, 1), (55, 1), (57, 1)] }, { coefficient := 1, powers := [(39, 1), (55, 1), (60, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (13, 1), (25, 1), (58, 1), (64, 1)] }, { coefficient := -2, powers := [(13, 1), (21, 1), (25, 1), (58, 1), (64, 1)] }, { coefficient := -1, powers := [(21, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (50, 1), (57, 1)] }, { coefficient := -1, powers := [(3, 1), (50, 1), (60, 1)] }, { coefficient := -1, powers := [(6, 1), (50, 1), (60, 1)] }, { coefficient := -1, powers := [(21, 1), (50, 1), (57, 1)] }, { coefficient := 1, powers := [(39, 1), (50, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (25, 1), (57, 1)] }, { coefficient := -1, powers := [(21, 1), (25, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (24, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(0, 2), (19, 1), (41, 1), (61, 1)] }, { coefficient := -1, powers := [(0, 2), (19, 1), (50, 1), (55, 1)] }, { coefficient := -1, powers := [(0, 2), (19, 1), (64, 1)] }, { coefficient := -1, powers := [(0, 1), (19, 1), (21, 1), (41, 1), (61, 1)] }, { coefficient := 1, powers := [(0, 1), (19, 1), (21, 1), (50, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (2, 1), (48, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 1), (2, 1), (53, 1), (62, 1)] }, { coefficient := 1, powers := [(2, 1), (21, 1), (48, 1), (62, 1)] }, { coefficient := 1, powers := [(2, 1), (21, 1), (53, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(64, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (61, 1)] }, { coefficient := -1, powers := [(6, 1), (61, 1)] }, { coefficient := 1, powers := [(39, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (58, 1)] }, { coefficient := -1, powers := [(21, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (13, 1), (57, 1)] }, { coefficient := -1, powers := [(3, 1), (13, 1), (60, 1)] }, { coefficient := -1, powers := [(6, 1), (13, 1), (60, 1)] }, { coefficient := -1, powers := [(13, 1), (21, 1), (57, 1)] }, { coefficient := 1, powers := [(13, 1), (39, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (2, 1), (41, 1), (61, 1)] }, { coefficient := -1, powers := [(0, 1), (2, 1), (50, 1), (55, 1)] }, { coefficient := -1, powers := [(0, 1)] }, { coefficient := -1, powers := [(2, 1), (21, 1), (41, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (21, 1), (50, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(0, 2), (41, 1), (61, 1)] }, { coefficient := 1, powers := [(0, 2), (50, 1), (55, 1)] }, { coefficient := 1, powers := [(0, 2), (64, 1)] }, { coefficient := 1, powers := [(0, 1), (21, 1), (41, 1), (61, 1)] }, { coefficient := -1, powers := [(0, 1), (21, 1), (50, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (60, 1)] }, { coefficient := 1, powers := [(6, 1), (60, 1)] }, { coefficient := 1, powers := [(21, 1), (57, 1)] }, { coefficient := -1, powers := [(39, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (2, 1), (41, 1), (48, 1), (61, 1)] }, { coefficient := 1, powers := [(0, 1), (2, 1), (41, 1), (53, 1), (61, 1)] }, { coefficient := 1, powers := [(0, 1), (2, 1), (48, 1), (50, 1), (55, 1)] }, { coefficient := 1, powers := [(0, 1), (2, 1), (50, 1), (53, 1), (55, 1)] }, { coefficient := -1, powers := [(2, 1), (21, 1), (41, 1), (48, 1), (61, 1)] }, { coefficient := -1, powers := [(2, 1), (21, 1), (41, 1), (53, 1), (61, 1)] }, { coefficient := -1, powers := [(2, 1), (21, 1), (48, 1), (50, 1), (55, 1)] }, { coefficient := -1, powers := [(2, 1), (21, 1), (50, 1), (53, 1), (55, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (2, 1), (48, 1), (50, 1), (55, 1)] }, { coefficient := -2, powers := [(0, 1), (2, 1), (50, 1), (53, 1), (55, 1)] }, { coefficient := 2, powers := [(0, 1), (13, 1), (31, 1), (50, 1), (54, 1)] }, { coefficient := -1, powers := [(2, 1), (3, 1), (50, 1), (55, 1), (60, 1)] }, { coefficient := -1, powers := [(2, 1), (6, 1), (50, 1), (55, 1), (60, 1)] }, { coefficient := 2, powers := [(2, 1), (21, 1), (48, 1), (50, 1), (55, 1)] }, { coefficient := 2, powers := [(2, 1), (21, 1), (50, 1), (53, 1), (55, 1)] }, { coefficient := 1, powers := [(2, 1), (39, 1), (50, 1), (55, 1), (60, 1)] }, { coefficient := -1, powers := [(3, 1), (20, 1), (25, 1), (55, 1), (60, 1)] }, { coefficient := -1, powers := [(6, 1), (20, 1), (25, 1), (55, 1), (60, 1)] }, { coefficient := -2, powers := [(13, 1), (21, 1), (31, 1), (50, 1), (54, 1)] }, { coefficient := 1, powers := [(20, 1), (25, 1), (39, 1), (55, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(0, 2), (40, 1), (60, 1)] }, { coefficient := -1, powers := [(0, 2), (48, 1), (53, 1)] }, { coefficient := -2, powers := [(0, 1), (13, 1), (25, 1), (53, 1), (58, 1)] }, { coefficient := 2, powers := [(13, 1), (21, 1), (25, 1), (53, 1), (58, 1)] }, { coefficient := 1, powers := [(21, 1), (53, 1)] }, { coefficient := 1, powers := [(26, 1), (48, 1)] }, { coefficient := 1, powers := [(39, 1), (60, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := -1, powers := [(0, 2), (2, 1), (57, 1), (64, 1)] }, { coefficient := 1, powers := [(0, 2), (57, 1)] }, { coefficient := -1, powers := [(0, 1), (2, 1), (41, 1), (61, 1)] }, { coefficient := 1, powers := [(0, 1), (2, 1), (50, 1), (55, 1)] }, { coefficient := -2, powers := [(0, 1), (13, 1), (32, 1), (50, 1)] }, { coefficient := -2, powers := [(0, 1), (20, 1), (25, 1), (55, 1)] }, { coefficient := 1, powers := [(0, 1)] }, { coefficient := 1, powers := [(2, 1), (21, 1), (41, 1), (61, 1)] }, { coefficient := -1, powers := [(2, 1), (21, 1), (50, 1), (55, 1)] }, { coefficient := 2, powers := [(13, 1), (21, 1), (32, 1), (50, 1)] }, { coefficient := -1, powers := [(19, 1), (21, 1), (24, 1), (64, 1)] }, { coefficient := -1, powers := [(19, 1), (24, 1), (26, 1), (64, 1)] }, { coefficient := 2, powers := [(20, 1), (21, 1), (25, 1), (55, 1)] }, { coefficient := -1, powers := [(26, 1)] }],
  [{ coefficient := 1, powers := [(0, 2), (2, 1), (48, 1), (58, 1), (62, 1)] }, { coefficient := 1, powers := [(0, 2), (2, 1), (53, 1), (58, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 1), (2, 1), (21, 1), (48, 1), (58, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 1), (2, 1), (21, 1), (53, 1), (58, 1), (62, 1)] }, { coefficient := 1, powers := [(0, 1), (2, 1), (27, 1), (46, 1), (48, 1), (62, 1)] }, { coefficient := 1, powers := [(0, 1), (2, 1), (27, 1), (46, 1), (53, 1), (62, 1)] }, { coefficient := 1, powers := [(0, 1), (8, 1), (38, 1), (57, 1)] }, { coefficient := -1, powers := [(0, 1), (19, 1), (31, 1), (58, 1)] }, { coefficient := -1, powers := [(0, 1), (20, 1), (32, 1), (57, 1)] }, { coefficient := -1, powers := [(2, 1), (3, 1), (58, 1), (60, 1)] }, { coefficient := -1, powers := [(2, 1), (6, 1), (58, 1), (60, 1)] }, { coefficient := -1, powers := [(2, 1), (21, 1), (27, 1), (46, 1), (48, 1), (62, 1)] }, { coefficient := -1, powers := [(2, 1), (21, 1), (27, 1), (46, 1), (53, 1), (62, 1)] }, { coefficient := 1, powers := [(2, 1), (39, 1), (58, 1), (60, 1)] }, { coefficient := -1, powers := [(3, 1), (8, 1), (38, 1), (60, 1)] }, { coefficient := -1, powers := [(3, 1), (20, 1), (32, 1), (60, 1)] }, { coefficient := -1, powers := [(6, 1), (8, 1), (38, 1), (60, 1)] }, { coefficient := -1, powers := [(6, 1), (20, 1), (32, 1), (60, 1)] }, { coefficient := -1, powers := [(8, 1), (21, 1), (38, 1), (57, 1)] }, { coefficient := 1, powers := [(8, 1), (38, 1), (39, 1), (60, 1)] }, { coefficient := 1, powers := [(19, 1), (21, 1), (31, 1), (58, 1)] }, { coefficient := 1, powers := [(20, 1), (21, 1), (32, 1), (57, 1)] }, { coefficient := 1, powers := [(20, 1), (32, 1), (39, 1), (60, 1)] }]
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
    (values : Fin 66 → R) :
    ¬ ∀ index : Fin 40,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component19.SelectedLeafB7_4.selectedHasNoCommonZero

end Krenn.Component19.SelectedLeafB7_4
