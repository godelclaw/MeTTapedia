import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component19.SelectedLeafB5_4

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "0b27adb8ab7c55ccbda57f691242d2e621478f45e40858211472b0efb4e49628"
def certificateSHA256 : String := "707c88a6b3207171e46a22146fe0998776f416e2eb4a5b8111417f9d5d271582"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 45 → Fin 669 := ![
  2,
  10,
  12,
  18,
  20,
  22,
  29,
  187,
  196,
  216,
  220,
  291,
  304,
  316,
  318,
  319,
  359,
  418,
  420,
  422,
  424,
  429,
  439,
  440,
  442,
  468,
  470,
  517,
  565,
  582,
  583,
  604,
  605,
  606,
  607,
  608,
  646,
  654,
  661,
  662,
  663,
  664,
  665,
  667,
  668
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 45 → SparsePoly (Fin 65) := ![
  [{ coefficient := 1, powers := [(5, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(31, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (48, 1)] }, { coefficient := 1, powers := [(13, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (53, 1)] }, { coefficient := 1, powers := [(25, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (30, 1), (60, 1)] }, { coefficient := 1, powers := [(19, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (25, 1), (60, 1)] }, { coefficient := 1, powers := [(25, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (46, 1), (53, 1)] }, { coefficient := 1, powers := [(31, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (61, 1)] }, { coefficient := 1, powers := [(13, 1), (50, 1)] }, { coefficient := 1, powers := [(20, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (49, 1)] }, { coefficient := 1, powers := [(20, 1), (43, 1)] }, { coefficient := 1, powers := [(20, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (55, 1)] }, { coefficient := 1, powers := [(32, 1), (44, 1)] }, { coefficient := 1, powers := [(35, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(31, 1), (54, 1)] }, { coefficient := 1, powers := [(32, 1), (43, 1)] }, { coefficient := 1, powers := [(32, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (25, 1), (60, 1)] }, { coefficient := 1, powers := [(11, 1), (25, 1), (57, 1)] }, { coefficient := 1, powers := [(16, 1), (25, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (48, 1)] }, { coefficient := 1, powers := [(19, 1), (30, 1), (43, 1)] }, { coefficient := 1, powers := [(19, 1), (30, 1), (48, 1)] }, { coefficient := 1, powers := [(19, 1), (31, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (50, 1)] }, { coefficient := 1, powers := [(5, 1), (38, 1)] }, { coefficient := 1, powers := [(19, 1), (30, 1), (50, 1)] }, { coefficient := 1, powers := [(20, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (53, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (53, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (57, 1)] }, { coefficient := 1, powers := [(19, 1), (31, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1)] }, { coefficient := 1, powers := [(13, 1), (32, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (61, 1)] }, { coefficient := 1, powers := [(13, 1), (27, 1), (49, 1)] }, { coefficient := 1, powers := [(13, 1), (58, 1)] }, { coefficient := 1, powers := [(20, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (43, 1)] }, { coefficient := 1, powers := [(19, 1), (48, 1)] }, { coefficient := 1, powers := [(19, 1), (53, 1)] }, { coefficient := 1, powers := [(19, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(31, 1), (43, 1)] }, { coefficient := 1, powers := [(31, 1), (48, 1)] }, { coefficient := 1, powers := [(31, 1), (53, 1)] }, { coefficient := 1, powers := [(31, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (41, 1), (61, 1)] }, { coefficient := 1, powers := [(0, 1), (44, 1), (58, 1)] }, { coefficient := 1, powers := [(0, 1), (50, 1), (55, 1)] }, { coefficient := 1, powers := [(27, 1), (44, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (41, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (25, 1), (60, 1)] }, { coefficient := 1, powers := [(19, 1), (25, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (44, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (57, 1)] }, { coefficient := 1, powers := [(13, 1), (25, 1), (57, 1)] }, { coefficient := 1, powers := [(19, 1), (31, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (21, 1), (60, 1)] }, { coefficient := 1, powers := [(11, 1), (21, 1), (57, 1)] }, { coefficient := 1, powers := [(11, 1)] }, { coefficient := 1, powers := [(16, 1), (21, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (46, 1), (54, 1)] }, { coefficient := 1, powers := [(25, 1), (58, 1)] }, { coefficient := 1, powers := [(32, 1), (50, 1)] }, { coefficient := 1, powers := [(38, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (48, 1)] }, { coefficient := 1, powers := [(6, 1), (60, 1)] }, { coefficient := 1, powers := [(26, 1), (43, 1)] }, { coefficient := 1, powers := [(26, 1), (48, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (53, 1)] }, { coefficient := 1, powers := [(3, 1), (60, 1)] }, { coefficient := 1, powers := [(21, 1), (53, 1)] }, { coefficient := 1, powers := [(21, 1), (57, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1), (48, 1)] }, { coefficient := 1, powers := [(4, 1), (28, 1), (60, 1)] }, { coefficient := 1, powers := [(4, 1), (37, 1)] }, { coefficient := 1, powers := [(11, 1), (28, 1), (48, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1)] }, { coefficient := 1, powers := [(16, 1), (28, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (53, 1)] }, { coefficient := 1, powers := [(7, 1), (22, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (34, 1)] }, { coefficient := 1, powers := [(11, 1), (22, 1), (57, 1)] }, { coefficient := 1, powers := [(11, 1), (29, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (60, 1)] }, { coefficient := 1, powers := [(11, 1), (48, 1)] }, { coefficient := 1, powers := [(11, 1), (57, 1)] }, { coefficient := 1, powers := [(16, 1), (43, 1)] }, { coefficient := 1, powers := [(16, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (53, 1)] }, { coefficient := 1, powers := [(23, 1), (57, 1)] }, { coefficient := 1, powers := [(29, 1), (43, 1)] }, { coefficient := 1, powers := [(29, 1), (48, 1)] }, { coefficient := 1, powers := [(34, 1), (40, 1)] }, { coefficient := 1, powers := [(37, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (39, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1)] }, { coefficient := 1, powers := [(3, 1), (26, 1), (60, 1)] }, { coefficient := 1, powers := [(6, 1), (21, 1), (60, 1)] }, { coefficient := 1, powers := [(21, 1)] }, { coefficient := 1, powers := [(26, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (40, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (43, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (48, 1), (53, 1)] }, { coefficient := 1, powers := [(43, 1)] }, { coefficient := 1, powers := [(48, 1)] }, { coefficient := 1, powers := [(53, 1)] }, { coefficient := 1, powers := [(57, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (40, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (43, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (48, 1), (53, 1)] }, { coefficient := 1, powers := [(19, 1), (31, 1), (43, 1)] }, { coefficient := 1, powers := [(19, 1), (31, 1), (48, 1)] }, { coefficient := 1, powers := [(19, 1), (31, 1), (53, 1)] }, { coefficient := 1, powers := [(19, 1), (31, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (40, 1), (60, 1)] }, { coefficient := 1, powers := [(1, 1), (43, 1), (57, 1)] }, { coefficient := 1, powers := [(1, 1), (48, 1), (53, 1)] }, { coefficient := 1, powers := [(4, 1), (29, 1), (60, 1)] }, { coefficient := 1, powers := [(4, 1), (34, 1), (57, 1)] }, { coefficient := 1, powers := [(4, 1), (37, 1), (53, 1)] }, { coefficient := 1, powers := [(7, 1), (23, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (34, 1), (48, 1)] }, { coefficient := 1, powers := [(7, 1), (37, 1), (43, 1)] }, { coefficient := 1, powers := [(11, 1), (23, 1), (57, 1)] }, { coefficient := 1, powers := [(11, 1), (29, 1), (48, 1)] }, { coefficient := 1, powers := [(11, 1), (37, 1), (40, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1), (53, 1)] }, { coefficient := 1, powers := [(16, 1), (29, 1), (43, 1)] }, { coefficient := 1, powers := [(16, 1), (34, 1), (40, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (41, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (44, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (50, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (38, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (25, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (50, 1)] }, { coefficient := 1, powers := [(8, 1), (38, 1), (44, 1)] }, { coefficient := 1, powers := [(13, 1), (25, 1), (58, 1)] }, { coefficient := 1, powers := [(13, 1), (32, 1), (50, 1)] }, { coefficient := 1, powers := [(13, 1), (38, 1), (41, 1)] }, { coefficient := 1, powers := [(20, 1), (25, 1), (55, 1)] }, { coefficient := 1, powers := [(20, 1), (32, 1), (44, 1)] }, { coefficient := 1, powers := [(20, 1), (35, 1), (41, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(43, 1)] }],
  [{ coefficient := 1, powers := [(44, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 45 → SparsePoly (Fin 65) := ![
  [{ coefficient := 2, powers := [(0, 1), (30, 1), (49, 1), (55, 1)] }, { coefficient := -1, powers := [(3, 1), (32, 1), (61, 1)] }, { coefficient := -1, powers := [(3, 1), (35, 1), (58, 1)] }, { coefficient := -1, powers := [(3, 1), (38, 1), (55, 1)] }, { coefficient := -1, powers := [(6, 1), (32, 1), (61, 1)] }, { coefficient := -1, powers := [(6, 1), (35, 1), (58, 1)] }, { coefficient := -1, powers := [(6, 1), (38, 1), (55, 1)] }, { coefficient := 2, powers := [(26, 1), (30, 1), (49, 1), (55, 1)] }, { coefficient := 1, powers := [(32, 1), (39, 1), (61, 1)] }, { coefficient := 1, powers := [(35, 1), (39, 1), (58, 1)] }, { coefficient := 1, powers := [(38, 1), (39, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (25, 1), (27, 1), (57, 1)] }, { coefficient := -1, powers := [(25, 1), (26, 1), (27, 1), (57, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (13, 1), (23, 1), (53, 2), (58, 1)] }, { coefficient := 2, powers := [(0, 1), (13, 1), (34, 1), (40, 1), (53, 1), (58, 1)] }, { coefficient := -2, powers := [(13, 1), (23, 1), (26, 1), (53, 2), (58, 1)] }, { coefficient := 2, powers := [(13, 1), (26, 1), (34, 1), (40, 1), (53, 1), (58, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (30, 1), (48, 1), (55, 1)] }, { coefficient := -1, powers := [(0, 1), (30, 1), (55, 1), (57, 1)] }, { coefficient := -2, powers := [(0, 1), (31, 1), (55, 1)] }, { coefficient := -2, powers := [(26, 1), (30, 1), (48, 1), (55, 1)] }, { coefficient := -1, powers := [(26, 1), (30, 1), (55, 1), (57, 1)] }, { coefficient := -2, powers := [(26, 1), (31, 1), (55, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (19, 1), (48, 1), (50, 1)] }, { coefficient := -1, powers := [(0, 1), (19, 1), (50, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (19, 1), (50, 1), (60, 1)] }, { coefficient := 1, powers := [(6, 1), (19, 1), (50, 1), (60, 1)] }, { coefficient := 2, powers := [(19, 1), (26, 1), (48, 1), (50, 1)] }, { coefficient := -1, powers := [(19, 1), (26, 1), (50, 1), (57, 1)] }, { coefficient := -1, powers := [(19, 1), (39, 1), (50, 1), (60, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (13, 1), (46, 1), (53, 1)] }, { coefficient := -1, powers := [(0, 1), (13, 1), (46, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (13, 1), (46, 1), (60, 1)] }, { coefficient := 1, powers := [(3, 1), (19, 1), (61, 1)] }, { coefficient := 1, powers := [(6, 1), (13, 1), (46, 1), (60, 1)] }, { coefficient := 1, powers := [(6, 1), (19, 1), (61, 1)] }, { coefficient := 2, powers := [(13, 1), (26, 1), (46, 1), (53, 1)] }, { coefficient := -1, powers := [(13, 1), (26, 1), (46, 1), (57, 1)] }, { coefficient := -1, powers := [(13, 1), (39, 1), (46, 1), (60, 1)] }, { coefficient := -1, powers := [(19, 1), (39, 1), (61, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (19, 1), (50, 1)] }, { coefficient := -2, powers := [(19, 1), (26, 1), (50, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (32, 1), (50, 1)] }, { coefficient := -2, powers := [(26, 1), (32, 1), (50, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (4, 1), (13, 1), (34, 1), (53, 1), (58, 1)] }, { coefficient := -2, powers := [(0, 1), (11, 1), (13, 1), (23, 1), (53, 1), (58, 1)] }, { coefficient := -2, powers := [(0, 1), (13, 1), (58, 1)] }, { coefficient := -2, powers := [(0, 1), (20, 1), (55, 1)] }, { coefficient := 2, powers := [(4, 1), (13, 1), (26, 1), (34, 1), (53, 1), (58, 1)] }, { coefficient := -2, powers := [(11, 1), (13, 1), (23, 1), (26, 1), (53, 1), (58, 1)] }, { coefficient := -2, powers := [(13, 1), (26, 1), (58, 1)] }, { coefficient := -2, powers := [(20, 1), (26, 1), (55, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (49, 1), (55, 1)] }, { coefficient := -2, powers := [(26, 1), (49, 1), (55, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (4, 1), (13, 1), (34, 1), (53, 2), (58, 1)] }, { coefficient := -2, powers := [(4, 1), (13, 1), (26, 1), (34, 1), (53, 2), (58, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (13, 1), (54, 1)] }, { coefficient := -2, powers := [(13, 1), (26, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (32, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (32, 1), (60, 1)] }, { coefficient := 1, powers := [(6, 1), (32, 1), (60, 1)] }, { coefficient := 1, powers := [(26, 1), (32, 1), (57, 1)] }, { coefficient := -1, powers := [(32, 1), (39, 1), (60, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (25, 1), (55, 1)] }, { coefficient := 2, powers := [(25, 1), (26, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (20, 1), (57, 1)] }, { coefficient := -1, powers := [(3, 1), (20, 1), (60, 1)] }, { coefficient := -1, powers := [(6, 1), (20, 1), (60, 1)] }, { coefficient := 1, powers := [(20, 1), (26, 1), (57, 1)] }, { coefficient := 1, powers := [(20, 1), (39, 1), (60, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (13, 1), (50, 1)] }, { coefficient := 2, powers := [(13, 1), (26, 1), (50, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (6, 1), (13, 1), (21, 1), (34, 1), (48, 1), (53, 2), (58, 1)] }, { coefficient := -2, powers := [(0, 1), (6, 1), (13, 1), (34, 1), (53, 2), (58, 1)] }, { coefficient := 4, powers := [(0, 1), (13, 1), (21, 1), (29, 1), (48, 1), (53, 1), (58, 1)] }, { coefficient := 2, powers := [(0, 1), (13, 1), (21, 1), (34, 1), (40, 1), (53, 1), (58, 1)] }, { coefficient := -2, powers := [(0, 1), (13, 1), (22, 1), (48, 1), (53, 1), (58, 1)] }, { coefficient := 2, powers := [(0, 1), (13, 1), (23, 1), (53, 1), (58, 1)] }, { coefficient := 2, powers := [(0, 1), (13, 1), (28, 1), (53, 2), (58, 1)] }, { coefficient := -2, powers := [(0, 1), (13, 1), (29, 1), (53, 1), (58, 1)] }, { coefficient := 2, powers := [(6, 1), (13, 1), (21, 1), (26, 1), (34, 1), (48, 1), (53, 2), (58, 1)] }, { coefficient := -2, powers := [(6, 1), (13, 1), (26, 1), (34, 1), (53, 2), (58, 1)] }, { coefficient := 4, powers := [(13, 1), (21, 1), (26, 1), (29, 1), (48, 1), (53, 1), (58, 1)] }, { coefficient := 2, powers := [(13, 1), (21, 1), (26, 1), (34, 1), (40, 1), (53, 1), (58, 1)] }, { coefficient := -2, powers := [(13, 1), (22, 1), (26, 1), (48, 1), (53, 1), (58, 1)] }, { coefficient := 2, powers := [(13, 1), (23, 1), (26, 1), (53, 1), (58, 1)] }, { coefficient := 2, powers := [(13, 1), (26, 1), (28, 1), (53, 2), (58, 1)] }, { coefficient := -2, powers := [(13, 1), (26, 1), (29, 1), (53, 1), (58, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (50, 1), (55, 1)] }, { coefficient := 2, powers := [(26, 1), (50, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (55, 1), (57, 1)] }, { coefficient := 1, powers := [(26, 1), (55, 1), (57, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (50, 1), (55, 1)] }, { coefficient := 2, powers := [(26, 1), (50, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (50, 1), (57, 1)] }, { coefficient := -1, powers := [(3, 1), (50, 1), (60, 1)] }, { coefficient := -1, powers := [(6, 1), (50, 1), (60, 1)] }, { coefficient := 1, powers := [(26, 1), (50, 1), (57, 1)] }, { coefficient := 1, powers := [(39, 1), (50, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (25, 1), (57, 1)] }, { coefficient := 1, powers := [(25, 1), (26, 1), (57, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (24, 1), (50, 1), (55, 1)] }, { coefficient := -2, powers := [(24, 1), (26, 1), (50, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(0, 2), (19, 1), (41, 1), (61, 1)] }, { coefficient := -1, powers := [(0, 2), (19, 1), (50, 1), (55, 1)] }, { coefficient := -1, powers := [(0, 2), (19, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (19, 1), (21, 1), (63, 1)] }, { coefficient := 1, powers := [(0, 1), (19, 1), (26, 1), (41, 1), (61, 1)] }, { coefficient := -1, powers := [(0, 1), (19, 1), (26, 1), (50, 1), (55, 1)] }, { coefficient := -1, powers := [(0, 1), (19, 1), (26, 1), (63, 1)] }, { coefficient := -1, powers := [(19, 1), (21, 1), (26, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (2, 1), (48, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 1), (2, 1), (53, 1), (62, 1)] }, { coefficient := -1, powers := [(2, 1), (26, 1), (48, 1), (62, 1)] }, { coefficient := -1, powers := [(2, 1), (26, 1), (53, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (61, 1)] }, { coefficient := -1, powers := [(6, 1), (61, 1)] }, { coefficient := 1, powers := [(39, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (58, 1)] }, { coefficient := 1, powers := [(26, 1), (58, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (6, 1), (13, 1), (25, 1), (34, 1), (48, 1), (53, 2), (58, 1)] }, { coefficient := -4, powers := [(0, 1), (13, 1), (25, 1), (29, 1), (48, 1), (53, 1), (58, 1)] }, { coefficient := -2, powers := [(0, 1), (13, 1), (25, 1), (34, 1), (40, 1), (53, 1), (58, 1)] }, { coefficient := -2, powers := [(6, 1), (13, 1), (25, 1), (26, 1), (34, 1), (48, 1), (53, 2), (58, 1)] }, { coefficient := -4, powers := [(13, 1), (25, 1), (26, 1), (29, 1), (48, 1), (53, 1), (58, 1)] }, { coefficient := -2, powers := [(13, 1), (25, 1), (26, 1), (34, 1), (40, 1), (53, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (13, 1), (57, 1)] }, { coefficient := -1, powers := [(3, 1), (13, 1), (60, 1)] }, { coefficient := -1, powers := [(6, 1), (13, 1), (60, 1)] }, { coefficient := 1, powers := [(13, 1), (26, 1), (57, 1)] }, { coefficient := 1, powers := [(13, 1), (39, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (62, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(26, 1), (62, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 2, powers := [(0, 1), (13, 1), (25, 1), (53, 2), (58, 1)] }, { coefficient := 2, powers := [(13, 1), (25, 1), (26, 1), (53, 2), (58, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (13, 1), (25, 1), (48, 1), (53, 1), (58, 1)] }, { coefficient := 2, powers := [(13, 1), (25, 1), (26, 1), (48, 1), (53, 1), (58, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (6, 1), (13, 1), (25, 1), (34, 1), (53, 2), (58, 1)] }, { coefficient := -2, powers := [(0, 1), (13, 1), (25, 1), (28, 1), (53, 2), (58, 1)] }, { coefficient := 2, powers := [(0, 1), (13, 1), (25, 1), (29, 1), (53, 1), (58, 1)] }, { coefficient := 2, powers := [(6, 1), (13, 1), (25, 1), (26, 1), (34, 1), (53, 2), (58, 1)] }, { coefficient := -2, powers := [(13, 1), (25, 1), (26, 1), (28, 1), (53, 2), (58, 1)] }, { coefficient := 2, powers := [(13, 1), (25, 1), (26, 1), (29, 1), (53, 1), (58, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (11, 1), (13, 1), (25, 1), (53, 1), (58, 1)] }, { coefficient := 2, powers := [(11, 1), (13, 1), (25, 1), (26, 1), (53, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(62, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (2, 1), (41, 1), (61, 1)] }, { coefficient := -1, powers := [(0, 1), (2, 1), (50, 1), (55, 1)] }, { coefficient := -1, powers := [(0, 1)] }, { coefficient := 1, powers := [(2, 1), (26, 1), (41, 1), (61, 1)] }, { coefficient := -1, powers := [(2, 1), (26, 1), (50, 1), (55, 1)] }, { coefficient := -1, powers := [(21, 1), (26, 1), (62, 1)] }, { coefficient := -1, powers := [(21, 1)] }, { coefficient := -1, powers := [(26, 1)] }],
  [{ coefficient := -1, powers := [(0, 2), (41, 1), (61, 1)] }, { coefficient := 1, powers := [(0, 2), (50, 1), (55, 1)] }, { coefficient := 1, powers := [(0, 2), (63, 1)] }, { coefficient := 1, powers := [(0, 1), (21, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (26, 1), (41, 1), (61, 1)] }, { coefficient := 1, powers := [(0, 1), (26, 1), (50, 1), (55, 1)] }, { coefficient := 1, powers := [(0, 1), (26, 1), (63, 1)] }, { coefficient := 1, powers := [(21, 1), (26, 1), (63, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (13, 1), (25, 1), (53, 1), (58, 1)] }, { coefficient := -2, powers := [(13, 1), (25, 1), (26, 1), (53, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (60, 1)] }, { coefficient := 1, powers := [(6, 1), (60, 1)] }, { coefficient := -1, powers := [(26, 1), (57, 1)] }, { coefficient := -1, powers := [(39, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (2, 1), (41, 1), (48, 1), (61, 1)] }, { coefficient := 1, powers := [(0, 1), (2, 1), (41, 1), (53, 1), (61, 1)] }, { coefficient := 1, powers := [(0, 1), (2, 1), (48, 1), (50, 1), (55, 1)] }, { coefficient := 1, powers := [(0, 1), (2, 1), (50, 1), (53, 1), (55, 1)] }, { coefficient := 1, powers := [(2, 1), (26, 1), (41, 1), (48, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (26, 1), (41, 1), (53, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (26, 1), (48, 1), (50, 1), (55, 1)] }, { coefficient := 1, powers := [(2, 1), (26, 1), (50, 1), (53, 1), (55, 1)] }, { coefficient := 1, powers := [(21, 1), (26, 1), (40, 1), (60, 1)] }, { coefficient := 1, powers := [(21, 1), (26, 1), (48, 1), (53, 1)] }, { coefficient := -1, powers := [(21, 1), (48, 1)] }, { coefficient := -1, powers := [(26, 1), (53, 1)] }, { coefficient := 1, powers := [(39, 1), (60, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 2, powers := [(0, 1), (13, 1), (25, 1), (40, 1), (53, 1), (58, 1), (60, 1)] }, { coefficient := -2, powers := [(0, 1), (13, 1), (25, 1), (48, 1), (53, 2), (58, 1)] }, { coefficient := 2, powers := [(13, 1), (25, 1), (26, 1), (40, 1), (53, 1), (58, 1), (60, 1)] }, { coefficient := -2, powers := [(13, 1), (25, 1), (26, 1), (48, 1), (53, 2), (58, 1)] }],
  [{ coefficient := -1, powers := [(0, 2), (40, 1), (60, 1)] }, { coefficient := -1, powers := [(0, 2), (48, 1), (53, 1)] }, { coefficient := -1, powers := [(0, 1), (21, 1), (40, 1), (60, 1)] }, { coefficient := -1, powers := [(0, 1), (21, 1), (48, 1), (53, 1)] }, { coefficient := -1, powers := [(0, 1), (26, 1), (40, 1), (60, 1)] }, { coefficient := -1, powers := [(0, 1), (26, 1), (48, 1), (53, 1)] }, { coefficient := -1, powers := [(21, 1), (26, 1), (40, 1), (60, 1)] }, { coefficient := -1, powers := [(21, 1), (26, 1), (48, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(0, 2), (2, 1), (57, 1), (63, 1)] }, { coefficient := 1, powers := [(0, 2), (57, 1)] }, { coefficient := 2, powers := [(0, 1), (1, 1), (13, 1), (25, 1), (53, 1), (57, 1), (58, 1)] }, { coefficient := -1, powers := [(0, 1), (2, 1), (21, 1), (57, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (2, 1), (26, 1), (57, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (2, 1), (41, 1), (61, 1)] }, { coefficient := 1, powers := [(0, 1), (2, 1), (50, 1), (55, 1)] }, { coefficient := -2, powers := [(0, 1), (6, 1), (13, 1), (16, 1), (25, 1), (34, 1), (53, 2), (58, 1)] }, { coefficient := 2, powers := [(0, 1), (7, 1), (13, 1), (25, 1), (37, 1), (53, 1), (58, 1)] }, { coefficient := -2, powers := [(0, 1), (11, 1), (13, 1), (25, 1), (29, 1), (53, 1), (58, 1)] }, { coefficient := -2, powers := [(0, 1), (13, 1), (32, 1), (50, 1)] }, { coefficient := 2, powers := [(0, 1), (19, 1), (24, 1), (50, 1), (55, 1)] }, { coefficient := -2, powers := [(0, 1), (19, 1), (30, 1), (50, 1), (55, 1)] }, { coefficient := -2, powers := [(0, 1), (20, 1), (25, 1), (55, 1)] }, { coefficient := 1, powers := [(0, 1), (21, 1), (26, 1), (57, 1), (62, 1)] }, { coefficient := 1, powers := [(0, 1), (21, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (26, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1)] }, { coefficient := 2, powers := [(1, 1), (13, 1), (25, 1), (26, 1), (53, 1), (57, 1), (58, 1)] }, { coefficient := -1, powers := [(2, 1), (21, 1), (26, 1), (57, 1), (63, 1)] }, { coefficient := -1, powers := [(2, 1), (26, 1), (41, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (26, 1), (50, 1), (55, 1)] }, { coefficient := -2, powers := [(6, 1), (13, 1), (16, 1), (25, 1), (26, 1), (34, 1), (53, 2), (58, 1)] }, { coefficient := 2, powers := [(7, 1), (13, 1), (25, 1), (26, 1), (37, 1), (53, 1), (58, 1)] }, { coefficient := -2, powers := [(11, 1), (13, 1), (25, 1), (26, 1), (29, 1), (53, 1), (58, 1)] }, { coefficient := -2, powers := [(13, 1), (26, 1), (32, 1), (50, 1)] }, { coefficient := 2, powers := [(19, 1), (24, 1), (26, 1), (50, 1), (55, 1)] }, { coefficient := -2, powers := [(19, 1), (26, 1), (30, 1), (50, 1), (55, 1)] }, { coefficient := -2, powers := [(20, 1), (25, 1), (26, 1), (55, 1)] }, { coefficient := 1, powers := [(21, 1)] }],
  [{ coefficient := 1, powers := [(0, 2), (2, 1), (48, 1), (58, 1), (62, 1)] }, { coefficient := 1, powers := [(0, 2), (2, 1), (53, 1), (58, 1), (62, 1)] }, { coefficient := 1, powers := [(0, 1), (2, 1), (26, 1), (48, 1), (58, 1), (62, 1)] }, { coefficient := 1, powers := [(0, 1), (2, 1), (26, 1), (53, 1), (58, 1), (62, 1)] }, { coefficient := 1, powers := [(0, 1), (2, 1), (27, 1), (46, 1), (48, 1), (62, 1)] }, { coefficient := 1, powers := [(0, 1), (2, 1), (27, 1), (46, 1), (53, 1), (62, 1)] }, { coefficient := 1, powers := [(0, 1), (8, 1), (38, 1), (57, 1)] }, { coefficient := -1, powers := [(0, 1), (19, 1), (31, 1), (58, 1)] }, { coefficient := -1, powers := [(0, 1), (20, 1), (32, 1), (57, 1)] }, { coefficient := -1, powers := [(2, 1), (3, 1), (58, 1), (60, 1)] }, { coefficient := -1, powers := [(2, 1), (6, 1), (58, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (26, 1), (27, 1), (46, 1), (48, 1), (62, 1)] }, { coefficient := 1, powers := [(2, 1), (26, 1), (27, 1), (46, 1), (53, 1), (62, 1)] }, { coefficient := 1, powers := [(2, 1), (39, 1), (58, 1), (60, 1)] }, { coefficient := -1, powers := [(3, 1), (8, 1), (38, 1), (60, 1)] }, { coefficient := -1, powers := [(3, 1), (20, 1), (32, 1), (60, 1)] }, { coefficient := -1, powers := [(6, 1), (8, 1), (38, 1), (60, 1)] }, { coefficient := -1, powers := [(6, 1), (20, 1), (32, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (26, 1), (38, 1), (57, 1)] }, { coefficient := 1, powers := [(8, 1), (38, 1), (39, 1), (60, 1)] }, { coefficient := -1, powers := [(19, 1), (26, 1), (31, 1), (58, 1)] }, { coefficient := -1, powers := [(20, 1), (26, 1), (32, 1), (57, 1)] }, { coefficient := 1, powers := [(20, 1), (32, 1), (39, 1), (60, 1)] }]
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
    ¬ ∀ index : Fin 45,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component19.SelectedLeafB5_4.selectedHasNoCommonZero

end Krenn.Component19.SelectedLeafB5_4
