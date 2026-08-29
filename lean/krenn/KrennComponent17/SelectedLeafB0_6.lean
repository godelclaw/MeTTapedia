import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component17.SelectedLeafB0_6

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "0fdc23ae872cd60b1efca9676d6ee7cf9a0b956fdbbac60b62cb0827c82dedeb"
def certificateSHA256 : String := "4ca523a74a0b9de84b74cd909f30abf5927d619ae5717168ea7378952dd5a308"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 48 → Fin 608 := ![
  5,
  6,
  7,
  9,
  14,
  17,
  18,
  30,
  32,
  41,
  202,
  210,
  211,
  212,
  214,
  281,
  300,
  306,
  308,
  309,
  311,
  325,
  326,
  372,
  374,
  423,
  434,
  438,
  441,
  454,
  462,
  470,
  541,
  543,
  549,
  550,
  558,
  569,
  570,
  572,
  577,
  593,
  600,
  601,
  602,
  603,
  604,
  607
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 48 → SparsePoly (Fin 61) := ![
  [{ coefficient := 1, powers := [(3, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (34, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (31, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(32, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (44, 1)] }, { coefficient := 1, powers := [(13, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (43, 1)] }, { coefficient := 1, powers := [(27, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (51, 1)] }, { coefficient := 1, powers := [(29, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(31, 1), (38, 1)] }, { coefficient := 1, powers := [(34, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(52, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (19, 1), (54, 1)] }, { coefficient := 1, powers := [(13, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (43, 1), (51, 1)] }, { coefficient := 1, powers := [(21, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1)] }, { coefficient := 1, powers := [(19, 1), (43, 1)] }, { coefficient := 1, powers := [(24, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (44, 1)] }, { coefficient := 1, powers := [(4, 1), (34, 1)] }, { coefficient := 1, powers := [(15, 1), (21, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (50, 1)] }, { coefficient := 1, powers := [(7, 1), (31, 1)] }, { coefficient := 1, powers := [(11, 1), (26, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (58, 1)] }, { coefficient := 1, powers := [(13, 1), (47, 1)] }, { coefficient := 1, powers := [(18, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (52, 1)] }, { coefficient := 1, powers := [(29, 1), (41, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(28, 1), (51, 1)] }, { coefficient := 1, powers := [(29, 1), (40, 1)] }, { coefficient := 1, powers := [(29, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (31, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1), (47, 1)] }, { coefficient := 1, powers := [(18, 1), (31, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (34, 1), (52, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (41, 1)] }, { coefficient := 1, powers := [(13, 1), (34, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1)] }, { coefficient := 1, powers := [(24, 1), (40, 1), (43, 1)] }, { coefficient := 1, powers := [(24, 1), (45, 1)] }, { coefficient := 1, powers := [(43, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (52, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1)] }, { coefficient := 1, powers := [(13, 1), (29, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (57, 1)] }, { coefficient := 1, powers := [(17, 1), (20, 1), (50, 1)] }, { coefficient := 1, powers := [(17, 1), (20, 1), (54, 1)] }, { coefficient := 1, powers := [(17, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (58, 1)] }, { coefficient := 1, powers := [(13, 1), (25, 1), (45, 1)] }, { coefficient := 1, powers := [(13, 1), (55, 1)] }, { coefficient := 1, powers := [(18, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1), (51, 1)] }, { coefficient := 1, powers := [(19, 1), (43, 1), (51, 1)] }, { coefficient := 1, powers := [(19, 1), (55, 1)] }, { coefficient := 1, powers := [(25, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1), (50, 1)] }, { coefficient := 1, powers := [(20, 1), (50, 1)] }, { coefficient := 1, powers := [(20, 1), (54, 1)] }, { coefficient := 1, powers := [(46, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (37, 1), (58, 1)] }, { coefficient := 1, powers := [(13, 1), (28, 1), (45, 1)] }, { coefficient := 1, powers := [(13, 1), (35, 1), (37, 1)] }, { coefficient := 1, powers := [(18, 1), (32, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (43, 1), (51, 1)] }, { coefficient := 1, powers := [(23, 1), (55, 1)] }, { coefficient := 1, powers := [(29, 1), (47, 1)] }, { coefficient := 1, powers := [(35, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(28, 1), (43, 1), (51, 1)] }, { coefficient := 1, powers := [(28, 1), (55, 1)] }, { coefficient := 1, powers := [(29, 1), (40, 1), (43, 1)] }, { coefficient := 1, powers := [(29, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1)] }, { coefficient := 1, powers := [(6, 1), (57, 1)] }, { coefficient := 1, powers := [(24, 1), (40, 1)] }, { coefficient := 1, powers := [(24, 1), (44, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (50, 1)] }, { coefficient := 1, powers := [(3, 1), (57, 1)] }, { coefficient := 1, powers := [(19, 1), (50, 1)] }, { coefficient := 1, powers := [(19, 1), (54, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (41, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (54, 1)] }, { coefficient := 1, powers := [(13, 1), (23, 1), (54, 1)] }, { coefficient := 1, powers := [(13, 1), (28, 1), (46, 1)] }, { coefficient := 1, powers := [(17, 1), (28, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (57, 1)] }, { coefficient := 1, powers := [(7, 1), (57, 1)] }, { coefficient := 1, powers := [(11, 1), (44, 1)] }, { coefficient := 1, powers := [(11, 1), (54, 1)] }, { coefficient := 1, powers := [(15, 1), (40, 1)] }, { coefficient := 1, powers := [(15, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (50, 1)] }, { coefficient := 1, powers := [(21, 1), (54, 1)] }, { coefficient := 1, powers := [(26, 1), (40, 1)] }, { coefficient := 1, powers := [(26, 1), (44, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (40, 1), (55, 1)] }, { coefficient := 1, powers := [(0, 1), (45, 1), (51, 1)] }, { coefficient := 1, powers := [(25, 1), (40, 1), (43, 1)] }, { coefficient := 1, powers := [(25, 1), (45, 1)] }, { coefficient := 1, powers := [(43, 1), (51, 1)] }, { coefficient := 1, powers := [(55, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (46, 1), (51, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (57, 1)] }, { coefficient := 1, powers := [(8, 1), (23, 1), (57, 1)] }, { coefficient := 1, powers := [(17, 1), (23, 1), (51, 1)] }, { coefficient := 1, powers := [(17, 1), (29, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (37, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (40, 1), (54, 1)] }, { coefficient := 1, powers := [(0, 1), (44, 1), (50, 1)] }, { coefficient := 1, powers := [(40, 1)] }, { coefficient := 1, powers := [(44, 1)] }, { coefficient := 1, powers := [(50, 1)] }, { coefficient := 1, powers := [(54, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (37, 1), (57, 1)] }, { coefficient := 1, powers := [(1, 1), (40, 1), (54, 1)] }, { coefficient := 1, powers := [(1, 1), (44, 1), (50, 1)] }, { coefficient := 1, powers := [(4, 1), (26, 1), (57, 1)] }, { coefficient := 1, powers := [(4, 1), (31, 1), (54, 1)] }, { coefficient := 1, powers := [(4, 1), (34, 1), (50, 1)] }, { coefficient := 1, powers := [(7, 1), (21, 1), (57, 1)] }, { coefficient := 1, powers := [(7, 1), (31, 1), (44, 1)] }, { coefficient := 1, powers := [(7, 1), (34, 1), (40, 1)] }, { coefficient := 1, powers := [(11, 1), (21, 1), (54, 1)] }, { coefficient := 1, powers := [(11, 1), (26, 1), (44, 1)] }, { coefficient := 1, powers := [(11, 1), (34, 1), (37, 1)] }, { coefficient := 1, powers := [(15, 1), (21, 1), (50, 1)] }, { coefficient := 1, powers := [(15, 1), (26, 1), (40, 1)] }, { coefficient := 1, powers := [(15, 1), (31, 1), (37, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (41, 1), (55, 1)] }, { coefficient := 1, powers := [(2, 1), (47, 1), (52, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (52, 1)] }, { coefficient := 1, powers := [(8, 1), (23, 1), (58, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (47, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(13, 1), (23, 1), (55, 1)] }, { coefficient := 1, powers := [(13, 1), (29, 1), (47, 1)] }, { coefficient := 1, powers := [(13, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (52, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (41, 1)] }, { coefficient := 1, powers := [(18, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1)] }],
  [{ coefficient := 1, powers := [(1, 1)] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(41, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 48 → SparsePoly (Fin 61) := ![
  [{ coefficient := 2, powers := [(8, 1), (15, 1), (23, 1), (26, 1), (54, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (29, 1), (50, 1), (58, 1)] }, { coefficient := 1, powers := [(4, 1), (29, 1), (54, 1), (58, 1)] }, { coefficient := 1, powers := [(4, 1), (32, 1), (50, 1), (55, 1)] }, { coefficient := 1, powers := [(4, 1), (32, 1), (54, 1), (55, 1)] }, { coefficient := -1, powers := [(4, 1), (35, 1), (50, 1), (52, 1)] }, { coefficient := -1, powers := [(4, 1), (35, 1), (52, 1), (54, 1)] }, { coefficient := -1, powers := [(7, 1), (29, 1), (44, 1), (58, 1)] }, { coefficient := -1, powers := [(7, 1), (29, 1), (50, 1), (58, 1)] }, { coefficient := -1, powers := [(7, 1), (29, 1), (54, 1), (58, 1)] }, { coefficient := -1, powers := [(7, 1), (32, 1), (44, 1), (55, 1)] }, { coefficient := -1, powers := [(7, 1), (32, 1), (50, 1), (55, 1)] }, { coefficient := -1, powers := [(7, 1), (32, 1), (54, 1), (55, 1)] }, { coefficient := 1, powers := [(7, 1), (35, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(7, 1), (35, 1), (50, 1), (52, 1)] }, { coefficient := 1, powers := [(7, 1), (35, 1), (52, 1), (54, 1)] }],
  [{ coefficient := -2, powers := [(4, 1), (5, 1), (29, 1), (31, 1), (54, 1), (57, 1)] }, { coefficient := -2, powers := [(5, 1), (7, 1), (21, 1), (29, 1), (57, 2)] }, { coefficient := 2, powers := [(5, 1), (7, 1), (26, 1), (29, 1), (57, 2)] }, { coefficient := -2, powers := [(5, 1), (7, 1), (29, 1), (31, 1), (44, 1), (57, 1)] }, { coefficient := -2, powers := [(5, 1), (7, 1), (29, 1), (31, 1), (54, 1), (57, 1)] }, { coefficient := -2, powers := [(5, 1), (11, 1), (21, 1), (29, 1), (54, 1), (57, 1)] }, { coefficient := -2, powers := [(5, 1), (15, 1), (26, 1), (29, 1), (54, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (23, 1), (54, 1), (58, 1)] }, { coefficient := -1, powers := [(4, 1), (32, 1), (47, 1), (54, 1)] }, { coefficient := 1, powers := [(7, 1), (23, 1), (44, 1), (58, 1)] }, { coefficient := 1, powers := [(7, 1), (23, 1), (54, 1), (58, 1)] }, { coefficient := -1, powers := [(7, 1), (32, 1), (44, 1), (47, 1)] }, { coefficient := -1, powers := [(7, 1), (32, 1), (47, 1), (54, 1)] }],
  [{ coefficient := 2, powers := [(4, 1), (29, 1), (31, 1), (40, 1), (47, 1), (54, 1)] }, { coefficient := 2, powers := [(4, 1), (29, 1), (31, 1), (44, 1), (47, 1), (54, 1)] }, { coefficient := -2, powers := [(7, 1), (26, 1), (29, 1), (40, 1), (47, 1), (57, 1)] }, { coefficient := -2, powers := [(7, 1), (26, 1), (29, 1), (44, 1), (47, 1), (57, 1)] }, { coefficient := 2, powers := [(7, 1), (29, 1), (31, 1), (40, 1), (44, 1), (47, 1)] }, { coefficient := 2, powers := [(7, 1), (29, 1), (31, 1), (40, 1), (47, 1), (54, 1)] }, { coefficient := 2, powers := [(7, 1), (29, 1), (31, 1), (44, 2), (47, 1)] }, { coefficient := 2, powers := [(7, 1), (29, 1), (31, 1), (44, 1), (47, 1), (54, 1)] }, { coefficient := 2, powers := [(15, 1), (26, 1), (29, 1), (40, 1), (47, 1), (54, 1)] }, { coefficient := 2, powers := [(15, 1), (26, 1), (29, 1), (44, 1), (47, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (23, 1), (31, 1), (51, 1), (54, 1)] }, { coefficient := 1, powers := [(7, 1), (23, 1), (26, 1), (51, 1), (57, 1)] }, { coefficient := -1, powers := [(7, 1), (23, 1), (31, 1), (44, 1), (51, 1)] }, { coefficient := -1, powers := [(7, 1), (23, 1), (31, 1), (51, 1), (54, 1)] }, { coefficient := -2, powers := [(15, 1), (23, 1), (26, 1), (51, 1), (54, 1)] }],
  [{ coefficient := 2, powers := [(3, 1), (15, 1), (23, 1), (25, 1), (26, 1), (54, 1), (57, 1)] }, { coefficient := -1, powers := [(4, 1), (23, 1), (25, 1), (34, 1), (50, 1)] }, { coefficient := -1, powers := [(4, 1), (23, 1), (25, 1), (34, 1), (54, 1)] }, { coefficient := -1, powers := [(7, 1), (21, 1), (23, 1), (25, 1), (57, 1)] }, { coefficient := 1, powers := [(7, 1), (23, 1), (25, 1), (34, 1), (44, 1)] }, { coefficient := 1, powers := [(7, 1), (23, 1), (25, 1), (34, 1), (50, 1)] }, { coefficient := 1, powers := [(7, 1), (23, 1), (25, 1), (34, 1), (54, 1)] }, { coefficient := -1, powers := [(11, 1), (21, 1), (23, 1), (25, 1), (54, 1)] }, { coefficient := -1, powers := [(11, 1), (23, 1), (25, 1), (34, 1), (37, 1)] }, { coefficient := -1, powers := [(11, 1), (28, 1), (34, 1), (38, 1)] }, { coefficient := -2, powers := [(15, 1), (23, 1), (24, 1), (26, 1), (51, 1), (54, 1)] }, { coefficient := 1, powers := [(15, 1), (23, 1), (25, 1), (26, 1), (54, 1)] }, { coefficient := 1, powers := [(15, 1), (23, 1), (25, 1), (34, 1), (37, 1)] }, { coefficient := -1, powers := [(15, 1), (23, 1), (26, 1), (51, 1)] }, { coefficient := 1, powers := [(15, 1), (28, 1), (34, 1), (38, 1)] }],
  [{ coefficient := 2, powers := [(5, 1), (7, 1), (24, 1), (28, 1), (57, 1), (58, 1)] }, { coefficient := -1, powers := [(5, 1), (7, 1), (32, 1), (43, 1), (57, 1)] }, { coefficient := 2, powers := [(5, 1), (11, 1), (24, 1), (28, 1), (54, 1), (58, 1)] }, { coefficient := -1, powers := [(5, 1), (11, 1), (32, 1), (43, 1), (54, 1)] }, { coefficient := 1, powers := [(7, 1), (13, 1), (23, 1), (43, 1), (57, 1)] }, { coefficient := 1, powers := [(7, 1), (13, 1), (27, 1), (47, 1), (57, 1)] }, { coefficient := 1, powers := [(11, 1), (13, 1), (23, 1), (43, 1), (54, 1)] }, { coefficient := 1, powers := [(11, 1), (13, 1), (27, 1), (47, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (17, 1), (31, 1), (47, 1), (54, 1)] }, { coefficient := -1, powers := [(4, 1), (17, 1), (34, 1), (47, 1), (50, 1)] }, { coefficient := -1, powers := [(4, 1), (17, 1), (34, 1), (47, 1), (54, 1)] }, { coefficient := -1, powers := [(7, 1), (17, 1), (21, 1), (47, 1), (57, 1)] }, { coefficient := 1, powers := [(7, 1), (17, 1), (26, 1), (47, 1), (57, 1)] }, { coefficient := -1, powers := [(7, 1), (17, 1), (31, 1), (44, 1), (47, 1)] }, { coefficient := -1, powers := [(7, 1), (17, 1), (31, 1), (47, 1), (54, 1)] }, { coefficient := 1, powers := [(7, 1), (17, 1), (34, 1), (44, 1), (47, 1)] }, { coefficient := 1, powers := [(7, 1), (17, 1), (34, 1), (47, 1), (50, 1)] }, { coefficient := 1, powers := [(7, 1), (17, 1), (34, 1), (47, 1), (54, 1)] }, { coefficient := -1, powers := [(11, 1), (17, 1), (21, 1), (47, 1), (54, 1)] }, { coefficient := -1, powers := [(15, 1), (17, 1), (26, 1), (47, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (11, 1), (34, 1), (55, 1)] }, { coefficient := -1, powers := [(5, 1), (15, 1), (34, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (11, 1), (34, 1), (47, 1)] }, { coefficient := -1, powers := [(8, 1), (15, 1), (34, 1), (47, 1)] }, { coefficient := -1, powers := [(11, 1), (18, 1), (34, 1), (38, 1)] }, { coefficient := 1, powers := [(15, 1), (18, 1), (34, 1), (38, 1)] }],
  [{ coefficient := 2, powers := [(15, 1), (19, 1), (23, 1), (26, 1), (54, 1), (55, 1)] }, { coefficient := -1, powers := [(15, 1), (23, 1), (26, 1), (55, 1)] }, { coefficient := -1, powers := [(15, 1), (26, 1), (29, 1), (47, 1)] }, { coefficient := -1, powers := [(15, 1), (26, 1), (35, 1), (38, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (13, 1), (21, 1), (51, 1), (57, 1)] }, { coefficient := -1, powers := [(11, 1), (13, 1), (21, 1), (51, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (17, 1), (26, 1), (58, 1)] }, { coefficient := -1, powers := [(13, 1), (15, 1), (26, 1), (43, 1), (44, 1)] }, { coefficient := 1, powers := [(13, 1), (15, 1), (26, 1), (45, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (18, 1), (32, 1), (54, 1)] }, { coefficient := -1, powers := [(7, 1), (18, 1), (32, 1), (44, 1)] }, { coefficient := -1, powers := [(7, 1), (18, 1), (32, 1), (54, 1)] }],
  [{ coefficient := 2, powers := [(3, 1), (15, 1), (18, 1), (23, 1), (26, 1), (54, 1), (57, 1)] }, { coefficient := 1, powers := [(4, 1), (5, 1), (31, 1), (35, 1), (54, 1)] }, { coefficient := 1, powers := [(4, 1), (5, 1), (34, 1), (35, 1), (50, 1)] }, { coefficient := 1, powers := [(4, 1), (5, 1), (34, 1), (35, 1), (54, 1)] }, { coefficient := -1, powers := [(4, 1), (18, 1), (23, 1), (34, 1), (50, 1)] }, { coefficient := -2, powers := [(4, 1), (18, 1), (23, 1), (34, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (7, 1), (21, 1), (35, 1), (57, 1)] }, { coefficient := -1, powers := [(5, 1), (7, 1), (26, 1), (35, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (7, 1), (31, 1), (35, 1), (44, 1)] }, { coefficient := 1, powers := [(5, 1), (7, 1), (31, 1), (35, 1), (54, 1)] }, { coefficient := -1, powers := [(5, 1), (7, 1), (34, 1), (35, 1), (44, 1)] }, { coefficient := -1, powers := [(5, 1), (7, 1), (34, 1), (35, 1), (50, 1)] }, { coefficient := -1, powers := [(5, 1), (7, 1), (34, 1), (35, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (11, 1), (21, 1), (35, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (11, 1), (34, 1), (35, 1), (37, 1)] }, { coefficient := 1, powers := [(5, 1), (15, 1), (26, 1), (35, 1), (54, 1)] }, { coefficient := -1, powers := [(5, 1), (15, 1), (34, 1), (35, 1), (37, 1)] }, { coefficient := -1, powers := [(7, 1), (18, 1), (21, 1), (23, 1), (57, 1)] }, { coefficient := 1, powers := [(7, 1), (18, 1), (23, 1), (34, 1), (50, 1)] }, { coefficient := -1, powers := [(11, 1), (18, 1), (21, 1), (23, 1), (54, 1)] }, { coefficient := -1, powers := [(11, 1), (18, 1), (23, 1), (34, 1), (37, 1)] }, { coefficient := -1, powers := [(15, 1), (18, 1), (23, 1), (26, 1), (54, 1)] }, { coefficient := 1, powers := [(15, 1), (18, 1), (23, 1), (34, 1), (37, 1)] }],
  [{ coefficient := -2, powers := [(15, 1), (23, 1), (26, 1), (54, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (7, 1), (32, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (11, 1), (32, 1), (54, 1)] }, { coefficient := -1, powers := [(7, 1), (13, 1), (23, 1), (57, 1)] }, { coefficient := -1, powers := [(11, 1), (13, 1), (23, 1), (54, 1)] }],
  [{ coefficient := -2, powers := [(13, 1), (15, 1), (23, 1), (26, 1), (40, 1), (51, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(54, 1)] }],
  [{ coefficient := -1, powers := [(54, 1)] }],
  [{ coefficient := 2, powers := [(4, 1), (6, 1), (29, 1), (31, 1), (54, 1), (57, 1)] }, { coefficient := 1, powers := [(4, 1), (29, 1), (31, 1), (54, 1)] }, { coefficient := -2, powers := [(6, 1), (7, 1), (26, 1), (29, 1), (57, 2)] }, { coefficient := 2, powers := [(6, 1), (7, 1), (29, 1), (31, 1), (44, 1), (57, 1)] }, { coefficient := 2, powers := [(6, 1), (7, 1), (29, 1), (31, 1), (54, 1), (57, 1)] }, { coefficient := 2, powers := [(6, 1), (15, 1), (26, 1), (29, 1), (54, 1), (57, 1)] }, { coefficient := -1, powers := [(7, 1), (21, 1), (29, 1), (57, 1)] }, { coefficient := -1, powers := [(7, 1), (26, 1), (29, 1), (57, 1)] }, { coefficient := 1, powers := [(7, 1), (29, 1), (31, 1), (44, 1)] }, { coefficient := 1, powers := [(7, 1), (29, 1), (31, 1), (54, 1)] }, { coefficient := -1, powers := [(11, 1), (21, 1), (29, 1), (54, 1)] }, { coefficient := 1, powers := [(11, 1), (29, 1), (34, 1), (37, 1)] }, { coefficient := 1, powers := [(15, 1), (26, 1), (29, 1), (54, 1)] }, { coefficient := -1, powers := [(15, 1), (29, 1), (34, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (18, 1), (31, 1), (54, 1)] }, { coefficient := 1, powers := [(4, 1), (18, 1), (34, 1), (50, 1)] }, { coefficient := 2, powers := [(4, 1), (18, 1), (34, 1), (54, 1)] }, { coefficient := 1, powers := [(7, 1), (18, 1), (21, 1), (57, 1)] }, { coefficient := -1, powers := [(7, 1), (18, 1), (26, 1), (57, 1)] }, { coefficient := 1, powers := [(7, 1), (18, 1), (31, 1), (44, 1)] }, { coefficient := 1, powers := [(7, 1), (18, 1), (31, 1), (54, 1)] }, { coefficient := -1, powers := [(7, 1), (18, 1), (34, 1), (50, 1)] }, { coefficient := 1, powers := [(11, 1), (18, 1), (21, 1), (54, 1)] }, { coefficient := 1, powers := [(11, 1), (18, 1), (34, 1), (37, 1)] }, { coefficient := 1, powers := [(15, 1), (18, 1), (26, 1), (54, 1)] }, { coefficient := -1, powers := [(15, 1), (18, 1), (34, 1), (37, 1)] }],
  [{ coefficient := -2, powers := [(5, 1), (7, 1), (21, 1), (24, 1), (57, 1), (58, 1)] }, { coefficient := -2, powers := [(5, 1), (11, 1), (21, 1), (24, 1), (54, 1), (58, 1)] }, { coefficient := 1, powers := [(13, 1), (15, 1), (26, 1), (43, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (32, 1), (54, 1)] }, { coefficient := 1, powers := [(7, 1), (32, 1), (44, 1)] }, { coefficient := 1, powers := [(7, 1), (32, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (35, 1), (50, 1)] }, { coefficient := 1, powers := [(4, 1), (35, 1), (54, 1)] }, { coefficient := -1, powers := [(7, 1), (35, 1), (44, 1)] }, { coefficient := -1, powers := [(7, 1), (35, 1), (50, 1)] }, { coefficient := -1, powers := [(7, 1), (35, 1), (54, 1)] }],
  [{ coefficient := 2, powers := [(13, 1), (15, 1), (23, 1), (26, 1), (51, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (31, 1), (47, 1), (54, 1)] }, { coefficient := 1, powers := [(4, 1), (34, 1), (47, 1), (50, 1)] }, { coefficient := 1, powers := [(4, 1), (34, 1), (47, 1), (54, 1)] }, { coefficient := 1, powers := [(7, 1), (21, 1), (47, 1), (57, 1)] }, { coefficient := -1, powers := [(7, 1), (26, 1), (47, 1), (57, 1)] }, { coefficient := 1, powers := [(7, 1), (31, 1), (44, 1), (47, 1)] }, { coefficient := 1, powers := [(7, 1), (31, 1), (47, 1), (54, 1)] }, { coefficient := -1, powers := [(7, 1), (34, 1), (44, 1), (47, 1)] }, { coefficient := -1, powers := [(7, 1), (34, 1), (47, 1), (50, 1)] }, { coefficient := -1, powers := [(7, 1), (34, 1), (47, 1), (54, 1)] }, { coefficient := 1, powers := [(11, 1), (21, 1), (47, 1), (54, 1)] }, { coefficient := 1, powers := [(15, 1), (26, 1), (47, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (26, 1), (29, 1), (58, 1)] }, { coefficient := -1, powers := [(7, 1), (26, 1), (32, 1), (55, 1)] }],
  [{ coefficient := -2, powers := [(3, 1), (15, 1), (23, 1), (26, 1), (54, 1), (57, 1)] }, { coefficient := 1, powers := [(4, 1), (23, 1), (34, 1), (50, 1)] }, { coefficient := 1, powers := [(4, 1), (23, 1), (34, 1), (54, 1)] }, { coefficient := 1, powers := [(7, 1), (21, 1), (23, 1), (57, 1)] }, { coefficient := -1, powers := [(7, 1), (23, 1), (34, 1), (44, 1)] }, { coefficient := -1, powers := [(7, 1), (23, 1), (34, 1), (50, 1)] }, { coefficient := -1, powers := [(7, 1), (23, 1), (34, 1), (54, 1)] }, { coefficient := 1, powers := [(11, 1), (21, 1), (23, 1), (54, 1)] }, { coefficient := 1, powers := [(11, 1), (23, 1), (34, 1), (37, 1)] }, { coefficient := 1, powers := [(15, 1), (23, 1), (26, 1), (54, 1)] }, { coefficient := -1, powers := [(15, 1), (23, 1), (34, 1), (37, 1)] }],
  [{ coefficient := 2, powers := [(13, 1), (15, 1), (23, 1), (26, 1), (40, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (17, 1), (26, 1), (29, 1), (58, 1)] }, { coefficient := 1, powers := [(7, 1), (17, 1), (26, 1), (32, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (34, 1), (38, 1)] }, { coefficient := -1, powers := [(15, 1), (34, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (13, 1), (31, 1), (54, 1)] }, { coefficient := 1, powers := [(7, 1), (13, 1), (21, 1), (57, 1)] }, { coefficient := -1, powers := [(7, 1), (13, 1), (26, 1), (57, 1)] }, { coefficient := 1, powers := [(7, 1), (13, 1), (31, 1), (44, 1)] }, { coefficient := 1, powers := [(7, 1), (13, 1), (31, 1), (54, 1)] }, { coefficient := 1, powers := [(11, 1), (13, 1), (21, 1), (54, 1)] }, { coefficient := 1, powers := [(13, 1), (15, 1), (26, 1), (44, 1)] }, { coefficient := 2, powers := [(13, 1), (15, 1), (26, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(13, 1), (15, 1), (26, 1), (46, 1)] }],
  [{ coefficient := -2, powers := [(4, 1), (13, 1), (29, 1), (31, 1), (47, 1), (54, 1)] }, { coefficient := 2, powers := [(5, 1), (7, 1), (21, 1), (29, 1), (57, 1), (58, 1)] }, { coefficient := 2, powers := [(5, 1), (11, 1), (21, 1), (29, 1), (54, 1), (58, 1)] }, { coefficient := 2, powers := [(7, 1), (13, 1), (26, 1), (29, 1), (47, 1), (57, 1)] }, { coefficient := -2, powers := [(7, 1), (13, 1), (29, 1), (31, 1), (44, 1), (47, 1)] }, { coefficient := -2, powers := [(7, 1), (13, 1), (29, 1), (31, 1), (47, 1), (54, 1)] }, { coefficient := -2, powers := [(13, 1), (15, 1), (26, 1), (29, 1), (47, 1), (54, 1)] }],
  [{ coefficient := 2, powers := [(13, 1), (15, 1), (23, 1), (26, 1), (54, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(15, 1), (26, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(26, 1)] }],
  [{ coefficient := 1, powers := [(15, 1)] }],
  [{ coefficient := -2, powers := [(13, 1), (15, 1), (23, 1), (26, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (26, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (34, 1)] }, { coefficient := -2, powers := [(13, 1), (15, 1), (19, 1), (23, 1), (26, 1), (54, 1), (55, 1)] }, { coefficient := -1, powers := [(15, 1), (26, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(4, 1), (31, 1), (54, 1)] }, { coefficient := -1, powers := [(4, 1), (34, 1), (50, 1)] }, { coefficient := -1, powers := [(4, 1), (34, 1), (54, 1)] }, { coefficient := -1, powers := [(7, 1), (21, 1), (57, 1)] }, { coefficient := 1, powers := [(7, 1), (26, 1), (57, 1)] }, { coefficient := -1, powers := [(7, 1), (31, 1), (44, 1)] }, { coefficient := -1, powers := [(7, 1), (31, 1), (54, 1)] }, { coefficient := 1, powers := [(7, 1), (34, 1), (44, 1)] }, { coefficient := 1, powers := [(7, 1), (34, 1), (50, 1)] }, { coefficient := 1, powers := [(7, 1), (34, 1), (54, 1)] }, { coefficient := -1, powers := [(11, 1), (21, 1), (54, 1)] }, { coefficient := -1, powers := [(11, 1), (34, 1), (37, 1)] }, { coefficient := -1, powers := [(15, 1), (26, 1), (54, 1)] }, { coefficient := 1, powers := [(15, 1), (34, 1), (37, 1)] }],
  [{ coefficient := -2, powers := [(3, 1), (15, 1), (18, 1), (23, 1), (26, 1), (44, 1), (52, 1), (54, 1), (57, 1)] }, { coefficient := -1, powers := [(4, 1), (5, 1), (31, 1), (35, 1), (44, 1), (52, 1), (54, 1)] }, { coefficient := -1, powers := [(4, 1), (5, 1), (34, 1), (35, 1), (44, 1), (50, 1), (52, 1)] }, { coefficient := -1, powers := [(4, 1), (5, 1), (34, 1), (35, 1), (44, 1), (52, 1), (54, 1)] }, { coefficient := 2, powers := [(4, 1), (13, 1), (29, 1), (31, 1), (44, 1), (47, 1), (54, 1)] }, { coefficient := 1, powers := [(4, 1), (18, 1), (23, 1), (34, 1), (44, 1), (50, 1), (52, 1)] }, { coefficient := 2, powers := [(4, 1), (18, 1), (23, 1), (34, 1), (44, 1), (52, 1), (54, 1)] }, { coefficient := -2, powers := [(5, 1), (7, 1), (21, 1), (29, 1), (44, 1), (57, 1), (58, 1)] }, { coefficient := -1, powers := [(5, 1), (7, 1), (21, 1), (35, 1), (44, 1), (52, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (7, 1), (26, 1), (35, 1), (44, 1), (52, 1), (57, 1)] }, { coefficient := -1, powers := [(5, 1), (7, 1), (31, 1), (35, 1), (44, 2), (52, 1)] }, { coefficient := -1, powers := [(5, 1), (7, 1), (31, 1), (35, 1), (44, 1), (52, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (7, 1), (34, 1), (35, 1), (44, 2), (52, 1)] }, { coefficient := 1, powers := [(5, 1), (7, 1), (34, 1), (35, 1), (44, 1), (50, 1), (52, 1)] }, { coefficient := 1, powers := [(5, 1), (7, 1), (34, 1), (35, 1), (44, 1), (52, 1), (54, 1)] }, { coefficient := -2, powers := [(5, 1), (11, 1), (21, 1), (29, 1), (44, 1), (54, 1), (58, 1)] }, { coefficient := -1, powers := [(5, 1), (11, 1), (21, 1), (35, 1), (44, 1), (52, 1), (54, 1)] }, { coefficient := -1, powers := [(5, 1), (11, 1), (34, 1), (35, 1), (37, 1), (44, 1), (52, 1)] }, { coefficient := -1, powers := [(5, 1), (15, 1), (26, 1), (35, 1), (44, 1), (52, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (15, 1), (34, 1), (35, 1), (37, 1), (44, 1), (52, 1)] }, { coefficient := -2, powers := [(7, 1), (13, 1), (26, 1), (29, 1), (44, 1), (47, 1), (57, 1)] }, { coefficient := 2, powers := [(7, 1), (13, 1), (29, 1), (31, 1), (44, 2), (47, 1)] }, { coefficient := 2, powers := [(7, 1), (13, 1), (29, 1), (31, 1), (44, 1), (47, 1), (54, 1)] }, { coefficient := 1, powers := [(7, 1), (17, 1), (26, 1), (29, 1), (46, 1), (50, 1), (58, 1)] }, { coefficient := -1, powers := [(7, 1), (17, 1), (26, 1), (32, 1), (46, 1), (50, 1), (55, 1)] }, { coefficient := 1, powers := [(7, 1), (18, 1), (21, 1), (23, 1), (44, 1), (52, 1), (57, 1)] }, { coefficient := -1, powers := [(7, 1), (18, 1), (23, 1), (34, 1), (44, 1), (50, 1), (52, 1)] }, { coefficient := -1, powers := [(7, 1), (34, 1), (37, 1), (57, 1)] }, { coefficient := -1, powers := [(7, 1), (34, 1), (40, 1), (54, 1)] }, { coefficient := -1, powers := [(7, 1), (34, 1), (44, 1), (50, 1)] }, { coefficient := 1, powers := [(11, 1), (18, 1), (21, 1), (23, 1), (44, 1), (52, 1), (54, 1)] }, { coefficient := 1, powers := [(11, 1), (18, 1), (23, 1), (34, 1), (37, 1), (44, 1), (52, 1)] }, { coefficient := 2, powers := [(13, 1), (15, 1), (19, 1), (23, 1), (26, 1), (37, 1), (54, 1), (55, 1), (57, 1)] }, { coefficient := 2, powers := [(13, 1), (15, 1), (19, 1), (23, 1), (26, 1), (40, 1), (54, 2), (55, 1)] }, { coefficient := 2, powers := [(13, 1), (15, 1), (19, 1), (23, 1), (26, 1), (44, 1), (50, 1), (54, 1), (55, 1)] }, { coefficient := 2, powers := [(13, 1), (15, 1), (23, 1), (26, 1), (40, 1), (54, 1), (55, 1)] }, { coefficient := -2, powers := [(13, 1), (15, 1), (23, 1), (26, 1), (50, 1), (54, 1), (55, 1)] }, { coefficient := 2, powers := [(13, 1), (15, 1), (26, 1), (29, 1), (44, 1), (47, 1), (54, 1)] }, { coefficient := 1, powers := [(15, 1), (18, 1), (23, 1), (26, 1), (44, 1), (52, 1), (54, 1)] }, { coefficient := -1, powers := [(15, 1), (18, 1), (23, 1), (34, 1), (37, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(15, 1), (26, 1), (37, 1), (57, 1)] }, { coefficient := 1, powers := [(15, 1), (26, 1), (40, 1), (54, 1)] }, { coefficient := 1, powers := [(15, 1), (26, 1), (44, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(37, 1), (57, 1)] }, { coefficient := 1, powers := [(40, 1), (54, 1)] }, { coefficient := 1, powers := [(44, 1), (50, 1)] }, { coefficient := 1, powers := [(44, 1), (54, 1)] }, { coefficient := 1, powers := [(50, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (31, 1), (38, 1), (54, 1), (58, 1)] }, { coefficient := 1, powers := [(4, 1), (34, 1), (38, 1), (50, 1), (58, 1)] }, { coefficient := 1, powers := [(4, 1), (34, 1), (38, 1), (54, 1), (58, 1)] }, { coefficient := 1, powers := [(7, 1), (21, 1), (38, 1), (57, 1), (58, 1)] }, { coefficient := 1, powers := [(7, 1), (26, 1), (46, 1), (51, 1), (58, 1)] }, { coefficient := 1, powers := [(7, 1), (31, 1), (38, 1), (44, 1), (58, 1)] }, { coefficient := 1, powers := [(7, 1), (31, 1), (38, 1), (54, 1), (58, 1)] }, { coefficient := -1, powers := [(7, 1), (34, 1), (38, 1), (44, 1), (58, 1)] }, { coefficient := -1, powers := [(7, 1), (34, 1), (38, 1), (50, 1), (58, 1)] }, { coefficient := -1, powers := [(7, 1), (34, 1), (38, 1), (54, 1), (58, 1)] }, { coefficient := 1, powers := [(11, 1), (21, 1), (38, 1), (54, 1), (58, 1)] }, { coefficient := 1, powers := [(11, 1), (34, 1), (37, 1), (47, 1), (52, 1)] }, { coefficient := 1, powers := [(15, 1), (26, 1), (38, 1), (54, 1), (58, 1)] }, { coefficient := -1, powers := [(15, 1), (34, 1), (37, 1), (47, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (4, 1), (31, 1), (54, 1), (55, 1)] }, { coefficient := 1, powers := [(2, 1), (4, 1), (34, 1), (50, 1), (55, 1)] }, { coefficient := 1, powers := [(2, 1), (4, 1), (34, 1), (54, 1), (55, 1)] }, { coefficient := 1, powers := [(2, 1), (7, 1), (21, 1), (55, 1), (57, 1)] }, { coefficient := -1, powers := [(2, 1), (7, 1), (26, 1), (55, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (7, 1), (31, 1), (44, 1), (55, 1)] }, { coefficient := 1, powers := [(2, 1), (7, 1), (31, 1), (54, 1), (55, 1)] }, { coefficient := -1, powers := [(2, 1), (7, 1), (34, 1), (44, 1), (55, 1)] }, { coefficient := -1, powers := [(2, 1), (7, 1), (34, 1), (50, 1), (55, 1)] }, { coefficient := -1, powers := [(2, 1), (7, 1), (34, 1), (54, 1), (55, 1)] }, { coefficient := 1, powers := [(2, 1), (11, 1), (21, 1), (54, 1), (55, 1)] }, { coefficient := 1, powers := [(2, 1), (11, 1), (34, 1), (37, 1), (55, 1)] }, { coefficient := -1, powers := [(2, 1), (15, 1), (34, 1), (37, 1), (55, 1)] }, { coefficient := -2, powers := [(4, 1), (6, 1), (18, 1), (29, 1), (31, 1), (54, 1), (57, 1)] }, { coefficient := 1, powers := [(4, 1), (8, 1), (31, 1), (35, 1), (54, 1)] }, { coefficient := -1, powers := [(4, 1), (18, 1), (29, 1), (31, 1), (54, 1)] }, { coefficient := -1, powers := [(4, 1), (18, 1), (29, 1), (34, 1), (54, 1)] }, { coefficient := 2, powers := [(6, 1), (7, 1), (18, 1), (26, 1), (29, 1), (57, 2)] }, { coefficient := -2, powers := [(6, 1), (7, 1), (18, 1), (29, 1), (31, 1), (44, 1), (57, 1)] }, { coefficient := -2, powers := [(6, 1), (7, 1), (18, 1), (29, 1), (31, 1), (54, 1), (57, 1)] }, { coefficient := -2, powers := [(6, 1), (15, 1), (18, 1), (26, 1), (29, 1), (54, 1), (57, 1)] }, { coefficient := 1, powers := [(7, 1), (8, 1), (21, 1), (35, 1), (57, 1)] }, { coefficient := -1, powers := [(7, 1), (8, 1), (26, 1), (35, 1), (57, 1)] }, { coefficient := 1, powers := [(7, 1), (8, 1), (31, 1), (35, 1), (44, 1)] }, { coefficient := 1, powers := [(7, 1), (8, 1), (31, 1), (35, 1), (54, 1)] }, { coefficient := 1, powers := [(7, 1), (18, 1), (21, 1), (29, 1), (57, 1)] }, { coefficient := 1, powers := [(7, 1), (18, 1), (26, 1), (29, 1), (57, 1)] }, { coefficient := -1, powers := [(7, 1), (18, 1), (29, 1), (31, 1), (44, 1)] }, { coefficient := -1, powers := [(7, 1), (18, 1), (29, 1), (31, 1), (54, 1)] }, { coefficient := -1, powers := [(7, 1), (18, 1), (29, 1), (34, 1), (44, 1)] }, { coefficient := -1, powers := [(7, 1), (18, 1), (29, 1), (34, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (11, 1), (21, 1), (35, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (11, 1), (34, 1), (35, 1), (37, 1)] }, { coefficient := 1, powers := [(8, 1), (15, 1), (26, 1), (35, 1), (54, 1)] }, { coefficient := -1, powers := [(8, 1), (15, 1), (34, 1), (35, 1), (37, 1)] }, { coefficient := 1, powers := [(11, 1), (18, 1), (21, 1), (29, 1), (54, 1)] }, { coefficient := -1, powers := [(11, 1), (18, 1), (29, 1), (34, 1), (37, 1)] }, { coefficient := -1, powers := [(15, 1), (17, 1), (26, 1), (28, 1), (55, 1)] }, { coefficient := -1, powers := [(15, 1), (18, 1), (26, 1), (29, 1), (54, 1)] }, { coefficient := 1, powers := [(15, 1), (18, 1), (29, 1), (34, 1), (37, 1)] }]
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
    (values : Fin 61 → R) :
    ¬ ∀ index : Fin 48,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component17.SelectedLeafB0_6.selectedHasNoCommonZero

end Krenn.Component17.SelectedLeafB0_6
