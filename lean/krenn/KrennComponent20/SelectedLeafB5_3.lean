import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component20.SelectedLeafB5_3

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "48fdaf85703fcf441b12cf2fa5c1c58cad6a9faa474abdffd878b65423408f72"
def certificateSHA256 : String := "d7cf72773d4cdec8d909b080fe73392f571193b7b49ab7c3d6af67a09ed25067"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 54 → Fin 642 := ![
  6,
  9,
  12,
  15,
  16,
  23,
  27,
  33,
  97,
  141,
  177,
  179,
  183,
  186,
  187,
  189,
  191,
  192,
  193,
  194,
  197,
  198,
  291,
  313,
  317,
  318,
  345,
  348,
  349,
  350,
  351,
  352,
  353,
  369,
  373,
  374,
  387,
  408,
  462,
  466,
  480,
  527,
  534,
  551,
  579,
  580,
  622,
  634,
  635,
  636,
  637,
  638,
  640,
  641
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 54 → SparsePoly (Fin 64) := ![
  [{ coefficient := 1, powers := [(4, 1), (35, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (31, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (23, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (49, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (25, 1)] }, { coefficient := 1, powers := [(18, 1), (20, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (45, 1)] }, { coefficient := 1, powers := [(13, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (20, 1)] }, { coefficient := 1, powers := [(18, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (40, 1)] }, { coefficient := 1, powers := [(19, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (51, 1)] }, { coefficient := 1, powers := [(23, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (43, 1)] }, { coefficient := 1, powers := [(28, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (52, 1)] }, { coefficient := 1, powers := [(29, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (41, 1)] }, { coefficient := 1, powers := [(27, 1), (46, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(28, 1), (40, 1)] }, { coefficient := 1, powers := [(28, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (40, 1)] }, { coefficient := 1, powers := [(29, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(41, 1), (43, 1)] }, { coefficient := 1, powers := [(47, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(43, 1), (53, 1)] }, { coefficient := 1, powers := [(49, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (26, 1), (45, 1)] }, { coefficient := 1, powers := [(18, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (25, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (21, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (49, 1), (55, 1)] }, { coefficient := 1, powers := [(49, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (43, 1), (52, 1)] }, { coefficient := 1, powers := [(22, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1)] }, { coefficient := 1, powers := [(21, 1), (43, 1)] }, { coefficient := 1, powers := [(25, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (45, 1)] }, { coefficient := 1, powers := [(4, 1), (34, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (51, 1)] }, { coefficient := 1, powers := [(7, 1), (31, 1)] }, { coefficient := 1, powers := [(11, 1), (27, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (45, 1)] }, { coefficient := 1, powers := [(18, 1), (28, 1), (40, 1)] }, { coefficient := 1, powers := [(18, 1), (28, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (51, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (51, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (59, 1)] }, { coefficient := 1, powers := [(13, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (59, 1)] }, { coefficient := 1, powers := [(13, 1), (56, 1)] }, { coefficient := 1, powers := [(19, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1), (51, 1)] }, { coefficient := 1, powers := [(21, 1), (43, 1), (51, 1)] }, { coefficient := 1, powers := [(47, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (40, 1), (56, 1)] }, { coefficient := 1, powers := [(4, 1), (31, 1), (56, 1)] }, { coefficient := 1, powers := [(11, 1), (22, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (41, 1), (55, 1)] }, { coefficient := 1, powers := [(7, 1), (34, 1), (41, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (40, 1), (56, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (40, 1)] }, { coefficient := 1, powers := [(19, 1), (29, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (35, 1), (51, 1)] }, { coefficient := 1, powers := [(7, 1), (35, 1), (40, 1)] }, { coefficient := 1, powers := [(11, 1), (35, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (47, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1)] }, { coefficient := 1, powers := [(18, 1), (28, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (53, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1)] }, { coefficient := 1, powers := [(13, 1), (29, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (53, 1)] }, { coefficient := 1, powers := [(29, 1), (41, 1)] }, { coefficient := 1, powers := [(29, 1), (46, 1), (49, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (22, 1), (58, 1)] }, { coefficient := 1, powers := [(6, 1), (31, 1), (45, 1)] }, { coefficient := 1, powers := [(6, 1), (34, 1), (40, 1)] }, { coefficient := 1, powers := [(22, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (22, 1), (58, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1), (45, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (40, 1)] }, { coefficient := 1, powers := [(18, 1), (22, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (43, 1), (52, 1)] }, { coefficient := 1, powers := [(24, 1), (56, 1)] }, { coefficient := 1, powers := [(29, 1), (47, 1)] }, { coefficient := 1, powers := [(35, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (58, 1)] }, { coefficient := 1, powers := [(7, 1), (58, 1)] }, { coefficient := 1, powers := [(11, 1), (45, 1)] }, { coefficient := 1, powers := [(11, 1), (55, 1)] }, { coefficient := 1, powers := [(16, 1), (40, 1)] }, { coefficient := 1, powers := [(16, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (51, 1)] }, { coefficient := 1, powers := [(22, 1), (55, 1)] }, { coefficient := 1, powers := [(27, 1), (40, 1)] }, { coefficient := 1, powers := [(27, 1), (45, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (38, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (41, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (47, 1), (53, 1)] }, { coefficient := 1, powers := [(21, 1), (43, 1), (53, 1)] }, { coefficient := 1, powers := [(21, 1), (49, 1), (56, 1)] }, { coefficient := 1, powers := [(26, 1), (41, 1), (43, 1)] }, { coefficient := 1, powers := [(26, 1), (47, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (37, 1), (58, 1)] }, { coefficient := 1, powers := [(1, 1), (40, 1), (55, 1)] }, { coefficient := 1, powers := [(1, 1), (45, 1), (51, 1)] }, { coefficient := 1, powers := [(4, 1), (27, 1), (58, 1)] }, { coefficient := 1, powers := [(4, 1), (31, 1), (55, 1)] }, { coefficient := 1, powers := [(4, 1), (34, 1), (51, 1)] }, { coefficient := 1, powers := [(7, 1), (22, 1), (58, 1)] }, { coefficient := 1, powers := [(7, 1), (31, 1), (45, 1)] }, { coefficient := 1, powers := [(7, 1), (34, 1), (40, 1)] }, { coefficient := 1, powers := [(11, 1), (22, 1), (55, 1)] }, { coefficient := 1, powers := [(11, 1), (27, 1), (45, 1)] }, { coefficient := 1, powers := [(11, 1), (34, 1), (37, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1), (51, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1), (40, 1)] }, { coefficient := 1, powers := [(16, 1), (31, 1), (37, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (41, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (47, 1), (53, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (53, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (59, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (47, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(13, 1), (24, 1), (56, 1)] }, { coefficient := 1, powers := [(13, 1), (29, 1), (47, 1)] }, { coefficient := 1, powers := [(13, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (53, 1)] }, { coefficient := 1, powers := [(19, 1), (29, 1), (41, 1)] }, { coefficient := 1, powers := [(19, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (60, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (61, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(40, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(41, 1), (63, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 54 → SparsePoly (Fin 64) := ![
  [{ coefficient := -2, powers := [(8, 1), (22, 1), (41, 1), (58, 1)] }, { coefficient := 2, powers := [(8, 1), (27, 1), (41, 1), (58, 1)] }, { coefficient := 2, powers := [(8, 1), (31, 1), (41, 1), (55, 1)] }, { coefficient := 2, powers := [(8, 1), (34, 1), (41, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (24, 1), (55, 1), (59, 1)] }, { coefficient := 1, powers := [(4, 1), (32, 1), (47, 1), (55, 1)] }, { coefficient := 1, powers := [(7, 1), (24, 1), (40, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (32, 1), (40, 1), (47, 1)] }, { coefficient := -1, powers := [(11, 1), (24, 1), (37, 1), (59, 1)] }, { coefficient := -1, powers := [(11, 1), (32, 1), (37, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (34, 1), (37, 1), (41, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (34, 1), (37, 1)] }],
  [{ coefficient := -1, powers := [(21, 1), (29, 1), (60, 1)] }, { coefficient := -1, powers := [(24, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (22, 1), (41, 1), (51, 1), (56, 1), (63, 1)] }, { coefficient := -1, powers := [(2, 1), (22, 1), (41, 1), (55, 1), (56, 1), (63, 1)] }, { coefficient := -1, powers := [(2, 1), (27, 1), (40, 1), (41, 1), (56, 1), (63, 1)] }, { coefficient := -1, powers := [(2, 1), (27, 1), (41, 1), (45, 1), (56, 1), (63, 1)] }, { coefficient := -1, powers := [(2, 1), (34, 1), (37, 1), (41, 1), (56, 1), (63, 1)] }, { coefficient := -1, powers := [(5, 1), (22, 1), (32, 1), (51, 1), (56, 1), (63, 1)] }, { coefficient := -1, powers := [(5, 1), (22, 1), (32, 1), (55, 1), (56, 1), (63, 1)] }, { coefficient := -1, powers := [(5, 1), (27, 1), (32, 1), (40, 1), (56, 1), (63, 1)] }, { coefficient := -1, powers := [(5, 1), (27, 1), (32, 1), (45, 1), (56, 1), (63, 1)] }, { coefficient := -1, powers := [(5, 1), (32, 1), (34, 1), (37, 1), (56, 1), (63, 1)] }, { coefficient := -1, powers := [(8, 1), (22, 1), (24, 1), (51, 1), (59, 1), (63, 1)] }, { coefficient := -1, powers := [(8, 1), (22, 1), (24, 1), (55, 1), (59, 1), (63, 1)] }, { coefficient := -1, powers := [(8, 1), (22, 1), (32, 1), (47, 1), (51, 1), (63, 1)] }, { coefficient := -1, powers := [(8, 1), (22, 1), (32, 1), (47, 1), (55, 1), (63, 1)] }, { coefficient := -2, powers := [(8, 1), (22, 1), (35, 1), (40, 1), (41, 1), (63, 1)] }, { coefficient := -2, powers := [(8, 1), (22, 1), (35, 1), (41, 1), (51, 1), (63, 1)] }, { coefficient := -1, powers := [(8, 1), (24, 1), (27, 1), (45, 1), (59, 1), (63, 1)] }, { coefficient := -1, powers := [(8, 1), (24, 1), (34, 1), (37, 1), (59, 1), (63, 1)] }, { coefficient := -1, powers := [(8, 1), (27, 1), (32, 1), (45, 1), (47, 1), (63, 1)] }, { coefficient := -2, powers := [(8, 1), (27, 1), (35, 1), (41, 1), (45, 1), (63, 1)] }, { coefficient := -1, powers := [(8, 1), (32, 1), (34, 1), (37, 1), (47, 1), (63, 1)] }, { coefficient := -2, powers := [(8, 1), (34, 1), (35, 1), (37, 1), (41, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (29, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (7, 1), (41, 1), (43, 1), (58, 1)] }, { coefficient := -1, powers := [(5, 1), (7, 1), (32, 1), (43, 1), (58, 1)] }, { coefficient := -1, powers := [(6, 1), (11, 1), (18, 1), (24, 1), (51, 1), (59, 1)] }, { coefficient := -1, powers := [(6, 1), (11, 1), (18, 1), (32, 1), (47, 1), (51, 1)] }, { coefficient := -1, powers := [(7, 1), (18, 1), (24, 1), (59, 1)] }, { coefficient := -1, powers := [(7, 1), (18, 1), (32, 1), (47, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (4, 1), (41, 1), (46, 1), (56, 1), (58, 1), (63, 1)] }, { coefficient := -1, powers := [(4, 1), (5, 1), (32, 1), (46, 1), (56, 1), (58, 1), (63, 1)] }, { coefficient := -1, powers := [(4, 1), (8, 1), (24, 1), (46, 1), (58, 1), (59, 1), (63, 1)] }, { coefficient := -1, powers := [(4, 1), (8, 1), (32, 1), (46, 1), (47, 1), (58, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(26, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (20, 1), (56, 1)] }, { coefficient := -1, powers := [(19, 1), (20, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(29, 1), (47, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(23, 1), (26, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (47, 1), (49, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(24, 1), (53, 1), (62, 1)] }, { coefficient := 1, powers := [(29, 1), (41, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (18, 1), (29, 1), (59, 1), (61, 1), (62, 1)] }, { coefficient := 1, powers := [(8, 1), (18, 1), (24, 1), (59, 1), (61, 1), (62, 1)] }, { coefficient := -1, powers := [(8, 1), (18, 1), (25, 1), (32, 1), (47, 1), (61, 1)] }, { coefficient := 1, powers := [(13, 1), (18, 1), (24, 1), (56, 1), (61, 1), (62, 1)] }, { coefficient := -1, powers := [(13, 1), (18, 1), (29, 1), (47, 1), (61, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(18, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(19, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (4, 1), (41, 1), (56, 1), (58, 1), (63, 1)] }, { coefficient := 1, powers := [(4, 1), (5, 1), (32, 1), (56, 1), (58, 1), (63, 1)] }, { coefficient := 1, powers := [(4, 1), (8, 1), (24, 1), (58, 1), (59, 1), (63, 1)] }, { coefficient := 1, powers := [(4, 1), (8, 1), (32, 1), (47, 1), (58, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (18, 1), (29, 1), (59, 1), (61, 1), (62, 1)] }, { coefficient := 2, powers := [(8, 1), (11, 1), (18, 1), (22, 1), (35, 1), (41, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (59, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (26, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (21, 1), (60, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (47, 1)] }],
  [{ coefficient := -1, powers := [(29, 1), (49, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(18, 1), (24, 1), (56, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (7, 1), (41, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (7, 1), (32, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (32, 1), (51, 1)] }, { coefficient := 1, powers := [(13, 1), (29, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (41, 1), (51, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (51, 1), (56, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (51, 1), (59, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (47, 1), (51, 1)] }, { coefficient := -2, powers := [(8, 1), (35, 1), (41, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (41, 1), (45, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (45, 1), (56, 1)] }, { coefficient := -1, powers := [(8, 1), (24, 1), (40, 1), (59, 1)] }, { coefficient := -1, powers := [(8, 1), (32, 1), (40, 1), (47, 1)] }, { coefficient := 2, powers := [(8, 1), (35, 1), (41, 1), (45, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (29, 1), (59, 1), (61, 1), (62, 1)] }, { coefficient := -2, powers := [(8, 1), (11, 1), (22, 1), (35, 1), (41, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (29, 1), (59, 1), (61, 1), (62, 1)] }, { coefficient := -1, powers := [(8, 1), (24, 1), (59, 1), (61, 1), (62, 1)] }, { coefficient := 1, powers := [(8, 1), (25, 1), (32, 1), (47, 1), (61, 1)] }, { coefficient := -1, powers := [(13, 1), (24, 1), (56, 1), (61, 1), (62, 1)] }, { coefficient := 1, powers := [(13, 1), (29, 1), (47, 1), (61, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(29, 1), (40, 1), (62, 1)] }, { coefficient := -1, powers := [(29, 1), (51, 1), (62, 1)] }, { coefficient := 1, powers := [(29, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (40, 1), (62, 1)] }, { coefficient := 1, powers := [(24, 1), (51, 1), (62, 1)] }, { coefficient := -1, powers := [(24, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (32, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (41, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (40, 1), (41, 1), (56, 1), (63, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (40, 1), (56, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(41, 1), (62, 1)] }],
  [{ coefficient := 2, powers := [(8, 1), (34, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(53, 1)] }],
  [{ coefficient := -1, powers := [(47, 1)] }],
  [{ coefficient := 1, powers := [(19, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (11, 1), (24, 1), (51, 1), (59, 1)] }, { coefficient := -1, powers := [(8, 1), (11, 1), (32, 1), (47, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (11, 1), (24, 1), (51, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (11, 1), (32, 1), (47, 1), (51, 1)] }, { coefficient := 1, powers := [(7, 1), (24, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (32, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(13, 1)] }],
  [{ coefficient := 2, powers := [(8, 1), (22, 1), (35, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (16, 1), (41, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (16, 1), (32, 1), (56, 1)] }, { coefficient := 1, powers := [(8, 1), (11, 1), (24, 1), (59, 1)] }, { coefficient := 1, powers := [(8, 1), (11, 1), (32, 1), (47, 1)] }, { coefficient := 1, powers := [(8, 1), (16, 1), (24, 1), (59, 1)] }, { coefficient := 1, powers := [(8, 1), (16, 1), (32, 1), (47, 1)] }, { coefficient := 2, powers := [(8, 1), (16, 1), (35, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (41, 1), (56, 1)] }, { coefficient := -1, powers := [(5, 1), (32, 1), (56, 1)] }, { coefficient := -1, powers := [(8, 1), (24, 1), (59, 1)] }, { coefficient := -1, powers := [(8, 1), (32, 1), (47, 1)] }, { coefficient := -2, powers := [(8, 1), (35, 1), (41, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(2, 1), (38, 1), (59, 1)] }, { coefficient := -1, powers := [(2, 1), (41, 1), (56, 1)] }, { coefficient := -1, powers := [(2, 1), (47, 1), (53, 1)] }, { coefficient := -1, powers := [(13, 1), (29, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (37, 1), (41, 1), (56, 1), (58, 1)] }, { coefficient := -1, powers := [(2, 1), (40, 1), (41, 2), (55, 1), (56, 1), (63, 1)] }, { coefficient := -1, powers := [(2, 1), (41, 1), (45, 1), (51, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (37, 1), (56, 1), (58, 1)] }, { coefficient := -1, powers := [(5, 1), (32, 1), (40, 1), (41, 1), (55, 1), (56, 1), (63, 1)] }, { coefficient := -1, powers := [(5, 1), (32, 1), (45, 1), (51, 1), (56, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (37, 1), (58, 1), (59, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (40, 1), (51, 1), (59, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (40, 1), (55, 1), (59, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (37, 1), (47, 1), (58, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (40, 1), (47, 1), (51, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (40, 1), (47, 1), (55, 1)] }, { coefficient := 2, powers := [(8, 1), (35, 1), (37, 1), (41, 1), (58, 1)] }, { coefficient := 2, powers := [(8, 1), (35, 1), (40, 1), (41, 1), (55, 1)] }, { coefficient := 2, powers := [(8, 1), (35, 1), (41, 1), (45, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (29, 1), (45, 1), (59, 1), (62, 1)] }, { coefficient := -1, powers := [(5, 1), (29, 1), (51, 1), (59, 1), (62, 1)] }, { coefficient := 2, powers := [(8, 1), (11, 1), (22, 1), (35, 1), (41, 1), (45, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (51, 1), (59, 1), (62, 1)] }, { coefficient := -1, powers := [(8, 1), (25, 1), (32, 1), (47, 1), (51, 1)] }, { coefficient := 1, powers := [(13, 1), (24, 1), (51, 1), (56, 1), (62, 1)] }, { coefficient := -1, powers := [(13, 1), (29, 1), (47, 1), (51, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (41, 1), (56, 1)] }, { coefficient := -1, powers := [(8, 1), (24, 1), (59, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (41, 1)] }, { coefficient := -1, powers := [(13, 1), (24, 1), (56, 1)] }, { coefficient := 1, powers := [(13, 1), (29, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (29, 1), (41, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (4, 1), (27, 1), (41, 1), (56, 1), (58, 1)] }, { coefficient := -1, powers := [(2, 1), (7, 1), (34, 1), (40, 1), (41, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (16, 1), (22, 1), (41, 1), (51, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (16, 1), (22, 1), (41, 1), (55, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (16, 1), (27, 1), (41, 1), (45, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (16, 1), (34, 1), (37, 1), (41, 1), (56, 1)] }, { coefficient := -1, powers := [(4, 1), (5, 1), (27, 1), (32, 1), (56, 1), (58, 1)] }, { coefficient := -1, powers := [(4, 1), (8, 1), (24, 1), (27, 1), (58, 1), (59, 1)] }, { coefficient := -1, powers := [(4, 1), (8, 1), (27, 1), (32, 1), (47, 1), (58, 1)] }, { coefficient := -1, powers := [(5, 1), (7, 1), (32, 1), (34, 1), (40, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (16, 1), (22, 1), (32, 1), (51, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (16, 1), (22, 1), (32, 1), (55, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (16, 1), (27, 1), (32, 1), (45, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (16, 1), (32, 1), (34, 1), (37, 1), (56, 1)] }, { coefficient := 1, powers := [(8, 1), (16, 1), (22, 1), (24, 1), (51, 1), (59, 1)] }, { coefficient := 1, powers := [(8, 1), (16, 1), (22, 1), (24, 1), (55, 1), (59, 1)] }, { coefficient := 1, powers := [(8, 1), (16, 1), (22, 1), (32, 1), (47, 1), (51, 1)] }, { coefficient := 1, powers := [(8, 1), (16, 1), (22, 1), (32, 1), (47, 1), (55, 1)] }, { coefficient := 2, powers := [(8, 1), (16, 1), (22, 1), (35, 1), (40, 1), (41, 1)] }, { coefficient := 2, powers := [(8, 1), (16, 1), (22, 1), (35, 1), (41, 1), (51, 1)] }, { coefficient := 1, powers := [(8, 1), (16, 1), (24, 1), (27, 1), (45, 1), (59, 1)] }, { coefficient := 1, powers := [(8, 1), (16, 1), (24, 1), (34, 1), (37, 1), (59, 1)] }, { coefficient := 1, powers := [(8, 1), (16, 1), (27, 1), (32, 1), (45, 1), (47, 1)] }, { coefficient := 2, powers := [(8, 1), (16, 1), (27, 1), (35, 1), (41, 1), (45, 1)] }, { coefficient := 1, powers := [(8, 1), (16, 1), (32, 1), (34, 1), (37, 1), (47, 1)] }, { coefficient := 2, powers := [(8, 1), (16, 1), (34, 1), (35, 1), (37, 1), (41, 1)] }]
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
    (values : Fin 64 → R) :
    ¬ ∀ index : Fin 54,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component20.SelectedLeafB5_3.selectedHasNoCommonZero

end Krenn.Component20.SelectedLeafB5_3
