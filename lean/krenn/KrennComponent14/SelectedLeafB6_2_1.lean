import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component14.SelectedLeafB6_2_1

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "ca6c7be4257bd989f36949d89cf466cfda320ea13d80a7b23e3acb0336a0c8ca"
def certificateSHA256 : String := "46ac6002134e20673e0146b164c982326ccd8eb923ccaf2b67188b9131bb7635"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 43 → Fin 643 := ![
  5,
  8,
  19,
  21,
  22,
  23,
  24,
  25,
  164,
  183,
  191,
  192,
  197,
  198,
  231,
  282,
  313,
  348,
  349,
  350,
  351,
  360,
  362,
  456,
  457,
  458,
  460,
  470,
  501,
  556,
  563,
  575,
  576,
  621,
  631,
  633,
  635,
  636,
  637,
  639,
  640,
  641,
  642
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 43 → SparsePoly (Fin 63) := ![
  [{ coefficient := 1, powers := [(5, 1), (32, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (29, 1)] }],
  [{ coefficient := 1, powers := [(15, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (18, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(31, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(34, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (52, 1)] }, { coefficient := 1, powers := [(15, 1), (19, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (39, 1)] }, { coefficient := 1, powers := [(16, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (50, 1)] }, { coefficient := 1, powers := [(22, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (51, 1)] }, { coefficient := 1, powers := [(28, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(42, 1), (52, 1)] }, { coefficient := 1, powers := [(48, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(44, 1), (48, 1)] }, { coefficient := 1, powers := [(48, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (32, 1), (49, 1)] }, { coefficient := 1, powers := [(5, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (17, 1), (54, 1)] }, { coefficient := 1, powers := [(12, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (23, 1), (39, 1)] }, { coefficient := 1, powers := [(16, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (46, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (52, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1)] }, { coefficient := 1, powers := [(12, 1), (28, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (58, 1)] }, { coefficient := 1, powers := [(12, 1), (46, 1)] }, { coefficient := 1, powers := [(16, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (58, 1)] }, { coefficient := 1, powers := [(12, 1), (55, 1)] }, { coefficient := 1, powers := [(16, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1), (50, 1)] }, { coefficient := 1, powers := [(17, 1), (42, 1), (50, 1)] }, { coefficient := 1, powers := [(42, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1), (48, 1)] }, { coefficient := 1, powers := [(23, 1), (44, 1), (48, 1)] }, { coefficient := 1, powers := [(48, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (51, 1)] }, { coefficient := 1, powers := [(3, 1), (24, 1), (57, 1)] }, { coefficient := 1, powers := [(17, 1), (51, 1)] }, { coefficient := 1, powers := [(24, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (34, 1)] }, { coefficient := 1, powers := [(21, 1), (42, 1)] }, { coefficient := 1, powers := [(27, 1), (42, 1)] }, { coefficient := 1, powers := [(34, 1), (35, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (31, 1)] }, { coefficient := 1, powers := [(21, 1), (48, 1)] }, { coefficient := 1, powers := [(27, 1), (48, 1)] }, { coefficient := 1, powers := [(31, 1), (35, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (52, 1)] }, { coefficient := 1, powers := [(28, 1), (40, 1)] }, { coefficient := 1, powers := [(28, 1), (45, 1), (48, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1), (51, 1)] }, { coefficient := 1, powers := [(17, 1), (42, 1), (51, 1)] }, { coefficient := 1, powers := [(17, 1), (55, 1)] }, { coefficient := 1, powers := [(24, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (29, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (29, 1), (46, 1)] }, { coefficient := 1, powers := [(16, 1), (18, 1), (24, 1), (49, 1)] }, { coefficient := 1, powers := [(16, 1), (29, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (50, 1)] }, { coefficient := 1, powers := [(3, 1), (57, 1)] }, { coefficient := 1, powers := [(17, 1), (50, 1)] }, { coefficient := 1, powers := [(17, 1), (54, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1), (49, 1)] }, { coefficient := 1, powers := [(9, 1), (44, 1)] }, { coefficient := 1, powers := [(9, 1), (54, 1)] }, { coefficient := 1, powers := [(29, 1), (36, 1)] }, { coefficient := 1, powers := [(49, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (41, 1)] }, { coefficient := 1, powers := [(3, 1), (32, 1)] }, { coefficient := 1, powers := [(13, 1), (17, 1)] }, { coefficient := 1, powers := [(17, 1), (53, 1)] }, { coefficient := 1, powers := [(23, 1), (41, 1)] }, { coefficient := 1, powers := [(32, 1), (35, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1)] }, { coefficient := 1, powers := [(6, 1), (29, 1)] }, { coefficient := 1, powers := [(9, 1), (23, 1)] }, { coefficient := 1, powers := [(17, 1), (47, 1)] }, { coefficient := 1, powers := [(23, 1), (38, 1)] }, { coefficient := 1, powers := [(29, 1), (35, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (38, 1), (54, 1)] }, { coefficient := 1, powers := [(0, 1), (49, 1)] }, { coefficient := 1, powers := [(3, 1), (29, 1), (54, 1)] }, { coefficient := 1, powers := [(9, 1), (17, 1), (54, 1)] }, { coefficient := 1, powers := [(9, 1)] }, { coefficient := 1, powers := [(17, 1), (49, 1)] }, { coefficient := 1, powers := [(38, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (35, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (38, 1), (53, 1)] }, { coefficient := 1, powers := [(0, 1), (41, 1), (47, 1)] }, { coefficient := 1, powers := [(3, 1), (23, 1), (56, 1)] }, { coefficient := 1, powers := [(3, 1), (29, 1), (53, 1)] }, { coefficient := 1, powers := [(3, 1), (32, 1), (47, 1)] }, { coefficient := 1, powers := [(6, 1), (17, 1), (56, 1)] }, { coefficient := 1, powers := [(6, 1), (29, 1), (41, 1)] }, { coefficient := 1, powers := [(6, 1), (32, 1), (38, 1)] }, { coefficient := 1, powers := [(9, 1), (17, 1), (53, 1)] }, { coefficient := 1, powers := [(9, 1), (23, 1), (41, 1)] }, { coefficient := 1, powers := [(9, 1), (32, 1), (35, 1)] }, { coefficient := 1, powers := [(13, 1), (17, 1), (47, 1)] }, { coefficient := 1, powers := [(13, 1), (23, 1), (38, 1)] }, { coefficient := 1, powers := [(13, 1), (29, 1), (35, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (37, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (40, 1), (55, 1)] }, { coefficient := 1, powers := [(2, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(5, 1), (28, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (52, 1)] }, { coefficient := 1, powers := [(8, 1), (22, 1), (58, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1), (46, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (40, 1)] }, { coefficient := 1, powers := [(12, 1), (22, 1), (55, 1)] }, { coefficient := 1, powers := [(12, 1), (28, 1), (46, 1)] }, { coefficient := 1, powers := [(12, 1), (34, 1), (37, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1), (52, 1)] }, { coefficient := 1, powers := [(16, 1), (28, 1), (40, 1)] }, { coefficient := 1, powers := [(16, 1), (31, 1), (37, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1), (60, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(38, 1)] }],
  [{ coefficient := 1, powers := [(40, 1)] }],
  [{ coefficient := 1, powers := [(53, 1)] }],
  [{ coefficient := 1, powers := [(54, 1)] }],
  [{ coefficient := 1, powers := [(55, 1), (62, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 43 → SparsePoly (Fin 63) := ![
  [{ coefficient := 1, powers := [(0, 1), (6, 1), (31, 1), (49, 1), (55, 1)] }, { coefficient := -1, powers := [(3, 1), (9, 1), (31, 1), (55, 1)] }, { coefficient := -1, powers := [(3, 1), (9, 1), (34, 1), (52, 1)] }, { coefficient := -1, powers := [(3, 1), (23, 1), (31, 1), (49, 1), (55, 1)] }, { coefficient := 1, powers := [(3, 1), (31, 1), (47, 1), (55, 1)] }, { coefficient := 1, powers := [(3, 1), (34, 1), (47, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (13, 1), (31, 1), (46, 1)] }, { coefficient := -1, powers := [(6, 1), (31, 1), (41, 1), (46, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (6, 1), (16, 1), (19, 1), (22, 1), (56, 1), (60, 1)] }, { coefficient := -1, powers := [(3, 1), (9, 1), (16, 1), (19, 1), (22, 1), (32, 1), (60, 1)] }, { coefficient := 1, powers := [(3, 1), (16, 1), (19, 1), (22, 1), (23, 1), (56, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (13, 1), (24, 1), (31, 1), (49, 1)] }, { coefficient := -1, powers := [(6, 1), (24, 1), (31, 1), (41, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (31, 1), (32, 1), (37, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (21, 1), (37, 1), (56, 1)] }, { coefficient := -1, powers := [(0, 1), (27, 1), (37, 1), (56, 1)] }, { coefficient := -1, powers := [(13, 1), (21, 1), (29, 1), (37, 1)] }, { coefficient := -1, powers := [(13, 1), (27, 1), (29, 1), (37, 1)] }, { coefficient := 1, powers := [(21, 1), (29, 1), (37, 1), (41, 1)] }, { coefficient := 1, powers := [(27, 1), (29, 1), (37, 1), (41, 1)] }],
  [{ coefficient := -1, powers := [(0, 2), (5, 1), (29, 1), (41, 1), (55, 1)] }, { coefficient := -1, powers := [(0, 2), (16, 1), (29, 1), (37, 1), (41, 1)] }, { coefficient := -1, powers := [(0, 1), (5, 1), (17, 1), (29, 1), (41, 1), (55, 1)] }, { coefficient := -1, powers := [(0, 1), (5, 1), (23, 1), (29, 1), (41, 1), (55, 1)] }, { coefficient := -1, powers := [(0, 1), (16, 1), (17, 1), (29, 1), (37, 1), (41, 1)] }, { coefficient := -1, powers := [(0, 1), (16, 1), (23, 1), (29, 1), (37, 1), (41, 1)] }, { coefficient := -1, powers := [(5, 1), (17, 1), (23, 1), (29, 1), (41, 1), (55, 1)] }, { coefficient := -1, powers := [(16, 1), (17, 1), (23, 1), (29, 1), (37, 1), (41, 1)] }],
  [{ coefficient := -1, powers := [(0, 2), (5, 1), (29, 1), (41, 1), (52, 1)] }, { coefficient := -1, powers := [(0, 1), (5, 1), (17, 1), (29, 1), (41, 1), (52, 1)] }, { coefficient := -1, powers := [(0, 1), (5, 1), (23, 1), (29, 1), (41, 1), (52, 1)] }, { coefficient := -1, powers := [(5, 1), (17, 1), (23, 1), (29, 1), (41, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (6, 1), (16, 1), (22, 1), (56, 1), (60, 1)] }, { coefficient := 1, powers := [(3, 1), (9, 1), (16, 1), (22, 1), (32, 1), (60, 1)] }, { coefficient := -1, powers := [(3, 1), (16, 1), (22, 1), (23, 1), (56, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (3, 1), (22, 1), (23, 1), (52, 1), (56, 1)] }, { coefficient := -1, powers := [(3, 1), (13, 1), (22, 1), (23, 1), (29, 1), (52, 1)] }, { coefficient := 1, powers := [(3, 1), (22, 1), (23, 2), (52, 1), (56, 1)] }, { coefficient := 1, powers := [(3, 1), (22, 1), (23, 1), (29, 1), (41, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (3, 1), (16, 1), (23, 1), (52, 1), (56, 1)] }, { coefficient := 1, powers := [(3, 1), (13, 1), (16, 1), (23, 1), (29, 1), (52, 1)] }, { coefficient := -1, powers := [(3, 1), (16, 1), (23, 2), (52, 1), (56, 1)] }, { coefficient := -1, powers := [(3, 1), (16, 1), (23, 1), (29, 1), (41, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (6, 1), (16, 1), (48, 1), (56, 1)] }, { coefficient := 1, powers := [(3, 1), (9, 1), (16, 1), (32, 1), (48, 1)] }, { coefficient := -1, powers := [(3, 1), (16, 1), (23, 1), (48, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (5, 1), (21, 1), (56, 1)] }, { coefficient := -1, powers := [(0, 1), (5, 1), (27, 1), (56, 1)] }, { coefficient := -1, powers := [(5, 1), (13, 1), (21, 1), (29, 1)] }, { coefficient := -1, powers := [(5, 1), (13, 1), (27, 1), (29, 1)] }, { coefficient := 1, powers := [(5, 1), (21, 1), (29, 1), (41, 1)] }, { coefficient := 1, powers := [(5, 1), (27, 1), (29, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(0, 2), (6, 1), (16, 1), (22, 1), (51, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (3, 1), (9, 1), (16, 1), (22, 1), (32, 1), (51, 1)] }, { coefficient := -1, powers := [(0, 1), (3, 1), (16, 1), (22, 1), (23, 1), (51, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (6, 1), (16, 1), (22, 1), (23, 1), (51, 1), (56, 1)] }, { coefficient := 1, powers := [(3, 1), (9, 1), (16, 1), (22, 1), (23, 1), (32, 1), (51, 1)] }, { coefficient := -1, powers := [(3, 1), (16, 1), (22, 1), (23, 2), (51, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (6, 1), (31, 1), (55, 1)] }, { coefficient := 1, powers := [(3, 1), (23, 1), (31, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(0, 2), (28, 1), (29, 1), (36, 1), (41, 1), (46, 1)] }, { coefficient := -1, powers := [(0, 2), (29, 1), (34, 1), (36, 1), (37, 1), (41, 1)] }, { coefficient := 1, powers := [(0, 1), (17, 1), (28, 1), (29, 1), (36, 1), (41, 1), (46, 1)] }, { coefficient := -1, powers := [(0, 1), (17, 1), (29, 1), (34, 1), (36, 1), (37, 1), (41, 1)] }, { coefficient := 1, powers := [(0, 1), (23, 1), (28, 1), (29, 1), (36, 1), (41, 1), (46, 1)] }, { coefficient := -1, powers := [(0, 1), (23, 1), (29, 1), (34, 1), (36, 1), (37, 1), (41, 1)] }, { coefficient := -1, powers := [(0, 1), (28, 1), (35, 1), (46, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (34, 1), (35, 1), (37, 1), (56, 1)] }, { coefficient := 1, powers := [(3, 1), (9, 1), (28, 1), (32, 1), (46, 1)] }, { coefficient := -1, powers := [(3, 1), (9, 1), (32, 1), (34, 1), (37, 1)] }, { coefficient := -1, powers := [(3, 1), (23, 1), (28, 1), (46, 1), (56, 1)] }, { coefficient := 1, powers := [(3, 1), (23, 1), (34, 1), (37, 1), (56, 1)] }, { coefficient := -1, powers := [(3, 1), (28, 1), (32, 1), (46, 1), (47, 1)] }, { coefficient := 1, powers := [(3, 1), (32, 1), (34, 1), (37, 1), (47, 1)] }, { coefficient := -1, powers := [(13, 1), (28, 1), (29, 1), (35, 1), (46, 1)] }, { coefficient := 1, powers := [(13, 1), (29, 1), (34, 1), (35, 1), (37, 1)] }, { coefficient := 1, powers := [(17, 1), (23, 1), (28, 1), (29, 1), (36, 1), (41, 1), (46, 1)] }, { coefficient := -1, powers := [(17, 1), (23, 1), (29, 1), (34, 1), (36, 1), (37, 1), (41, 1)] }, { coefficient := 1, powers := [(28, 1), (29, 1), (35, 1), (41, 1), (46, 1)] }, { coefficient := -1, powers := [(29, 1), (34, 1), (35, 1), (37, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (3, 1), (22, 1), (52, 1), (56, 1)] }, { coefficient := 1, powers := [(3, 1), (13, 1), (22, 1), (29, 1), (52, 1)] }, { coefficient := -1, powers := [(3, 1), (22, 1), (23, 1), (52, 1), (56, 1)] }, { coefficient := -1, powers := [(3, 1), (22, 1), (29, 1), (41, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (3, 1), (52, 1), (56, 1)] }, { coefficient := -1, powers := [(3, 1), (13, 1), (29, 1), (52, 1)] }, { coefficient := 1, powers := [(3, 1), (23, 1), (52, 1), (56, 1)] }, { coefficient := 1, powers := [(3, 1), (29, 1), (41, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(0, 2), (29, 1), (36, 1), (41, 1), (46, 1)] }, { coefficient := -1, powers := [(0, 1), (17, 1), (29, 1), (36, 1), (41, 1), (46, 1)] }, { coefficient := -1, powers := [(0, 1), (23, 1), (29, 1), (36, 1), (41, 1), (46, 1)] }, { coefficient := 1, powers := [(0, 1), (35, 1), (46, 1), (56, 1)] }, { coefficient := -1, powers := [(3, 1), (9, 1), (32, 1), (46, 1)] }, { coefficient := 1, powers := [(3, 1), (23, 1), (46, 1), (56, 1)] }, { coefficient := 1, powers := [(3, 1), (32, 1), (46, 1), (47, 1)] }, { coefficient := 1, powers := [(13, 1), (29, 1), (35, 1), (46, 1)] }, { coefficient := -1, powers := [(17, 1), (23, 1), (29, 1), (36, 1), (41, 1), (46, 1)] }, { coefficient := -1, powers := [(29, 1), (35, 1), (41, 1), (46, 1)] }],
  [{ coefficient := -1, powers := [(0, 2), (28, 1), (29, 1), (36, 1), (41, 1)] }, { coefficient := -1, powers := [(0, 1), (17, 1), (28, 1), (29, 1), (36, 1), (41, 1)] }, { coefficient := -1, powers := [(0, 1), (23, 1), (28, 1), (29, 1), (36, 1), (41, 1)] }, { coefficient := 1, powers := [(0, 1), (28, 1), (35, 1), (56, 1)] }, { coefficient := -1, powers := [(3, 1), (9, 1), (28, 1), (32, 1)] }, { coefficient := 1, powers := [(3, 1), (23, 1), (28, 1), (56, 1)] }, { coefficient := 1, powers := [(3, 1), (28, 1), (32, 1), (47, 1)] }, { coefficient := 1, powers := [(13, 1), (28, 1), (29, 1), (35, 1)] }, { coefficient := -1, powers := [(17, 1), (23, 1), (28, 1), (29, 1), (36, 1), (41, 1)] }, { coefficient := -1, powers := [(28, 1), (29, 1), (35, 1), (41, 1)] }],
  [{ coefficient := -1, powers := [(0, 2), (22, 1), (29, 1), (36, 1), (41, 1)] }, { coefficient := -1, powers := [(0, 1), (17, 1), (22, 1), (29, 1), (36, 1), (41, 1)] }, { coefficient := -1, powers := [(0, 1), (22, 1), (23, 1), (29, 1), (36, 1), (41, 1)] }, { coefficient := 1, powers := [(0, 1), (22, 1), (35, 1), (56, 1)] }, { coefficient := -1, powers := [(3, 1), (9, 1), (22, 1), (32, 1)] }, { coefficient := 1, powers := [(3, 1), (22, 1), (23, 1), (56, 1)] }, { coefficient := 1, powers := [(3, 1), (22, 1), (32, 1), (47, 1)] }, { coefficient := 1, powers := [(13, 1), (22, 1), (29, 1), (35, 1)] }, { coefficient := -1, powers := [(17, 1), (22, 1), (23, 1), (29, 1), (36, 1), (41, 1)] }, { coefficient := -1, powers := [(22, 1), (29, 1), (35, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (9, 1), (24, 1), (41, 1), (44, 1), (62, 1)] }, { coefficient := -1, powers := [(6, 1), (24, 1), (56, 1), (62, 1)] }, { coefficient := 1, powers := [(9, 1), (13, 1), (24, 1), (62, 1)] }, { coefficient := 1, powers := [(9, 1), (23, 1), (24, 1), (41, 1), (44, 1), (62, 1)] }, { coefficient := -1, powers := [(13, 1), (24, 1), (47, 1), (62, 1)] }, { coefficient := 1, powers := [(24, 1), (41, 1), (47, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (6, 1), (16, 1), (22, 1), (51, 1), (56, 1)] }, { coefficient := -1, powers := [(3, 1), (9, 1), (16, 1), (22, 1), (32, 1), (51, 1)] }, { coefficient := 1, powers := [(3, 1), (16, 1), (22, 1), (23, 1), (51, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (9, 1), (41, 1), (42, 1), (44, 1), (62, 1)] }, { coefficient := -1, powers := [(6, 1), (42, 1), (56, 1), (62, 1)] }, { coefficient := 1, powers := [(9, 1), (13, 1), (42, 1), (62, 1)] }, { coefficient := 1, powers := [(9, 1), (23, 1), (41, 1), (42, 1), (44, 1), (62, 1)] }, { coefficient := -1, powers := [(13, 1), (42, 1), (47, 1), (62, 1)] }, { coefficient := 1, powers := [(41, 1), (42, 1), (47, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (5, 1), (52, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (13, 1), (29, 1), (52, 1)] }, { coefficient := -1, powers := [(5, 1), (29, 1), (41, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (5, 1), (55, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (16, 1), (37, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (13, 1), (29, 1), (55, 1)] }, { coefficient := -1, powers := [(5, 1), (29, 1), (41, 1), (55, 1)] }, { coefficient := 1, powers := [(13, 1), (16, 1), (29, 1), (37, 1)] }, { coefficient := -1, powers := [(16, 1), (29, 1), (37, 1), (41, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (6, 1), (16, 1), (56, 1)] }, { coefficient := -1, powers := [(3, 1), (9, 1), (16, 1), (32, 1)] }, { coefficient := 1, powers := [(3, 1), (16, 1), (23, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (9, 1), (41, 1), (44, 1), (62, 1)] }, { coefficient := 1, powers := [(6, 1), (56, 1), (62, 1)] }, { coefficient := -1, powers := [(9, 1), (13, 1), (62, 1)] }, { coefficient := -1, powers := [(9, 1), (23, 1), (41, 1), (44, 1), (62, 1)] }, { coefficient := 1, powers := [(13, 1), (47, 1), (62, 1)] }, { coefficient := -1, powers := [(41, 1), (47, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (13, 1), (31, 1)] }, { coefficient := 1, powers := [(6, 1), (31, 1), (41, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (9, 1), (24, 1), (41, 1), (42, 1), (44, 1), (62, 1)] }, { coefficient := 1, powers := [(6, 1), (24, 1), (42, 1), (56, 1), (62, 1)] }, { coefficient := -1, powers := [(9, 1), (13, 1), (24, 1), (42, 1), (62, 1)] }, { coefficient := -1, powers := [(9, 1), (23, 1), (24, 1), (41, 1), (42, 1), (44, 1), (62, 1)] }, { coefficient := 1, powers := [(13, 1), (24, 1), (42, 1), (47, 1), (62, 1)] }, { coefficient := -1, powers := [(24, 1), (41, 1), (42, 1), (47, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(0, 2), (41, 1)] }, { coefficient := 1, powers := [(0, 1), (17, 1), (41, 1)] }, { coefficient := 1, powers := [(0, 1), (23, 1), (41, 1)] }, { coefficient := 1, powers := [(17, 1), (23, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(9, 1)] }],
  [{ coefficient := 1, powers := [(41, 1)] }],
  [{ coefficient := -1, powers := [(0, 2), (41, 1), (44, 1)] }, { coefficient := -1, powers := [(0, 1), (23, 1), (41, 1), (44, 1)] }, { coefficient := -1, powers := [(0, 1), (41, 1)] }, { coefficient := -1, powers := [(23, 1), (41, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 2), (29, 1), (36, 1), (41, 1)] }, { coefficient := 1, powers := [(0, 1), (17, 1), (29, 1), (36, 1), (41, 1)] }, { coefficient := 1, powers := [(0, 1), (23, 1), (29, 1), (36, 1), (41, 1)] }, { coefficient := -1, powers := [(0, 1), (35, 1), (56, 1)] }, { coefficient := 1, powers := [(3, 1), (9, 1), (32, 1)] }, { coefficient := -1, powers := [(3, 1), (23, 1), (56, 1)] }, { coefficient := -1, powers := [(3, 1), (32, 1), (47, 1)] }, { coefficient := -1, powers := [(13, 1), (29, 1), (35, 1)] }, { coefficient := 1, powers := [(17, 1), (23, 1), (29, 1), (36, 1), (41, 1)] }, { coefficient := 1, powers := [(29, 1), (35, 1), (41, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (6, 1), (16, 1), (22, 1), (52, 1), (56, 1)] }, { coefficient := -1, powers := [(3, 1), (9, 1), (16, 1), (22, 1), (32, 1), (52, 1)] }, { coefficient := 1, powers := [(3, 1), (16, 1), (22, 1), (23, 1), (52, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [(0, 2), (29, 1), (36, 1), (37, 1), (41, 1), (58, 1)] }, { coefficient := -1, powers := [(0, 2), (29, 1), (36, 1), (40, 1), (41, 1), (55, 1)] }, { coefficient := 1, powers := [(0, 1), (3, 1), (46, 1), (52, 1), (56, 1)] }, { coefficient := -1, powers := [(0, 1), (17, 1), (29, 1), (36, 1), (37, 1), (41, 1), (58, 1)] }, { coefficient := -1, powers := [(0, 1), (17, 1), (29, 1), (36, 1), (40, 1), (41, 1), (55, 1)] }, { coefficient := -1, powers := [(0, 1), (23, 1), (29, 1), (36, 1), (37, 1), (41, 1), (58, 1)] }, { coefficient := -1, powers := [(0, 1), (23, 1), (29, 1), (36, 1), (40, 1), (41, 1), (55, 1)] }, { coefficient := 1, powers := [(0, 1), (35, 1), (37, 1), (56, 1), (58, 1)] }, { coefficient := 1, powers := [(0, 1), (35, 1), (40, 1), (55, 1), (56, 1)] }, { coefficient := -1, powers := [(3, 1), (9, 1), (32, 1), (37, 1), (58, 1)] }, { coefficient := -1, powers := [(3, 1), (9, 1), (32, 1), (40, 1), (55, 1)] }, { coefficient := 1, powers := [(3, 1), (13, 1), (29, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(3, 1), (23, 1), (37, 1), (56, 1), (58, 1)] }, { coefficient := 1, powers := [(3, 1), (23, 1), (40, 1), (55, 1), (56, 1)] }, { coefficient := -1, powers := [(3, 1), (23, 1), (46, 1), (52, 1), (56, 1)] }, { coefficient := -1, powers := [(3, 1), (29, 1), (41, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(3, 1), (32, 1), (37, 1), (47, 1), (58, 1)] }, { coefficient := 1, powers := [(3, 1), (32, 1), (40, 1), (47, 1), (55, 1)] }, { coefficient := 1, powers := [(13, 1), (29, 1), (35, 1), (37, 1), (58, 1)] }, { coefficient := 1, powers := [(13, 1), (29, 1), (35, 1), (40, 1), (55, 1)] }, { coefficient := -1, powers := [(17, 1), (23, 1), (29, 1), (36, 1), (37, 1), (41, 1), (58, 1)] }, { coefficient := -1, powers := [(17, 1), (23, 1), (29, 1), (36, 1), (40, 1), (41, 1), (55, 1)] }, { coefficient := -1, powers := [(29, 1), (35, 1), (37, 1), (41, 1), (58, 1)] }, { coefficient := -1, powers := [(29, 1), (35, 1), (40, 1), (41, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(0, 2), (41, 1), (44, 1)] }, { coefficient := 1, powers := [(0, 1), (23, 1), (41, 1), (44, 1)] }, { coefficient := 1, powers := [(0, 1), (41, 1)] }, { coefficient := 1, powers := [(6, 1), (32, 1)] }, { coefficient := 1, powers := [(13, 1), (23, 1)] }],
  [{ coefficient := -1, powers := [(0, 2), (8, 1), (29, 1), (34, 1), (36, 1), (41, 1)] }, { coefficient := 1, powers := [(0, 1), (6, 1), (16, 1), (28, 1), (56, 1)] }, { coefficient := -1, powers := [(0, 1), (8, 1), (17, 1), (29, 1), (34, 1), (36, 1), (41, 1)] }, { coefficient := -1, powers := [(0, 1), (8, 1), (23, 1), (29, 1), (34, 1), (36, 1), (41, 1)] }, { coefficient := 1, powers := [(0, 1), (8, 1), (34, 1), (35, 1), (56, 1)] }, { coefficient := -1, powers := [(3, 1), (8, 1), (9, 1), (32, 1), (34, 1)] }, { coefficient := 1, powers := [(3, 1), (8, 1), (23, 1), (34, 1), (56, 1)] }, { coefficient := 1, powers := [(3, 1), (8, 1), (32, 1), (34, 1), (47, 1)] }, { coefficient := 1, powers := [(3, 1), (9, 1), (16, 1), (28, 1), (32, 1)] }, { coefficient := -1, powers := [(3, 1), (16, 1), (23, 1), (28, 1), (56, 1)] }, { coefficient := 1, powers := [(8, 1), (13, 1), (29, 1), (34, 1), (35, 1)] }, { coefficient := -1, powers := [(8, 1), (17, 1), (23, 1), (29, 1), (34, 1), (36, 1), (41, 1)] }, { coefficient := -1, powers := [(8, 1), (29, 1), (34, 1), (35, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (38, 1)] }, { coefficient := 1, powers := [(3, 1), (29, 1)] }],
  [{ coefficient := 1, powers := [(0, 3), (38, 1), (41, 1), (44, 1)] }, { coefficient := 1, powers := [(0, 2), (3, 1), (29, 1), (41, 1), (44, 1)] }, { coefficient := -1, powers := [(0, 2), (6, 1), (16, 1), (22, 1), (48, 1), (51, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 2), (9, 1), (17, 1), (41, 1), (44, 1)] }, { coefficient := -1, powers := [(0, 2), (9, 1), (41, 1)] }, { coefficient := -1, powers := [(0, 2), (12, 1), (17, 1), (28, 1), (29, 1), (36, 1), (41, 1), (46, 1)] }, { coefficient := 1, powers := [(0, 2), (12, 1), (17, 1), (29, 1), (34, 1), (36, 1), (37, 1), (41, 1)] }, { coefficient := 1, powers := [(0, 2), (23, 1), (38, 1), (41, 1), (44, 1)] }, { coefficient := 1, powers := [(0, 2), (38, 1), (41, 1)] }, { coefficient := -1, powers := [(0, 1), (3, 1), (9, 1), (16, 1), (22, 1), (32, 1), (48, 1), (51, 1)] }, { coefficient := 1, powers := [(0, 1), (3, 1), (16, 1), (22, 1), (23, 1), (48, 1), (51, 1), (56, 1)] }, { coefficient := -1, powers := [(0, 1), (3, 1), (16, 1), (22, 1), (23, 1), (52, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (3, 1), (23, 1), (29, 1), (41, 1), (44, 1)] }, { coefficient := 1, powers := [(0, 1), (3, 1), (29, 1), (41, 1)] }, { coefficient := -1, powers := [(0, 1), (6, 1), (16, 1), (22, 1), (23, 1), (48, 1), (51, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (9, 1), (17, 1), (23, 1), (41, 1), (44, 1)] }, { coefficient := 1, powers := [(0, 1), (9, 1), (17, 1), (24, 1), (41, 1), (42, 1), (44, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 1), (9, 1), (23, 1), (41, 1)] }, { coefficient := -1, powers := [(0, 1), (12, 1), (17, 2), (28, 1), (29, 1), (36, 1), (41, 1), (46, 1)] }, { coefficient := 1, powers := [(0, 1), (12, 1), (17, 2), (29, 1), (34, 1), (36, 1), (37, 1), (41, 1)] }, { coefficient := -1, powers := [(0, 1), (12, 1), (17, 1), (23, 1), (28, 1), (29, 1), (36, 1), (41, 1), (46, 1)] }, { coefficient := 1, powers := [(0, 1), (12, 1), (17, 1), (23, 1), (29, 1), (34, 1), (36, 1), (37, 1), (41, 1)] }, { coefficient := 1, powers := [(0, 1), (12, 1), (17, 1), (28, 1), (35, 1), (46, 1), (56, 1)] }, { coefficient := -1, powers := [(0, 1), (12, 1), (17, 1), (34, 1), (35, 1), (37, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (23, 1), (38, 1), (41, 1)] }, { coefficient := -1, powers := [(3, 1), (9, 1), (12, 1), (17, 1), (28, 1), (32, 1), (46, 1)] }, { coefficient := 1, powers := [(3, 1), (9, 1), (12, 1), (17, 1), (32, 1), (34, 1), (37, 1)] }, { coefficient := -1, powers := [(3, 1), (9, 1), (16, 1), (22, 1), (23, 1), (32, 1), (48, 1), (51, 1)] }, { coefficient := 1, powers := [(3, 1), (12, 1), (17, 1), (23, 1), (28, 1), (46, 1), (56, 1)] }, { coefficient := -1, powers := [(3, 1), (12, 1), (17, 1), (23, 1), (34, 1), (37, 1), (56, 1)] }, { coefficient := 1, powers := [(3, 1), (12, 1), (17, 1), (28, 1), (32, 1), (46, 1), (47, 1)] }, { coefficient := -1, powers := [(3, 1), (12, 1), (17, 1), (32, 1), (34, 1), (37, 1), (47, 1)] }, { coefficient := -1, powers := [(3, 1), (13, 1), (16, 1), (22, 1), (23, 1), (29, 1), (52, 1)] }, { coefficient := 1, powers := [(3, 1), (16, 1), (22, 1), (23, 2), (48, 1), (51, 1), (56, 1)] }, { coefficient := 1, powers := [(3, 1), (16, 1), (22, 1), (23, 2), (52, 1), (56, 1)] }, { coefficient := 1, powers := [(3, 1), (16, 1), (22, 1), (23, 1), (29, 1), (41, 1), (52, 1)] }, { coefficient := 1, powers := [(3, 1), (23, 1), (29, 1), (41, 1)] }, { coefficient := -1, powers := [(6, 1), (17, 1), (24, 1), (42, 1), (56, 1), (62, 1)] }, { coefficient := 1, powers := [(9, 1), (13, 1), (17, 1), (24, 1), (42, 1), (62, 1)] }, { coefficient := 1, powers := [(9, 1), (17, 1), (23, 1), (24, 1), (41, 1), (42, 1), (44, 1), (62, 1)] }, { coefficient := 1, powers := [(12, 1), (13, 1), (17, 1), (28, 1), (29, 1), (35, 1), (46, 1)] }, { coefficient := -1, powers := [(12, 1), (13, 1), (17, 1), (29, 1), (34, 1), (35, 1), (37, 1)] }, { coefficient := -1, powers := [(12, 1), (17, 2), (23, 1), (28, 1), (29, 1), (36, 1), (41, 1), (46, 1)] }, { coefficient := 1, powers := [(12, 1), (17, 2), (23, 1), (29, 1), (34, 1), (36, 1), (37, 1), (41, 1)] }, { coefficient := -1, powers := [(12, 1), (17, 1), (28, 1), (29, 1), (35, 1), (41, 1), (46, 1)] }, { coefficient := 1, powers := [(12, 1), (17, 1), (29, 1), (34, 1), (35, 1), (37, 1), (41, 1)] }, { coefficient := -1, powers := [(13, 1), (17, 1), (24, 1), (42, 1), (47, 1), (62, 1)] }, { coefficient := 1, powers := [(17, 1), (24, 1), (41, 1), (42, 1), (47, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (9, 1), (17, 1), (41, 1), (44, 1)] }, { coefficient := -1, powers := [(6, 1), (17, 1), (56, 1)] }, { coefficient := 1, powers := [(9, 1), (13, 1), (17, 1)] }, { coefficient := 1, powers := [(9, 1), (17, 1), (23, 1), (41, 1), (44, 1)] }, { coefficient := -1, powers := [(13, 1), (17, 1), (47, 1)] }, { coefficient := 1, powers := [(17, 1), (41, 1), (47, 1)] }]
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
    (values : Fin 63 → R) :
    ¬ ∀ index : Fin 43,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component14.SelectedLeafB6_2_1.selectedHasNoCommonZero

end Krenn.Component14.SelectedLeafB6_2_1
