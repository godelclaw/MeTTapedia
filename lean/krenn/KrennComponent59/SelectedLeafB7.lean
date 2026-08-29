import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component59.SelectedLeafB7

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "485a7830121f76f6d0e5f036b582d262bdd701e3365de347cb214abeb5900f89"
def certificateSHA256 : String := "7b5c662c564773bcd5d6c33f31e522f70c8b803813cfdd85a4a06a0b5e88b295"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 49 → Fin 614 := ![
  0,
  1,
  3,
  4,
  6,
  7,
  9,
  10,
  11,
  16,
  26,
  29,
  34,
  35,
  37,
  40,
  42,
  192,
  203,
  222,
  224,
  235,
  237,
  247,
  251,
  332,
  337,
  349,
  351,
  358,
  363,
  376,
  395,
  396,
  471,
  497,
  560,
  574,
  575,
  578,
  579,
  580,
  585,
  608,
  609,
  610,
  611,
  612,
  613
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 49 → SparsePoly (Fin 61) := ![
  [{ coefficient := 1, powers := [(2, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (32, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (29, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (26, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(26, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(26, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (34, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (35, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (36, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (51, 1)] }, { coefficient := 1, powers := [(18, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (57, 1)] }, { coefficient := 1, powers := [(7, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (37, 1), (54, 1)] }, { coefficient := 1, powers := [(54, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1), (51, 1)] }, { coefficient := 1, powers := [(51, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (33, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (36, 1), (53, 1)] }, { coefficient := 1, powers := [(2, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (26, 1), (56, 1)] }, { coefficient := 1, powers := [(26, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (22, 1), (56, 1)] }, { coefficient := 1, powers := [(22, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1)] }, { coefficient := 1, powers := [(19, 1), (40, 1)] }, { coefficient := 1, powers := [(23, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (45, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (54, 1)] }, { coefficient := 1, powers := [(26, 1), (45, 1)] }, { coefficient := 1, powers := [(32, 1), (35, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (36, 1), (54, 1)] }, { coefficient := 1, powers := [(3, 1), (27, 1), (54, 1)] }, { coefficient := 1, powers := [(9, 1), (18, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1), (49, 1)] }, { coefficient := 1, powers := [(19, 1), (40, 1), (49, 1)] }, { coefficient := 1, powers := [(45, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (37, 1), (54, 1)] }, { coefficient := 1, powers := [(4, 1), (28, 1), (54, 1)] }, { coefficient := 1, powers := [(10, 1), (21, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (33, 1), (55, 1)] }, { coefficient := 1, powers := [(2, 1), (36, 1), (52, 1)] }, { coefficient := 1, powers := [(2, 1), (39, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (26, 1), (56, 1)] }, { coefficient := 1, powers := [(10, 1), (26, 1), (42, 1)] }, { coefficient := 1, powers := [(14, 1), (26, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (26, 1), (57, 1)] }, { coefficient := 1, powers := [(4, 1), (29, 1), (54, 1)] }, { coefficient := 1, powers := [(4, 1), (32, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (51, 1)] }, { coefficient := 1, powers := [(26, 1), (38, 1)] }, { coefficient := 1, powers := [(26, 1), (44, 1), (47, 1)] }, { coefficient := 1, powers := [(29, 1), (35, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (35, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (26, 1), (56, 1)] }, { coefficient := 1, powers := [(8, 1), (22, 1), (56, 1)] }, { coefficient := 1, powers := [(16, 1), (26, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (49, 1)] }, { coefficient := 1, powers := [(3, 1), (56, 1)] }, { coefficient := 1, powers := [(18, 1), (49, 1)] }, { coefficient := 1, powers := [(18, 1), (53, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (39, 1)] }, { coefficient := 1, powers := [(3, 1), (30, 1)] }, { coefficient := 1, powers := [(13, 1), (18, 1)] }, { coefficient := 1, powers := [(18, 1), (52, 1)] }, { coefficient := 1, powers := [(23, 1), (39, 1)] }, { coefficient := 1, powers := [(30, 1), (33, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1)] }, { coefficient := 1, powers := [(6, 1), (27, 1)] }, { coefficient := 1, powers := [(9, 1), (23, 1)] }, { coefficient := 1, powers := [(18, 1), (46, 1)] }, { coefficient := 1, powers := [(23, 1), (36, 1)] }, { coefficient := 1, powers := [(27, 1), (33, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (56, 1)] }, { coefficient := 1, powers := [(7, 1), (56, 1)] }, { coefficient := 1, powers := [(10, 1), (42, 1)] }, { coefficient := 1, powers := [(10, 1), (53, 1)] }, { coefficient := 1, powers := [(14, 1), (37, 1)] }, { coefficient := 1, powers := [(14, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (49, 1)] }, { coefficient := 1, powers := [(21, 1), (53, 1)] }, { coefficient := 1, powers := [(25, 1), (37, 1)] }, { coefficient := 1, powers := [(25, 1), (42, 1)] }, { coefficient := 1, powers := [(28, 1), (34, 1)] }, { coefficient := 1, powers := [(31, 1), (34, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (33, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1)] }, { coefficient := 1, powers := [(3, 1), (23, 1), (56, 1)] }, { coefficient := 1, powers := [(6, 1), (18, 1), (56, 1)] }, { coefficient := 1, powers := [(18, 1)] }, { coefficient := 1, powers := [(23, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (39, 1), (48, 1)] }, { coefficient := 1, powers := [(3, 1), (30, 1), (48, 1)] }, { coefficient := 1, powers := [(3, 1), (55, 1)] }, { coefficient := 1, powers := [(9, 1), (39, 1)] }, { coefficient := 1, powers := [(13, 1), (18, 1), (48, 1)] }, { coefficient := 1, powers := [(13, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (33, 1), (55, 1)] }, { coefficient := 1, powers := [(0, 1), (36, 1), (52, 1)] }, { coefficient := 1, powers := [(0, 1), (39, 1), (46, 1)] }, { coefficient := 1, powers := [(3, 1), (23, 1), (55, 1)] }, { coefficient := 1, powers := [(3, 1), (27, 1), (52, 1)] }, { coefficient := 1, powers := [(3, 1), (30, 1), (46, 1)] }, { coefficient := 1, powers := [(6, 1), (18, 1), (55, 1)] }, { coefficient := 1, powers := [(6, 1), (27, 1), (39, 1)] }, { coefficient := 1, powers := [(6, 1), (30, 1), (36, 1)] }, { coefficient := 1, powers := [(9, 1), (18, 1), (52, 1)] }, { coefficient := 1, powers := [(9, 1), (23, 1), (39, 1)] }, { coefficient := 1, powers := [(9, 1), (30, 1), (33, 1)] }, { coefficient := 1, powers := [(13, 1), (18, 1), (46, 1)] }, { coefficient := 1, powers := [(13, 1), (23, 1), (36, 1)] }, { coefficient := 1, powers := [(13, 1), (27, 1), (33, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1), (34, 1), (56, 1)] }, { coefficient := 1, powers := [(1, 1), (37, 1), (53, 1)] }, { coefficient := 1, powers := [(1, 1), (42, 1), (49, 1)] }, { coefficient := 1, powers := [(4, 1), (25, 1), (56, 1)] }, { coefficient := 1, powers := [(4, 1), (28, 1), (53, 1)] }, { coefficient := 1, powers := [(4, 1), (31, 1), (49, 1)] }, { coefficient := 1, powers := [(7, 1), (21, 1), (56, 1)] }, { coefficient := 1, powers := [(7, 1), (28, 1), (42, 1)] }, { coefficient := 1, powers := [(7, 1), (31, 1), (37, 1)] }, { coefficient := 1, powers := [(10, 1), (21, 1), (53, 1)] }, { coefficient := 1, powers := [(10, 1), (25, 1), (42, 1)] }, { coefficient := 1, powers := [(10, 1), (31, 1), (34, 1)] }, { coefficient := 1, powers := [(14, 1), (21, 1), (49, 1)] }, { coefficient := 1, powers := [(14, 1), (25, 1), (37, 1)] }, { coefficient := 1, powers := [(14, 1), (28, 1), (34, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (35, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (38, 1), (54, 1)] }, { coefficient := 1, powers := [(2, 1), (45, 1), (51, 1)] }, { coefficient := 1, powers := [(5, 1), (26, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (51, 1)] }, { coefficient := 1, powers := [(8, 1), (22, 1), (57, 1)] }, { coefficient := 1, powers := [(8, 1), (29, 1), (45, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (38, 1)] }, { coefficient := 1, powers := [(12, 1), (22, 1), (54, 1)] }, { coefficient := 1, powers := [(12, 1), (26, 1), (45, 1)] }, { coefficient := 1, powers := [(12, 1), (32, 1), (35, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (51, 1)] }, { coefficient := 1, powers := [(17, 1), (26, 1), (38, 1)] }, { coefficient := 1, powers := [(17, 1), (29, 1), (35, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (58, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1), (59, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (60, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 49 → SparsePoly (Fin 61) := ![
  [{ coefficient := -1, powers := [(0, 1), (2, 1), (3, 1), (23, 1), (38, 1), (48, 1), (54, 1), (56, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (2, 1), (6, 1), (9, 1), (38, 1), (54, 1), (56, 1), (60, 1)] }, { coefficient := -1, powers := [(0, 1), (2, 1), (6, 1), (18, 1), (38, 1), (48, 1), (54, 1), (56, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (2, 1), (9, 1), (38, 1), (54, 1), (60, 1)] }, { coefficient := -1, powers := [(0, 1), (2, 1), (18, 1), (38, 1), (48, 1), (54, 1), (60, 1)] }, { coefficient := -2, powers := [(0, 1), (2, 1), (23, 1), (38, 1), (48, 1), (54, 1), (60, 1)] }, { coefficient := -1, powers := [(2, 1), (3, 1), (23, 2), (38, 1), (48, 1), (54, 1), (56, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (3, 1), (23, 1), (36, 1), (38, 1), (54, 1), (56, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (3, 1), (27, 1), (33, 1), (38, 1), (54, 1), (56, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (6, 1), (9, 1), (23, 1), (38, 1), (54, 1), (56, 1), (60, 1)] }, { coefficient := -1, powers := [(2, 1), (6, 1), (18, 1), (23, 1), (38, 1), (48, 1), (54, 1), (56, 1), (60, 1)] }, { coefficient := -1, powers := [(2, 1), (9, 1), (18, 1), (38, 1), (54, 1), (60, 1)] }, { coefficient := -1, powers := [(2, 1), (9, 1), (23, 1), (38, 1), (54, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (7, 1), (28, 1), (29, 1), (54, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (10, 1), (25, 1), (29, 1), (54, 1), (60, 1)] }, { coefficient := -1, powers := [(5, 1), (14, 1), (25, 1), (29, 1), (54, 1), (60, 1)] }, { coefficient := -1, powers := [(17, 1), (18, 1), (22, 1), (51, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (2, 1), (3, 1), (38, 1), (39, 1), (54, 1), (56, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (2, 1), (3, 1), (38, 1), (52, 1), (54, 1), (56, 1), (60, 1)] }, { coefficient := -1, powers := [(0, 1), (2, 1), (38, 1), (39, 1), (54, 1), (60, 1)] }, { coefficient := -1, powers := [(2, 1), (3, 2), (30, 1), (38, 1), (54, 1), (56, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (3, 1), (18, 1), (38, 1), (39, 1), (54, 1), (56, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (3, 1), (18, 1), (38, 1), (52, 1), (54, 1), (56, 1), (60, 1)] }, { coefficient := -1, powers := [(2, 1), (3, 1), (23, 1), (38, 1), (39, 1), (54, 1), (56, 1), (60, 1)] }, { coefficient := -1, powers := [(2, 1), (3, 1), (30, 1), (38, 1), (54, 1), (60, 1)] }, { coefficient := -1, powers := [(2, 1), (18, 1), (38, 1), (39, 1), (54, 1), (60, 1)] }, { coefficient := -1, powers := [(2, 1), (23, 1), (38, 1), (39, 1), (54, 1), (60, 1)] }, { coefficient := -1, powers := [(2, 1), (30, 1), (33, 1), (38, 1), (54, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (2, 1), (6, 1), (30, 1), (36, 1), (38, 1), (54, 1), (60, 1)] }, { coefficient := -1, powers := [(0, 1), (2, 1), (38, 1), (54, 1), (60, 1)] }, { coefficient := 1, powers := [(1, 1), (5, 1), (29, 1), (42, 1), (54, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (6, 1), (18, 1), (30, 1), (36, 1), (38, 1), (54, 1), (60, 1)] }, { coefficient := -1, powers := [(2, 1), (18, 1), (38, 1), (54, 1), (60, 1)] }, { coefficient := 1, powers := [(4, 1), (5, 1), (29, 1), (31, 1), (54, 1), (60, 1)] }, { coefficient := -1, powers := [(5, 1), (14, 1), (25, 1), (26, 1), (57, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (23, 1), (29, 1), (45, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (25, 1), (51, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (31, 1), (54, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (22, 1), (57, 1)] }, { coefficient := -1, powers := [(6, 1), (22, 1), (57, 1)] }, { coefficient := -1, powers := [(32, 1), (33, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (3, 1), (6, 1), (30, 1), (38, 1), (56, 1)] }, { coefficient := -1, powers := [(2, 1), (3, 1), (13, 1), (23, 1), (38, 1), (56, 1)] }, { coefficient := 2, powers := [(2, 1), (3, 1), (30, 1), (38, 1)] }, { coefficient := -1, powers := [(2, 1), (6, 1), (30, 1), (38, 1)] }, { coefficient := -1, powers := [(2, 1), (13, 1), (23, 1), (38, 1)] }, { coefficient := -1, powers := [(2, 1), (23, 1), (38, 1), (52, 1)] }, { coefficient := 1, powers := [(2, 1), (30, 1), (33, 1), (38, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (25, 1), (53, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (29, 1), (31, 1), (34, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (3, 1), (13, 1), (38, 1), (46, 1), (56, 1)] }, { coefficient := -1, powers := [(2, 1), (6, 1), (9, 1), (38, 1), (52, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (6, 1), (13, 1), (36, 1), (38, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (9, 1), (13, 1), (33, 1), (38, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (9, 1), (38, 1), (52, 1)] }, { coefficient := -1, powers := [(2, 1), (13, 1), (23, 1), (38, 1), (48, 1)] }, { coefficient := -1, powers := [(2, 1), (13, 1), (38, 1), (46, 1)] }, { coefficient := 1, powers := [(2, 1), (18, 1), (38, 1), (48, 1), (52, 1)] }, { coefficient := 1, powers := [(2, 1), (23, 1), (38, 1), (48, 1), (52, 1)] }, { coefficient := -1, powers := [(2, 1), (33, 1), (38, 1), (55, 1)] }, { coefficient := -1, powers := [(2, 1), (36, 1), (38, 1), (52, 1)] }, { coefficient := -1, powers := [(2, 1), (38, 1), (46, 1), (52, 1)] }, { coefficient := -1, powers := [(2, 1), (38, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (7, 1), (29, 1), (56, 1)] }, { coefficient := -1, powers := [(5, 1), (14, 1), (29, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (16, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [(17, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (5, 1), (54, 1), (56, 1)] }, { coefficient := -1, powers := [(5, 1), (14, 1), (31, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (3, 1), (57, 1), (58, 1)] }, { coefficient := -1, powers := [(2, 1), (33, 1), (57, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (2, 1), (3, 1), (38, 1), (52, 1), (56, 1), (59, 1)] }, { coefficient := -1, powers := [(0, 1), (2, 1), (6, 1), (38, 1), (52, 1), (56, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (2, 1), (13, 1), (33, 1), (38, 1), (56, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (2, 1), (38, 1), (52, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (6, 1), (30, 1), (38, 1), (59, 1)] }, { coefficient := -1, powers := [(2, 1), (13, 1), (23, 1), (38, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (22, 1), (42, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (25, 1), (26, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (7, 1), (29, 1), (31, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(17, 1), (22, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (2, 1), (3, 1), (30, 1), (38, 1), (48, 1), (54, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (2, 1), (3, 1), (38, 1), (54, 1), (55, 1), (60, 1)] }, { coefficient := -1, powers := [(0, 1), (2, 1), (9, 1), (13, 1), (38, 1), (54, 1), (60, 1)] }, { coefficient := -1, powers := [(0, 1), (2, 1), (9, 1), (38, 1), (52, 1), (54, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (2, 1), (13, 1), (18, 1), (38, 1), (48, 1), (54, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (2, 1), (13, 1), (36, 1), (38, 1), (54, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (2, 1), (18, 1), (38, 1), (48, 1), (52, 1), (54, 1), (60, 1)] }, { coefficient := -1, powers := [(2, 1), (3, 1), (9, 1), (30, 1), (38, 1), (54, 1), (60, 1)] }, { coefficient := -1, powers := [(2, 1), (3, 1), (23, 1), (30, 1), (38, 1), (48, 1), (54, 1), (60, 1)] }, { coefficient := -1, powers := [(2, 1), (3, 1), (23, 1), (38, 1), (54, 1), (55, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (3, 1), (27, 1), (38, 1), (52, 1), (54, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (6, 1), (9, 1), (30, 1), (38, 1), (54, 1), (60, 1)] }, { coefficient := -1, powers := [(2, 1), (6, 1), (18, 1), (30, 1), (38, 1), (48, 1), (54, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (35, 1), (57, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (38, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (6, 1), (18, 1), (30, 1), (38, 1), (54, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (29, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(51, 1)] }],
  [{ coefficient := 1, powers := [(12, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (3, 1), (38, 1), (52, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (6, 1), (38, 1), (52, 1), (56, 1)] }, { coefficient := -1, powers := [(2, 1), (13, 1), (33, 1), (38, 1), (56, 1)] }, { coefficient := -1, powers := [(2, 1), (38, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (29, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (29, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (2, 1), (3, 1), (38, 1), (54, 1), (56, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (3, 1), (23, 1), (38, 1), (54, 1), (56, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (18, 1), (38, 1), (54, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (25, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (25, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(17, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (6, 1), (30, 1), (36, 1), (38, 1), (54, 1)] }, { coefficient := 1, powers := [(2, 1), (38, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (3, 1), (23, 1), (38, 1), (48, 1), (54, 1), (56, 1)] }, { coefficient := -1, powers := [(2, 1), (6, 1), (9, 1), (38, 1), (54, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (6, 1), (18, 1), (38, 1), (48, 1), (54, 1), (56, 1)] }, { coefficient := -1, powers := [(2, 1), (9, 1), (38, 1), (54, 1)] }, { coefficient := 1, powers := [(2, 1), (38, 1), (46, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (3, 1), (38, 1), (39, 1), (54, 1), (56, 1)] }, { coefficient := -1, powers := [(2, 1), (3, 1), (38, 1), (52, 1), (54, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (25, 1), (26, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (14, 1), (29, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (3, 1), (30, 1), (38, 1), (48, 1), (54, 1)] }, { coefficient := -1, powers := [(2, 1), (3, 1), (38, 1), (54, 1), (55, 1)] }, { coefficient := 1, powers := [(2, 1), (9, 1), (13, 1), (38, 1), (54, 1)] }, { coefficient := 1, powers := [(2, 1), (9, 1), (38, 1), (52, 1), (54, 1)] }, { coefficient := -1, powers := [(2, 1), (13, 1), (18, 1), (38, 1), (48, 1), (54, 1)] }, { coefficient := -1, powers := [(2, 1), (13, 1), (36, 1), (38, 1), (54, 1)] }, { coefficient := -1, powers := [(2, 1), (18, 1), (38, 1), (48, 1), (52, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (18, 1), (38, 1), (54, 1)] }, { coefficient := 2, powers := [(2, 1), (23, 1), (38, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (3, 1), (38, 1), (54, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (29, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(2, 1), (3, 1), (35, 1), (56, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (33, 1), (35, 1), (56, 1), (57, 1)] }, { coefficient := -1, powers := [(5, 1), (7, 1), (29, 1), (31, 1), (37, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (2, 1), (3, 1), (36, 1), (38, 1), (52, 1), (54, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (2, 1), (6, 1), (36, 1), (38, 1), (52, 1), (54, 1), (56, 1)] }, { coefficient := -1, powers := [(0, 1), (2, 1), (13, 1), (33, 1), (36, 1), (38, 1), (54, 1), (56, 1)] }, { coefficient := -1, powers := [(0, 1), (2, 1), (36, 1), (38, 1), (52, 1), (54, 1)] }, { coefficient := -1, powers := [(2, 1), (6, 1), (30, 1), (36, 1), (38, 1), (54, 1)] }, { coefficient := 1, powers := [(2, 1), (13, 1), (23, 1), (36, 1), (38, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (2, 1), (3, 1), (23, 1), (38, 1), (39, 1), (48, 1), (54, 1), (56, 1)] }, { coefficient := -1, powers := [(0, 1), (2, 1), (3, 1), (30, 1), (33, 1), (38, 1), (48, 1), (54, 1), (56, 1)] }, { coefficient := -1, powers := [(0, 1), (2, 1), (3, 1), (30, 1), (38, 1), (48, 1), (54, 1)] }, { coefficient := 1, powers := [(0, 1), (2, 1), (3, 1), (36, 1), (38, 1), (52, 1), (54, 1), (56, 1)] }, { coefficient := -1, powers := [(0, 1), (2, 1), (3, 1), (38, 1), (46, 1), (52, 1), (54, 1), (56, 1)] }, { coefficient := -1, powers := [(0, 1), (2, 1), (3, 1), (38, 1), (54, 1), (55, 1)] }, { coefficient := -1, powers := [(0, 1), (2, 1), (6, 1), (9, 1), (38, 1), (39, 1), (54, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (2, 1), (6, 1), (18, 1), (38, 1), (39, 1), (48, 1), (54, 1), (56, 1)] }, { coefficient := -1, powers := [(0, 1), (2, 1), (6, 1), (30, 1), (36, 1), (38, 1), (49, 1), (54, 1)] }, { coefficient := 1, powers := [(0, 1), (2, 1), (9, 1), (13, 1), (33, 1), (38, 1), (54, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (2, 1), (9, 1), (13, 1), (38, 1), (54, 1)] }, { coefficient := 1, powers := [(0, 1), (2, 1), (9, 1), (33, 1), (38, 1), (52, 1), (54, 1), (56, 1)] }, { coefficient := -1, powers := [(0, 1), (2, 1), (9, 1), (38, 1), (39, 1), (54, 1)] }, { coefficient := 1, powers := [(0, 1), (2, 1), (9, 1), (38, 1), (52, 1), (54, 1)] }, { coefficient := -1, powers := [(0, 1), (2, 1), (13, 1), (18, 1), (33, 1), (38, 1), (48, 1), (54, 1), (56, 1)] }, { coefficient := -1, powers := [(0, 1), (2, 1), (13, 1), (18, 1), (38, 1), (48, 1), (54, 1)] }, { coefficient := -1, powers := [(0, 1), (2, 1), (13, 1), (33, 1), (36, 1), (38, 1), (54, 1), (56, 1)] }, { coefficient := -1, powers := [(0, 1), (2, 1), (13, 1), (36, 1), (38, 1), (54, 1)] }, { coefficient := -1, powers := [(0, 1), (2, 1), (18, 1), (33, 1), (38, 1), (48, 1), (52, 1), (54, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (2, 1), (18, 1), (38, 1), (39, 1), (48, 1), (54, 1)] }, { coefficient := -1, powers := [(0, 1), (2, 1), (18, 1), (38, 1), (48, 1), (52, 1), (54, 1)] }, { coefficient := 2, powers := [(0, 1), (2, 1), (23, 1), (38, 1), (39, 1), (48, 1), (54, 1)] }, { coefficient := 1, powers := [(0, 1), (2, 1), (38, 1), (39, 1), (46, 1), (54, 1)] }, { coefficient := 1, powers := [(0, 1), (2, 1), (38, 1), (49, 1), (54, 1)] }, { coefficient := -1, powers := [(1, 1), (5, 1), (29, 1), (42, 1), (49, 1), (54, 1)] }, { coefficient := 1, powers := [(2, 1), (3, 2), (30, 1), (38, 1), (46, 1), (54, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (3, 1), (9, 1), (30, 1), (33, 1), (38, 1), (54, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (3, 1), (9, 1), (30, 1), (38, 1), (54, 1)] }, { coefficient := -1, powers := [(2, 1), (3, 1), (18, 1), (38, 1), (39, 1), (46, 1), (54, 1), (56, 1)] }, { coefficient := -1, powers := [(2, 1), (3, 1), (18, 1), (38, 1), (46, 1), (52, 1), (54, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (3, 1), (23, 2), (38, 1), (39, 1), (48, 1), (54, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (3, 1), (23, 1), (30, 1), (33, 1), (38, 1), (48, 1), (54, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (3, 1), (23, 1), (30, 1), (38, 1), (48, 1), (54, 1)] }, { coefficient := -1, powers := [(2, 1), (3, 1), (23, 1), (36, 1), (38, 1), (39, 1), (54, 1), (56, 1)] }, { coefficient := -1, powers := [(2, 1), (3, 1), (23, 1), (36, 1), (38, 1), (52, 1), (54, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (3, 1), (23, 1), (38, 1), (54, 1), (55, 1)] }, { coefficient := -1, powers := [(2, 1), (3, 1), (27, 1), (33, 1), (38, 1), (39, 1), (54, 1), (56, 1)] }, { coefficient := -1, powers := [(2, 1), (3, 1), (27, 1), (33, 1), (38, 1), (52, 1), (54, 1), (56, 1)] }, { coefficient := -1, powers := [(2, 1), (3, 1), (27, 1), (38, 1), (52, 1), (54, 1)] }, { coefficient := 1, powers := [(2, 1), (3, 1), (30, 1), (38, 1), (46, 1), (54, 1)] }, { coefficient := -1, powers := [(2, 1), (6, 1), (9, 1), (23, 1), (38, 1), (39, 1), (54, 1), (56, 1)] }, { coefficient := -1, powers := [(2, 1), (6, 1), (9, 1), (30, 1), (33, 1), (38, 1), (54, 1), (56, 1)] }, { coefficient := -1, powers := [(2, 1), (6, 1), (9, 1), (30, 1), (38, 1), (54, 1)] }, { coefficient := 1, powers := [(2, 1), (6, 1), (18, 1), (23, 1), (38, 1), (39, 1), (48, 1), (54, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (6, 1), (18, 1), (30, 1), (33, 1), (38, 1), (48, 1), (54, 1), (56, 1)] }, { coefficient := -1, powers := [(2, 1), (6, 1), (18, 1), (30, 1), (36, 1), (38, 1), (49, 1), (54, 1)] }, { coefficient := -1, powers := [(2, 1), (6, 1), (18, 1), (30, 1), (36, 1), (38, 1), (53, 1), (54, 1)] }, { coefficient := 1, powers := [(2, 1), (9, 1), (18, 1), (38, 1), (39, 1), (54, 1)] }, { coefficient := 1, powers := [(2, 1), (9, 1), (23, 1), (38, 1), (39, 1), (54, 1)] }, { coefficient := -1, powers := [(2, 1), (18, 1), (33, 1), (38, 1), (54, 1), (55, 1)] }, { coefficient := -1, powers := [(2, 1), (18, 1), (36, 1), (38, 1), (52, 1), (54, 1)] }, { coefficient := 1, powers := [(2, 1), (18, 1), (38, 1), (49, 1), (54, 1)] }, { coefficient := 1, powers := [(2, 1), (23, 1), (38, 1), (39, 1), (46, 1), (54, 1)] }, { coefficient := 1, powers := [(2, 1), (30, 1), (33, 1), (38, 1), (46, 1), (54, 1)] }, { coefficient := -1, powers := [(2, 1), (33, 1), (35, 1), (56, 1), (57, 1)] }, { coefficient := -1, powers := [(2, 1), (35, 1), (57, 1)] }, { coefficient := -1, powers := [(4, 1), (5, 1), (29, 1), (31, 1), (49, 1), (54, 1)] }, { coefficient := -1, powers := [(5, 1), (7, 1), (28, 1), (29, 1), (42, 1), (54, 1)] }, { coefficient := -1, powers := [(5, 1), (10, 1), (25, 1), (29, 1), (42, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (14, 1), (25, 1), (26, 1), (49, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (14, 1), (25, 1), (29, 1), (42, 1), (54, 1)] }, { coefficient := -1, powers := [(8, 1), (23, 1), (29, 1), (45, 1), (49, 1)] }, { coefficient := -1, powers := [(8, 1), (32, 1), (33, 1), (38, 1), (56, 1)] }, { coefficient := -1, powers := [(8, 1), (32, 1), (38, 1)] }, { coefficient := 1, powers := [(17, 1), (18, 1), (22, 1), (42, 1), (51, 1)] }]
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
    ¬ ∀ index : Fin 49,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component59.SelectedLeafB7.selectedHasNoCommonZero

end Krenn.Component59.SelectedLeafB7
