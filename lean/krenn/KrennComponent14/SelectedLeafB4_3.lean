import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component14.SelectedLeafB4_3

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "648f15705b238e46c49674808e3446720dad37cebce4306ec4108c58b2de19e0"
def certificateSHA256 : String := "8bfcf13fe20dba95a85c17585977794c70882b892bb6bf7e572c998cea2c2494"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 45 → Fin 640 := ![
  4,
  6,
  7,
  9,
  11,
  12,
  16,
  17,
  20,
  23,
  24,
  25,
  173,
  179,
  183,
  192,
  282,
  313,
  320,
  342,
  345,
  348,
  349,
  350,
  351,
  369,
  383,
  399,
  401,
  409,
  410,
  422,
  454,
  460,
  470,
  510,
  579,
  580,
  632,
  633,
  634,
  635,
  636,
  638,
  639
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 45 → SparsePoly (Fin 62) := ![
  [{ coefficient := 1, powers := [(4, 1), (34, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (31, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(15, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (17, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(31, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(34, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (23, 1)] }, { coefficient := 1, powers := [(15, 1), (17, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (44, 1)] }, { coefficient := 1, powers := [(12, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (39, 1)] }, { coefficient := 1, powers := [(16, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (51, 1)] }, { coefficient := 1, powers := [(28, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (17, 1), (54, 1)] }, { coefficient := 1, powers := [(12, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (23, 1), (39, 1)] }, { coefficient := 1, powers := [(16, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (48, 1), (54, 1)] }, { coefficient := 1, powers := [(26, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1)] }, { coefficient := 1, powers := [(17, 1), (42, 1)] }, { coefficient := 1, powers := [(23, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (52, 1)] }, { coefficient := 1, powers := [(17, 1), (52, 1)] }, { coefficient := 1, powers := [(24, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (46, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (52, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1)] }, { coefficient := 1, powers := [(12, 1), (28, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (58, 1)] }, { coefficient := 1, powers := [(12, 1), (46, 1)] }, { coefficient := 1, powers := [(16, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (58, 1)] }, { coefficient := 1, powers := [(12, 1), (55, 1)] }, { coefficient := 1, powers := [(16, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (40, 1), (54, 1)] }, { coefficient := 1, powers := [(7, 1), (33, 1), (40, 1)] }, { coefficient := 1, powers := [(15, 1), (26, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (39, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (39, 1)] }, { coefficient := 1, powers := [(16, 1), (28, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (28, 1), (58, 1)] }, { coefficient := 1, powers := [(4, 1), (31, 1), (55, 1)] }, { coefficient := 1, powers := [(4, 1), (34, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (34, 1), (50, 1)] }, { coefficient := 1, powers := [(7, 1), (34, 1), (39, 1)] }, { coefficient := 1, powers := [(11, 1), (34, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (22, 1), (57, 1)] }, { coefficient := 1, powers := [(11, 1), (22, 1), (54, 1)] }, { coefficient := 1, powers := [(15, 1), (22, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (22, 1), (58, 1)] }, { coefficient := 1, powers := [(7, 1), (31, 1), (46, 1)] }, { coefficient := 1, powers := [(7, 1), (34, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (22, 1), (55, 1)] }, { coefficient := 1, powers := [(11, 1), (28, 1), (46, 1)] }, { coefficient := 1, powers := [(11, 1), (34, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (45, 1), (48, 1), (54, 1)] }, { coefficient := 1, powers := [(26, 1), (40, 1)] }, { coefficient := 1, powers := [(26, 1), (45, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (52, 1)] }, { coefficient := 1, powers := [(28, 1), (40, 1)] }, { coefficient := 1, powers := [(28, 1), (45, 1), (48, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1), (51, 1)] }, { coefficient := 1, powers := [(17, 1), (42, 1), (51, 1)] }, { coefficient := 1, powers := [(17, 1), (55, 1)] }, { coefficient := 1, powers := [(24, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (17, 1), (57, 1)] }, { coefficient := 1, powers := [(11, 1), (17, 1), (54, 1)] }, { coefficient := 1, powers := [(11, 1)] }, { coefficient := 1, powers := [(15, 1), (17, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (57, 1)] }, { coefficient := 1, powers := [(7, 1), (57, 1)] }, { coefficient := 1, powers := [(11, 1), (44, 1)] }, { coefficient := 1, powers := [(11, 1), (54, 1)] }, { coefficient := 1, powers := [(15, 1), (39, 1)] }, { coefficient := 1, powers := [(15, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (50, 1)] }, { coefficient := 1, powers := [(20, 1), (54, 1)] }, { coefficient := 1, powers := [(26, 1), (39, 1)] }, { coefficient := 1, powers := [(26, 1), (44, 1)] }, { coefficient := 1, powers := [(30, 1), (36, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (36, 1), (57, 1)] }, { coefficient := 1, powers := [(1, 1), (39, 1), (54, 1)] }, { coefficient := 1, powers := [(1, 1), (44, 1), (50, 1)] }, { coefficient := 1, powers := [(4, 1), (26, 1), (57, 1)] }, { coefficient := 1, powers := [(4, 1), (30, 1), (54, 1)] }, { coefficient := 1, powers := [(4, 1), (33, 1), (50, 1)] }, { coefficient := 1, powers := [(7, 1), (20, 1), (57, 1)] }, { coefficient := 1, powers := [(7, 1), (30, 1), (44, 1)] }, { coefficient := 1, powers := [(7, 1), (33, 1), (39, 1)] }, { coefficient := 1, powers := [(11, 1), (20, 1), (54, 1)] }, { coefficient := 1, powers := [(11, 1), (26, 1), (44, 1)] }, { coefficient := 1, powers := [(11, 1), (33, 1), (36, 1)] }, { coefficient := 1, powers := [(15, 1), (20, 1), (50, 1)] }, { coefficient := 1, powers := [(15, 1), (26, 1), (39, 1)] }, { coefficient := 1, powers := [(15, 1), (30, 1), (36, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (37, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (40, 1), (55, 1)] }, { coefficient := 1, powers := [(2, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(5, 1), (28, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (52, 1)] }, { coefficient := 1, powers := [(8, 1), (22, 1), (58, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1), (46, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (40, 1)] }, { coefficient := 1, powers := [(12, 1), (22, 1), (55, 1)] }, { coefficient := 1, powers := [(12, 1), (28, 1), (46, 1)] }, { coefficient := 1, powers := [(12, 1), (34, 1), (37, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1), (52, 1)] }, { coefficient := 1, powers := [(16, 1), (28, 1), (40, 1)] }, { coefficient := 1, powers := [(16, 1), (31, 1), (37, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (59, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1)] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(39, 1), (60, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(40, 1), (61, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 45 → SparsePoly (Fin 62) := ![
  [{ coefficient := 1, powers := [(8, 1), (30, 1), (40, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (40, 1), (50, 1)] }, { coefficient := -1, powers := [(12, 1), (20, 1), (37, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1), (26, 1), (37, 1), (57, 1)] }, { coefficient := -1, powers := [(12, 1), (30, 1), (37, 1), (44, 1), (50, 1), (60, 1)] }, { coefficient := 1, powers := [(12, 1), (30, 1), (37, 1), (54, 1)] }, { coefficient := 1, powers := [(12, 1), (33, 1), (37, 1), (50, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (20, 1), (28, 1), (58, 1)] }, { coefficient := -1, powers := [(4, 1), (20, 1), (31, 1), (55, 1)] }, { coefficient := -1, powers := [(4, 1), (20, 1), (34, 1), (52, 1)] }, { coefficient := 1, powers := [(4, 1), (26, 1), (28, 1), (58, 1)] }, { coefficient := 1, powers := [(4, 1), (26, 1), (31, 1), (55, 1)] }, { coefficient := 1, powers := [(4, 1), (26, 1), (34, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (30, 1), (44, 1), (55, 1)] }, { coefficient := 1, powers := [(16, 1), (30, 1), (37, 1), (44, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (20, 1), (34, 1), (40, 1)] }, { coefficient := 1, powers := [(4, 1), (26, 1), (34, 1), (40, 1)] }],
  [{ coefficient := 2, powers := [(12, 1), (20, 1), (28, 1), (44, 1)] }, { coefficient := 2, powers := [(12, 1), (20, 1), (28, 1), (50, 1)] }, { coefficient := 2, powers := [(12, 1), (20, 1), (28, 1), (54, 1)] }, { coefficient := -2, powers := [(12, 1), (26, 1), (28, 1), (44, 1)] }, { coefficient := -2, powers := [(12, 1), (26, 1), (28, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (20, 1), (31, 1), (44, 1)] }, { coefficient := -1, powers := [(5, 1), (20, 1), (31, 1), (50, 1)] }, { coefficient := -1, powers := [(5, 1), (20, 1), (31, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (26, 1), (31, 1), (44, 1)] }, { coefficient := 1, powers := [(5, 1), (26, 1), (31, 1), (54, 1)] }, { coefficient := 1, powers := [(12, 1), (20, 1), (22, 1), (44, 1)] }, { coefficient := 1, powers := [(12, 1), (20, 1), (22, 1), (50, 1)] }, { coefficient := 1, powers := [(12, 1), (20, 1), (22, 1), (54, 1)] }, { coefficient := -1, powers := [(12, 1), (22, 1), (26, 1), (44, 1)] }, { coefficient := -1, powers := [(12, 1), (22, 1), (26, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (22, 1), (23, 1), (30, 1), (44, 2), (51, 1)] }, { coefficient := -1, powers := [(7, 1), (22, 1), (24, 1), (30, 1), (44, 2)] }],
  [{ coefficient := -1, powers := [(20, 1), (39, 1), (61, 1)] }, { coefficient := -1, powers := [(20, 1), (50, 1), (61, 1)] }, { coefficient := -1, powers := [(20, 1), (54, 1), (61, 1)] }, { coefficient := -1, powers := [(26, 1), (39, 1), (61, 1)] }, { coefficient := -1, powers := [(26, 1), (44, 1), (61, 1)] }, { coefficient := -1, powers := [(33, 1), (36, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (20, 1), (22, 1), (52, 1), (57, 1), (59, 1)] }, { coefficient := 1, powers := [(4, 1), (22, 1), (26, 1), (52, 1), (57, 1), (59, 1)] }, { coefficient := 1, powers := [(4, 1), (22, 1), (30, 1), (52, 1), (54, 1), (59, 1)] }, { coefficient := 1, powers := [(4, 1), (22, 1), (33, 1), (50, 1), (52, 1), (59, 1)] }, { coefficient := -1, powers := [(11, 1), (20, 1), (22, 1), (44, 1), (52, 1), (59, 1)] }, { coefficient := -1, powers := [(11, 1), (20, 1), (22, 1), (50, 1), (52, 1), (59, 1)] }, { coefficient := -1, powers := [(11, 1), (20, 1), (22, 1), (52, 1), (54, 1), (59, 1)] }, { coefficient := 1, powers := [(11, 1), (22, 1), (26, 1), (44, 1), (52, 1), (59, 1)] }, { coefficient := 1, powers := [(11, 1), (22, 1), (26, 1), (52, 1), (54, 1), (59, 1)] }, { coefficient := -2, powers := [(15, 1), (20, 1), (28, 1), (40, 1), (44, 1), (50, 1)] }, { coefficient := -2, powers := [(15, 1), (20, 1), (28, 1), (40, 1), (50, 2)] }, { coefficient := -2, powers := [(15, 1), (20, 1), (28, 1), (40, 1), (50, 1), (54, 1)] }, { coefficient := 2, powers := [(15, 1), (26, 1), (28, 1), (40, 1), (44, 1), (50, 1)] }, { coefficient := 2, powers := [(15, 1), (26, 1), (28, 1), (40, 1), (50, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (20, 1), (22, 1), (24, 1), (57, 1), (59, 1)] }, { coefficient := -1, powers := [(4, 1), (20, 1), (22, 1), (51, 1), (57, 1)] }, { coefficient := 1, powers := [(4, 1), (22, 1), (24, 1), (26, 1), (57, 1), (59, 1)] }, { coefficient := 1, powers := [(4, 1), (22, 1), (24, 1), (30, 1), (54, 1), (59, 1)] }, { coefficient := 1, powers := [(4, 1), (22, 1), (24, 1), (33, 1), (50, 1), (59, 1)] }, { coefficient := 1, powers := [(4, 1), (22, 1), (26, 1), (51, 1), (57, 1)] }, { coefficient := 1, powers := [(4, 1), (22, 1), (30, 1), (51, 1), (54, 1)] }, { coefficient := 1, powers := [(4, 1), (22, 1), (33, 1), (50, 1), (51, 1)] }, { coefficient := -1, powers := [(11, 1), (20, 1), (22, 1), (24, 1), (44, 1), (59, 1)] }, { coefficient := -1, powers := [(11, 1), (20, 1), (22, 1), (24, 1), (50, 1), (59, 1)] }, { coefficient := -1, powers := [(11, 1), (20, 1), (22, 1), (24, 1), (54, 1), (59, 1)] }, { coefficient := -1, powers := [(11, 1), (20, 1), (22, 1), (44, 1), (51, 1)] }, { coefficient := -1, powers := [(11, 1), (20, 1), (22, 1), (50, 1), (51, 1)] }, { coefficient := -1, powers := [(11, 1), (20, 1), (22, 1), (51, 1), (54, 1)] }, { coefficient := 1, powers := [(11, 1), (22, 1), (24, 1), (26, 1), (44, 1), (59, 1)] }, { coefficient := 1, powers := [(11, 1), (22, 1), (24, 1), (26, 1), (54, 1), (59, 1)] }, { coefficient := 1, powers := [(11, 1), (22, 1), (26, 1), (44, 1), (51, 1)] }, { coefficient := 1, powers := [(11, 1), (22, 1), (26, 1), (51, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (11, 1), (30, 1), (55, 1)] }, { coefficient := -1, powers := [(8, 1), (11, 1), (30, 1), (46, 1)] }, { coefficient := -1, powers := [(11, 1), (16, 1), (30, 1), (37, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (11, 1), (30, 1), (52, 1)] }, { coefficient := -1, powers := [(8, 1), (11, 1), (30, 1), (40, 1)] }, { coefficient := -1, powers := [(11, 1), (12, 1), (30, 1), (37, 1), (44, 1), (60, 1)] }, { coefficient := -1, powers := [(11, 1), (12, 1), (30, 1), (37, 1)] }],
  [{ coefficient := 2, powers := [(16, 1), (20, 1), (28, 1), (40, 1), (44, 1), (50, 1)] }, { coefficient := 2, powers := [(16, 1), (20, 1), (28, 1), (40, 1), (50, 2)] }, { coefficient := 2, powers := [(16, 1), (20, 1), (28, 1), (40, 1), (50, 1), (54, 1)] }, { coefficient := -2, powers := [(16, 1), (26, 1), (28, 1), (40, 1), (44, 1), (50, 1)] }, { coefficient := -2, powers := [(16, 1), (26, 1), (28, 1), (40, 1), (50, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (17, 1), (22, 1), (30, 1), (44, 1), (55, 1)] }],
  [{ coefficient := -2, powers := [(11, 1), (20, 1), (23, 1), (28, 1), (40, 1), (44, 1)] }, { coefficient := -2, powers := [(11, 1), (20, 1), (23, 1), (28, 1), (40, 1), (50, 1)] }, { coefficient := -2, powers := [(11, 1), (20, 1), (23, 1), (28, 1), (40, 1), (54, 1)] }, { coefficient := 2, powers := [(11, 1), (23, 1), (26, 1), (28, 1), (40, 1), (44, 1)] }, { coefficient := 2, powers := [(11, 1), (23, 1), (26, 1), (28, 1), (40, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (16, 1), (20, 1), (48, 1), (57, 1)] }, { coefficient := -1, powers := [(4, 1), (16, 1), (26, 1), (48, 1), (57, 1)] }, { coefficient := -1, powers := [(4, 1), (16, 1), (30, 1), (48, 1), (54, 1)] }, { coefficient := -1, powers := [(4, 1), (16, 1), (33, 1), (48, 1), (50, 1)] }, { coefficient := 1, powers := [(11, 1), (16, 1), (20, 1), (44, 1), (48, 1)] }, { coefficient := 1, powers := [(11, 1), (16, 1), (20, 1), (48, 1), (50, 1)] }, { coefficient := 1, powers := [(11, 1), (16, 1), (20, 1), (48, 1), (54, 1)] }, { coefficient := -1, powers := [(11, 1), (16, 1), (26, 1), (44, 1), (48, 1)] }, { coefficient := -1, powers := [(11, 1), (16, 1), (26, 1), (48, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (22, 1), (30, 1), (44, 1), (55, 1)] }],
  [{ coefficient := 2, powers := [(11, 1), (20, 1), (28, 1), (40, 1), (44, 1)] }, { coefficient := 2, powers := [(11, 1), (20, 1), (28, 1), (40, 1), (50, 1)] }, { coefficient := 2, powers := [(11, 1), (20, 1), (28, 1), (40, 1), (54, 1)] }, { coefficient := -2, powers := [(11, 1), (26, 1), (28, 1), (40, 1), (44, 1)] }, { coefficient := -2, powers := [(11, 1), (26, 1), (28, 1), (40, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (39, 1), (45, 1), (61, 1)] }, { coefficient := 1, powers := [(11, 1), (44, 1), (45, 1), (61, 1)] }, { coefficient := 1, powers := [(11, 1), (45, 1), (54, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (12, 1), (22, 1), (30, 1), (44, 2), (51, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (16, 1), (20, 1), (22, 1), (57, 1), (59, 1)] }, { coefficient := -1, powers := [(4, 1), (16, 1), (22, 1), (26, 1), (57, 1), (59, 1)] }, { coefficient := -1, powers := [(4, 1), (16, 1), (22, 1), (30, 1), (54, 1), (59, 1)] }, { coefficient := -1, powers := [(4, 1), (16, 1), (22, 1), (33, 1), (50, 1), (59, 1)] }, { coefficient := 1, powers := [(11, 1), (16, 1), (20, 1), (22, 1), (44, 1), (59, 1)] }, { coefficient := 1, powers := [(11, 1), (16, 1), (20, 1), (22, 1), (50, 1), (59, 1)] }, { coefficient := 1, powers := [(11, 1), (16, 1), (20, 1), (22, 1), (54, 1), (59, 1)] }, { coefficient := -1, powers := [(11, 1), (16, 1), (22, 1), (26, 1), (44, 1), (59, 1)] }, { coefficient := -1, powers := [(11, 1), (16, 1), (22, 1), (26, 1), (54, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (30, 1), (44, 1), (52, 1)] }, { coefficient := -1, powers := [(11, 1), (20, 1), (44, 1), (52, 1)] }, { coefficient := -1, powers := [(11, 1), (20, 1), (50, 1), (52, 1)] }, { coefficient := -1, powers := [(11, 1), (20, 1), (52, 1), (54, 1)] }, { coefficient := 1, powers := [(11, 1), (26, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(11, 1), (26, 1), (52, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (20, 1), (46, 1), (57, 1)] }, { coefficient := 1, powers := [(4, 1), (26, 1), (46, 1), (57, 1)] }, { coefficient := 1, powers := [(4, 1), (30, 1), (46, 1), (54, 1)] }, { coefficient := 1, powers := [(4, 1), (33, 1), (46, 1), (50, 1)] }, { coefficient := -1, powers := [(11, 1), (20, 1), (44, 1), (46, 1)] }, { coefficient := -1, powers := [(11, 1), (20, 1), (46, 1), (50, 1)] }, { coefficient := -1, powers := [(11, 1), (20, 1), (46, 1), (54, 1)] }, { coefficient := 1, powers := [(11, 1), (26, 1), (44, 1), (46, 1)] }, { coefficient := 1, powers := [(11, 1), (26, 1), (46, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (28, 1), (30, 1), (44, 1)] }, { coefficient := -1, powers := [(11, 1), (20, 1), (28, 1), (44, 1)] }, { coefficient := -1, powers := [(11, 1), (20, 1), (28, 1), (50, 1)] }, { coefficient := -1, powers := [(11, 1), (20, 1), (28, 1), (54, 1)] }, { coefficient := 1, powers := [(11, 1), (26, 1), (28, 1), (44, 1)] }, { coefficient := 1, powers := [(11, 1), (26, 1), (28, 1), (54, 1)] }, { coefficient := -1, powers := [(11, 1), (28, 1), (30, 1), (36, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (20, 1), (22, 1), (57, 1)] }, { coefficient := 1, powers := [(4, 1), (22, 1), (26, 1), (57, 1)] }, { coefficient := 1, powers := [(4, 1), (22, 1), (30, 1), (54, 1)] }, { coefficient := 1, powers := [(4, 1), (22, 1), (33, 1), (50, 1)] }, { coefficient := -1, powers := [(11, 1), (20, 1), (22, 1), (44, 1)] }, { coefficient := -1, powers := [(11, 1), (20, 1), (22, 1), (50, 1)] }, { coefficient := -1, powers := [(11, 1), (20, 1), (22, 1), (54, 1)] }, { coefficient := 1, powers := [(11, 1), (22, 1), (26, 1), (44, 1)] }, { coefficient := 1, powers := [(11, 1), (22, 1), (26, 1), (54, 1)] }, { coefficient := -1, powers := [(11, 1), (22, 1), (30, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(39, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(11, 1), (20, 1), (40, 1), (44, 1), (60, 1)] }, { coefficient := -1, powers := [(11, 1), (20, 1), (40, 1), (50, 1), (60, 1)] }, { coefficient := -1, powers := [(11, 1), (20, 1), (40, 1), (54, 1), (60, 1)] }, { coefficient := 1, powers := [(11, 1), (26, 1), (40, 1), (44, 1), (60, 1)] }, { coefficient := 1, powers := [(11, 1), (26, 1), (40, 1), (54, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (30, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (30, 1), (37, 1), (44, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(16, 1), (17, 1), (20, 1), (44, 1), (52, 1)] }, { coefficient := -1, powers := [(16, 1), (17, 1), (20, 1), (50, 1), (52, 1)] }, { coefficient := -1, powers := [(16, 1), (17, 1), (20, 1), (52, 1), (54, 1)] }, { coefficient := 1, powers := [(16, 1), (17, 1), (26, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(16, 1), (17, 1), (26, 1), (52, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (30, 1), (44, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (20, 1), (44, 1)] }, { coefficient := -1, powers := [(12, 1), (20, 1), (50, 1)] }, { coefficient := -1, powers := [(12, 1), (20, 1), (54, 1)] }, { coefficient := 1, powers := [(12, 1), (26, 1), (44, 1)] }, { coefficient := 1, powers := [(12, 1), (26, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(11, 1), (39, 1), (61, 1)] }, { coefficient := -1, powers := [(11, 1), (44, 1), (61, 1)] }, { coefficient := -1, powers := [(11, 1), (54, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (16, 1), (20, 1), (57, 1)] }, { coefficient := 1, powers := [(4, 1), (16, 1), (26, 1), (57, 1)] }, { coefficient := 1, powers := [(4, 1), (16, 1), (30, 1), (54, 1)] }, { coefficient := 1, powers := [(4, 1), (16, 1), (33, 1), (50, 1)] }, { coefficient := -1, powers := [(11, 1), (16, 1), (20, 1), (44, 1)] }, { coefficient := -1, powers := [(11, 1), (16, 1), (20, 1), (50, 1)] }, { coefficient := -1, powers := [(11, 1), (16, 1), (20, 1), (54, 1)] }, { coefficient := 1, powers := [(11, 1), (16, 1), (26, 1), (44, 1)] }, { coefficient := 1, powers := [(11, 1), (16, 1), (26, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (12, 1), (22, 1), (30, 1), (44, 2)] }],
  [{ coefficient := 1, powers := [(16, 1), (20, 1), (22, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(16, 1), (20, 1), (22, 1), (50, 1), (52, 1)] }, { coefficient := 1, powers := [(16, 1), (20, 1), (22, 1), (52, 1), (54, 1)] }, { coefficient := -1, powers := [(16, 1), (22, 1), (26, 1), (44, 1), (52, 1)] }, { coefficient := -1, powers := [(16, 1), (22, 1), (26, 1), (52, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(20, 1)] }],
  [{ coefficient := 1, powers := [(11, 1)] }, { coefficient := 1, powers := [(15, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(4, 1), (20, 1), (57, 1)] }, { coefficient := -1, powers := [(4, 1), (26, 1), (57, 1)] }, { coefficient := -1, powers := [(4, 1), (30, 1), (54, 1)] }, { coefficient := -1, powers := [(4, 1), (33, 1), (50, 1)] }, { coefficient := -1, powers := [(7, 1), (30, 1), (44, 1)] }, { coefficient := 1, powers := [(11, 1), (20, 1), (44, 1)] }, { coefficient := 1, powers := [(11, 1), (20, 1), (50, 1)] }, { coefficient := 1, powers := [(11, 1), (20, 1), (54, 1)] }, { coefficient := -1, powers := [(11, 1), (26, 1), (44, 1)] }, { coefficient := -1, powers := [(11, 1), (26, 1), (54, 1)] }, { coefficient := 1, powers := [(11, 1), (30, 1), (36, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (16, 1), (20, 1), (22, 1), (52, 1), (57, 1)] }, { coefficient := 1, powers := [(4, 1), (16, 1), (22, 1), (26, 1), (52, 1), (57, 1)] }, { coefficient := 1, powers := [(4, 1), (16, 1), (22, 1), (30, 1), (52, 1), (54, 1)] }, { coefficient := 1, powers := [(4, 1), (16, 1), (22, 1), (33, 1), (50, 1), (52, 1)] }, { coefficient := -1, powers := [(11, 1), (16, 1), (20, 1), (22, 1), (44, 1), (52, 1)] }, { coefficient := -1, powers := [(11, 1), (16, 1), (20, 1), (22, 1), (50, 1), (52, 1)] }, { coefficient := -1, powers := [(11, 1), (16, 1), (20, 1), (22, 1), (52, 1), (54, 1)] }, { coefficient := 1, powers := [(11, 1), (16, 1), (22, 1), (26, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(11, 1), (16, 1), (22, 1), (26, 1), (52, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(36, 1), (57, 1)] }, { coefficient := -1, powers := [(39, 1), (40, 1), (54, 1), (61, 1)] }, { coefficient := 1, powers := [(39, 1), (54, 1)] }, { coefficient := 1, powers := [(44, 1), (50, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (20, 1), (37, 1), (57, 1), (58, 1)] }, { coefficient := -1, powers := [(4, 1), (20, 1), (40, 1), (55, 1), (57, 1)] }, { coefficient := 1, powers := [(4, 1), (26, 1), (37, 1), (57, 1), (58, 1)] }, { coefficient := 1, powers := [(4, 1), (26, 1), (40, 1), (55, 1), (57, 1)] }, { coefficient := 1, powers := [(4, 1), (30, 1), (37, 1), (54, 1), (58, 1)] }, { coefficient := 1, powers := [(4, 1), (30, 1), (40, 1), (54, 1), (55, 1)] }, { coefficient := 1, powers := [(4, 1), (33, 1), (37, 1), (50, 1), (58, 1)] }, { coefficient := 1, powers := [(4, 1), (33, 1), (40, 1), (50, 1), (55, 1)] }, { coefficient := 1, powers := [(7, 1), (30, 1), (37, 1), (44, 1), (58, 1)] }, { coefficient := 1, powers := [(7, 1), (30, 1), (40, 1), (44, 1), (55, 1)] }, { coefficient := -1, powers := [(11, 1), (20, 1), (37, 1), (44, 1), (58, 1)] }, { coefficient := -1, powers := [(11, 1), (20, 1), (37, 1), (50, 1), (58, 1)] }, { coefficient := -1, powers := [(11, 1), (20, 1), (37, 1), (54, 1), (58, 1)] }, { coefficient := 1, powers := [(11, 1), (20, 1), (39, 1), (40, 1), (44, 1), (55, 1), (60, 1)] }, { coefficient := 1, powers := [(11, 1), (20, 1), (39, 1), (40, 1), (50, 1), (55, 1), (60, 1)] }, { coefficient := 1, powers := [(11, 1), (20, 1), (39, 1), (40, 1), (54, 1), (55, 1), (60, 1)] }, { coefficient := -1, powers := [(11, 1), (20, 1), (40, 1), (44, 1), (55, 1)] }, { coefficient := -1, powers := [(11, 1), (20, 1), (40, 1), (50, 1), (55, 1)] }, { coefficient := -1, powers := [(11, 1), (20, 1), (40, 1), (54, 1), (55, 1)] }, { coefficient := 1, powers := [(11, 1), (20, 1), (44, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(11, 1), (20, 1), (46, 1), (50, 1), (52, 1)] }, { coefficient := 1, powers := [(11, 1), (20, 1), (46, 1), (52, 1), (54, 1)] }, { coefficient := 1, powers := [(11, 1), (26, 1), (37, 1), (44, 1), (58, 1)] }, { coefficient := 1, powers := [(11, 1), (26, 1), (37, 1), (54, 1), (58, 1)] }, { coefficient := -1, powers := [(11, 1), (26, 1), (39, 1), (40, 1), (44, 1), (55, 1), (60, 1)] }, { coefficient := -1, powers := [(11, 1), (26, 1), (39, 1), (40, 1), (54, 1), (55, 1), (60, 1)] }, { coefficient := 1, powers := [(11, 1), (26, 1), (40, 1), (44, 1), (55, 1)] }, { coefficient := 1, powers := [(11, 1), (26, 1), (40, 1), (54, 1), (55, 1)] }, { coefficient := -1, powers := [(11, 1), (26, 1), (44, 1), (46, 1), (52, 1)] }, { coefficient := -1, powers := [(11, 1), (26, 1), (46, 1), (52, 1), (54, 1)] }, { coefficient := -1, powers := [(11, 1), (30, 1), (36, 1), (37, 1), (58, 1)] }, { coefficient := -1, powers := [(11, 1), (30, 1), (36, 1), (40, 1), (55, 1)] }, { coefficient := -1, powers := [(11, 1), (30, 1), (36, 1), (46, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (12, 1), (30, 1), (34, 1), (37, 1), (44, 1)] }, { coefficient := 1, powers := [(8, 1), (11, 1), (20, 1), (34, 1), (40, 1), (44, 1)] }, { coefficient := 1, powers := [(8, 1), (11, 1), (20, 1), (34, 1), (40, 1), (50, 1)] }, { coefficient := 1, powers := [(8, 1), (11, 1), (20, 1), (34, 1), (40, 1), (54, 1)] }, { coefficient := -1, powers := [(8, 1), (11, 1), (26, 1), (34, 1), (40, 1), (44, 1)] }, { coefficient := -1, powers := [(8, 1), (11, 1), (26, 1), (34, 1), (40, 1), (54, 1)] }, { coefficient := 1, powers := [(11, 1), (16, 1), (20, 1), (28, 1), (40, 1), (44, 1)] }, { coefficient := 1, powers := [(11, 1), (16, 1), (20, 1), (28, 1), (40, 1), (50, 1)] }, { coefficient := 1, powers := [(11, 1), (16, 1), (20, 1), (28, 1), (40, 1), (54, 1)] }, { coefficient := -1, powers := [(11, 1), (16, 1), (26, 1), (28, 1), (40, 1), (44, 1)] }, { coefficient := -1, powers := [(11, 1), (16, 1), (26, 1), (28, 1), (40, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (33, 1), (39, 1)] }, { coefficient := 1, powers := [(11, 1), (26, 1), (39, 1)] }, { coefficient := 1, powers := [(11, 1), (26, 1), (44, 1)] }, { coefficient := 1, powers := [(11, 1), (26, 1), (54, 1)] }, { coefficient := 1, powers := [(15, 1), (20, 1), (39, 1)] }, { coefficient := 1, powers := [(15, 1), (20, 1), (50, 1)] }, { coefficient := 1, powers := [(15, 1), (20, 1), (54, 1)] }, { coefficient := 1, powers := [(15, 1), (26, 1), (44, 1)] }, { coefficient := 1, powers := [(15, 1), (33, 1), (36, 1)] }]
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
    (values : Fin 62 → R) :
    ¬ ∀ index : Fin 45,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component14.SelectedLeafB4_3.selectedHasNoCommonZero

end Krenn.Component14.SelectedLeafB4_3
