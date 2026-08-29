import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component14.SelectedLeafB4_1_6

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "74d32322026663235456ee97fa184a8df4b115579d80902b46f367c220af5fdb"
def certificateSHA256 : String := "42a589fe5c1e82ff999b702084bcfff9e74c481ae5ddb6cf521d9e18b705d70a"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 30 → Fin 643 := ![
  4,
  7,
  13,
  17,
  24,
  25,
  112,
  170,
  173,
  288,
  313,
  320,
  348,
  349,
  350,
  351,
  410,
  454,
  559,
  579,
  580,
  591,
  632,
  633,
  635,
  636,
  638,
  639,
  640,
  642
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 30 → SparsePoly (Fin 63) := ![
  [{ coefficient := 1, powers := [(4, 1), (34, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (31, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (23, 1)] }],
  [{ coefficient := 1, powers := [(15, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(31, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(34, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (26, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (58, 1)] }, { coefficient := 1, powers := [(7, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (23, 1)] }, { coefficient := 1, powers := [(15, 1), (17, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (23, 1), (43, 1)] }, { coefficient := 1, powers := [(12, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (23, 1), (39, 1)] }, { coefficient := 1, powers := [(16, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (48, 1), (54, 1)] }, { coefficient := 1, powers := [(26, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (46, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (52, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1)] }, { coefficient := 1, powers := [(12, 1), (28, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (58, 1)] }, { coefficient := 1, powers := [(12, 1), (46, 1)] }, { coefficient := 1, powers := [(16, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (58, 1)] }, { coefficient := 1, powers := [(12, 1), (55, 1)] }, { coefficient := 1, powers := [(16, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (22, 1), (58, 1)] }, { coefficient := 1, powers := [(7, 1), (31, 1), (46, 1)] }, { coefficient := 1, powers := [(7, 1), (34, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (45, 1), (48, 1), (54, 1)] }, { coefficient := 1, powers := [(26, 1), (40, 1)] }, { coefficient := 1, powers := [(26, 1), (45, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (32, 1)] }, { coefficient := 1, powers := [(11, 1), (23, 1), (43, 1)] }, { coefficient := 1, powers := [(11, 1), (53, 1)] }, { coefficient := 1, powers := [(14, 1), (23, 1), (39, 1)] }, { coefficient := 1, powers := [(14, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (57, 1)] }, { coefficient := 1, powers := [(7, 1), (57, 1)] }, { coefficient := 1, powers := [(11, 1), (44, 1)] }, { coefficient := 1, powers := [(11, 1), (54, 1)] }, { coefficient := 1, powers := [(15, 1), (39, 1)] }, { coefficient := 1, powers := [(15, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (50, 1)] }, { coefficient := 1, powers := [(20, 1), (54, 1)] }, { coefficient := 1, powers := [(26, 1), (39, 1)] }, { coefficient := 1, powers := [(26, 1), (44, 1)] }, { coefficient := 1, powers := [(30, 1), (36, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (43, 1), (50, 1)] }, { coefficient := 1, powers := [(7, 1), (30, 1), (43, 1)] }, { coefficient := 1, powers := [(11, 1), (26, 1), (43, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1), (50, 1)] }, { coefficient := 1, powers := [(14, 1), (26, 1), (39, 1)] }, { coefficient := 1, powers := [(14, 1), (30, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (36, 1), (57, 1)] }, { coefficient := 1, powers := [(1, 1), (39, 1), (54, 1)] }, { coefficient := 1, powers := [(1, 1), (44, 1), (50, 1)] }, { coefficient := 1, powers := [(4, 1), (26, 1), (57, 1)] }, { coefficient := 1, powers := [(4, 1), (30, 1), (54, 1)] }, { coefficient := 1, powers := [(4, 1), (33, 1), (50, 1)] }, { coefficient := 1, powers := [(7, 1), (20, 1), (57, 1)] }, { coefficient := 1, powers := [(7, 1), (30, 1), (44, 1)] }, { coefficient := 1, powers := [(7, 1), (33, 1), (39, 1)] }, { coefficient := 1, powers := [(11, 1), (20, 1), (54, 1)] }, { coefficient := 1, powers := [(11, 1), (26, 1), (44, 1)] }, { coefficient := 1, powers := [(11, 1), (33, 1), (36, 1)] }, { coefficient := 1, powers := [(15, 1), (20, 1), (50, 1)] }, { coefficient := 1, powers := [(15, 1), (26, 1), (39, 1)] }, { coefficient := 1, powers := [(15, 1), (30, 1), (36, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (37, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (40, 1), (55, 1)] }, { coefficient := 1, powers := [(2, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(5, 1), (28, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (52, 1)] }, { coefficient := 1, powers := [(8, 1), (22, 1), (58, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1), (46, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (40, 1)] }, { coefficient := 1, powers := [(12, 1), (22, 1), (55, 1)] }, { coefficient := 1, powers := [(12, 1), (28, 1), (46, 1)] }, { coefficient := 1, powers := [(12, 1), (34, 1), (37, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1), (52, 1)] }, { coefficient := 1, powers := [(16, 1), (28, 1), (40, 1)] }, { coefficient := 1, powers := [(16, 1), (31, 1), (37, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1)] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(39, 1)] }],
  [{ coefficient := 1, powers := [(40, 1), (60, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(53, 1), (61, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(55, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 30 → SparsePoly (Fin 63) := ![
  [{ coefficient := 1, powers := [(8, 1), (20, 1), (32, 1), (40, 1), (50, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (30, 1), (40, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (40, 1), (50, 1)] }, { coefficient := 1, powers := [(12, 1), (20, 1), (32, 1), (37, 1), (50, 1), (61, 1)] }, { coefficient := 1, powers := [(12, 1), (30, 1), (37, 1), (54, 1)] }, { coefficient := 1, powers := [(12, 1), (33, 1), (37, 1), (50, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (20, 1), (32, 1), (46, 1), (50, 1), (61, 1)] }, { coefficient := -1, powers := [(8, 1), (30, 1), (46, 1), (54, 1)] }, { coefficient := -1, powers := [(8, 1), (33, 1), (46, 1), (50, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (20, 1), (34, 1), (37, 1), (43, 1), (57, 1), (61, 1)] }, { coefficient := 1, powers := [(7, 1), (30, 1), (34, 1), (37, 1), (43, 2), (61, 2)] }, { coefficient := -1, powers := [(7, 1), (30, 1), (34, 1), (37, 1), (43, 1), (44, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(17, 1), (20, 1), (43, 1), (50, 1), (60, 1), (61, 1)] }, { coefficient := -1, powers := [(20, 1), (54, 1), (60, 1)] }, { coefficient := -1, powers := [(26, 1), (44, 1), (60, 1)] }, { coefficient := -1, powers := [(26, 1), (50, 1), (60, 1)] }, { coefficient := -1, powers := [(33, 1), (36, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (11, 1), (30, 1), (46, 1)] }, { coefficient := -1, powers := [(8, 1), (14, 1), (30, 1), (46, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (11, 1), (30, 1), (40, 1)] }, { coefficient := -1, powers := [(8, 1), (14, 1), (30, 1), (40, 1), (61, 1)] }, { coefficient := -1, powers := [(11, 1), (12, 1), (30, 1), (37, 1)] }, { coefficient := -1, powers := [(12, 1), (14, 1), (30, 1), (37, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(44, 1), (60, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (20, 1), (28, 1), (32, 1), (50, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (28, 1), (30, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (28, 1), (33, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (43, 1), (50, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (20, 1), (34, 1), (37, 1), (57, 1), (61, 1)] }, { coefficient := -1, powers := [(7, 1), (30, 1), (34, 1), (37, 1), (43, 1), (61, 2)] }, { coefficient := 1, powers := [(7, 1), (30, 1), (34, 1), (37, 1), (44, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (20, 1), (22, 1), (32, 1), (50, 1), (52, 1), (61, 1)] }, { coefficient := 1, powers := [(4, 1), (20, 1), (28, 1), (32, 1), (40, 1), (50, 1), (61, 1)] }, { coefficient := 1, powers := [(4, 1), (20, 1), (31, 1), (32, 1), (37, 1), (50, 1), (61, 1)] }, { coefficient := -1, powers := [(4, 1), (22, 1), (30, 1), (52, 1), (54, 1)] }, { coefficient := -1, powers := [(4, 1), (22, 1), (33, 1), (50, 1), (52, 1)] }, { coefficient := 1, powers := [(4, 1), (28, 1), (30, 1), (40, 1), (54, 1)] }, { coefficient := 1, powers := [(4, 1), (28, 1), (33, 1), (40, 1), (50, 1)] }, { coefficient := 1, powers := [(4, 1), (30, 1), (31, 1), (37, 1), (54, 1)] }, { coefficient := 1, powers := [(4, 1), (31, 1), (33, 1), (37, 1), (50, 1)] }, { coefficient := 1, powers := [(7, 1), (20, 1), (28, 1), (32, 1), (40, 1), (50, 1), (61, 1)] }, { coefficient := 1, powers := [(7, 1), (20, 1), (31, 1), (37, 1), (57, 1)] }, { coefficient := 1, powers := [(7, 1), (28, 1), (30, 1), (40, 1), (54, 1)] }, { coefficient := 1, powers := [(7, 1), (28, 1), (33, 1), (40, 1), (50, 1)] }, { coefficient := -1, powers := [(7, 1), (30, 1), (31, 1), (37, 1), (43, 1), (61, 1)] }, { coefficient := 1, powers := [(7, 1), (30, 1), (31, 1), (37, 1), (44, 1)] }, { coefficient := 1, powers := [(11, 1), (22, 1), (30, 1), (36, 1), (52, 1)] }, { coefficient := -1, powers := [(11, 1), (30, 1), (31, 1), (36, 1), (37, 1)] }, { coefficient := 1, powers := [(14, 1), (22, 1), (30, 1), (36, 1), (52, 1), (61, 1)] }, { coefficient := -1, powers := [(14, 1), (30, 1), (31, 1), (36, 1), (37, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (45, 1), (57, 1), (60, 1)] }, { coefficient := 1, powers := [(11, 1), (43, 1), (45, 1), (60, 1), (61, 1)] }, { coefficient := 1, powers := [(11, 1), (44, 1), (45, 1), (60, 1)] }, { coefficient := 1, powers := [(11, 1), (45, 1), (54, 1), (60, 1)] }, { coefficient := 1, powers := [(14, 1), (44, 1), (45, 1), (60, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (20, 1), (32, 1), (50, 1), (52, 1), (61, 1)] }, { coefficient := 1, powers := [(4, 1), (30, 1), (52, 1), (54, 1)] }, { coefficient := 1, powers := [(4, 1), (33, 1), (50, 1), (52, 1)] }, { coefficient := 1, powers := [(7, 1), (20, 1), (52, 1), (57, 1)] }, { coefficient := -1, powers := [(7, 1), (30, 1), (43, 1), (52, 1), (61, 1)] }, { coefficient := 1, powers := [(7, 1), (30, 1), (44, 1), (52, 1)] }, { coefficient := -1, powers := [(11, 1), (30, 1), (36, 1), (52, 1)] }, { coefficient := -1, powers := [(14, 1), (30, 1), (36, 1), (52, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (20, 1), (32, 1), (46, 1), (50, 1), (61, 1)] }, { coefficient := 1, powers := [(4, 1), (30, 1), (46, 1), (54, 1)] }, { coefficient := 1, powers := [(4, 1), (33, 1), (46, 1), (50, 1)] }, { coefficient := 1, powers := [(7, 1), (20, 1), (32, 1), (46, 1), (50, 1), (61, 1)] }, { coefficient := 1, powers := [(7, 1), (30, 1), (46, 1), (54, 1)] }, { coefficient := 1, powers := [(7, 1), (33, 1), (46, 1), (50, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (20, 1), (28, 1), (32, 1), (50, 1), (61, 1)] }, { coefficient := 1, powers := [(7, 1), (20, 1), (28, 1), (57, 1)] }, { coefficient := -1, powers := [(7, 1), (28, 1), (30, 1), (43, 1), (61, 1)] }, { coefficient := 1, powers := [(7, 1), (28, 1), (30, 1), (44, 1)] }, { coefficient := -1, powers := [(7, 1), (28, 1), (30, 1), (54, 1)] }, { coefficient := -1, powers := [(7, 1), (28, 1), (33, 1), (50, 1)] }, { coefficient := -1, powers := [(11, 1), (28, 1), (30, 1), (36, 1)] }, { coefficient := -1, powers := [(14, 1), (28, 1), (30, 1), (36, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (20, 1), (22, 1), (32, 1), (50, 1), (61, 1)] }, { coefficient := 1, powers := [(4, 1), (22, 1), (30, 1), (54, 1)] }, { coefficient := 1, powers := [(4, 1), (22, 1), (33, 1), (50, 1)] }, { coefficient := -1, powers := [(11, 1), (22, 1), (30, 1), (36, 1)] }, { coefficient := -1, powers := [(14, 1), (22, 1), (30, 1), (36, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (20, 1), (57, 1)] }, { coefficient := -1, powers := [(8, 1), (30, 1), (43, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (30, 1), (44, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (57, 1), (60, 1)] }, { coefficient := -1, powers := [(11, 1), (43, 1), (60, 1), (61, 1)] }, { coefficient := -1, powers := [(11, 1), (44, 1), (60, 1)] }, { coefficient := -1, powers := [(11, 1), (54, 1), (60, 1)] }, { coefficient := -1, powers := [(14, 1), (44, 1), (60, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(20, 1), (50, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(26, 1)] }],
  [{ coefficient := 1, powers := [(11, 1)] }, { coefficient := 1, powers := [(15, 1)] }],
  [{ coefficient := 1, powers := [(61, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(4, 1), (20, 1), (32, 1), (50, 1), (61, 1)] }, { coefficient := -1, powers := [(4, 1), (30, 1), (54, 1)] }, { coefficient := -1, powers := [(4, 1), (33, 1), (50, 1)] }, { coefficient := -1, powers := [(7, 1), (20, 1), (57, 1)] }, { coefficient := 1, powers := [(7, 1), (30, 1), (43, 1), (61, 1)] }, { coefficient := -1, powers := [(7, 1), (30, 1), (44, 1)] }, { coefficient := 1, powers := [(11, 1), (30, 1), (36, 1)] }, { coefficient := 1, powers := [(14, 1), (30, 1), (36, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(36, 1), (57, 1)] }, { coefficient := 1, powers := [(39, 1), (54, 1)] }, { coefficient := -1, powers := [(43, 1), (50, 1), (61, 1)] }, { coefficient := 1, powers := [(44, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (20, 1), (32, 1), (37, 1), (50, 1), (58, 1), (61, 1)] }, { coefficient := 1, powers := [(4, 1), (20, 1), (32, 1), (40, 1), (50, 1), (55, 1), (61, 1)] }, { coefficient := -1, powers := [(4, 1), (20, 1), (32, 1), (46, 1), (50, 1), (52, 1), (61, 1)] }, { coefficient := 1, powers := [(4, 1), (30, 1), (37, 1), (54, 1), (58, 1)] }, { coefficient := 1, powers := [(4, 1), (30, 1), (40, 1), (54, 1), (55, 1)] }, { coefficient := -1, powers := [(4, 1), (30, 1), (46, 1), (52, 1), (54, 1)] }, { coefficient := 1, powers := [(4, 1), (33, 1), (37, 1), (50, 1), (58, 1)] }, { coefficient := 1, powers := [(4, 1), (33, 1), (40, 1), (50, 1), (55, 1)] }, { coefficient := -1, powers := [(4, 1), (33, 1), (46, 1), (50, 1), (52, 1)] }, { coefficient := -1, powers := [(7, 1), (20, 1), (32, 1), (46, 1), (50, 1), (52, 1), (61, 1)] }, { coefficient := 1, powers := [(7, 1), (20, 1), (37, 1), (57, 1), (58, 1)] }, { coefficient := 1, powers := [(7, 1), (20, 1), (40, 1), (55, 1), (57, 1)] }, { coefficient := -1, powers := [(7, 1), (30, 1), (37, 1), (43, 1), (58, 1), (61, 1)] }, { coefficient := 1, powers := [(7, 1), (30, 1), (37, 1), (44, 1), (58, 1)] }, { coefficient := -1, powers := [(7, 1), (30, 1), (40, 1), (43, 1), (55, 1), (61, 1)] }, { coefficient := 1, powers := [(7, 1), (30, 1), (40, 1), (44, 1), (55, 1)] }, { coefficient := -1, powers := [(7, 1), (30, 1), (46, 1), (52, 1), (54, 1)] }, { coefficient := -1, powers := [(7, 1), (33, 1), (46, 1), (50, 1), (52, 1)] }, { coefficient := -1, powers := [(11, 1), (30, 1), (36, 1), (37, 1), (58, 1)] }, { coefficient := -1, powers := [(11, 1), (30, 1), (36, 1), (40, 1), (55, 1)] }, { coefficient := -1, powers := [(14, 1), (30, 1), (36, 1), (37, 1), (58, 1), (61, 1)] }, { coefficient := -1, powers := [(14, 1), (30, 1), (36, 1), (40, 1), (55, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (16, 1), (20, 1), (22, 1), (23, 1), (32, 1), (50, 1), (52, 1), (61, 1)] }, { coefficient := -1, powers := [(4, 1), (16, 1), (20, 1), (23, 1), (28, 1), (32, 1), (40, 1), (50, 1), (61, 1)] }, { coefficient := -1, powers := [(4, 1), (16, 1), (20, 1), (23, 1), (31, 1), (32, 1), (37, 1), (50, 1), (61, 1)] }, { coefficient := 1, powers := [(4, 1), (16, 1), (22, 1), (23, 1), (30, 1), (52, 1), (54, 1)] }, { coefficient := 1, powers := [(4, 1), (16, 1), (22, 1), (23, 1), (33, 1), (50, 1), (52, 1)] }, { coefficient := -1, powers := [(4, 1), (16, 1), (23, 1), (28, 1), (30, 1), (40, 1), (54, 1)] }, { coefficient := -1, powers := [(4, 1), (16, 1), (23, 1), (28, 1), (33, 1), (40, 1), (50, 1)] }, { coefficient := -1, powers := [(4, 1), (16, 1), (23, 1), (30, 1), (31, 1), (37, 1), (54, 1)] }, { coefficient := -1, powers := [(4, 1), (16, 1), (23, 1), (31, 1), (33, 1), (37, 1), (50, 1)] }, { coefficient := -1, powers := [(7, 1), (16, 1), (20, 1), (23, 1), (28, 1), (32, 1), (40, 1), (50, 1), (61, 1)] }, { coefficient := -1, powers := [(7, 1), (16, 1), (20, 1), (23, 1), (31, 1), (37, 1), (57, 1)] }, { coefficient := -1, powers := [(7, 1), (16, 1), (23, 1), (28, 1), (30, 1), (40, 1), (54, 1)] }, { coefficient := -1, powers := [(7, 1), (16, 1), (23, 1), (28, 1), (33, 1), (40, 1), (50, 1)] }, { coefficient := 1, powers := [(7, 1), (16, 1), (23, 1), (30, 1), (31, 1), (37, 1), (43, 1), (61, 1)] }, { coefficient := -1, powers := [(7, 1), (16, 1), (23, 1), (30, 1), (31, 1), (37, 1), (44, 1)] }, { coefficient := 1, powers := [(7, 1), (33, 1)] }, { coefficient := -1, powers := [(11, 1), (16, 1), (22, 1), (23, 1), (30, 1), (36, 1), (52, 1)] }, { coefficient := 1, powers := [(11, 1), (16, 1), (23, 1), (30, 1), (31, 1), (36, 1), (37, 1)] }, { coefficient := -1, powers := [(11, 1), (26, 1)] }, { coefficient := -1, powers := [(14, 1), (16, 1), (22, 1), (23, 1), (30, 1), (36, 1), (52, 1), (61, 1)] }, { coefficient := 1, powers := [(14, 1), (16, 1), (23, 1), (30, 1), (31, 1), (36, 1), (37, 1), (61, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1), (23, 1), (50, 1), (61, 1)] }, { coefficient := -1, powers := [(14, 1), (26, 1), (61, 1)] }, { coefficient := -1, powers := [(15, 1), (26, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (26, 1), (57, 1)] }, { coefficient := 1, powers := [(11, 1), (26, 1), (43, 1), (61, 1)] }, { coefficient := 1, powers := [(11, 1), (26, 1), (44, 1)] }, { coefficient := 1, powers := [(11, 1), (26, 1), (54, 1)] }, { coefficient := 1, powers := [(15, 1), (17, 1), (20, 1), (43, 1), (50, 1), (61, 1)] }, { coefficient := 1, powers := [(15, 1), (20, 1), (54, 1)] }, { coefficient := 1, powers := [(15, 1), (26, 1), (44, 1)] }, { coefficient := 1, powers := [(15, 1), (26, 1), (50, 1)] }, { coefficient := 1, powers := [(15, 1), (33, 1), (36, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (12, 1), (20, 1), (34, 1), (37, 1), (57, 1)] }, { coefficient := 1, powers := [(7, 1), (12, 1), (30, 1), (34, 1), (37, 1), (43, 1), (61, 1)] }, { coefficient := -1, powers := [(7, 1), (12, 1), (30, 1), (34, 1), (37, 1), (44, 1)] }, { coefficient := 1, powers := [(11, 1), (20, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (5, 1), (20, 1), (31, 1), (32, 1), (50, 1), (61, 1)] }, { coefficient := 1, powers := [(4, 1), (5, 1), (30, 1), (31, 1), (54, 1)] }, { coefficient := 1, powers := [(4, 1), (5, 1), (31, 1), (33, 1), (50, 1)] }, { coefficient := 1, powers := [(5, 1), (7, 1), (20, 1), (31, 1), (57, 1)] }, { coefficient := -1, powers := [(5, 1), (7, 1), (30, 1), (31, 1), (43, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (7, 1), (30, 1), (31, 1), (44, 1)] }, { coefficient := -1, powers := [(5, 1), (11, 1), (30, 1), (31, 1), (36, 1)] }, { coefficient := -1, powers := [(5, 1), (14, 1), (30, 1), (31, 1), (36, 1), (61, 1)] }, { coefficient := 1, powers := [(7, 1), (12, 1), (20, 1), (22, 1), (57, 1)] }, { coefficient := -1, powers := [(7, 1), (12, 1), (22, 1), (30, 1), (43, 1), (61, 1)] }, { coefficient := 1, powers := [(7, 1), (12, 1), (22, 1), (30, 1), (44, 1)] }]
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
    ¬ ∀ index : Fin 30,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component14.SelectedLeafB4_1_6.selectedHasNoCommonZero

end Krenn.Component14.SelectedLeafB4_1_6
