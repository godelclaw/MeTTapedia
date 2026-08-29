import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component48.SelectedLeafB6_1

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "2ce3ac4adb932560e35577fe27a434c8a7e7552833a66256e93e3298d2e820e5"
def certificateSHA256 : String := "ed7f5e57c99f3d22ab45e3465294456a22eb8949527b7e000d6c042f0e96e0ab"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 46 → Fin 641 := ![
  2,
  3,
  4,
  14,
  29,
  30,
  45,
  161,
  162,
  169,
  171,
  173,
  176,
  178,
  179,
  200,
  206,
  207,
  228,
  239,
  252,
  258,
  345,
  348,
  359,
  360,
  365,
  384,
  393,
  395,
  404,
  443,
  478,
  560,
  576,
  577,
  621,
  628,
  632,
  634,
  635,
  636,
  637,
  638,
  639,
  640
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 46 → SparsePoly (Fin 63) := ![
  [{ coefficient := 1, powers := [(3, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(15, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (33, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1)] }, { coefficient := 1, powers := [(25, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (48, 1)] }, { coefficient := 1, powers := [(25, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (51, 1)] }, { coefficient := 1, powers := [(12, 1), (29, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (36, 1)] }, { coefficient := 1, powers := [(36, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (33, 1)] }, { coefficient := 1, powers := [(33, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (31, 1)] }, { coefficient := 1, powers := [(18, 1), (26, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (29, 1)] }, { coefficient := 1, powers := [(29, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (30, 1)] }, { coefficient := 1, powers := [(30, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (51, 1)] }, { coefficient := 1, powers := [(29, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1), (51, 1)] }, { coefficient := 1, powers := [(13, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1), (53, 1)] }, { coefficient := 1, powers := [(13, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (30, 1), (58, 1)] }, { coefficient := 1, powers := [(30, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (24, 1), (58, 1)] }, { coefficient := 1, powers := [(24, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (31, 1), (44, 1)] }, { coefficient := 1, powers := [(8, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (24, 1), (55, 1)] }, { coefficient := 1, powers := [(9, 1), (29, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (49, 1)] }, { coefficient := 1, powers := [(15, 1), (22, 1), (49, 1)] }, { coefficient := 1, powers := [(15, 1), (27, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (48, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (53, 1)] }, { coefficient := 1, powers := [(30, 1), (42, 1)] }, { coefficient := 1, powers := [(33, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (56, 1)] }, { coefficient := 1, powers := [(30, 1), (48, 1)] }, { coefficient := 1, powers := [(36, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1), (54, 1)] }, { coefficient := 1, powers := [(6, 1), (34, 1), (42, 1)] }, { coefficient := 1, powers := [(13, 1), (25, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (39, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (57, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (30, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (33, 1), (56, 1)] }, { coefficient := 1, powers := [(3, 1), (36, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (36, 1), (49, 1)] }, { coefficient := 1, powers := [(6, 1), (36, 1), (40, 1)] }, { coefficient := 1, powers := [(9, 1), (36, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (24, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (33, 1), (48, 1)] }, { coefficient := 1, powers := [(6, 1), (36, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (21, 1), (44, 1), (51, 1)] }, { coefficient := 1, powers := [(13, 1), (21, 1), (51, 1)] }, { coefficient := 1, powers := [(13, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (41, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(26, 1), (46, 1)] }, { coefficient := 1, powers := [(56, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (40, 1), (55, 1)] }, { coefficient := 1, powers := [(3, 1), (31, 1), (55, 1)] }, { coefficient := 1, powers := [(9, 1), (20, 1), (55, 1)] }, { coefficient := 1, powers := [(9, 1)] }, { coefficient := 1, powers := [(40, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1)] }, { coefficient := 1, powers := [(3, 1), (34, 1)] }, { coefficient := 1, powers := [(13, 1), (20, 1)] }, { coefficient := 1, powers := [(20, 1), (54, 1)] }, { coefficient := 1, powers := [(25, 1), (43, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (49, 1)] }, { coefficient := 1, powers := [(6, 1), (31, 1)] }, { coefficient := 1, powers := [(9, 1), (25, 1)] }, { coefficient := 1, powers := [(20, 1), (49, 1)] }, { coefficient := 1, powers := [(25, 1), (40, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (41, 1), (54, 1)] }, { coefficient := 1, powers := [(0, 1), (44, 1)] }, { coefficient := 1, powers := [(6, 1), (34, 1), (41, 1)] }, { coefficient := 1, powers := [(13, 1), (25, 1), (41, 1)] }, { coefficient := 1, powers := [(13, 1)] }, { coefficient := 1, powers := [(25, 1), (44, 1)] }, { coefficient := 1, powers := [(54, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (42, 1), (55, 1)] }, { coefficient := 1, powers := [(2, 1), (47, 1), (51, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (55, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (55, 1)] }, { coefficient := 1, powers := [(12, 1), (29, 1), (47, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (51, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (37, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (40, 1), (54, 1)] }, { coefficient := 1, powers := [(0, 1), (43, 1), (49, 1)] }, { coefficient := 1, powers := [(3, 1), (25, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (31, 1), (54, 1)] }, { coefficient := 1, powers := [(3, 1), (34, 1), (49, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1), (57, 1)] }, { coefficient := 1, powers := [(6, 1), (31, 1), (43, 1)] }, { coefficient := 1, powers := [(6, 1), (34, 1), (40, 1)] }, { coefficient := 1, powers := [(9, 1), (20, 1), (54, 1)] }, { coefficient := 1, powers := [(9, 1), (25, 1), (43, 1)] }, { coefficient := 1, powers := [(9, 1), (34, 1), (37, 1)] }, { coefficient := 1, powers := [(13, 1), (20, 1), (49, 1)] }, { coefficient := 1, powers := [(13, 1), (25, 1), (40, 1)] }, { coefficient := 1, powers := [(13, 1), (31, 1), (37, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (39, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (42, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (48, 1), (53, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1), (53, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (59, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (48, 1)] }, { coefficient := 1, powers := [(8, 1), (36, 1), (42, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (56, 1)] }, { coefficient := 1, powers := [(12, 1), (30, 1), (48, 1)] }, { coefficient := 1, powers := [(12, 1), (36, 1), (39, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (53, 1)] }, { coefficient := 1, powers := [(19, 1), (30, 1), (42, 1)] }, { coefficient := 1, powers := [(19, 1), (33, 1), (39, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (60, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1), (61, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(40, 1)] }],
  [{ coefficient := 1, powers := [(41, 1)] }],
  [{ coefficient := 1, powers := [(42, 1), (62, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 46 → SparsePoly (Fin 63) := ![
  [{ coefficient := -1, powers := [(3, 1), (5, 1), (30, 1), (31, 1), (54, 1), (58, 1)] }, { coefficient := -1, powers := [(5, 1), (9, 1), (20, 1), (30, 1), (54, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (9, 1), (30, 1), (34, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (31, 1), (37, 1), (43, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (34, 1), (37, 1), (49, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (36, 1), (37, 1), (53, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1), (36, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (8, 1), (24, 1), (31, 1), (34, 1), (60, 1)] }, { coefficient := -1, powers := [(3, 1), (8, 1), (24, 1), (31, 1), (54, 1), (58, 1)] }, { coefficient := -1, powers := [(5, 1), (24, 1), (31, 1), (37, 1), (43, 1), (53, 1), (58, 1), (62, 1)] }, { coefficient := 1, powers := [(8, 1), (9, 1), (20, 1), (24, 1), (34, 1), (60, 1)] }, { coefficient := -1, powers := [(8, 1), (9, 1), (20, 1), (24, 1), (54, 1), (58, 1)] }, { coefficient := -1, powers := [(8, 1), (9, 1), (24, 1), (34, 1), (37, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (22, 1), (43, 1), (61, 1)] }, { coefficient := 1, powers := [(20, 1), (22, 1), (43, 1), (61, 1)] }, { coefficient := 1, powers := [(20, 1), (22, 1), (54, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (34, 1), (37, 1), (59, 1)] }, { coefficient := 1, powers := [(19, 1), (34, 1), (37, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (5, 1), (26, 1), (33, 1), (37, 1), (46, 1), (57, 1), (60, 1), (62, 1)] }, { coefficient := 1, powers := [(0, 1), (5, 1), (33, 1), (37, 1), (46, 1), (52, 1), (57, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 1), (8, 1), (33, 1), (37, 1), (48, 1), (57, 1), (60, 1), (62, 1)] }, { coefficient := 1, powers := [(3, 1), (5, 1), (26, 1), (31, 1), (33, 1), (46, 1), (54, 1), (60, 1), (62, 1)] }, { coefficient := 1, powers := [(3, 1), (5, 1), (31, 1), (33, 1), (46, 1), (52, 1), (54, 1), (62, 1)] }, { coefficient := -1, powers := [(3, 1), (5, 1), (31, 1), (36, 1), (44, 1), (53, 1), (62, 1)] }, { coefficient := -1, powers := [(3, 1), (8, 1), (13, 1), (31, 1), (36, 1), (60, 1)] }, { coefficient := 1, powers := [(3, 1), (8, 1), (31, 1), (33, 1), (34, 1), (37, 1), (48, 1), (60, 2), (62, 1)] }, { coefficient := -1, powers := [(3, 1), (8, 1), (31, 1), (33, 1), (48, 1), (54, 1), (60, 1), (62, 1)] }, { coefficient := 1, powers := [(3, 1), (57, 1), (62, 1)] }, { coefficient := 1, powers := [(5, 1), (6, 1), (20, 1), (26, 1), (33, 1), (46, 1), (57, 1), (60, 1), (62, 1)] }, { coefficient := 1, powers := [(5, 1), (6, 1), (20, 1), (33, 1), (46, 1), (52, 1), (57, 1), (62, 1)] }, { coefficient := 1, powers := [(5, 1), (9, 1), (20, 1), (26, 1), (33, 1), (46, 1), (54, 1), (60, 1), (62, 1)] }, { coefficient := 1, powers := [(5, 1), (9, 1), (20, 1), (33, 1), (46, 1), (52, 1), (54, 1), (62, 1)] }, { coefficient := -1, powers := [(5, 1), (9, 1), (20, 1), (36, 1), (44, 1), (53, 1), (62, 1)] }, { coefficient := 1, powers := [(5, 1), (9, 1), (26, 1), (33, 1), (34, 1), (37, 1), (46, 1), (60, 1), (62, 1)] }, { coefficient := 1, powers := [(5, 1), (9, 1), (33, 1), (34, 1), (37, 1), (46, 1), (52, 1), (62, 1)] }, { coefficient := -1, powers := [(5, 1), (26, 1), (31, 1), (33, 1), (37, 1), (43, 1), (46, 1), (60, 1), (62, 1)] }, { coefficient := -1, powers := [(5, 1), (26, 1), (33, 1), (34, 1), (37, 1), (46, 1), (49, 1), (60, 1), (62, 1)] }, { coefficient := -1, powers := [(5, 1), (31, 1), (33, 1), (37, 2), (43, 1), (48, 1), (53, 1), (58, 1), (60, 1), (62, 2)] }, { coefficient := -1, powers := [(5, 1), (31, 1), (33, 1), (37, 1), (43, 1), (46, 1), (52, 1), (62, 1)] }, { coefficient := -1, powers := [(5, 1), (33, 1), (34, 1), (37, 1), (46, 1), (49, 1), (52, 1), (62, 1)] }, { coefficient := -1, powers := [(6, 1), (8, 1), (20, 1), (33, 1), (48, 1), (57, 1), (60, 1), (62, 1)] }, { coefficient := -1, powers := [(8, 1), (9, 1), (13, 1), (20, 1), (36, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (9, 1), (20, 1), (33, 1), (34, 1), (37, 1), (48, 1), (60, 2), (62, 1)] }, { coefficient := -1, powers := [(8, 1), (9, 1), (20, 1), (33, 1), (48, 1), (54, 1), (60, 1), (62, 1)] }, { coefficient := -1, powers := [(8, 1), (9, 1), (33, 1), (34, 1), (37, 1), (48, 1), (60, 1), (62, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1), (33, 1), (37, 1), (43, 1), (48, 1), (60, 1), (62, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (34, 1), (37, 1), (48, 1), (49, 1), (60, 1), (62, 1)] }, { coefficient := -1, powers := [(43, 1), (49, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (5, 1), (31, 1), (34, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (5, 1), (26, 1), (33, 1), (37, 1), (57, 1), (60, 1)] }, { coefficient := -1, powers := [(0, 1), (5, 1), (33, 1), (37, 1), (52, 1), (57, 1)] }, { coefficient := -1, powers := [(3, 1), (5, 1), (26, 1), (31, 1), (33, 1), (54, 1), (60, 1)] }, { coefficient := -1, powers := [(3, 1), (5, 1), (31, 1), (33, 1), (52, 1), (54, 1)] }, { coefficient := -1, powers := [(5, 1), (6, 1), (20, 1), (26, 1), (33, 1), (57, 1), (60, 1)] }, { coefficient := -1, powers := [(5, 1), (6, 1), (20, 1), (33, 1), (52, 1), (57, 1)] }, { coefficient := -1, powers := [(5, 1), (9, 1), (20, 1), (26, 1), (33, 1), (54, 1), (60, 1)] }, { coefficient := -1, powers := [(5, 1), (9, 1), (20, 1), (33, 1), (52, 1), (54, 1)] }, { coefficient := -1, powers := [(5, 1), (9, 1), (26, 1), (33, 1), (34, 1), (37, 1), (60, 1)] }, { coefficient := -1, powers := [(5, 1), (9, 1), (33, 1), (34, 1), (37, 1), (52, 1)] }, { coefficient := 1, powers := [(5, 1), (26, 1), (31, 1), (33, 1), (37, 1), (43, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (26, 1), (33, 1), (34, 1), (37, 1), (49, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (33, 1), (37, 1), (43, 1), (52, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (34, 1), (37, 1), (49, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (8, 1), (33, 1), (37, 1), (57, 1), (60, 1)] }, { coefficient := -1, powers := [(3, 1), (8, 1), (31, 1), (33, 1), (34, 1), (37, 1), (60, 2)] }, { coefficient := 1, powers := [(3, 1), (8, 1), (31, 1), (33, 1), (54, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (33, 1), (37, 2), (43, 1), (53, 1), (58, 1), (60, 1), (62, 1)] }, { coefficient := 1, powers := [(6, 1), (8, 1), (20, 1), (33, 1), (57, 1), (60, 1)] }, { coefficient := -1, powers := [(8, 1), (9, 1), (20, 1), (33, 1), (34, 1), (37, 1), (60, 2)] }, { coefficient := 1, powers := [(8, 1), (9, 1), (20, 1), (33, 1), (54, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (9, 1), (33, 1), (34, 1), (37, 1), (60, 1)] }, { coefficient := -1, powers := [(8, 1), (31, 1), (33, 1), (37, 1), (43, 1), (60, 1)] }, { coefficient := -1, powers := [(8, 1), (33, 1), (34, 1), (37, 1), (49, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (9, 1), (20, 1), (34, 1), (47, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (9, 1), (34, 1), (53, 1)] }, { coefficient := -1, powers := [(8, 1), (34, 1), (42, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (8, 1), (31, 1), (34, 1), (48, 1), (60, 1)] }, { coefficient := -1, powers := [(5, 1), (31, 1), (37, 1), (43, 1), (48, 1), (53, 1), (58, 1), (62, 1)] }, { coefficient := 1, powers := [(8, 1), (9, 1), (20, 1), (34, 1), (48, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (36, 1), (37, 1), (42, 1), (44, 1)] }, { coefficient := -1, powers := [(6, 1), (20, 1), (36, 1), (42, 1), (44, 1)] }, { coefficient := -1, powers := [(24, 1), (37, 1), (43, 1), (59, 1)] }, { coefficient := -1, powers := [(36, 1), (37, 1), (42, 1), (43, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (12, 1), (20, 1), (34, 1), (47, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (34, 1), (37, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (9, 1), (18, 1), (20, 1), (34, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [(21, 1), (31, 1), (37, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (5, 1), (31, 1), (36, 1)] }, { coefficient := -1, powers := [(5, 1), (9, 1), (20, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (5, 1), (31, 1), (54, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (9, 1), (20, 1), (54, 1), (59, 1)] }, { coefficient := -1, powers := [(5, 1), (31, 1), (37, 1), (43, 1), (59, 1)] }, { coefficient := -1, powers := [(5, 1), (34, 1), (37, 1), (49, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (8, 1), (31, 1), (54, 1), (59, 1)] }, { coefficient := 1, powers := [(8, 1), (9, 1), (20, 1), (54, 1), (59, 1)] }, { coefficient := 1, powers := [(8, 1), (9, 1), (34, 1), (37, 1), (59, 1)] }, { coefficient := 1, powers := [(19, 1), (31, 1), (37, 1), (43, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (36, 1), (37, 1), (42, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1), (36, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (12, 1), (20, 1), (34, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (43, 1), (61, 1)] }, { coefficient := -1, powers := [(20, 1), (43, 1), (61, 1)] }, { coefficient := -1, powers := [(20, 1), (54, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (31, 1), (37, 1), (43, 1), (53, 1), (58, 1)] }, { coefficient := -1, powers := [(31, 1), (37, 1), (43, 1), (53, 1)] }, { coefficient := -1, powers := [(34, 1), (37, 1), (49, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (19, 1), (37, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (19, 1), (31, 1), (54, 1)] }, { coefficient := 1, powers := [(6, 1), (19, 1), (20, 1), (57, 1)] }, { coefficient := 1, powers := [(9, 1), (19, 1), (20, 1), (54, 1)] }, { coefficient := 1, powers := [(9, 1), (19, 1), (34, 1), (37, 1)] }, { coefficient := -1, powers := [(19, 1), (31, 1), (37, 1), (43, 1)] }, { coefficient := -1, powers := [(19, 1), (34, 1), (37, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (12, 1), (37, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (12, 1), (31, 1), (54, 1)] }, { coefficient := 1, powers := [(6, 1), (12, 1), (20, 1), (57, 1)] }, { coefficient := 1, powers := [(9, 1), (12, 1), (20, 1), (54, 1)] }, { coefficient := 1, powers := [(9, 1), (12, 1), (34, 1), (37, 1)] }, { coefficient := -1, powers := [(12, 1), (31, 1), (37, 1), (43, 1)] }, { coefficient := -1, powers := [(12, 1), (34, 1), (37, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (8, 1), (31, 1), (36, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (9, 1), (20, 1), (36, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (37, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (9, 1), (34, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (34, 1), (42, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (8, 1), (31, 1), (34, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (37, 1), (43, 1), (53, 1), (58, 1), (62, 1)] }, { coefficient := -1, powers := [(8, 1), (9, 1), (20, 1), (34, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(31, 1), (37, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (5, 1), (33, 1), (37, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (5, 1), (31, 1), (33, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (6, 1), (20, 1), (33, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (9, 1), (20, 1), (33, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (9, 1), (33, 1), (34, 1), (37, 1)] }, { coefficient := -1, powers := [(5, 1), (31, 1), (33, 1), (37, 1), (43, 1)] }, { coefficient := -1, powers := [(5, 1), (33, 1), (34, 1), (37, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (5, 1), (33, 1), (34, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(49, 1)] }],
  [{ coefficient := 1, powers := [(43, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (5, 1), (31, 1), (36, 1), (53, 1)] }, { coefficient := 1, powers := [(5, 1), (9, 1), (20, 1), (36, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (9, 1), (20, 1), (34, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(0, 1), (37, 1), (57, 1)] }, { coefficient := -1, powers := [(3, 1), (31, 1), (54, 1)] }, { coefficient := -1, powers := [(6, 1), (20, 1), (57, 1)] }, { coefficient := -1, powers := [(9, 1), (20, 1), (54, 1)] }, { coefficient := -1, powers := [(9, 1), (34, 1), (37, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1), (43, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (5, 1), (26, 1), (33, 1), (37, 1), (46, 1), (57, 1)] }, { coefficient := -1, powers := [(0, 1), (8, 1), (33, 1), (37, 1), (48, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (5, 1), (26, 1), (31, 1), (33, 1), (46, 1), (54, 1)] }, { coefficient := 1, powers := [(3, 1), (8, 1), (31, 1), (33, 1), (34, 1), (37, 1), (48, 1), (60, 1)] }, { coefficient := -1, powers := [(3, 1), (8, 1), (31, 1), (33, 1), (48, 1), (54, 1)] }, { coefficient := -1, powers := [(3, 1), (8, 1), (31, 1), (36, 1), (42, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (6, 1), (20, 1), (26, 1), (33, 1), (46, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (9, 1), (20, 1), (26, 1), (33, 1), (46, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (9, 1), (26, 1), (33, 1), (34, 1), (37, 1), (46, 1)] }, { coefficient := -1, powers := [(5, 1), (26, 1), (31, 1), (33, 1), (37, 1), (43, 1), (46, 1)] }, { coefficient := -1, powers := [(5, 1), (26, 1), (33, 1), (34, 1), (37, 1), (46, 1), (49, 1)] }, { coefficient := -1, powers := [(5, 1), (31, 1), (33, 1), (37, 2), (43, 1), (48, 1), (53, 1), (58, 1), (62, 1)] }, { coefficient := -1, powers := [(6, 1), (8, 1), (20, 1), (33, 1), (48, 1), (57, 1)] }, { coefficient := 1, powers := [(8, 1), (9, 1), (20, 1), (33, 1), (34, 1), (37, 1), (48, 1), (60, 1)] }, { coefficient := -1, powers := [(8, 1), (9, 1), (20, 1), (33, 1), (48, 1), (54, 1)] }, { coefficient := -1, powers := [(8, 1), (9, 1), (20, 1), (36, 1), (42, 1), (54, 1)] }, { coefficient := -1, powers := [(8, 1), (9, 1), (33, 1), (34, 1), (37, 1), (48, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1), (33, 1), (37, 1), (43, 1), (48, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (34, 1), (37, 1), (48, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1), (49, 1)] }, { coefficient := 1, powers := [(20, 1), (43, 1), (49, 1)] }, { coefficient := 1, powers := [(20, 1), (49, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (37, 1), (42, 1), (56, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (37, 1), (48, 1), (53, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (9, 1), (20, 1), (34, 1), (42, 1), (55, 1), (56, 1)] }, { coefficient := 1, powers := [(3, 1), (31, 1), (39, 1), (54, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (31, 1), (42, 1), (54, 1), (56, 1)] }, { coefficient := 1, powers := [(3, 1), (31, 1), (48, 1), (53, 1), (54, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1), (42, 1), (56, 1), (57, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1), (48, 1), (53, 1), (57, 1)] }, { coefficient := 1, powers := [(6, 1), (31, 1), (37, 1), (43, 1), (48, 1), (53, 1), (58, 1)] }, { coefficient := 1, powers := [(9, 1), (20, 1), (39, 1), (54, 1), (59, 1)] }, { coefficient := 1, powers := [(9, 1), (20, 1), (42, 1), (54, 1), (56, 1)] }, { coefficient := 1, powers := [(9, 1), (20, 1), (48, 1), (53, 1), (54, 1)] }, { coefficient := 1, powers := [(9, 1), (34, 1), (37, 1), (39, 1), (59, 1)] }, { coefficient := 1, powers := [(9, 1), (34, 1), (37, 1), (42, 1), (56, 1)] }, { coefficient := 1, powers := [(9, 1), (34, 1), (37, 1), (48, 1), (53, 1)] }, { coefficient := -1, powers := [(31, 1), (37, 1), (39, 1), (43, 1), (59, 1)] }, { coefficient := -1, powers := [(31, 1), (37, 1), (42, 1), (43, 1), (56, 1)] }, { coefficient := -1, powers := [(34, 1), (37, 1), (39, 1), (49, 1), (59, 1)] }, { coefficient := -1, powers := [(34, 1), (37, 1), (42, 1), (49, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (3, 1), (5, 1), (33, 1), (34, 1), (55, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (15, 1), (27, 1), (43, 1), (61, 1)] }, { coefficient := 1, powers := [(0, 1), (18, 1), (26, 1), (36, 1), (37, 1), (42, 1), (44, 1)] }, { coefficient := 1, powers := [(0, 1), (54, 1)] }, { coefficient := -1, powers := [(3, 1), (5, 1), (33, 1), (34, 1), (56, 1)] }, { coefficient := 1, powers := [(3, 1), (12, 1), (20, 1), (29, 1), (34, 1), (47, 1), (56, 1)] }, { coefficient := -1, powers := [(5, 1), (30, 1), (34, 1), (37, 1), (59, 1)] }, { coefficient := -1, powers := [(6, 1), (8, 1), (34, 1), (36, 1), (42, 1)] }, { coefficient := 1, powers := [(6, 1), (18, 1), (20, 1), (26, 1), (36, 1), (42, 1), (44, 1)] }, { coefficient := 1, powers := [(6, 1), (34, 1)] }, { coefficient := 1, powers := [(13, 1), (25, 1)] }, { coefficient := 1, powers := [(15, 1), (20, 1), (27, 1), (43, 1), (61, 1)] }, { coefficient := 1, powers := [(15, 1), (20, 1), (27, 1), (54, 1), (61, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (26, 1), (37, 1), (43, 1), (59, 1)] }, { coefficient := 1, powers := [(18, 1), (26, 1), (36, 1), (37, 1), (42, 1), (43, 1)] }, { coefficient := -1, powers := [(25, 1), (43, 1)] }],
  [{ coefficient := -1, powers := [(0, 2), (5, 1), (33, 1), (37, 1), (56, 1), (57, 1)] }, { coefficient := -1, powers := [(0, 1), (3, 1), (5, 1), (31, 1), (33, 1), (54, 1), (56, 1)] }, { coefficient := -1, powers := [(0, 1), (3, 1), (5, 1), (31, 1), (36, 1), (53, 1), (54, 1)] }, { coefficient := -1, powers := [(0, 1), (5, 1), (6, 1), (20, 1), (33, 1), (56, 1), (57, 1)] }, { coefficient := -1, powers := [(0, 1), (5, 1), (9, 1), (20, 1), (33, 1), (54, 1), (56, 1)] }, { coefficient := -1, powers := [(0, 1), (5, 1), (9, 1), (20, 1), (36, 1), (53, 1), (54, 1)] }, { coefficient := -1, powers := [(0, 1), (5, 1), (9, 1), (33, 1), (34, 1), (37, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (5, 1), (31, 1), (33, 1), (37, 1), (43, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (5, 1), (33, 1), (34, 1), (37, 1), (49, 1), (56, 1)] }, { coefficient := -1, powers := [(3, 1), (5, 1), (6, 1), (31, 1), (34, 1), (36, 1), (53, 1)] }, { coefficient := -1, powers := [(3, 1), (5, 1), (13, 1), (25, 1), (31, 1), (36, 1), (53, 1)] }, { coefficient := -1, powers := [(5, 1), (6, 1), (9, 1), (20, 1), (34, 1), (36, 1), (53, 1)] }, { coefficient := -1, powers := [(5, 1), (9, 1), (13, 1), (20, 1), (25, 1), (36, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (5, 1), (25, 1), (26, 1), (33, 1), (37, 1), (46, 1), (57, 1), (60, 1)] }, { coefficient := -1, powers := [(0, 1), (5, 1), (25, 1), (33, 1), (37, 1), (46, 1), (52, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (8, 1), (25, 1), (33, 1), (37, 1), (48, 1), (57, 1), (60, 1)] }, { coefficient := -1, powers := [(3, 1), (5, 1), (25, 1), (26, 1), (31, 1), (33, 1), (46, 1), (54, 1), (60, 1)] }, { coefficient := -1, powers := [(3, 1), (5, 1), (25, 1), (31, 1), (33, 1), (46, 1), (52, 1), (54, 1)] }, { coefficient := 1, powers := [(3, 1), (5, 1), (25, 1), (31, 1), (36, 1), (44, 1), (53, 1)] }, { coefficient := -1, powers := [(3, 1), (8, 1), (25, 1), (31, 1), (33, 1), (34, 1), (37, 1), (48, 1), (60, 2)] }, { coefficient := 1, powers := [(3, 1), (8, 1), (25, 1), (31, 1), (33, 1), (48, 1), (54, 1), (60, 1)] }, { coefficient := -1, powers := [(3, 1), (25, 1), (57, 1)] }, { coefficient := -1, powers := [(5, 1), (6, 1), (20, 1), (25, 1), (26, 1), (33, 1), (46, 1), (57, 1), (60, 1)] }, { coefficient := -1, powers := [(5, 1), (6, 1), (20, 1), (25, 1), (33, 1), (46, 1), (52, 1), (57, 1)] }, { coefficient := -1, powers := [(5, 1), (6, 1), (31, 1), (36, 1), (37, 1), (43, 1), (53, 1), (58, 1)] }, { coefficient := -1, powers := [(5, 1), (9, 1), (20, 1), (25, 1), (26, 1), (33, 1), (46, 1), (54, 1), (60, 1)] }, { coefficient := -1, powers := [(5, 1), (9, 1), (20, 1), (25, 1), (33, 1), (46, 1), (52, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (9, 1), (20, 1), (25, 1), (36, 1), (44, 1), (53, 1)] }, { coefficient := -1, powers := [(5, 1), (9, 1), (25, 1), (26, 1), (33, 1), (34, 1), (37, 1), (46, 1), (60, 1)] }, { coefficient := -1, powers := [(5, 1), (9, 1), (25, 1), (33, 1), (34, 1), (37, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(5, 1), (25, 1), (26, 1), (31, 1), (33, 1), (37, 1), (43, 1), (46, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (25, 1), (26, 1), (33, 1), (34, 1), (37, 1), (46, 1), (49, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (25, 1), (31, 1), (33, 1), (37, 2), (43, 1), (48, 1), (53, 1), (58, 1), (60, 1), (62, 1)] }, { coefficient := 1, powers := [(5, 1), (25, 1), (31, 1), (33, 1), (37, 1), (43, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(5, 1), (25, 1), (33, 1), (34, 1), (37, 1), (46, 1), (49, 1), (52, 1)] }, { coefficient := 1, powers := [(6, 1), (8, 1), (20, 1), (25, 1), (33, 1), (48, 1), (57, 1), (60, 1)] }, { coefficient := -1, powers := [(8, 1), (9, 1), (20, 1), (25, 1), (33, 1), (34, 1), (37, 1), (48, 1), (60, 2)] }, { coefficient := 1, powers := [(8, 1), (9, 1), (20, 1), (25, 1), (33, 1), (48, 1), (54, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (9, 1), (25, 1), (33, 1), (34, 1), (37, 1), (48, 1), (60, 1)] }, { coefficient := -1, powers := [(8, 1), (25, 1), (31, 1), (33, 1), (37, 1), (43, 1), (48, 1), (60, 1)] }, { coefficient := -1, powers := [(8, 1), (25, 1), (33, 1), (34, 1), (37, 1), (48, 1), (49, 1), (60, 1)] }, { coefficient := -1, powers := [(13, 1), (31, 1), (37, 1)] }, { coefficient := 1, powers := [(25, 1), (43, 1), (49, 1)] }]
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
    ¬ ∀ index : Fin 46,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component48.SelectedLeafB6_1.selectedHasNoCommonZero

end Krenn.Component48.SelectedLeafB6_1
