import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component37.SelectedLeafB7_3_7

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "ddf052f92e6c9a7fa8c7aa9a6733b30782e44a1f2d2ccca15feb4803f8f3808f"
def certificateSHA256 : String := "747c5f946c7425ab2f26d9b75eb99d49a3602004648711b365ed4bb78214ef0e"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 44 → Fin 667 := ![
  0,
  1,
  2,
  3,
  4,
  6,
  13,
  29,
  149,
  171,
  175,
  181,
  221,
  257,
  269,
  287,
  294,
  296,
  309,
  310,
  311,
  411,
  450,
  454,
  484,
  485,
  515,
  562,
  566,
  567,
  570,
  602,
  603,
  649,
  650,
  655,
  657,
  658,
  659,
  661,
  662,
  664,
  665,
  666
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 44 → SparsePoly (Fin 70) := ![
  [{ coefficient := 1, powers := [(1, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (21, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (26, 1)] }, { coefficient := 1, powers := [(26, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (20, 1)] }, { coefficient := 1, powers := [(18, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (54, 1)] }, { coefficient := 1, powers := [(30, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (26, 1), (47, 1)] }, { coefficient := 1, powers := [(9, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (25, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (24, 1), (52, 1)] }, { coefficient := 1, powers := [(21, 1), (29, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (21, 1), (45, 1), (51, 1)] }, { coefficient := 1, powers := [(1, 1), (42, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1)] }, { coefficient := 1, powers := [(20, 1), (44, 1)] }, { coefficient := 1, powers := [(25, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (51, 1)] }, { coefficient := 1, powers := [(20, 1), (51, 1)] }, { coefficient := 1, powers := [(25, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (24, 1)] }, { coefficient := 1, powers := [(21, 1), (28, 1), (45, 1)] }, { coefficient := 1, powers := [(24, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (41, 1)] }, { coefficient := 1, powers := [(19, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (52, 1)] }, { coefficient := 1, powers := [(24, 1), (57, 1)] }, { coefficient := 1, powers := [(29, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (25, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (25, 1), (41, 1)] }, { coefficient := 1, powers := [(19, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (61, 1)] }, { coefficient := 1, powers := [(12, 1), (26, 1), (47, 1)] }, { coefficient := 1, powers := [(12, 1), (58, 1)] }, { coefficient := 1, powers := [(19, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (55, 1)] }, { coefficient := 1, powers := [(30, 1), (42, 1)] }, { coefficient := 1, powers := [(30, 1), (48, 1), (51, 1)] }, { coefficient := 1, powers := [(33, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (37, 1), (60, 1)] }, { coefficient := 1, powers := [(1, 1)] }, { coefficient := 1, powers := [(10, 1), (35, 1), (37, 1)] }, { coefficient := 1, powers := [(15, 1), (32, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (39, 1), (60, 1)] }, { coefficient := 1, powers := [(1, 1), (48, 1), (54, 1)] }, { coefficient := 1, powers := [(10, 1), (35, 1), (39, 1)] }, { coefficient := 1, powers := [(15, 1), (32, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (25, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (50, 1)] }, { coefficient := 1, powers := [(17, 1), (21, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (26, 1), (47, 1)] }, { coefficient := 1, powers := [(18, 1), (58, 1)] }, { coefficient := 1, powers := [(19, 1), (26, 1), (41, 1)] }, { coefficient := 1, powers := [(19, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (44, 1), (54, 1)] }, { coefficient := 1, powers := [(24, 1), (58, 1)] }, { coefficient := 1, powers := [(30, 1), (49, 1)] }, { coefficient := 1, powers := [(36, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (51, 1), (57, 1)] }, { coefficient := 1, powers := [(24, 1), (53, 1)] }, { coefficient := 1, powers := [(29, 1), (42, 1)] }, { coefficient := 1, powers := [(29, 1), (48, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (44, 1), (54, 1)] }, { coefficient := 1, powers := [(29, 1), (58, 1)] }, { coefficient := 1, powers := [(30, 1), (41, 1), (44, 1)] }, { coefficient := 1, powers := [(30, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1)] }, { coefficient := 1, powers := [(3, 1), (34, 1)] }, { coefficient := 1, powers := [(13, 1), (20, 1)] }, { coefficient := 1, powers := [(20, 1), (56, 1)] }, { coefficient := 1, powers := [(25, 1), (43, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (50, 1)] }, { coefficient := 1, powers := [(6, 1), (31, 1)] }, { coefficient := 1, powers := [(9, 1), (25, 1)] }, { coefficient := 1, powers := [(20, 1), (50, 1)] }, { coefficient := 1, powers := [(25, 1), (40, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (41, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (47, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (36, 1), (41, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (58, 1)] }, { coefficient := 1, powers := [(18, 1), (30, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (29, 1), (54, 1)] }, { coefficient := 1, powers := [(19, 1), (30, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (42, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (48, 1), (53, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1), (29, 1), (48, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (53, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (37, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (40, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (43, 1), (50, 1)] }, { coefficient := 1, powers := [(3, 1), (25, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (31, 1), (56, 1)] }, { coefficient := 1, powers := [(3, 1), (34, 1), (50, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (31, 1), (43, 1)] }, { coefficient := 1, powers := [(6, 1), (34, 1), (40, 1)] }, { coefficient := 1, powers := [(9, 1), (20, 1), (56, 1)] }, { coefficient := 1, powers := [(9, 1), (25, 1), (43, 1)] }, { coefficient := 1, powers := [(9, 1), (34, 1), (37, 1)] }, { coefficient := 1, powers := [(13, 1), (20, 1), (50, 1)] }, { coefficient := 1, powers := [(13, 1), (25, 1), (40, 1)] }, { coefficient := 1, powers := [(13, 1), (31, 1), (37, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (39, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (42, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (49, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (49, 1)] }, { coefficient := 1, powers := [(8, 1), (36, 1), (42, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (58, 1)] }, { coefficient := 1, powers := [(12, 1), (30, 1), (49, 1)] }, { coefficient := 1, powers := [(12, 1), (36, 1), (39, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (55, 1)] }, { coefficient := 1, powers := [(19, 1), (30, 1), (42, 1)] }, { coefficient := 1, powers := [(19, 1), (33, 1), (39, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(40, 1)] }],
  [{ coefficient := 1, powers := [(41, 1), (65, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(56, 1), (67, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(57, 1), (68, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(58, 1), (69, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 44 → SparsePoly (Fin 70) := ![
  [{ coefficient := -1, powers := [(2, 1), (53, 1), (58, 1), (63, 1), (68, 1)] }, { coefficient := -2, powers := [(12, 1), (13, 1), (29, 1), (58, 1), (63, 1), (67, 1), (68, 1)] }, { coefficient := -1, powers := [(12, 1), (29, 1), (58, 1), (63, 1), (68, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (51, 1), (58, 1), (63, 1), (68, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (33, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (5, 1), (30, 1), (43, 1), (61, 1), (63, 1)] }, { coefficient := -1, powers := [(3, 1), (5, 1), (30, 1), (34, 1), (61, 1), (63, 1)] }, { coefficient := -1, powers := [(5, 1), (13, 1), (30, 1), (34, 1), (37, 1), (61, 1), (63, 1), (67, 1)] }, { coefficient := -1, powers := [(5, 1), (20, 1), (30, 1), (43, 1), (61, 1), (63, 1)] }, { coefficient := -1, powers := [(5, 1), (20, 1), (30, 1), (56, 1), (61, 1), (63, 1)] }, { coefficient := -1, powers := [(5, 1), (25, 1), (30, 1), (43, 1), (61, 1), (63, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (34, 1), (37, 1), (43, 1), (61, 1), (63, 1), (67, 1)] }, { coefficient := -1, powers := [(5, 1), (30, 1), (34, 1), (37, 1), (61, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (37, 1), (48, 1), (61, 1), (63, 1)] }, { coefficient := -1, powers := [(2, 1), (42, 1), (47, 1), (63, 1), (65, 1)] }, { coefficient := -1, powers := [(12, 1), (24, 1), (44, 1), (63, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (42, 1), (44, 1), (63, 1), (65, 1)] }, { coefficient := 2, powers := [(19, 1), (24, 1), (51, 1), (63, 1)] }, { coefficient := -1, powers := [(19, 1), (29, 1), (42, 1), (63, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (49, 1), (63, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1), (63, 1)] }, { coefficient := -1, powers := [(19, 1), (24, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (30, 1), (37, 1), (61, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1), (30, 1), (61, 1)] }, { coefficient := -1, powers := [(13, 1), (25, 1), (30, 1), (37, 1), (61, 1), (67, 1)] }, { coefficient := 1, powers := [(25, 1), (30, 1), (37, 1), (43, 1), (61, 1), (67, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (21, 1), (30, 1), (61, 1)] }, { coefficient := -1, powers := [(13, 1), (21, 1), (30, 1), (37, 1), (61, 1), (67, 1)] }, { coefficient := 1, powers := [(21, 1), (30, 1), (37, 1), (43, 1), (61, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (51, 1), (58, 1), (63, 1), (67, 1)] }, { coefficient := 2, powers := [(12, 1), (28, 1), (58, 1), (63, 1), (67, 1)] }, { coefficient := 2, powers := [(12, 1), (29, 1), (58, 1), (63, 1), (67, 1), (68, 1)] }, { coefficient := 1, powers := [(19, 1), (30, 1), (51, 1), (63, 1), (67, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (20, 1), (30, 1), (47, 1), (56, 1), (61, 1), (69, 1)] }, { coefficient := -1, powers := [(5, 1), (30, 1), (34, 1), (37, 1), (47, 1), (61, 1), (69, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (25, 1), (26, 1), (52, 1)] }, { coefficient := -1, powers := [(24, 1), (26, 1)] }],
  [{ coefficient := -2, powers := [(24, 1), (51, 1), (58, 1), (62, 1)] }, { coefficient := -1, powers := [(30, 1), (42, 1), (44, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(19, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (20, 1), (30, 1), (56, 1), (61, 1), (69, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (34, 1), (37, 1), (61, 1), (69, 1)] }],
  [{ coefficient := -1, powers := [(24, 1), (26, 1), (52, 1)] }],
  [{ coefficient := -2, powers := [(12, 1), (58, 1), (67, 1), (68, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (58, 1), (63, 1), (67, 1)] }, { coefficient := -1, powers := [(19, 1), (30, 1), (63, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (30, 1), (42, 1), (62, 1)] }],
  [{ coefficient := 2, powers := [(18, 1), (24, 1), (58, 1), (62, 1)] }],
  [{ coefficient := -2, powers := [(12, 1), (58, 1), (67, 1)] }],
  [{ coefficient := -1, powers := [(24, 1), (25, 1), (26, 1), (53, 1)] }, { coefficient := 1, powers := [(24, 1), (26, 1), (51, 1)] }],
  [{ coefficient := 2, powers := [(12, 1), (13, 1), (58, 1), (67, 1), (68, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (26, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(24, 1)] }],
  [{ coefficient := 1, powers := [(19, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (39, 1), (61, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (37, 1), (61, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (30, 1), (61, 1)] }, { coefficient := 1, powers := [(13, 1), (30, 1), (37, 1), (61, 1), (67, 1)] }, { coefficient := -1, powers := [(30, 1), (37, 1), (43, 1), (61, 1), (67, 1)] }],
  [{ coefficient := -1, powers := [(24, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(12, 1)] }],
  [{ coefficient := -1, powers := [(18, 1), (58, 1), (68, 1)] }],
  [{ coefficient := -1, powers := [(18, 1), (42, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (30, 1), (50, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (30, 1), (43, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(42, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(58, 1), (68, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (30, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -2, powers := [(18, 1), (24, 1), (51, 1), (58, 1)] }, { coefficient := -1, powers := [(18, 1), (30, 1), (42, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (5, 1), (30, 1), (43, 1), (50, 1), (61, 1)] }, { coefficient := -1, powers := [(2, 1), (39, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (42, 1), (47, 1), (54, 1), (65, 1)] }, { coefficient := 1, powers := [(2, 1), (42, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (48, 1), (53, 1), (58, 1), (68, 1)] }, { coefficient := -1, powers := [(2, 1), (49, 1), (55, 1)] }, { coefficient := 1, powers := [(3, 1), (5, 1), (30, 1), (34, 1), (50, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (13, 1), (30, 1), (34, 1), (37, 1), (50, 1), (61, 1), (67, 1)] }, { coefficient := 1, powers := [(5, 1), (20, 1), (30, 1), (43, 1), (50, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (20, 1), (30, 1), (50, 1), (56, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (25, 1), (30, 1), (43, 1), (50, 1), (61, 1)] }, { coefficient := -1, powers := [(5, 1), (30, 1), (34, 1), (37, 1), (43, 1), (50, 1), (61, 1), (67, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (34, 1), (37, 1), (50, 1), (61, 1)] }, { coefficient := -1, powers := [(5, 1), (36, 1), (55, 1)] }, { coefficient := -1, powers := [(8, 1), (33, 1), (49, 1)] }, { coefficient := 2, powers := [(12, 1), (13, 1), (29, 1), (48, 1), (58, 1), (67, 1), (68, 1)] }, { coefficient := -2, powers := [(12, 1), (21, 1), (28, 1), (45, 1), (58, 1), (67, 1)] }, { coefficient := -2, powers := [(12, 1), (21, 1), (29, 1), (45, 1), (58, 1), (67, 1), (68, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (44, 1), (54, 1)] }, { coefficient := 1, powers := [(12, 1), (29, 1), (48, 1), (58, 1), (68, 1)] }, { coefficient := -1, powers := [(18, 1), (29, 1), (42, 1), (44, 1), (54, 1), (65, 1)] }, { coefficient := -1, powers := [(18, 1), (29, 1), (48, 1), (51, 1), (58, 1), (68, 1)] }, { coefficient := -2, powers := [(19, 1), (24, 1), (51, 1), (54, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (55, 1)] }, { coefficient := 1, powers := [(19, 1), (29, 1), (42, 1), (54, 1), (65, 1)] }, { coefficient := 1, powers := [(19, 1), (30, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (5, 1), (30, 1), (56, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (6, 1), (30, 1), (34, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (13, 1), (25, 1), (30, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (20, 1), (26, 1), (30, 1), (47, 1), (56, 1), (61, 1), (69, 1)] }, { coefficient := -1, powers := [(5, 1), (25, 1), (30, 1), (43, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (26, 1), (30, 1), (34, 1), (37, 1), (47, 1), (61, 1), (69, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (42, 1), (58, 1)] }, { coefficient := -1, powers := [(8, 1), (36, 1), (42, 1)] }, { coefficient := 1, powers := [(18, 1), (30, 1), (42, 1), (44, 1)] }, { coefficient := -1, powers := [(19, 1), (30, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (2, 1), (42, 1), (58, 1), (63, 1)] }, { coefficient := 1, powers := [(1, 1), (19, 1), (30, 1), (42, 1), (63, 1)] }, { coefficient := -1, powers := [(5, 1), (13, 1), (30, 1), (31, 1), (37, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (31, 1), (37, 1), (43, 1), (61, 1)] }, { coefficient := 2, powers := [(12, 1), (24, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (42, 1), (58, 1)] }, { coefficient := -1, powers := [(5, 1), (33, 1), (58, 1)] }, { coefficient := -2, powers := [(12, 1), (13, 1), (24, 1), (58, 1), (67, 1)] }, { coefficient := -1, powers := [(12, 1), (24, 1), (58, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (51, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (9, 1), (20, 1), (30, 1), (56, 1), (61, 1)] }, { coefficient := -1, powers := [(5, 1), (9, 1), (30, 1), (34, 1), (37, 1), (61, 1)] }]
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
    (values : Fin 70 → R) :
    ¬ ∀ index : Fin 44,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component37.SelectedLeafB7_3_7.selectedHasNoCommonZero

end Krenn.Component37.SelectedLeafB7_3_7
