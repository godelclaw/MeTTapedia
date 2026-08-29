import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component37.SelectedLeafB4_1_2_0

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "89b267d34c450fa6d7c3405e36fe7b13ca8b517ffeade0a7ad18c09bf9f41dc9"
def certificateSHA256 : String := "77296e64acfeba23213402a4ddd53c63a2ad3d1be1a80378bfb4c621466aa39f"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 53 → Fin 670 := ![
  5,
  7,
  147,
  171,
  179,
  180,
  181,
  294,
  295,
  298,
  299,
  313,
  317,
  319,
  402,
  410,
  411,
  415,
  421,
  424,
  433,
  438,
  447,
  450,
  454,
  456,
  470,
  474,
  505,
  519,
  523,
  531,
  539,
  566,
  588,
  602,
  603,
  605,
  638,
  655,
  656,
  657,
  659,
  660,
  661,
  662,
  663,
  664,
  665,
  666,
  667,
  668,
  669
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 53 → SparsePoly (Fin 65) := ![
  [{ coefficient := 1, powers := [(5, 1), (35, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (32, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (31, 1)] }, { coefficient := 1, powers := [(15, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (55, 1)] }, { coefficient := 1, powers := [(30, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (44, 1)] }, { coefficient := 1, powers := [(28, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (54, 1)] }, { coefficient := 1, powers := [(30, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1)] }, { coefficient := 1, powers := [(20, 1), (44, 1)] }, { coefficient := 1, powers := [(25, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (49, 1)] }, { coefficient := 1, powers := [(21, 1), (44, 1)] }, { coefficient := 1, powers := [(25, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (46, 1)] }, { coefficient := 1, powers := [(4, 1), (35, 1)] }, { coefficient := 1, powers := [(15, 1), (22, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (52, 1)] }, { coefficient := 1, powers := [(7, 1), (32, 1)] }, { coefficient := 1, powers := [(10, 1), (27, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(20, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(44, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (49, 1), (52, 1)] }, { coefficient := 1, powers := [(21, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(49, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (38, 1), (59, 1)] }, { coefficient := 1, powers := [(4, 1), (27, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (22, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (20, 1), (50, 1)] }, { coefficient := 1, powers := [(14, 1), (25, 1), (40, 1)] }, { coefficient := 1, powers := [(14, 1), (31, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (25, 1), (41, 1)] }, { coefficient := 1, powers := [(18, 1), (25, 1), (46, 1)] }, { coefficient := 1, powers := [(18, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (25, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (25, 1), (41, 1)] }, { coefficient := 1, powers := [(19, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (21, 1), (45, 1), (52, 1)] }, { coefficient := 1, powers := [(13, 1), (21, 1), (52, 1)] }, { coefficient := 1, powers := [(21, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (21, 1), (25, 1), (45, 1)] }, { coefficient := 1, powers := [(10, 1), (21, 1), (56, 1)] }, { coefficient := 1, powers := [(14, 1), (21, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1)] }, { coefficient := 1, powers := [(25, 1), (41, 1), (44, 1)] }, { coefficient := 1, powers := [(25, 1), (47, 1)] }, { coefficient := 1, powers := [(44, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (49, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1)] }, { coefficient := 1, powers := [(18, 1), (28, 1), (49, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1)] }, { coefficient := 1, powers := [(12, 1), (30, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (33, 1)] }, { coefficient := 1, powers := [(23, 1), (51, 1)] }, { coefficient := 1, powers := [(28, 1), (51, 1)] }, { coefficient := 1, powers := [(33, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (61, 1)] }, { coefficient := 1, powers := [(12, 1), (26, 1), (47, 1)] }, { coefficient := 1, powers := [(12, 1), (58, 1)] }, { coefficient := 1, powers := [(19, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (55, 1)] }, { coefficient := 1, powers := [(30, 1), (42, 1)] }, { coefficient := 1, powers := [(30, 1), (48, 1), (51, 1)] }, { coefficient := 1, powers := [(33, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (21, 1), (45, 1)] }, { coefficient := 1, powers := [(13, 1), (21, 1)] }, { coefficient := 1, powers := [(21, 1), (25, 1), (45, 1)] }, { coefficient := 1, powers := [(21, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1), (50, 1)] }, { coefficient := 1, powers := [(6, 1), (31, 1), (46, 1)] }, { coefficient := 1, powers := [(9, 1), (25, 1), (46, 1)] }, { coefficient := 1, powers := [(50, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1), (51, 1)] }, { coefficient := 1, powers := [(6, 1), (61, 1)] }, { coefficient := 1, powers := [(25, 1), (47, 1), (51, 1)] }, { coefficient := 1, powers := [(44, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (25, 1), (60, 1)] }, { coefficient := 1, powers := [(10, 1), (25, 1), (46, 1)] }, { coefficient := 1, powers := [(15, 1), (25, 1), (41, 1)] }, { coefficient := 1, powers := [(15, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (27, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (52, 1)] }, { coefficient := 1, powers := [(18, 1), (27, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (22, 1), (60, 1)] }, { coefficient := 1, powers := [(6, 1), (32, 1), (46, 1)] }, { coefficient := 1, powers := [(6, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(22, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (20, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (31, 1), (43, 1)] }, { coefficient := 1, powers := [(7, 1), (34, 1), (40, 1)] }, { coefficient := 1, powers := [(14, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (34, 1), (42, 1)] }, { coefficient := 1, powers := [(11, 1), (21, 1), (45, 1)] }, { coefficient := 1, powers := [(14, 1), (21, 1), (53, 1)] }, { coefficient := 1, powers := [(14, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (44, 1), (54, 1)] }, { coefficient := 1, powers := [(24, 1), (58, 1)] }, { coefficient := 1, powers := [(30, 1), (49, 1)] }, { coefficient := 1, powers := [(36, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (41, 1), (56, 1)] }, { coefficient := 1, powers := [(1, 1), (45, 1)] }, { coefficient := 1, powers := [(4, 1), (32, 1), (56, 1)] }, { coefficient := 1, powers := [(10, 1), (22, 1), (56, 1)] }, { coefficient := 1, powers := [(14, 1), (22, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1)] }, { coefficient := 1, powers := [(3, 1), (34, 1)] }, { coefficient := 1, powers := [(13, 1), (20, 1)] }, { coefficient := 1, powers := [(20, 1), (56, 1)] }, { coefficient := 1, powers := [(25, 1), (43, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (50, 1)] }, { coefficient := 1, powers := [(6, 1), (31, 1)] }, { coefficient := 1, powers := [(9, 1), (25, 1)] }, { coefficient := 1, powers := [(20, 1), (50, 1)] }, { coefficient := 1, powers := [(25, 1), (40, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (52, 1)] }, { coefficient := 1, powers := [(22, 1), (57, 1)] }, { coefficient := 1, powers := [(27, 1), (41, 1)] }, { coefficient := 1, powers := [(27, 1), (46, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1)] }, { coefficient := 1, powers := [(35, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (24, 1), (61, 1)] }, { coefficient := 1, powers := [(6, 1), (33, 1), (49, 1)] }, { coefficient := 1, powers := [(6, 1), (36, 1), (42, 1)] }, { coefficient := 1, powers := [(24, 1), (44, 1), (51, 1)] }, { coefficient := 1, powers := [(28, 1), (42, 1), (44, 1)] }, { coefficient := 1, powers := [(28, 1), (49, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (37, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (40, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (43, 1), (50, 1)] }, { coefficient := 1, powers := [(3, 1), (25, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (31, 1), (56, 1)] }, { coefficient := 1, powers := [(3, 1), (34, 1), (50, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (31, 1), (43, 1)] }, { coefficient := 1, powers := [(6, 1), (34, 1), (40, 1)] }, { coefficient := 1, powers := [(9, 1), (20, 1), (56, 1)] }, { coefficient := 1, powers := [(9, 1), (25, 1), (43, 1)] }, { coefficient := 1, powers := [(9, 1), (34, 1), (37, 1)] }, { coefficient := 1, powers := [(13, 1), (20, 1), (50, 1)] }, { coefficient := 1, powers := [(13, 1), (25, 1), (40, 1)] }, { coefficient := 1, powers := [(13, 1), (31, 1), (37, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1), (38, 1), (60, 1)] }, { coefficient := 1, powers := [(1, 1), (41, 1), (57, 1)] }, { coefficient := 1, powers := [(1, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(4, 1), (27, 1), (60, 1)] }, { coefficient := 1, powers := [(4, 1), (32, 1), (57, 1)] }, { coefficient := 1, powers := [(4, 1), (35, 1), (52, 1)] }, { coefficient := 1, powers := [(7, 1), (22, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (32, 1), (46, 1)] }, { coefficient := 1, powers := [(7, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(10, 1), (22, 1), (57, 1)] }, { coefficient := 1, powers := [(10, 1), (27, 1), (46, 1)] }, { coefficient := 1, powers := [(10, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(15, 1), (22, 1), (52, 1)] }, { coefficient := 1, powers := [(15, 1), (27, 1), (41, 1)] }, { coefficient := 1, powers := [(15, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (39, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (42, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (49, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (49, 1)] }, { coefficient := 1, powers := [(8, 1), (36, 1), (42, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (58, 1)] }, { coefficient := 1, powers := [(12, 1), (30, 1), (49, 1)] }, { coefficient := 1, powers := [(12, 1), (36, 1), (39, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (55, 1)] }, { coefficient := 1, powers := [(19, 1), (30, 1), (42, 1)] }, { coefficient := 1, powers := [(19, 1), (33, 1), (39, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1)] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(40, 1)] }],
  [{ coefficient := 1, powers := [(41, 1)] }],
  [{ coefficient := 1, powers := [(42, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(56, 1)] }],
  [{ coefficient := 1, powers := [(57, 1), (64, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(58, 1)] }],
  [{ coefficient := 1, powers := [(25, 1)] }],
  [{ coefficient := 1, powers := [(27, 1)] }],
  [{ coefficient := 1, powers := [(30, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 53 → SparsePoly (Fin 65) := ![
  [{ coefficient := -1, powers := [(4, 1), (36, 1), (52, 1), (55, 1), (57, 1), (64, 1)] }, { coefficient := -1, powers := [(6, 1), (10, 1), (36, 1), (46, 1), (52, 2), (55, 1), (64, 1)] }, { coefficient := 1, powers := [(10, 1), (36, 1), (38, 1), (52, 1), (55, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (36, 1), (42, 1), (57, 1)] }, { coefficient := 1, powers := [(6, 1), (10, 1), (36, 1), (42, 1), (46, 1), (52, 1)] }, { coefficient := -1, powers := [(10, 1), (36, 1), (38, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (22, 1), (37, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (24, 1), (26, 1), (32, 1), (57, 1)] }, { coefficient := -1, powers := [(6, 1), (10, 1), (22, 1), (24, 1), (26, 1), (52, 1), (60, 1)] }, { coefficient := -1, powers := [(6, 1), (10, 1), (24, 1), (26, 1), (32, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(10, 1), (24, 1), (26, 1), (32, 1), (38, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (18, 1), (32, 1), (49, 1), (57, 1)] }, { coefficient := -1, powers := [(6, 1), (10, 1), (18, 1), (22, 1), (49, 1), (52, 1), (60, 1)] }, { coefficient := -1, powers := [(6, 1), (10, 1), (18, 1), (32, 1), (46, 1), (49, 1), (52, 1)] }, { coefficient := 1, powers := [(10, 1), (18, 1), (32, 1), (38, 1), (49, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (10, 1), (18, 1), (22, 1), (52, 1), (55, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (12, 1), (32, 1), (44, 1), (57, 1)] }, { coefficient := -1, powers := [(6, 1), (10, 1), (12, 1), (22, 1), (44, 1), (52, 1), (60, 1)] }, { coefficient := -1, powers := [(6, 1), (10, 1), (12, 1), (32, 1), (44, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(10, 1), (12, 1), (32, 1), (38, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (10, 1), (22, 1), (24, 1), (51, 1), (52, 2), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (10, 1), (22, 1), (28, 1), (42, 1), (52, 2), (60, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (10, 1), (22, 1), (23, 1), (51, 1), (52, 2), (60, 1)] }, { coefficient := -1, powers := [(8, 1), (10, 1), (22, 1), (33, 1), (37, 1), (52, 2), (60, 1)] }],
  [{ coefficient := 1, powers := [(52, 1)] }],
  [{ coefficient := 1, powers := [(46, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (10, 1), (22, 1), (24, 1), (51, 1), (52, 1), (60, 1)] }, { coefficient := -1, powers := [(8, 1), (10, 1), (22, 1), (28, 1), (42, 1), (52, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (10, 1), (22, 1), (23, 1), (51, 1), (52, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (10, 1), (22, 1), (33, 1), (37, 1), (52, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (37, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (37, 1), (46, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (10, 1), (22, 1), (24, 1), (44, 1), (52, 1), (55, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (24, 1), (26, 1), (32, 1), (53, 1), (57, 1)] }, { coefficient := -1, powers := [(4, 1), (24, 1), (32, 1), (55, 1), (57, 1)] }, { coefficient := 1, powers := [(6, 1), (10, 1), (22, 1), (24, 1), (26, 1), (52, 1), (53, 1), (60, 1)] }, { coefficient := -2, powers := [(6, 1), (10, 1), (22, 1), (24, 1), (52, 1), (55, 1), (60, 1)] }, { coefficient := 1, powers := [(6, 1), (10, 1), (24, 1), (26, 1), (32, 1), (46, 1), (52, 1), (53, 1)] }, { coefficient := -1, powers := [(6, 1), (10, 1), (24, 1), (32, 1), (46, 1), (52, 1), (55, 1)] }, { coefficient := -1, powers := [(10, 1), (24, 1), (26, 1), (32, 1), (38, 1), (53, 1)] }, { coefficient := 1, powers := [(10, 1), (24, 1), (32, 1), (38, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(9, 1), (11, 1), (22, 1), (37, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(11, 1), (22, 1), (37, 1), (50, 1), (60, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(9, 1), (22, 1), (37, 1), (53, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(22, 1), (37, 1), (50, 1), (53, 1), (60, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (10, 1), (22, 1), (24, 1), (51, 1), (52, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (10, 1), (22, 1), (52, 1), (55, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (32, 1), (49, 1), (57, 1)] }, { coefficient := 1, powers := [(6, 1), (10, 1), (22, 1), (49, 1), (52, 1), (60, 1)] }, { coefficient := 1, powers := [(6, 1), (10, 1), (32, 1), (46, 1), (49, 1), (52, 1)] }, { coefficient := -1, powers := [(10, 1), (32, 1), (38, 1), (49, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (10, 1), (22, 1), (49, 1), (52, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (24, 1), (32, 1), (57, 1)] }, { coefficient := 1, powers := [(6, 1), (10, 1), (22, 1), (24, 1), (52, 1), (60, 1)] }, { coefficient := 1, powers := [(6, 1), (10, 1), (24, 1), (32, 1), (46, 1), (52, 1)] }, { coefficient := -1, powers := [(10, 1), (24, 1), (32, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (19, 1), (32, 1), (57, 1)] }, { coefficient := 1, powers := [(6, 1), (10, 1), (19, 1), (22, 1), (52, 1), (60, 1)] }, { coefficient := 1, powers := [(6, 1), (10, 1), (19, 1), (32, 1), (46, 1), (52, 1)] }, { coefficient := -1, powers := [(10, 1), (19, 1), (32, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (11, 1), (22, 1), (37, 1), (52, 1), (60, 1), (63, 1)] }, { coefficient := -1, powers := [(11, 1), (22, 1), (37, 1), (50, 1), (52, 1), (60, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (22, 1), (37, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (10, 1), (22, 1), (24, 1), (52, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(32, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (36, 1), (55, 1), (57, 1), (64, 1)] }, { coefficient := 1, powers := [(6, 1), (10, 1), (36, 1), (46, 1), (52, 1), (55, 1), (64, 1)] }, { coefficient := -1, powers := [(10, 1), (36, 1), (38, 1), (55, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(10, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (22, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (22, 1), (37, 1), (60, 1), (63, 1)] }, { coefficient := -1, powers := [(22, 1), (37, 1), (50, 1), (60, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (12, 1), (32, 1), (57, 1)] }, { coefficient := 1, powers := [(6, 1), (10, 1), (12, 1), (22, 1), (52, 1), (60, 1)] }, { coefficient := 1, powers := [(6, 1), (10, 1), (12, 1), (32, 1), (46, 1), (52, 1)] }, { coefficient := -1, powers := [(10, 1), (12, 1), (32, 1), (38, 1)] }],
  [{ coefficient := -1, powers := [(9, 1), (37, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (22, 1), (50, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(14, 1), (22, 1), (37, 1), (46, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(10, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (10, 1), (22, 1), (52, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (22, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(4, 1), (32, 1), (57, 1)] }, { coefficient := -1, powers := [(6, 1), (10, 1), (22, 1), (52, 1), (60, 1)] }, { coefficient := -1, powers := [(6, 1), (10, 1), (32, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(10, 1), (32, 1), (38, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (37, 1), (38, 1), (59, 1), (60, 1)] }, { coefficient := 1, powers := [(9, 1), (37, 1), (45, 1), (60, 1)] }, { coefficient := 1, powers := [(38, 1), (60, 1)] }, { coefficient := -1, powers := [(46, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (32, 1), (39, 1), (57, 1), (61, 1)] }, { coefficient := 1, powers := [(4, 1), (32, 1), (42, 1), (57, 1), (58, 1)] }, { coefficient := 1, powers := [(6, 1), (10, 1), (22, 1), (39, 1), (52, 1), (60, 1), (61, 1)] }, { coefficient := 1, powers := [(6, 1), (10, 1), (22, 1), (42, 1), (52, 1), (58, 1), (60, 1)] }, { coefficient := -1, powers := [(6, 1), (10, 1), (22, 1), (49, 1), (52, 1), (55, 1), (60, 1)] }, { coefficient := 1, powers := [(6, 1), (10, 1), (32, 1), (39, 1), (46, 1), (52, 1), (61, 1)] }, { coefficient := 1, powers := [(6, 1), (10, 1), (32, 1), (42, 1), (46, 1), (52, 1), (58, 1)] }, { coefficient := -1, powers := [(10, 1), (32, 1), (38, 1), (39, 1), (61, 1)] }, { coefficient := -1, powers := [(10, 1), (32, 1), (38, 1), (42, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (7, 1), (22, 1), (56, 1), (60, 1)] }, { coefficient := -1, powers := [(6, 1), (14, 1), (22, 1), (60, 1)] }, { coefficient := -1, powers := [(13, 1), (15, 1), (22, 1), (37, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (9, 1), (37, 1), (56, 1), (60, 1)] }, { coefficient := 1, powers := [(1, 1), (57, 1)] }, { coefficient := 1, powers := [(6, 1), (10, 1), (35, 1), (52, 1)] }, { coefficient := 1, powers := [(7, 1), (35, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (9, 1), (22, 1), (34, 1), (37, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (22, 1), (34, 1), (37, 1), (50, 1), (60, 1)] }, { coefficient := -1, powers := [(9, 1), (14, 1), (22, 1), (37, 1), (60, 1)] }, { coefficient := 1, powers := [(14, 1), (22, 1), (37, 1), (50, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (7, 1), (22, 1), (31, 1), (60, 1)] }, { coefficient := 1, powers := [(4, 1), (9, 1), (32, 1), (37, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (9, 1), (20, 1), (22, 1), (60, 1)] }, { coefficient := -1, powers := [(7, 1), (20, 1), (22, 1), (50, 1), (60, 1)] }, { coefficient := 1, powers := [(9, 1), (10, 1), (21, 1), (22, 1), (37, 1), (53, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(9, 1), (10, 1), (22, 1), (37, 1), (60, 1)] }, { coefficient := -1, powers := [(9, 1), (11, 1), (21, 1), (22, 1), (37, 1), (52, 1), (60, 1), (63, 1)] }, { coefficient := -1, powers := [(10, 1), (21, 1), (22, 1), (37, 1), (50, 1), (53, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(11, 1), (21, 1), (22, 1), (37, 1), (50, 1), (52, 1), (60, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (5, 1), (32, 1), (36, 1), (55, 1), (57, 1)] }, { coefficient := -1, powers := [(5, 1), (6, 1), (10, 1), (32, 1), (36, 1), (46, 1), (52, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (10, 1), (32, 1), (36, 1), (38, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (5, 1), (32, 1), (33, 1), (57, 1)] }, { coefficient := -1, powers := [(4, 1), (12, 1), (24, 1), (32, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (6, 1), (10, 1), (22, 1), (33, 1), (52, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (6, 1), (10, 1), (32, 1), (33, 1), (46, 1), (52, 1)] }, { coefficient := -1, powers := [(5, 1), (10, 1), (32, 1), (33, 1), (38, 1)] }, { coefficient := -1, powers := [(6, 1), (10, 1), (12, 1), (22, 1), (24, 1), (52, 1), (60, 1)] }, { coefficient := -1, powers := [(6, 1), (10, 1), (12, 1), (24, 1), (32, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(10, 1), (12, 1), (24, 1), (32, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (7, 1), (22, 1), (59, 1), (60, 1)] }, { coefficient := -1, powers := [(4, 1), (18, 1), (24, 1), (26, 1), (32, 1), (47, 1), (53, 1), (57, 1)] }, { coefficient := 1, powers := [(4, 1), (18, 1), (24, 1), (32, 1), (47, 1), (55, 1), (57, 1)] }, { coefficient := -1, powers := [(4, 1), (19, 1), (24, 1), (26, 1), (32, 1), (41, 1), (53, 1), (57, 1)] }, { coefficient := 1, powers := [(4, 1), (19, 1), (24, 1), (32, 1), (41, 1), (55, 1), (57, 1)] }, { coefficient := -1, powers := [(4, 1), (32, 1), (38, 1), (60, 1)] }, { coefficient := -1, powers := [(6, 1), (10, 1), (18, 1), (22, 1), (24, 1), (26, 1), (47, 1), (52, 1), (53, 1), (60, 1)] }, { coefficient := -1, powers := [(6, 1), (10, 1), (18, 1), (22, 1), (24, 1), (41, 1), (44, 1), (52, 1), (55, 1), (60, 1)] }, { coefficient := -1, powers := [(6, 1), (10, 1), (18, 1), (22, 1), (24, 1), (44, 1), (46, 1), (52, 1), (55, 1), (60, 1)] }, { coefficient := 2, powers := [(6, 1), (10, 1), (18, 1), (22, 1), (24, 1), (47, 1), (52, 1), (55, 1), (60, 1)] }, { coefficient := -1, powers := [(6, 1), (10, 1), (18, 1), (24, 1), (26, 1), (32, 1), (46, 1), (47, 1), (52, 1), (53, 1)] }, { coefficient := 1, powers := [(6, 1), (10, 1), (18, 1), (24, 1), (32, 1), (46, 1), (47, 1), (52, 1), (55, 1)] }, { coefficient := -1, powers := [(6, 1), (10, 1), (19, 1), (22, 1), (24, 1), (26, 1), (41, 1), (52, 1), (53, 1), (60, 1)] }, { coefficient := 2, powers := [(6, 1), (10, 1), (19, 1), (22, 1), (24, 1), (41, 1), (52, 1), (55, 1), (60, 1)] }, { coefficient := -1, powers := [(6, 1), (10, 1), (19, 1), (24, 1), (26, 1), (32, 1), (41, 1), (46, 1), (52, 1), (53, 1)] }, { coefficient := 1, powers := [(6, 1), (10, 1), (19, 1), (24, 1), (32, 1), (41, 1), (46, 1), (52, 1), (55, 1)] }, { coefficient := 1, powers := [(7, 1), (9, 1), (22, 1), (43, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (13, 1), (22, 1), (40, 1), (60, 1)] }, { coefficient := -1, powers := [(7, 1), (22, 1), (43, 1), (50, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (10, 1), (22, 1), (23, 1), (49, 1), (51, 1), (52, 2), (60, 1)] }, { coefficient := -1, powers := [(8, 1), (10, 1), (22, 1), (24, 1), (41, 1), (44, 1), (51, 1), (52, 1), (60, 1)] }, { coefficient := -1, powers := [(8, 1), (10, 1), (22, 1), (24, 1), (44, 1), (51, 1), (52, 2), (60, 1)] }, { coefficient := -1, powers := [(8, 1), (10, 1), (22, 1), (28, 1), (42, 1), (44, 1), (52, 2), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (10, 1), (22, 1), (33, 1), (37, 1), (49, 1), (52, 2), (60, 1)] }, { coefficient := 1, powers := [(9, 1), (10, 1), (21, 1), (22, 1), (37, 1), (45, 1), (53, 1), (60, 1), (63, 1)] }, { coefficient := -1, powers := [(9, 1), (11, 1), (21, 1), (22, 1), (37, 1), (45, 1), (52, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(10, 1), (18, 1), (24, 1), (26, 1), (32, 1), (38, 1), (47, 1), (53, 1)] }, { coefficient := -1, powers := [(10, 1), (18, 1), (24, 1), (32, 1), (38, 1), (47, 1), (55, 1)] }, { coefficient := 1, powers := [(10, 1), (19, 1), (24, 1), (26, 1), (32, 1), (38, 1), (41, 1), (53, 1)] }, { coefficient := -1, powers := [(10, 1), (19, 1), (24, 1), (32, 1), (38, 1), (41, 1), (55, 1)] }, { coefficient := -1, powers := [(10, 1), (21, 1), (22, 1), (37, 1), (45, 1), (50, 1), (53, 1), (60, 1), (63, 1)] }, { coefficient := -1, powers := [(10, 1), (32, 1), (38, 1), (46, 1)] }, { coefficient := 1, powers := [(11, 1), (21, 1), (22, 1), (37, 1), (45, 1), (50, 1), (52, 1), (60, 1), (63, 1)] }, { coefficient := -1, powers := [(15, 1), (32, 1), (38, 1), (41, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (4, 1), (37, 1), (59, 1), (60, 1)] }, { coefficient := -1, powers := [(4, 1), (5, 1), (36, 1), (55, 1), (57, 1), (60, 1), (64, 1)] }, { coefficient := -1, powers := [(4, 1), (18, 1), (36, 1), (48, 1), (55, 1), (57, 1), (64, 1)] }, { coefficient := 1, powers := [(4, 1), (60, 1)] }, { coefficient := -1, powers := [(5, 1), (6, 1), (10, 1), (36, 1), (46, 1), (52, 1), (55, 1), (60, 1), (64, 1)] }, { coefficient := 1, powers := [(5, 1), (10, 1), (36, 1), (38, 1), (55, 1), (60, 1), (64, 1)] }, { coefficient := -1, powers := [(6, 1), (10, 1), (18, 1), (36, 1), (46, 1), (48, 1), (52, 1), (55, 1), (64, 1)] }, { coefficient := 1, powers := [(10, 1), (18, 1), (36, 1), (38, 1), (48, 1), (55, 1), (64, 1)] }, { coefficient := -1, powers := [(10, 1), (41, 1)] }, { coefficient := -1, powers := [(10, 1), (46, 1)] }, { coefficient := 1, powers := [(15, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (5, 1), (32, 1), (57, 1), (61, 1)] }, { coefficient := 1, powers := [(4, 1), (12, 1), (32, 1), (44, 1), (48, 1), (57, 1)] }, { coefficient := -1, powers := [(4, 1), (12, 1), (32, 1), (49, 1), (57, 1)] }, { coefficient := 1, powers := [(4, 1), (18, 1), (32, 1), (49, 1), (51, 1), (57, 1)] }, { coefficient := -1, powers := [(4, 1), (19, 1), (32, 1), (48, 1), (51, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (6, 1), (10, 1), (22, 1), (52, 1), (60, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (6, 1), (10, 1), (32, 1), (46, 1), (52, 1), (61, 1)] }, { coefficient := -1, powers := [(5, 1), (10, 1), (32, 1), (38, 1), (61, 1)] }, { coefficient := 1, powers := [(6, 1), (10, 1), (12, 1), (22, 1), (44, 1), (48, 1), (52, 1), (60, 1)] }, { coefficient := -1, powers := [(6, 1), (10, 1), (12, 1), (22, 1), (49, 1), (52, 1), (60, 1)] }, { coefficient := 1, powers := [(6, 1), (10, 1), (12, 1), (32, 1), (44, 1), (46, 1), (48, 1), (52, 1)] }, { coefficient := -1, powers := [(6, 1), (10, 1), (12, 1), (32, 1), (46, 1), (49, 1), (52, 1)] }, { coefficient := 1, powers := [(6, 1), (10, 1), (18, 1), (22, 1), (49, 1), (51, 1), (52, 1), (60, 1)] }, { coefficient := 1, powers := [(6, 1), (10, 1), (18, 1), (32, 1), (46, 1), (49, 1), (51, 1), (52, 1)] }, { coefficient := -1, powers := [(6, 1), (10, 1), (19, 1), (22, 1), (48, 1), (51, 1), (52, 1), (60, 1)] }, { coefficient := -1, powers := [(6, 1), (10, 1), (19, 1), (32, 1), (46, 1), (48, 1), (51, 1), (52, 1)] }, { coefficient := -1, powers := [(10, 1), (12, 1), (32, 1), (38, 1), (44, 1), (48, 1)] }, { coefficient := 1, powers := [(10, 1), (12, 1), (32, 1), (38, 1), (49, 1)] }, { coefficient := -1, powers := [(10, 1), (18, 1), (32, 1), (38, 1), (49, 1), (51, 1)] }, { coefficient := 1, powers := [(10, 1), (19, 1), (32, 1), (38, 1), (48, 1), (51, 1)] }]
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
    ¬ ∀ index : Fin 53,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component37.SelectedLeafB4_1_2_0.selectedHasNoCommonZero

end Krenn.Component37.SelectedLeafB4_1_2_0
