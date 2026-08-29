import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component37.SelectedLeafB4_3_4

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "91a80e4ebb1deea35c5012af18dbf2752b23f0d41d7fc74680a75f1f1703f3d6"
def certificateSHA256 : String := "82eace8c103e0af229e97d3d8e5552bc27b920c96a9d882b30d5eb62ef467d7f"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 60 → Fin 667 := ![
  7,
  14,
  27,
  168,
  170,
  171,
  175,
  176,
  177,
  179,
  180,
  181,
  182,
  256,
  257,
  294,
  295,
  296,
  297,
  298,
  299,
  307,
  310,
  311,
  312,
  349,
  393,
  395,
  411,
  426,
  429,
  433,
  438,
  440,
  446,
  450,
  454,
  465,
  476,
  495,
  497,
  516,
  523,
  542,
  566,
  581,
  605,
  606,
  607,
  609,
  622,
  628,
  656,
  657,
  658,
  659,
  660,
  663,
  665,
  666
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 60 → SparsePoly (Fin 66) := ![
  [{ coefficient := 1, powers := [(8, 1), (32, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (22, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (26, 1)] }, { coefficient := 1, powers := [(18, 1), (20, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (44, 1)] }, { coefficient := 1, powers := [(19, 1), (20, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (20, 1)] }, { coefficient := 1, powers := [(18, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (44, 1)] }, { coefficient := 1, powers := [(19, 1), (20, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (49, 1)] }, { coefficient := 1, powers := [(19, 1), (21, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (55, 1)] }, { coefficient := 1, powers := [(30, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (44, 1)] }, { coefficient := 1, powers := [(28, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (54, 1)] }, { coefficient := 1, powers := [(30, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (42, 1)] }, { coefficient := 1, powers := [(27, 1), (48, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (25, 1), (46, 1)] }, { coefficient := 1, powers := [(18, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (25, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1)] }, { coefficient := 1, powers := [(20, 1), (44, 1)] }, { coefficient := 1, powers := [(25, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (49, 1)] }, { coefficient := 1, powers := [(21, 1), (44, 1)] }, { coefficient := 1, powers := [(25, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (51, 1)] }, { coefficient := 1, powers := [(20, 1), (51, 1)] }, { coefficient := 1, powers := [(25, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (55, 1)] }, { coefficient := 1, powers := [(20, 1), (55, 1)] }, { coefficient := 1, powers := [(26, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (46, 1)] }, { coefficient := 1, powers := [(4, 1), (35, 1)] }, { coefficient := 1, powers := [(15, 1), (22, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (52, 1)] }, { coefficient := 1, powers := [(7, 1), (32, 1)] }, { coefficient := 1, powers := [(10, 1), (27, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (46, 1)] }, { coefficient := 1, powers := [(12, 1), (57, 1)] }, { coefficient := 1, powers := [(18, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (41, 1)] }, { coefficient := 1, powers := [(19, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (52, 1)] }, { coefficient := 1, powers := [(24, 1), (57, 1)] }, { coefficient := 1, powers := [(29, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (54, 1)] }, { coefficient := 1, powers := [(30, 1), (41, 1)] }, { coefficient := 1, powers := [(30, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (30, 1), (60, 1)] }, { coefficient := 1, powers := [(23, 1), (54, 1)] }, { coefficient := 1, powers := [(30, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (20, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1)] }, { coefficient := 1, powers := [(18, 1), (20, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (25, 1), (48, 1)] }, { coefficient := 1, powers := [(18, 1), (21, 1), (51, 1)] }, { coefficient := 1, powers := [(18, 1), (25, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (25, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (25, 1), (41, 1)] }, { coefficient := 1, powers := [(19, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (53, 1)] }, { coefficient := 1, powers := [(20, 1), (51, 1), (57, 1)] }, { coefficient := 1, powers := [(20, 1), (53, 1)] }, { coefficient := 1, powers := [(51, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (44, 1)] }, { coefficient := 1, powers := [(18, 1), (28, 1), (44, 1)] }, { coefficient := 1, powers := [(18, 1), (36, 1), (37, 1)] }, { coefficient := 1, powers := [(19, 1), (23, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (49, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1)] }, { coefficient := 1, powers := [(18, 1), (28, 1), (49, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1)] }, { coefficient := 1, powers := [(12, 1), (30, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (36, 1)] }, { coefficient := 1, powers := [(23, 1), (44, 1)] }, { coefficient := 1, powers := [(28, 1), (44, 1)] }, { coefficient := 1, powers := [(36, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (61, 1)] }, { coefficient := 1, powers := [(12, 1), (49, 1)] }, { coefficient := 1, powers := [(19, 1), (21, 1), (53, 1)] }, { coefficient := 1, powers := [(19, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (61, 1)] }, { coefficient := 1, powers := [(12, 1), (26, 1), (47, 1)] }, { coefficient := 1, powers := [(12, 1), (58, 1)] }, { coefficient := 1, powers := [(19, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (55, 1)] }, { coefficient := 1, powers := [(30, 1), (42, 1)] }, { coefficient := 1, powers := [(30, 1), (48, 1), (51, 1)] }, { coefficient := 1, powers := [(33, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1), (53, 1)] }, { coefficient := 1, powers := [(3, 1), (61, 1)] }, { coefficient := 1, powers := [(20, 1), (44, 1), (53, 1)] }, { coefficient := 1, powers := [(44, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1), (55, 1)] }, { coefficient := 1, powers := [(26, 1), (47, 1), (51, 1)] }, { coefficient := 1, powers := [(44, 1), (55, 1)] }, { coefficient := 1, powers := [(51, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (46, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (46, 1)] }, { coefficient := 1, powers := [(12, 1), (30, 1), (46, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (49, 1), (52, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1), (52, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (49, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (25, 1), (61, 1)] }, { coefficient := 1, powers := [(12, 1), (25, 1), (49, 1)] }, { coefficient := 1, powers := [(19, 1), (21, 1), (51, 1)] }, { coefficient := 1, powers := [(19, 1), (25, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (22, 1), (60, 1)] }, { coefficient := 1, powers := [(6, 1), (32, 1), (46, 1)] }, { coefficient := 1, powers := [(6, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(22, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (22, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (46, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(18, 1), (22, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (44, 1), (54, 1)] }, { coefficient := 1, powers := [(24, 1), (58, 1)] }, { coefficient := 1, powers := [(30, 1), (49, 1)] }, { coefficient := 1, powers := [(36, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (52, 1)] }, { coefficient := 1, powers := [(3, 1), (60, 1)] }, { coefficient := 1, powers := [(20, 1), (52, 1)] }, { coefficient := 1, powers := [(20, 1), (57, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(22, 1), (52, 1)] }, { coefficient := 1, powers := [(22, 1), (57, 1)] }, { coefficient := 1, powers := [(27, 1), (41, 1)] }, { coefficient := 1, powers := [(27, 1), (46, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1)] }, { coefficient := 1, powers := [(35, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (37, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1)] }, { coefficient := 1, powers := [(3, 1), (25, 1), (60, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1), (60, 1)] }, { coefficient := 1, powers := [(20, 1)] }, { coefficient := 1, powers := [(25, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (37, 1), (61, 1)] }, { coefficient := 1, powers := [(0, 1), (44, 1), (51, 1)] }, { coefficient := 1, powers := [(3, 1), (25, 1), (61, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1), (61, 1)] }, { coefficient := 1, powers := [(20, 1), (44, 1), (51, 1)] }, { coefficient := 1, powers := [(25, 1), (44, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (48, 1), (53, 1)] }, { coefficient := 1, powers := [(21, 1), (51, 1), (57, 1)] }, { coefficient := 1, powers := [(21, 1), (53, 1)] }, { coefficient := 1, powers := [(42, 1)] }, { coefficient := 1, powers := [(48, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (47, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (29, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (47, 1)] }, { coefficient := 1, powers := [(12, 1), (29, 1), (58, 1)] }, { coefficient := 1, powers := [(12, 1), (30, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (29, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (30, 1), (61, 1)] }, { coefficient := 1, powers := [(3, 1), (33, 1), (58, 1)] }, { coefficient := 1, powers := [(3, 1), (36, 1), (55, 1)] }, { coefficient := 1, powers := [(23, 1), (44, 1), (55, 1)] }, { coefficient := 1, powers := [(23, 1), (51, 1), (58, 1)] }, { coefficient := 1, powers := [(30, 1), (44, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (38, 1), (60, 1)] }, { coefficient := 1, powers := [(1, 1), (41, 1), (57, 1)] }, { coefficient := 1, powers := [(1, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(4, 1), (27, 1), (60, 1)] }, { coefficient := 1, powers := [(4, 1), (32, 1), (57, 1)] }, { coefficient := 1, powers := [(4, 1), (35, 1), (52, 1)] }, { coefficient := 1, powers := [(7, 1), (22, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (32, 1), (46, 1)] }, { coefficient := 1, powers := [(7, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(10, 1), (22, 1), (57, 1)] }, { coefficient := 1, powers := [(10, 1), (27, 1), (46, 1)] }, { coefficient := 1, powers := [(10, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(15, 1), (22, 1), (52, 1)] }, { coefficient := 1, powers := [(15, 1), (27, 1), (41, 1)] }, { coefficient := 1, powers := [(15, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (39, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (42, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (49, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (49, 1)] }, { coefficient := 1, powers := [(8, 1), (36, 1), (42, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (58, 1)] }, { coefficient := 1, powers := [(12, 1), (30, 1), (49, 1)] }, { coefficient := 1, powers := [(12, 1), (36, 1), (39, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (55, 1)] }, { coefficient := 1, powers := [(19, 1), (30, 1), (42, 1)] }, { coefficient := 1, powers := [(19, 1), (33, 1), (39, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1)] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(42, 1), (64, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(57, 1)] }],
  [{ coefficient := 1, powers := [(58, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 60 → SparsePoly (Fin 66) := ![
  [{ coefficient := -1, powers := [(0, 1), (7, 1), (24, 1), (41, 1), (52, 1), (61, 1)] }, { coefficient := 1, powers := [(0, 1), (10, 1), (24, 1), (38, 1), (52, 1), (61, 1)] }, { coefficient := -1, powers := [(0, 1), (15, 1), (24, 1), (38, 1), (52, 1), (61, 1)] }, { coefficient := 3, powers := [(7, 1), (24, 1), (41, 1), (61, 1)] }, { coefficient := 2, powers := [(7, 1), (36, 1), (41, 1), (42, 1)] }, { coefficient := -3, powers := [(10, 1), (24, 1), (38, 1), (61, 1)] }, { coefficient := -2, powers := [(10, 1), (36, 1), (38, 1), (42, 1)] }, { coefficient := 3, powers := [(15, 1), (24, 1), (38, 1), (61, 1)] }, { coefficient := 2, powers := [(15, 1), (36, 1), (38, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (6, 1), (10, 1), (24, 1), (52, 2), (54, 1), (61, 1)] }, { coefficient := 1, powers := [(0, 1), (7, 1), (24, 1), (52, 1), (54, 1), (61, 1)] }, { coefficient := -3, powers := [(6, 1), (10, 1), (24, 1), (52, 1), (54, 1), (61, 1)] }, { coefficient := -2, powers := [(6, 1), (10, 1), (36, 1), (42, 1), (52, 1), (54, 1)] }, { coefficient := -3, powers := [(7, 1), (24, 1), (54, 1), (61, 1)] }, { coefficient := -2, powers := [(7, 1), (36, 1), (42, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (4, 1), (8, 1), (24, 1), (51, 1), (52, 1), (60, 1), (61, 1), (64, 1)] }, { coefficient := 1, powers := [(0, 1), (8, 1), (15, 1), (24, 1), (41, 1), (51, 1), (52, 1), (61, 1), (64, 1)] }, { coefficient := -3, powers := [(4, 1), (8, 1), (24, 1), (51, 1), (60, 1), (61, 1), (64, 1)] }, { coefficient := -2, powers := [(4, 1), (8, 1), (36, 1), (42, 1), (51, 1), (60, 1), (64, 1)] }, { coefficient := -3, powers := [(8, 1), (15, 1), (24, 1), (41, 1), (51, 1), (61, 1), (64, 1)] }, { coefficient := -2, powers := [(8, 1), (15, 1), (36, 1), (41, 1), (42, 1), (51, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (29, 1), (47, 1)] }, { coefficient := 1, powers := [(24, 1), (47, 1)] }, { coefficient := 1, powers := [(29, 1), (49, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (30, 1), (41, 1), (48, 1)] }, { coefficient := -1, powers := [(20, 1), (30, 1), (41, 1), (48, 1)] }, { coefficient := 1, powers := [(23, 1), (48, 1), (54, 1)] }, { coefficient := -1, powers := [(30, 1), (48, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (30, 1), (48, 1)] }, { coefficient := -1, powers := [(21, 1), (30, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (24, 1), (47, 1), (51, 1), (54, 1), (62, 1)] }, { coefficient := 1, powers := [(0, 1), (24, 1), (47, 1), (53, 1), (54, 1)] }, { coefficient := -1, powers := [(0, 1), (29, 1), (49, 1), (51, 1), (54, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 1), (29, 1), (49, 1), (53, 1), (54, 1)] }, { coefficient := -1, powers := [(0, 1), (30, 1), (41, 1), (44, 1), (48, 1), (51, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 1), (30, 1), (41, 1), (44, 1), (48, 1), (53, 1)] }, { coefficient := -1, powers := [(0, 1), (30, 1), (41, 1), (49, 1), (53, 1)] }, { coefficient := -1, powers := [(0, 1), (30, 1), (46, 1), (49, 1), (53, 1)] }, { coefficient := -1, powers := [(20, 1), (30, 1), (41, 1), (44, 1), (48, 1), (51, 1), (62, 1)] }, { coefficient := -1, powers := [(20, 1), (30, 1), (41, 1), (44, 1), (48, 1), (53, 1)] }, { coefficient := 1, powers := [(20, 1), (30, 1), (41, 1), (49, 1), (51, 1), (62, 1)] }, { coefficient := 1, powers := [(20, 1), (30, 1), (41, 1), (49, 1), (53, 1)] }, { coefficient := 1, powers := [(21, 1), (29, 1), (44, 1), (55, 1), (62, 1)] }, { coefficient := -1, powers := [(21, 1), (30, 1), (41, 1), (44, 1), (51, 1), (62, 1)] }, { coefficient := -1, powers := [(21, 1), (30, 1), (41, 1), (44, 1), (53, 1)] }, { coefficient := -1, powers := [(21, 1), (30, 1), (47, 1), (53, 1)] }, { coefficient := 1, powers := [(23, 1), (44, 1), (48, 1), (51, 1), (54, 1), (62, 1)] }, { coefficient := 1, powers := [(23, 1), (44, 1), (48, 1), (53, 1), (54, 1)] }, { coefficient := -1, powers := [(23, 1), (49, 1), (51, 1), (54, 1), (62, 1)] }, { coefficient := -1, powers := [(23, 1), (49, 1), (53, 1), (54, 1)] }, { coefficient := 1, powers := [(24, 1), (44, 1), (55, 1), (62, 1)] }, { coefficient := 1, powers := [(26, 1), (29, 1), (49, 1), (51, 1), (62, 1)] }, { coefficient := 1, powers := [(26, 1), (29, 1), (49, 1), (53, 1)] }, { coefficient := -1, powers := [(30, 1), (41, 1), (49, 1), (51, 1)] }, { coefficient := -1, powers := [(30, 1), (44, 1), (48, 1), (51, 1), (62, 1)] }, { coefficient := -3, powers := [(30, 1), (44, 1), (48, 1), (53, 1)] }, { coefficient := -1, powers := [(30, 1), (47, 1), (48, 1), (51, 1)] }, { coefficient := 2, powers := [(30, 1), (49, 1), (51, 1), (62, 1)] }, { coefficient := 3, powers := [(30, 1), (49, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(30, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (18, 1), (46, 1), (49, 1)] }, { coefficient := -1, powers := [(0, 1), (18, 1), (47, 1), (48, 1)] }, { coefficient := 1, powers := [(5, 1), (44, 1), (60, 1)] }, { coefficient := 1, powers := [(18, 1), (21, 1), (47, 1)] }, { coefficient := -2, powers := [(18, 1), (49, 1)] }, { coefficient := -2, powers := [(19, 1), (48, 1)] }],
  [{ coefficient := -1, powers := [(18, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (12, 1), (47, 1)] }, { coefficient := -2, powers := [(12, 1), (44, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (4, 1), (8, 1), (24, 1), (52, 1), (60, 1), (61, 1), (64, 1)] }, { coefficient := -1, powers := [(0, 1), (8, 1), (15, 1), (24, 1), (41, 1), (52, 1), (61, 1), (64, 1)] }, { coefficient := 3, powers := [(4, 1), (8, 1), (24, 1), (60, 1), (61, 1), (64, 1)] }, { coefficient := 2, powers := [(4, 1), (8, 1), (36, 1), (42, 1), (60, 1), (64, 1)] }, { coefficient := 3, powers := [(8, 1), (15, 1), (24, 1), (41, 1), (61, 1), (64, 1)] }, { coefficient := 2, powers := [(8, 1), (15, 1), (36, 1), (41, 1), (42, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (24, 1), (47, 1), (54, 1)] }, { coefficient := -1, powers := [(0, 1), (29, 1), (49, 1), (54, 1)] }, { coefficient := -1, powers := [(0, 1), (30, 1), (41, 1), (44, 1), (48, 1)] }, { coefficient := -1, powers := [(0, 1), (30, 1), (41, 1), (49, 1)] }, { coefficient := -1, powers := [(0, 1), (30, 1), (46, 1), (49, 1)] }, { coefficient := -1, powers := [(20, 1), (30, 1), (41, 1), (44, 1), (48, 1)] }, { coefficient := 1, powers := [(20, 1), (30, 1), (41, 1), (49, 1)] }, { coefficient := -1, powers := [(21, 1), (30, 1), (41, 1), (44, 1)] }, { coefficient := -1, powers := [(21, 1), (30, 1), (47, 1)] }, { coefficient := 1, powers := [(23, 1), (44, 1), (48, 1), (54, 1)] }, { coefficient := -1, powers := [(23, 1), (49, 1), (54, 1)] }, { coefficient := 1, powers := [(26, 1), (29, 1), (49, 1)] }, { coefficient := -3, powers := [(30, 1), (44, 1), (48, 1)] }, { coefficient := 3, powers := [(30, 1), (49, 1)] }],
  [{ coefficient := -1, powers := [(30, 1), (48, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (30, 1), (41, 1), (51, 1), (60, 1)] }, { coefficient := -1, powers := [(18, 1), (21, 1), (29, 1), (55, 1), (62, 1)] }, { coefficient := -1, powers := [(18, 1), (24, 1), (55, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (30, 1), (41, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (18, 1), (24, 1), (47, 1), (54, 1), (62, 1)] }, { coefficient := 1, powers := [(0, 1), (18, 1), (29, 1), (49, 1), (54, 1), (62, 1)] }, { coefficient := 1, powers := [(0, 1), (18, 1), (30, 1), (41, 1), (44, 1), (48, 1), (62, 1)] }, { coefficient := 1, powers := [(18, 1), (20, 1), (30, 1), (41, 1), (44, 1), (48, 1), (62, 1)] }, { coefficient := -1, powers := [(18, 1), (20, 1), (30, 1), (41, 1), (49, 1), (62, 1)] }, { coefficient := 1, powers := [(18, 1), (21, 1), (30, 1), (41, 1), (44, 1), (62, 1)] }, { coefficient := -1, powers := [(18, 1), (23, 1), (44, 1), (48, 1), (54, 1), (62, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (49, 1), (54, 1), (62, 1)] }, { coefficient := -1, powers := [(18, 1), (26, 1), (29, 1), (49, 1), (62, 1)] }, { coefficient := 1, powers := [(18, 1), (30, 1), (41, 1), (49, 1)] }, { coefficient := 1, powers := [(18, 1), (30, 1), (44, 1), (48, 1), (62, 1)] }, { coefficient := 1, powers := [(18, 1), (30, 1), (47, 1), (48, 1)] }, { coefficient := -2, powers := [(18, 1), (30, 1), (49, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(18, 1), (21, 1), (29, 1), (47, 1)] }, { coefficient := -1, powers := [(18, 1), (24, 1), (47, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (8, 1), (24, 1), (52, 2), (61, 1)] }, { coefficient := 3, powers := [(8, 1), (24, 1), (52, 1), (61, 1)] }, { coefficient := 2, powers := [(8, 1), (36, 1), (42, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (8, 1), (24, 1), (41, 1), (52, 1), (61, 1)] }, { coefficient := -3, powers := [(8, 1), (24, 1), (41, 1), (61, 1)] }, { coefficient := -2, powers := [(8, 1), (36, 1), (41, 1), (42, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (24, 1), (25, 1), (47, 1), (54, 1)] }, { coefficient := 1, powers := [(0, 1), (25, 1), (29, 1), (49, 1), (54, 1)] }, { coefficient := 1, powers := [(0, 1), (25, 1), (30, 1), (41, 1), (44, 1), (48, 1)] }, { coefficient := 1, powers := [(0, 1), (25, 1), (30, 1), (41, 1), (49, 1)] }, { coefficient := 1, powers := [(0, 1), (25, 1), (30, 1), (46, 1), (49, 1)] }, { coefficient := 1, powers := [(20, 1), (25, 1), (30, 1), (41, 1), (44, 1), (48, 1)] }, { coefficient := -1, powers := [(20, 1), (25, 1), (30, 1), (41, 1), (49, 1)] }, { coefficient := 1, powers := [(21, 1), (25, 1), (30, 1), (41, 1), (44, 1)] }, { coefficient := 1, powers := [(21, 1), (25, 1), (30, 1), (47, 1)] }, { coefficient := -1, powers := [(23, 1), (25, 1), (44, 1), (48, 1), (54, 1)] }, { coefficient := 1, powers := [(23, 1), (25, 1), (49, 1), (54, 1)] }, { coefficient := -1, powers := [(25, 1), (26, 1), (29, 1), (49, 1)] }, { coefficient := 3, powers := [(25, 1), (30, 1), (44, 1), (48, 1)] }, { coefficient := -3, powers := [(25, 1), (30, 1), (49, 1)] }],
  [{ coefficient := -1, powers := [(21, 1), (30, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (8, 1), (61, 1)] }, { coefficient := 1, powers := [(0, 1), (19, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (12, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (24, 1), (47, 1), (54, 1)] }, { coefficient := 1, powers := [(0, 1), (29, 1), (49, 1), (54, 1)] }, { coefficient := 1, powers := [(0, 1), (30, 1), (41, 1), (44, 1), (48, 1)] }, { coefficient := 1, powers := [(0, 1), (30, 1), (41, 1), (49, 1)] }, { coefficient := 1, powers := [(0, 1), (30, 1), (46, 1), (49, 1)] }, { coefficient := 1, powers := [(20, 1), (30, 1), (41, 1), (44, 1), (48, 1)] }, { coefficient := -1, powers := [(20, 1), (30, 1), (41, 1), (49, 1)] }, { coefficient := 1, powers := [(21, 1), (30, 1), (41, 1), (44, 1)] }, { coefficient := 1, powers := [(21, 1), (30, 1), (47, 1)] }, { coefficient := -1, powers := [(23, 1), (44, 1), (48, 1), (54, 1)] }, { coefficient := 1, powers := [(23, 1), (49, 1), (54, 1)] }, { coefficient := -1, powers := [(26, 1), (29, 1), (49, 1)] }, { coefficient := 3, powers := [(30, 1), (44, 1), (48, 1)] }, { coefficient := -3, powers := [(30, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(30, 1), (47, 1)] }],
  [{ coefficient := -1, powers := [(30, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (19, 1), (30, 1), (41, 1), (48, 1)] }, { coefficient := 2, powers := [(18, 1), (30, 1), (44, 1), (48, 1)] }, { coefficient := 1, powers := [(19, 1), (20, 1), (30, 1), (41, 1), (48, 1)] }, { coefficient := -1, powers := [(19, 1), (23, 1), (48, 1), (54, 1)] }, { coefficient := 1, powers := [(19, 1), (30, 1), (48, 1)] }],
  [{ coefficient := 2, powers := [(48, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(55, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (46, 1), (49, 1)] }, { coefficient := 1, powers := [(0, 1), (47, 1), (48, 1)] }, { coefficient := -1, powers := [(21, 1), (47, 1)] }, { coefficient := 2, powers := [(49, 1)] }],
  [{ coefficient := -2, powers := [(18, 1), (48, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (30, 1), (41, 1)] }, { coefficient := 1, powers := [(20, 1), (30, 1), (41, 1)] }, { coefficient := -1, powers := [(23, 1), (54, 1)] }, { coefficient := 1, powers := [(30, 1)] }],
  [{ coefficient := -1, powers := [(21, 1), (29, 1)] }, { coefficient := -1, powers := [(24, 1)] }],
  [{ coefficient := 2, powers := [(19, 1)] }],
  [{ coefficient := -2, powers := [(18, 1), (30, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (21, 1), (29, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (49, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (55, 1)] }, { coefficient := -1, powers := [(20, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(30, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (8, 1), (10, 1), (24, 1), (52, 2), (61, 1)] }, { coefficient := -3, powers := [(8, 1), (10, 1), (24, 1), (52, 1), (61, 1)] }, { coefficient := -2, powers := [(8, 1), (10, 1), (36, 1), (42, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (6, 1), (10, 1), (24, 1), (52, 2), (61, 1)] }, { coefficient := -1, powers := [(0, 1), (7, 1), (24, 1), (52, 1), (61, 1)] }, { coefficient := 3, powers := [(6, 1), (10, 1), (24, 1), (52, 1), (61, 1)] }, { coefficient := 2, powers := [(6, 1), (10, 1), (36, 1), (42, 1), (52, 1)] }, { coefficient := 3, powers := [(7, 1), (24, 1), (61, 1)] }, { coefficient := 2, powers := [(7, 1), (36, 1), (42, 1)] }],
  [{ coefficient := 2, powers := [(12, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (36, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (8, 1), (10, 1), (24, 1), (52, 1), (61, 1)] }, { coefficient := 3, powers := [(8, 1), (10, 1), (24, 1), (61, 1)] }, { coefficient := 2, powers := [(8, 1), (10, 1), (36, 1), (42, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (30, 1), (41, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (30, 1), (41, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (19, 1), (30, 1), (41, 1)] }, { coefficient := -1, powers := [(19, 1), (20, 1), (30, 1), (41, 1)] }, { coefficient := 1, powers := [(19, 1), (23, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (48, 1)] }, { coefficient := 1, powers := [(21, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (60, 1)] }, { coefficient := 2, powers := [(18, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (8, 1), (24, 1), (52, 1), (61, 1)] }, { coefficient := -3, powers := [(8, 1), (24, 1), (61, 1)] }, { coefficient := -2, powers := [(8, 1), (36, 1), (42, 1)] }],
  [{ coefficient := -2, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (18, 1), (24, 1), (47, 1), (51, 1), (54, 1)] }, { coefficient := -1, powers := [(0, 1), (18, 1), (29, 1), (49, 1), (51, 1), (54, 1)] }, { coefficient := -1, powers := [(0, 1), (18, 1), (30, 1), (41, 1), (44, 1), (48, 1), (51, 1)] }, { coefficient := -1, powers := [(18, 1), (20, 1), (30, 1), (41, 1), (44, 1), (48, 1), (51, 1)] }, { coefficient := 1, powers := [(18, 1), (20, 1), (30, 1), (41, 1), (49, 1), (51, 1)] }, { coefficient := 1, powers := [(18, 1), (21, 1), (29, 1), (44, 1), (55, 1)] }, { coefficient := -1, powers := [(18, 1), (21, 1), (30, 1), (41, 1), (44, 1), (51, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (44, 1), (48, 1), (51, 1), (54, 1)] }, { coefficient := -1, powers := [(18, 1), (23, 1), (49, 1), (51, 1), (54, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (44, 1), (55, 1)] }, { coefficient := 1, powers := [(18, 1), (26, 1), (29, 1), (49, 1), (51, 1)] }, { coefficient := -1, powers := [(18, 1), (30, 1), (44, 1), (48, 1), (51, 1)] }, { coefficient := 2, powers := [(18, 1), (30, 1), (49, 1), (51, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (8, 1), (24, 1), (38, 1), (52, 1), (60, 1), (61, 1)] }, { coefficient := -1, powers := [(0, 1), (8, 1), (24, 1), (41, 1), (52, 2), (61, 1)] }, { coefficient := -1, powers := [(0, 1), (8, 1), (24, 1), (41, 1), (52, 1), (57, 1), (61, 1)] }, { coefficient := 3, powers := [(8, 1), (24, 1), (38, 1), (60, 1), (61, 1)] }, { coefficient := 3, powers := [(8, 1), (24, 1), (41, 1), (52, 1), (61, 1)] }, { coefficient := 3, powers := [(8, 1), (24, 1), (41, 1), (57, 1), (61, 1)] }, { coefficient := 2, powers := [(8, 1), (36, 1), (38, 1), (42, 1), (60, 1)] }, { coefficient := 2, powers := [(8, 1), (36, 1), (41, 1), (42, 1), (52, 1)] }, { coefficient := 2, powers := [(8, 1), (36, 1), (41, 1), (42, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (49, 1), (52, 1), (55, 1)] }, { coefficient := 1, powers := [(20, 1), (49, 1), (52, 1), (55, 1)] }, { coefficient := 2, powers := [(39, 1), (61, 1)] }, { coefficient := 2, powers := [(42, 1), (58, 1)] }, { coefficient := -2, powers := [(44, 1), (48, 1), (55, 1)] }, { coefficient := -1, powers := [(49, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (4, 1), (8, 1), (24, 1), (27, 1), (52, 1), (60, 1), (61, 1)] }, { coefficient := 1, powers := [(0, 1), (8, 1), (15, 1), (24, 1), (27, 1), (41, 1), (52, 1), (61, 1)] }, { coefficient := -3, powers := [(4, 1), (8, 1), (24, 1), (27, 1), (60, 1), (61, 1)] }, { coefficient := -2, powers := [(4, 1), (8, 1), (27, 1), (36, 1), (42, 1), (60, 1)] }, { coefficient := -3, powers := [(8, 1), (15, 1), (24, 1), (27, 1), (41, 1), (61, 1)] }, { coefficient := -2, powers := [(8, 1), (15, 1), (27, 1), (36, 1), (41, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(0, 2), (19, 1), (30, 1), (41, 1), (42, 1)] }, { coefficient := -1, powers := [(0, 1), (4, 1), (8, 1), (24, 1), (32, 1), (52, 1), (61, 1)] }, { coefficient := -1, powers := [(0, 1), (8, 1), (24, 1), (61, 1)] }, { coefficient := 1, powers := [(0, 1), (12, 1), (20, 1), (24, 1), (47, 1), (54, 1)] }, { coefficient := -1, powers := [(0, 1), (12, 1), (20, 1), (29, 1), (49, 1), (54, 1)] }, { coefficient := -1, powers := [(0, 1), (12, 1), (20, 1), (30, 1), (41, 1), (44, 1), (48, 1)] }, { coefficient := -1, powers := [(0, 1), (12, 1), (20, 1), (30, 1), (41, 1), (49, 1)] }, { coefficient := -1, powers := [(0, 1), (12, 1), (20, 1), (30, 1), (46, 1), (49, 1)] }, { coefficient := 1, powers := [(0, 1), (12, 1), (24, 1), (25, 1), (47, 1), (54, 1)] }, { coefficient := -1, powers := [(0, 1), (12, 1), (25, 1), (29, 1), (49, 1), (54, 1)] }, { coefficient := -1, powers := [(0, 1), (12, 1), (25, 1), (30, 1), (41, 1), (44, 1), (48, 1)] }, { coefficient := -1, powers := [(0, 1), (12, 1), (25, 1), (30, 1), (41, 1), (49, 1)] }, { coefficient := -1, powers := [(0, 1), (12, 1), (25, 1), (30, 1), (46, 1), (49, 1)] }, { coefficient := 1, powers := [(0, 1), (19, 1), (20, 1), (30, 1), (41, 1), (42, 1)] }, { coefficient := -1, powers := [(0, 1), (19, 1), (20, 1), (30, 1), (41, 1), (48, 1), (51, 1)] }, { coefficient := 1, powers := [(0, 1), (19, 1), (21, 1), (30, 1), (41, 1), (51, 1)] }, { coefficient := -1, powers := [(0, 1), (19, 1), (23, 1), (42, 1), (54, 1)] }, { coefficient := -1, powers := [(0, 1), (19, 1), (24, 1), (55, 1)] }, { coefficient := 3, powers := [(4, 1), (8, 1), (24, 1), (32, 1), (61, 1)] }, { coefficient := 2, powers := [(4, 1), (8, 1), (32, 1), (36, 1), (42, 1)] }, { coefficient := -1, powers := [(5, 1), (20, 1), (36, 1), (55, 1)] }, { coefficient := -1, powers := [(12, 1), (20, 2), (30, 1), (41, 1), (44, 1), (48, 1)] }, { coefficient := 1, powers := [(12, 1), (20, 2), (30, 1), (41, 1), (49, 1)] }, { coefficient := -1, powers := [(12, 1), (20, 1), (21, 1), (30, 1), (41, 1), (44, 1)] }, { coefficient := -1, powers := [(12, 1), (20, 1), (21, 1), (30, 1), (47, 1)] }, { coefficient := 1, powers := [(12, 1), (20, 1), (23, 1), (44, 1), (48, 1), (54, 1)] }, { coefficient := -1, powers := [(12, 1), (20, 1), (23, 1), (49, 1), (54, 1)] }, { coefficient := -1, powers := [(12, 1), (20, 1), (25, 1), (30, 1), (41, 1), (44, 1), (48, 1)] }, { coefficient := 1, powers := [(12, 1), (20, 1), (25, 1), (30, 1), (41, 1), (49, 1)] }, { coefficient := 1, powers := [(12, 1), (20, 1), (26, 1), (29, 1), (49, 1)] }, { coefficient := -3, powers := [(12, 1), (20, 1), (30, 1), (44, 1), (48, 1)] }, { coefficient := 3, powers := [(12, 1), (20, 1), (30, 1), (49, 1)] }, { coefficient := -1, powers := [(12, 1), (21, 1), (25, 1), (30, 1), (41, 1), (44, 1)] }, { coefficient := -1, powers := [(12, 1), (21, 1), (25, 1), (30, 1), (47, 1)] }, { coefficient := 1, powers := [(12, 1), (23, 1), (25, 1), (44, 1), (48, 1), (54, 1)] }, { coefficient := -1, powers := [(12, 1), (23, 1), (25, 1), (49, 1), (54, 1)] }, { coefficient := 1, powers := [(12, 1), (25, 1), (26, 1), (29, 1), (49, 1)] }, { coefficient := -3, powers := [(12, 1), (25, 1), (30, 1), (44, 1), (48, 1)] }, { coefficient := 3, powers := [(12, 1), (25, 1), (30, 1), (49, 1)] }, { coefficient := -2, powers := [(18, 1), (20, 1), (30, 1), (44, 1), (48, 1), (51, 1)] }, { coefficient := -1, powers := [(19, 1), (20, 2), (30, 1), (41, 1), (48, 1), (51, 1)] }, { coefficient := 1, powers := [(19, 1), (20, 1), (21, 1), (30, 1), (41, 1), (51, 1)] }, { coefficient := 1, powers := [(19, 1), (20, 1), (23, 1), (48, 1), (51, 1), (54, 1)] }, { coefficient := -1, powers := [(19, 1), (20, 1), (30, 1), (48, 1), (51, 1)] }, { coefficient := -1, powers := [(19, 1), (21, 1), (23, 1), (51, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (12, 1), (29, 1), (48, 1)] }, { coefficient := 1, powers := [(3, 1), (5, 1), (33, 1), (60, 1)] }, { coefficient := -2, powers := [(3, 1), (18, 1), (33, 1), (48, 1)] }, { coefficient := 1, powers := [(5, 1), (23, 1), (51, 1), (60, 1)] }, { coefficient := 2, powers := [(5, 1), (33, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1)] }, { coefficient := -1, powers := [(18, 1), (21, 1), (29, 1), (51, 1)] }, { coefficient := -2, powers := [(18, 1), (23, 1), (48, 1), (51, 1)] }, { coefficient := -1, powers := [(18, 1), (24, 1), (51, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
/-- Lean replays the exact selected-row integer certificate. -/
theorem constantIdentity :
    ∑ index, (multipliers index).toPoly *
      (selectedEquations index).toPoly = C (2 : ℤ) := by
  simp (config := { maxSteps := 1000000 })
    [Fin.sum_univ_succ, multipliers, selectedEquations,
    SparsePoly.toPoly, SparseTerm.toPoly]
  ring

/-- The selected rows have no common zero in a characteristic-zero ring. -/
theorem selectedHasNoCommonZero {R : Type*} [CommRing R] [Nontrivial R] [CharZero R]
    (values : Fin 66 → R) :
    ¬ ∀ index : Fin 60,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((2 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (2 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (2 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component37.SelectedLeafB4_3_4.selectedHasNoCommonZero

end Krenn.Component37.SelectedLeafB4_3_4
