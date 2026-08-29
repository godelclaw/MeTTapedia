import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component37.SelectedLeafB2_7

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "00030dd4235a9fee2165784a566e084b664ecdf912b53eb7441cb50b2d1556e6"
def certificateSHA256 : String := "1c77da374782eb8ae85d6d3e3d1f8343ad86676cb9d797a7c78348544a8cc5b3"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 37 → Fin 664 := ![
  0,
  1,
  3,
  4,
  16,
  19,
  22,
  27,
  31,
  57,
  146,
  154,
  161,
  171,
  182,
  298,
  310,
  311,
  315,
  335,
  446,
  450,
  471,
  478,
  479,
  566,
  580,
  609,
  645,
  649,
  650,
  657,
  658,
  659,
  660,
  661,
  663
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 37 → SparsePoly (Fin 66) := ![
  [{ coefficient := 1, powers := [(1, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (40, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (35, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (53, 1)] }, { coefficient := 1, powers := [(11, 1), (27, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (25, 1)] }, { coefficient := 1, powers := [(15, 1), (20, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (25, 1)] }, { coefficient := 1, powers := [(15, 1), (20, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (42, 1)] }, { coefficient := 1, powers := [(27, 1), (48, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (46, 1)] }, { coefficient := 1, powers := [(4, 1), (35, 1)] }, { coefficient := 1, powers := [(15, 1), (22, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (41, 1)] }, { coefficient := 1, powers := [(19, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (52, 1)] }, { coefficient := 1, powers := [(24, 1), (57, 1)] }, { coefficient := 1, powers := [(29, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1), (51, 1)] }, { coefficient := 1, powers := [(25, 1), (46, 1), (51, 1)] }, { coefficient := 1, powers := [(51, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (40, 1), (58, 1)] }, { coefficient := 1, powers := [(8, 1), (36, 1), (40, 1)] }, { coefficient := 1, powers := [(19, 1), (30, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (61, 1)] }, { coefficient := 1, powers := [(12, 1), (49, 1)] }, { coefficient := 1, powers := [(19, 1), (21, 1), (53, 1)] }, { coefficient := 1, powers := [(19, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (61, 1)] }, { coefficient := 1, powers := [(12, 1), (26, 1), (47, 1)] }, { coefficient := 1, powers := [(12, 1), (58, 1)] }, { coefficient := 1, powers := [(19, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1), (53, 1)] }, { coefficient := 1, powers := [(46, 1), (51, 1)] }, { coefficient := 1, powers := [(51, 1), (57, 1)] }, { coefficient := 1, powers := [(53, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (48, 1), (51, 1)] }, { coefficient := 1, powers := [(21, 1), (51, 1)] }, { coefficient := 1, powers := [(25, 1), (42, 1)] }, { coefficient := 1, powers := [(25, 1), (48, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (48, 1), (52, 1)] }, { coefficient := 1, powers := [(21, 1), (52, 1)] }, { coefficient := 1, powers := [(21, 1), (57, 1)] }, { coefficient := 1, powers := [(48, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (44, 1), (54, 1)] }, { coefficient := 1, powers := [(24, 1), (58, 1)] }, { coefficient := 1, powers := [(30, 1), (49, 1)] }, { coefficient := 1, powers := [(36, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1)] }, { coefficient := 1, powers := [(6, 1), (60, 1)] }, { coefficient := 1, powers := [(25, 1), (41, 1)] }, { coefficient := 1, powers := [(25, 1), (46, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (48, 1), (53, 1)] }, { coefficient := 1, powers := [(21, 1), (51, 1), (57, 1)] }, { coefficient := 1, powers := [(21, 1), (53, 1)] }, { coefficient := 1, powers := [(42, 1)] }, { coefficient := 1, powers := [(48, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (38, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (41, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(41, 1)] }, { coefficient := 1, powers := [(46, 1)] }, { coefficient := 1, powers := [(52, 1)] }, { coefficient := 1, powers := [(57, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (41, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (47, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (36, 1), (41, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (58, 1)] }, { coefficient := 1, powers := [(18, 1), (30, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (29, 1), (54, 1)] }, { coefficient := 1, powers := [(19, 1), (30, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (42, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (48, 1), (53, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1), (29, 1), (48, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (53, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (39, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (42, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (49, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (49, 1)] }, { coefficient := 1, powers := [(8, 1), (36, 1), (42, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (58, 1)] }, { coefficient := 1, powers := [(12, 1), (30, 1), (49, 1)] }, { coefficient := 1, powers := [(12, 1), (36, 1), (39, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (55, 1)] }, { coefficient := 1, powers := [(19, 1), (30, 1), (42, 1)] }, { coefficient := 1, powers := [(19, 1), (33, 1), (39, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(40, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(42, 1), (65, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 37 → SparsePoly (Fin 66) := ![
  [{ coefficient := 1, powers := [(6, 1), (15, 1), (22, 1), (25, 1), (51, 1), (60, 1), (62, 2), (65, 1)] }, { coefficient := -1, powers := [(12, 1), (25, 2), (29, 1), (46, 1), (58, 1), (62, 1)] }, { coefficient := 1, powers := [(25, 2), (46, 1), (51, 1), (52, 1), (62, 1), (65, 1)] }, { coefficient := -2, powers := [(25, 1), (46, 1), (51, 1), (62, 1), (65, 1)] }, { coefficient := -2, powers := [(51, 1), (62, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (25, 2), (33, 1), (41, 1), (46, 1), (62, 1)] }, { coefficient := 1, powers := [(8, 1), (25, 2), (33, 1), (46, 2), (62, 1)] }, { coefficient := 1, powers := [(8, 1), (25, 2), (33, 1), (46, 1), (52, 1), (62, 1)] }, { coefficient := -1, powers := [(12, 1), (25, 2), (30, 1), (41, 1), (46, 1), (62, 1)] }, { coefficient := -1, powers := [(12, 1), (25, 2), (30, 1), (46, 2), (62, 1)] }, { coefficient := -1, powers := [(12, 1), (25, 2), (30, 1), (46, 1), (52, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (24, 1), (25, 2), (41, 1), (44, 1), (46, 1), (62, 1)] }, { coefficient := -1, powers := [(12, 1), (24, 1), (25, 2), (44, 1), (46, 2), (62, 1)] }, { coefficient := -1, powers := [(12, 1), (24, 1), (25, 2), (44, 1), (46, 1), (52, 1), (62, 1)] }, { coefficient := -1, powers := [(19, 1), (25, 2), (29, 1), (42, 1), (46, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (25, 2), (36, 1), (41, 1), (46, 1), (62, 1)] }, { coefficient := 1, powers := [(5, 1), (25, 2), (36, 1), (46, 2), (62, 1)] }, { coefficient := 1, powers := [(5, 1), (25, 2), (36, 1), (46, 1), (52, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (25, 2), (46, 1), (53, 1), (58, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(21, 1), (25, 2), (30, 1), (41, 1), (46, 1), (53, 1), (63, 1)] }, { coefficient := -1, powers := [(21, 1), (25, 2), (30, 1), (46, 2), (53, 1), (63, 1)] }, { coefficient := -1, powers := [(21, 1), (25, 2), (30, 1), (46, 1), (52, 1), (53, 1), (63, 1)] }, { coefficient := 1, powers := [(24, 1), (25, 2), (26, 1), (41, 1), (46, 1), (53, 1), (63, 1)] }, { coefficient := 1, powers := [(24, 1), (25, 2), (26, 1), (46, 2), (53, 1), (63, 1)] }, { coefficient := 1, powers := [(24, 1), (25, 2), (26, 1), (46, 1), (52, 1), (53, 1), (63, 1)] }, { coefficient := -1, powers := [(25, 2), (30, 1), (42, 1), (46, 2), (63, 1)] }, { coefficient := 1, powers := [(25, 2), (33, 1), (39, 1), (41, 1), (46, 1), (63, 1)] }, { coefficient := 1, powers := [(25, 2), (33, 1), (39, 1), (46, 2), (63, 1)] }, { coefficient := 1, powers := [(25, 2), (33, 1), (39, 1), (46, 1), (52, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (15, 1), (21, 1), (25, 1), (46, 1), (60, 1), (62, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (21, 1), (25, 1), (46, 1), (51, 2), (62, 1), (65, 2)] }],
  [{ coefficient := -2, powers := [(12, 1), (24, 1), (25, 2), (46, 1), (52, 1), (62, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (25, 1), (60, 1), (62, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(21, 1), (25, 2), (46, 2), (62, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(21, 1), (25, 1), (27, 1), (46, 2), (51, 1), (62, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (25, 1), (27, 1), (46, 2), (62, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(24, 1), (25, 2), (26, 1), (41, 1), (46, 1)] }, { coefficient := -1, powers := [(24, 1), (25, 2), (26, 1), (46, 2)] }, { coefficient := -1, powers := [(24, 1), (25, 2), (26, 1), (46, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(10, 1), (21, 1), (25, 1), (46, 1), (51, 1), (62, 1), (65, 2)] }],
  [{ coefficient := 1, powers := [(6, 1), (25, 1), (60, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(25, 2), (30, 1), (42, 1), (46, 1)] }],
  [{ coefficient := 2, powers := [(12, 1), (25, 2), (46, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(1, 1), (21, 1), (25, 1), (46, 2), (62, 1), (65, 1)] }, { coefficient := -1, powers := [(1, 1), (21, 1), (25, 1), (46, 1), (57, 1), (62, 1), (65, 1)] }, { coefficient := 1, powers := [(10, 1), (21, 1), (25, 1), (27, 1), (46, 1), (62, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(25, 2), (42, 1), (46, 2), (63, 1)] }, { coefficient := 1, powers := [(25, 2), (42, 1), (46, 1), (52, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(25, 2), (30, 1), (41, 1), (46, 1)] }, { coefficient := 1, powers := [(25, 2), (30, 1), (46, 2)] }, { coefficient := 1, powers := [(25, 2), (30, 1), (46, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (25, 2), (41, 1), (46, 1)] }, { coefficient := 1, powers := [(24, 1), (25, 2), (46, 2)] }, { coefficient := 1, powers := [(24, 1), (25, 2), (46, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (21, 1), (25, 2), (46, 2), (62, 1), (65, 1)] }, { coefficient := 1, powers := [(1, 1), (21, 1), (25, 1), (46, 1), (62, 1), (65, 1)] }, { coefficient := 1, powers := [(6, 1), (15, 1), (21, 1), (22, 1), (25, 1), (60, 1), (62, 1), (65, 1)] }, { coefficient := -2, powers := [(21, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(25, 1), (46, 1), (52, 1), (65, 1)] }, { coefficient := 2, powers := [(46, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (46, 1), (51, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (25, 2), (41, 1), (46, 1)] }, { coefficient := 1, powers := [(12, 1), (25, 2), (46, 2)] }, { coefficient := 1, powers := [(12, 1), (25, 2), (46, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(25, 1), (46, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (15, 1), (22, 1), (25, 1), (60, 1), (62, 1), (65, 1)] }, { coefficient := -1, powers := [(25, 1), (46, 1), (65, 1)] }, { coefficient := 2, powers := [(65, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (25, 2), (33, 1), (46, 1), (58, 1)] }, { coefficient := -1, powers := [(12, 1), (24, 1), (25, 2), (46, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(25, 2), (42, 1), (46, 1)] }],
  [{ coefficient := -1, powers := [(25, 2), (46, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(25, 2), (41, 1), (46, 1)] }, { coefficient := -1, powers := [(25, 2), (46, 2)] }, { coefficient := -1, powers := [(25, 2), (46, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(1, 1), (21, 1), (25, 2), (46, 3), (53, 1), (62, 1), (65, 1)] }, { coefficient := 1, powers := [(1, 1), (21, 1), (25, 1), (46, 3), (51, 1), (62, 1), (65, 1)] }, { coefficient := 1, powers := [(1, 1), (21, 1), (25, 1), (46, 2), (51, 1), (57, 1), (62, 1), (65, 1)] }, { coefficient := -1, powers := [(1, 1), (21, 1), (25, 1), (46, 2), (53, 1), (62, 1), (65, 1)] }, { coefficient := -1, powers := [(5, 1), (25, 2), (33, 1), (38, 1), (46, 1), (58, 1), (60, 1)] }, { coefficient := -1, powers := [(5, 1), (25, 2), (33, 1), (41, 1), (46, 1), (57, 1), (58, 1)] }, { coefficient := -1, powers := [(5, 1), (25, 2), (33, 1), (46, 2), (52, 1), (58, 1)] }, { coefficient := -1, powers := [(6, 1), (15, 1), (21, 1), (22, 1), (25, 1), (46, 1), (53, 1), (60, 1), (62, 1), (65, 1)] }, { coefficient := 1, powers := [(6, 1), (15, 1), (22, 1), (25, 1), (42, 1), (57, 1), (60, 1), (62, 1), (65, 1)] }, { coefficient := 1, powers := [(6, 1), (15, 1), (22, 1), (25, 1), (48, 1), (53, 1), (60, 1), (62, 1), (65, 1)] }, { coefficient := -1, powers := [(10, 1), (21, 1), (25, 1), (27, 1), (46, 2), (51, 1), (62, 1), (65, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (25, 2), (38, 1), (46, 1), (58, 1), (60, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (25, 2), (41, 1), (46, 1), (57, 1), (58, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (25, 2), (46, 2), (52, 1), (58, 1)] }, { coefficient := 2, powers := [(21, 1), (46, 1), (53, 1), (65, 1)] }, { coefficient := 1, powers := [(25, 1), (42, 1), (46, 1), (57, 1), (65, 1)] }, { coefficient := 1, powers := [(25, 1), (46, 2)] }, { coefficient := 1, powers := [(25, 1), (46, 1), (48, 1), (53, 1), (65, 1)] }, { coefficient := -2, powers := [(42, 1), (57, 1), (65, 1)] }, { coefficient := -2, powers := [(46, 1), (48, 1), (51, 1), (65, 1)] }, { coefficient := -2, powers := [(48, 1), (53, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (25, 2), (36, 1), (41, 1), (46, 1), (55, 1)] }, { coefficient := -1, powers := [(5, 1), (25, 2), (36, 1), (46, 2), (55, 1)] }, { coefficient := -1, powers := [(5, 1), (25, 2), (36, 1), (46, 1), (52, 1), (55, 1)] }, { coefficient := -1, powers := [(6, 1), (15, 1), (22, 1), (25, 1), (48, 1), (51, 1), (60, 1), (62, 1), (65, 1)] }, { coefficient := -1, powers := [(6, 1), (25, 1), (46, 1), (60, 1)] }, { coefficient := -1, powers := [(8, 1), (25, 2), (33, 1), (41, 1), (46, 1), (49, 1)] }, { coefficient := -1, powers := [(8, 1), (25, 2), (33, 1), (46, 2), (49, 1)] }, { coefficient := -1, powers := [(8, 1), (25, 2), (33, 1), (46, 1), (49, 1), (52, 1)] }, { coefficient := 2, powers := [(12, 1), (24, 1), (25, 2), (40, 1), (46, 1), (52, 1), (58, 1), (63, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (25, 2), (41, 1), (44, 1), (46, 1), (54, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (25, 2), (44, 1), (46, 2), (54, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (25, 2), (44, 1), (46, 1), (52, 1), (54, 1)] }, { coefficient := 1, powers := [(12, 1), (25, 2), (29, 1), (46, 1), (48, 1), (58, 1)] }, { coefficient := 1, powers := [(12, 1), (25, 2), (30, 1), (41, 1), (46, 1), (49, 1)] }, { coefficient := 1, powers := [(12, 1), (25, 2), (30, 1), (46, 2), (49, 1)] }, { coefficient := 1, powers := [(12, 1), (25, 2), (30, 1), (46, 1), (49, 1), (52, 1)] }, { coefficient := 1, powers := [(19, 1), (25, 2), (29, 1), (42, 1), (46, 1), (54, 1)] }, { coefficient := -1, powers := [(21, 1), (25, 1), (46, 1), (53, 1), (65, 1)] }, { coefficient := -1, powers := [(25, 2), (46, 1), (48, 1), (51, 1), (52, 1), (65, 1)] }, { coefficient := 2, powers := [(25, 1), (46, 1), (48, 1), (51, 1), (65, 1)] }, { coefficient := 2, powers := [(48, 1), (51, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(25, 2), (39, 1), (41, 1), (46, 1), (61, 1)] }, { coefficient := 1, powers := [(25, 2), (39, 1), (46, 2), (61, 1)] }, { coefficient := 1, powers := [(25, 2), (39, 1), (46, 1), (52, 1), (61, 1)] }, { coefficient := -1, powers := [(25, 2), (40, 1), (42, 1), (46, 2), (58, 1), (63, 1)] }, { coefficient := -1, powers := [(25, 2), (40, 1), (42, 1), (46, 1), (52, 1), (58, 1), (63, 1)] }, { coefficient := 1, powers := [(25, 2), (41, 1), (46, 1), (49, 1), (55, 1)] }, { coefficient := 1, powers := [(25, 2), (42, 1), (46, 2), (58, 1)] }, { coefficient := -1, powers := [(25, 2), (42, 1), (46, 1), (47, 1), (54, 1)] }, { coefficient := 1, powers := [(25, 2), (42, 1), (46, 1), (52, 1), (58, 1)] }, { coefficient := 1, powers := [(25, 2), (42, 1), (46, 1), (57, 1), (58, 1)] }, { coefficient := 1, powers := [(25, 2), (46, 2), (49, 1), (55, 1)] }, { coefficient := 1, powers := [(25, 2), (46, 1), (48, 1), (53, 1), (58, 1)] }, { coefficient := 1, powers := [(25, 2), (46, 1), (49, 1), (52, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (25, 2), (36, 1), (42, 1), (46, 2)] }, { coefficient := -1, powers := [(8, 1), (25, 2), (36, 1), (42, 1), (46, 1), (52, 1)] }, { coefficient := 2, powers := [(12, 1), (24, 1), (25, 2), (46, 1), (52, 1), (58, 1)] }, { coefficient := -1, powers := [(18, 1), (24, 1), (25, 2), (46, 1), (53, 1), (58, 1)] }, { coefficient := 1, powers := [(19, 1), (21, 1), (25, 2), (30, 1), (41, 1), (46, 1), (53, 1)] }, { coefficient := 1, powers := [(19, 1), (21, 1), (25, 2), (30, 1), (46, 2), (53, 1)] }, { coefficient := 1, powers := [(19, 1), (21, 1), (25, 2), (30, 1), (46, 1), (52, 1), (53, 1)] }, { coefficient := -1, powers := [(19, 1), (24, 1), (25, 2), (26, 1), (41, 1), (46, 1), (53, 1)] }, { coefficient := -1, powers := [(19, 1), (24, 1), (25, 2), (26, 1), (46, 2), (53, 1)] }, { coefficient := -1, powers := [(19, 1), (24, 1), (25, 2), (26, 1), (46, 1), (52, 1), (53, 1)] }, { coefficient := -1, powers := [(19, 1), (25, 2), (30, 1), (42, 1), (46, 1), (52, 1)] }, { coefficient := -1, powers := [(19, 1), (25, 2), (33, 1), (39, 1), (41, 1), (46, 1)] }, { coefficient := -1, powers := [(19, 1), (25, 2), (33, 1), (39, 1), (46, 2)] }, { coefficient := -1, powers := [(19, 1), (25, 2), (33, 1), (39, 1), (46, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (6, 1), (25, 1), (35, 1), (60, 1), (62, 1)] }, { coefficient := 1, powers := [(6, 1), (15, 1), (22, 1), (25, 1), (60, 1), (62, 1)] }, { coefficient := 1, powers := [(10, 1), (21, 1), (25, 1), (27, 1), (46, 1), (51, 1), (62, 1), (65, 1)] }, { coefficient := 1, powers := [(25, 2), (46, 1), (52, 1)] }, { coefficient := -1, powers := [(25, 1), (46, 1)] }, { coefficient := -2, powers := [] }]
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
    ¬ ∀ index : Fin 37,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((2 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (2 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (2 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component37.SelectedLeafB2_7.selectedHasNoCommonZero

end Krenn.Component37.SelectedLeafB2_7
