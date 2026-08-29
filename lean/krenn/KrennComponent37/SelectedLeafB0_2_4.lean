import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component37.SelectedLeafB0_2_4

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "9f510ad8839726f9435a750bc246bb33acee035ab0c96abb86ba83cb844111ef"
def certificateSHA256 : String := "b6f1d61861a0ddc2d83847c105d44840633fa7d659b6203ad2709e2993edd71e"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 57 → Fin 667 := ![
  9,
  14,
  22,
  171,
  175,
  177,
  179,
  181,
  183,
  184,
  256,
  266,
  298,
  299,
  307,
  308,
  310,
  311,
  312,
  315,
  316,
  317,
  393,
  410,
  411,
  431,
  433,
  438,
  446,
  450,
  453,
  454,
  455,
  460,
  471,
  478,
  479,
  480,
  502,
  526,
  556,
  566,
  567,
  580,
  604,
  605,
  609,
  645,
  656,
  657,
  658,
  659,
  660,
  663,
  664,
  665,
  666
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 57 → SparsePoly (Fin 64) := ![
  [{ coefficient := 1, powers := [(12, 1), (27, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (22, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (20, 1)] }, { coefficient := 1, powers := [(18, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (49, 1)] }, { coefficient := 1, powers := [(19, 1), (21, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (55, 1)] }, { coefficient := 1, powers := [(30, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (54, 1)] }, { coefficient := 1, powers := [(30, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(28, 1), (53, 1)] }, { coefficient := -1, powers := [(29, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (55, 1)] }, { coefficient := 1, powers := [(30, 1), (46, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (25, 1), (46, 1)] }, { coefficient := 1, powers := [(18, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (23, 1), (53, 1)] }, { coefficient := 1, powers := [(29, 1), (43, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (46, 1)] }, { coefficient := 1, powers := [(4, 1), (35, 1)] }, { coefficient := 1, powers := [(15, 1), (22, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (52, 1)] }, { coefficient := 1, powers := [(7, 1), (32, 1)] }, { coefficient := 1, powers := [(10, 1), (27, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (46, 1)] }, { coefficient := 1, powers := [(12, 1), (57, 1)] }, { coefficient := 1, powers := [(18, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (23, 1)] }, { coefficient := 1, powers := [(23, 1), (56, 1)] }, { coefficient := 1, powers := [(28, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (41, 1)] }, { coefficient := 1, powers := [(19, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (52, 1)] }, { coefficient := 1, powers := [(24, 1), (57, 1)] }, { coefficient := 1, powers := [(29, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (54, 1)] }, { coefficient := 1, powers := [(30, 1), (41, 1)] }, { coefficient := 1, powers := [(30, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1), (51, 1)] }, { coefficient := 1, powers := [(25, 1), (46, 1), (51, 1)] }, { coefficient := 1, powers := [(51, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1), (55, 1)] }, { coefficient := 1, powers := [(26, 1), (46, 1), (51, 1)] }, { coefficient := 1, powers := [(55, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (49, 1), (52, 1)] }, { coefficient := 1, powers := [(21, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(49, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (20, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1)] }, { coefficient := 1, powers := [(18, 1), (20, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (25, 1), (41, 1)] }, { coefficient := 1, powers := [(18, 1), (25, 1), (46, 1)] }, { coefficient := 1, powers := [(18, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (25, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (25, 1), (41, 1)] }, { coefficient := 1, powers := [(19, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (47, 1)] }, { coefficient := 1, powers := [(18, 1), (28, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (28, 1), (41, 1)] }, { coefficient := 1, powers := [(19, 1), (29, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (49, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1)] }, { coefficient := 1, powers := [(18, 1), (28, 1), (49, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1)] }, { coefficient := 1, powers := [(12, 1), (30, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (61, 1)] }, { coefficient := 1, powers := [(12, 1), (49, 1)] }, { coefficient := 1, powers := [(19, 1), (21, 1), (53, 1)] }, { coefficient := 1, powers := [(19, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (61, 1)] }, { coefficient := 1, powers := [(12, 1), (26, 1), (47, 1)] }, { coefficient := 1, powers := [(12, 1), (58, 1)] }, { coefficient := 1, powers := [(19, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (41, 1)] }, { coefficient := 1, powers := [(18, 1), (46, 1)] }, { coefficient := 1, powers := [(18, 1), (52, 1)] }, { coefficient := 1, powers := [(18, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (55, 1)] }, { coefficient := 1, powers := [(30, 1), (42, 1)] }, { coefficient := 1, powers := [(30, 1), (48, 1), (51, 1)] }, { coefficient := 1, powers := [(33, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (41, 1)] }, { coefficient := 1, powers := [(29, 1), (46, 1)] }, { coefficient := 1, powers := [(29, 1), (52, 1)] }, { coefficient := 1, powers := [(29, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (39, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (48, 1), (54, 1)] }, { coefficient := 1, powers := [(21, 1), (54, 1)] }, { coefficient := 1, powers := [(26, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1), (53, 1)] }, { coefficient := 1, powers := [(46, 1), (51, 1)] }, { coefficient := 1, powers := [(51, 1), (57, 1)] }, { coefficient := 1, powers := [(53, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (48, 1), (51, 1)] }, { coefficient := 1, powers := [(21, 1), (51, 1)] }, { coefficient := 1, powers := [(25, 1), (42, 1)] }, { coefficient := 1, powers := [(25, 1), (48, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (48, 1), (52, 1)] }, { coefficient := 1, powers := [(21, 1), (52, 1)] }, { coefficient := 1, powers := [(21, 1), (57, 1)] }, { coefficient := 1, powers := [(48, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (48, 1), (55, 1)] }, { coefficient := 1, powers := [(21, 1), (55, 1)] }, { coefficient := 1, powers := [(26, 1), (42, 1)] }, { coefficient := 1, powers := [(26, 1), (48, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (33, 1), (57, 1)] }, { coefficient := 1, powers := [(23, 1), (51, 1), (57, 1)] }, { coefficient := 1, powers := [(23, 1), (53, 1)] }, { coefficient := 1, powers := [(29, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (29, 1), (60, 1)] }, { coefficient := 1, powers := [(28, 1), (41, 1)] }, { coefficient := 1, powers := [(28, 1), (46, 1)] }, { coefficient := 1, powers := [(29, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (22, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1), (27, 1), (46, 1)] }, { coefficient := 1, powers := [(12, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(18, 1), (22, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (44, 1), (54, 1)] }, { coefficient := 1, powers := [(24, 1), (58, 1)] }, { coefficient := 1, powers := [(30, 1), (49, 1)] }, { coefficient := 1, powers := [(36, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (51, 1), (57, 1)] }, { coefficient := 1, powers := [(24, 1), (53, 1)] }, { coefficient := 1, powers := [(29, 1), (42, 1)] }, { coefficient := 1, powers := [(29, 1), (48, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1)] }, { coefficient := 1, powers := [(6, 1), (60, 1)] }, { coefficient := 1, powers := [(25, 1), (41, 1)] }, { coefficient := 1, powers := [(25, 1), (46, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(4, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (60, 1)] }, { coefficient := 1, powers := [(10, 1), (46, 1)] }, { coefficient := 1, powers := [(10, 1), (57, 1)] }, { coefficient := 1, powers := [(15, 1), (41, 1)] }, { coefficient := 1, powers := [(15, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (52, 1)] }, { coefficient := 1, powers := [(22, 1), (57, 1)] }, { coefficient := 1, powers := [(27, 1), (41, 1)] }, { coefficient := 1, powers := [(27, 1), (46, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1)] }, { coefficient := 1, powers := [(35, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (48, 1), (53, 1)] }, { coefficient := 1, powers := [(21, 1), (51, 1), (57, 1)] }, { coefficient := 1, powers := [(21, 1), (53, 1)] }, { coefficient := 1, powers := [(42, 1)] }, { coefficient := 1, powers := [(48, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (38, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (41, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(41, 1)] }, { coefficient := 1, powers := [(46, 1)] }, { coefficient := 1, powers := [(52, 1)] }, { coefficient := 1, powers := [(57, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (38, 1), (60, 1)] }, { coefficient := 1, powers := [(1, 1), (41, 1), (57, 1)] }, { coefficient := 1, powers := [(1, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(4, 1), (27, 1), (60, 1)] }, { coefficient := 1, powers := [(4, 1), (32, 1), (57, 1)] }, { coefficient := 1, powers := [(4, 1), (35, 1), (52, 1)] }, { coefficient := 1, powers := [(7, 1), (22, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (32, 1), (46, 1)] }, { coefficient := 1, powers := [(7, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(10, 1), (22, 1), (57, 1)] }, { coefficient := 1, powers := [(10, 1), (27, 1), (46, 1)] }, { coefficient := 1, powers := [(10, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(15, 1), (22, 1), (52, 1)] }, { coefficient := 1, powers := [(15, 1), (27, 1), (41, 1)] }, { coefficient := 1, powers := [(15, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (39, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (42, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (49, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (49, 1)] }, { coefficient := 1, powers := [(8, 1), (36, 1), (42, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (58, 1)] }, { coefficient := 1, powers := [(12, 1), (30, 1), (49, 1)] }, { coefficient := 1, powers := [(12, 1), (36, 1), (39, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (55, 1)] }, { coefficient := 1, powers := [(19, 1), (30, 1), (42, 1)] }, { coefficient := 1, powers := [(19, 1), (33, 1), (39, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1)] }],
  [{ coefficient := 1, powers := [(1, 1)] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(42, 1)] }],
  [{ coefficient := 1, powers := [(56, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(57, 1)] }],
  [{ coefficient := 1, powers := [(58, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 57 → SparsePoly (Fin 64) := ![
  [{ coefficient := -1, powers := [(7, 1), (30, 1), (49, 1), (60, 1)] }, { coefficient := 2, powers := [(10, 1), (30, 1), (41, 1), (49, 1)] }, { coefficient := 2, powers := [(10, 1), (30, 1), (49, 1), (52, 1)] }, { coefficient := -1, powers := [(15, 1), (30, 1), (41, 1), (49, 1)] }, { coefficient := -1, powers := [(15, 1), (30, 1), (49, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(10, 1), (30, 1), (49, 1), (53, 1)] }, { coefficient := 1, powers := [(15, 1), (30, 1), (49, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (18, 1), (30, 1), (49, 1), (60, 1)] }, { coefficient := -1, powers := [(15, 1), (18, 1), (30, 1), (49, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(24, 1), (26, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (22, 1), (30, 1), (49, 1), (53, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (30, 1), (35, 1), (49, 1), (52, 1), (53, 1)] }, { coefficient := 1, powers := [(15, 1), (22, 1), (30, 1), (49, 1), (52, 1), (53, 1)] }, { coefficient := 2, powers := [(30, 1), (49, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(28, 1), (55, 1)] }, { coefficient := -1, powers := [(30, 1), (51, 1)] }],
  [{ coefficient := -1, powers := [(18, 1), (49, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (44, 1)] }, { coefficient := -1, powers := [(19, 1), (51, 1)] }],
  [{ coefficient := -1, powers := [(19, 1), (26, 1), (43, 1), (48, 1), (63, 1)] }, { coefficient := -1, powers := [(19, 1), (26, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (21, 1)] }, { coefficient := 1, powers := [(19, 1), (25, 1), (48, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (22, 1), (30, 1), (49, 1), (60, 1)] }, { coefficient := 1, powers := [(15, 1), (22, 1), (30, 1), (49, 1), (52, 1)] }, { coefficient := 2, powers := [(30, 1), (49, 1)] }],
  [{ coefficient := -1, powers := [(19, 1), (26, 1), (48, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (30, 1), (49, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (30, 1), (46, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (22, 1), (25, 1), (30, 1), (49, 1), (60, 1)] }, { coefficient := -1, powers := [(7, 1), (30, 1), (35, 1), (49, 1)] }, { coefficient := -1, powers := [(15, 1), (22, 1), (25, 1), (30, 1), (49, 1), (52, 1)] }, { coefficient := -2, powers := [(25, 1), (30, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (26, 1), (48, 1), (53, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (25, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(19, 1), (25, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(19, 1), (21, 1), (51, 1)] }, { coefficient := -1, powers := [(19, 1), (25, 1), (48, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (24, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(19, 1), (24, 1)] }, { coefficient := -1, powers := [(19, 1), (28, 1), (48, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (30, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (22, 1), (30, 1), (49, 1), (60, 1)] }, { coefficient := -1, powers := [(7, 1), (30, 1), (35, 1), (49, 1), (52, 1)] }, { coefficient := -1, powers := [(15, 1), (22, 1), (30, 1), (49, 1), (52, 1)] }, { coefficient := -2, powers := [(30, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (30, 1), (35, 1), (49, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(24, 1), (55, 1)] }, { coefficient := -1, powers := [(28, 1), (48, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (48, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(55, 1)] }],
  [{ coefficient := 1, powers := [(49, 1)] }],
  [{ coefficient := 1, powers := [(30, 1)] }],
  [{ coefficient := 1, powers := [(24, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (25, 1), (30, 1), (35, 1), (49, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(19, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (21, 1), (25, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (29, 1), (51, 1)] }],
  [{ coefficient := -1, powers := [(19, 1), (24, 1), (25, 1), (54, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (26, 1)] }, { coefficient := 1, powers := [(19, 1), (26, 1), (28, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (30, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (30, 1), (44, 1)] }, { coefficient := -1, powers := [(19, 1), (25, 1), (29, 1), (55, 1)] }, { coefficient := 2, powers := [(19, 1), (28, 1), (55, 1)] }, { coefficient := 1, powers := [(19, 1), (30, 1), (51, 1)] }],
  [{ coefficient := -1, powers := [(19, 1), (29, 1)] }],
  [{ coefficient := -1, powers := [(19, 1), (26, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (21, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (30, 1), (49, 1)] }, { coefficient := -1, powers := [(15, 1), (30, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(12, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (25, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(19, 1), (21, 1), (29, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (27, 1), (30, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (15, 1), (30, 1), (49, 1)] }],
  [{ coefficient := -1, powers := [(19, 1), (30, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (12, 1), (30, 1), (35, 1), (49, 1)] }, { coefficient := -2, powers := [(10, 1), (12, 1), (27, 1), (30, 1), (49, 1)] }, { coefficient := -1, powers := [(19, 1), (21, 1), (28, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (30, 1), (49, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(7, 1), (12, 1), (30, 1), (35, 1), (38, 1), (49, 1), (60, 1)] }, { coefficient := -1, powers := [(7, 1), (12, 1), (30, 1), (35, 1), (41, 1), (49, 1), (57, 1)] }, { coefficient := -1, powers := [(7, 1), (12, 1), (30, 1), (35, 1), (46, 1), (49, 1), (52, 1)] }, { coefficient := 2, powers := [(10, 1), (12, 1), (27, 1), (30, 1), (38, 1), (49, 1), (60, 1)] }, { coefficient := 2, powers := [(10, 1), (12, 1), (27, 1), (30, 1), (41, 1), (49, 1), (57, 1)] }, { coefficient := 2, powers := [(10, 1), (12, 1), (27, 1), (30, 1), (46, 1), (49, 1), (52, 1)] }, { coefficient := -1, powers := [(12, 1), (30, 1), (44, 1), (48, 1), (52, 1)] }, { coefficient := 1, powers := [(12, 1), (30, 1), (49, 1), (52, 1)] }, { coefficient := 1, powers := [(19, 1), (21, 1), (28, 1), (38, 1), (55, 1), (60, 1)] }, { coefficient := 1, powers := [(19, 1), (21, 1), (28, 1), (41, 1), (55, 1), (57, 1)] }, { coefficient := 1, powers := [(19, 1), (21, 1), (28, 1), (46, 1), (52, 1), (55, 1)] }, { coefficient := 1, powers := [(19, 1), (21, 1), (29, 1), (46, 1), (55, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (25, 1), (46, 1), (53, 1), (54, 1)] }, { coefficient := -1, powers := [(19, 1), (24, 1), (26, 1), (46, 1), (53, 1)] }, { coefficient := -1, powers := [(19, 1), (24, 1), (46, 1), (51, 1), (54, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (46, 1), (55, 1)] }, { coefficient := 1, powers := [(19, 1), (25, 1), (29, 1), (48, 1), (52, 1), (55, 1)] }, { coefficient := -1, powers := [(19, 1), (26, 1), (28, 1), (46, 1), (48, 1), (53, 1)] }, { coefficient := 1, powers := [(19, 1), (28, 1), (46, 1), (48, 1), (55, 1)] }, { coefficient := -2, powers := [(19, 1), (28, 1), (48, 1), (52, 1), (55, 1)] }, { coefficient := -1, powers := [(19, 1), (29, 1), (39, 1), (51, 1), (60, 1)] }, { coefficient := -1, powers := [(19, 1), (29, 1), (48, 1), (51, 1), (54, 1)] }, { coefficient := 1, powers := [(19, 1), (29, 1), (48, 1), (55, 1)] }, { coefficient := -1, powers := [(19, 1), (30, 1), (41, 1), (48, 1), (51, 1)] }, { coefficient := -1, powers := [(19, 1), (30, 1), (48, 1), (51, 1), (52, 1)] }, { coefficient := 1, powers := [(19, 1), (30, 1), (48, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (30, 1), (38, 1), (49, 1), (60, 1)] }, { coefficient := 1, powers := [(12, 1), (30, 1), (41, 1), (49, 1), (57, 1)] }, { coefficient := -1, powers := [(12, 1), (30, 1), (46, 1), (49, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(25, 1), (47, 1), (48, 1), (55, 1)] }, { coefficient := 1, powers := [(39, 1), (61, 1)] }, { coefficient := -1, powers := [(49, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (19, 1), (30, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (58, 1)] }, { coefficient := 1, powers := [(8, 1), (36, 1)] }, { coefficient := -1, powers := [(19, 1), (25, 1), (29, 1), (54, 1)] }, { coefficient := -1, powers := [(19, 1), (25, 1), (30, 1), (41, 1)] }, { coefficient := 1, powers := [(19, 1), (26, 1), (29, 1)] }],
  [{ coefficient := -1, powers := [(19, 1), (23, 1), (26, 1), (48, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (19, 1), (26, 1), (33, 1), (48, 1)] }, { coefficient := 1, powers := [(4, 1), (12, 1), (30, 1), (32, 1), (49, 1)] }, { coefficient := -1, powers := [(7, 1), (12, 1), (20, 1), (22, 1), (30, 1), (49, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (12, 1), (20, 1), (30, 1), (35, 1), (49, 1), (52, 1)] }, { coefficient := -1, powers := [(7, 1), (12, 1), (22, 1), (25, 1), (30, 1), (49, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (18, 1), (25, 1), (30, 1), (35, 1), (49, 1), (53, 1)] }, { coefficient := 1, powers := [(10, 1), (12, 1), (27, 1), (30, 1), (49, 1)] }, { coefficient := 1, powers := [(12, 1), (15, 1), (20, 1), (22, 1), (30, 1), (49, 1), (52, 1)] }, { coefficient := 1, powers := [(12, 1), (15, 1), (22, 1), (25, 1), (30, 1), (49, 1), (52, 1)] }, { coefficient := 2, powers := [(12, 1), (20, 1), (30, 1), (49, 1)] }, { coefficient := -1, powers := [(12, 1), (21, 1), (30, 1), (44, 1)] }, { coefficient := 2, powers := [(12, 1), (25, 1), (30, 1), (49, 1)] }, { coefficient := -1, powers := [(19, 1), (21, 1), (28, 1), (55, 1)] }, { coefficient := 1, powers := [(19, 1), (23, 1), (26, 1), (48, 1), (51, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (25, 1), (55, 1)] }, { coefficient := -1, powers := [(19, 1), (24, 1), (26, 1), (51, 1)] }, { coefficient := -1, powers := [(19, 1), (26, 1), (28, 1), (48, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (33, 1)] }, { coefficient := -1, powers := [(12, 1), (24, 1)] }]
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
    ¬ ∀ index : Fin 57,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component37.SelectedLeafB0_2_4.selectedHasNoCommonZero

end Krenn.Component37.SelectedLeafB0_2_4
