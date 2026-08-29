import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component37.SelectedLeafB0_3_7

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "d627102e4027190dcadb8cf0787cebd7bad1d024abed0ce977bda56c7f640ee9"
def certificateSHA256 : String := "667224eca9f46eeb07caf5ad45fec99e0a8625c155c32198efb9d10ce884220a"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 67 → Fin 667 := ![
  5,
  7,
  23,
  27,
  170,
  175,
  178,
  179,
  180,
  182,
  183,
  256,
  266,
  279,
  280,
  283,
  294,
  295,
  297,
  298,
  299,
  307,
  308,
  315,
  342,
  393,
  407,
  409,
  414,
  427,
  429,
  431,
  438,
  440,
  445,
  454,
  460,
  465,
  471,
  478,
  479,
  480,
  483,
  496,
  502,
  519,
  542,
  562,
  566,
  567,
  581,
  605,
  623,
  624,
  626,
  628,
  642,
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
def selectedEquations : Fin 67 → SparsePoly (Fin 67) := ![
  [{ coefficient := 1, powers := [(5, 1), (35, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (32, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (44, 1)] }, { coefficient := 1, powers := [(19, 1), (20, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (20, 1)] }, { coefficient := 1, powers := [(18, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (47, 1)] }, { coefficient := -1, powers := [(29, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (55, 1)] }, { coefficient := 1, powers := [(30, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (44, 1)] }, { coefficient := 1, powers := [(28, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (42, 1)] }, { coefficient := 1, powers := [(27, 1), (48, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(28, 1), (53, 1)] }, { coefficient := -1, powers := [(29, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (25, 1), (46, 1)] }, { coefficient := 1, powers := [(18, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (23, 1), (53, 1)] }, { coefficient := 1, powers := [(29, 1), (43, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (25, 1), (44, 1)] }, { coefficient := 1, powers := [(19, 1), (20, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (25, 1), (49, 1)] }, { coefficient := 1, powers := [(19, 1), (21, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (44, 1), (54, 1)] }, { coefficient := 1, powers := [(22, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1)] }, { coefficient := 1, powers := [(20, 1), (44, 1)] }, { coefficient := 1, powers := [(25, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (49, 1)] }, { coefficient := 1, powers := [(21, 1), (44, 1)] }, { coefficient := 1, powers := [(25, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (55, 1)] }, { coefficient := 1, powers := [(20, 1), (55, 1)] }, { coefficient := 1, powers := [(26, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (46, 1)] }, { coefficient := 1, powers := [(4, 1), (35, 1)] }, { coefficient := 1, powers := [(15, 1), (22, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (52, 1)] }, { coefficient := 1, powers := [(7, 1), (32, 1)] }, { coefficient := 1, powers := [(10, 1), (27, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (46, 1)] }, { coefficient := 1, powers := [(12, 1), (57, 1)] }, { coefficient := 1, powers := [(18, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (23, 1)] }, { coefficient := 1, powers := [(23, 1), (56, 1)] }, { coefficient := 1, powers := [(28, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1), (51, 1)] }, { coefficient := 1, powers := [(25, 1), (46, 1), (51, 1)] }, { coefficient := 1, powers := [(51, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (46, 1), (51, 1)] }, { coefficient := 1, powers := [(12, 1), (28, 1), (46, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (20, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1)] }, { coefficient := 1, powers := [(18, 1), (20, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (20, 1), (52, 1)] }, { coefficient := 1, powers := [(18, 1), (20, 1), (57, 1)] }, { coefficient := 1, powers := [(18, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (21, 1), (58, 1)] }, { coefficient := 1, powers := [(18, 1), (26, 1), (49, 1)] }, { coefficient := 1, powers := [(19, 1), (21, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (44, 1), (55, 1)] }, { coefficient := 1, powers := [(29, 1), (51, 1), (58, 1)] }, { coefficient := 1, powers := [(30, 1), (47, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (54, 1)] }, { coefficient := 1, powers := [(3, 1), (26, 1), (60, 1)] }, { coefficient := 1, powers := [(20, 1), (54, 1)] }, { coefficient := 1, powers := [(26, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (44, 1)] }, { coefficient := 1, powers := [(18, 1), (28, 1), (44, 1)] }, { coefficient := 1, powers := [(18, 1), (36, 1), (37, 1)] }, { coefficient := 1, powers := [(19, 1), (23, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (47, 1)] }, { coefficient := 1, powers := [(18, 1), (28, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (28, 1), (41, 1)] }, { coefficient := 1, powers := [(19, 1), (29, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1)] }, { coefficient := 1, powers := [(12, 1), (30, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (36, 1)] }, { coefficient := 1, powers := [(23, 1), (44, 1)] }, { coefficient := 1, powers := [(28, 1), (44, 1)] }, { coefficient := 1, powers := [(36, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (60, 1)] }, { coefficient := 1, powers := [(18, 1), (21, 1), (52, 1)] }, { coefficient := 1, powers := [(18, 1), (21, 1), (57, 1)] }, { coefficient := 1, powers := [(18, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (55, 1)] }, { coefficient := 1, powers := [(30, 1), (42, 1)] }, { coefficient := 1, powers := [(30, 1), (48, 1), (51, 1)] }, { coefficient := 1, powers := [(33, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (39, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (48, 1), (54, 1)] }, { coefficient := 1, powers := [(21, 1), (54, 1)] }, { coefficient := 1, powers := [(26, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1), (53, 1)] }, { coefficient := 1, powers := [(3, 1), (61, 1)] }, { coefficient := 1, powers := [(20, 1), (44, 1), (53, 1)] }, { coefficient := 1, powers := [(44, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1), (53, 1)] }, { coefficient := 1, powers := [(46, 1), (51, 1)] }, { coefficient := 1, powers := [(51, 1), (57, 1)] }, { coefficient := 1, powers := [(53, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (48, 1), (51, 1)] }, { coefficient := 1, powers := [(21, 1), (51, 1)] }, { coefficient := 1, powers := [(25, 1), (42, 1)] }, { coefficient := 1, powers := [(25, 1), (48, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (48, 1), (52, 1)] }, { coefficient := 1, powers := [(21, 1), (52, 1)] }, { coefficient := 1, powers := [(21, 1), (57, 1)] }, { coefficient := 1, powers := [(48, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (48, 1), (55, 1)] }, { coefficient := 1, powers := [(21, 1), (55, 1)] }, { coefficient := 1, powers := [(26, 1), (42, 1)] }, { coefficient := 1, powers := [(26, 1), (48, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (49, 1), (54, 1)] }, { coefficient := 1, powers := [(21, 1), (44, 1), (54, 1)] }, { coefficient := 1, powers := [(21, 1), (58, 1)] }, { coefficient := 1, powers := [(26, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (48, 1), (51, 1)] }, { coefficient := 1, powers := [(12, 1), (28, 1), (48, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (51, 1)] }, { coefficient := 1, powers := [(18, 1), (28, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (33, 1), (57, 1)] }, { coefficient := 1, powers := [(23, 1), (51, 1), (57, 1)] }, { coefficient := 1, powers := [(23, 1), (53, 1)] }, { coefficient := 1, powers := [(29, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (27, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (52, 1)] }, { coefficient := 1, powers := [(18, 1), (27, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (22, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (46, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(18, 1), (22, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (26, 1), (47, 1)] }, { coefficient := 1, powers := [(18, 1), (58, 1)] }, { coefficient := 1, powers := [(19, 1), (26, 1), (41, 1)] }, { coefficient := 1, powers := [(19, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (44, 1), (54, 1)] }, { coefficient := 1, powers := [(24, 1), (58, 1)] }, { coefficient := 1, powers := [(30, 1), (49, 1)] }, { coefficient := 1, powers := [(36, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (51, 1), (57, 1)] }, { coefficient := 1, powers := [(24, 1), (53, 1)] }, { coefficient := 1, powers := [(29, 1), (42, 1)] }, { coefficient := 1, powers := [(29, 1), (48, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (52, 1)] }, { coefficient := 1, powers := [(3, 1), (60, 1)] }, { coefficient := 1, powers := [(20, 1), (52, 1)] }, { coefficient := 1, powers := [(20, 1), (57, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(22, 1), (52, 1)] }, { coefficient := 1, powers := [(22, 1), (57, 1)] }, { coefficient := 1, powers := [(27, 1), (41, 1)] }, { coefficient := 1, powers := [(27, 1), (46, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1)] }, { coefficient := 1, powers := [(35, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (48, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (48, 1)] }, { coefficient := 1, powers := [(12, 1), (30, 1), (48, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (55, 1)] }, { coefficient := 1, powers := [(18, 1), (30, 1), (42, 1)] }, { coefficient := 1, powers := [(18, 1), (33, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (49, 1), (51, 1)] }, { coefficient := 1, powers := [(5, 1), (28, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1), (51, 1)] }, { coefficient := 1, powers := [(12, 1), (28, 1), (49, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (51, 1)] }, { coefficient := 1, powers := [(19, 1), (28, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (49, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1), (54, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (58, 1)] }, { coefficient := 1, powers := [(18, 1), (30, 1), (49, 1)] }, { coefficient := 1, powers := [(18, 1), (36, 1), (39, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (30, 1), (61, 1)] }, { coefficient := 1, powers := [(3, 1), (33, 1), (58, 1)] }, { coefficient := 1, powers := [(3, 1), (36, 1), (55, 1)] }, { coefficient := 1, powers := [(23, 1), (44, 1), (55, 1)] }, { coefficient := 1, powers := [(23, 1), (51, 1), (58, 1)] }, { coefficient := 1, powers := [(30, 1), (44, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (44, 1), (55, 1)] }, { coefficient := 1, powers := [(24, 1), (51, 1), (58, 1)] }, { coefficient := 1, powers := [(30, 1), (42, 1), (44, 1)] }, { coefficient := 1, powers := [(30, 1), (49, 1), (51, 1)] }, { coefficient := 1, powers := [(33, 1), (39, 1), (44, 1)] }, { coefficient := 1, powers := [(36, 1), (39, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (38, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (41, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(41, 1)] }, { coefficient := 1, powers := [(46, 1)] }, { coefficient := 1, powers := [(52, 1)] }, { coefficient := 1, powers := [(57, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (38, 1), (60, 1)] }, { coefficient := 1, powers := [(1, 1), (41, 1), (57, 1)] }, { coefficient := 1, powers := [(1, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(4, 1), (27, 1), (60, 1)] }, { coefficient := 1, powers := [(4, 1), (32, 1), (57, 1)] }, { coefficient := 1, powers := [(4, 1), (35, 1), (52, 1)] }, { coefficient := 1, powers := [(7, 1), (22, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (32, 1), (46, 1)] }, { coefficient := 1, powers := [(7, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(10, 1), (22, 1), (57, 1)] }, { coefficient := 1, powers := [(10, 1), (27, 1), (46, 1)] }, { coefficient := 1, powers := [(10, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(15, 1), (22, 1), (52, 1)] }, { coefficient := 1, powers := [(15, 1), (27, 1), (41, 1)] }, { coefficient := 1, powers := [(15, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (39, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (42, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (49, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (49, 1)] }, { coefficient := 1, powers := [(8, 1), (36, 1), (42, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (58, 1)] }, { coefficient := 1, powers := [(12, 1), (30, 1), (49, 1)] }, { coefficient := 1, powers := [(12, 1), (36, 1), (39, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (55, 1)] }, { coefficient := 1, powers := [(19, 1), (30, 1), (42, 1)] }, { coefficient := 1, powers := [(19, 1), (33, 1), (39, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1)] }],
  [{ coefficient := 1, powers := [(1, 1)] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(42, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(56, 1), (64, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(57, 1), (65, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(58, 1), (66, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 67 → SparsePoly (Fin 67) := ![
  [{ coefficient := -1, powers := [(4, 1), (28, 1), (54, 1), (57, 1), (61, 1)] }, { coefficient := 1, powers := [(4, 1), (30, 1), (57, 1), (61, 1)] }, { coefficient := 1, powers := [(4, 1), (33, 1), (57, 1), (58, 1)] }, { coefficient := 1, powers := [(4, 1), (36, 1), (55, 1), (57, 1)] }, { coefficient := 1, powers := [(7, 1), (28, 1), (46, 1), (54, 1), (61, 1)] }, { coefficient := 1, powers := [(7, 1), (28, 1), (52, 1), (54, 1), (61, 1)] }, { coefficient := 1, powers := [(7, 1), (28, 1), (54, 1), (57, 1), (61, 1)] }, { coefficient := -1, powers := [(7, 1), (30, 1), (46, 1), (61, 1)] }, { coefficient := -1, powers := [(7, 1), (30, 1), (52, 1), (61, 1)] }, { coefficient := -1, powers := [(7, 1), (30, 1), (57, 1), (61, 1)] }, { coefficient := -1, powers := [(7, 1), (33, 1), (46, 1), (58, 1)] }, { coefficient := -1, powers := [(7, 1), (33, 1), (52, 1), (58, 1)] }, { coefficient := -1, powers := [(7, 1), (33, 1), (57, 1), (58, 1)] }, { coefficient := -1, powers := [(7, 1), (36, 1), (46, 1), (55, 1)] }, { coefficient := -1, powers := [(7, 1), (36, 1), (52, 1), (55, 1)] }, { coefficient := -1, powers := [(7, 1), (36, 1), (55, 1), (57, 1)] }, { coefficient := -1, powers := [(10, 1), (28, 1), (38, 1), (54, 1), (61, 1)] }, { coefficient := 1, powers := [(10, 1), (30, 1), (38, 1), (61, 1)] }, { coefficient := 1, powers := [(10, 1), (33, 1), (38, 1), (58, 1)] }, { coefficient := 1, powers := [(10, 1), (36, 1), (38, 1), (55, 1)] }, { coefficient := 1, powers := [(15, 1), (28, 1), (38, 1), (54, 1), (61, 1)] }, { coefficient := -1, powers := [(15, 1), (30, 1), (38, 1), (61, 1)] }, { coefficient := -1, powers := [(15, 1), (33, 1), (38, 1), (58, 1)] }, { coefficient := -1, powers := [(15, 1), (36, 1), (38, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (24, 1), (57, 1), (61, 1)] }, { coefficient := 1, powers := [(4, 1), (33, 1), (49, 1), (57, 1)] }, { coefficient := 1, powers := [(4, 1), (36, 1), (42, 1), (57, 1)] }, { coefficient := -1, powers := [(7, 1), (24, 1), (46, 1), (61, 1)] }, { coefficient := -1, powers := [(7, 1), (24, 1), (52, 1), (61, 1)] }, { coefficient := -1, powers := [(7, 1), (24, 1), (57, 1), (61, 1)] }, { coefficient := -1, powers := [(7, 1), (33, 1), (46, 1), (49, 1)] }, { coefficient := -1, powers := [(7, 1), (33, 1), (49, 1), (52, 1)] }, { coefficient := -1, powers := [(7, 1), (33, 1), (49, 1), (57, 1)] }, { coefficient := -1, powers := [(7, 1), (36, 1), (42, 1), (46, 1)] }, { coefficient := -1, powers := [(7, 1), (36, 1), (42, 1), (52, 1)] }, { coefficient := -1, powers := [(7, 1), (36, 1), (42, 1), (57, 1)] }, { coefficient := -1, powers := [(10, 1), (24, 1), (38, 1), (61, 1)] }, { coefficient := -1, powers := [(10, 1), (33, 1), (38, 1), (49, 1)] }, { coefficient := -1, powers := [(10, 1), (36, 1), (38, 1), (42, 1)] }, { coefficient := 1, powers := [(15, 1), (24, 1), (38, 1), (61, 1)] }, { coefficient := 1, powers := [(15, 1), (33, 1), (38, 1), (49, 1)] }, { coefficient := 1, powers := [(15, 1), (36, 1), (38, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (10, 1), (28, 1), (44, 1), (54, 1), (57, 1), (61, 1), (66, 1)] }, { coefficient := -1, powers := [(5, 1), (10, 1), (30, 1), (44, 1), (57, 1), (61, 1), (66, 1)] }, { coefficient := -1, powers := [(5, 1), (10, 1), (33, 1), (44, 1), (57, 1), (58, 1), (66, 1)] }, { coefficient := -1, powers := [(5, 1), (10, 1), (36, 1), (44, 1), (55, 1), (57, 1), (66, 1)] }, { coefficient := -1, powers := [(7, 1), (18, 1), (24, 1), (61, 1)] }, { coefficient := -1, powers := [(7, 1), (18, 1), (33, 1), (49, 1)] }, { coefficient := -1, powers := [(7, 1), (18, 1), (36, 1), (42, 1)] }, { coefficient := 1, powers := [(8, 1), (10, 1), (24, 1), (44, 1), (52, 1), (61, 1), (66, 1)] }, { coefficient := 1, powers := [(8, 1), (10, 1), (33, 1), (44, 1), (49, 1), (52, 1), (66, 1)] }, { coefficient := 1, powers := [(8, 1), (10, 1), (36, 1), (42, 1), (44, 1), (52, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (8, 1), (24, 1), (51, 1), (60, 1), (61, 1), (63, 1)] }, { coefficient := -1, powers := [(4, 1), (8, 1), (33, 1), (49, 1), (51, 1), (60, 1), (63, 1)] }, { coefficient := -1, powers := [(4, 1), (8, 1), (36, 1), (42, 1), (51, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(4, 1), (18, 1), (28, 1), (54, 1), (61, 1)] }, { coefficient := -1, powers := [(4, 1), (18, 1), (30, 1), (61, 1)] }, { coefficient := -1, powers := [(4, 1), (18, 1), (33, 1), (58, 1)] }, { coefficient := -1, powers := [(4, 1), (18, 1), (36, 1), (55, 1)] }, { coefficient := -1, powers := [(5, 1), (15, 1), (28, 1), (46, 1), (51, 1), (54, 1), (61, 1), (63, 1)] }, { coefficient := 1, powers := [(5, 1), (15, 1), (30, 1), (46, 1), (51, 1), (61, 1), (63, 1)] }, { coefficient := 1, powers := [(5, 1), (15, 1), (33, 1), (46, 1), (51, 1), (58, 1), (63, 1)] }, { coefficient := 1, powers := [(5, 1), (15, 1), (36, 1), (46, 1), (51, 1), (55, 1), (63, 1)] }, { coefficient := 1, powers := [(8, 1), (15, 1), (24, 1), (46, 1), (51, 1), (61, 1), (63, 1)] }, { coefficient := 1, powers := [(8, 1), (15, 1), (24, 1), (51, 1), (52, 1), (61, 1), (63, 1)] }, { coefficient := 1, powers := [(8, 1), (15, 1), (24, 1), (51, 1), (57, 1), (61, 1), (63, 1)] }, { coefficient := 1, powers := [(8, 1), (15, 1), (33, 1), (46, 1), (49, 1), (51, 1), (63, 1)] }, { coefficient := 1, powers := [(8, 1), (15, 1), (33, 1), (49, 1), (51, 1), (52, 1), (63, 1)] }, { coefficient := 1, powers := [(8, 1), (15, 1), (33, 1), (49, 1), (51, 1), (57, 1), (63, 1)] }, { coefficient := 1, powers := [(8, 1), (15, 1), (36, 1), (42, 1), (46, 1), (51, 1), (63, 1)] }, { coefficient := 1, powers := [(8, 1), (15, 1), (36, 1), (42, 1), (51, 1), (52, 1), (63, 1)] }, { coefficient := 1, powers := [(8, 1), (15, 1), (36, 1), (42, 1), (51, 1), (57, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(30, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (49, 1), (51, 1), (54, 1)] }, { coefficient := -1, powers := [(29, 1), (49, 1), (55, 1)] }, { coefficient := 1, powers := [(30, 1), (44, 1), (48, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(18, 1), (21, 1), (55, 1), (58, 1), (66, 1)] }, { coefficient := 1, powers := [(18, 1), (48, 1), (55, 1), (58, 1), (65, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (21, 1), (47, 1), (58, 1), (66, 1)] }, { coefficient := -1, powers := [(18, 1), (44, 1), (48, 1)] }, { coefficient := -1, powers := [(18, 1), (47, 1), (48, 1), (58, 1), (65, 1), (66, 1)] }, { coefficient := -1, powers := [(19, 1), (48, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (8, 1), (24, 1), (60, 1), (61, 1), (63, 1)] }, { coefficient := 1, powers := [(4, 1), (8, 1), (33, 1), (49, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(4, 1), (8, 1), (36, 1), (42, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(5, 1), (15, 1), (28, 1), (46, 1), (54, 1), (61, 1), (63, 1)] }, { coefficient := -1, powers := [(5, 1), (15, 1), (30, 1), (46, 1), (61, 1), (63, 1)] }, { coefficient := -1, powers := [(5, 1), (15, 1), (33, 1), (46, 1), (58, 1), (63, 1)] }, { coefficient := -1, powers := [(5, 1), (15, 1), (36, 1), (46, 1), (55, 1), (63, 1)] }, { coefficient := -1, powers := [(8, 1), (15, 1), (24, 1), (46, 1), (61, 1), (63, 1)] }, { coefficient := -1, powers := [(8, 1), (15, 1), (24, 1), (52, 1), (61, 1), (63, 1)] }, { coefficient := -1, powers := [(8, 1), (15, 1), (24, 1), (57, 1), (61, 1), (63, 1)] }, { coefficient := -1, powers := [(8, 1), (15, 1), (33, 1), (46, 1), (49, 1), (63, 1)] }, { coefficient := -1, powers := [(8, 1), (15, 1), (33, 1), (49, 1), (52, 1), (63, 1)] }, { coefficient := -1, powers := [(8, 1), (15, 1), (33, 1), (49, 1), (57, 1), (63, 1)] }, { coefficient := -1, powers := [(8, 1), (15, 1), (36, 1), (42, 1), (46, 1), (63, 1)] }, { coefficient := -1, powers := [(8, 1), (15, 1), (36, 1), (42, 1), (52, 1), (63, 1)] }, { coefficient := -1, powers := [(8, 1), (15, 1), (36, 1), (42, 1), (57, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(18, 1), (21, 1), (58, 2), (66, 1)] }, { coefficient := 1, powers := [(18, 1), (21, 1), (58, 1)] }, { coefficient := -1, powers := [(18, 1), (43, 1), (48, 1), (58, 1), (64, 1), (65, 1)] }, { coefficient := 1, powers := [(18, 1), (48, 1), (58, 2), (65, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(30, 1), (44, 1), (48, 1)] }],
  [{ coefficient := -1, powers := [(18, 1), (48, 1), (58, 1), (64, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(30, 1), (48, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (10, 1), (28, 1), (54, 1), (57, 1), (61, 1), (66, 1)] }, { coefficient := 1, powers := [(5, 1), (10, 1), (30, 1), (57, 1), (61, 1), (66, 1)] }, { coefficient := 1, powers := [(5, 1), (10, 1), (33, 1), (57, 1), (58, 1), (66, 1)] }, { coefficient := 1, powers := [(5, 1), (10, 1), (36, 1), (55, 1), (57, 1), (66, 1)] }, { coefficient := -1, powers := [(8, 1), (10, 1), (24, 1), (52, 1), (61, 1), (66, 1)] }, { coefficient := -1, powers := [(8, 1), (10, 1), (33, 1), (49, 1), (52, 1), (66, 1)] }, { coefficient := -1, powers := [(8, 1), (10, 1), (36, 1), (42, 1), (52, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (30, 1), (48, 1), (57, 1)] }, { coefficient := 1, powers := [(18, 1), (30, 1), (48, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(18, 1), (29, 1), (51, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (29, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (28, 1), (54, 1), (57, 1), (61, 1)] }, { coefficient := -1, powers := [(5, 1), (30, 1), (57, 1), (61, 1)] }, { coefficient := -1, powers := [(5, 1), (33, 1), (57, 1), (58, 1)] }, { coefficient := -1, powers := [(5, 1), (36, 1), (55, 1), (57, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (52, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (49, 1), (52, 1)] }, { coefficient := 1, powers := [(8, 1), (36, 1), (42, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (28, 1), (46, 1), (54, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (46, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (46, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1), (46, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (46, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (52, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (57, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (46, 1), (49, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (49, 1), (52, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (49, 1), (57, 1)] }, { coefficient := 1, powers := [(8, 1), (36, 1), (42, 1), (46, 1)] }, { coefficient := 1, powers := [(8, 1), (36, 1), (42, 1), (52, 1)] }, { coefficient := 1, powers := [(8, 1), (36, 1), (42, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [(25, 1), (30, 1), (44, 1), (48, 1)] }, { coefficient := -1, powers := [(28, 1), (48, 1), (58, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (48, 1), (53, 1), (58, 1), (64, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(18, 1), (24, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(48, 1), (58, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(30, 1), (44, 1), (48, 1)] }],
  [{ coefficient := -1, powers := [(26, 1), (29, 1), (49, 1), (51, 1)] }],
  [{ coefficient := -1, powers := [(29, 1), (51, 1)] }],
  [{ coefficient := -1, powers := [(18, 1), (21, 1), (58, 1), (66, 1)] }, { coefficient := 1, powers := [(18, 1), (48, 1), (58, 1), (65, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(18, 1), (29, 1), (49, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(48, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(26, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(44, 1), (48, 1)] }],
  [{ coefficient := -1, powers := [(18, 1), (48, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (22, 1), (28, 1), (54, 1), (61, 1)] }, { coefficient := 1, powers := [(7, 1), (22, 1), (30, 1), (61, 1)] }, { coefficient := 1, powers := [(7, 1), (22, 1), (33, 1), (58, 1)] }, { coefficient := 1, powers := [(7, 1), (22, 1), (36, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(19, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (29, 1), (51, 1)] }],
  [{ coefficient := -1, powers := [(18, 1), (30, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (24, 1), (25, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (29, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (18, 1), (22, 1), (28, 1), (54, 1), (61, 1)] }, { coefficient := -1, powers := [(7, 1), (18, 1), (22, 1), (30, 1), (61, 1)] }, { coefficient := -1, powers := [(7, 1), (18, 1), (22, 1), (33, 1), (58, 1)] }, { coefficient := -1, powers := [(7, 1), (18, 1), (22, 1), (36, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(19, 1), (29, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (29, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(58, 1)] }],
  [{ coefficient := -1, powers := [(18, 1), (48, 1), (58, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (28, 1), (54, 1), (61, 1)] }, { coefficient := 1, powers := [(4, 1), (30, 1), (61, 1)] }, { coefficient := 1, powers := [(4, 1), (33, 1), (58, 1)] }, { coefficient := 1, powers := [(4, 1), (36, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (24, 1), (61, 1)] }, { coefficient := 1, powers := [(7, 1), (33, 1), (49, 1)] }, { coefficient := 1, powers := [(7, 1), (36, 1), (42, 1)] }],
  [{ coefficient := -1, powers := [(28, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(12, 1)] }],
  [{ coefficient := -1, powers := [(18, 1), (25, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (26, 1), (29, 1), (49, 1), (51, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (15, 1), (28, 1), (54, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (15, 1), (30, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (15, 1), (33, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (15, 1), (36, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (10, 1), (24, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (10, 1), (33, 1), (49, 1)] }, { coefficient := 1, powers := [(8, 1), (10, 1), (36, 1), (42, 1)] }],
  [{ coefficient := -1, powers := [(44, 1)] }],
  [{ coefficient := 1, powers := [(54, 1)] }],
  [{ coefficient := -1, powers := [(51, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(18, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (7, 1), (28, 1), (35, 1), (54, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (7, 1), (30, 1), (35, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (7, 1), (33, 1), (35, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (7, 1), (35, 1), (36, 1), (55, 1)] }, { coefficient := -1, powers := [(8, 1), (10, 1), (24, 1), (27, 1), (61, 1)] }, { coefficient := -1, powers := [(8, 1), (10, 1), (27, 1), (33, 1), (49, 1)] }, { coefficient := -1, powers := [(8, 1), (10, 1), (27, 1), (36, 1), (42, 1)] }, { coefficient := 1, powers := [(8, 1), (15, 1), (24, 1), (27, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (15, 1), (27, 1), (33, 1), (49, 1)] }, { coefficient := 1, powers := [(8, 1), (15, 1), (27, 1), (36, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (28, 1), (54, 1), (61, 1)] }, { coefficient := -1, powers := [(5, 1), (30, 1), (61, 1)] }, { coefficient := -1, powers := [(5, 1), (33, 1), (58, 1)] }, { coefficient := -1, powers := [(5, 1), (36, 1), (55, 1)] }, { coefficient := -1, powers := [(8, 1), (24, 1), (61, 1)] }, { coefficient := -1, powers := [(8, 1), (33, 1), (49, 1)] }, { coefficient := -1, powers := [(8, 1), (36, 1), (42, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(5, 1), (7, 1), (28, 1), (35, 1), (38, 1), (54, 1), (60, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (7, 1), (28, 1), (35, 1), (41, 1), (54, 1), (57, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (7, 1), (28, 1), (35, 1), (46, 1), (52, 1), (54, 1), (61, 1)] }, { coefficient := -1, powers := [(5, 1), (7, 1), (30, 1), (35, 1), (38, 1), (60, 1), (61, 1)] }, { coefficient := -1, powers := [(5, 1), (7, 1), (30, 1), (35, 1), (41, 1), (57, 1), (61, 1)] }, { coefficient := -1, powers := [(5, 1), (7, 1), (30, 1), (35, 1), (46, 1), (52, 1), (61, 1)] }, { coefficient := -1, powers := [(5, 1), (7, 1), (33, 1), (35, 1), (38, 1), (58, 1), (60, 1)] }, { coefficient := -1, powers := [(5, 1), (7, 1), (33, 1), (35, 1), (41, 1), (57, 1), (58, 1)] }, { coefficient := -1, powers := [(5, 1), (7, 1), (33, 1), (35, 1), (46, 1), (52, 1), (58, 1)] }, { coefficient := -1, powers := [(5, 1), (7, 1), (35, 1), (36, 1), (38, 1), (55, 1), (60, 1)] }, { coefficient := -1, powers := [(5, 1), (7, 1), (35, 1), (36, 1), (41, 1), (55, 1), (57, 1)] }, { coefficient := -1, powers := [(5, 1), (7, 1), (35, 1), (36, 1), (46, 1), (52, 1), (55, 1)] }, { coefficient := -1, powers := [(7, 1), (18, 1), (22, 1), (28, 1), (48, 1), (52, 1), (54, 1), (61, 1)] }, { coefficient := 1, powers := [(7, 1), (18, 1), (22, 1), (30, 1), (48, 1), (52, 1), (61, 1)] }, { coefficient := 1, powers := [(7, 1), (18, 1), (22, 1), (33, 1), (48, 1), (52, 1), (58, 1)] }, { coefficient := 1, powers := [(7, 1), (18, 1), (22, 1), (36, 1), (48, 1), (52, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (10, 1), (24, 1), (27, 1), (38, 1), (60, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (10, 1), (24, 1), (27, 1), (41, 1), (57, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (10, 1), (24, 1), (27, 1), (46, 1), (52, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (10, 1), (27, 1), (33, 1), (38, 1), (49, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (10, 1), (27, 1), (33, 1), (41, 1), (49, 1), (57, 1)] }, { coefficient := 1, powers := [(8, 1), (10, 1), (27, 1), (33, 1), (46, 1), (49, 1), (52, 1)] }, { coefficient := 1, powers := [(8, 1), (10, 1), (27, 1), (36, 1), (38, 1), (42, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (10, 1), (27, 1), (36, 1), (41, 1), (42, 1), (57, 1)] }, { coefficient := 1, powers := [(8, 1), (10, 1), (27, 1), (36, 1), (42, 1), (46, 1), (52, 1)] }, { coefficient := -1, powers := [(8, 1), (15, 1), (24, 1), (27, 1), (38, 1), (60, 1), (61, 1)] }, { coefficient := -1, powers := [(8, 1), (15, 1), (24, 1), (27, 1), (41, 1), (57, 1), (61, 1)] }, { coefficient := -1, powers := [(8, 1), (15, 1), (24, 1), (27, 1), (46, 1), (52, 1), (61, 1)] }, { coefficient := -1, powers := [(8, 1), (15, 1), (27, 1), (33, 1), (38, 1), (49, 1), (60, 1)] }, { coefficient := -1, powers := [(8, 1), (15, 1), (27, 1), (33, 1), (41, 1), (49, 1), (57, 1)] }, { coefficient := -1, powers := [(8, 1), (15, 1), (27, 1), (33, 1), (46, 1), (49, 1), (52, 1)] }, { coefficient := -1, powers := [(8, 1), (15, 1), (27, 1), (36, 1), (38, 1), (42, 1), (60, 1)] }, { coefficient := -1, powers := [(8, 1), (15, 1), (27, 1), (36, 1), (41, 1), (42, 1), (57, 1)] }, { coefficient := -1, powers := [(8, 1), (15, 1), (27, 1), (36, 1), (42, 1), (46, 1), (52, 1)] }, { coefficient := -1, powers := [(12, 1), (30, 1), (44, 1), (48, 1), (57, 1)] }, { coefficient := -1, powers := [(18, 1), (24, 1), (25, 1), (46, 1), (53, 1), (58, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (46, 1), (51, 1), (58, 1)] }, { coefficient := -1, powers := [(18, 1), (26, 1), (29, 1), (49, 1), (51, 1), (52, 1)] }, { coefficient := -1, powers := [(18, 1), (29, 1), (48, 1), (51, 1), (58, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (49, 1), (51, 1), (54, 1)] }, { coefficient := -1, powers := [(18, 1), (29, 1), (49, 1), (55, 1)] }, { coefficient := -1, powers := [(19, 1), (29, 1), (39, 1), (51, 1), (60, 1)] }, { coefficient := -1, powers := [(19, 1), (29, 1), (48, 1), (51, 1), (54, 1)] }, { coefficient := 1, powers := [(19, 1), (29, 1), (48, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (28, 1), (38, 1), (54, 1), (60, 1), (61, 1)] }, { coefficient := -1, powers := [(5, 1), (28, 1), (41, 1), (54, 1), (57, 1), (61, 1)] }, { coefficient := -1, powers := [(5, 1), (28, 1), (46, 1), (54, 1), (57, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (38, 1), (60, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (41, 1), (57, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (46, 1), (57, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (38, 1), (58, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (41, 1), (57, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (46, 1), (57, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1), (38, 1), (55, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1), (41, 1), (55, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1), (46, 1), (55, 1), (57, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (38, 1), (60, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (41, 1), (57, 1), (61, 1)] }, { coefficient := -1, powers := [(8, 1), (24, 1), (46, 1), (52, 1), (61, 1)] }, { coefficient := -1, powers := [(8, 1), (24, 1), (52, 2), (61, 1)] }, { coefficient := -1, powers := [(8, 1), (24, 1), (52, 1), (57, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (38, 1), (49, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (41, 1), (49, 1), (57, 1)] }, { coefficient := -1, powers := [(8, 1), (33, 1), (46, 1), (49, 1), (52, 1)] }, { coefficient := -1, powers := [(8, 1), (33, 1), (49, 1), (52, 2)] }, { coefficient := -1, powers := [(8, 1), (33, 1), (49, 1), (52, 1), (57, 1)] }, { coefficient := 1, powers := [(8, 1), (36, 1), (38, 1), (42, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (36, 1), (41, 1), (42, 1), (57, 1)] }, { coefficient := -1, powers := [(8, 1), (36, 1), (42, 1), (46, 1), (52, 1)] }, { coefficient := -1, powers := [(8, 1), (36, 1), (42, 1), (52, 2)] }, { coefficient := -1, powers := [(8, 1), (36, 1), (42, 1), (52, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [(26, 1), (42, 1), (47, 1)] }, { coefficient := 1, powers := [(39, 1), (61, 1)] }, { coefficient := 1, powers := [(42, 1), (58, 1)] }, { coefficient := -1, powers := [(44, 1), (48, 1), (55, 1)] }, { coefficient := -1, powers := [(46, 1), (48, 1), (51, 1), (58, 1), (65, 1)] }, { coefficient := -1, powers := [(48, 1), (51, 1), (58, 1)] }, { coefficient := 1, powers := [(49, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (8, 1), (24, 1), (27, 1), (60, 1), (61, 1)] }, { coefficient := -1, powers := [(4, 1), (8, 1), (27, 1), (33, 1), (49, 1), (60, 1)] }, { coefficient := -1, powers := [(4, 1), (8, 1), (27, 1), (36, 1), (42, 1), (60, 1)] }, { coefficient := -1, powers := [(5, 1), (15, 1), (27, 1), (28, 1), (46, 1), (54, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (15, 1), (27, 1), (30, 1), (46, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (15, 1), (27, 1), (33, 1), (46, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (15, 1), (27, 1), (36, 1), (46, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (15, 1), (24, 1), (27, 1), (46, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (15, 1), (24, 1), (27, 1), (52, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (15, 1), (24, 1), (27, 1), (57, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (15, 1), (27, 1), (33, 1), (46, 1), (49, 1)] }, { coefficient := 1, powers := [(8, 1), (15, 1), (27, 1), (33, 1), (49, 1), (52, 1)] }, { coefficient := 1, powers := [(8, 1), (15, 1), (27, 1), (33, 1), (49, 1), (57, 1)] }, { coefficient := 1, powers := [(8, 1), (15, 1), (27, 1), (36, 1), (42, 1), (46, 1)] }, { coefficient := 1, powers := [(8, 1), (15, 1), (27, 1), (36, 1), (42, 1), (52, 1)] }, { coefficient := 1, powers := [(8, 1), (15, 1), (27, 1), (36, 1), (42, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [(18, 1), (23, 1), (48, 1), (53, 1), (58, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (18, 1), (33, 1), (48, 1), (58, 1)] }, { coefficient := 1, powers := [(12, 1), (28, 1), (48, 1), (58, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (48, 1), (51, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (10, 1), (22, 1), (28, 1), (54, 1), (57, 1), (61, 1)] }, { coefficient := -1, powers := [(5, 1), (10, 1), (22, 1), (30, 1), (57, 1), (61, 1)] }, { coefficient := -1, powers := [(5, 1), (10, 1), (22, 1), (33, 1), (57, 1), (58, 1)] }, { coefficient := -1, powers := [(5, 1), (10, 1), (22, 1), (36, 1), (55, 1), (57, 1)] }, { coefficient := 1, powers := [(8, 1), (10, 1), (22, 1), (24, 1), (52, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (10, 1), (22, 1), (33, 1), (49, 1), (52, 1)] }, { coefficient := 1, powers := [(8, 1), (10, 1), (22, 1), (36, 1), (42, 1), (52, 1)] }, { coefficient := 1, powers := [(18, 1), (21, 1), (28, 1), (53, 1), (58, 1)] }, { coefficient := -1, powers := [(18, 1), (28, 1), (48, 1), (53, 1), (58, 1), (65, 1)] }]
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
    (values : Fin 67 → R) :
    ¬ ∀ index : Fin 67,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component37.SelectedLeafB0_3_7.selectedHasNoCommonZero

end Krenn.Component37.SelectedLeafB0_3_7
