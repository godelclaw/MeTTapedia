import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component37.SelectedLeafB0_0_0

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "3a30dd06c834c5f407af285ff14ae21721375e9729e8c7b4c3ea3b5dabf55e93"
def certificateSHA256 : String := "a22aa4917c82d7c4e404c761001246626696a885db4a53457f9f6c5c89319101"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 67 → Fin 667 := ![
  5,
  9,
  14,
  17,
  22,
  27,
  170,
  171,
  175,
  178,
  179,
  180,
  181,
  183,
  184,
  256,
  280,
  285,
  295,
  298,
  299,
  301,
  307,
  310,
  311,
  312,
  316,
  317,
  393,
  406,
  411,
  424,
  426,
  438,
  445,
  446,
  450,
  454,
  471,
  475,
  479,
  482,
  483,
  497,
  519,
  556,
  566,
  570,
  583,
  602,
  603,
  604,
  605,
  612,
  645,
  655,
  656,
  657,
  658,
  659,
  660,
  661,
  662,
  663,
  664,
  665,
  666
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 67 → SparsePoly (Fin 62) := ![
  [{ coefficient := 1, powers := [(5, 1), (35, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (27, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (22, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (44, 1)] }, { coefficient := 1, powers := [(19, 1), (20, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (20, 1)] }, { coefficient := 1, powers := [(18, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (47, 1)] }, { coefficient := -1, powers := [(29, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (55, 1)] }, { coefficient := 1, powers := [(30, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (44, 1)] }, { coefficient := 1, powers := [(28, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (54, 1)] }, { coefficient := 1, powers := [(30, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(28, 1), (53, 1)] }, { coefficient := -1, powers := [(29, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (55, 1)] }, { coefficient := 1, powers := [(30, 1), (46, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (25, 1), (46, 1)] }, { coefficient := 1, powers := [(18, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (25, 1), (49, 1)] }, { coefficient := 1, powers := [(19, 1), (21, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(29, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (49, 1)] }, { coefficient := 1, powers := [(21, 1), (44, 1)] }, { coefficient := 1, powers := [(25, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (46, 1)] }, { coefficient := 1, powers := [(4, 1), (35, 1)] }, { coefficient := 1, powers := [(15, 1), (22, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (52, 1)] }, { coefficient := 1, powers := [(7, 1), (32, 1)] }, { coefficient := 1, powers := [(10, 1), (27, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (59, 1)] }, { coefficient := 1, powers := [(9, 1), (43, 1)] }, { coefficient := 1, powers := [(13, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (46, 1)] }, { coefficient := 1, powers := [(12, 1), (57, 1)] }, { coefficient := 1, powers := [(18, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (41, 1)] }, { coefficient := 1, powers := [(19, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (52, 1)] }, { coefficient := 1, powers := [(24, 1), (57, 1)] }, { coefficient := 1, powers := [(29, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (54, 1)] }, { coefficient := 1, powers := [(30, 1), (41, 1)] }, { coefficient := 1, powers := [(30, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1), (55, 1)] }, { coefficient := 1, powers := [(26, 1), (46, 1), (51, 1)] }, { coefficient := 1, powers := [(55, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (49, 1), (52, 1)] }, { coefficient := 1, powers := [(21, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(49, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (20, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1)] }, { coefficient := 1, powers := [(18, 1), (20, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (20, 1), (50, 1)] }, { coefficient := 1, powers := [(18, 1), (25, 1), (40, 1)] }, { coefficient := 1, powers := [(18, 1), (31, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (25, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (25, 1), (41, 1)] }, { coefficient := 1, powers := [(19, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1)] }, { coefficient := 1, powers := [(25, 1), (41, 1), (44, 1)] }, { coefficient := 1, powers := [(25, 1), (47, 1)] }, { coefficient := 1, powers := [(44, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (53, 1)] }, { coefficient := 1, powers := [(20, 1), (51, 1), (57, 1)] }, { coefficient := 1, powers := [(20, 1), (53, 1)] }, { coefficient := 1, powers := [(51, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1)] }, { coefficient := 1, powers := [(12, 1), (30, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (60, 1)] }, { coefficient := 1, powers := [(18, 1), (21, 1), (52, 1)] }, { coefficient := 1, powers := [(18, 1), (21, 1), (57, 1)] }, { coefficient := 1, powers := [(18, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (61, 1)] }, { coefficient := 1, powers := [(12, 1), (49, 1)] }, { coefficient := 1, powers := [(19, 1), (21, 1), (53, 1)] }, { coefficient := 1, powers := [(19, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (61, 1)] }, { coefficient := 1, powers := [(12, 1), (26, 1), (47, 1)] }, { coefficient := 1, powers := [(12, 1), (58, 1)] }, { coefficient := 1, powers := [(19, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (55, 1)] }, { coefficient := 1, powers := [(30, 1), (42, 1)] }, { coefficient := 1, powers := [(30, 1), (48, 1), (51, 1)] }, { coefficient := 1, powers := [(33, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1), (53, 1)] }, { coefficient := 1, powers := [(46, 1), (51, 1)] }, { coefficient := 1, powers := [(51, 1), (57, 1)] }, { coefficient := 1, powers := [(53, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1), (52, 1)] }, { coefficient := 1, powers := [(41, 1), (44, 1)] }, { coefficient := 1, powers := [(44, 1), (52, 1)] }, { coefficient := 1, powers := [(47, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (48, 1), (52, 1)] }, { coefficient := 1, powers := [(21, 1), (52, 1)] }, { coefficient := 1, powers := [(21, 1), (57, 1)] }, { coefficient := 1, powers := [(48, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (49, 1), (53, 1)] }, { coefficient := 1, powers := [(21, 1), (44, 1), (53, 1)] }, { coefficient := 1, powers := [(42, 1), (44, 1)] }, { coefficient := 1, powers := [(49, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (49, 1), (54, 1)] }, { coefficient := 1, powers := [(21, 1), (44, 1), (54, 1)] }, { coefficient := 1, powers := [(21, 1), (58, 1)] }, { coefficient := 1, powers := [(26, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (49, 1), (52, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1), (52, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (49, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (27, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (52, 1)] }, { coefficient := 1, powers := [(18, 1), (27, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (22, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1), (27, 1), (46, 1)] }, { coefficient := 1, powers := [(12, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(18, 1), (22, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (44, 1), (54, 1)] }, { coefficient := 1, powers := [(24, 1), (58, 1)] }, { coefficient := 1, powers := [(30, 1), (49, 1)] }, { coefficient := 1, powers := [(36, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (44, 1), (54, 1)] }, { coefficient := 1, powers := [(29, 1), (58, 1)] }, { coefficient := 1, powers := [(30, 1), (41, 1), (44, 1)] }, { coefficient := 1, powers := [(30, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (31, 1), (57, 1)] }, { coefficient := 1, powers := [(9, 1), (20, 1), (57, 1)] }, { coefficient := 1, powers := [(9, 1)] }, { coefficient := 1, powers := [(40, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1)] }, { coefficient := 1, powers := [(3, 1), (34, 1)] }, { coefficient := 1, powers := [(13, 1), (20, 1)] }, { coefficient := 1, powers := [(20, 1), (56, 1)] }, { coefficient := 1, powers := [(25, 1), (43, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (50, 1)] }, { coefficient := 1, powers := [(6, 1), (31, 1)] }, { coefficient := 1, powers := [(9, 1), (25, 1)] }, { coefficient := 1, powers := [(20, 1), (50, 1)] }, { coefficient := 1, powers := [(25, 1), (40, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (60, 1)] }, { coefficient := 1, powers := [(10, 1), (46, 1)] }, { coefficient := 1, powers := [(10, 1), (57, 1)] }, { coefficient := 1, powers := [(15, 1), (41, 1)] }, { coefficient := 1, powers := [(15, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (52, 1)] }, { coefficient := 1, powers := [(22, 1), (57, 1)] }, { coefficient := 1, powers := [(27, 1), (41, 1)] }, { coefficient := 1, powers := [(27, 1), (46, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1)] }, { coefficient := 1, powers := [(35, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1), (50, 1)] }, { coefficient := 1, powers := [(6, 1), (31, 1), (45, 1)] }, { coefficient := 1, powers := [(6, 1), (59, 1)] }, { coefficient := 1, powers := [(9, 1), (25, 1), (45, 1)] }, { coefficient := 1, powers := [(9, 1), (56, 1)] }, { coefficient := 1, powers := [(13, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (38, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (41, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(41, 1)] }, { coefficient := 1, powers := [(46, 1)] }, { coefficient := 1, powers := [(52, 1)] }, { coefficient := 1, powers := [(57, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (37, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (40, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (43, 1), (50, 1)] }, { coefficient := 1, powers := [(3, 1), (25, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (31, 1), (56, 1)] }, { coefficient := 1, powers := [(3, 1), (34, 1), (50, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (31, 1), (43, 1)] }, { coefficient := 1, powers := [(6, 1), (34, 1), (40, 1)] }, { coefficient := 1, powers := [(9, 1), (20, 1), (56, 1)] }, { coefficient := 1, powers := [(9, 1), (25, 1), (43, 1)] }, { coefficient := 1, powers := [(9, 1), (34, 1), (37, 1)] }, { coefficient := 1, powers := [(13, 1), (20, 1), (50, 1)] }, { coefficient := 1, powers := [(13, 1), (25, 1), (40, 1)] }, { coefficient := 1, powers := [(13, 1), (31, 1), (37, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1), (38, 1), (60, 1)] }, { coefficient := 1, powers := [(1, 1), (41, 1), (57, 1)] }, { coefficient := 1, powers := [(1, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(4, 1), (27, 1), (60, 1)] }, { coefficient := 1, powers := [(4, 1), (32, 1), (57, 1)] }, { coefficient := 1, powers := [(4, 1), (35, 1), (52, 1)] }, { coefficient := 1, powers := [(7, 1), (22, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (32, 1), (46, 1)] }, { coefficient := 1, powers := [(7, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(10, 1), (22, 1), (57, 1)] }, { coefficient := 1, powers := [(10, 1), (27, 1), (46, 1)] }, { coefficient := 1, powers := [(10, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(15, 1), (22, 1), (52, 1)] }, { coefficient := 1, powers := [(15, 1), (27, 1), (41, 1)] }, { coefficient := 1, powers := [(15, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (39, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (42, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (49, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (49, 1)] }, { coefficient := 1, powers := [(8, 1), (36, 1), (42, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (58, 1)] }, { coefficient := 1, powers := [(12, 1), (30, 1), (49, 1)] }, { coefficient := 1, powers := [(12, 1), (36, 1), (39, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (55, 1)] }, { coefficient := 1, powers := [(19, 1), (30, 1), (42, 1)] }, { coefficient := 1, powers := [(19, 1), (33, 1), (39, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1)] }],
  [{ coefficient := 1, powers := [(1, 1)] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(40, 1)] }],
  [{ coefficient := 1, powers := [(41, 1)] }],
  [{ coefficient := 1, powers := [(42, 1)] }],
  [{ coefficient := 1, powers := [(56, 1)] }],
  [{ coefficient := 1, powers := [(57, 1)] }],
  [{ coefficient := 1, powers := [(58, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 67 → SparsePoly (Fin 62) := ![
  [{ coefficient := 1, powers := [(4, 1), (36, 1), (52, 1), (55, 1)] }, { coefficient := 1, powers := [(7, 1), (36, 1), (52, 1), (55, 1)] }, { coefficient := 1, powers := [(10, 1), (36, 1), (38, 1), (55, 1)] }, { coefficient := -1, powers := [(15, 1), (36, 1), (38, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (30, 1), (49, 1), (60, 1)] }, { coefficient := 2, powers := [(10, 1), (30, 1), (49, 1), (52, 1)] }, { coefficient := -1, powers := [(15, 1), (30, 1), (49, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(10, 1), (30, 1), (49, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(13, 1), (20, 1), (24, 1), (44, 1), (55, 1)] }, { coefficient := 1, powers := [(13, 1), (24, 1), (25, 1), (44, 1), (55, 1)] }, { coefficient := -1, powers := [(24, 1), (25, 1), (43, 1), (44, 1), (55, 1)] }, { coefficient := -1, powers := [(24, 1), (34, 1), (37, 1), (44, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (18, 1), (30, 1), (49, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (18, 1), (36, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(24, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (10, 1), (24, 1), (26, 1), (27, 1), (36, 1), (52, 1), (55, 1)] }, { coefficient := -2, powers := [(24, 1), (26, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (10, 1), (27, 1), (29, 1), (36, 1), (49, 1), (53, 1), (54, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (10, 1), (27, 1), (30, 1), (36, 1), (49, 1), (52, 1), (53, 1), (55, 1)] }, { coefficient := 1, powers := [(6, 1), (24, 1), (44, 1), (55, 1), (59, 1)] }, { coefficient := -1, powers := [(7, 1), (22, 1), (30, 1), (49, 1), (53, 1), (60, 1)] }, { coefficient := 2, powers := [(30, 1), (49, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (10, 1), (18, 1), (27, 1), (36, 1), (48, 1), (55, 2)] }],
  [{ coefficient := 1, powers := [(5, 1), (10, 1), (18, 1), (27, 1), (36, 1), (47, 1), (48, 1), (55, 1)] }, { coefficient := -1, powers := [(5, 1), (10, 1), (18, 1), (27, 1), (36, 1), (49, 1), (52, 1), (55, 1)] }, { coefficient := -1, powers := [(18, 1), (49, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (10, 1), (18, 1), (27, 1), (36, 1), (53, 1), (54, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(19, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (10, 1), (18, 1), (27, 1), (36, 1), (49, 1), (54, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (10, 1), (18, 1), (27, 1), (36, 1), (49, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (10, 1), (27, 1), (29, 1), (36, 1), (49, 1), (54, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (10, 1), (27, 1), (30, 1), (36, 1), (49, 1), (52, 1), (55, 1)] }, { coefficient := -1, powers := [(7, 1), (22, 1), (30, 1), (49, 1), (60, 1)] }, { coefficient := 2, powers := [(30, 1), (49, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (10, 1), (27, 1), (29, 1), (36, 1), (53, 1), (54, 1), (55, 1)] }, { coefficient := -1, powers := [(30, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (26, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (10, 1), (18, 1), (27, 1), (29, 1), (36, 1), (53, 1), (54, 1), (55, 1)] }, { coefficient := 1, powers := [(18, 1), (30, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (30, 1), (49, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (36, 1), (46, 1), (55, 1)] }, { coefficient := 1, powers := [(12, 1), (30, 1), (46, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (24, 1), (25, 1), (44, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (10, 1), (25, 1), (27, 1), (29, 1), (36, 1), (49, 1), (54, 1), (55, 1)] }, { coefficient := -1, powers := [(5, 1), (10, 1), (25, 1), (27, 1), (30, 1), (36, 1), (49, 1), (52, 1), (55, 1)] }, { coefficient := -1, powers := [(5, 1), (10, 1), (27, 1), (30, 1), (36, 1), (49, 1), (55, 1)] }, { coefficient := -1, powers := [(5, 1), (10, 1), (27, 1), (36, 2), (39, 1), (55, 1)] }, { coefficient := 1, powers := [(7, 1), (22, 1), (25, 1), (30, 1), (49, 1), (60, 1)] }, { coefficient := 1, powers := [(15, 1), (22, 1), (30, 1), (49, 1)] }, { coefficient := -2, powers := [(25, 1), (30, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (10, 1), (27, 1), (33, 1), (36, 1), (39, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (10, 1), (18, 1), (27, 1), (36, 1), (44, 1), (55, 2)] }],
  [{ coefficient := -1, powers := [(5, 2), (10, 1), (27, 1), (36, 1), (55, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (10, 1), (18, 1), (27, 1), (36, 1), (49, 1), (51, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (10, 1), (19, 1), (24, 1), (27, 1), (36, 1), (52, 1), (55, 1)] }, { coefficient := -2, powers := [(19, 1), (24, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (30, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (10, 1), (27, 1), (29, 1), (36, 1), (49, 1), (54, 1), (55, 1)] }, { coefficient := -1, powers := [(5, 1), (10, 1), (27, 1), (30, 1), (36, 1), (49, 1), (52, 1), (55, 1)] }, { coefficient := 1, powers := [(7, 1), (22, 1), (30, 1), (49, 1), (60, 1)] }, { coefficient := -2, powers := [(30, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (24, 1), (44, 1), (55, 1)] }, { coefficient := -1, powers := [(24, 1), (25, 1), (44, 1), (45, 1), (55, 1)] }, { coefficient := -1, powers := [(24, 1), (43, 1), (44, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(18, 1), (24, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (24, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (10, 1), (27, 1), (36, 1), (49, 1), (52, 1), (55, 1)] }, { coefficient := 1, powers := [(49, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (22, 1), (36, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (10, 1), (27, 1), (29, 1), (36, 1), (54, 1), (55, 1)] }, { coefficient := 1, powers := [(30, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (10, 1), (24, 1), (27, 1), (36, 1), (52, 1), (55, 1)] }, { coefficient := 1, powers := [(24, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (10, 1), (18, 1), (27, 1), (36, 1), (47, 1), (55, 1)] }, { coefficient := 1, powers := [(19, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (10, 1), (19, 1), (24, 1), (26, 1), (27, 1), (36, 1), (52, 1), (55, 1)] }, { coefficient := 2, powers := [(19, 1), (24, 1), (26, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (10, 1), (18, 1), (24, 1), (27, 1), (36, 1), (55, 2)] }, { coefficient := 1, powers := [(12, 1), (21, 1), (30, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (26, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (18, 1), (22, 1), (36, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (10, 1), (18, 1), (27, 1), (29, 1), (36, 1), (54, 1), (55, 1)] }, { coefficient := -1, powers := [(18, 1), (30, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (29, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (10, 1), (27, 1), (36, 1), (55, 2)] }],
  [{ coefficient := -1, powers := [(7, 1), (36, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (30, 1), (49, 1)] }, { coefficient := -1, powers := [(15, 1), (30, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (10, 1), (18, 1), (27, 1), (36, 1), (53, 1), (55, 1)] }, { coefficient := 1, powers := [(12, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (21, 1)] }],
  [{ coefficient := -1, powers := [(18, 1), (24, 1), (25, 1), (43, 1), (44, 1), (55, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (34, 1), (37, 1), (44, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (24, 1), (44, 1), (50, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (24, 1), (25, 1), (44, 1), (45, 1), (55, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (43, 1), (44, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (27, 1), (36, 1), (55, 1)] }, { coefficient := 1, powers := [(12, 1), (27, 1), (30, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (15, 1), (36, 1), (55, 1)] }, { coefficient := 1, powers := [(12, 1), (15, 1), (30, 1), (49, 1)] }],
  [{ coefficient := -1, powers := [(18, 1), (24, 1), (25, 1), (44, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(5, 2), (10, 1), (27, 1), (30, 1), (36, 1), (55, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (10, 1), (12, 1), (27, 1), (30, 1), (36, 1), (49, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (10, 1), (12, 1), (27, 1), (36, 2), (39, 1), (55, 1)] }, { coefficient := -1, powers := [(5, 1), (10, 1), (27, 1), (36, 1), (55, 1)] }, { coefficient := -1, powers := [(5, 1), (15, 1), (27, 1), (36, 1), (55, 1)] }, { coefficient := -2, powers := [(10, 1), (12, 1), (27, 1), (30, 1), (49, 1)] }, { coefficient := -1, powers := [(12, 1), (15, 1), (22, 1), (30, 1), (49, 1)] }],
  [{ coefficient := -1, powers := [(18, 1), (24, 1), (44, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (36, 1), (55, 1)] }, { coefficient := -1, powers := [(12, 1), (30, 1), (49, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (10, 1), (27, 1), (36, 1), (52, 1), (55, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(5, 2), (10, 1), (27, 1), (30, 1), (36, 1), (38, 1), (55, 1), (60, 1), (61, 1)] }, { coefficient := -1, powers := [(5, 2), (10, 1), (27, 1), (30, 1), (36, 1), (46, 1), (52, 1), (55, 1), (61, 1)] }, { coefficient := -1, powers := [(5, 1), (10, 1), (12, 1), (27, 1), (30, 1), (36, 1), (38, 1), (49, 1), (55, 1), (60, 1)] }, { coefficient := -1, powers := [(5, 1), (10, 1), (12, 1), (27, 1), (30, 1), (36, 1), (46, 1), (49, 1), (52, 1), (55, 1)] }, { coefficient := -1, powers := [(5, 1), (10, 1), (12, 1), (27, 1), (36, 2), (38, 1), (39, 1), (55, 1), (60, 1)] }, { coefficient := -1, powers := [(5, 1), (10, 1), (12, 1), (27, 1), (36, 2), (39, 1), (46, 1), (52, 1), (55, 1)] }, { coefficient := -1, powers := [(5, 1), (10, 1), (18, 1), (24, 1), (27, 1), (36, 1), (47, 1), (52, 1), (55, 2)] }, { coefficient := -1, powers := [(5, 1), (10, 1), (19, 1), (24, 1), (26, 1), (27, 1), (36, 1), (46, 1), (52, 1), (53, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (10, 1), (19, 1), (24, 1), (27, 1), (36, 1), (46, 1), (52, 1), (55, 2)] }, { coefficient := 1, powers := [(5, 1), (10, 1), (27, 1), (36, 1), (38, 1), (55, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (10, 1), (27, 1), (36, 1), (46, 1), (52, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (15, 1), (27, 1), (36, 1), (38, 1), (55, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (15, 1), (27, 1), (36, 1), (46, 1), (52, 1), (55, 1)] }, { coefficient := 1, powers := [(7, 1), (18, 1), (22, 1), (36, 1), (48, 1), (52, 1), (55, 1)] }, { coefficient := 2, powers := [(10, 1), (12, 1), (27, 1), (30, 1), (38, 1), (49, 1), (60, 1)] }, { coefficient := 2, powers := [(10, 1), (12, 1), (27, 1), (30, 1), (46, 1), (49, 1), (52, 1)] }, { coefficient := 1, powers := [(12, 1), (15, 1), (22, 1), (30, 1), (38, 1), (49, 1), (60, 1)] }, { coefficient := 1, powers := [(12, 1), (15, 1), (22, 1), (30, 1), (46, 1), (49, 1), (52, 1)] }, { coefficient := -1, powers := [(12, 1), (21, 1), (30, 1), (47, 1), (52, 1)] }, { coefficient := -1, powers := [(12, 1), (24, 1), (26, 1), (47, 1), (52, 1)] }, { coefficient := -1, powers := [(12, 1), (29, 1), (49, 1), (54, 1)] }, { coefficient := 1, powers := [(12, 1), (30, 1), (49, 1), (52, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (37, 1), (44, 1), (55, 1), (59, 1)] }, { coefficient := -1, powers := [(18, 1), (24, 1), (43, 1), (44, 1), (50, 1), (55, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (47, 1), (55, 1)] }, { coefficient := -2, powers := [(19, 1), (24, 1), (26, 1), (46, 1), (53, 1)] }, { coefficient := 2, powers := [(19, 1), (24, 1), (46, 1), (55, 1)] }, { coefficient := -1, powers := [(19, 1), (24, 1), (53, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (36, 1), (38, 1), (55, 1), (60, 1)] }, { coefficient := 1, powers := [(12, 1), (30, 1), (38, 1), (49, 1), (60, 1)] }, { coefficient := -1, powers := [(12, 1), (30, 1), (46, 1), (49, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (10, 1), (27, 1), (36, 1), (39, 1), (52, 1), (55, 1), (61, 1)] }, { coefficient := -1, powers := [(5, 1), (10, 1), (27, 1), (36, 1), (49, 1), (52, 1), (55, 2)] }, { coefficient := 1, powers := [(39, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (18, 1), (24, 1), (25, 1), (43, 1), (44, 1), (55, 1), (57, 1)] }, { coefficient := -1, powers := [(0, 1), (18, 1), (24, 1), (34, 1), (37, 1), (44, 1), (55, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (18, 1), (24, 1), (44, 1), (55, 1), (56, 1)] }, { coefficient := 1, powers := [(6, 1), (18, 1), (24, 1), (34, 1), (44, 1), (55, 1)] }, { coefficient := -1, powers := [(13, 1), (18, 1), (24, 1), (25, 1), (44, 1), (55, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (25, 1), (43, 1), (44, 1), (55, 1)] }, { coefficient := -1, powers := [(18, 1), (24, 1), (34, 1), (37, 1), (44, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (5, 2), (10, 1), (27, 1), (30, 1), (36, 1), (55, 1), (57, 1), (61, 1)] }, { coefficient := -1, powers := [(0, 1), (5, 1), (10, 1), (12, 1), (27, 1), (30, 1), (36, 1), (49, 1), (55, 1), (57, 1)] }, { coefficient := -1, powers := [(0, 1), (5, 1), (10, 1), (12, 1), (27, 1), (36, 2), (39, 1), (55, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (5, 1), (10, 1), (27, 1), (36, 1), (55, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (5, 1), (15, 1), (27, 1), (36, 1), (55, 1), (57, 1)] }, { coefficient := 2, powers := [(0, 1), (10, 1), (12, 1), (27, 1), (30, 1), (49, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (12, 1), (15, 1), (22, 1), (30, 1), (49, 1), (57, 1)] }, { coefficient := 1, powers := [(1, 1), (5, 1), (36, 1), (55, 1), (57, 1)] }, { coefficient := 1, powers := [(1, 1), (12, 1), (30, 1), (49, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (7, 1), (35, 1), (36, 1), (55, 1)] }, { coefficient := -1, powers := [(5, 1), (10, 1), (12, 1), (27, 1), (30, 1), (36, 1), (49, 1), (55, 1)] }, { coefficient := -1, powers := [(5, 1), (10, 1), (12, 1), (27, 1), (36, 2), (39, 1), (55, 1)] }, { coefficient := -1, powers := [(5, 1), (10, 1), (18, 1), (24, 1), (27, 1), (36, 1), (44, 1), (55, 2)] }, { coefficient := -1, powers := [(5, 1), (10, 1), (18, 1), (27, 1), (30, 1), (36, 1), (49, 1), (51, 1), (55, 1)] }, { coefficient := -1, powers := [(5, 1), (10, 1), (19, 1), (27, 1), (33, 1), (36, 1), (39, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (10, 1), (27, 1), (36, 1), (55, 1)] }, { coefficient := 1, powers := [(7, 1), (12, 1), (30, 1), (35, 1), (49, 1)] }, { coefficient := 2, powers := [(10, 1), (12, 1), (27, 1), (30, 1), (49, 1)] }, { coefficient := 1, powers := [(12, 1), (15, 1), (22, 1), (30, 1), (49, 1)] }, { coefficient := -1, powers := [(12, 1), (15, 1), (27, 1), (30, 1), (49, 1)] }, { coefficient := -1, powers := [(12, 1), (24, 1), (26, 1), (44, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (25, 1), (44, 1), (55, 1)] }, { coefficient := -1, powers := [(19, 1), (24, 1), (25, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (5, 1), (10, 1), (27, 1), (36, 1), (52, 1), (55, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (8, 1), (10, 1), (27, 1), (36, 2), (52, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (10, 1), (18, 1), (27, 1), (29, 1), (36, 1), (44, 1), (54, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (10, 1), (18, 1), (27, 1), (30, 1), (36, 1), (47, 1), (55, 1)] }, { coefficient := -1, powers := [(5, 1), (10, 1), (19, 1), (27, 1), (29, 1), (36, 1), (54, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (10, 1), (19, 1), (27, 1), (30, 1), (36, 1), (52, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (36, 1)] }, { coefficient := 1, powers := [(18, 1), (30, 1), (44, 1)] }, { coefficient := -1, powers := [(19, 1), (30, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (18, 1), (24, 1), (31, 1), (44, 1), (55, 1)] }, { coefficient := 1, powers := [(9, 1), (18, 1), (20, 1), (24, 1), (44, 1), (55, 1)] }, { coefficient := 1, powers := [(9, 1), (18, 1), (24, 1), (25, 1), (44, 1), (55, 1)] }, { coefficient := -1, powers := [(18, 1), (20, 1), (24, 1), (44, 1), (50, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (18, 1), (24, 1), (25, 1), (31, 1), (43, 1), (44, 1), (55, 1)] }, { coefficient := -1, powers := [(3, 1), (18, 1), (24, 1), (31, 1), (34, 1), (37, 1), (44, 1), (55, 1)] }, { coefficient := 1, powers := [(4, 1), (5, 1), (32, 1), (36, 1), (55, 1)] }, { coefficient := 1, powers := [(4, 1), (12, 1), (30, 1), (32, 1), (49, 1)] }, { coefficient := -1, powers := [(5, 2), (10, 1), (27, 1), (30, 1), (36, 1), (55, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (7, 1), (32, 1), (36, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (10, 1), (12, 1), (20, 1), (27, 1), (29, 1), (36, 1), (49, 1), (54, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (10, 1), (12, 1), (20, 1), (27, 1), (30, 1), (36, 1), (49, 1), (52, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (10, 1), (12, 1), (25, 1), (27, 1), (29, 1), (36, 1), (49, 1), (54, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (10, 1), (12, 1), (25, 1), (27, 1), (30, 1), (36, 1), (49, 1), (52, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (10, 1), (18, 1), (24, 1), (27, 1), (36, 1), (44, 1), (55, 2)] }, { coefficient := -1, powers := [(5, 1), (10, 1), (19, 1), (24, 1), (26, 1), (27, 1), (36, 1), (51, 1), (52, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (10, 1), (22, 1), (36, 1), (55, 1)] }, { coefficient := -1, powers := [(5, 1), (15, 1), (22, 1), (36, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (15, 1), (27, 1), (36, 1), (55, 1)] }, { coefficient := -1, powers := [(7, 1), (12, 1), (20, 1), (22, 1), (30, 1), (49, 1), (60, 1)] }, { coefficient := -1, powers := [(7, 1), (12, 1), (22, 1), (25, 1), (30, 1), (49, 1), (60, 1)] }, { coefficient := 1, powers := [(9, 1), (18, 1), (20, 1), (24, 1), (25, 1), (43, 1), (44, 1), (55, 1)] }, { coefficient := -1, powers := [(9, 1), (18, 1), (20, 1), (24, 1), (34, 1), (37, 1), (44, 1), (55, 1)] }, { coefficient := 1, powers := [(10, 1), (12, 1), (27, 1), (30, 1), (49, 1)] }, { coefficient := 2, powers := [(12, 1), (20, 1), (30, 1), (49, 1)] }, { coefficient := 2, powers := [(12, 1), (25, 1), (30, 1), (49, 1)] }, { coefficient := -1, powers := [(19, 1), (20, 1), (24, 1), (51, 1), (54, 1)] }, { coefficient := -2, powers := [(19, 1), (24, 1), (26, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(5, 2), (10, 1), (27, 1), (33, 1), (36, 1), (52, 1), (55, 1)] }, { coefficient := -1, powers := [(5, 1), (10, 1), (18, 1), (24, 1), (27, 1), (36, 1), (53, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1)] }, { coefficient := -1, powers := [(12, 1), (24, 1)] }]
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
    ¬ ∀ index : Fin 67,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component37.SelectedLeafB0_0_0.selectedHasNoCommonZero

end Krenn.Component37.SelectedLeafB0_0_0
