import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component37.SelectedLeafB4_3_7

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "c94b95494b158df8f21986f05d80fe0d574394cb2909170501cd6dd18056a216"
def certificateSHA256 : String := "2e1eca0958f485dc6b0cc3fddf3ac91430f8b3023bb10940771d3c8f9b53b2cf"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 26 → Fin 667 := ![
  5,
  7,
  14,
  15,
  23,
  27,
  181,
  182,
  283,
  298,
  299,
  454,
  519,
  542,
  566,
  604,
  605,
  623,
  626,
  642,
  656,
  657,
  659,
  660,
  663,
  666
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 26 → SparsePoly (Fin 68) := ![
  [{ coefficient := 1, powers := [(5, 1), (35, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (32, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (22, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (27, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (54, 1)] }, { coefficient := 1, powers := [(30, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (42, 1)] }, { coefficient := 1, powers := [(27, 1), (48, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (44, 1), (54, 1)] }, { coefficient := 1, powers := [(22, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (46, 1)] }, { coefficient := 1, powers := [(4, 1), (35, 1)] }, { coefficient := 1, powers := [(15, 1), (22, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (52, 1)] }, { coefficient := 1, powers := [(7, 1), (32, 1)] }, { coefficient := 1, powers := [(10, 1), (27, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (55, 1)] }, { coefficient := 1, powers := [(30, 1), (42, 1)] }, { coefficient := 1, powers := [(30, 1), (48, 1), (51, 1)] }, { coefficient := 1, powers := [(33, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (27, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (52, 1)] }, { coefficient := 1, powers := [(18, 1), (27, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (22, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (46, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(18, 1), (22, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (44, 1), (54, 1)] }, { coefficient := 1, powers := [(24, 1), (58, 1)] }, { coefficient := 1, powers := [(30, 1), (49, 1)] }, { coefficient := 1, powers := [(36, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (60, 1)] }, { coefficient := 1, powers := [(10, 1), (46, 1)] }, { coefficient := 1, powers := [(10, 1), (57, 1)] }, { coefficient := 1, powers := [(15, 1), (41, 1)] }, { coefficient := 1, powers := [(15, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (52, 1)] }, { coefficient := 1, powers := [(22, 1), (57, 1)] }, { coefficient := 1, powers := [(27, 1), (41, 1)] }, { coefficient := 1, powers := [(27, 1), (46, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1)] }, { coefficient := 1, powers := [(35, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (48, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (48, 1)] }, { coefficient := 1, powers := [(12, 1), (30, 1), (48, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (55, 1)] }, { coefficient := 1, powers := [(18, 1), (30, 1), (42, 1)] }, { coefficient := 1, powers := [(18, 1), (33, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (49, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1), (54, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (58, 1)] }, { coefficient := 1, powers := [(18, 1), (30, 1), (49, 1)] }, { coefficient := 1, powers := [(18, 1), (36, 1), (39, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (44, 1), (55, 1)] }, { coefficient := 1, powers := [(24, 1), (51, 1), (58, 1)] }, { coefficient := 1, powers := [(30, 1), (42, 1), (44, 1)] }, { coefficient := 1, powers := [(30, 1), (49, 1), (51, 1)] }, { coefficient := 1, powers := [(33, 1), (39, 1), (44, 1)] }, { coefficient := 1, powers := [(36, 1), (39, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (38, 1), (60, 1)] }, { coefficient := 1, powers := [(1, 1), (41, 1), (57, 1)] }, { coefficient := 1, powers := [(1, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(4, 1), (27, 1), (60, 1)] }, { coefficient := 1, powers := [(4, 1), (32, 1), (57, 1)] }, { coefficient := 1, powers := [(4, 1), (35, 1), (52, 1)] }, { coefficient := 1, powers := [(7, 1), (22, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (32, 1), (46, 1)] }, { coefficient := 1, powers := [(7, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(10, 1), (22, 1), (57, 1)] }, { coefficient := 1, powers := [(10, 1), (27, 1), (46, 1)] }, { coefficient := 1, powers := [(10, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(15, 1), (22, 1), (52, 1)] }, { coefficient := 1, powers := [(15, 1), (27, 1), (41, 1)] }, { coefficient := 1, powers := [(15, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (39, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (42, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (49, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (49, 1)] }, { coefficient := 1, powers := [(8, 1), (36, 1), (42, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (58, 1)] }, { coefficient := 1, powers := [(12, 1), (30, 1), (49, 1)] }, { coefficient := 1, powers := [(12, 1), (36, 1), (39, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (55, 1)] }, { coefficient := 1, powers := [(19, 1), (30, 1), (42, 1)] }, { coefficient := 1, powers := [(19, 1), (33, 1), (39, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1)] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(42, 1), (64, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(58, 1), (67, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 26 → SparsePoly (Fin 68) := ![
  [{ coefficient := 1, powers := [(4, 1), (30, 1), (41, 1), (61, 1)] }, { coefficient := 1, powers := [(4, 1), (30, 1), (52, 1), (61, 1)] }, { coefficient := 1, powers := [(4, 1), (30, 1), (57, 1), (61, 1)] }, { coefficient := 1, powers := [(4, 1), (33, 1), (41, 1), (58, 1)] }, { coefficient := 1, powers := [(4, 1), (33, 1), (52, 1), (58, 1)] }, { coefficient := 1, powers := [(4, 1), (33, 1), (57, 1), (58, 1)] }, { coefficient := -1, powers := [(4, 1), (36, 1), (41, 1), (51, 1), (54, 1)] }, { coefficient := 1, powers := [(4, 1), (36, 1), (41, 1), (55, 1)] }, { coefficient := -1, powers := [(4, 1), (36, 1), (51, 1), (52, 1), (54, 1)] }, { coefficient := -1, powers := [(4, 1), (36, 1), (51, 1), (54, 1), (57, 1)] }, { coefficient := 1, powers := [(4, 1), (36, 1), (52, 1), (55, 1)] }, { coefficient := 1, powers := [(4, 1), (36, 1), (55, 1), (57, 1)] }, { coefficient := 1, powers := [(7, 1), (30, 1), (41, 1), (61, 1)] }, { coefficient := 1, powers := [(7, 1), (33, 1), (41, 1), (58, 1)] }, { coefficient := -1, powers := [(7, 1), (36, 1), (41, 1), (51, 1), (54, 1)] }, { coefficient := 1, powers := [(7, 1), (36, 1), (41, 1), (55, 1)] }, { coefficient := 1, powers := [(10, 1), (30, 1), (38, 1), (61, 1)] }, { coefficient := 1, powers := [(10, 1), (33, 1), (38, 1), (58, 1)] }, { coefficient := -1, powers := [(10, 1), (36, 1), (38, 1), (51, 1), (54, 1)] }, { coefficient := 1, powers := [(10, 1), (36, 1), (38, 1), (55, 1)] }, { coefficient := -1, powers := [(15, 1), (30, 1), (38, 1), (61, 1)] }, { coefficient := -1, powers := [(15, 1), (33, 1), (38, 1), (58, 1)] }, { coefficient := 1, powers := [(15, 1), (36, 1), (38, 1), (51, 1), (54, 1)] }, { coefficient := -1, powers := [(15, 1), (36, 1), (38, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (24, 1), (57, 1), (61, 1)] }, { coefficient := -1, powers := [(4, 1), (33, 1), (44, 1), (48, 1), (57, 1)] }, { coefficient := 1, powers := [(4, 1), (33, 1), (49, 1), (57, 1)] }, { coefficient := 1, powers := [(4, 1), (36, 1), (42, 1), (57, 1)] }, { coefficient := 1, powers := [(7, 1), (24, 1), (41, 1), (61, 1)] }, { coefficient := -1, powers := [(7, 1), (33, 1), (41, 1), (44, 1), (48, 1)] }, { coefficient := 1, powers := [(7, 1), (33, 1), (41, 1), (49, 1)] }, { coefficient := 1, powers := [(7, 1), (36, 1), (41, 1), (42, 1)] }, { coefficient := -1, powers := [(10, 1), (24, 1), (38, 1), (61, 1)] }, { coefficient := 1, powers := [(10, 1), (33, 1), (38, 1), (44, 1), (48, 1)] }, { coefficient := -1, powers := [(10, 1), (33, 1), (38, 1), (49, 1)] }, { coefficient := -1, powers := [(10, 1), (36, 1), (38, 1), (42, 1)] }, { coefficient := 1, powers := [(15, 1), (24, 1), (38, 1), (61, 1)] }, { coefficient := -1, powers := [(15, 1), (33, 1), (38, 1), (44, 1), (48, 1)] }, { coefficient := 1, powers := [(15, 1), (33, 1), (38, 1), (49, 1)] }, { coefficient := 1, powers := [(15, 1), (36, 1), (38, 1), (42, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (24, 1), (54, 1), (61, 1)] }, { coefficient := 1, powers := [(7, 1), (33, 1), (44, 1), (48, 1), (54, 1)] }, { coefficient := -1, powers := [(7, 1), (33, 1), (49, 1), (54, 1)] }, { coefficient := -1, powers := [(7, 1), (36, 1), (42, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (30, 1), (48, 1), (61, 1)] }, { coefficient := -1, powers := [(4, 1), (33, 1), (48, 1), (58, 1)] }, { coefficient := 1, powers := [(4, 1), (36, 1), (48, 1), (51, 1), (54, 1)] }, { coefficient := -1, powers := [(4, 1), (36, 1), (48, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (5, 1), (30, 1), (44, 1), (60, 1), (61, 1), (67, 1)] }, { coefficient := 1, powers := [(4, 1), (5, 1), (33, 1), (44, 1), (58, 1), (60, 1), (67, 1)] }, { coefficient := -1, powers := [(4, 1), (5, 1), (36, 1), (44, 1), (51, 1), (54, 1), (60, 1), (67, 1)] }, { coefficient := 1, powers := [(4, 1), (5, 1), (36, 1), (44, 1), (55, 1), (60, 1), (67, 1)] }, { coefficient := 1, powers := [(5, 1), (10, 1), (30, 1), (44, 1), (46, 1), (61, 1), (67, 1)] }, { coefficient := 1, powers := [(5, 1), (10, 1), (33, 1), (44, 1), (46, 1), (58, 1), (67, 1)] }, { coefficient := -1, powers := [(5, 1), (10, 1), (36, 1), (44, 1), (46, 1), (51, 1), (54, 1), (67, 1)] }, { coefficient := 1, powers := [(5, 1), (10, 1), (36, 1), (44, 1), (46, 1), (55, 1), (67, 1)] }, { coefficient := 1, powers := [(8, 1), (10, 1), (24, 1), (44, 1), (52, 1), (61, 1), (67, 1)] }, { coefficient := -1, powers := [(8, 1), (10, 1), (33, 1), (44, 2), (48, 1), (52, 1), (67, 1)] }, { coefficient := 1, powers := [(8, 1), (10, 1), (33, 1), (44, 1), (49, 1), (52, 1), (67, 1)] }, { coefficient := 1, powers := [(8, 1), (10, 1), (36, 1), (42, 1), (44, 1), (52, 1), (67, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (8, 1), (24, 1), (51, 1), (60, 1), (61, 1), (64, 1)] }, { coefficient := 1, powers := [(4, 1), (8, 1), (33, 1), (44, 1), (48, 1), (51, 1), (60, 1), (64, 1)] }, { coefficient := -1, powers := [(4, 1), (8, 1), (33, 1), (49, 1), (51, 1), (60, 1), (64, 1)] }, { coefficient := -1, powers := [(4, 1), (8, 1), (36, 1), (42, 1), (51, 1), (60, 1), (64, 1)] }, { coefficient := 1, powers := [(5, 1), (15, 1), (30, 1), (46, 1), (51, 1), (61, 1), (64, 1)] }, { coefficient := 1, powers := [(5, 1), (15, 1), (33, 1), (46, 1), (51, 1), (58, 1), (64, 1)] }, { coefficient := -1, powers := [(5, 1), (15, 1), (36, 1), (46, 1), (51, 2), (54, 1), (64, 1)] }, { coefficient := 1, powers := [(5, 1), (15, 1), (36, 1), (46, 1), (51, 1), (55, 1), (64, 1)] }, { coefficient := -1, powers := [(8, 1), (15, 1), (24, 1), (41, 1), (51, 1), (61, 1), (64, 1)] }, { coefficient := 1, powers := [(8, 1), (15, 1), (33, 1), (41, 1), (44, 1), (48, 1), (51, 1), (64, 1)] }, { coefficient := -1, powers := [(8, 1), (15, 1), (33, 1), (41, 1), (49, 1), (51, 1), (64, 1)] }, { coefficient := -1, powers := [(8, 1), (15, 1), (36, 1), (41, 1), (42, 1), (51, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (44, 1)] }, { coefficient := -1, powers := [(19, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (8, 1), (24, 1), (60, 1), (61, 1), (64, 1)] }, { coefficient := -1, powers := [(4, 1), (8, 1), (33, 1), (44, 1), (48, 1), (60, 1), (64, 1)] }, { coefficient := 1, powers := [(4, 1), (8, 1), (33, 1), (49, 1), (60, 1), (64, 1)] }, { coefficient := 1, powers := [(4, 1), (8, 1), (36, 1), (42, 1), (60, 1), (64, 1)] }, { coefficient := -1, powers := [(5, 1), (15, 1), (30, 1), (46, 1), (61, 1), (64, 1)] }, { coefficient := -1, powers := [(5, 1), (15, 1), (33, 1), (46, 1), (58, 1), (64, 1)] }, { coefficient := 1, powers := [(5, 1), (15, 1), (36, 1), (46, 1), (51, 1), (54, 1), (64, 1)] }, { coefficient := -1, powers := [(5, 1), (15, 1), (36, 1), (46, 1), (55, 1), (64, 1)] }, { coefficient := 1, powers := [(8, 1), (15, 1), (24, 1), (41, 1), (61, 1), (64, 1)] }, { coefficient := -1, powers := [(8, 1), (15, 1), (33, 1), (41, 1), (44, 1), (48, 1), (64, 1)] }, { coefficient := 1, powers := [(8, 1), (15, 1), (33, 1), (41, 1), (49, 1), (64, 1)] }, { coefficient := 1, powers := [(8, 1), (15, 1), (36, 1), (41, 1), (42, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (5, 1), (30, 1), (60, 1), (61, 1), (67, 1)] }, { coefficient := -1, powers := [(4, 1), (5, 1), (33, 1), (58, 1), (60, 1), (67, 1)] }, { coefficient := 1, powers := [(4, 1), (5, 1), (36, 1), (51, 1), (54, 1), (60, 1), (67, 1)] }, { coefficient := -1, powers := [(4, 1), (5, 1), (36, 1), (55, 1), (60, 1), (67, 1)] }, { coefficient := -1, powers := [(5, 1), (10, 1), (30, 1), (46, 1), (61, 1), (67, 1)] }, { coefficient := -1, powers := [(5, 1), (10, 1), (33, 1), (46, 1), (58, 1), (67, 1)] }, { coefficient := 1, powers := [(5, 1), (10, 1), (36, 1), (46, 1), (51, 1), (54, 1), (67, 1)] }, { coefficient := -1, powers := [(5, 1), (10, 1), (36, 1), (46, 1), (55, 1), (67, 1)] }, { coefficient := -1, powers := [(8, 1), (10, 1), (24, 1), (52, 1), (61, 1), (67, 1)] }, { coefficient := 1, powers := [(8, 1), (10, 1), (33, 1), (44, 1), (48, 1), (52, 1), (67, 1)] }, { coefficient := -1, powers := [(8, 1), (10, 1), (33, 1), (49, 1), (52, 1), (67, 1)] }, { coefficient := -1, powers := [(8, 1), (10, 1), (36, 1), (42, 1), (52, 1), (67, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (30, 1), (41, 1), (61, 1)] }, { coefficient := -1, powers := [(5, 1), (30, 1), (52, 1), (61, 1)] }, { coefficient := -1, powers := [(5, 1), (30, 1), (57, 1), (61, 1)] }, { coefficient := -1, powers := [(5, 1), (33, 1), (41, 1), (58, 1)] }, { coefficient := -1, powers := [(5, 1), (33, 1), (52, 1), (58, 1)] }, { coefficient := -1, powers := [(5, 1), (33, 1), (57, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1), (41, 1), (51, 1), (54, 1)] }, { coefficient := -1, powers := [(5, 1), (36, 1), (41, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1), (51, 1), (52, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1), (51, 1), (54, 1), (57, 1)] }, { coefficient := -1, powers := [(5, 1), (36, 1), (52, 1), (55, 1)] }, { coefficient := -1, powers := [(5, 1), (36, 1), (55, 1), (57, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (52, 1), (61, 1)] }, { coefficient := -1, powers := [(8, 1), (33, 1), (44, 1), (48, 1), (52, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (49, 1), (52, 1)] }, { coefficient := 1, powers := [(8, 1), (36, 1), (42, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (30, 1), (46, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (46, 1), (58, 1)] }, { coefficient := -1, powers := [(5, 1), (36, 1), (46, 1), (51, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1), (46, 1), (55, 1)] }, { coefficient := -1, powers := [(8, 1), (24, 1), (41, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (41, 1), (44, 1), (48, 1)] }, { coefficient := -1, powers := [(8, 1), (33, 1), (41, 1), (49, 1)] }, { coefficient := -1, powers := [(8, 1), (36, 1), (41, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(19, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (30, 1), (61, 1)] }, { coefficient := 1, powers := [(4, 1), (33, 1), (58, 1)] }, { coefficient := -1, powers := [(4, 1), (36, 1), (51, 1), (54, 1)] }, { coefficient := 1, powers := [(4, 1), (36, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (24, 1), (61, 1)] }, { coefficient := -1, powers := [(7, 1), (33, 1), (44, 1), (48, 1)] }, { coefficient := 1, powers := [(7, 1), (33, 1), (49, 1)] }, { coefficient := 1, powers := [(7, 1), (36, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(12, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (22, 1), (30, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (22, 1), (33, 1), (58, 1)] }, { coefficient := -1, powers := [(5, 1), (22, 1), (36, 1), (51, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (22, 1), (36, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (15, 1), (30, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (15, 1), (33, 1), (58, 1)] }, { coefficient := -1, powers := [(5, 1), (15, 1), (36, 1), (51, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (15, 1), (36, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (10, 1), (24, 1), (61, 1)] }, { coefficient := -1, powers := [(8, 1), (10, 1), (33, 1), (44, 1), (48, 1)] }, { coefficient := 1, powers := [(8, 1), (10, 1), (33, 1), (49, 1)] }, { coefficient := 1, powers := [(8, 1), (10, 1), (36, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(44, 1)] }],
  [{ coefficient := 1, powers := [(51, 1)] }],
  [{ coefficient := -1, powers := [(18, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (30, 1), (61, 1)] }, { coefficient := -1, powers := [(5, 1), (33, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1), (51, 1), (54, 1)] }, { coefficient := -1, powers := [(5, 1), (36, 1), (55, 1)] }, { coefficient := -1, powers := [(8, 1), (24, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (44, 1), (48, 1)] }, { coefficient := -1, powers := [(8, 1), (33, 1), (49, 1)] }, { coefficient := -1, powers := [(8, 1), (36, 1), (42, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(5, 1), (30, 1), (38, 1), (60, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (41, 1), (46, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (41, 1), (57, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (46, 1), (52, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (46, 1), (57, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (38, 1), (58, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (41, 1), (46, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (41, 1), (57, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (46, 1), (52, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (46, 1), (57, 1), (58, 1)] }, { coefficient := -1, powers := [(5, 1), (36, 1), (38, 1), (51, 1), (54, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1), (38, 1), (55, 1), (60, 1)] }, { coefficient := -1, powers := [(5, 1), (36, 1), (41, 1), (46, 1), (51, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1), (41, 1), (46, 1), (55, 1)] }, { coefficient := -1, powers := [(5, 1), (36, 1), (41, 1), (51, 1), (54, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1), (41, 1), (55, 1), (57, 1)] }, { coefficient := -1, powers := [(5, 1), (36, 1), (46, 1), (51, 1), (52, 1), (54, 1)] }, { coefficient := -1, powers := [(5, 1), (36, 1), (46, 1), (51, 1), (54, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1), (46, 1), (52, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1), (46, 1), (55, 1), (57, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (38, 1), (60, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (41, 1), (52, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (41, 1), (57, 1), (61, 1)] }, { coefficient := -1, powers := [(8, 1), (33, 1), (38, 1), (44, 1), (48, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (38, 1), (49, 1), (60, 1)] }, { coefficient := -1, powers := [(8, 1), (33, 1), (41, 1), (44, 1), (48, 1), (52, 1)] }, { coefficient := -1, powers := [(8, 1), (33, 1), (41, 1), (44, 1), (48, 1), (57, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (41, 1), (49, 1), (52, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (41, 1), (49, 1), (57, 1)] }, { coefficient := 1, powers := [(8, 1), (36, 1), (38, 1), (42, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (36, 1), (41, 1), (42, 1), (52, 1)] }, { coefficient := 1, powers := [(8, 1), (36, 1), (41, 1), (42, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(39, 1), (61, 1)] }, { coefficient := 1, powers := [(42, 1), (58, 1)] }, { coefficient := -1, powers := [(44, 1), (48, 1), (55, 1)] }, { coefficient := -1, powers := [(49, 1), (51, 1), (54, 1)] }, { coefficient := 1, powers := [(49, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (8, 1), (24, 1), (27, 1), (60, 1), (61, 1)] }, { coefficient := 1, powers := [(4, 1), (8, 1), (27, 1), (33, 1), (44, 1), (48, 1), (60, 1)] }, { coefficient := -1, powers := [(4, 1), (8, 1), (27, 1), (33, 1), (49, 1), (60, 1)] }, { coefficient := -1, powers := [(4, 1), (8, 1), (27, 1), (36, 1), (42, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (15, 1), (27, 1), (30, 1), (46, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (15, 1), (27, 1), (33, 1), (46, 1), (58, 1)] }, { coefficient := -1, powers := [(5, 1), (15, 1), (27, 1), (36, 1), (46, 1), (51, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (15, 1), (27, 1), (36, 1), (46, 1), (55, 1)] }, { coefficient := -1, powers := [(8, 1), (15, 1), (24, 1), (27, 1), (41, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (15, 1), (27, 1), (33, 1), (41, 1), (44, 1), (48, 1)] }, { coefficient := -1, powers := [(8, 1), (15, 1), (27, 1), (33, 1), (41, 1), (49, 1)] }, { coefficient := -1, powers := [(8, 1), (15, 1), (27, 1), (36, 1), (41, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (5, 1), (22, 1), (30, 1), (60, 1), (61, 1)] }, { coefficient := 1, powers := [(4, 1), (5, 1), (22, 1), (33, 1), (58, 1), (60, 1)] }, { coefficient := -1, powers := [(4, 1), (5, 1), (22, 1), (36, 1), (51, 1), (54, 1), (60, 1)] }, { coefficient := 1, powers := [(4, 1), (5, 1), (22, 1), (36, 1), (55, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (10, 1), (22, 1), (30, 1), (46, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (10, 1), (22, 1), (33, 1), (46, 1), (58, 1)] }, { coefficient := -1, powers := [(5, 1), (10, 1), (22, 1), (36, 1), (46, 1), (51, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (10, 1), (22, 1), (36, 1), (46, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (10, 1), (22, 1), (24, 1), (52, 1), (61, 1)] }, { coefficient := -1, powers := [(8, 1), (10, 1), (22, 1), (33, 1), (44, 1), (48, 1), (52, 1)] }, { coefficient := 1, powers := [(8, 1), (10, 1), (22, 1), (33, 1), (49, 1), (52, 1)] }, { coefficient := 1, powers := [(8, 1), (10, 1), (22, 1), (36, 1), (42, 1), (52, 1)] }]
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
    (values : Fin 68 → R) :
    ¬ ∀ index : Fin 26,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component37.SelectedLeafB4_3_7.selectedHasNoCommonZero

end Krenn.Component37.SelectedLeafB4_3_7
