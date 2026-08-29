import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component37.SelectedLeafB0_7

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "17ecbabf37f6de1e0191d4650cd4be48e078cdd86468966e9f313bbd608c07c5"
def certificateSHA256 : String := "b9caa10483871844b956cd05a09f90ca7766cde1f599cd47a9efff302fc5c8ad"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 47 → Fin 664 := ![
  5,
  7,
  8,
  14,
  16,
  19,
  23,
  27,
  147,
  151,
  154,
  161,
  171,
  179,
  180,
  182,
  185,
  234,
  247,
  283,
  298,
  299,
  315,
  335,
  359,
  362,
  433,
  438,
  446,
  449,
  450,
  471,
  542,
  566,
  590,
  604,
  605,
  609,
  645,
  656,
  657,
  658,
  659,
  660,
  661,
  662,
  663
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 47 → SparsePoly (Fin 65) := ![
  [{ coefficient := 1, powers := [(5, 1), (35, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (32, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (22, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (31, 1)] }, { coefficient := 1, powers := [(15, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (30, 1)] }, { coefficient := 1, powers := [(30, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (25, 1)] }, { coefficient := 1, powers := [(15, 1), (20, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (25, 1)] }, { coefficient := 1, powers := [(15, 1), (20, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (55, 1)] }, { coefficient := 1, powers := [(30, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (44, 1)] }, { coefficient := 1, powers := [(28, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (42, 1)] }, { coefficient := 1, powers := [(27, 1), (48, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(32, 1), (39, 1)] }, { coefficient := 1, powers := [(35, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (25, 1), (48, 1)] }, { coefficient := 1, powers := [(15, 1), (21, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (25, 1), (46, 1)] }, { coefficient := 1, powers := [(15, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (44, 1), (54, 1)] }, { coefficient := 1, powers := [(22, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (46, 1)] }, { coefficient := 1, powers := [(4, 1), (35, 1)] }, { coefficient := 1, powers := [(15, 1), (22, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (52, 1)] }, { coefficient := 1, powers := [(7, 1), (32, 1)] }, { coefficient := 1, powers := [(10, 1), (27, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1), (51, 1)] }, { coefficient := 1, powers := [(25, 1), (46, 1), (51, 1)] }, { coefficient := 1, powers := [(51, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (40, 1), (58, 1)] }, { coefficient := 1, powers := [(8, 1), (36, 1), (40, 1)] }, { coefficient := 1, powers := [(19, 1), (30, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (32, 1), (58, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (49, 1)] }, { coefficient := 1, powers := [(19, 1), (32, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (35, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (42, 1)] }, { coefficient := 1, powers := [(12, 1), (35, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (49, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1)] }, { coefficient := 1, powers := [(18, 1), (28, 1), (49, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1)] }, { coefficient := 1, powers := [(12, 1), (30, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (61, 1)] }, { coefficient := 1, powers := [(12, 1), (49, 1)] }, { coefficient := 1, powers := [(19, 1), (21, 1), (53, 1)] }, { coefficient := 1, powers := [(19, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (60, 1)] }, { coefficient := 1, powers := [(18, 1), (26, 1), (41, 1)] }, { coefficient := 1, powers := [(18, 1), (26, 1), (46, 1)] }, { coefficient := 1, powers := [(18, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (61, 1)] }, { coefficient := 1, powers := [(12, 1), (26, 1), (47, 1)] }, { coefficient := 1, powers := [(12, 1), (58, 1)] }, { coefficient := 1, powers := [(19, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1), (53, 1)] }, { coefficient := 1, powers := [(46, 1), (51, 1)] }, { coefficient := 1, powers := [(51, 1), (57, 1)] }, { coefficient := 1, powers := [(53, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (22, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (46, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(18, 1), (22, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (44, 1), (54, 1)] }, { coefficient := 1, powers := [(24, 1), (58, 1)] }, { coefficient := 1, powers := [(30, 1), (49, 1)] }, { coefficient := 1, powers := [(36, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (42, 1), (57, 1)] }, { coefficient := 1, powers := [(1, 1), (48, 1), (53, 1)] }, { coefficient := 1, powers := [(7, 1), (35, 1), (42, 1)] }, { coefficient := 1, powers := [(11, 1), (27, 1), (48, 1)] }, { coefficient := 1, powers := [(15, 1), (27, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (60, 1)] }, { coefficient := 1, powers := [(10, 1), (46, 1)] }, { coefficient := 1, powers := [(10, 1), (57, 1)] }, { coefficient := 1, powers := [(15, 1), (41, 1)] }, { coefficient := 1, powers := [(15, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (52, 1)] }, { coefficient := 1, powers := [(22, 1), (57, 1)] }, { coefficient := 1, powers := [(27, 1), (41, 1)] }, { coefficient := 1, powers := [(27, 1), (46, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1)] }, { coefficient := 1, powers := [(35, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (48, 1), (53, 1)] }, { coefficient := 1, powers := [(21, 1), (51, 1), (57, 1)] }, { coefficient := 1, powers := [(21, 1), (53, 1)] }, { coefficient := 1, powers := [(42, 1)] }, { coefficient := 1, powers := [(48, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (38, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (41, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(41, 1)] }, { coefficient := 1, powers := [(46, 1)] }, { coefficient := 1, powers := [(52, 1)] }, { coefficient := 1, powers := [(57, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (38, 1), (60, 1)] }, { coefficient := 1, powers := [(1, 1), (41, 1), (57, 1)] }, { coefficient := 1, powers := [(1, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(4, 1), (27, 1), (60, 1)] }, { coefficient := 1, powers := [(4, 1), (32, 1), (57, 1)] }, { coefficient := 1, powers := [(4, 1), (35, 1), (52, 1)] }, { coefficient := 1, powers := [(7, 1), (22, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (32, 1), (46, 1)] }, { coefficient := 1, powers := [(7, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(10, 1), (22, 1), (57, 1)] }, { coefficient := 1, powers := [(10, 1), (27, 1), (46, 1)] }, { coefficient := 1, powers := [(10, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(15, 1), (22, 1), (52, 1)] }, { coefficient := 1, powers := [(15, 1), (27, 1), (41, 1)] }, { coefficient := 1, powers := [(15, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (39, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (42, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (49, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (49, 1)] }, { coefficient := 1, powers := [(8, 1), (36, 1), (42, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (58, 1)] }, { coefficient := 1, powers := [(12, 1), (30, 1), (49, 1)] }, { coefficient := 1, powers := [(12, 1), (36, 1), (39, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (55, 1)] }, { coefficient := 1, powers := [(19, 1), (30, 1), (42, 1)] }, { coefficient := 1, powers := [(19, 1), (33, 1), (39, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1)] }],
  [{ coefficient := 1, powers := [(1, 1)] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(40, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(41, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(42, 1), (64, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 47 → SparsePoly (Fin 65) := ![
  [{ coefficient := -1, powers := [(4, 1), (36, 1), (41, 1), (42, 1), (55, 1), (64, 1)] }, { coefficient := -1, powers := [(4, 1), (36, 1), (42, 1), (46, 1), (55, 1), (64, 1)] }, { coefficient := -1, powers := [(4, 1), (36, 1), (42, 1), (52, 1), (55, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (33, 1), (41, 1), (42, 1), (49, 1), (64, 1)] }, { coefficient := 1, powers := [(4, 1), (33, 1), (42, 1), (46, 1), (49, 1), (64, 1)] }, { coefficient := 1, powers := [(4, 1), (33, 1), (42, 1), (49, 1), (52, 1), (64, 1)] }, { coefficient := -1, powers := [(4, 1), (36, 1), (41, 1), (42, 2), (64, 1)] }, { coefficient := 1, powers := [(4, 1), (36, 1), (41, 1), (42, 1), (46, 1), (63, 1)] }, { coefficient := -1, powers := [(4, 1), (36, 1), (42, 2), (46, 1), (64, 1)] }, { coefficient := -1, powers := [(4, 1), (36, 1), (42, 2), (52, 1), (64, 1)] }, { coefficient := 1, powers := [(4, 1), (36, 1), (42, 1), (46, 2), (63, 1)] }, { coefficient := 1, powers := [(4, 1), (36, 1), (42, 1), (46, 1), (52, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (12, 1), (30, 1), (32, 1), (41, 1), (42, 1), (62, 1), (64, 1)] }, { coefficient := -1, powers := [(4, 1), (12, 1), (30, 1), (32, 1), (42, 1), (46, 1), (62, 1), (64, 1)] }, { coefficient := -1, powers := [(4, 1), (12, 1), (30, 1), (32, 1), (42, 1), (52, 1), (62, 1), (64, 1)] }, { coefficient := 2, powers := [(7, 1), (12, 1), (22, 1), (30, 1), (60, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (36, 1), (41, 1), (42, 1), (54, 1), (63, 1)] }, { coefficient := 1, powers := [(4, 1), (36, 1), (42, 1), (46, 1), (54, 1), (63, 1)] }, { coefficient := 1, powers := [(4, 1), (36, 1), (42, 1), (52, 1), (54, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (22, 1), (26, 1), (36, 1), (41, 2), (42, 1), (62, 1), (63, 1)] }, { coefficient := -2, powers := [(4, 1), (22, 1), (26, 1), (36, 1), (41, 1), (42, 1), (46, 1), (62, 1), (63, 1)] }, { coefficient := -1, powers := [(4, 1), (22, 1), (26, 1), (36, 1), (41, 1), (42, 1), (52, 1), (62, 1), (63, 1)] }, { coefficient := -1, powers := [(4, 1), (22, 1), (26, 1), (36, 1), (42, 1), (46, 2), (62, 1), (63, 1)] }, { coefficient := -1, powers := [(4, 1), (22, 1), (26, 1), (36, 1), (42, 1), (46, 1), (52, 1), (62, 1), (63, 1)] }, { coefficient := -1, powers := [(4, 1), (22, 1), (36, 1), (41, 1), (42, 1), (54, 1), (62, 1), (63, 1)] }, { coefficient := -1, powers := [(4, 1), (22, 1), (36, 1), (42, 1), (46, 1), (54, 1), (62, 1), (63, 1)] }, { coefficient := -1, powers := [(4, 1), (22, 1), (36, 1), (42, 1), (52, 1), (54, 1), (62, 1), (63, 1)] }, { coefficient := -1, powers := [(4, 1), (24, 1), (32, 1), (41, 1), (42, 1), (44, 1), (55, 1), (62, 1), (64, 1)] }, { coefficient := -1, powers := [(4, 1), (24, 1), (32, 1), (42, 1), (44, 1), (46, 1), (55, 1), (62, 1), (64, 1)] }, { coefficient := -1, powers := [(4, 1), (24, 1), (32, 1), (42, 1), (44, 1), (52, 1), (55, 1), (62, 1), (64, 1)] }, { coefficient := -1, powers := [(4, 1), (30, 1), (32, 1), (41, 1), (42, 1), (49, 1), (51, 1), (62, 1), (64, 1)] }, { coefficient := -1, powers := [(4, 1), (30, 1), (32, 1), (42, 1), (46, 1), (49, 1), (51, 1), (62, 1), (64, 1)] }, { coefficient := -1, powers := [(4, 1), (30, 1), (32, 1), (42, 1), (49, 1), (51, 1), (52, 1), (62, 1), (64, 1)] }, { coefficient := 1, powers := [(7, 1), (22, 1), (24, 1), (44, 1), (55, 1), (60, 1), (62, 1)] }, { coefficient := 1, powers := [(7, 1), (22, 1), (30, 1), (49, 1), (51, 1), (60, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (21, 1), (30, 1), (32, 1), (41, 1), (42, 1), (53, 1), (62, 1), (64, 1)] }, { coefficient := 1, powers := [(4, 1), (21, 1), (30, 1), (32, 1), (42, 1), (46, 1), (53, 1), (62, 1), (64, 1)] }, { coefficient := 1, powers := [(4, 1), (21, 1), (30, 1), (32, 1), (42, 1), (52, 1), (53, 1), (62, 1), (64, 1)] }, { coefficient := -1, powers := [(4, 1), (24, 1), (26, 1), (32, 1), (41, 1), (42, 1), (53, 1), (62, 1), (64, 1)] }, { coefficient := -1, powers := [(4, 1), (24, 1), (26, 1), (32, 1), (42, 1), (46, 1), (53, 1), (62, 1), (64, 1)] }, { coefficient := -1, powers := [(4, 1), (24, 1), (26, 1), (32, 1), (42, 1), (52, 1), (53, 1), (62, 1), (64, 1)] }, { coefficient := 1, powers := [(4, 1), (24, 1), (32, 1), (41, 1), (42, 1), (55, 1), (62, 1), (64, 1)] }, { coefficient := 1, powers := [(4, 1), (24, 1), (32, 1), (42, 1), (46, 1), (55, 1), (62, 1), (64, 1)] }, { coefficient := 1, powers := [(4, 1), (24, 1), (32, 1), (42, 1), (52, 1), (55, 1), (62, 1), (64, 1)] }, { coefficient := -1, powers := [(7, 1), (21, 1), (22, 1), (30, 1), (53, 1), (60, 1), (62, 1)] }, { coefficient := 1, powers := [(7, 1), (22, 1), (24, 1), (26, 1), (53, 1), (60, 1), (62, 1)] }, { coefficient := -1, powers := [(7, 1), (22, 1), (24, 1), (55, 1), (60, 1), (62, 1)] }, { coefficient := -1, powers := [(7, 1), (22, 1), (30, 1), (42, 1), (60, 1), (62, 1)] }, { coefficient := 1, powers := [(7, 1), (22, 1), (33, 1), (39, 1), (60, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (7, 1), (33, 1), (44, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (51, 1), (60, 1), (64, 1)] }, { coefficient := -1, powers := [(10, 1), (31, 1), (38, 1), (51, 1), (62, 1), (64, 1)] }, { coefficient := 1, powers := [(10, 1), (46, 1), (51, 1), (64, 1)] }, { coefficient := -1, powers := [(10, 1), (51, 1), (52, 1), (64, 1)] }, { coefficient := -1, powers := [(11, 1), (41, 1), (64, 1)] }, { coefficient := 1, powers := [(15, 1), (41, 1), (51, 1), (64, 1)] }, { coefficient := 1, powers := [(15, 1), (51, 1), (52, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(32, 1), (38, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (12, 1), (32, 1), (41, 1), (42, 1), (49, 1), (62, 1), (64, 1)] }, { coefficient := 1, powers := [(4, 1), (12, 1), (32, 1), (42, 1), (46, 1), (49, 1), (62, 1), (64, 1)] }, { coefficient := 1, powers := [(4, 1), (12, 1), (32, 1), (42, 1), (49, 1), (52, 1), (62, 1), (64, 1)] }, { coefficient := -2, powers := [(7, 1), (12, 1), (22, 1), (49, 1), (60, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (22, 1), (46, 2), (51, 1), (52, 1), (64, 1)] }, { coefficient := 1, powers := [(21, 1), (32, 1), (38, 1), (46, 2), (51, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(21, 1), (22, 1), (46, 2), (52, 1), (64, 1)] }, { coefficient := -1, powers := [(21, 1), (32, 1), (38, 1), (46, 2), (64, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (24, 1), (26, 1), (32, 1), (41, 1), (42, 1), (64, 1)] }, { coefficient := 1, powers := [(4, 1), (24, 1), (26, 1), (32, 1), (42, 1), (46, 1), (64, 1)] }, { coefficient := 1, powers := [(4, 1), (24, 1), (26, 1), (32, 1), (42, 1), (52, 1), (64, 1)] }, { coefficient := -1, powers := [(7, 1), (22, 1), (24, 1), (26, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (18, 1), (32, 1), (41, 1), (42, 1), (49, 1), (64, 1)] }, { coefficient := 1, powers := [(4, 1), (18, 1), (32, 1), (42, 1), (46, 1), (49, 1), (64, 1)] }, { coefficient := 1, powers := [(4, 1), (18, 1), (32, 1), (42, 1), (49, 1), (52, 1), (64, 1)] }, { coefficient := -1, powers := [(7, 1), (18, 1), (22, 1), (49, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (18, 1), (32, 1), (41, 1), (42, 1), (55, 1), (64, 1)] }, { coefficient := 1, powers := [(4, 1), (18, 1), (32, 1), (42, 1), (46, 1), (55, 1), (64, 1)] }, { coefficient := 1, powers := [(4, 1), (18, 1), (32, 1), (42, 1), (52, 1), (55, 1), (64, 1)] }, { coefficient := -1, powers := [(7, 1), (18, 1), (22, 1), (55, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (60, 1), (64, 1)] }, { coefficient := 1, powers := [(10, 1), (31, 1), (38, 1), (62, 1), (64, 1)] }, { coefficient := -1, powers := [(10, 1), (46, 1), (64, 1)] }, { coefficient := 1, powers := [(10, 1), (52, 1), (64, 1)] }, { coefficient := -1, powers := [(15, 1), (41, 1), (64, 1)] }, { coefficient := -1, powers := [(15, 1), (52, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (12, 1), (36, 1), (41, 1), (42, 1), (64, 1)] }, { coefficient := -1, powers := [(4, 1), (12, 1), (36, 1), (42, 1), (46, 1), (64, 1)] }, { coefficient := -1, powers := [(4, 1), (12, 1), (36, 1), (42, 1), (52, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(22, 1), (46, 1), (51, 1), (52, 1), (64, 1)] }, { coefficient := -1, powers := [(32, 1), (38, 1), (46, 1), (51, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (22, 1), (46, 1), (52, 1), (64, 1)] }, { coefficient := 1, powers := [(21, 1), (32, 1), (38, 1), (46, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (7, 1), (33, 1), (60, 1)] }, { coefficient := -1, powers := [(7, 1), (12, 1), (24, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(52, 1)] }],
  [{ coefficient := -1, powers := [(31, 1), (38, 1), (62, 1)] }, { coefficient := 1, powers := [(46, 1)] }],
  [{ coefficient := -1, powers := [(10, 1), (21, 1), (22, 1), (46, 1), (52, 1), (64, 1)] }, { coefficient := -1, powers := [(10, 1), (21, 1), (32, 1), (38, 1), (46, 1), (64, 1)] }, { coefficient := 1, powers := [(10, 1), (22, 1), (48, 1), (52, 1), (64, 1)] }, { coefficient := 1, powers := [(10, 1), (32, 1), (38, 1), (48, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (22, 1), (42, 1), (60, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (33, 1), (41, 1), (42, 1), (64, 1)] }, { coefficient := -1, powers := [(4, 1), (33, 1), (42, 1), (46, 1), (64, 1)] }, { coefficient := -1, powers := [(4, 1), (33, 1), (42, 1), (52, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (36, 1), (41, 1), (42, 1), (64, 1)] }, { coefficient := 1, powers := [(4, 1), (36, 1), (42, 1), (46, 1), (64, 1)] }, { coefficient := 1, powers := [(4, 1), (36, 1), (42, 1), (52, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (32, 1), (41, 1), (42, 1), (55, 1), (64, 1)] }, { coefficient := -1, powers := [(4, 1), (32, 1), (42, 1), (46, 1), (55, 1), (64, 1)] }, { coefficient := -1, powers := [(4, 1), (32, 1), (42, 1), (52, 1), (55, 1), (64, 1)] }, { coefficient := 1, powers := [(7, 1), (22, 1), (55, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (32, 1), (41, 1), (42, 1), (49, 1), (64, 1)] }, { coefficient := -1, powers := [(4, 1), (32, 1), (42, 1), (46, 1), (49, 1), (64, 1)] }, { coefficient := -1, powers := [(4, 1), (32, 1), (42, 1), (49, 1), (52, 1), (64, 1)] }, { coefficient := 1, powers := [(7, 1), (22, 1), (49, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (30, 1), (32, 1), (41, 1), (42, 1), (64, 1)] }, { coefficient := -1, powers := [(4, 1), (30, 1), (32, 1), (42, 1), (46, 1), (64, 1)] }, { coefficient := -1, powers := [(4, 1), (30, 1), (32, 1), (42, 1), (52, 1), (64, 1)] }, { coefficient := 1, powers := [(7, 1), (22, 1), (30, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (22, 1), (36, 1), (41, 1), (42, 1), (63, 1)] }, { coefficient := 1, powers := [(4, 1), (22, 1), (36, 1), (42, 1), (46, 1), (63, 1)] }, { coefficient := 1, powers := [(4, 1), (22, 1), (36, 1), (42, 1), (52, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (24, 1), (32, 1), (41, 1), (42, 1), (64, 1)] }, { coefficient := -1, powers := [(4, 1), (24, 1), (32, 1), (42, 1), (46, 1), (64, 1)] }, { coefficient := -1, powers := [(4, 1), (24, 1), (32, 1), (42, 1), (52, 1), (64, 1)] }, { coefficient := 1, powers := [(7, 1), (22, 1), (24, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (21, 1), (22, 1), (52, 1), (64, 1)] }, { coefficient := 1, powers := [(10, 1), (21, 1), (32, 1), (38, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (36, 1), (41, 1), (42, 1), (63, 1)] }, { coefficient := -1, powers := [(4, 1), (36, 1), (42, 1), (46, 1), (63, 1)] }, { coefficient := -1, powers := [(4, 1), (36, 1), (42, 1), (52, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (12, 1), (22, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(41, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(27, 1)] }],
  [{ coefficient := 1, powers := [(10, 1)] }],
  [{ coefficient := -1, powers := [(10, 1), (22, 1), (52, 1), (64, 1)] }, { coefficient := -1, powers := [(10, 1), (32, 1), (38, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (32, 1)] }, { coefficient := -1, powers := [(10, 1), (27, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(4, 1), (32, 1), (41, 1), (42, 1), (64, 1)] }, { coefficient := 1, powers := [(4, 1), (32, 1), (42, 1), (46, 1), (64, 1)] }, { coefficient := 1, powers := [(4, 1), (32, 1), (42, 1), (52, 1), (64, 1)] }, { coefficient := -1, powers := [(7, 1), (22, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (32, 1), (38, 1), (60, 1)] }, { coefficient := -1, powers := [(4, 1), (32, 1), (41, 1), (57, 1)] }, { coefficient := -1, powers := [(4, 1), (32, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(10, 1), (21, 1), (22, 1), (46, 2), (51, 1), (52, 1), (64, 1)] }, { coefficient := -1, powers := [(10, 1), (21, 1), (22, 1), (46, 1), (52, 1), (53, 1), (64, 1)] }, { coefficient := 1, powers := [(10, 1), (21, 1), (32, 1), (38, 1), (46, 2), (51, 1), (64, 1)] }, { coefficient := -1, powers := [(10, 1), (21, 1), (32, 1), (38, 1), (46, 1), (53, 1), (64, 1)] }, { coefficient := 1, powers := [(10, 1), (22, 1), (42, 1), (52, 1), (57, 1), (64, 1)] }, { coefficient := -1, powers := [(10, 1), (22, 1), (46, 1), (48, 1), (51, 1), (52, 1), (64, 1)] }, { coefficient := 1, powers := [(10, 1), (22, 1), (48, 1), (52, 1), (53, 1), (64, 1)] }, { coefficient := 1, powers := [(10, 1), (27, 1), (38, 1), (60, 1)] }, { coefficient := 1, powers := [(10, 1), (27, 1), (41, 1), (57, 1)] }, { coefficient := 1, powers := [(10, 1), (27, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(10, 1), (32, 1), (38, 1), (42, 1), (57, 1), (64, 1)] }, { coefficient := -1, powers := [(10, 1), (32, 1), (38, 1), (46, 1), (48, 1), (51, 1), (64, 1)] }, { coefficient := 1, powers := [(10, 1), (32, 1), (38, 1), (48, 1), (53, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(31, 1), (38, 1), (52, 1), (62, 1)] }, { coefficient := 1, powers := [(38, 1), (60, 1)] }, { coefficient := -1, powers := [(41, 1), (42, 1), (57, 1), (64, 1)] }, { coefficient := -1, powers := [(41, 1), (48, 1), (53, 1), (64, 1)] }, { coefficient := 1, powers := [(41, 1), (57, 1)] }, { coefficient := -1, powers := [(46, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (32, 1), (39, 1), (41, 1), (42, 1), (61, 1), (64, 1)] }, { coefficient := -1, powers := [(4, 1), (32, 1), (39, 1), (42, 1), (46, 1), (61, 1), (64, 1)] }, { coefficient := -1, powers := [(4, 1), (32, 1), (39, 1), (42, 1), (52, 1), (61, 1), (64, 1)] }, { coefficient := -1, powers := [(4, 1), (32, 1), (41, 1), (42, 2), (58, 1), (64, 1)] }, { coefficient := 1, powers := [(4, 1), (32, 1), (41, 1), (42, 1), (49, 1), (55, 1), (64, 1)] }, { coefficient := -1, powers := [(4, 1), (32, 1), (42, 2), (46, 1), (58, 1), (64, 1)] }, { coefficient := -1, powers := [(4, 1), (32, 1), (42, 2), (52, 1), (58, 1), (64, 1)] }, { coefficient := 1, powers := [(4, 1), (32, 1), (42, 1), (46, 1), (49, 1), (55, 1), (64, 1)] }, { coefficient := 1, powers := [(4, 1), (32, 1), (42, 1), (49, 1), (52, 1), (55, 1), (64, 1)] }, { coefficient := 1, powers := [(7, 1), (22, 1), (39, 1), (60, 1), (61, 1)] }, { coefficient := -1, powers := [(7, 1), (22, 1), (40, 1), (42, 1), (58, 1), (60, 1), (62, 1)] }, { coefficient := 1, powers := [(7, 1), (22, 1), (42, 1), (58, 1), (60, 1)] }, { coefficient := -1, powers := [(7, 1), (22, 1), (49, 1), (55, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (12, 1), (30, 1), (32, 1), (41, 1), (42, 1), (49, 1), (64, 1)] }, { coefficient := -1, powers := [(4, 1), (12, 1), (30, 1), (32, 1), (42, 1), (46, 1), (49, 1), (64, 1)] }, { coefficient := -1, powers := [(4, 1), (12, 1), (30, 1), (32, 1), (42, 1), (49, 1), (52, 1), (64, 1)] }, { coefficient := 1, powers := [(4, 1), (18, 1), (22, 1), (26, 1), (36, 1), (41, 2), (42, 1), (63, 1)] }, { coefficient := 2, powers := [(4, 1), (18, 1), (22, 1), (26, 1), (36, 1), (41, 1), (42, 1), (46, 1), (63, 1)] }, { coefficient := 1, powers := [(4, 1), (18, 1), (22, 1), (26, 1), (36, 1), (41, 1), (42, 1), (52, 1), (63, 1)] }, { coefficient := 1, powers := [(4, 1), (18, 1), (22, 1), (26, 1), (36, 1), (42, 1), (46, 2), (63, 1)] }, { coefficient := 1, powers := [(4, 1), (18, 1), (22, 1), (26, 1), (36, 1), (42, 1), (46, 1), (52, 1), (63, 1)] }, { coefficient := 1, powers := [(4, 1), (18, 1), (22, 1), (36, 1), (41, 1), (42, 1), (54, 1), (63, 1)] }, { coefficient := 1, powers := [(4, 1), (18, 1), (22, 1), (36, 1), (42, 1), (46, 1), (54, 1), (63, 1)] }, { coefficient := 1, powers := [(4, 1), (18, 1), (22, 1), (36, 1), (42, 1), (52, 1), (54, 1), (63, 1)] }, { coefficient := 1, powers := [(4, 1), (18, 1), (24, 1), (32, 1), (41, 1), (42, 1), (44, 1), (55, 1), (64, 1)] }, { coefficient := 1, powers := [(4, 1), (18, 1), (24, 1), (32, 1), (42, 1), (44, 1), (46, 1), (55, 1), (64, 1)] }, { coefficient := 1, powers := [(4, 1), (18, 1), (24, 1), (32, 1), (42, 1), (44, 1), (52, 1), (55, 1), (64, 1)] }, { coefficient := 1, powers := [(4, 1), (18, 1), (30, 1), (32, 1), (41, 1), (42, 1), (49, 1), (51, 1), (64, 1)] }, { coefficient := 1, powers := [(4, 1), (18, 1), (30, 1), (32, 1), (42, 1), (46, 1), (49, 1), (51, 1), (64, 1)] }, { coefficient := 1, powers := [(4, 1), (18, 1), (30, 1), (32, 1), (42, 1), (49, 1), (51, 1), (52, 1), (64, 1)] }, { coefficient := -1, powers := [(4, 1), (19, 1), (21, 1), (30, 1), (32, 1), (41, 1), (42, 1), (53, 1), (64, 1)] }, { coefficient := -1, powers := [(4, 1), (19, 1), (21, 1), (30, 1), (32, 1), (42, 1), (46, 1), (53, 1), (64, 1)] }, { coefficient := -1, powers := [(4, 1), (19, 1), (21, 1), (30, 1), (32, 1), (42, 1), (52, 1), (53, 1), (64, 1)] }, { coefficient := 1, powers := [(4, 1), (19, 1), (24, 1), (26, 1), (32, 1), (41, 1), (42, 1), (53, 1), (64, 1)] }, { coefficient := 1, powers := [(4, 1), (19, 1), (24, 1), (26, 1), (32, 1), (42, 1), (46, 1), (53, 1), (64, 1)] }, { coefficient := 1, powers := [(4, 1), (19, 1), (24, 1), (26, 1), (32, 1), (42, 1), (52, 1), (53, 1), (64, 1)] }, { coefficient := -1, powers := [(4, 1), (19, 1), (24, 1), (32, 1), (41, 1), (42, 1), (55, 1), (64, 1)] }, { coefficient := -1, powers := [(4, 1), (19, 1), (24, 1), (32, 1), (42, 1), (46, 1), (55, 1), (64, 1)] }, { coefficient := -1, powers := [(4, 1), (19, 1), (24, 1), (32, 1), (42, 1), (52, 1), (55, 1), (64, 1)] }, { coefficient := -1, powers := [(7, 1), (8, 1), (22, 1), (36, 1), (42, 1), (60, 1)] }, { coefficient := 2, powers := [(7, 1), (12, 1), (22, 1), (30, 1), (49, 1), (60, 1)] }, { coefficient := -1, powers := [(7, 1), (18, 1), (22, 1), (24, 1), (44, 1), (55, 1), (60, 1)] }, { coefficient := -1, powers := [(7, 1), (18, 1), (22, 1), (30, 1), (49, 1), (51, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (19, 1), (21, 1), (22, 1), (30, 1), (53, 1), (60, 1)] }, { coefficient := -1, powers := [(7, 1), (19, 1), (22, 1), (24, 1), (26, 1), (53, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (19, 1), (22, 1), (24, 1), (55, 1), (60, 1)] }, { coefficient := -1, powers := [(7, 1), (19, 1), (22, 1), (33, 1), (39, 1), (60, 1)] }, { coefficient := -1, powers := [(15, 1), (32, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (8, 1), (35, 1), (36, 1), (41, 1), (42, 1)] }, { coefficient := 1, powers := [(4, 1), (8, 1), (35, 1), (36, 1), (42, 1), (46, 1)] }, { coefficient := 1, powers := [(4, 1), (8, 1), (35, 1), (36, 1), (42, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (8, 1), (35, 1), (36, 1), (41, 1), (42, 1)] }, { coefficient := -1, powers := [(4, 1), (8, 1), (35, 1), (36, 1), (42, 1), (46, 1)] }, { coefficient := -1, powers := [(4, 1), (8, 1), (35, 1), (36, 1), (42, 1), (52, 1)] }, { coefficient := 1, powers := [(4, 1), (32, 1), (41, 1)] }, { coefficient := 1, powers := [(4, 1), (32, 1), (46, 1)] }, { coefficient := 1, powers := [(4, 1), (32, 1), (52, 1)] }, { coefficient := 1, powers := [(7, 1), (27, 1), (60, 1)] }, { coefficient := -1, powers := [(7, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(10, 1), (22, 1), (52, 1)] }, { coefficient := -1, powers := [(10, 1), (27, 1), (31, 1), (38, 1), (62, 1)] }, { coefficient := 1, powers := [(10, 1), (27, 1), (46, 1)] }, { coefficient := -1, powers := [(10, 1), (27, 1), (52, 1)] }, { coefficient := 1, powers := [(10, 1), (32, 1), (38, 1)] }, { coefficient := 1, powers := [(15, 1), (27, 1), (52, 1)] }]
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
    ¬ ∀ index : Fin 47,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component37.SelectedLeafB0_7.selectedHasNoCommonZero

end Krenn.Component37.SelectedLeafB0_7
