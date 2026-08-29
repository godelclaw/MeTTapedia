import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component60.SelectedLeafB2_3

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "abe058282de12f1756f31e58cc668bbe3803c9bb2739f045ed448ad6006d6812"
def certificateSHA256 : String := "bfba81ef08f31f9bda176ad14620ec260bcf2904f652d088cb72097f9d864eb8"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 73 → Fin 662 := ![
  7,
  10,
  11,
  12,
  13,
  14,
  22,
  25,
  44,
  57,
  145,
  146,
  147,
  149,
  150,
  151,
  152,
  164,
  165,
  167,
  168,
  172,
  173,
  178,
  194,
  206,
  211,
  236,
  237,
  263,
  264,
  292,
  293,
  294,
  295,
  297,
  298,
  300,
  301,
  302,
  303,
  310,
  313,
  314,
  348,
  350,
  403,
  434,
  436,
  443,
  446,
  449,
  453,
  455,
  459,
  460,
  463,
  491,
  556,
  583,
  592,
  600,
  601,
  608,
  609,
  612,
  653,
  655,
  656,
  657,
  658,
  659,
  660
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 73 → SparsePoly (Fin 64) := ![
  [{ coefficient := 1, powers := [(5, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (29, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (29, 1)] }],
  [{ coefficient := 1, powers := [(15, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(15, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (35, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (35, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (53, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (35, 1)] }, { coefficient := 1, powers := [(35, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (32, 1)] }, { coefficient := 1, powers := [(32, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (30, 1)] }, { coefficient := 1, powers := [(18, 1), (26, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (26, 1)] }, { coefficient := 1, powers := [(26, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (29, 1)] }, { coefficient := 1, powers := [(29, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (43, 1)] }, { coefficient := 1, powers := [(39, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (25, 1)] }, { coefficient := 1, powers := [(18, 1), (20, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (26, 1)] }, { coefficient := 1, powers := [(18, 1), (20, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (43, 1)] }, { coefficient := 1, powers := [(19, 1), (20, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (46, 1)] }, { coefficient := 1, powers := [(19, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (20, 1)] }, { coefficient := 1, powers := [(18, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (43, 1)] }, { coefficient := 1, powers := [(19, 1), (20, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (53, 1)] }, { coefficient := 1, powers := [(29, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (29, 1), (59, 1)] }, { coefficient := 1, powers := [(29, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (30, 1), (44, 1)] }, { coefficient := 1, powers := [(8, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (26, 1), (46, 1)] }, { coefficient := 1, powers := [(9, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (25, 1), (45, 1)] }, { coefficient := 1, powers := [(18, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (25, 1), (46, 1)] }, { coefficient := 1, powers := [(19, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (25, 1), (43, 1)] }, { coefficient := 1, powers := [(19, 1), (20, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (25, 1), (48, 1)] }, { coefficient := 1, powers := [(19, 1), (21, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1)] }, { coefficient := 1, powers := [(20, 1), (43, 1)] }, { coefficient := 1, powers := [(25, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (48, 1)] }, { coefficient := 1, powers := [(21, 1), (43, 1)] }, { coefficient := 1, powers := [(25, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (50, 1)] }, { coefficient := 1, powers := [(20, 1), (50, 1)] }, { coefficient := 1, powers := [(25, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (54, 1)] }, { coefficient := 1, powers := [(20, 1), (54, 1)] }, { coefficient := 1, powers := [(26, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (48, 1)] }, { coefficient := 1, powers := [(10, 1), (27, 1), (48, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (49, 1)] }, { coefficient := 1, powers := [(15, 1), (22, 1), (49, 1)] }, { coefficient := 1, powers := [(15, 1), (27, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (54, 1)] }, { coefficient := 1, powers := [(11, 1), (27, 1), (53, 1)] }, { coefficient := 1, powers := [(15, 1), (22, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (48, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1)] }, { coefficient := 1, powers := [(12, 1), (29, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (58, 1)] }, { coefficient := 1, powers := [(9, 1), (42, 1)] }, { coefficient := 1, powers := [(13, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (46, 1)] }, { coefficient := 1, powers := [(19, 1), (40, 1)] }, { coefficient := 1, powers := [(19, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1), (54, 1)] }, { coefficient := 1, powers := [(13, 1), (54, 1)] }, { coefficient := 1, powers := [(26, 1), (44, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1), (50, 1)] }, { coefficient := 1, powers := [(25, 1), (45, 1), (50, 1)] }, { coefficient := 1, powers := [(50, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (32, 1), (55, 1)] }, { coefficient := 1, powers := [(6, 1), (32, 1), (42, 1)] }, { coefficient := 1, powers := [(13, 1), (32, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (35, 1), (49, 1)] }, { coefficient := 1, powers := [(6, 1), (35, 1), (39, 1)] }, { coefficient := 1, powers := [(9, 1), (35, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (25, 1), (40, 1)] }, { coefficient := 1, powers := [(18, 1), (25, 1), (45, 1)] }, { coefficient := 1, powers := [(18, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (60, 1)] }, { coefficient := 1, powers := [(12, 1), (48, 1)] }, { coefficient := 1, powers := [(19, 1), (21, 1), (52, 1)] }, { coefficient := 1, powers := [(19, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (60, 1)] }, { coefficient := 1, powers := [(12, 1), (26, 1), (46, 1)] }, { coefficient := 1, powers := [(12, 1), (57, 1)] }, { coefficient := 1, powers := [(19, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (54, 1)] }, { coefficient := 1, powers := [(29, 1), (41, 1)] }, { coefficient := 1, powers := [(29, 1), (47, 1), (50, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (37, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(43, 1), (52, 1)] }, { coefficient := 1, powers := [(46, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1), (51, 1)] }, { coefficient := 1, powers := [(3, 1), (33, 1), (51, 1)] }, { coefficient := 1, powers := [(13, 1), (20, 1), (51, 1)] }, { coefficient := 1, powers := [(42, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1), (52, 1)] }, { coefficient := 1, powers := [(3, 1), (60, 1)] }, { coefficient := 1, powers := [(20, 1), (43, 1), (52, 1)] }, { coefficient := 1, powers := [(43, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1), (50, 1)] }, { coefficient := 1, powers := [(13, 1), (50, 1)] }, { coefficient := 1, powers := [(25, 1), (44, 1), (50, 1)] }, { coefficient := 1, powers := [(50, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1), (52, 1)] }, { coefficient := 1, powers := [(45, 1), (50, 1)] }, { coefficient := 1, powers := [(50, 1), (56, 1)] }, { coefficient := 1, powers := [(52, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1), (53, 1)] }, { coefficient := 1, powers := [(26, 1), (40, 1)] }, { coefficient := 1, powers := [(26, 1), (45, 1)] }, { coefficient := 1, powers := [(53, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1), (51, 1)] }, { coefficient := 1, powers := [(40, 1), (43, 1)] }, { coefficient := 1, powers := [(43, 1), (51, 1)] }, { coefficient := 1, powers := [(46, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (29, 1), (60, 1)] }, { coefficient := 1, powers := [(3, 1), (32, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (35, 1), (54, 1)] }, { coefficient := 1, powers := [(29, 1), (43, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (43, 1), (53, 1)] }, { coefficient := 1, powers := [(24, 1), (57, 1)] }, { coefficient := 1, powers := [(29, 1), (48, 1)] }, { coefficient := 1, powers := [(35, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (39, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (30, 1), (57, 1)] }, { coefficient := 1, powers := [(9, 1), (20, 1), (57, 1)] }, { coefficient := 1, powers := [(9, 1), (26, 1), (43, 1)] }, { coefficient := 1, powers := [(26, 1), (39, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (46, 1), (53, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (40, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (46, 1)] }, { coefficient := 1, powers := [(19, 1), (29, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1)] }, { coefficient := 1, powers := [(3, 1), (33, 1)] }, { coefficient := 1, powers := [(13, 1), (20, 1)] }, { coefficient := 1, powers := [(20, 1), (55, 1)] }, { coefficient := 1, powers := [(25, 1), (42, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (49, 1)] }, { coefficient := 1, powers := [(6, 1), (30, 1)] }, { coefficient := 1, powers := [(9, 1), (25, 1)] }, { coefficient := 1, powers := [(20, 1), (49, 1)] }, { coefficient := 1, powers := [(25, 1), (39, 1)] }, { coefficient := 1, powers := [(30, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (46, 1), (53, 1)] }, { coefficient := 1, powers := [(26, 1), (40, 1), (43, 1)] }, { coefficient := 1, powers := [(26, 1), (46, 1)] }, { coefficient := 1, powers := [(43, 1), (53, 1)] }, { coefficient := 1, powers := [(57, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (41, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (47, 1), (52, 1)] }, { coefficient := 1, powers := [(21, 1), (50, 1), (56, 1)] }, { coefficient := 1, powers := [(21, 1), (52, 1)] }, { coefficient := 1, powers := [(41, 1)] }, { coefficient := 1, powers := [(47, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1), (49, 1)] }, { coefficient := 1, powers := [(6, 1), (30, 1), (44, 1)] }, { coefficient := 1, powers := [(6, 1), (58, 1)] }, { coefficient := 1, powers := [(9, 1), (25, 1), (44, 1)] }, { coefficient := 1, powers := [(9, 1), (55, 1)] }, { coefficient := 1, powers := [(13, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (36, 1), (58, 1)] }, { coefficient := 1, powers := [(0, 1), (39, 1), (55, 1)] }, { coefficient := 1, powers := [(0, 1), (42, 1), (49, 1)] }, { coefficient := 1, powers := [(3, 1), (25, 1), (58, 1)] }, { coefficient := 1, powers := [(3, 1), (30, 1), (55, 1)] }, { coefficient := 1, powers := [(3, 1), (33, 1), (49, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1), (58, 1)] }, { coefficient := 1, powers := [(6, 1), (30, 1), (42, 1)] }, { coefficient := 1, powers := [(6, 1), (33, 1), (39, 1)] }, { coefficient := 1, powers := [(9, 1), (20, 1), (55, 1)] }, { coefficient := 1, powers := [(9, 1), (25, 1), (42, 1)] }, { coefficient := 1, powers := [(9, 1), (33, 1), (36, 1)] }, { coefficient := 1, powers := [(13, 1), (20, 1), (49, 1)] }, { coefficient := 1, powers := [(13, 1), (25, 1), (39, 1)] }, { coefficient := 1, powers := [(13, 1), (30, 1), (36, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (41, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (48, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (48, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1), (29, 1), (48, 1)] }, { coefficient := 1, powers := [(12, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (54, 1)] }, { coefficient := 1, powers := [(19, 1), (29, 1), (41, 1)] }, { coefficient := 1, powers := [(19, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (61, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(39, 1)] }],
  [{ coefficient := 1, powers := [(40, 1), (62, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 73 → SparsePoly (Fin 64) := ![
  [{ coefficient := 1, powers := [(5, 1), (6, 1), (20, 1), (29, 1), (32, 1), (57, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (6, 1), (20, 1), (32, 2), (57, 2)] }, { coefficient := 1, powers := [(5, 1), (6, 1), (20, 1), (32, 1), (35, 1), (54, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (6, 1), (26, 1), (29, 1), (35, 1), (50, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (6, 1), (26, 1), (32, 1), (35, 1), (50, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (6, 1), (26, 1), (35, 2), (50, 1), (54, 1)] }],
  [{ coefficient := 2, powers := [(12, 1), (27, 1), (48, 1), (61, 1)] }],
  [{ coefficient := -3, powers := [(19, 1), (27, 1), (47, 1), (61, 1)] }],
  [{ coefficient := 3, powers := [(19, 1), (22, 1), (54, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (13, 1), (20, 1), (22, 1), (35, 1), (54, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (20, 1), (22, 1), (32, 1), (42, 1), (57, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (20, 1), (22, 1), (32, 1), (55, 1), (57, 1), (61, 1)] }, { coefficient := -1, powers := [(5, 1), (20, 1), (22, 1), (35, 1), (42, 1), (54, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (22, 1), (25, 1), (32, 1), (42, 1), (57, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (22, 1), (32, 1), (33, 1), (36, 1), (57, 1), (61, 1)] }],
  [{ coefficient := -2, powers := [(12, 1), (22, 1), (53, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (6, 1), (12, 1), (20, 1), (32, 1), (53, 1), (57, 1), (58, 1)] }, { coefficient := -1, powers := [(5, 1), (6, 1), (12, 1), (26, 1), (35, 1), (50, 1), (53, 1), (58, 1)] }, { coefficient := -1, powers := [(12, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (6, 1), (19, 1), (20, 1), (32, 1), (47, 1), (57, 1), (58, 1)] }, { coefficient := -1, powers := [(5, 1), (6, 1), (19, 1), (26, 1), (35, 1), (47, 1), (50, 1), (58, 1)] }, { coefficient := -1, powers := [(5, 1), (25, 1), (30, 1), (46, 1), (55, 1)] }, { coefficient := -2, powers := [(19, 1), (21, 1), (45, 1)] }, { coefficient := -2, powers := [(19, 1), (25, 1), (45, 1), (47, 1)] }, { coefficient := -1, powers := [(19, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (13, 1), (20, 1), (30, 1), (54, 1)] }, { coefficient := -1, powers := [(5, 1), (30, 1), (33, 1), (36, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (20, 1), (54, 1), (58, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(21, 1), (43, 1), (52, 1)] }, { coefficient := -1, powers := [(41, 1), (46, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (9, 1), (33, 1), (54, 1)] }, { coefficient := -1, powers := [(5, 1), (13, 1), (20, 1), (30, 1), (51, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (30, 1), (42, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (6, 1), (20, 1), (24, 1), (32, 1), (44, 1), (57, 1), (60, 1)] }, { coefficient := -1, powers := [(5, 1), (6, 1), (20, 1), (32, 1), (35, 1), (41, 1), (44, 1), (57, 1)] }, { coefficient := -1, powers := [(5, 1), (6, 1), (24, 1), (26, 1), (35, 1), (44, 1), (50, 1), (60, 1)] }, { coefficient := -1, powers := [(5, 1), (6, 1), (26, 1), (35, 2), (41, 1), (44, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (13, 1), (35, 1), (50, 1)] }, { coefficient := 1, powers := [(5, 1), (25, 1), (32, 1), (42, 1), (46, 1)] }, { coefficient := -1, powers := [(5, 1), (32, 1), (33, 1), (36, 1), (46, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (50, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (6, 1), (12, 1), (20, 1), (32, 1), (42, 1), (48, 1), (57, 1), (59, 1)] }, { coefficient := -1, powers := [(5, 1), (6, 1), (12, 1), (26, 1), (35, 1), (42, 1), (48, 1), (50, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (26, 1), (32, 1), (55, 1)] }],
  [{ coefficient := -2, powers := [(24, 1), (46, 1), (53, 1)] }],
  [{ coefficient := -2, powers := [(24, 1), (40, 1), (43, 1)] }, { coefficient := -2, powers := [(24, 1), (43, 1), (45, 1)] }, { coefficient := 1, powers := [(24, 1), (46, 1)] }],
  [{ coefficient := 2, powers := [(24, 1), (26, 1), (40, 1)] }, { coefficient := 1, powers := [(24, 1), (26, 1), (51, 1)] }, { coefficient := 1, powers := [(24, 1), (40, 1), (53, 1), (62, 1)] }, { coefficient := -2, powers := [(24, 1), (53, 1)] }],
  [{ coefficient := 2, powers := [(24, 1), (25, 1), (26, 1), (40, 1)] }, { coefficient := 2, powers := [(24, 1), (25, 1), (26, 1), (51, 1)] }, { coefficient := 1, powers := [(24, 1), (25, 1), (40, 1), (53, 1), (62, 1)] }, { coefficient := 1, powers := [(24, 1), (25, 1), (51, 1), (53, 1), (62, 1)] }],
  [{ coefficient := 2, powers := [(24, 1), (26, 1), (46, 1), (52, 1)] }, { coefficient := 2, powers := [(24, 1), (40, 1), (43, 1), (54, 1)] }, { coefficient := 2, powers := [(24, 1), (43, 1), (45, 1), (54, 1)] }, { coefficient := 2, powers := [(24, 1), (46, 1), (50, 1), (53, 1)] }, { coefficient := 1, powers := [(24, 1), (46, 1), (52, 1), (53, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (26, 1), (52, 1)] }, { coefficient := 1, powers := [(24, 1), (52, 1), (53, 1), (62, 1)] }, { coefficient := 2, powers := [(24, 1), (54, 1)] }],
  [{ coefficient := 3, powers := [(11, 1), (19, 1), (27, 1), (61, 1)] }, { coefficient := 2, powers := [(12, 1), (16, 1), (22, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (6, 1), (12, 1), (20, 1), (32, 1), (48, 1), (57, 1), (58, 1)] }, { coefficient := -1, powers := [(5, 1), (6, 1), (12, 1), (26, 1), (35, 1), (48, 1), (50, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (6, 1), (20, 1), (24, 1), (32, 1), (57, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (6, 1), (20, 1), (32, 1), (35, 1), (41, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (6, 1), (24, 1), (26, 1), (35, 1), (50, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (6, 1), (26, 1), (35, 2), (41, 1), (50, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (25, 1), (32, 1), (42, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (33, 1), (36, 1)] }],
  [{ coefficient := -2, powers := [(24, 1), (26, 1), (46, 1)] }],
  [{ coefficient := -2, powers := [(24, 1), (26, 1), (40, 1)] }, { coefficient := 2, powers := [(24, 1), (26, 1), (45, 1)] }, { coefficient := -2, powers := [(24, 1), (26, 1), (51, 1)] }, { coefficient := -1, powers := [(24, 1), (40, 1), (53, 1), (62, 1)] }, { coefficient := -1, powers := [(24, 1), (51, 1), (53, 1), (62, 1)] }, { coefficient := 2, powers := [(24, 1), (53, 1)] }],
  [{ coefficient := 2, powers := [(24, 1), (52, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(29, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (29, 1), (30, 1), (52, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (29, 1), (52, 1)] }],
  [{ coefficient := -2, powers := [(5, 1), (9, 1), (26, 1), (35, 1), (44, 1)] }],
  [{ coefficient := -3, powers := [(5, 1), (9, 1), (13, 1), (35, 1)] }, { coefficient := -2, powers := [(5, 1), (9, 1), (35, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (13, 1), (35, 1), (49, 1)] }, { coefficient := -1, powers := [(18, 1), (24, 1), (46, 1)] }, { coefficient := -2, powers := [(19, 1), (24, 1), (51, 1)] }],
  [{ coefficient := -2, powers := [(12, 1), (29, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (13, 1), (20, 1), (35, 1), (54, 1), (61, 1)] }, { coefficient := -1, powers := [(5, 1), (20, 1), (32, 1), (42, 1), (57, 1), (61, 1)] }, { coefficient := -1, powers := [(5, 1), (20, 1), (32, 1), (55, 1), (57, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (20, 1), (35, 1), (42, 1), (54, 1), (61, 1)] }, { coefficient := -1, powers := [(5, 1), (25, 1), (32, 1), (42, 1), (57, 1), (61, 1)] }, { coefficient := -1, powers := [(5, 1), (32, 1), (33, 1), (36, 1), (57, 1), (61, 1)] }],
  [{ coefficient := -3, powers := [(19, 1), (24, 1), (61, 1)] }],
  [{ coefficient := 2, powers := [(54, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (6, 1), (20, 1), (32, 1), (48, 1), (57, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (6, 1), (26, 1), (35, 1), (48, 1), (50, 1), (58, 1)] }, { coefficient := 1, powers := [(48, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (6, 1), (12, 1), (20, 1), (29, 1), (32, 1), (48, 1), (57, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (6, 1), (12, 1), (26, 1), (29, 1), (35, 1), (48, 1), (50, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (25, 1), (32, 1), (57, 1)] }, { coefficient := -1, powers := [(5, 1), (25, 1), (35, 1), (54, 1)] }],
  [{ coefficient := -2, powers := [(20, 1), (24, 1), (26, 1), (52, 1)] }, { coefficient := -1, powers := [(20, 1), (24, 1), (52, 1), (53, 1), (62, 1)] }, { coefficient := -2, powers := [(24, 1), (25, 1), (26, 1), (52, 1)] }, { coefficient := -1, powers := [(24, 1), (25, 1), (52, 1), (53, 1), (62, 1)] }, { coefficient := 4, powers := [(24, 1), (26, 1), (50, 1)] }, { coefficient := 1, powers := [(24, 1), (50, 1), (53, 1), (62, 1)] }],
  [{ coefficient := 2, powers := [(5, 1), (9, 1), (20, 1), (35, 1)] }, { coefficient := -1, powers := [(5, 1), (20, 1), (35, 1), (49, 1)] }, { coefficient := -1, powers := [(5, 1), (30, 1), (35, 1), (36, 1)] }],
  [{ coefficient := 2, powers := [(19, 1), (29, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (30, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (33, 1), (54, 1)] }],
  [{ coefficient := -2, powers := [(24, 1), (43, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(29, 1)] }],
  [{ coefficient := 1, powers := [(24, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (6, 1), (19, 1), (20, 1), (32, 1), (57, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (6, 1), (19, 1), (26, 1), (35, 1), (50, 1), (58, 1)] }, { coefficient := 1, powers := [(19, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (25, 1), (29, 1), (30, 1), (55, 1)] }, { coefficient := -2, powers := [(18, 1), (24, 1), (25, 1), (53, 1)] }, { coefficient := -1, powers := [(18, 1), (24, 1), (26, 1)] }, { coefficient := -1, powers := [(18, 1), (24, 1), (53, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (30, 1), (35, 1), (36, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (29, 1), (30, 1), (55, 1)] }],
  [{ coefficient := 2, powers := [(5, 1), (9, 1), (26, 1), (35, 1)] }],
  [{ coefficient := 2, powers := [(19, 1), (21, 1), (29, 1)] }],
  [{ coefficient := 2, powers := [(12, 1), (24, 1), (43, 1)] }, { coefficient := -2, powers := [(19, 1), (24, 1), (50, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (24, 1), (26, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (30, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (6, 1), (12, 1), (20, 1), (32, 1), (57, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (6, 1), (12, 1), (26, 1), (35, 1), (50, 1), (58, 1)] }, { coefficient := 1, powers := [(12, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (32, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(41, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (9, 1), (35, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (49, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (26, 1), (35, 1), (44, 1), (50, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (42, 1), (57, 1)] }, { coefficient := -1, powers := [(5, 1), (35, 1), (42, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (24, 1)] }],
  [{ coefficient := -2, powers := [(19, 1), (29, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (26, 1), (35, 1), (50, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (32, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (6, 1), (20, 1), (32, 1), (57, 1), (58, 1)] }, { coefficient := -1, powers := [(5, 1), (6, 1), (26, 1), (35, 1), (50, 1), (58, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 3, powers := [(5, 1), (9, 1), (13, 1), (35, 1), (54, 1)] }, { coefficient := -2, powers := [(5, 1), (9, 1), (20, 1), (35, 1), (44, 1), (54, 1)] }, { coefficient := -1, powers := [(5, 1), (9, 1), (35, 1), (42, 1), (54, 1)] }, { coefficient := 2, powers := [(5, 1), (9, 1), (35, 1), (54, 1), (55, 1)] }, { coefficient := -1, powers := [(5, 1), (13, 1), (35, 1), (49, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (20, 1), (35, 1), (44, 1), (49, 1), (54, 1)] }, { coefficient := -1, powers := [(5, 1), (25, 1), (29, 1), (30, 1), (37, 1), (55, 1), (60, 1)] }, { coefficient := -1, powers := [(5, 1), (25, 1), (29, 1), (30, 1), (46, 1), (52, 1), (55, 1)] }, { coefficient := -1, powers := [(5, 1), (30, 1), (35, 1), (36, 1), (42, 1), (51, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (35, 1), (36, 1), (44, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (36, 1), (57, 1), (58, 1)] }, { coefficient := -1, powers := [(5, 1), (32, 1), (42, 1), (49, 1), (57, 1)] }, { coefficient := -1, powers := [(5, 1), (35, 1), (36, 1), (54, 1), (58, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (26, 1), (46, 1), (51, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (40, 1), (57, 1)] }, { coefficient := -2, powers := [(12, 1), (24, 1), (43, 1), (45, 1), (53, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (46, 1), (53, 1)] }, { coefficient := 2, powers := [(18, 1), (24, 1), (25, 1), (37, 1), (53, 1), (60, 1)] }, { coefficient := 2, powers := [(18, 1), (24, 1), (25, 1), (46, 1), (52, 1), (53, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (26, 1), (37, 1), (60, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (26, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (37, 1), (53, 1), (60, 1), (62, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (46, 1), (52, 1), (53, 1), (62, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (46, 1), (54, 1)] }, { coefficient := -1, powers := [(18, 1), (29, 1), (48, 1), (52, 1)] }, { coefficient := -2, powers := [(19, 1), (21, 1), (29, 1), (45, 1), (52, 1)] }, { coefficient := 2, powers := [(19, 1), (24, 1), (45, 1), (50, 1), (53, 1)] }, { coefficient := 2, powers := [(19, 1), (24, 1), (51, 1), (54, 1)] }, { coefficient := 2, powers := [(19, 1), (29, 1), (41, 1), (56, 1)] }, { coefficient := -2, powers := [(19, 1), (29, 1), (45, 1), (47, 1), (50, 1)] }, { coefficient := 2, powers := [(19, 1), (29, 1), (47, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (13, 1), (20, 1), (35, 1), (49, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (20, 1), (32, 1), (42, 1), (49, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (20, 1), (32, 1), (49, 1), (55, 1), (57, 1)] }, { coefficient := -1, powers := [(5, 1), (20, 1), (35, 1), (42, 1), (49, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (25, 1), (32, 1), (42, 1), (49, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (33, 1), (36, 1), (49, 1), (57, 1)] }, { coefficient := 2, powers := [(12, 1), (29, 1), (48, 1)] }, { coefficient := 3, powers := [(19, 1), (24, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (6, 1), (20, 1), (32, 1), (38, 1), (57, 1), (58, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (6, 1), (20, 1), (32, 1), (41, 1), (57, 2), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (6, 1), (26, 1), (35, 1), (38, 1), (50, 1), (58, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (6, 1), (26, 1), (35, 1), (41, 1), (50, 1), (57, 1), (58, 1)] }, { coefficient := 1, powers := [(21, 1), (43, 1), (52, 1), (53, 1)] }, { coefficient := 1, powers := [(38, 1), (60, 1)] }, { coefficient := -1, powers := [(40, 1), (41, 1), (57, 1), (62, 1)] }, { coefficient := 1, powers := [(41, 1), (57, 1)] }, { coefficient := -2, powers := [(48, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (5, 1), (35, 1), (54, 1), (55, 1)] }, { coefficient := -1, powers := [(5, 1), (6, 1), (12, 1), (13, 1), (20, 1), (29, 1), (32, 1), (48, 1), (57, 1), (59, 1)] }, { coefficient := -1, powers := [(5, 1), (6, 1), (12, 1), (13, 1), (26, 1), (29, 1), (35, 1), (48, 1), (50, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (6, 1), (12, 1), (20, 1), (29, 1), (32, 1), (42, 1), (48, 1), (57, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (6, 1), (12, 1), (26, 1), (29, 1), (35, 1), (42, 1), (48, 1), (50, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (6, 1), (18, 1), (20, 1), (24, 1), (26, 1), (32, 1), (44, 1), (57, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (6, 1), (18, 1), (20, 1), (26, 1), (32, 1), (35, 1), (41, 1), (44, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (6, 1), (18, 1), (24, 1), (26, 2), (35, 1), (44, 1), (50, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (6, 1), (18, 1), (26, 2), (35, 2), (41, 1), (44, 1), (50, 1)] }, { coefficient := 1, powers := [(5, 1), (6, 1), (32, 1), (33, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (13, 1), (15, 1), (20, 1), (27, 1), (35, 1), (54, 1), (61, 1)] }, { coefficient := -1, powers := [(5, 1), (13, 1), (26, 1), (35, 1), (50, 1)] }, { coefficient := 1, powers := [(5, 1), (15, 1), (20, 1), (27, 1), (32, 1), (42, 1), (57, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (15, 1), (20, 1), (27, 1), (32, 1), (55, 1), (57, 1), (61, 1)] }, { coefficient := -1, powers := [(5, 1), (15, 1), (20, 1), (27, 1), (35, 1), (42, 1), (54, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (15, 1), (25, 1), (27, 1), (32, 1), (42, 1), (57, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (15, 1), (27, 1), (32, 1), (33, 1), (36, 1), (57, 1), (61, 1)] }, { coefficient := -1, powers := [(5, 1), (25, 1), (26, 1), (32, 1), (42, 1), (46, 1)] }, { coefficient := -1, powers := [(5, 1), (25, 1), (26, 1), (35, 1), (44, 1), (50, 1)] }, { coefficient := -1, powers := [(5, 1), (25, 1), (32, 1), (42, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (25, 1), (35, 1), (42, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (26, 1), (32, 1), (33, 1), (36, 1), (46, 1)] }, { coefficient := -1, powers := [(5, 1), (26, 1), (35, 1), (50, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (6, 1), (20, 1), (35, 1), (54, 1), (58, 1)] }, { coefficient := -1, powers := [(8, 1), (35, 1), (41, 1)] }, { coefficient := -1, powers := [(12, 1), (24, 1), (43, 1), (53, 1)] }, { coefficient := -1, powers := [(19, 1), (29, 1), (41, 1)] }]
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
    ¬ ∀ index : Fin 73,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component60.SelectedLeafB2_3.selectedHasNoCommonZero

end Krenn.Component60.SelectedLeafB2_3
