import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component37.SelectedLeafB5_0_0

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "fb7147c430830e638340e53287130dc004895770b7a48724a0b182a012edeca0"
def certificateSHA256 : String := "e87888107a710f7ca904695a4f70068682fd5d8944f0a901586704625c3a28b5"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 48 → Fin 667 := ![
  6,
  13,
  17,
  148,
  149,
  168,
  175,
  176,
  179,
  180,
  216,
  222,
  256,
  280,
  294,
  295,
  296,
  300,
  301,
  307,
  310,
  334,
  393,
  411,
  433,
  438,
  446,
  450,
  469,
  481,
  482,
  573,
  583,
  591,
  602,
  603,
  612,
  647,
  655,
  657,
  658,
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
def selectedEquations : Fin 48 → SparsePoly (Fin 64) := ![
  [{ coefficient := 1, powers := [(5, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (31, 1)] }, { coefficient := 1, powers := [(18, 1), (26, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (26, 1)] }, { coefficient := 1, powers := [(26, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (26, 1)] }, { coefficient := 1, powers := [(18, 1), (20, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (20, 1)] }, { coefficient := 1, powers := [(18, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (44, 1)] }, { coefficient := 1, powers := [(19, 1), (20, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (55, 1)] }, { coefficient := 1, powers := [(30, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (44, 1)] }, { coefficient := 1, powers := [(28, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (31, 1), (45, 1)] }, { coefficient := 1, powers := [(8, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (26, 1), (48, 1)] }, { coefficient := 1, powers := [(31, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (25, 1), (46, 1)] }, { coefficient := 1, powers := [(18, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (25, 1), (49, 1)] }, { coefficient := 1, powers := [(19, 1), (21, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1)] }, { coefficient := 1, powers := [(20, 1), (44, 1)] }, { coefficient := 1, powers := [(25, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (49, 1)] }, { coefficient := 1, powers := [(21, 1), (44, 1)] }, { coefficient := 1, powers := [(25, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (51, 1)] }, { coefficient := 1, powers := [(20, 1), (51, 1)] }, { coefficient := 1, powers := [(25, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (50, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (50, 1)] }, { coefficient := 1, powers := [(18, 1), (28, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (59, 1)] }, { coefficient := 1, powers := [(9, 1), (43, 1)] }, { coefficient := 1, powers := [(13, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (46, 1)] }, { coefficient := 1, powers := [(12, 1), (57, 1)] }, { coefficient := 1, powers := [(18, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (41, 1)] }, { coefficient := 1, powers := [(19, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (39, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (59, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (20, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1)] }, { coefficient := 1, powers := [(18, 1), (20, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (25, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (25, 1), (41, 1)] }, { coefficient := 1, powers := [(19, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (49, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1)] }, { coefficient := 1, powers := [(18, 1), (28, 1), (49, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1)] }, { coefficient := 1, powers := [(12, 1), (30, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (61, 1)] }, { coefficient := 1, powers := [(12, 1), (49, 1)] }, { coefficient := 1, powers := [(19, 1), (21, 1), (53, 1)] }, { coefficient := 1, powers := [(19, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (61, 1)] }, { coefficient := 1, powers := [(12, 1), (26, 1), (47, 1)] }, { coefficient := 1, powers := [(12, 1), (58, 1)] }, { coefficient := 1, powers := [(19, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1), (54, 1)] }, { coefficient := 1, powers := [(13, 1), (26, 1), (41, 1)] }, { coefficient := 1, powers := [(13, 1), (54, 1)] }, { coefficient := 1, powers := [(26, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (49, 1), (50, 1)] }, { coefficient := 1, powers := [(6, 1), (31, 1), (49, 1)] }, { coefficient := 1, powers := [(9, 1), (25, 1), (49, 1)] }, { coefficient := 1, powers := [(21, 1), (44, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (49, 1), (53, 1)] }, { coefficient := 1, powers := [(21, 1), (44, 1), (53, 1)] }, { coefficient := 1, powers := [(42, 1), (44, 1)] }, { coefficient := 1, powers := [(49, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (21, 1), (45, 1), (54, 1)] }, { coefficient := 1, powers := [(13, 1), (21, 1), (54, 1)] }, { coefficient := 1, powers := [(21, 1), (26, 1), (45, 1)] }, { coefficient := 1, powers := [(34, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (31, 1), (57, 1)] }, { coefficient := 1, powers := [(9, 1), (20, 1), (57, 1)] }, { coefficient := 1, powers := [(9, 1)] }, { coefficient := 1, powers := [(40, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (37, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (40, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (43, 1), (50, 1)] }, { coefficient := 1, powers := [(17, 1), (23, 1), (50, 1)] }, { coefficient := 1, powers := [(17, 1), (28, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1)] }, { coefficient := 1, powers := [(3, 1), (34, 1)] }, { coefficient := 1, powers := [(13, 1), (20, 1)] }, { coefficient := 1, powers := [(20, 1), (56, 1)] }, { coefficient := 1, powers := [(25, 1), (43, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (50, 1)] }, { coefficient := 1, powers := [(6, 1), (31, 1)] }, { coefficient := 1, powers := [(9, 1), (25, 1)] }, { coefficient := 1, powers := [(20, 1), (50, 1)] }, { coefficient := 1, powers := [(25, 1), (40, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1), (50, 1)] }, { coefficient := 1, powers := [(6, 1), (31, 1), (45, 1)] }, { coefficient := 1, powers := [(6, 1), (59, 1)] }, { coefficient := 1, powers := [(9, 1), (25, 1), (45, 1)] }, { coefficient := 1, powers := [(9, 1), (56, 1)] }, { coefficient := 1, powers := [(13, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (41, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (45, 1)] }, { coefficient := 1, powers := [(6, 1), (34, 1), (41, 1)] }, { coefficient := 1, powers := [(13, 1), (25, 1), (41, 1)] }, { coefficient := 1, powers := [(13, 1)] }, { coefficient := 1, powers := [(25, 1), (45, 1)] }, { coefficient := 1, powers := [(56, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (37, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (40, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (43, 1), (50, 1)] }, { coefficient := 1, powers := [(3, 1), (25, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (31, 1), (56, 1)] }, { coefficient := 1, powers := [(3, 1), (34, 1), (50, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (31, 1), (43, 1)] }, { coefficient := 1, powers := [(6, 1), (34, 1), (40, 1)] }, { coefficient := 1, powers := [(9, 1), (20, 1), (56, 1)] }, { coefficient := 1, powers := [(9, 1), (25, 1), (43, 1)] }, { coefficient := 1, powers := [(9, 1), (34, 1), (37, 1)] }, { coefficient := 1, powers := [(13, 1), (20, 1), (50, 1)] }, { coefficient := 1, powers := [(13, 1), (25, 1), (40, 1)] }, { coefficient := 1, powers := [(13, 1), (31, 1), (37, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (39, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (42, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (49, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (49, 1)] }, { coefficient := 1, powers := [(8, 1), (36, 1), (42, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (58, 1)] }, { coefficient := 1, powers := [(12, 1), (30, 1), (49, 1)] }, { coefficient := 1, powers := [(12, 1), (36, 1), (39, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (55, 1)] }, { coefficient := 1, powers := [(19, 1), (30, 1), (42, 1)] }, { coefficient := 1, powers := [(19, 1), (33, 1), (39, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(40, 1)] }],
  [{ coefficient := 1, powers := [(41, 1)] }],
  [{ coefficient := 1, powers := [(42, 1)] }],
  [{ coefficient := 1, powers := [(56, 1)] }],
  [{ coefficient := 1, powers := [(57, 1)] }],
  [{ coefficient := 1, powers := [(58, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 48 → SparsePoly (Fin 64) := ![
  [{ coefficient := -1, powers := [(0, 1), (2, 1), (30, 1), (37, 1), (61, 1), (63, 1)] }, { coefficient := -1, powers := [(2, 1), (6, 1), (20, 1), (30, 1), (61, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (21, 1), (23, 1), (44, 1), (55, 1), (63, 1)] }, { coefficient := -1, powers := [(2, 1), (23, 1), (25, 1), (49, 1), (55, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (13, 1), (20, 1), (23, 1), (39, 1), (61, 1), (63, 1)] }, { coefficient := -1, powers := [(2, 1), (13, 1), (20, 1), (23, 1), (49, 1), (55, 1), (63, 1)] }, { coefficient := 1, powers := [(2, 1), (13, 1), (21, 1), (23, 1), (44, 1), (55, 1), (63, 1)] }, { coefficient := 1, powers := [(2, 1), (20, 1), (23, 1), (39, 1), (43, 1), (61, 1), (63, 1)] }, { coefficient := 1, powers := [(2, 1), (21, 1), (23, 1), (43, 1), (44, 1), (55, 1), (63, 1)] }, { coefficient := 1, powers := [(2, 1), (23, 1), (25, 1), (43, 1), (49, 1), (55, 1), (63, 1)] }, { coefficient := -1, powers := [(2, 1), (23, 1), (34, 1), (37, 1), (49, 1), (55, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (2, 1), (24, 1), (37, 1), (45, 1), (61, 1), (63, 1)] }, { coefficient := 1, powers := [(2, 1), (6, 1), (20, 1), (24, 1), (45, 1), (61, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (13, 1), (37, 1), (48, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (37, 1), (43, 1), (48, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(24, 1), (47, 1)] }],
  [{ coefficient := -1, powers := [(24, 1), (44, 1), (55, 1), (62, 1)] }, { coefficient := 1, powers := [(24, 1), (47, 1), (55, 1)] }, { coefficient := -1, powers := [(30, 1), (49, 1), (51, 1), (62, 1)] }, { coefficient := 1, powers := [(30, 1), (49, 1), (53, 1)] }, { coefficient := -1, powers := [(33, 1), (39, 1), (44, 1), (62, 1)] }, { coefficient := -1, powers := [(33, 1), (39, 1), (47, 1)] }, { coefficient := -1, powers := [(36, 1), (39, 1), (51, 1), (62, 1)] }, { coefficient := -1, powers := [(36, 1), (39, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(33, 1), (39, 1)] }],
  [{ coefficient := -1, powers := [(18, 1), (49, 1)] }],
  [{ coefficient := -1, powers := [(18, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (2, 1), (24, 1), (37, 1), (61, 1), (63, 1)] }, { coefficient := -1, powers := [(2, 1), (6, 1), (20, 1), (24, 1), (61, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (13, 1), (37, 1), (61, 1)] }, { coefficient := -1, powers := [(2, 1), (37, 1), (43, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(30, 1), (49, 1)] }, { coefficient := -1, powers := [(36, 1), (39, 1)] }],
  [{ coefficient := -1, powers := [(30, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (24, 1), (55, 1), (62, 1)] }, { coefficient := 1, powers := [(18, 1), (33, 1), (39, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (20, 1), (45, 1), (50, 1), (55, 1)] }, { coefficient := -1, powers := [(2, 1), (37, 1), (55, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (43, 1), (50, 1), (55, 1)] }, { coefficient := 1, powers := [(18, 1), (30, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (30, 1), (49, 1), (62, 1)] }, { coefficient := 1, powers := [(18, 1), (36, 1), (39, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (13, 1), (20, 1), (39, 1), (61, 1), (63, 1)] }, { coefficient := 1, powers := [(2, 1), (13, 1), (20, 1), (49, 1), (55, 1), (63, 1)] }, { coefficient := -1, powers := [(2, 1), (13, 1), (21, 1), (44, 1), (55, 1), (63, 1)] }, { coefficient := -1, powers := [(2, 1), (20, 1), (39, 1), (43, 1), (61, 1), (63, 1)] }, { coefficient := -1, powers := [(2, 1), (21, 1), (43, 1), (44, 1), (55, 1), (63, 1)] }, { coefficient := -1, powers := [(2, 1), (25, 1), (43, 1), (49, 1), (55, 1), (63, 1)] }, { coefficient := 1, powers := [(2, 1), (34, 1), (37, 1), (49, 1), (55, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (25, 1), (39, 1), (61, 1)] }, { coefficient := -1, powers := [(2, 1), (25, 1), (49, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(25, 1), (30, 1), (49, 1)] }, { coefficient := 1, powers := [(25, 1), (36, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (33, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (2, 1), (37, 1), (61, 1), (63, 1)] }, { coefficient := 1, powers := [(2, 1), (6, 1), (20, 1), (61, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(30, 1), (49, 1)] }, { coefficient := 1, powers := [(36, 1), (39, 1)] }],
  [{ coefficient := -1, powers := [(24, 1), (55, 1)] }, { coefficient := 1, powers := [(33, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(55, 1)] }],
  [{ coefficient := 1, powers := [(49, 1)] }],
  [{ coefficient := 1, powers := [(30, 1)] }],
  [{ coefficient := 1, powers := [(24, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (3, 1), (21, 1), (50, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (13, 1), (55, 1)] }, { coefficient := 1, powers := [(2, 1), (20, 1), (45, 1), (55, 1)] }, { coefficient := -1, powers := [(2, 1), (43, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(18, 1), (30, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (3, 1), (50, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (25, 1), (39, 1), (43, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (25, 1), (43, 1), (49, 1), (55, 1)] }, { coefficient := 1, powers := [(2, 1), (34, 1), (37, 1), (39, 1), (61, 1)] }, { coefficient := -1, powers := [(2, 1), (34, 1), (37, 1), (49, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (21, 1), (44, 1), (55, 1), (63, 1)] }, { coefficient := 1, powers := [(2, 1), (25, 1), (49, 1), (55, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (49, 1), (50, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (13, 1), (49, 1), (55, 1)] }, { coefficient := 1, powers := [(2, 1), (39, 1), (43, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (20, 1), (49, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (20, 1), (49, 1), (50, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (39, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (49, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(18, 1), (24, 1), (44, 1), (55, 1)] }, { coefficient := -1, powers := [(18, 1), (30, 1), (49, 1), (51, 1)] }, { coefficient := -1, powers := [(18, 1), (33, 1), (39, 1), (44, 1)] }, { coefficient := -1, powers := [(18, 1), (36, 1), (39, 1), (51, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (2, 1), (37, 1), (39, 1), (59, 1), (61, 1)] }, { coefficient := -1, powers := [(2, 1), (6, 1), (20, 1), (39, 1), (59, 1), (61, 1)] }, { coefficient := -1, powers := [(2, 1), (13, 1), (20, 1), (39, 1), (50, 1), (61, 1)] }, { coefficient := -1, powers := [(2, 1), (13, 1), (20, 1), (49, 1), (50, 1), (55, 1)] }, { coefficient := 1, powers := [(2, 1), (13, 1), (21, 1), (44, 1), (50, 1), (55, 1)] }, { coefficient := 1, powers := [(2, 1), (20, 1), (39, 1), (43, 1), (50, 1), (61, 1)] }, { coefficient := -1, powers := [(2, 1), (21, 1), (37, 1), (44, 1), (55, 1), (59, 1)] }, { coefficient := -1, powers := [(2, 1), (25, 1), (37, 1), (49, 1), (55, 1), (59, 1)] }, { coefficient := -1, powers := [(2, 1), (34, 1), (37, 1), (49, 1), (50, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (2, 1), (18, 1), (24, 1), (26, 1), (37, 1), (45, 1), (61, 1), (63, 1)] }, { coefficient := 1, powers := [(0, 1), (2, 1), (25, 1), (39, 1), (43, 1), (57, 1), (61, 1)] }, { coefficient := -1, powers := [(0, 1), (2, 1), (25, 1), (43, 1), (49, 1), (55, 1), (57, 1)] }, { coefficient := -1, powers := [(0, 1), (2, 1), (34, 1), (37, 1), (39, 1), (57, 1), (61, 1)] }, { coefficient := 1, powers := [(0, 1), (2, 1), (34, 1), (37, 1), (49, 1), (55, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (2, 1), (39, 1), (56, 1), (61, 1)] }, { coefficient := -1, powers := [(0, 1), (2, 1), (49, 1), (55, 1), (56, 1)] }, { coefficient := -1, powers := [(2, 2), (21, 1), (44, 1), (55, 1), (56, 1), (63, 1)] }, { coefficient := -1, powers := [(2, 2), (25, 1), (49, 1), (55, 1), (56, 1), (63, 1)] }, { coefficient := -1, powers := [(2, 1), (6, 1), (18, 1), (20, 1), (24, 1), (26, 1), (45, 1), (61, 1), (63, 1)] }, { coefficient := 1, powers := [(2, 1), (6, 1), (34, 1), (39, 1), (61, 1)] }, { coefficient := -1, powers := [(2, 1), (6, 1), (34, 1), (49, 1), (55, 1)] }, { coefficient := -1, powers := [(2, 1), (13, 1), (18, 1), (20, 1), (28, 1), (39, 1), (61, 1), (63, 1)] }, { coefficient := -1, powers := [(2, 1), (13, 1), (18, 1), (20, 1), (28, 1), (49, 1), (55, 1), (63, 1)] }, { coefficient := 1, powers := [(2, 1), (13, 1), (18, 1), (21, 1), (28, 1), (44, 1), (55, 1), (63, 1)] }, { coefficient := 1, powers := [(2, 1), (13, 1), (25, 1), (49, 1), (55, 1)] }, { coefficient := 1, powers := [(2, 1), (13, 1), (26, 1), (37, 1), (48, 1), (61, 1)] }, { coefficient := -1, powers := [(2, 1), (17, 1), (21, 1), (28, 1), (44, 1), (55, 1), (63, 1)] }, { coefficient := -1, powers := [(2, 1), (17, 1), (25, 1), (28, 1), (49, 1), (55, 1), (63, 1)] }, { coefficient := 1, powers := [(2, 1), (18, 1), (20, 1), (28, 1), (39, 1), (43, 1), (61, 1), (63, 1)] }, { coefficient := 1, powers := [(2, 1), (18, 1), (21, 1), (28, 1), (43, 1), (44, 1), (55, 1), (63, 1)] }, { coefficient := 1, powers := [(2, 1), (18, 1), (25, 1), (28, 1), (43, 1), (49, 1), (55, 1), (63, 1)] }, { coefficient := -1, powers := [(2, 1), (18, 1), (28, 1), (34, 1), (37, 1), (49, 1), (55, 1), (63, 1)] }, { coefficient := -1, powers := [(2, 1), (25, 1), (43, 1), (49, 1), (55, 1)] }, { coefficient := -1, powers := [(2, 1), (26, 1), (37, 1), (43, 1), (48, 1), (61, 1)] }, { coefficient := -1, powers := [(2, 1), (34, 1), (37, 1), (39, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (34, 1), (37, 1), (49, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (2, 1), (20, 1), (49, 1), (50, 1), (55, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (3, 1), (13, 1), (21, 1), (26, 1), (50, 1), (61, 1)] }, { coefficient := -1, powers := [(2, 1), (6, 1), (20, 1), (34, 1), (49, 1), (50, 1), (55, 1)] }, { coefficient := -1, powers := [(2, 1), (13, 1), (20, 1), (25, 1), (49, 1), (50, 1), (55, 1)] }, { coefficient := -1, powers := [(19, 1), (20, 1), (33, 1), (39, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (25, 1), (55, 1)] }, { coefficient := -1, powers := [(19, 1), (25, 1), (33, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (58, 1)] }, { coefficient := 1, powers := [(8, 1), (36, 1)] }, { coefficient := 1, powers := [(18, 1), (30, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (3, 1), (31, 1), (39, 1), (61, 1)] }, { coefficient := -1, powers := [(2, 1), (3, 1), (31, 1), (49, 1), (55, 1)] }, { coefficient := 1, powers := [(2, 1), (9, 1), (20, 1), (39, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (3, 1), (25, 1), (31, 1), (39, 1), (43, 1), (61, 1)] }, { coefficient := -1, powers := [(2, 1), (3, 1), (25, 1), (31, 1), (43, 1), (49, 1), (55, 1)] }, { coefficient := -1, powers := [(2, 1), (3, 1), (31, 1), (34, 1), (37, 1), (39, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (3, 1), (31, 1), (34, 1), (37, 1), (49, 1), (55, 1)] }, { coefficient := 1, powers := [(2, 1), (9, 1), (20, 1), (25, 1), (39, 1), (43, 1), (61, 1)] }, { coefficient := -1, powers := [(2, 1), (9, 1), (20, 1), (25, 1), (43, 1), (49, 1), (55, 1)] }, { coefficient := -1, powers := [(2, 1), (9, 1), (20, 1), (34, 1), (37, 1), (39, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (9, 1), (20, 1), (34, 1), (37, 1), (49, 1), (55, 1)] }, { coefficient := 1, powers := [(12, 1), (20, 1), (30, 1), (49, 1)] }, { coefficient := -1, powers := [(12, 1), (20, 1), (36, 1), (39, 1)] }, { coefficient := 1, powers := [(12, 1), (25, 1), (30, 1), (49, 1)] }, { coefficient := -1, powers := [(12, 1), (25, 1), (36, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (33, 1)] }]
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
    ¬ ∀ index : Fin 48,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component37.SelectedLeafB5_0_0.selectedHasNoCommonZero

end Krenn.Component37.SelectedLeafB5_0_0
