import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component37.SelectedLeafB6_4_1

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "d4731b670011a4fae2b68c7b70e0df0f7f7ee54c1d70e8ec77549e7e1507cc0c"
def certificateSHA256 : String := "dbe32e772bbfcd4e84efcf4e5749fcd55ef370ca2f55e534d6eac3884db250d7"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 31 → Fin 667 := ![
  1,
  3,
  4,
  5,
  7,
  16,
  19,
  23,
  171,
  175,
  183,
  283,
  298,
  359,
  393,
  426,
  446,
  447,
  450,
  484,
  502,
  566,
  580,
  657,
  659,
  660,
  661,
  662,
  663,
  665,
  666
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 31 → SparsePoly (Fin 66) := ![
  [{ coefficient := 1, powers := [(1, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (35, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (32, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (20, 1)] }, { coefficient := 1, powers := [(18, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(28, 1), (53, 1)] }, { coefficient := -1, powers := [(29, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (44, 1), (54, 1)] }, { coefficient := 1, powers := [(22, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (46, 1)] }, { coefficient := 1, powers := [(4, 1), (35, 1)] }, { coefficient := 1, powers := [(15, 1), (22, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (32, 1), (58, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (49, 1)] }, { coefficient := 1, powers := [(19, 1), (32, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (20, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1)] }, { coefficient := 1, powers := [(18, 1), (20, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (53, 1)] }, { coefficient := 1, powers := [(20, 1), (51, 1), (57, 1)] }, { coefficient := 1, powers := [(20, 1), (53, 1)] }, { coefficient := 1, powers := [(51, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (61, 1)] }, { coefficient := 1, powers := [(12, 1), (49, 1)] }, { coefficient := 1, powers := [(19, 1), (21, 1), (53, 1)] }, { coefficient := 1, powers := [(19, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (33, 1)] }, { coefficient := 1, powers := [(23, 1), (51, 1)] }, { coefficient := 1, powers := [(28, 1), (51, 1)] }, { coefficient := 1, powers := [(33, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (61, 1)] }, { coefficient := 1, powers := [(12, 1), (26, 1), (47, 1)] }, { coefficient := 1, powers := [(12, 1), (58, 1)] }, { coefficient := 1, powers := [(19, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (37, 1), (60, 1)] }, { coefficient := 1, powers := [(1, 1)] }, { coefficient := 1, powers := [(10, 1), (35, 1), (37, 1)] }, { coefficient := 1, powers := [(15, 1), (32, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (33, 1), (57, 1)] }, { coefficient := 1, powers := [(23, 1), (51, 1), (57, 1)] }, { coefficient := 1, powers := [(23, 1), (53, 1)] }, { coefficient := 1, powers := [(29, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (44, 1), (54, 1)] }, { coefficient := 1, powers := [(24, 1), (58, 1)] }, { coefficient := 1, powers := [(30, 1), (49, 1)] }, { coefficient := 1, powers := [(36, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1)] }, { coefficient := 1, powers := [(6, 1), (60, 1)] }, { coefficient := 1, powers := [(25, 1), (41, 1)] }, { coefficient := 1, powers := [(25, 1), (46, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (39, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (42, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (49, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (49, 1)] }, { coefficient := 1, powers := [(8, 1), (36, 1), (42, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (58, 1)] }, { coefficient := 1, powers := [(12, 1), (30, 1), (49, 1)] }, { coefficient := 1, powers := [(12, 1), (36, 1), (39, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (55, 1)] }, { coefficient := 1, powers := [(19, 1), (30, 1), (42, 1)] }, { coefficient := 1, powers := [(19, 1), (33, 1), (39, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(40, 1), (64, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(41, 1)] }],
  [{ coefficient := 1, powers := [(42, 1)] }],
  [{ coefficient := 1, powers := [(57, 1)] }],
  [{ coefficient := 1, powers := [(58, 1), (65, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 31 → SparsePoly (Fin 66) := ![
  [{ coefficient := 1, powers := [(0, 1), (4, 1), (8, 1), (33, 1), (35, 1), (63, 2)] }, { coefficient := -1, powers := [(0, 1), (4, 1), (12, 1), (30, 1), (35, 1), (63, 2)] }, { coefficient := 1, powers := [(4, 1), (8, 1), (25, 1), (33, 1), (35, 1), (63, 2)] }, { coefficient := -1, powers := [(4, 1), (12, 1), (25, 1), (30, 1), (35, 1), (63, 2)] }, { coefficient := -1, powers := [(6, 1), (8, 1), (33, 1), (58, 1), (60, 1), (63, 1), (65, 1)] }, { coefficient := 1, powers := [(6, 1), (12, 1), (30, 1), (58, 1), (60, 1), (63, 1), (65, 1)] }, { coefficient := -1, powers := [(8, 1), (10, 1), (33, 1), (35, 1), (37, 1), (63, 2)] }, { coefficient := -1, powers := [(8, 1), (15, 1), (32, 1), (33, 1), (37, 1), (63, 2)] }, { coefficient := -1, powers := [(8, 1), (33, 1), (37, 1), (58, 1), (60, 1), (63, 1), (65, 1)] }, { coefficient := 1, powers := [(10, 1), (12, 1), (30, 1), (35, 1), (37, 1), (63, 2)] }, { coefficient := 1, powers := [(12, 1), (15, 1), (30, 1), (32, 1), (37, 1), (63, 2)] }, { coefficient := 1, powers := [(12, 1), (30, 1), (37, 1), (58, 1), (60, 1), (63, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (4, 1), (12, 1), (24, 1), (35, 1), (44, 1), (63, 2)] }, { coefficient := -1, powers := [(4, 1), (12, 1), (24, 1), (25, 1), (35, 1), (44, 1), (63, 2)] }, { coefficient := 1, powers := [(6, 1), (12, 1), (24, 1), (44, 1), (58, 1), (60, 1), (63, 1), (65, 1)] }, { coefficient := 1, powers := [(10, 1), (12, 1), (24, 1), (35, 1), (37, 1), (44, 1), (63, 2)] }, { coefficient := 1, powers := [(12, 1), (15, 1), (24, 1), (32, 1), (37, 1), (44, 1), (63, 2)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (37, 1), (44, 1), (58, 1), (60, 1), (63, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (4, 1), (5, 1), (35, 1), (36, 1), (63, 2)] }, { coefficient := 1, powers := [(4, 1), (5, 1), (25, 1), (35, 1), (36, 1), (63, 2)] }, { coefficient := -1, powers := [(5, 1), (6, 1), (36, 1), (58, 1), (60, 1), (63, 1), (65, 1)] }, { coefficient := -1, powers := [(5, 1), (10, 1), (35, 1), (36, 1), (37, 1), (63, 2)] }, { coefficient := -1, powers := [(5, 1), (15, 1), (32, 1), (36, 1), (37, 1), (63, 2)] }, { coefficient := -1, powers := [(5, 1), (36, 1), (37, 1), (58, 1), (60, 1), (63, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (4, 1), (33, 1), (58, 1), (63, 1)] }, { coefficient := 1, powers := [(4, 1), (25, 1), (33, 1), (58, 1), (63, 1)] }, { coefficient := -1, powers := [(10, 1), (33, 1), (37, 1), (58, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(15, 1), (33, 1), (37, 1), (49, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (4, 1), (24, 1), (25, 1), (35, 1), (53, 1), (58, 1), (63, 1), (64, 1)] }, { coefficient := -1, powers := [(4, 1), (24, 1), (25, 2), (35, 1), (53, 1), (58, 1), (63, 1), (64, 1)] }, { coefficient := 1, powers := [(6, 1), (24, 1), (25, 1), (53, 1), (58, 2), (60, 1), (64, 1), (65, 1)] }, { coefficient := 1, powers := [(10, 1), (24, 1), (25, 1), (35, 1), (37, 1), (53, 1), (58, 1), (63, 1), (64, 1)] }, { coefficient := 1, powers := [(15, 1), (24, 1), (25, 1), (32, 1), (37, 1), (53, 1), (58, 1), (63, 1), (64, 1)] }, { coefficient := 1, powers := [(24, 1), (25, 1), (37, 1), (53, 1), (58, 2), (60, 1), (64, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (4, 1), (21, 1), (30, 1), (35, 1), (53, 1), (63, 1), (64, 1)] }, { coefficient := 1, powers := [(0, 1), (4, 1), (24, 1), (26, 1), (35, 1), (53, 1), (63, 1), (64, 1)] }, { coefficient := 1, powers := [(0, 1), (4, 1), (33, 1), (35, 1), (39, 1), (63, 1), (64, 1)] }, { coefficient := -1, powers := [(4, 1), (21, 1), (25, 1), (30, 1), (35, 1), (53, 1), (63, 1), (64, 1)] }, { coefficient := 1, powers := [(4, 1), (24, 1), (25, 1), (26, 1), (35, 1), (53, 1), (63, 1), (64, 1)] }, { coefficient := 1, powers := [(4, 1), (25, 1), (33, 1), (35, 1), (39, 1), (63, 1), (64, 1)] }, { coefficient := 1, powers := [(6, 1), (21, 1), (30, 1), (53, 1), (58, 1), (60, 1), (64, 1), (65, 1)] }, { coefficient := -1, powers := [(6, 1), (24, 1), (26, 1), (53, 1), (58, 1), (60, 1), (64, 1), (65, 1)] }, { coefficient := -1, powers := [(6, 1), (33, 1), (39, 1), (58, 1), (60, 1), (64, 1), (65, 1)] }, { coefficient := 1, powers := [(10, 1), (21, 1), (30, 1), (35, 1), (37, 1), (53, 1), (63, 1), (64, 1)] }, { coefficient := -1, powers := [(10, 1), (24, 1), (26, 1), (35, 1), (37, 1), (53, 1), (63, 1), (64, 1)] }, { coefficient := -1, powers := [(10, 1), (33, 1), (35, 1), (37, 1), (39, 1), (63, 1), (64, 1)] }, { coefficient := 1, powers := [(15, 1), (21, 1), (30, 1), (32, 1), (37, 1), (53, 1), (63, 1), (64, 1)] }, { coefficient := -1, powers := [(15, 1), (24, 1), (26, 1), (32, 1), (37, 1), (53, 1), (63, 1), (64, 1)] }, { coefficient := 1, powers := [(21, 1), (30, 1), (37, 1), (53, 1), (58, 1), (60, 1), (64, 1), (65, 1)] }, { coefficient := -1, powers := [(24, 1), (26, 1), (37, 1), (53, 1), (58, 1), (60, 1), (64, 1), (65, 1)] }, { coefficient := -1, powers := [(33, 1), (37, 1), (39, 1), (58, 1), (60, 1), (64, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (15, 1), (44, 1), (63, 1), (65, 1)] }, { coefficient := -1, powers := [(15, 1), (25, 1), (44, 1), (63, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (4, 1), (24, 1), (26, 1), (35, 1), (63, 1)] }, { coefficient := -1, powers := [(4, 1), (24, 1), (25, 1), (26, 1), (35, 1), (63, 1)] }, { coefficient := 1, powers := [(6, 1), (24, 1), (26, 1), (58, 1), (60, 1), (65, 1)] }, { coefficient := 1, powers := [(10, 1), (24, 1), (26, 1), (35, 1), (37, 1), (63, 1)] }, { coefficient := 1, powers := [(15, 1), (24, 1), (26, 1), (32, 1), (37, 1), (63, 1)] }, { coefficient := 1, powers := [(24, 1), (26, 1), (37, 1), (58, 1), (60, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (4, 1), (24, 1), (35, 1), (53, 1), (58, 1), (63, 1)] }, { coefficient := 1, powers := [(4, 1), (24, 1), (25, 1), (35, 1), (53, 1), (58, 1), (63, 1)] }, { coefficient := -1, powers := [(6, 1), (24, 1), (53, 1), (58, 2), (60, 1), (65, 1)] }, { coefficient := -1, powers := [(10, 1), (24, 1), (35, 1), (37, 1), (53, 1), (58, 1), (63, 1)] }, { coefficient := -1, powers := [(15, 1), (24, 1), (32, 1), (37, 1), (53, 1), (58, 1), (63, 1)] }, { coefficient := -1, powers := [(24, 1), (37, 1), (53, 1), (58, 2), (60, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (5, 1), (58, 1), (60, 1)] }, { coefficient := -1, powers := [(5, 1), (20, 1), (58, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (15, 1), (63, 1), (65, 1)] }, { coefficient := 1, powers := [(15, 1), (25, 1), (63, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (63, 1)] }, { coefficient := -1, powers := [(25, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(15, 1), (33, 1), (37, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (4, 1), (24, 1), (35, 1), (58, 1), (63, 1)] }, { coefficient := -1, powers := [(4, 1), (24, 1), (25, 1), (35, 1), (58, 1), (63, 1)] }, { coefficient := 1, powers := [(6, 1), (24, 1), (58, 2), (60, 1), (65, 1)] }, { coefficient := 1, powers := [(10, 1), (24, 1), (35, 1), (37, 1), (58, 1), (63, 1)] }, { coefficient := 1, powers := [(15, 1), (24, 1), (32, 1), (37, 1), (58, 1), (63, 1)] }, { coefficient := 1, powers := [(24, 1), (37, 1), (58, 2), (60, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (23, 1), (58, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (28, 1), (58, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (4, 1), (30, 1), (35, 1), (63, 1)] }, { coefficient := 1, powers := [(4, 1), (25, 1), (30, 1), (35, 1), (63, 1)] }, { coefficient := -1, powers := [(6, 1), (30, 1), (58, 1), (60, 1), (65, 1)] }, { coefficient := -1, powers := [(10, 1), (30, 1), (35, 1), (37, 1), (63, 1)] }, { coefficient := -1, powers := [(15, 1), (30, 1), (32, 1), (37, 1), (63, 1)] }, { coefficient := -1, powers := [(30, 1), (37, 1), (58, 1), (60, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (58, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (4, 1), (24, 1), (35, 1), (63, 1)] }, { coefficient := 1, powers := [(4, 1), (24, 1), (25, 1), (35, 1), (63, 1)] }, { coefficient := -1, powers := [(6, 1), (24, 1), (58, 1), (60, 1), (65, 1)] }, { coefficient := -1, powers := [(10, 1), (24, 1), (35, 1), (37, 1), (63, 1)] }, { coefficient := -1, powers := [(15, 1), (24, 1), (32, 1), (37, 1), (63, 1)] }, { coefficient := -1, powers := [(24, 1), (37, 1), (58, 1), (60, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(63, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (5, 1), (58, 1), (60, 1)] }, { coefficient := -1, powers := [(5, 1), (20, 1), (58, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (4, 1), (12, 1), (35, 1), (63, 1)] }, { coefficient := 1, powers := [(4, 1), (12, 1), (25, 1), (35, 1), (63, 1)] }, { coefficient := -1, powers := [(6, 1), (12, 1), (58, 1), (60, 1), (65, 1)] }, { coefficient := -1, powers := [(10, 1), (12, 1), (35, 1), (37, 1), (63, 1)] }, { coefficient := -1, powers := [(12, 1), (15, 1), (32, 1), (37, 1), (63, 1)] }, { coefficient := -1, powers := [(12, 1), (37, 1), (58, 1), (60, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [] }],
  [{ coefficient := -1, powers := [(0, 1), (4, 1), (35, 1), (63, 1)] }, { coefficient := -1, powers := [(4, 1), (25, 1), (35, 1), (63, 1)] }, { coefficient := 1, powers := [(6, 1), (58, 1), (60, 1), (65, 1)] }, { coefficient := 1, powers := [(10, 1), (35, 1), (37, 1), (63, 1)] }, { coefficient := 1, powers := [(15, 1), (32, 1), (37, 1), (63, 1)] }, { coefficient := 1, powers := [(37, 1), (58, 1), (60, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (4, 1), (5, 1), (35, 1), (36, 1), (55, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (4, 1), (8, 1), (33, 1), (35, 1), (49, 1), (63, 1)] }, { coefficient := 1, powers := [(0, 1), (4, 1), (12, 1), (24, 1), (35, 1), (44, 1), (54, 1), (63, 1)] }, { coefficient := 1, powers := [(0, 1), (4, 1), (12, 1), (30, 1), (35, 1), (49, 1), (63, 1)] }, { coefficient := 1, powers := [(0, 1), (46, 1)] }, { coefficient := -1, powers := [(4, 1), (5, 1), (25, 1), (35, 1), (36, 1), (55, 1), (63, 1)] }, { coefficient := -1, powers := [(4, 1), (8, 1), (25, 1), (33, 1), (35, 1), (49, 1), (63, 1)] }, { coefficient := 1, powers := [(4, 1), (12, 1), (24, 1), (25, 1), (35, 1), (44, 1), (54, 1), (63, 1)] }, { coefficient := 1, powers := [(4, 1), (12, 1), (25, 1), (30, 1), (35, 1), (49, 1), (63, 1)] }, { coefficient := 1, powers := [(5, 1), (6, 1), (36, 1), (55, 1), (58, 1), (60, 1), (65, 1)] }, { coefficient := 1, powers := [(5, 1), (10, 1), (35, 1), (36, 1), (37, 1), (55, 1), (63, 1)] }, { coefficient := 1, powers := [(5, 1), (15, 1), (32, 1), (36, 1), (37, 1), (55, 1), (63, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1), (37, 1), (55, 1), (58, 1), (60, 1), (65, 1)] }, { coefficient := 1, powers := [(6, 1), (8, 1), (33, 1), (49, 1), (58, 1), (60, 1), (65, 1)] }, { coefficient := -1, powers := [(6, 1), (12, 1), (24, 1), (44, 1), (54, 1), (58, 1), (60, 1), (65, 1)] }, { coefficient := -1, powers := [(6, 1), (12, 1), (30, 1), (49, 1), (58, 1), (60, 1), (65, 1)] }, { coefficient := 1, powers := [(8, 1), (10, 1), (33, 1), (35, 1), (37, 1), (49, 1), (63, 1)] }, { coefficient := 1, powers := [(8, 1), (15, 1), (32, 1), (33, 1), (37, 1), (49, 1), (63, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (37, 1), (49, 1), (58, 1), (60, 1), (65, 1)] }, { coefficient := -1, powers := [(10, 1), (12, 1), (24, 1), (35, 1), (37, 1), (44, 1), (54, 1), (63, 1)] }, { coefficient := -1, powers := [(10, 1), (12, 1), (30, 1), (35, 1), (37, 1), (49, 1), (63, 1)] }, { coefficient := -1, powers := [(12, 1), (15, 1), (24, 1), (32, 1), (37, 1), (44, 1), (54, 1), (63, 1)] }, { coefficient := -1, powers := [(12, 1), (15, 1), (30, 1), (32, 1), (37, 1), (49, 1), (63, 1)] }, { coefficient := -1, powers := [(12, 1), (24, 1), (37, 1), (44, 1), (54, 1), (58, 1), (60, 1), (65, 1)] }, { coefficient := -1, powers := [(12, 1), (30, 1), (37, 1), (49, 1), (58, 1), (60, 1), (65, 1)] }, { coefficient := 1, powers := [(25, 1), (46, 1)] }, { coefficient := -1, powers := [(37, 1), (60, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (4, 1), (35, 1), (39, 1), (61, 1), (63, 1)] }, { coefficient := 1, powers := [(0, 1), (4, 1), (35, 1), (49, 1), (55, 1), (63, 1)] }, { coefficient := 1, powers := [(4, 1), (25, 1), (35, 1), (39, 1), (61, 1), (63, 1)] }, { coefficient := 1, powers := [(4, 1), (25, 1), (35, 1), (49, 1), (55, 1), (63, 1)] }, { coefficient := -1, powers := [(6, 1), (39, 1), (58, 1), (60, 1), (61, 1), (65, 1)] }, { coefficient := -1, powers := [(6, 1), (49, 1), (55, 1), (58, 1), (60, 1), (65, 1)] }, { coefficient := -1, powers := [(10, 1), (35, 1), (37, 1), (39, 1), (61, 1), (63, 1)] }, { coefficient := -1, powers := [(10, 1), (35, 1), (37, 1), (49, 1), (55, 1), (63, 1)] }, { coefficient := -1, powers := [(15, 1), (32, 1), (37, 1), (39, 1), (61, 1), (63, 1)] }, { coefficient := -1, powers := [(15, 1), (32, 1), (37, 1), (49, 1), (55, 1), (63, 1)] }, { coefficient := -1, powers := [(37, 1), (39, 1), (58, 1), (60, 1), (61, 1), (65, 1)] }, { coefficient := -1, powers := [(37, 1), (49, 1), (55, 1), (58, 1), (60, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (4, 1), (18, 1), (24, 1), (25, 1), (35, 1), (53, 1), (58, 1), (63, 1)] }, { coefficient := 1, powers := [(0, 1), (4, 1), (19, 1), (21, 1), (30, 1), (35, 1), (53, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (4, 1), (19, 1), (24, 1), (26, 1), (35, 1), (53, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (4, 1), (19, 1), (33, 1), (35, 1), (39, 1), (63, 1)] }, { coefficient := 1, powers := [(4, 1), (18, 1), (24, 1), (25, 2), (35, 1), (53, 1), (58, 1), (63, 1)] }, { coefficient := 1, powers := [(4, 1), (19, 1), (21, 1), (25, 1), (30, 1), (35, 1), (53, 1), (63, 1)] }, { coefficient := -1, powers := [(4, 1), (19, 1), (24, 1), (25, 1), (26, 1), (35, 1), (53, 1), (63, 1)] }, { coefficient := -1, powers := [(4, 1), (19, 1), (25, 1), (33, 1), (35, 1), (39, 1), (63, 1)] }, { coefficient := -1, powers := [(6, 1), (18, 1), (24, 1), (25, 1), (53, 1), (58, 2), (60, 1), (65, 1)] }, { coefficient := -1, powers := [(6, 1), (19, 1), (21, 1), (30, 1), (53, 1), (58, 1), (60, 1), (65, 1)] }, { coefficient := 1, powers := [(6, 1), (19, 1), (24, 1), (26, 1), (53, 1), (58, 1), (60, 1), (65, 1)] }, { coefficient := 1, powers := [(6, 1), (19, 1), (33, 1), (39, 1), (58, 1), (60, 1), (65, 1)] }, { coefficient := -1, powers := [(10, 1), (18, 1), (24, 1), (25, 1), (35, 1), (37, 1), (53, 1), (58, 1), (63, 1)] }, { coefficient := -1, powers := [(10, 1), (19, 1), (21, 1), (30, 1), (35, 1), (37, 1), (53, 1), (63, 1)] }, { coefficient := 1, powers := [(10, 1), (19, 1), (24, 1), (26, 1), (35, 1), (37, 1), (53, 1), (63, 1)] }, { coefficient := 1, powers := [(10, 1), (19, 1), (33, 1), (35, 1), (37, 1), (39, 1), (63, 1)] }, { coefficient := -1, powers := [(15, 1), (18, 1), (24, 1), (25, 1), (32, 1), (37, 1), (53, 1), (58, 1), (63, 1)] }, { coefficient := -1, powers := [(15, 1), (19, 1), (21, 1), (30, 1), (32, 1), (37, 1), (53, 1), (63, 1)] }, { coefficient := 1, powers := [(15, 1), (19, 1), (24, 1), (26, 1), (32, 1), (37, 1), (53, 1), (63, 1)] }, { coefficient := -1, powers := [(18, 1), (24, 1), (25, 1), (37, 1), (53, 1), (58, 2), (60, 1), (65, 1)] }, { coefficient := -1, powers := [(19, 1), (21, 1), (30, 1), (37, 1), (53, 1), (58, 1), (60, 1), (65, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (26, 1), (37, 1), (53, 1), (58, 1), (60, 1), (65, 1)] }, { coefficient := 1, powers := [(19, 1), (33, 1), (37, 1), (39, 1), (58, 1), (60, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(25, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (2, 1), (4, 1), (35, 1), (58, 1), (63, 1)] }, { coefficient := 1, powers := [(0, 1), (4, 1), (8, 1), (35, 1), (36, 1), (63, 1)] }, { coefficient := 1, powers := [(2, 1), (4, 1), (25, 1), (35, 1), (58, 1), (63, 1)] }, { coefficient := -1, powers := [(2, 1), (6, 1), (58, 2), (60, 1), (65, 1)] }, { coefficient := -1, powers := [(2, 1), (10, 1), (35, 1), (37, 1), (58, 1), (63, 1)] }, { coefficient := -1, powers := [(2, 1), (15, 1), (32, 1), (37, 1), (58, 1), (63, 1)] }, { coefficient := -1, powers := [(2, 1), (37, 1), (58, 2), (60, 1), (65, 1)] }, { coefficient := 1, powers := [(4, 1), (8, 1), (25, 1), (35, 1), (36, 1), (63, 1)] }, { coefficient := -1, powers := [(6, 1), (8, 1), (36, 1), (58, 1), (60, 1), (65, 1)] }, { coefficient := -1, powers := [(8, 1), (10, 1), (35, 1), (36, 1), (37, 1), (63, 1)] }, { coefficient := -1, powers := [(8, 1), (15, 1), (32, 1), (36, 1), (37, 1), (63, 1)] }, { coefficient := -1, powers := [(8, 1), (36, 1), (37, 1), (58, 1), (60, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (3, 1), (5, 1), (33, 1), (58, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (4, 1), (12, 1), (20, 1), (24, 1), (35, 1), (58, 1), (63, 1)] }, { coefficient := 1, powers := [(0, 1), (5, 1), (23, 1), (51, 1), (58, 1), (60, 1)] }, { coefficient := 1, powers := [(3, 1), (5, 1), (20, 1), (33, 1), (58, 1), (60, 1)] }, { coefficient := 1, powers := [(4, 1), (12, 1), (20, 1), (24, 1), (25, 1), (35, 1), (58, 1), (63, 1)] }, { coefficient := -1, powers := [(5, 1), (20, 1), (28, 1), (51, 1), (58, 1), (60, 1)] }, { coefficient := -1, powers := [(6, 1), (12, 1), (20, 1), (24, 1), (58, 2), (60, 1), (65, 1)] }, { coefficient := -1, powers := [(10, 1), (12, 1), (20, 1), (24, 1), (35, 1), (37, 1), (58, 1), (63, 1)] }, { coefficient := -1, powers := [(12, 1), (15, 1), (20, 1), (24, 1), (32, 1), (37, 1), (58, 1), (63, 1)] }, { coefficient := -1, powers := [(12, 1), (20, 1), (24, 1), (37, 1), (58, 2), (60, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (15, 1), (22, 1), (63, 1)] }, { coefficient := -1, powers := [(5, 1), (6, 1), (33, 1), (58, 1), (60, 1)] }, { coefficient := -1, powers := [(5, 1), (33, 1), (37, 1), (58, 1), (60, 1)] }, { coefficient := 1, powers := [(6, 1), (60, 1)] }, { coefficient := -1, powers := [(15, 1), (22, 1), (25, 1), (63, 1)] }, { coefficient := 1, powers := [(37, 1), (60, 1)] }]
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
    ¬ ∀ index : Fin 31,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((2 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (2 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (2 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component37.SelectedLeafB6_4_1.selectedHasNoCommonZero

end Krenn.Component37.SelectedLeafB6_4_1
