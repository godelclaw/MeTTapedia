import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component37.SelectedLeafB0_3_2_5

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "6e2b5c7db2af610508fec30dc7f7397293f765609237594407aad679af76cac1"
def certificateSHA256 : String := "64839d6122b8c309b8d7c7d4fe93db8b7df49e702d5abf488816712db4488087"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 66 → Fin 670 := ![
  5,
  14,
  20,
  23,
  148,
  149,
  151,
  156,
  157,
  167,
  168,
  175,
  179,
  180,
  183,
  216,
  222,
  256,
  257,
  285,
  294,
  295,
  297,
  298,
  299,
  301,
  307,
  312,
  313,
  315,
  316,
  342,
  410,
  412,
  413,
  430,
  433,
  434,
  436,
  438,
  445,
  450,
  453,
  470,
  472,
  487,
  519,
  602,
  603,
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
  663,
  664,
  665,
  666,
  667,
  668,
  669
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 66 → SparsePoly (Fin 67) := ![
  [{ coefficient := 1, powers := [(5, 1), (35, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (22, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (31, 1)] }, { coefficient := 1, powers := [(18, 1), (26, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (26, 1)] }, { coefficient := 1, powers := [(26, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (30, 1)] }, { coefficient := 1, powers := [(30, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (28, 1)] }, { coefficient := 1, powers := [(15, 1), (23, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (30, 1)] }, { coefficient := 1, powers := [(15, 1), (23, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (25, 1)] }, { coefficient := 1, powers := [(18, 1), (20, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (26, 1)] }, { coefficient := 1, powers := [(18, 1), (20, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (20, 1)] }, { coefficient := 1, powers := [(18, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (55, 1)] }, { coefficient := 1, powers := [(30, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (44, 1)] }, { coefficient := 1, powers := [(28, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(28, 1), (53, 1)] }, { coefficient := -1, powers := [(29, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (31, 1), (45, 1)] }, { coefficient := 1, powers := [(8, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (26, 1), (48, 1)] }, { coefficient := 1, powers := [(31, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (25, 1), (46, 1)] }, { coefficient := 1, powers := [(18, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (25, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(29, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1)] }, { coefficient := 1, powers := [(20, 1), (44, 1)] }, { coefficient := 1, powers := [(25, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (49, 1)] }, { coefficient := 1, powers := [(21, 1), (44, 1)] }, { coefficient := 1, powers := [(25, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (55, 1)] }, { coefficient := 1, powers := [(20, 1), (55, 1)] }, { coefficient := 1, powers := [(26, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (46, 1)] }, { coefficient := 1, powers := [(4, 1), (35, 1)] }, { coefficient := 1, powers := [(15, 1), (22, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (52, 1)] }, { coefficient := 1, powers := [(7, 1), (32, 1)] }, { coefficient := 1, powers := [(10, 1), (27, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (59, 1)] }, { coefficient := 1, powers := [(9, 1), (43, 1)] }, { coefficient := 1, powers := [(13, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (46, 1)] }, { coefficient := 1, powers := [(12, 1), (57, 1)] }, { coefficient := 1, powers := [(18, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (54, 1)] }, { coefficient := 1, powers := [(30, 1), (41, 1)] }, { coefficient := 1, powers := [(30, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(20, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(44, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1), (51, 1)] }, { coefficient := 1, powers := [(25, 1), (46, 1), (51, 1)] }, { coefficient := 1, powers := [(51, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1), (55, 1)] }, { coefficient := 1, powers := [(26, 1), (46, 1), (51, 1)] }, { coefficient := 1, powers := [(55, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (46, 1), (51, 1)] }, { coefficient := 1, powers := [(12, 1), (28, 1), (46, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (25, 1), (41, 1)] }, { coefficient := 1, powers := [(18, 1), (25, 1), (46, 1)] }, { coefficient := 1, powers := [(18, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (20, 1), (50, 1)] }, { coefficient := 1, powers := [(19, 1), (25, 1), (40, 1)] }, { coefficient := 1, powers := [(19, 1), (31, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (44, 1), (53, 1)] }, { coefficient := 1, powers := [(29, 1), (42, 1), (44, 1)] }, { coefficient := 1, powers := [(29, 1), (49, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (46, 1)] }, { coefficient := 1, powers := [(18, 1), (28, 1), (41, 1)] }, { coefficient := 1, powers := [(18, 1), (28, 1), (46, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (49, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1)] }, { coefficient := 1, powers := [(18, 1), (28, 1), (49, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (51, 1)] }, { coefficient := 1, powers := [(12, 1), (28, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (51, 1)] }, { coefficient := 1, powers := [(18, 1), (33, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (53, 1)] }, { coefficient := 1, powers := [(12, 1), (23, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1), (29, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1)] }, { coefficient := 1, powers := [(12, 1), (30, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (60, 1)] }, { coefficient := 1, powers := [(18, 1), (21, 1), (52, 1)] }, { coefficient := 1, powers := [(18, 1), (21, 1), (57, 1)] }, { coefficient := 1, powers := [(18, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (61, 1)] }, { coefficient := 1, powers := [(12, 1), (26, 1), (47, 1)] }, { coefficient := 1, powers := [(12, 1), (58, 1)] }, { coefficient := 1, powers := [(19, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (41, 1)] }, { coefficient := 1, powers := [(18, 1), (46, 1)] }, { coefficient := 1, powers := [(18, 1), (52, 1)] }, { coefficient := 1, powers := [(18, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1), (50, 1)] }, { coefficient := 1, powers := [(6, 1), (31, 1), (46, 1)] }, { coefficient := 1, powers := [(9, 1), (25, 1), (46, 1)] }, { coefficient := 1, powers := [(50, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1), (54, 1)] }, { coefficient := 1, powers := [(26, 1), (41, 1)] }, { coefficient := 1, powers := [(26, 1), (46, 1)] }, { coefficient := 1, powers := [(54, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (37, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1)] }, { coefficient := 1, powers := [(18, 1), (28, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (27, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (52, 1)] }, { coefficient := 1, powers := [(18, 1), (27, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1)] }, { coefficient := 1, powers := [(3, 1), (34, 1)] }, { coefficient := 1, powers := [(13, 1), (20, 1)] }, { coefficient := 1, powers := [(20, 1), (56, 1)] }, { coefficient := 1, powers := [(25, 1), (43, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (50, 1)] }, { coefficient := 1, powers := [(6, 1), (31, 1)] }, { coefficient := 1, powers := [(9, 1), (25, 1)] }, { coefficient := 1, powers := [(20, 1), (50, 1)] }, { coefficient := 1, powers := [(25, 1), (40, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1)] }],
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
  [{ coefficient := 1, powers := [(42, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(56, 1)] }],
  [{ coefficient := 1, powers := [(57, 1), (64, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(58, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (65, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(27, 1)] }],
  [{ coefficient := 1, powers := [(30, 1), (66, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 66 → SparsePoly (Fin 67) := ![
  [{ coefficient := -1, powers := [(4, 1), (30, 1), (41, 1), (61, 1)] }, { coefficient := -1, powers := [(4, 1), (30, 1), (46, 1), (61, 1)] }, { coefficient := -1, powers := [(4, 1), (30, 1), (52, 1), (61, 1)] }, { coefficient := 1, powers := [(7, 1), (30, 1), (41, 1), (61, 1)] }, { coefficient := 1, powers := [(10, 1), (30, 1), (38, 1), (61, 1)] }, { coefficient := -1, powers := [(15, 1), (30, 1), (38, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (21, 1), (30, 1), (41, 1), (61, 1)] }, { coefficient := 1, powers := [(7, 1), (21, 1), (30, 1), (46, 1), (61, 1)] }, { coefficient := -1, powers := [(7, 1), (30, 1), (48, 1), (61, 1)] }],
  [{ coefficient := -2, powers := [(13, 1), (20, 1), (30, 1), (42, 1)] }, { coefficient := -2, powers := [(13, 1), (20, 1), (33, 1), (39, 1)] }, { coefficient := -1, powers := [(25, 1), (30, 1), (42, 1), (43, 1)] }, { coefficient := -1, powers := [(25, 1), (33, 1), (39, 1), (43, 1)] }, { coefficient := -1, powers := [(30, 1), (34, 1), (37, 1), (42, 1)] }, { coefficient := -1, powers := [(33, 1), (34, 1), (37, 1), (39, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (10, 1), (28, 1), (30, 1), (52, 1), (61, 1), (66, 1)] }, { coefficient := 1, powers := [(5, 1), (10, 1), (29, 1), (30, 1), (61, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (20, 1), (36, 1), (42, 1), (45, 1)] }, { coefficient := 1, powers := [(6, 1), (25, 1), (36, 1), (42, 1), (43, 1), (46, 1)] }, { coefficient := 1, powers := [(6, 1), (34, 1), (36, 1), (37, 1), (42, 1), (46, 1)] }, { coefficient := 1, powers := [(6, 1), (36, 1), (42, 1), (43, 1)] }, { coefficient := 1, powers := [(13, 1), (36, 1), (37, 1), (42, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (12, 1), (13, 1), (36, 1), (48, 1)] }, { coefficient := 1, powers := [(6, 1), (12, 1), (20, 1), (36, 1), (45, 1), (48, 1)] }, { coefficient := -1, powers := [(6, 1), (12, 1), (25, 1), (36, 1), (43, 1), (46, 1), (48, 1)] }, { coefficient := -1, powers := [(6, 1), (12, 1), (34, 1), (36, 1), (37, 1), (46, 1), (48, 1)] }, { coefficient := -1, powers := [(6, 1), (12, 1), (36, 1), (43, 1), (48, 1)] }, { coefficient := -2, powers := [(12, 1), (13, 1), (36, 1), (37, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (25, 2), (36, 1), (42, 1), (43, 1), (46, 1), (66, 1)] }, { coefficient := 1, powers := [(8, 1), (25, 1), (34, 1), (36, 1), (37, 1), (42, 1), (46, 1), (66, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (36, 1), (37, 1), (42, 1), (66, 1)] }, { coefficient := 1, powers := [(12, 1), (13, 1), (25, 1), (36, 1), (39, 1), (66, 1)] }, { coefficient := -1, powers := [(12, 1), (20, 1), (25, 1), (36, 1), (39, 1), (45, 1), (66, 1)] }, { coefficient := 1, powers := [(12, 1), (25, 2), (36, 1), (39, 1), (43, 1), (46, 1), (66, 1)] }, { coefficient := 1, powers := [(12, 1), (25, 1), (34, 1), (36, 1), (37, 1), (39, 1), (46, 1), (66, 1)] }, { coefficient := 1, powers := [(12, 1), (34, 1), (36, 1), (37, 1), (39, 1), (66, 1)] }, { coefficient := -1, powers := [(19, 1), (25, 1), (30, 1), (42, 1), (43, 1), (66, 1)] }, { coefficient := -1, powers := [(19, 1), (25, 1), (33, 1), (39, 1), (43, 1), (66, 1)] }, { coefficient := 1, powers := [(19, 1), (30, 1), (34, 1), (37, 1), (42, 1), (66, 1)] }, { coefficient := 1, powers := [(19, 1), (33, 1), (34, 1), (37, 1), (39, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (22, 1), (30, 1), (52, 1), (54, 1), (61, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (22, 1), (30, 1), (52, 1), (61, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(26, 1), (29, 1), (49, 1), (65, 1)] }, { coefficient := 1, powers := [(30, 1), (41, 1), (49, 1)] }, { coefficient := 1, powers := [(30, 1), (46, 1), (49, 1)] }],
  [{ coefficient := -1, powers := [(29, 1), (49, 1)] }],
  [{ coefficient := -1, powers := [(26, 1), (29, 1), (49, 1), (51, 1), (65, 1)] }, { coefficient := -1, powers := [(30, 1), (41, 1), (49, 1), (51, 1)] }, { coefficient := -1, powers := [(30, 1), (46, 1), (49, 1), (51, 1)] }],
  [{ coefficient := -1, powers := [(18, 1), (49, 1)] }],
  [{ coefficient := -1, powers := [(18, 1), (21, 1), (53, 1), (55, 1), (63, 1)] }, { coefficient := -1, powers := [(18, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (21, 1), (49, 1), (55, 1), (63, 1)] }, { coefficient := -1, powers := [(18, 1), (26, 1), (41, 1), (49, 1), (64, 1)] }, { coefficient := -1, powers := [(18, 1), (26, 1), (49, 1), (52, 1), (64, 1)] }, { coefficient := -1, powers := [(18, 1), (26, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (20, 1), (36, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (12, 1), (13, 1), (36, 1)] }, { coefficient := -1, powers := [(6, 1), (12, 1), (20, 1), (36, 1), (45, 1)] }, { coefficient := 1, powers := [(6, 1), (12, 1), (25, 1), (36, 1), (43, 1), (46, 1)] }, { coefficient := 1, powers := [(6, 1), (12, 1), (34, 1), (36, 1), (37, 1), (46, 1)] }, { coefficient := 1, powers := [(6, 1), (12, 1), (36, 1), (43, 1)] }, { coefficient := 2, powers := [(12, 1), (13, 1), (36, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (49, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(24, 1), (26, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (25, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(18, 1), (24, 1), (52, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(18, 1), (29, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (29, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (30, 1), (41, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (46, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (52, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (30, 1), (46, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (25, 1), (36, 1), (42, 1)] }, { coefficient := 1, powers := [(12, 1), (25, 1), (36, 1), (39, 1)] }, { coefficient := 1, powers := [(19, 1), (25, 1), (30, 1), (42, 1)] }, { coefficient := 1, powers := [(19, 1), (25, 1), (33, 1), (39, 1)] }],
  [{ coefficient := -1, powers := [(23, 1), (25, 1), (49, 1), (54, 1)] }, { coefficient := 1, powers := [(26, 1), (28, 1), (41, 1), (49, 1), (64, 1)] }, { coefficient := 1, powers := [(26, 1), (28, 1), (49, 1), (52, 1), (64, 1)] }, { coefficient := 1, powers := [(26, 1), (28, 1), (49, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (10, 1), (22, 1), (30, 1), (61, 1), (66, 1)] }, { coefficient := -1, powers := [(12, 1), (25, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (24, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (24, 1), (26, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(19, 1), (24, 1), (25, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(26, 1), (41, 1), (49, 1), (64, 1)] }, { coefficient := -1, powers := [(26, 1), (49, 1), (52, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(30, 1), (49, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (30, 1), (42, 1)] }, { coefficient := 1, powers := [(13, 1), (33, 1), (39, 1)] }, { coefficient := 1, powers := [(20, 1), (30, 1), (42, 1), (45, 1)] }, { coefficient := 1, powers := [(20, 1), (33, 1), (39, 1), (45, 1)] }, { coefficient := -1, powers := [(30, 1), (42, 1), (43, 1)] }, { coefficient := -1, powers := [(33, 1), (39, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (21, 1), (55, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(26, 1), (49, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(55, 1)] }],
  [{ coefficient := -1, powers := [(26, 1), (41, 1), (49, 1)] }, { coefficient := -1, powers := [(26, 1), (46, 1), (49, 1)] }, { coefficient := -1, powers := [(26, 1), (49, 1), (52, 1)] }, { coefficient := -1, powers := [(26, 1), (49, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (49, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(49, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (22, 1), (30, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (25, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (21, 1), (22, 1), (30, 1), (61, 1)] }, { coefficient := 1, powers := [(23, 1), (26, 1), (49, 1), (51, 1)] }, { coefficient := 1, powers := [(26, 1), (33, 1), (37, 1), (49, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (25, 1), (36, 1), (42, 1), (43, 1)] }, { coefficient := -1, powers := [(8, 1), (34, 1), (36, 1), (37, 1), (42, 1)] }, { coefficient := -1, powers := [(12, 1), (25, 1), (36, 1), (39, 1), (43, 1)] }, { coefficient := -1, powers := [(12, 1), (34, 1), (36, 1), (37, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (28, 1), (49, 1), (51, 1)] }],
  [{ coefficient := -1, powers := [(49, 1), (51, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (30, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (36, 1), (42, 1), (50, 1)] }, { coefficient := 1, powers := [(12, 1), (36, 1), (39, 1), (50, 1)] }, { coefficient := 1, powers := [(19, 1), (30, 1), (42, 1), (50, 1)] }, { coefficient := 1, powers := [(19, 1), (33, 1), (39, 1), (50, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (13, 1), (36, 1), (39, 1)] }, { coefficient := -1, powers := [(19, 1), (20, 1), (30, 1), (42, 1), (45, 1)] }, { coefficient := -1, powers := [(19, 1), (20, 1), (33, 1), (39, 1), (45, 1)] }, { coefficient := 1, powers := [(19, 1), (30, 1), (42, 1), (43, 1)] }, { coefficient := 1, powers := [(19, 1), (33, 1), (39, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (15, 1), (30, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (20, 1), (36, 1), (39, 1)] }, { coefficient := 1, powers := [(19, 1), (20, 1), (30, 1), (42, 1)] }, { coefficient := 1, powers := [(19, 1), (20, 1), (33, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (10, 1), (22, 1), (30, 1), (61, 1)] }, { coefficient := -1, powers := [(5, 1), (15, 1), (22, 1), (30, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (36, 1), (42, 1)] }, { coefficient := -1, powers := [(12, 1), (36, 1), (39, 1)] }, { coefficient := -1, powers := [(19, 1), (30, 1), (42, 1)] }, { coefficient := -1, powers := [(19, 1), (33, 1), (39, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (30, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(5, 1), (10, 1), (22, 1), (30, 1), (38, 1), (60, 1), (61, 1)] }, { coefficient := -1, powers := [(5, 1), (10, 1), (22, 1), (30, 1), (41, 1), (57, 1), (61, 1)] }, { coefficient := -1, powers := [(5, 1), (10, 1), (22, 1), (30, 1), (46, 1), (52, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (15, 1), (22, 1), (30, 1), (38, 1), (60, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (15, 1), (22, 1), (30, 1), (41, 1), (57, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (15, 1), (22, 1), (30, 1), (46, 1), (52, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (25, 1), (36, 1), (42, 1), (43, 1), (46, 1), (50, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (36, 1), (37, 1), (42, 1), (46, 1), (50, 1)] }, { coefficient := 1, powers := [(8, 1), (36, 1), (37, 1), (42, 1), (59, 1)] }, { coefficient := 1, powers := [(12, 1), (13, 1), (36, 1), (39, 1), (50, 1)] }, { coefficient := -1, powers := [(12, 1), (20, 1), (36, 1), (39, 1), (45, 1), (50, 1)] }, { coefficient := 1, powers := [(12, 1), (25, 1), (36, 1), (39, 1), (43, 1), (46, 1), (50, 1)] }, { coefficient := 1, powers := [(12, 1), (34, 1), (36, 1), (37, 1), (39, 1), (46, 1), (50, 1)] }, { coefficient := 1, powers := [(12, 1), (36, 1), (37, 1), (39, 1), (59, 1)] }, { coefficient := -1, powers := [(18, 1), (28, 1), (46, 1), (49, 1), (51, 1), (54, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (25, 1), (46, 1), (55, 1), (65, 1)] }, { coefficient := -1, powers := [(19, 1), (24, 1), (26, 1), (46, 1), (51, 1), (65, 1)] }, { coefficient := 1, powers := [(19, 1), (30, 1), (37, 1), (42, 1), (59, 1)] }, { coefficient := -1, powers := [(19, 1), (30, 1), (42, 1), (43, 1), (50, 1)] }, { coefficient := 1, powers := [(19, 1), (33, 1), (37, 1), (39, 1), (59, 1)] }, { coefficient := -1, powers := [(19, 1), (33, 1), (39, 1), (43, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (30, 1), (38, 1), (60, 1), (61, 1)] }, { coefficient := -1, powers := [(5, 1), (30, 1), (41, 1), (46, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (41, 1), (57, 1), (61, 1)] }, { coefficient := -1, powers := [(5, 1), (30, 1), (46, 2), (61, 1)] }, { coefficient := -1, powers := [(5, 1), (30, 1), (46, 1), (52, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(25, 1), (49, 1), (53, 1), (54, 1)] }, { coefficient := 1, powers := [(26, 1), (41, 1), (46, 1), (49, 1), (51, 1), (64, 1)] }, { coefficient := 1, powers := [(26, 1), (41, 1), (49, 1), (51, 1)] }, { coefficient := 1, powers := [(26, 1), (46, 1), (49, 1), (51, 1), (52, 1), (64, 1)] }, { coefficient := 2, powers := [(26, 1), (46, 1), (49, 1), (51, 1)] }, { coefficient := 1, powers := [(26, 1), (49, 1), (51, 1), (52, 1)] }, { coefficient := 1, powers := [(26, 1), (49, 1), (51, 1), (57, 1)] }, { coefficient := 1, powers := [(37, 1), (49, 1), (51, 1), (54, 1), (60, 1)] }, { coefficient := 1, powers := [(39, 1), (61, 1)] }, { coefficient := 1, powers := [(42, 1), (58, 1)] }, { coefficient := 1, powers := [(49, 1), (51, 1), (54, 1)] }, { coefficient := -1, powers := [(49, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (8, 1), (36, 1), (42, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (12, 1), (36, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (19, 1), (30, 1), (42, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (19, 1), (33, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(6, 1), (8, 1), (34, 1), (36, 1), (42, 1)] }, { coefficient := 1, powers := [(6, 1), (12, 1), (13, 1), (26, 1), (36, 1), (48, 1)] }, { coefficient := -1, powers := [(6, 1), (12, 1), (20, 1), (26, 1), (36, 1), (45, 1), (48, 1)] }, { coefficient := 1, powers := [(6, 1), (12, 1), (25, 1), (26, 1), (36, 1), (43, 1), (46, 1), (48, 1)] }, { coefficient := 1, powers := [(6, 1), (12, 1), (26, 1), (34, 1), (36, 1), (37, 1), (46, 1), (48, 1)] }, { coefficient := 1, powers := [(6, 1), (12, 1), (26, 1), (36, 1), (43, 1), (48, 1)] }, { coefficient := 1, powers := [(6, 1), (12, 1), (34, 1), (36, 1), (39, 1)] }, { coefficient := 1, powers := [(6, 1), (18, 1), (20, 1), (26, 1), (36, 1), (42, 1), (45, 1)] }, { coefficient := -1, powers := [(6, 1), (18, 1), (25, 1), (26, 1), (36, 1), (42, 1), (43, 1), (46, 1)] }, { coefficient := -1, powers := [(6, 1), (18, 1), (26, 1), (34, 1), (36, 1), (37, 1), (42, 1), (46, 1)] }, { coefficient := -1, powers := [(6, 1), (18, 1), (26, 1), (36, 1), (42, 1), (43, 1)] }, { coefficient := 1, powers := [(6, 1), (19, 1), (30, 1), (34, 1), (42, 1)] }, { coefficient := 1, powers := [(6, 1), (19, 1), (33, 1), (34, 1), (39, 1)] }, { coefficient := -1, powers := [(8, 1), (25, 2), (30, 1), (36, 1), (42, 1), (43, 1), (46, 1), (66, 1)] }, { coefficient := -1, powers := [(8, 1), (25, 1), (30, 1), (34, 1), (36, 1), (37, 1), (42, 1), (46, 1), (66, 1)] }, { coefficient := -1, powers := [(8, 1), (30, 1), (34, 1), (36, 1), (37, 1), (42, 1), (66, 1)] }, { coefficient := -1, powers := [(12, 1), (13, 1), (25, 1), (30, 1), (36, 1), (39, 1), (66, 1)] }, { coefficient := 1, powers := [(12, 1), (13, 1), (25, 1), (36, 1), (39, 1)] }, { coefficient := 2, powers := [(12, 1), (13, 1), (26, 1), (36, 1), (37, 1), (48, 1)] }, { coefficient := 1, powers := [(12, 1), (20, 1), (25, 1), (30, 1), (36, 1), (39, 1), (45, 1), (66, 1)] }, { coefficient := -1, powers := [(12, 1), (25, 2), (30, 1), (36, 1), (39, 1), (43, 1), (46, 1), (66, 1)] }, { coefficient := -1, powers := [(12, 1), (25, 1), (30, 1), (34, 1), (36, 1), (37, 1), (39, 1), (46, 1), (66, 1)] }, { coefficient := -1, powers := [(12, 1), (30, 1), (34, 1), (36, 1), (37, 1), (39, 1), (66, 1)] }, { coefficient := -1, powers := [(13, 1), (18, 1), (26, 1), (36, 1), (37, 1), (42, 1)] }, { coefficient := -1, powers := [(13, 1), (19, 1), (25, 1), (30, 1), (42, 1)] }, { coefficient := -1, powers := [(13, 1), (19, 1), (25, 1), (33, 1), (39, 1)] }, { coefficient := 1, powers := [(19, 1), (25, 1), (30, 2), (42, 1), (43, 1), (66, 1)] }, { coefficient := 1, powers := [(19, 1), (25, 1), (30, 1), (33, 1), (39, 1), (43, 1), (66, 1)] }, { coefficient := -1, powers := [(19, 1), (30, 2), (34, 1), (37, 1), (42, 1), (66, 1)] }, { coefficient := -1, powers := [(19, 1), (30, 1), (33, 1), (34, 1), (37, 1), (39, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(18, 1), (21, 1), (29, 1), (44, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (8, 1), (31, 1), (36, 1), (42, 1)] }, { coefficient := 1, powers := [(3, 1), (12, 1), (31, 1), (36, 1), (39, 1)] }, { coefficient := 1, powers := [(3, 1), (19, 1), (30, 1), (31, 1), (42, 1)] }, { coefficient := 1, powers := [(3, 1), (19, 1), (31, 1), (33, 1), (39, 1)] }, { coefficient := 1, powers := [(8, 1), (9, 1), (20, 1), (36, 1), (42, 1)] }, { coefficient := -1, powers := [(8, 1), (20, 1), (36, 1), (42, 1), (50, 1)] }, { coefficient := -1, powers := [(12, 1), (20, 1), (36, 1), (39, 1), (50, 1)] }, { coefficient := -1, powers := [(19, 1), (20, 1), (30, 1), (42, 1), (50, 1)] }, { coefficient := -1, powers := [(19, 1), (20, 1), (33, 1), (39, 1), (50, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (26, 1), (28, 1), (41, 1), (49, 1)] }, { coefficient := -1, powers := [(12, 1), (26, 1), (28, 1), (49, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (33, 1)] }, { coefficient := -1, powers := [(12, 1), (24, 1), (25, 1), (65, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (24, 1), (61, 1)] }, { coefficient := -1, powers := [(12, 1), (26, 1), (29, 1), (49, 1)] }, { coefficient := 1, powers := [(18, 1), (26, 1), (29, 1), (49, 1), (51, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (18, 1), (30, 1), (48, 1), (61, 1)] }, { coefficient := -1, powers := [(5, 1), (15, 1), (30, 1), (46, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (10, 1), (22, 1), (30, 1), (41, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (10, 1), (22, 1), (30, 1), (46, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (10, 1), (22, 1), (30, 1), (52, 1), (61, 1)] }, { coefficient := -1, powers := [(8, 1), (9, 1), (25, 2), (36, 1), (42, 1), (43, 1), (46, 1)] }, { coefficient := -1, powers := [(8, 1), (9, 1), (25, 1), (34, 1), (36, 1), (37, 1), (42, 1), (46, 1)] }, { coefficient := -1, powers := [(8, 1), (9, 1), (34, 1), (36, 1), (37, 1), (42, 1)] }, { coefficient := -1, powers := [(9, 1), (12, 1), (13, 1), (25, 1), (36, 1), (39, 1)] }, { coefficient := 1, powers := [(9, 1), (12, 1), (20, 1), (25, 1), (36, 1), (39, 1), (45, 1)] }, { coefficient := -1, powers := [(9, 1), (12, 1), (25, 2), (36, 1), (39, 1), (43, 1), (46, 1)] }, { coefficient := -1, powers := [(9, 1), (12, 1), (25, 1), (34, 1), (36, 1), (37, 1), (39, 1), (46, 1)] }, { coefficient := -1, powers := [(9, 1), (12, 1), (34, 1), (36, 1), (37, 1), (39, 1)] }, { coefficient := 1, powers := [(9, 1), (19, 1), (25, 1), (30, 1), (42, 1), (43, 1)] }, { coefficient := 1, powers := [(9, 1), (19, 1), (25, 1), (33, 1), (39, 1), (43, 1)] }, { coefficient := -1, powers := [(9, 1), (19, 1), (30, 1), (34, 1), (37, 1), (42, 1)] }, { coefficient := -1, powers := [(9, 1), (19, 1), (33, 1), (34, 1), (37, 1), (39, 1)] }]
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
    ¬ ∀ index : Fin 66,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component37.SelectedLeafB0_3_2_5.selectedHasNoCommonZero

end Krenn.Component37.SelectedLeafB0_3_2_5
