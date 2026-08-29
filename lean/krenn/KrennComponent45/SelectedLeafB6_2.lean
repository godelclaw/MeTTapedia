import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component45.SelectedLeafB6_2

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "3aafec5511d8450fcb8deb987473b422f1f5acc44cef066d52bc7c0321a99367"
def certificateSHA256 : String := "4c399bb6a136ac2fd245e069ae430a20553ca29cec2bc3c479c912207b52b24d"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 46 → Fin 566 := ![
  2,
  3,
  4,
  6,
  7,
  17,
  18,
  24,
  32,
  34,
  50,
  201,
  203,
  210,
  214,
  219,
  237,
  240,
  242,
  267,
  284,
  301,
  359,
  360,
  361,
  364,
  365,
  372,
  379,
  380,
  393,
  414,
  421,
  440,
  468,
  516,
  522,
  525,
  526,
  557,
  559,
  561,
  562,
  563,
  564,
  565
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 46 → SparsePoly (Fin 60) := ![
  [{ coefficient := 1, powers := [(3, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(15, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (20, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(31, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1)] }, { coefficient := 1, powers := [(25, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (50, 1)] }, { coefficient := 1, powers := [(20, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (36, 1)] }, { coefficient := 1, powers := [(36, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (33, 1)] }, { coefficient := 1, powers := [(33, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (30, 1)] }, { coefficient := 1, powers := [(30, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (20, 1)] }, { coefficient := 1, powers := [(18, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (48, 1)] }, { coefficient := 1, powers := [(21, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (53, 1)] }, { coefficient := 1, powers := [(26, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (30, 1), (55, 1)] }, { coefficient := 1, powers := [(30, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (24, 1), (55, 1)] }, { coefficient := 1, powers := [(24, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (26, 1), (45, 1)] }, { coefficient := 1, powers := [(9, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (47, 1)] }, { coefficient := 1, powers := [(15, 1), (22, 1), (47, 1)] }, { coefficient := 1, powers := [(15, 1), (27, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (46, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (50, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1)] }, { coefficient := 1, powers := [(13, 1), (30, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (55, 1)] }, { coefficient := 1, powers := [(18, 1), (21, 1), (48, 1)] }, { coefficient := 1, powers := [(18, 1), (21, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (54, 1)] }, { coefficient := 1, powers := [(9, 1), (51, 1)] }, { coefficient := 1, powers := [(14, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (44, 1)] }, { coefficient := 1, powers := [(13, 1), (52, 1)] }, { coefficient := 1, powers := [(18, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (50, 1)] }, { coefficient := 1, powers := [(30, 1), (42, 1)] }, { coefficient := 1, powers := [(33, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (53, 1)] }, { coefficient := 1, powers := [(30, 1), (46, 1)] }, { coefficient := 1, powers := [(36, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (37, 1), (54, 1)] }, { coefficient := 1, powers := [(1, 1), (40, 1), (51, 1)] }, { coefficient := 1, powers := [(1, 1), (43, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (42, 1), (51, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (51, 1)] }, { coefficient := 1, powers := [(13, 1), (24, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (30, 1), (56, 1)] }, { coefficient := 1, powers := [(3, 1), (33, 1), (53, 1)] }, { coefficient := 1, powers := [(3, 1), (36, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (24, 1), (56, 1)] }, { coefficient := 1, powers := [(6, 1), (33, 1), (46, 1)] }, { coefficient := 1, powers := [(6, 1), (36, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (20, 1), (52, 1)] }, { coefficient := 1, powers := [(13, 1)] }, { coefficient := 1, powers := [(18, 1), (20, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (41, 1), (51, 1)] }, { coefficient := 1, powers := [(6, 1), (34, 1), (41, 1)] }, { coefficient := 1, powers := [(14, 1), (25, 1), (41, 1)] }, { coefficient := 1, powers := [(14, 1)] }, { coefficient := 1, powers := [(51, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (31, 1), (53, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1), (46, 1)] }, { coefficient := 1, powers := [(12, 1), (21, 1), (53, 1)] }, { coefficient := 1, powers := [(12, 1), (26, 1), (46, 1)] }, { coefficient := 1, powers := [(19, 1), (31, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1)] }, { coefficient := 1, powers := [(3, 1), (34, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1)] }, { coefficient := 1, powers := [(20, 1), (51, 1)] }, { coefficient := 1, powers := [(25, 1), (43, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1)] }, { coefficient := 1, powers := [(6, 1), (31, 1)] }, { coefficient := 1, powers := [(9, 1), (25, 1)] }, { coefficient := 1, powers := [(20, 1), (47, 1)] }, { coefficient := 1, powers := [(25, 1), (40, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (37, 1), (54, 1)] }, { coefficient := 1, powers := [(0, 1), (40, 1), (51, 1)] }, { coefficient := 1, powers := [(0, 1), (43, 1), (47, 1)] }, { coefficient := 1, powers := [(3, 1), (25, 1), (54, 1)] }, { coefficient := 1, powers := [(3, 1), (31, 1), (51, 1)] }, { coefficient := 1, powers := [(3, 1), (34, 1), (47, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1), (54, 1)] }, { coefficient := 1, powers := [(6, 1), (31, 1), (43, 1)] }, { coefficient := 1, powers := [(6, 1), (34, 1), (40, 1)] }, { coefficient := 1, powers := [(9, 1), (20, 1), (51, 1)] }, { coefficient := 1, powers := [(9, 1), (25, 1), (43, 1)] }, { coefficient := 1, powers := [(9, 1), (34, 1), (37, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1), (47, 1)] }, { coefficient := 1, powers := [(14, 1), (25, 1), (40, 1)] }, { coefficient := 1, powers := [(14, 1), (31, 1), (37, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (42, 1), (53, 1)] }, { coefficient := 1, powers := [(2, 1), (46, 1), (50, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (53, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1), (50, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (56, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (46, 1)] }, { coefficient := 1, powers := [(8, 1), (36, 1), (42, 1)] }, { coefficient := 1, powers := [(13, 1), (24, 1), (53, 1)] }, { coefficient := 1, powers := [(13, 1), (30, 1), (46, 1)] }, { coefficient := 1, powers := [(13, 1), (36, 1), (39, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (50, 1)] }, { coefficient := 1, powers := [(19, 1), (30, 1), (42, 1)] }, { coefficient := 1, powers := [(19, 1), (33, 1), (39, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1), (58, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(40, 1)] }],
  [{ coefficient := 1, powers := [(41, 1), (59, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(42, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 46 → SparsePoly (Fin 60) := ![
  [{ coefficient := -1, powers := [(0, 1), (5, 1), (6, 1), (30, 1), (54, 1), (55, 1)] }, { coefficient := -2, powers := [(0, 1), (5, 1), (9, 1), (30, 1), (51, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (6, 1), (14, 1), (30, 1), (31, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (31, 1), (37, 1), (43, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (25, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (31, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (6, 1), (33, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (6, 1), (8, 1), (24, 1), (54, 1), (55, 1)] }, { coefficient := -2, powers := [(0, 1), (8, 1), (9, 1), (24, 1), (51, 1), (55, 1)] }, { coefficient := -1, powers := [(6, 1), (8, 1), (9, 1), (24, 1), (34, 1), (55, 1)] }, { coefficient := 1, powers := [(6, 1), (8, 1), (14, 1), (24, 1), (31, 1), (55, 1)] }, { coefficient := -1, powers := [(8, 1), (9, 1), (14, 1), (24, 1), (55, 1), (59, 1)] }, { coefficient := -1, powers := [(8, 1), (9, 1), (24, 1), (34, 1), (37, 1), (55, 1)] }, { coefficient := -1, powers := [(8, 1), (9, 1), (24, 1), (51, 1), (55, 1), (59, 1)] }, { coefficient := -1, powers := [(8, 1), (24, 1), (25, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (31, 1), (37, 1), (43, 1), (55, 1)] }, { coefficient := -1, powers := [(8, 1), (24, 1), (31, 1), (51, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (6, 1), (26, 1), (33, 1), (34, 1)] }, { coefficient := -1, powers := [(5, 1), (14, 1), (26, 1), (33, 1), (59, 1)] }, { coefficient := -1, powers := [(5, 1), (26, 1), (33, 1), (34, 1), (37, 1)] }, { coefficient := -1, powers := [(5, 1), (26, 1), (33, 1), (51, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (8, 1), (33, 1), (34, 1)] }, { coefficient := 1, powers := [(8, 1), (14, 1), (33, 1), (59, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (34, 1), (37, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (51, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (24, 1), (25, 1), (44, 1), (53, 1), (54, 1)] }, { coefficient := -1, powers := [(3, 1), (24, 1), (25, 1), (52, 1), (53, 1), (54, 1)] }, { coefficient := -1, powers := [(3, 1), (24, 1), (31, 1), (44, 1), (51, 1), (53, 1)] }, { coefficient := -1, powers := [(3, 1), (24, 1), (31, 1), (51, 1), (52, 1), (53, 1)] }, { coefficient := 1, powers := [(6, 1), (30, 1), (46, 1), (54, 1)] }, { coefficient := 2, powers := [(9, 1), (30, 1), (46, 1), (51, 1)] }, { coefficient := -1, powers := [(24, 1), (25, 1), (37, 1), (44, 1), (53, 1), (54, 1)] }, { coefficient := -1, powers := [(24, 1), (25, 1), (37, 1), (52, 1), (53, 1), (54, 1)] }, { coefficient := -1, powers := [(24, 1), (31, 1), (37, 1), (44, 1), (51, 1), (53, 1)] }, { coefficient := -1, powers := [(24, 1), (31, 1), (37, 1), (51, 1), (52, 1), (53, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (9, 1), (24, 1), (53, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (22, 1), (43, 1), (58, 1)] }, { coefficient := 2, powers := [(14, 1), (20, 1), (22, 1), (58, 1)] }, { coefficient := 1, powers := [(20, 1), (22, 1), (43, 1), (58, 1)] }, { coefficient := 1, powers := [(20, 1), (22, 1), (51, 1), (58, 1)] }, { coefficient := 1, powers := [(22, 1), (25, 1), (43, 1), (58, 1)] }, { coefficient := 1, powers := [(22, 1), (34, 1), (37, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (24, 1), (50, 1), (54, 1)] }, { coefficient := 2, powers := [(9, 1), (24, 1), (50, 1), (51, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (13, 1), (24, 1), (25, 1), (52, 1), (54, 1)] }, { coefficient := -1, powers := [(3, 1), (13, 1), (24, 1), (31, 1), (51, 1), (52, 1)] }, { coefficient := -1, powers := [(13, 1), (24, 1), (25, 1), (37, 1), (52, 1), (54, 1)] }, { coefficient := -1, powers := [(13, 1), (24, 1), (31, 1), (37, 1), (51, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (14, 1), (19, 1), (33, 1)] }, { coefficient := 1, powers := [(19, 1), (33, 1), (37, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (8, 1), (33, 1), (54, 1)] }, { coefficient := 2, powers := [(8, 1), (9, 1), (33, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (6, 1), (36, 1), (54, 1)] }, { coefficient := 2, powers := [(5, 1), (9, 1), (36, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (25, 1), (39, 1), (54, 1)] }, { coefficient := 1, powers := [(13, 1), (31, 1), (39, 1), (51, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (25, 1), (46, 1), (54, 1)] }, { coefficient := -1, powers := [(8, 1), (31, 1), (46, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (6, 1), (34, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (14, 1), (56, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (37, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (51, 1), (56, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (24, 1), (25, 1), (49, 1), (53, 1), (54, 1)] }, { coefficient := -1, powers := [(3, 1), (24, 1), (31, 1), (49, 1), (51, 1), (53, 1)] }, { coefficient := -1, powers := [(24, 1), (25, 1), (37, 1), (49, 1), (53, 1), (54, 1)] }, { coefficient := -1, powers := [(24, 1), (31, 1), (37, 1), (49, 1), (51, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(6, 2), (9, 1), (18, 1), (34, 1), (36, 1), (50, 1)] }, { coefficient := -1, powers := [(6, 2), (14, 1), (18, 1), (31, 1), (36, 1), (50, 1)] }, { coefficient := 1, powers := [(6, 1), (9, 1), (14, 1), (18, 1), (36, 1), (50, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (9, 1), (18, 1), (34, 1), (36, 1), (37, 1), (50, 1)] }, { coefficient := 1, powers := [(6, 1), (9, 1), (18, 1), (36, 1), (50, 1), (51, 1), (59, 1)] }, { coefficient := -1, powers := [(6, 1), (18, 1), (31, 1), (36, 1), (37, 1), (43, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (12, 1), (14, 1), (33, 1)] }, { coefficient := 1, powers := [(12, 1), (33, 1), (37, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (5, 1), (6, 1), (54, 1), (56, 1)] }, { coefficient := 2, powers := [(0, 1), (5, 1), (9, 1), (51, 1), (56, 1)] }, { coefficient := -1, powers := [(5, 1), (6, 1), (14, 1), (31, 1), (56, 1)] }, { coefficient := -1, powers := [(5, 1), (31, 1), (37, 1), (43, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (6, 1), (8, 1), (54, 1), (56, 1)] }, { coefficient := 2, powers := [(0, 1), (8, 1), (9, 1), (51, 1), (56, 1)] }, { coefficient := 1, powers := [(6, 1), (8, 1), (9, 1), (34, 1), (56, 1)] }, { coefficient := -1, powers := [(6, 1), (8, 1), (14, 1), (31, 1), (56, 1)] }, { coefficient := -1, powers := [(6, 1), (9, 1), (19, 1), (34, 1), (50, 1)] }, { coefficient := 1, powers := [(6, 1), (14, 1), (19, 1), (31, 1), (50, 1)] }, { coefficient := 1, powers := [(8, 1), (9, 1), (14, 1), (56, 1), (59, 1)] }, { coefficient := 1, powers := [(8, 1), (9, 1), (34, 1), (37, 1), (56, 1)] }, { coefficient := 1, powers := [(8, 1), (9, 1), (51, 1), (56, 1), (59, 1)] }, { coefficient := -1, powers := [(8, 1), (31, 1), (37, 1), (43, 1), (56, 1)] }, { coefficient := -1, powers := [(9, 1), (14, 1), (19, 1), (50, 1), (59, 1)] }, { coefficient := -1, powers := [(9, 1), (19, 1), (34, 1), (37, 1), (50, 1)] }, { coefficient := -1, powers := [(9, 1), (19, 1), (50, 1), (51, 1), (59, 1)] }, { coefficient := 1, powers := [(19, 1), (31, 1), (37, 1), (43, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (6, 1), (33, 1), (34, 1)] }, { coefficient := 1, powers := [(5, 1), (14, 1), (33, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (34, 1), (37, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (51, 1), (59, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (43, 1), (58, 1)] }, { coefficient := -2, powers := [(14, 1), (20, 1), (58, 1)] }, { coefficient := -1, powers := [(20, 1), (43, 1), (58, 1)] }, { coefficient := -1, powers := [(20, 1), (51, 1), (58, 1)] }, { coefficient := -1, powers := [(25, 1), (43, 1), (58, 1)] }, { coefficient := -1, powers := [(34, 1), (37, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(6, 2), (9, 1), (34, 1), (50, 1), (55, 1)] }, { coefficient := -1, powers := [(6, 2), (14, 1), (31, 1), (50, 1), (55, 1)] }, { coefficient := 1, powers := [(6, 1), (9, 1), (14, 1), (50, 1), (55, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (9, 1), (34, 1), (37, 1), (50, 1), (55, 1)] }, { coefficient := 1, powers := [(6, 1), (9, 1), (34, 1), (50, 1)] }, { coefficient := 1, powers := [(6, 1), (9, 1), (50, 1), (51, 1), (55, 1), (59, 1)] }, { coefficient := -1, powers := [(6, 1), (14, 1), (31, 1), (50, 1)] }, { coefficient := -1, powers := [(6, 1), (20, 1), (50, 1), (54, 1)] }, { coefficient := -1, powers := [(6, 1), (31, 1), (37, 1), (43, 1), (50, 1), (55, 1)] }, { coefficient := 1, powers := [(9, 1), (14, 1), (50, 1), (59, 1)] }, { coefficient := -2, powers := [(9, 1), (20, 1), (50, 1), (51, 1)] }, { coefficient := 1, powers := [(9, 1), (34, 1), (37, 1), (50, 1)] }, { coefficient := 1, powers := [(9, 1), (50, 1), (51, 1), (59, 1)] }, { coefficient := -1, powers := [(31, 1), (37, 1), (43, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (25, 1), (46, 1), (54, 1)] }, { coefficient := 1, powers := [(3, 1), (31, 1), (46, 1), (51, 1)] }, { coefficient := -1, powers := [(6, 1), (25, 1), (46, 1), (54, 1)] }, { coefficient := -2, powers := [(9, 1), (25, 1), (46, 1), (51, 1)] }, { coefficient := 1, powers := [(25, 1), (37, 1), (46, 1), (54, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1), (46, 1), (51, 1)] }],
  [{ coefficient := -1, powers := [(6, 2), (9, 1), (34, 1), (36, 1), (50, 1)] }, { coefficient := 1, powers := [(6, 2), (14, 1), (31, 1), (36, 1), (50, 1)] }, { coefficient := -1, powers := [(6, 1), (9, 1), (14, 1), (36, 1), (50, 1), (59, 1)] }, { coefficient := -1, powers := [(6, 1), (9, 1), (34, 1), (36, 1), (37, 1), (50, 1)] }, { coefficient := -1, powers := [(6, 1), (9, 1), (36, 1), (50, 1), (51, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (31, 1), (36, 1), (37, 1), (43, 1), (50, 1)] }],
  [{ coefficient := -1, powers := [(0, 1)] }, { coefficient := 1, powers := [(20, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (24, 1), (25, 2), (53, 1), (54, 1)] }, { coefficient := 1, powers := [(3, 1), (24, 1), (25, 1), (31, 1), (51, 1), (53, 1)] }, { coefficient := 1, powers := [(24, 1), (25, 2), (37, 1), (53, 1), (54, 1)] }, { coefficient := 1, powers := [(24, 1), (25, 1), (31, 1), (37, 1), (51, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (6, 1), (19, 1), (54, 1)] }, { coefficient := 2, powers := [(0, 1), (9, 1), (19, 1), (51, 1)] }, { coefficient := 1, powers := [(3, 1), (19, 1), (25, 1), (54, 1)] }, { coefficient := 1, powers := [(3, 1), (19, 1), (31, 1), (51, 1)] }, { coefficient := 1, powers := [(6, 1), (9, 1), (19, 1), (34, 1)] }, { coefficient := -1, powers := [(6, 1), (14, 1), (19, 1), (31, 1)] }, { coefficient := 1, powers := [(9, 1), (14, 1), (19, 1), (59, 1)] }, { coefficient := 1, powers := [(9, 1), (19, 1), (34, 1), (37, 1)] }, { coefficient := 1, powers := [(9, 1), (19, 1), (51, 1), (59, 1)] }, { coefficient := -1, powers := [(19, 1), (31, 1), (37, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (6, 1), (13, 1), (54, 1)] }, { coefficient := 2, powers := [(0, 1), (9, 1), (13, 1), (51, 1)] }, { coefficient := 1, powers := [(6, 1), (9, 1), (13, 1), (34, 1)] }, { coefficient := -1, powers := [(6, 1), (13, 1), (14, 1), (31, 1)] }, { coefficient := 1, powers := [(9, 1), (13, 1), (14, 1), (59, 1)] }, { coefficient := 1, powers := [(9, 1), (13, 1), (34, 1), (37, 1)] }, { coefficient := 1, powers := [(9, 1), (13, 1), (51, 1), (59, 1)] }, { coefficient := -1, powers := [(13, 1), (25, 1), (37, 1), (54, 1)] }, { coefficient := -1, powers := [(13, 1), (31, 1), (37, 1), (43, 1)] }, { coefficient := -1, powers := [(13, 1), (31, 1), (37, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (58, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (9, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (25, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (25, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (24, 1), (25, 1), (53, 1), (54, 1)] }, { coefficient := 1, powers := [(3, 1), (24, 1), (31, 1), (51, 1), (53, 1)] }, { coefficient := 1, powers := [(24, 1), (25, 1), (37, 1), (53, 1), (54, 1)] }, { coefficient := 1, powers := [(24, 1), (31, 1), (37, 1), (51, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(9, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (14, 1), (33, 1)] }, { coefficient := -1, powers := [(33, 1), (37, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(47, 1)] }],
  [{ coefficient := 1, powers := [(14, 1)] }, { coefficient := 1, powers := [(43, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(0, 1), (6, 1), (54, 1)] }, { coefficient := -2, powers := [(0, 1), (9, 1), (51, 1)] }, { coefficient := -1, powers := [(3, 1), (25, 1), (54, 1)] }, { coefficient := -1, powers := [(3, 1), (31, 1), (51, 1)] }, { coefficient := -1, powers := [(6, 1), (9, 1), (34, 1)] }, { coefficient := 1, powers := [(6, 1), (14, 1), (31, 1)] }, { coefficient := -1, powers := [(9, 1), (14, 1), (59, 1)] }, { coefficient := -1, powers := [(9, 1), (34, 1), (37, 1)] }, { coefficient := -1, powers := [(9, 1), (51, 1), (59, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1), (43, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (37, 1), (54, 1)] }, { coefficient := 1, powers := [(0, 1), (43, 1), (47, 1)] }, { coefficient := 2, powers := [(14, 1), (20, 1), (47, 1)] }, { coefficient := 1, powers := [(20, 1), (43, 1), (47, 1)] }, { coefficient := 1, powers := [(20, 1), (47, 1), (51, 1)] }, { coefficient := 1, powers := [(25, 1), (43, 1), (47, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (6, 1), (39, 1), (54, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (6, 1), (46, 1), (50, 1), (54, 1)] }, { coefficient := 2, powers := [(0, 1), (9, 1), (39, 1), (51, 1), (56, 1)] }, { coefficient := 2, powers := [(0, 1), (9, 1), (46, 1), (50, 1), (51, 1)] }, { coefficient := 1, powers := [(3, 1), (25, 1), (39, 1), (54, 1), (56, 1)] }, { coefficient := 1, powers := [(3, 1), (31, 1), (39, 1), (51, 1), (56, 1)] }, { coefficient := -1, powers := [(6, 2), (9, 1), (34, 1), (46, 1), (50, 1), (55, 1)] }, { coefficient := 1, powers := [(6, 2), (14, 1), (31, 1), (46, 1), (50, 1), (55, 1)] }, { coefficient := -1, powers := [(6, 1), (9, 1), (14, 1), (46, 1), (50, 1), (55, 1), (59, 1)] }, { coefficient := -1, powers := [(6, 1), (9, 1), (34, 1), (37, 1), (46, 1), (50, 1), (55, 1)] }, { coefficient := 1, powers := [(6, 1), (9, 1), (34, 1), (39, 1), (56, 1)] }, { coefficient := -1, powers := [(6, 1), (9, 1), (46, 1), (50, 1), (51, 1), (55, 1), (59, 1)] }, { coefficient := -1, powers := [(6, 1), (14, 1), (31, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1), (46, 1), (50, 1), (54, 1)] }, { coefficient := 1, powers := [(6, 1), (25, 1), (46, 1), (50, 1), (54, 1)] }, { coefficient := 1, powers := [(6, 1), (31, 1), (37, 1), (43, 1), (46, 1), (50, 1), (55, 1)] }, { coefficient := 1, powers := [(9, 1), (14, 1), (39, 1), (56, 1), (59, 1)] }, { coefficient := 2, powers := [(9, 1), (20, 1), (46, 1), (50, 1), (51, 1)] }, { coefficient := 2, powers := [(9, 1), (25, 1), (46, 1), (50, 1), (51, 1)] }, { coefficient := 1, powers := [(9, 1), (34, 1), (37, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(9, 1), (39, 1), (51, 1), (56, 1), (59, 1)] }, { coefficient := -1, powers := [(25, 1), (37, 1), (46, 1), (50, 1), (54, 1)] }, { coefficient := -1, powers := [(31, 1), (37, 1), (39, 1), (43, 1), (56, 1)] }, { coefficient := -1, powers := [(31, 1), (37, 1), (46, 1), (50, 1), (51, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (1, 1), (51, 1), (58, 1)] }, { coefficient := 2, powers := [(0, 1), (15, 1), (27, 1), (43, 1), (58, 1)] }, { coefficient := 1, powers := [(0, 1), (51, 1)] }, { coefficient := -1, powers := [(5, 1), (6, 1), (30, 1), (34, 1), (56, 1)] }, { coefficient := -1, powers := [(5, 1), (14, 1), (30, 1), (56, 1), (59, 1)] }, { coefficient := -1, powers := [(5, 1), (30, 1), (34, 1), (37, 1), (56, 1)] }, { coefficient := -1, powers := [(5, 1), (30, 1), (51, 1), (56, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (34, 1)] }, { coefficient := 2, powers := [(14, 1), (15, 1), (20, 1), (27, 1), (58, 1)] }, { coefficient := 1, powers := [(15, 1), (20, 1), (27, 1), (43, 1), (58, 1)] }, { coefficient := 1, powers := [(15, 1), (20, 1), (27, 1), (51, 1), (58, 1)] }, { coefficient := 1, powers := [(15, 1), (25, 1), (27, 1), (43, 1), (58, 1)] }, { coefficient := 1, powers := [(15, 1), (27, 1), (34, 1), (37, 1), (58, 1)] }, { coefficient := -1, powers := [(25, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (9, 1), (51, 1)] }, { coefficient := 1, powers := [(6, 1), (9, 1), (34, 1)] }, { coefficient := 1, powers := [(9, 1), (14, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (2, 1), (6, 1), (53, 1), (54, 1)] }, { coefficient := 1, powers := [(0, 1), (6, 1), (8, 1), (36, 1), (54, 1)] }, { coefficient := 2, powers := [(0, 1), (8, 1), (9, 1), (36, 1), (51, 1)] }, { coefficient := 1, powers := [(2, 1), (3, 1), (25, 1), (53, 1), (54, 1)] }, { coefficient := 1, powers := [(2, 1), (3, 1), (31, 1), (51, 1), (53, 1)] }, { coefficient := 1, powers := [(2, 1), (6, 1), (9, 1), (34, 1), (53, 1)] }, { coefficient := -1, powers := [(2, 1), (6, 1), (14, 1), (31, 1), (53, 1)] }, { coefficient := 1, powers := [(2, 1), (9, 1), (14, 1), (53, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (9, 1), (34, 1), (37, 1), (53, 1)] }, { coefficient := 1, powers := [(2, 1), (9, 1), (51, 1), (53, 1), (59, 1)] }, { coefficient := -1, powers := [(2, 1), (31, 1), (37, 1), (43, 1), (53, 1)] }, { coefficient := 1, powers := [(3, 1), (8, 1), (25, 1), (36, 1), (54, 1)] }, { coefficient := 1, powers := [(3, 1), (8, 1), (31, 1), (36, 1), (51, 1)] }, { coefficient := 1, powers := [(6, 1), (8, 1), (9, 1), (34, 1), (36, 1)] }, { coefficient := -1, powers := [(6, 1), (8, 1), (14, 1), (31, 1), (36, 1)] }, { coefficient := -1, powers := [(6, 1), (8, 1), (25, 1), (36, 1), (54, 1)] }, { coefficient := -1, powers := [(6, 1), (8, 1), (31, 1), (36, 1), (51, 1)] }, { coefficient := 1, powers := [(8, 1), (9, 1), (14, 1), (36, 1), (59, 1)] }, { coefficient := 1, powers := [(8, 1), (9, 1), (34, 1), (36, 1), (37, 1)] }, { coefficient := 1, powers := [(8, 1), (9, 1), (36, 1), (51, 1), (59, 1)] }, { coefficient := -1, powers := [(8, 1), (31, 1), (36, 1), (37, 1), (43, 1)] }]
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
    (values : Fin 60 → R) :
    ¬ ∀ index : Fin 46,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component45.SelectedLeafB6_2.selectedHasNoCommonZero

end Krenn.Component45.SelectedLeafB6_2
