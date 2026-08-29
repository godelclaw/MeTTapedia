import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component47.SelectedLeafB5_6

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "db812b8d884c99c1e0c4b2384aefea3900a481840eb8757862585b85f0ea052e"
def certificateSHA256 : String := "a8146e165e0cc1e42efe392d7dc6f722eac4e1cb5ae7fcb6629dbd6fb8bd7385"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 43 → Fin 593 := ![
  0,
  1,
  2,
  3,
  5,
  6,
  7,
  18,
  22,
  31,
  33,
  34,
  208,
  210,
  220,
  221,
  240,
  272,
  286,
  287,
  363,
  364,
  365,
  366,
  370,
  376,
  377,
  378,
  380,
  384,
  401,
  403,
  410,
  411,
  449,
  544,
  545,
  550,
  584,
  586,
  587,
  589,
  592
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 43 → SparsePoly (Fin 62) := ![
  [{ coefficient := 1, powers := [(2, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(15, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (20, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1)] }, { coefficient := 1, powers := [(25, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (51, 1)] }, { coefficient := 1, powers := [(20, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (33, 1)] }, { coefficient := 1, powers := [(18, 1), (21, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (32, 1)] }, { coefficient := 1, powers := [(32, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (20, 1)] }, { coefficient := 1, powers := [(18, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (29, 1), (56, 1)] }, { coefficient := 1, powers := [(29, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (33, 1), (48, 1)] }, { coefficient := 1, powers := [(5, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (24, 1), (56, 1)] }, { coefficient := 1, powers := [(24, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (46, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (51, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1)] }, { coefficient := 1, powers := [(14, 1), (29, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (55, 1)] }, { coefficient := 1, powers := [(9, 1), (52, 1)] }, { coefficient := 1, powers := [(15, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (57, 1)] }, { coefficient := 1, powers := [(14, 1), (54, 1)] }, { coefficient := 1, powers := [(19, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (43, 1)] }, { coefficient := 1, powers := [(14, 1), (53, 1)] }, { coefficient := 1, powers := [(18, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (51, 1)] }, { coefficient := 1, powers := [(29, 1), (41, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (54, 1)] }, { coefficient := 1, powers := [(29, 1), (46, 1)] }, { coefficient := 1, powers := [(35, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (36, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (25, 1), (57, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (38, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (41, 1), (54, 1)] }, { coefficient := 1, powers := [(0, 1), (46, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1), (51, 1)] }, { coefficient := 1, powers := [(3, 1), (33, 1), (51, 1)] }, { coefficient := 1, powers := [(15, 1), (20, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (36, 1), (55, 1)] }, { coefficient := 1, powers := [(2, 1), (39, 1), (52, 1)] }, { coefficient := 1, powers := [(2, 1), (42, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (29, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (32, 1), (54, 1)] }, { coefficient := 1, powers := [(3, 1), (35, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (32, 1), (52, 1)] }, { coefficient := 1, powers := [(6, 1), (32, 1), (42, 1)] }, { coefficient := 1, powers := [(15, 1), (32, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (20, 1), (53, 1)] }, { coefficient := 1, powers := [(14, 1)] }, { coefficient := 1, powers := [(18, 1), (20, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1)] }, { coefficient := 1, powers := [(3, 1), (33, 1)] }, { coefficient := 1, powers := [(15, 1), (20, 1)] }, { coefficient := 1, powers := [(20, 1), (52, 1)] }, { coefficient := 1, powers := [(25, 1), (42, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1)] }, { coefficient := 1, powers := [(6, 1), (30, 1)] }, { coefficient := 1, powers := [(9, 1), (25, 1)] }, { coefficient := 1, powers := [(20, 1), (47, 1)] }, { coefficient := 1, powers := [(25, 1), (39, 1)] }, { coefficient := 1, powers := [(30, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (36, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1)] }, { coefficient := 1, powers := [(3, 1), (25, 1), (56, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1), (56, 1)] }, { coefficient := 1, powers := [(20, 1)] }, { coefficient := 1, powers := [(25, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (36, 1), (55, 1)] }, { coefficient := 1, powers := [(0, 1), (39, 1), (52, 1)] }, { coefficient := 1, powers := [(0, 1), (42, 1), (47, 1)] }, { coefficient := 1, powers := [(3, 1), (25, 1), (55, 1)] }, { coefficient := 1, powers := [(3, 1), (30, 1), (52, 1)] }, { coefficient := 1, powers := [(3, 1), (33, 1), (47, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1), (55, 1)] }, { coefficient := 1, powers := [(6, 1), (30, 1), (42, 1)] }, { coefficient := 1, powers := [(6, 1), (33, 1), (39, 1)] }, { coefficient := 1, powers := [(9, 1), (20, 1), (52, 1)] }, { coefficient := 1, powers := [(9, 1), (25, 1), (42, 1)] }, { coefficient := 1, powers := [(9, 1), (33, 1), (36, 1)] }, { coefficient := 1, powers := [(15, 1), (20, 1), (47, 1)] }, { coefficient := 1, powers := [(15, 1), (25, 1), (39, 1)] }, { coefficient := 1, powers := [(15, 1), (30, 1), (36, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (41, 1), (54, 1)] }, { coefficient := 1, powers := [(2, 1), (46, 1), (51, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (51, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (57, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (46, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(14, 1), (24, 1), (54, 1)] }, { coefficient := 1, powers := [(14, 1), (29, 1), (46, 1)] }, { coefficient := 1, powers := [(14, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (51, 1)] }, { coefficient := 1, powers := [(19, 1), (29, 1), (41, 1)] }, { coefficient := 1, powers := [(19, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (58, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (59, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(41, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 43 → SparsePoly (Fin 62) := ![
  [{ coefficient := 1, powers := [(0, 1), (5, 1), (32, 1), (39, 1), (54, 1), (59, 1)] }, { coefficient := -1, powers := [(5, 1), (20, 1), (35, 1), (39, 1), (51, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (5, 1), (15, 1), (32, 1), (54, 1), (59, 1)] }, { coefficient := -1, powers := [(0, 1), (5, 1), (32, 1), (42, 1), (54, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (5, 1), (32, 1), (33, 1), (54, 1), (59, 1)] }, { coefficient := -1, powers := [(5, 1), (20, 1), (32, 1), (42, 1), (54, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (5, 1), (29, 1), (56, 1), (58, 1)] }, { coefficient := 4, powers := [(2, 1), (5, 1), (20, 1), (29, 1), (38, 1), (56, 1), (57, 1), (58, 1)] }, { coefficient := 4, powers := [(2, 1), (5, 1), (25, 1), (29, 1), (38, 1), (56, 1), (57, 1), (58, 1)] }, { coefficient := -1, powers := [(5, 1), (29, 1), (33, 1), (39, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (8, 1), (24, 1), (56, 1), (58, 1)] }, { coefficient := 2, powers := [(2, 1), (8, 1), (20, 1), (24, 1), (38, 1), (56, 1), (57, 1), (58, 1)] }, { coefficient := 2, powers := [(2, 1), (8, 1), (24, 1), (25, 1), (38, 1), (56, 1), (57, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (5, 1), (24, 1), (25, 1), (32, 1), (54, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (5, 1), (25, 1), (32, 2), (46, 1), (54, 1)] }],
  [{ coefficient := -2, powers := [(2, 1), (6, 1), (20, 1), (24, 1), (46, 1), (51, 1), (57, 1), (58, 1)] }, { coefficient := -2, powers := [(2, 1), (6, 1), (24, 1), (25, 1), (46, 1), (51, 1), (57, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (15, 1), (25, 1), (32, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (33, 1), (36, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (5, 1), (24, 1), (25, 1), (32, 1), (43, 1), (54, 2), (55, 1)] }, { coefficient := -1, powers := [(3, 1), (5, 1), (24, 1), (25, 1), (32, 1), (53, 1), (54, 2), (55, 1)] }, { coefficient := 1, powers := [(29, 1), (46, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (20, 1), (35, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (5, 1), (21, 1), (25, 1), (32, 2), (48, 1), (54, 2)] }],
  [{ coefficient := 1, powers := [(24, 1), (51, 1), (58, 1)] }],
  [{ coefficient := -4, powers := [(2, 1), (5, 1), (20, 1), (24, 1), (51, 1), (57, 1), (58, 2)] }, { coefficient := -4, powers := [(2, 1), (5, 1), (24, 1), (25, 1), (51, 1), (57, 1), (58, 2)] }, { coefficient := -1, powers := [(3, 1), (5, 1), (14, 1), (24, 1), (25, 1), (32, 1), (53, 1), (54, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (15, 1), (32, 1), (39, 1)] }, { coefficient := -1, powers := [(5, 1), (15, 1), (32, 1), (47, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (39, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (51, 1), (58, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (58, 1)] }],
  [{ coefficient := 4, powers := [(2, 1), (5, 1), (20, 1), (24, 1), (54, 1), (57, 1), (58, 2)] }, { coefficient := 4, powers := [(2, 1), (5, 1), (24, 1), (25, 1), (54, 1), (57, 1), (58, 2)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (39, 1), (42, 1)] }, { coefficient := -1, powers := [(19, 1), (24, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (5, 1), (25, 1), (32, 2), (48, 1), (54, 2)] }],
  [{ coefficient := -1, powers := [(5, 1), (15, 1), (30, 1), (54, 1)] }, { coefficient := -1, powers := [(5, 1), (30, 1), (42, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (39, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (5, 1), (24, 1), (25, 1), (32, 1), (50, 1), (54, 2), (55, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (5, 1), (57, 1), (58, 1)] }, { coefficient := -4, powers := [(2, 1), (5, 1), (20, 1), (38, 1), (57, 2), (58, 1)] }, { coefficient := -4, powers := [(2, 1), (5, 1), (25, 1), (38, 1), (57, 2), (58, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (5, 1), (25, 1), (32, 2), (54, 2)] }],
  [{ coefficient := 1, powers := [(0, 1), (8, 1), (57, 1), (58, 1)] }, { coefficient := -2, powers := [(2, 1), (8, 1), (20, 1), (38, 1), (57, 2), (58, 1)] }, { coefficient := 2, powers := [(2, 1), (8, 1), (20, 1), (46, 1), (51, 1), (57, 1), (58, 1)] }, { coefficient := -2, powers := [(2, 1), (8, 1), (25, 1), (38, 1), (57, 2), (58, 1)] }, { coefficient := 2, powers := [(2, 1), (8, 1), (25, 1), (46, 1), (51, 1), (57, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (51, 1), (58, 1)] }, { coefficient := 1, powers := [(3, 1), (5, 1), (25, 1), (32, 1), (51, 1), (54, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(25, 1), (46, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (20, 1), (32, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (5, 1), (24, 1), (25, 1), (32, 1), (54, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (5, 1), (24, 1), (25, 2), (32, 1), (54, 2), (55, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (19, 1), (58, 1)] }, { coefficient := -2, powers := [(2, 1), (5, 1), (20, 1), (54, 1), (57, 1), (58, 1)] }, { coefficient := -2, powers := [(2, 1), (5, 1), (25, 1), (54, 1), (57, 1), (58, 1)] }, { coefficient := -2, powers := [(2, 1), (8, 1), (20, 1), (46, 1), (57, 1), (58, 1)] }, { coefficient := -2, powers := [(2, 1), (8, 1), (25, 1), (46, 1), (57, 1), (58, 1)] }, { coefficient := -2, powers := [(2, 1), (19, 1), (20, 1), (38, 1), (57, 1), (58, 1)] }, { coefficient := -2, powers := [(2, 1), (19, 1), (25, 1), (38, 1), (57, 1), (58, 1)] }, { coefficient := 1, powers := [(3, 1), (5, 1), (19, 1), (25, 1), (32, 1), (54, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (14, 1), (58, 1)] }, { coefficient := -2, powers := [(2, 1), (5, 1), (20, 1), (51, 1), (57, 1), (58, 1)] }, { coefficient := -2, powers := [(2, 1), (5, 1), (25, 1), (51, 1), (57, 1), (58, 1)] }, { coefficient := -2, powers := [(2, 1), (14, 1), (20, 1), (38, 1), (57, 1), (58, 1)] }, { coefficient := -2, powers := [(2, 1), (14, 1), (25, 1), (38, 1), (57, 1), (58, 1)] }, { coefficient := 1, powers := [(3, 1), (5, 1), (14, 1), (25, 1), (32, 1), (54, 1), (55, 1)] }],
  [{ coefficient := -2, powers := [(2, 1), (38, 1), (56, 1), (58, 1)] }],
  [{ coefficient := -2, powers := [(2, 2), (20, 1), (38, 1), (57, 1), (58, 2)] }, { coefficient := -2, powers := [(2, 2), (25, 1), (38, 1), (57, 1), (58, 2)] }, { coefficient := 2, powers := [(2, 1), (5, 1), (20, 1), (29, 1), (57, 1), (58, 2)] }, { coefficient := 2, powers := [(2, 1), (5, 1), (25, 1), (29, 1), (57, 1), (58, 2)] }, { coefficient := -1, powers := [(2, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (35, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (5, 1), (32, 1), (54, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (5, 1), (25, 1), (32, 1), (54, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (33, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (30, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (5, 1), (24, 1), (25, 1), (32, 1), (54, 2), (55, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (32, 1), (39, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (15, 1), (32, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (42, 1), (54, 1)] }],
  [{ coefficient := 2, powers := [(2, 1), (38, 1), (57, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (32, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (58, 1)] }, { coefficient := 2, powers := [(2, 1), (20, 1), (38, 1), (57, 1), (58, 1)] }, { coefficient := 2, powers := [(2, 1), (25, 1), (38, 1), (57, 1), (58, 1)] }, { coefficient := -1, powers := [(3, 1), (5, 1), (25, 1), (32, 1), (54, 1), (55, 1)] }],
  [{ coefficient := 2, powers := [(2, 2), (20, 1), (38, 2), (57, 2), (58, 1)] }, { coefficient := 2, powers := [(2, 2), (20, 1), (38, 1), (46, 1), (51, 1), (57, 1), (58, 1)] }, { coefficient := 2, powers := [(2, 2), (25, 1), (38, 2), (57, 2), (58, 1)] }, { coefficient := 2, powers := [(2, 2), (25, 1), (38, 1), (46, 1), (51, 1), (57, 1), (58, 1)] }, { coefficient := -4, powers := [(2, 1), (5, 1), (20, 1), (24, 1), (51, 1), (54, 1), (57, 1), (58, 1)] }, { coefficient := -2, powers := [(2, 1), (5, 1), (20, 1), (29, 1), (38, 1), (57, 2), (58, 1)] }, { coefficient := -2, powers := [(2, 1), (5, 1), (20, 1), (29, 1), (46, 1), (51, 1), (57, 1), (58, 1)] }, { coefficient := -4, powers := [(2, 1), (5, 1), (24, 1), (25, 1), (51, 1), (54, 1), (57, 1), (58, 1)] }, { coefficient := -2, powers := [(2, 1), (5, 1), (25, 1), (29, 1), (38, 1), (57, 2), (58, 1)] }, { coefficient := -2, powers := [(2, 1), (5, 1), (25, 1), (29, 1), (46, 1), (51, 1), (57, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (54, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (5, 1), (15, 1), (32, 1), (47, 1), (54, 1)] }, { coefficient := -1, powers := [(0, 1), (5, 1), (32, 1), (36, 1), (54, 1), (55, 1)] }, { coefficient := -1, powers := [(0, 1), (5, 1), (32, 1), (39, 1), (42, 1), (54, 1)] }, { coefficient := -1, powers := [(0, 1), (5, 1), (32, 1), (39, 1), (52, 1), (54, 1)] }, { coefficient := -1, powers := [(3, 1), (5, 1), (32, 1), (33, 1), (47, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (20, 1), (32, 1), (42, 1), (47, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (20, 1), (35, 1), (39, 1), (42, 1), (51, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (2, 2), (20, 1), (38, 1), (54, 1), (57, 1), (58, 2)] }, { coefficient := 2, powers := [(0, 1), (2, 2), (25, 1), (38, 1), (54, 1), (57, 1), (58, 2)] }, { coefficient := -2, powers := [(0, 1), (2, 1), (5, 1), (20, 1), (29, 1), (54, 1), (57, 1), (58, 2)] }, { coefficient := -2, powers := [(0, 1), (2, 1), (5, 1), (25, 1), (29, 1), (54, 1), (57, 1), (58, 2)] }, { coefficient := 2, powers := [(0, 1), (2, 1), (54, 1), (58, 1)] }, { coefficient := 1, powers := [(0, 1), (8, 1), (35, 1), (58, 1)] }, { coefficient := -2, powers := [(2, 2), (20, 1), (38, 1), (54, 1), (57, 1), (58, 1)] }, { coefficient := -2, powers := [(2, 2), (25, 1), (38, 1), (54, 1), (57, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (3, 1), (5, 1), (25, 1), (32, 1), (54, 2), (55, 1)] }, { coefficient := 2, powers := [(2, 1), (5, 1), (20, 1), (29, 1), (54, 1), (57, 1), (58, 1)] }, { coefficient := 2, powers := [(2, 1), (5, 1), (25, 1), (29, 1), (54, 1), (57, 1), (58, 1)] }, { coefficient := 2, powers := [(2, 1), (8, 1), (20, 1), (29, 1), (46, 1), (57, 1), (58, 1)] }, { coefficient := -2, powers := [(2, 1), (8, 1), (20, 1), (35, 1), (38, 1), (57, 1), (58, 1)] }, { coefficient := 2, powers := [(2, 1), (8, 1), (25, 1), (29, 1), (46, 1), (57, 1), (58, 1)] }, { coefficient := -2, powers := [(2, 1), (8, 1), (25, 1), (35, 1), (38, 1), (57, 1), (58, 1)] }, { coefficient := 1, powers := [(3, 1), (5, 1), (8, 1), (25, 1), (32, 1), (35, 1), (54, 1), (55, 1)] }]
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
    ¬ ∀ index : Fin 43,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component47.SelectedLeafB5_6.selectedHasNoCommonZero

end Krenn.Component47.SelectedLeafB5_6
