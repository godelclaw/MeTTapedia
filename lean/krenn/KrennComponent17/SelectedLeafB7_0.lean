import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component17.SelectedLeafB7_0

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "ca62e7b0aafb6ac9f79fc96d1cc863e7264a4943d7c8d042777e6ff24f7c5e32"
def certificateSHA256 : String := "4cf7658ff67fee1ce21a78bbf4afafabe2c23b60f65d3dceb7f307cf0cae2c3e"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 38 → Fin 608 := ![
  0,
  2,
  3,
  4,
  5,
  32,
  183,
  198,
  199,
  206,
  207,
  306,
  307,
  311,
  312,
  323,
  325,
  335,
  415,
  425,
  434,
  436,
  439,
  464,
  486,
  541,
  552,
  553,
  567,
  568,
  589,
  599,
  601,
  602,
  603,
  605,
  606,
  607
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 38 → SparsePoly (Fin 62) := ![
  [{ coefficient := 1, powers := [(1, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (52, 1)] }, { coefficient := 1, powers := [(19, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (47, 1)] }, { coefficient := 1, powers := [(18, 1), (20, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (51, 1)] }, { coefficient := -1, powers := [(17, 1), (25, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (19, 1)] }, { coefficient := 1, powers := [(17, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (43, 1)] }, { coefficient := 1, powers := [(18, 1), (19, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1)] }, { coefficient := 1, powers := [(19, 1), (43, 1)] }, { coefficient := 1, powers := [(24, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1)] }, { coefficient := 1, powers := [(20, 1), (43, 1)] }, { coefficient := 1, powers := [(24, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (58, 1)] }, { coefficient := 1, powers := [(13, 1), (47, 1)] }, { coefficient := 1, powers := [(18, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (56, 1)] }, { coefficient := 1, powers := [(9, 1), (53, 1)] }, { coefficient := 1, powers := [(14, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (45, 1)] }, { coefficient := 1, powers := [(18, 1), (40, 1)] }, { coefficient := 1, powers := [(18, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (52, 1)] }, { coefficient := 1, powers := [(29, 1), (41, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (36, 1), (56, 1)] }, { coefficient := 1, powers := [(1, 1), (39, 1), (53, 1)] }, { coefficient := 1, powers := [(1, 1), (42, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (24, 1), (45, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (40, 1)] }, { coefficient := 1, powers := [(18, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (51, 1)] }, { coefficient := 1, powers := [(3, 1), (25, 1), (57, 1)] }, { coefficient := 1, powers := [(19, 1), (51, 1)] }, { coefficient := 1, powers := [(25, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (52, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1)] }, { coefficient := 1, powers := [(13, 1), (29, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (35, 1)] }, { coefficient := 1, powers := [(22, 1), (43, 1)] }, { coefficient := 1, powers := [(27, 1), (43, 1)] }, { coefficient := 1, powers := [(35, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (30, 1)] }, { coefficient := 1, powers := [(12, 1), (25, 1)] }, { coefficient := 1, powers := [(17, 1), (19, 1), (25, 1), (49, 1)] }, { coefficient := 1, powers := [(17, 1), (25, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1), (51, 1)] }, { coefficient := 1, powers := [(20, 1), (43, 1), (51, 1)] }, { coefficient := 1, powers := [(20, 1), (55, 1)] }, { coefficient := 1, powers := [(25, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (29, 1), (58, 1)] }, { coefficient := 1, powers := [(3, 1), (32, 1), (55, 1)] }, { coefficient := 1, powers := [(3, 1), (35, 1), (52, 1)] }, { coefficient := 1, powers := [(22, 1), (43, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (43, 1), (51, 1)] }, { coefficient := 1, powers := [(23, 1), (55, 1)] }, { coefficient := 1, powers := [(29, 1), (47, 1)] }, { coefficient := 1, powers := [(35, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (38, 1), (58, 1)] }, { coefficient := 1, powers := [(0, 1), (41, 1), (55, 1)] }, { coefficient := 1, powers := [(0, 1), (47, 1), (52, 1)] }, { coefficient := 1, powers := [(20, 1), (43, 1), (52, 1)] }, { coefficient := 1, powers := [(25, 1), (41, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (40, 1), (53, 1)] }, { coefficient := 1, powers := [(6, 1), (33, 1), (40, 1)] }, { coefficient := 1, powers := [(14, 1), (24, 1), (40, 1)] }, { coefficient := 1, powers := [(14, 1)] }, { coefficient := 1, powers := [(53, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1)] }, { coefficient := 1, powers := [(3, 1), (33, 1)] }, { coefficient := 1, powers := [(14, 1), (19, 1)] }, { coefficient := 1, powers := [(19, 1), (53, 1)] }, { coefficient := 1, powers := [(24, 1), (42, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (48, 1)] }, { coefficient := 1, powers := [(6, 1), (30, 1)] }, { coefficient := 1, powers := [(9, 1), (24, 1)] }, { coefficient := 1, powers := [(19, 1), (48, 1)] }, { coefficient := 1, powers := [(24, 1), (39, 1)] }, { coefficient := 1, powers := [(30, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (30, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (30, 1), (47, 1)] }, { coefficient := 1, powers := [(12, 1), (20, 1), (55, 1)] }, { coefficient := 1, powers := [(12, 1), (25, 1), (47, 1)] }, { coefficient := 1, powers := [(18, 1), (20, 1), (25, 1), (49, 1)] }, { coefficient := 1, powers := [(18, 1), (30, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (36, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (39, 1), (53, 1)] }, { coefficient := 1, powers := [(0, 1), (42, 1), (48, 1)] }, { coefficient := 1, powers := [(3, 1), (24, 1), (56, 1)] }, { coefficient := 1, powers := [(3, 1), (30, 1), (53, 1)] }, { coefficient := 1, powers := [(3, 1), (33, 1), (48, 1)] }, { coefficient := 1, powers := [(6, 1), (19, 1), (56, 1)] }, { coefficient := 1, powers := [(6, 1), (30, 1), (42, 1)] }, { coefficient := 1, powers := [(6, 1), (33, 1), (39, 1)] }, { coefficient := 1, powers := [(9, 1), (19, 1), (53, 1)] }, { coefficient := 1, powers := [(9, 1), (24, 1), (42, 1)] }, { coefficient := 1, powers := [(9, 1), (33, 1), (36, 1)] }, { coefficient := 1, powers := [(14, 1), (19, 1), (48, 1)] }, { coefficient := 1, powers := [(14, 1), (24, 1), (39, 1)] }, { coefficient := 1, powers := [(14, 1), (30, 1), (36, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (41, 1), (55, 1)] }, { coefficient := 1, powers := [(2, 1), (47, 1), (52, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (52, 1)] }, { coefficient := 1, powers := [(8, 1), (23, 1), (58, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (47, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(13, 1), (23, 1), (55, 1)] }, { coefficient := 1, powers := [(13, 1), (29, 1), (47, 1)] }, { coefficient := 1, powers := [(13, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (52, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (41, 1)] }, { coefficient := 1, powers := [(18, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (59, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1), (60, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(39, 1)] }],
  [{ coefficient := 1, powers := [(40, 1)] }],
  [{ coefficient := 1, powers := [(41, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 38 → SparsePoly (Fin 62) := ![
  [{ coefficient := -1, powers := [(0, 1), (9, 1), (60, 1)] }, { coefficient := -1, powers := [(0, 1), (48, 1), (60, 1)] }, { coefficient := -1, powers := [(9, 1), (24, 1), (60, 1)] }, { coefficient := -1, powers := [(19, 1), (48, 1), (60, 1)] }, { coefficient := -1, powers := [(30, 1), (36, 1), (60, 1)] }],
  [{ coefficient := 2, powers := [(3, 1), (9, 1), (13, 1), (29, 1), (33, 1), (60, 1)] }, { coefficient := 2, powers := [(3, 1), (13, 1), (14, 1), (29, 1), (30, 1), (60, 1)] }, { coefficient := -2, powers := [(3, 1), (13, 1), (24, 1), (29, 1), (56, 1), (60, 1)] }, { coefficient := -2, powers := [(3, 1), (13, 1), (29, 1), (33, 1), (48, 1), (60, 1)] }, { coefficient := -1, powers := [(8, 1), (14, 1), (30, 1), (32, 1), (36, 1), (60, 1)] }, { coefficient := 1, powers := [(12, 1), (14, 1), (25, 1), (32, 1), (36, 1), (60, 1)] }, { coefficient := -2, powers := [(13, 1), (14, 1), (29, 1), (30, 1), (36, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (12, 1), (14, 1), (23, 1), (36, 1), (58, 1), (60, 1)] }, { coefficient := 1, powers := [(3, 1), (9, 1), (13, 1), (23, 1), (33, 1), (43, 1), (60, 1)] }, { coefficient := 1, powers := [(3, 1), (13, 1), (14, 1), (23, 1), (30, 1), (43, 1), (60, 1)] }, { coefficient := -1, powers := [(3, 1), (13, 1), (23, 1), (24, 1), (43, 1), (56, 1), (60, 1)] }, { coefficient := -1, powers := [(3, 1), (13, 1), (23, 1), (33, 1), (43, 1), (48, 1), (60, 1)] }, { coefficient := 1, powers := [(12, 1), (14, 1), (19, 1), (23, 1), (36, 1), (58, 1), (60, 1)] }, { coefficient := 1, powers := [(12, 1), (14, 1), (23, 1), (24, 1), (36, 1), (58, 1), (60, 1)] }, { coefficient := -1, powers := [(12, 1), (14, 1), (24, 1), (32, 1), (36, 1), (47, 1), (60, 1)] }, { coefficient := -1, powers := [(13, 1), (14, 1), (23, 1), (30, 1), (36, 1), (43, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (14, 1), (19, 1), (30, 1), (36, 1), (47, 1), (59, 1), (60, 1)] }, { coefficient := -1, powers := [(2, 1), (14, 1), (20, 1), (30, 1), (36, 1), (43, 1), (59, 1), (60, 1)] }, { coefficient := -1, powers := [(3, 1), (5, 1), (9, 1), (33, 1), (35, 1), (60, 1)] }, { coefficient := -1, powers := [(3, 1), (5, 1), (14, 1), (30, 1), (35, 1), (60, 1)] }, { coefficient := 1, powers := [(3, 1), (5, 1), (24, 1), (35, 1), (56, 1), (60, 1)] }, { coefficient := 1, powers := [(3, 1), (5, 1), (33, 1), (35, 1), (48, 1), (60, 1)] }, { coefficient := -1, powers := [(5, 1), (9, 1), (27, 1), (33, 1), (43, 1), (60, 1)] }, { coefficient := -1, powers := [(5, 1), (9, 1), (33, 1), (35, 1), (36, 1), (60, 1)] }, { coefficient := -1, powers := [(5, 1), (14, 1), (27, 1), (30, 1), (43, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (24, 1), (27, 1), (43, 1), (56, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (24, 1), (35, 1), (36, 1), (56, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (27, 1), (33, 1), (43, 1), (48, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (35, 1), (36, 1), (48, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (9, 1), (33, 1), (38, 1)] }, { coefficient := -1, powers := [(2, 1), (14, 1), (30, 1), (38, 1)] }, { coefficient := 1, powers := [(2, 1), (24, 1), (38, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (33, 1), (38, 1), (48, 1)] }, { coefficient := 1, powers := [(5, 1), (9, 1), (29, 1), (33, 1)] }, { coefficient := 1, powers := [(5, 1), (14, 1), (29, 1), (30, 1)] }, { coefficient := -1, powers := [(5, 1), (24, 1), (29, 1), (56, 1)] }, { coefficient := -1, powers := [(5, 1), (29, 1), (33, 1), (48, 1)] }, { coefficient := -1, powers := [(8, 1), (9, 1), (23, 1), (33, 1)] }, { coefficient := -1, powers := [(8, 1), (14, 1), (23, 1), (30, 1)] }, { coefficient := 1, powers := [(8, 1), (23, 1), (24, 1), (56, 1)] }, { coefficient := 1, powers := [(8, 1), (23, 1), (33, 1), (48, 1)] }, { coefficient := 1, powers := [(12, 1), (14, 1), (23, 1), (25, 1), (36, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (9, 1), (17, 1), (33, 1), (47, 1)] }, { coefficient := 1, powers := [(3, 1), (14, 1), (17, 1), (30, 1), (47, 1)] }, { coefficient := -1, powers := [(3, 1), (17, 1), (24, 1), (47, 1), (56, 1)] }, { coefficient := -1, powers := [(3, 1), (17, 1), (33, 1), (47, 1), (48, 1)] }, { coefficient := -1, powers := [(14, 1), (17, 1), (30, 1), (36, 1), (47, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (14, 1), (30, 1), (36, 1), (47, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(14, 1), (25, 1), (32, 1), (36, 1)] }],
  [{ coefficient := -1, powers := [(14, 1), (23, 1), (24, 1), (36, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(14, 1), (23, 1), (25, 1), (36, 1), (49, 1), (58, 1)] }, { coefficient := 1, powers := [(14, 1), (30, 1), (32, 1), (36, 1), (38, 1), (43, 1), (59, 1)] }, { coefficient := 1, powers := [(14, 1), (30, 1), (32, 1), (36, 1), (38, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (30, 1), (32, 1), (36, 1), (38, 1)] }],
  [{ coefficient := -1, powers := [(14, 1), (17, 1), (30, 1), (32, 1), (36, 1), (38, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (14, 1), (32, 1), (36, 1), (51, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (9, 1), (29, 1), (33, 1)] }, { coefficient := -1, powers := [(3, 1), (14, 1), (29, 1), (30, 1)] }, { coefficient := 1, powers := [(3, 1), (24, 1), (29, 1), (56, 1)] }, { coefficient := 1, powers := [(3, 1), (29, 1), (33, 1), (48, 1)] }, { coefficient := 1, powers := [(14, 1), (29, 1), (30, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(19, 1)] }],
  [{ coefficient := -1, powers := [(14, 1), (19, 1), (30, 1), (32, 1), (36, 1), (38, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (9, 1), (18, 1), (33, 1)] }, { coefficient := -1, powers := [(3, 1), (14, 1), (18, 1), (30, 1)] }, { coefficient := 1, powers := [(3, 1), (18, 1), (24, 1), (56, 1)] }, { coefficient := 1, powers := [(3, 1), (18, 1), (33, 1), (48, 1)] }, { coefficient := 1, powers := [(14, 1), (18, 1), (30, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(14, 1), (30, 1), (32, 1), (36, 1), (38, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (14, 1), (23, 1), (36, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (9, 1), (33, 1), (47, 1)] }, { coefficient := -1, powers := [(3, 1), (14, 1), (30, 1), (47, 1)] }, { coefficient := 1, powers := [(3, 1), (24, 1), (47, 1), (56, 1)] }, { coefficient := 1, powers := [(3, 1), (33, 1), (47, 1), (48, 1)] }, { coefficient := 1, powers := [(14, 1), (30, 1), (36, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (9, 1), (33, 1), (52, 1)] }, { coefficient := 1, powers := [(5, 1), (14, 1), (30, 1), (52, 1)] }, { coefficient := -1, powers := [(5, 1), (24, 1), (52, 1), (56, 1)] }, { coefficient := -1, powers := [(5, 1), (33, 1), (48, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (23, 1), (36, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (14, 1), (32, 1), (36, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (9, 1), (33, 1)] }, { coefficient := -1, powers := [(5, 1), (14, 1), (30, 1)] }, { coefficient := 1, powers := [(5, 1), (24, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (48, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (9, 1), (13, 1), (33, 1)] }, { coefficient := -1, powers := [(3, 1), (13, 1), (14, 1), (30, 1)] }, { coefficient := 1, powers := [(3, 1), (13, 1), (24, 1), (56, 1)] }, { coefficient := 1, powers := [(3, 1), (13, 1), (33, 1), (48, 1)] }, { coefficient := 1, powers := [(13, 1), (14, 1), (30, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (14, 1), (30, 1), (36, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (30, 1)] }, { coefficient := -1, powers := [(9, 1), (19, 1)] }],
  [{ coefficient := 1, powers := [(9, 1)] }],
  [{ coefficient := 1, powers := [(42, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (32, 1), (36, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(3, 1), (9, 1), (33, 1)] }, { coefficient := 1, powers := [(3, 1), (14, 1), (30, 1)] }, { coefficient := -1, powers := [(3, 1), (24, 1), (56, 1)] }, { coefficient := -1, powers := [(3, 1), (33, 1), (48, 1)] }, { coefficient := -1, powers := [(14, 1), (30, 1), (36, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (14, 1), (30, 1), (36, 1), (38, 1), (58, 1)] }, { coefficient := 1, powers := [(14, 1), (17, 1), (30, 1), (32, 1), (36, 1), (38, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (9, 1), (42, 1)] }, { coefficient := -1, powers := [(0, 1), (12, 1), (14, 1), (23, 1), (36, 1), (51, 1), (58, 1)] }, { coefficient := -1, powers := [(0, 1), (36, 1), (56, 1)] }, { coefficient := -1, powers := [(2, 1), (14, 1), (19, 1), (30, 1), (36, 1), (47, 1), (52, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (14, 1), (20, 1), (30, 1), (36, 1), (43, 1), (52, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (5, 1), (9, 1), (33, 1), (35, 1), (52, 1)] }, { coefficient := 1, powers := [(3, 1), (5, 1), (14, 1), (30, 1), (35, 1), (52, 1)] }, { coefficient := -1, powers := [(3, 1), (5, 1), (24, 1), (35, 1), (52, 1), (56, 1)] }, { coefficient := -1, powers := [(3, 1), (5, 1), (33, 1), (35, 1), (48, 1), (52, 1)] }, { coefficient := -1, powers := [(3, 1), (9, 1), (13, 1), (23, 1), (33, 1), (43, 1), (51, 1)] }, { coefficient := -2, powers := [(3, 1), (9, 1), (13, 1), (29, 1), (33, 1), (47, 1)] }, { coefficient := -1, powers := [(3, 1), (13, 1), (14, 1), (23, 1), (30, 1), (43, 1), (51, 1)] }, { coefficient := -2, powers := [(3, 1), (13, 1), (14, 1), (29, 1), (30, 1), (47, 1)] }, { coefficient := 1, powers := [(3, 1), (13, 1), (23, 1), (24, 1), (43, 1), (51, 1), (56, 1)] }, { coefficient := 1, powers := [(3, 1), (13, 1), (23, 1), (33, 1), (43, 1), (48, 1), (51, 1)] }, { coefficient := 2, powers := [(3, 1), (13, 1), (24, 1), (29, 1), (47, 1), (56, 1)] }, { coefficient := 2, powers := [(3, 1), (13, 1), (29, 1), (33, 1), (47, 1), (48, 1)] }, { coefficient := 1, powers := [(5, 1), (9, 1), (27, 1), (33, 1), (43, 1), (52, 1)] }, { coefficient := 1, powers := [(5, 1), (9, 1), (33, 1), (35, 1), (36, 1), (52, 1)] }, { coefficient := 1, powers := [(5, 1), (14, 1), (27, 1), (30, 1), (43, 1), (52, 1)] }, { coefficient := -1, powers := [(5, 1), (24, 1), (27, 1), (43, 1), (52, 1), (56, 1)] }, { coefficient := -1, powers := [(5, 1), (24, 1), (35, 1), (36, 1), (52, 1), (56, 1)] }, { coefficient := -1, powers := [(5, 1), (27, 1), (33, 1), (43, 1), (48, 1), (52, 1)] }, { coefficient := -1, powers := [(5, 1), (33, 1), (35, 1), (36, 1), (48, 1), (52, 1)] }, { coefficient := 1, powers := [(8, 1), (14, 1), (30, 1), (32, 1), (36, 1), (47, 1)] }, { coefficient := 1, powers := [(9, 1), (24, 1), (42, 1)] }, { coefficient := -1, powers := [(12, 1), (14, 1), (19, 1), (23, 1), (36, 1), (51, 1), (58, 1)] }, { coefficient := -1, powers := [(12, 1), (14, 1), (23, 1), (24, 1), (36, 1), (51, 1), (58, 1)] }, { coefficient := 1, powers := [(12, 1), (14, 1), (24, 1), (32, 1), (36, 1), (47, 1), (51, 1)] }, { coefficient := -1, powers := [(12, 1), (14, 1), (25, 1), (32, 1), (36, 1), (47, 1)] }, { coefficient := 1, powers := [(13, 1), (14, 1), (23, 1), (30, 1), (36, 1), (43, 1), (51, 1)] }, { coefficient := 2, powers := [(13, 1), (14, 1), (29, 1), (30, 1), (36, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (42, 1), (48, 1)] }, { coefficient := 1, powers := [(30, 1), (36, 1), (42, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (1, 1), (53, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (53, 1)] }, { coefficient := 1, powers := [(6, 1), (33, 1)] }, { coefficient := -1, powers := [(14, 1), (17, 1), (23, 1), (25, 1), (36, 1), (58, 1)] }, { coefficient := 1, powers := [(14, 1), (24, 1)] }, { coefficient := -1, powers := [(24, 1), (42, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (3, 1), (30, 1), (53, 1)] }, { coefficient := 1, powers := [(0, 1), (9, 1), (19, 1), (53, 1)] }, { coefficient := -1, powers := [(3, 1), (6, 1), (30, 1), (33, 1)] }, { coefficient := -1, powers := [(3, 1), (14, 1), (24, 1), (30, 1)] }, { coefficient := 1, powers := [(6, 1), (9, 1), (19, 1), (33, 1)] }, { coefficient := 1, powers := [(9, 1), (14, 1), (19, 1), (24, 1)] }, { coefficient := 1, powers := [(14, 1), (18, 1), (19, 1), (30, 1), (32, 1), (36, 1), (38, 1)] }, { coefficient := 1, powers := [(14, 1), (18, 1), (24, 1), (30, 1), (32, 1), (36, 1), (38, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (2, 1), (14, 1), (30, 1), (36, 1), (55, 1), (59, 1)] }, { coefficient := -1, powers := [(2, 1), (3, 1), (9, 1), (33, 1), (55, 1)] }, { coefficient := -1, powers := [(2, 1), (3, 1), (14, 1), (30, 1), (55, 1)] }, { coefficient := 1, powers := [(2, 1), (3, 1), (24, 1), (55, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (3, 1), (33, 1), (48, 1), (55, 1)] }, { coefficient := -1, powers := [(2, 1), (14, 1), (25, 1), (30, 1), (36, 1), (43, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (14, 1), (30, 1), (36, 1), (55, 1)] }, { coefficient := -1, powers := [(3, 1), (8, 1), (9, 1), (33, 1), (35, 1)] }, { coefficient := -1, powers := [(3, 1), (8, 1), (14, 1), (30, 1), (35, 1)] }, { coefficient := 1, powers := [(3, 1), (8, 1), (24, 1), (35, 1), (56, 1)] }, { coefficient := 1, powers := [(3, 1), (8, 1), (33, 1), (35, 1), (48, 1)] }, { coefficient := 1, powers := [(3, 1), (9, 1), (18, 1), (29, 1), (33, 1)] }, { coefficient := 1, powers := [(3, 1), (14, 1), (18, 1), (29, 1), (30, 1)] }, { coefficient := -1, powers := [(3, 1), (18, 1), (24, 1), (29, 1), (56, 1)] }, { coefficient := -1, powers := [(3, 1), (18, 1), (29, 1), (33, 1), (48, 1)] }, { coefficient := 1, powers := [(8, 1), (14, 1), (30, 1), (35, 1), (36, 1)] }, { coefficient := -1, powers := [(14, 1), (18, 1), (29, 1), (30, 1), (36, 1)] }]
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
    ¬ ∀ index : Fin 38,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component17.SelectedLeafB7_0.selectedHasNoCommonZero

end Krenn.Component17.SelectedLeafB7_0
