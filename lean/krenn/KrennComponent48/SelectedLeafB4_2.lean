import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component48.SelectedLeafB4_2

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "c11a1f2d13c48390d269bfdce89d8403f78b26d199f016b8c7a2f59d47bf4cce"
def certificateSHA256 : String := "b1d30d349c59696878f6305d59c070296adeaf47e18fa900d71cb7d35397435b"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 44 → Fin 641 := ![
  2,
  3,
  4,
  11,
  23,
  26,
  57,
  58,
  59,
  128,
  162,
  164,
  167,
  170,
  171,
  173,
  176,
  177,
  195,
  196,
  228,
  239,
  260,
  348,
  349,
  354,
  359,
  360,
  393,
  401,
  404,
  421,
  434,
  462,
  483,
  576,
  577,
  632,
  634,
  635,
  637,
  638,
  639,
  640
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 44 → SparsePoly (Fin 62) := ![
  [{ coefficient := 1, powers := [(3, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (20, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (33, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (33, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (36, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (33, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (48, 1)] }, { coefficient := 1, powers := [(25, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (53, 1)] }, { coefficient := 1, powers := [(20, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (47, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (52, 1)] }, { coefficient := 1, powers := [(18, 1), (30, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (36, 1)] }, { coefficient := 1, powers := [(36, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (33, 1)] }, { coefficient := 1, powers := [(33, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (31, 1)] }, { coefficient := 1, powers := [(18, 1), (26, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (26, 1)] }, { coefficient := 1, powers := [(26, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (47, 1)] }, { coefficient := -1, powers := [(18, 1), (21, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (20, 1)] }, { coefficient := 1, powers := [(18, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (30, 1), (58, 1)] }, { coefficient := 1, powers := [(30, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (24, 1), (58, 1)] }, { coefficient := 1, powers := [(24, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (26, 1), (47, 1)] }, { coefficient := 1, powers := [(31, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (48, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (53, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1)] }, { coefficient := 1, powers := [(12, 1), (30, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (45, 1)] }, { coefficient := 1, powers := [(12, 1), (55, 1)] }, { coefficient := 1, powers := [(18, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (53, 1)] }, { coefficient := 1, powers := [(30, 1), (42, 1)] }, { coefficient := 1, powers := [(33, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (56, 1)] }, { coefficient := 1, powers := [(30, 1), (48, 1)] }, { coefficient := 1, powers := [(36, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (30, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (33, 1), (56, 1)] }, { coefficient := 1, powers := [(3, 1), (36, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (31, 1), (56, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1), (48, 1)] }, { coefficient := 1, powers := [(19, 1), (31, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (24, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (33, 1), (48, 1)] }, { coefficient := 1, powers := [(6, 1), (36, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (20, 1), (55, 1)] }, { coefficient := 1, powers := [(12, 1)] }, { coefficient := 1, powers := [(18, 1), (20, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (20, 1), (50, 1)] }, { coefficient := 1, powers := [(18, 1), (20, 1), (55, 1)] }, { coefficient := 1, powers := [(18, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (34, 1)] }, { coefficient := 1, powers := [(17, 1), (21, 1)] }, { coefficient := 1, powers := [(18, 1), (21, 1), (25, 1), (44, 1)] }, { coefficient := 1, powers := [(18, 1), (21, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1), (49, 1)] }, { coefficient := 1, powers := [(6, 1), (31, 1), (45, 1)] }, { coefficient := 1, powers := [(9, 1), (25, 1), (45, 1)] }, { coefficient := 1, powers := [(49, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1)] }, { coefficient := 1, powers := [(3, 1), (34, 1)] }, { coefficient := 1, powers := [(13, 1), (20, 1)] }, { coefficient := 1, powers := [(20, 1), (54, 1)] }, { coefficient := 1, powers := [(25, 1), (43, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (49, 1)] }, { coefficient := 1, powers := [(6, 1), (31, 1)] }, { coefficient := 1, powers := [(9, 1), (25, 1)] }, { coefficient := 1, powers := [(20, 1), (49, 1)] }, { coefficient := 1, powers := [(25, 1), (40, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (37, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (40, 1), (54, 1)] }, { coefficient := 1, powers := [(0, 1), (43, 1), (49, 1)] }, { coefficient := 1, powers := [(3, 1), (25, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (31, 1), (54, 1)] }, { coefficient := 1, powers := [(3, 1), (34, 1), (49, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1), (57, 1)] }, { coefficient := 1, powers := [(6, 1), (31, 1), (43, 1)] }, { coefficient := 1, powers := [(6, 1), (34, 1), (40, 1)] }, { coefficient := 1, powers := [(9, 1), (20, 1), (54, 1)] }, { coefficient := 1, powers := [(9, 1), (25, 1), (43, 1)] }, { coefficient := 1, powers := [(9, 1), (34, 1), (37, 1)] }, { coefficient := 1, powers := [(13, 1), (20, 1), (49, 1)] }, { coefficient := 1, powers := [(13, 1), (25, 1), (40, 1)] }, { coefficient := 1, powers := [(13, 1), (31, 1), (37, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (39, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (42, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (48, 1), (53, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1), (53, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (59, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (48, 1)] }, { coefficient := 1, powers := [(8, 1), (36, 1), (42, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (56, 1)] }, { coefficient := 1, powers := [(12, 1), (30, 1), (48, 1)] }, { coefficient := 1, powers := [(12, 1), (36, 1), (39, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (53, 1)] }, { coefficient := 1, powers := [(19, 1), (30, 1), (42, 1)] }, { coefficient := 1, powers := [(19, 1), (33, 1), (39, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (60, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(40, 1)] }],
  [{ coefficient := 1, powers := [(41, 1), (61, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(42, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 44 → SparsePoly (Fin 62) := ![
  [{ coefficient := 1, powers := [(0, 2), (5, 1), (30, 1), (43, 1), (49, 1), (58, 1), (60, 1)] }, { coefficient := -1, powers := [(0, 1), (3, 1), (5, 1), (25, 1), (30, 1), (57, 1), (58, 1), (60, 1)] }, { coefficient := -1, powers := [(0, 1), (5, 1), (6, 1), (20, 1), (30, 1), (57, 1), (58, 1), (60, 1)] }, { coefficient := -1, powers := [(0, 1), (5, 1), (9, 1), (20, 1), (30, 1), (54, 1), (58, 1), (60, 1)] }, { coefficient := -1, powers := [(0, 1), (5, 1), (9, 1), (30, 1), (34, 1), (37, 1), (58, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (5, 1), (20, 1), (30, 1), (43, 1), (49, 1), (58, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (5, 1), (20, 1), (30, 1), (49, 1), (54, 1), (58, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (5, 1), (25, 1), (30, 1), (43, 1), (49, 1), (58, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (5, 1), (30, 1), (34, 1), (37, 1), (49, 1), (58, 1), (60, 1)] }, { coefficient := -1, powers := [(0, 1), (5, 1), (30, 1), (37, 1), (57, 1), (58, 1)] }, { coefficient := -1, powers := [(5, 1), (13, 1), (30, 1), (31, 1), (37, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (31, 1), (37, 1), (43, 1), (58, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (31, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (33, 1), (37, 1), (56, 1)] }, { coefficient := 1, powers := [(3, 1), (25, 1), (33, 1), (56, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1), (33, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(0, 2), (8, 1), (24, 1), (43, 1), (49, 1), (58, 1), (60, 1)] }, { coefficient := -1, powers := [(0, 1), (3, 1), (8, 1), (24, 1), (25, 1), (57, 1), (58, 1), (60, 1)] }, { coefficient := -1, powers := [(0, 1), (6, 1), (8, 1), (20, 1), (24, 1), (57, 1), (58, 1), (60, 1)] }, { coefficient := -1, powers := [(0, 1), (8, 1), (9, 1), (20, 1), (24, 1), (54, 1), (58, 1), (60, 1)] }, { coefficient := -1, powers := [(0, 1), (8, 1), (9, 1), (24, 1), (34, 1), (37, 1), (58, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (8, 1), (20, 1), (24, 1), (43, 1), (49, 1), (58, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (8, 1), (20, 1), (24, 1), (49, 1), (54, 1), (58, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (8, 1), (24, 1), (25, 1), (43, 1), (49, 1), (58, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (8, 1), (24, 1), (34, 1), (37, 1), (49, 1), (58, 1), (60, 1)] }, { coefficient := -1, powers := [(0, 1), (8, 1), (24, 1), (37, 1), (57, 1), (58, 1)] }, { coefficient := -1, powers := [(8, 1), (24, 1), (31, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (30, 1), (43, 1), (48, 1), (49, 1), (60, 1)] }, { coefficient := -1, powers := [(3, 1), (24, 1), (31, 1), (45, 1), (54, 1), (56, 1)] }, { coefficient := -1, powers := [(3, 1), (24, 1), (31, 1), (54, 1), (55, 1), (56, 1)] }, { coefficient := 1, powers := [(3, 1), (25, 1), (30, 1), (48, 1), (57, 1), (60, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1), (30, 1), (48, 1), (57, 1), (60, 1)] }, { coefficient := 1, powers := [(9, 1), (20, 1), (30, 1), (48, 1), (54, 1), (60, 1)] }, { coefficient := 1, powers := [(9, 1), (30, 1), (34, 1), (37, 1), (48, 1), (60, 1)] }, { coefficient := -1, powers := [(20, 1), (30, 1), (43, 1), (48, 1), (49, 1), (60, 1)] }, { coefficient := -1, powers := [(20, 1), (30, 1), (48, 1), (49, 1), (54, 1), (60, 1)] }, { coefficient := -1, powers := [(24, 1), (31, 1), (37, 1), (45, 1), (54, 1), (56, 1)] }, { coefficient := -1, powers := [(24, 1), (31, 1), (37, 1), (54, 1), (55, 1), (56, 1)] }, { coefficient := -1, powers := [(25, 1), (30, 1), (43, 1), (48, 1), (49, 1), (60, 1)] }, { coefficient := -1, powers := [(30, 1), (34, 1), (37, 1), (48, 1), (49, 1), (60, 1)] }, { coefficient := 1, powers := [(30, 1), (37, 1), (48, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (24, 1), (43, 1), (49, 1), (53, 1), (60, 1)] }, { coefficient := 1, powers := [(3, 1), (24, 1), (25, 1), (53, 1), (57, 1), (60, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1), (24, 1), (53, 1), (57, 1), (60, 1)] }, { coefficient := 1, powers := [(9, 1), (20, 1), (24, 1), (53, 1), (54, 1), (60, 1)] }, { coefficient := 1, powers := [(9, 1), (24, 1), (34, 1), (37, 1), (53, 1), (60, 1)] }, { coefficient := -1, powers := [(20, 1), (24, 1), (43, 1), (49, 1), (53, 1), (60, 1)] }, { coefficient := -1, powers := [(20, 1), (24, 1), (49, 1), (53, 1), (54, 1), (60, 1)] }, { coefficient := -1, powers := [(24, 1), (25, 1), (43, 1), (49, 1), (53, 1), (60, 1)] }, { coefficient := -1, powers := [(24, 1), (34, 1), (37, 1), (49, 1), (53, 1), (60, 1)] }, { coefficient := 1, powers := [(24, 1), (37, 1), (53, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (5, 1), (33, 1), (43, 1), (45, 1), (49, 1)] }, { coefficient := -1, powers := [(3, 1), (12, 1), (24, 1), (31, 1), (54, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (9, 1), (18, 1), (21, 1), (33, 2), (37, 1), (50, 1), (54, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (9, 1), (18, 1), (21, 1), (33, 2), (37, 1), (54, 1), (55, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (9, 1), (33, 1), (54, 1)] }, { coefficient := -1, powers := [(5, 1), (25, 1), (33, 1), (43, 1), (45, 1), (49, 1)] }, { coefficient := -1, powers := [(5, 1), (33, 1), (34, 1), (37, 1), (45, 1), (49, 1)] }, { coefficient := -1, powers := [(5, 1), (33, 1), (43, 1), (49, 1)] }, { coefficient := -1, powers := [(5, 1), (33, 1), (49, 1), (54, 1)] }, { coefficient := -1, powers := [(12, 1), (24, 1), (31, 1), (37, 1), (54, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (5, 1), (31, 1), (43, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (25, 1), (31, 1), (43, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (34, 1), (37, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (17, 1), (25, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (13, 1), (31, 1), (37, 1), (53, 1), (58, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (37, 1), (43, 1), (53, 1), (58, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(9, 1), (21, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (8, 1), (33, 1), (43, 1), (49, 1), (60, 1)] }, { coefficient := 1, powers := [(3, 1), (8, 1), (25, 1), (33, 1), (57, 1), (60, 1)] }, { coefficient := 1, powers := [(6, 1), (8, 1), (20, 1), (33, 1), (57, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (9, 1), (20, 1), (33, 1), (54, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (9, 1), (33, 1), (34, 1), (37, 1), (60, 1)] }, { coefficient := -1, powers := [(8, 1), (20, 1), (33, 1), (43, 1), (49, 1), (60, 1)] }, { coefficient := -1, powers := [(8, 1), (20, 1), (33, 1), (49, 1), (54, 1), (60, 1)] }, { coefficient := -1, powers := [(8, 1), (25, 1), (33, 1), (43, 1), (49, 1), (60, 1)] }, { coefficient := -1, powers := [(8, 1), (33, 1), (34, 1), (37, 1), (49, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (37, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (5, 1), (36, 1), (43, 1), (49, 1), (60, 1)] }, { coefficient := 1, powers := [(3, 1), (5, 1), (25, 1), (36, 1), (57, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (6, 1), (20, 1), (36, 1), (57, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (9, 1), (20, 1), (36, 1), (54, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (9, 1), (34, 1), (36, 1), (37, 1), (60, 1)] }, { coefficient := -1, powers := [(5, 1), (20, 1), (36, 1), (43, 1), (49, 1), (60, 1)] }, { coefficient := -1, powers := [(5, 1), (20, 1), (36, 1), (49, 1), (54, 1), (60, 1)] }, { coefficient := -1, powers := [(5, 1), (25, 1), (36, 1), (43, 1), (49, 1), (60, 1)] }, { coefficient := -1, powers := [(5, 1), (34, 1), (36, 1), (37, 1), (49, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1), (37, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (9, 1), (21, 1), (33, 1), (37, 1), (54, 1), (56, 1), (59, 1)] }, { coefficient := 1, powers := [(9, 1), (19, 1), (21, 1), (33, 1), (37, 1), (53, 1), (54, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (9, 1), (21, 1), (33, 1), (37, 1), (54, 1), (56, 1), (59, 1)] }, { coefficient := 1, powers := [(9, 1), (12, 1), (21, 1), (33, 1), (37, 1), (48, 1), (54, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (31, 1), (39, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (5, 1), (31, 1), (43, 1), (45, 1), (56, 1)] }, { coefficient := -1, powers := [(5, 1), (25, 1), (31, 1), (43, 1), (45, 1), (56, 1)] }, { coefficient := -1, powers := [(5, 1), (31, 1), (34, 1), (37, 1), (45, 1), (56, 1)] }, { coefficient := -1, powers := [(8, 1), (31, 1), (48, 1), (54, 1)] }, { coefficient := -1, powers := [(9, 1), (17, 1), (25, 1), (47, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (24, 1), (37, 1), (59, 1)] }, { coefficient := -1, powers := [(24, 1), (37, 1), (43, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (19, 1), (33, 1), (37, 1), (47, 1)] }, { coefficient := -1, powers := [(19, 1), (33, 1), (37, 1), (43, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (25, 1), (33, 1), (37, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (24, 1), (31, 1), (51, 1), (54, 1), (56, 1)] }, { coefficient := -1, powers := [(24, 1), (31, 1), (37, 1), (51, 1), (54, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [(0, 2), (5, 1), (43, 1), (49, 1), (59, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (3, 1), (5, 1), (25, 1), (57, 1), (59, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (5, 1), (6, 1), (20, 1), (57, 1), (59, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (5, 1), (9, 1), (20, 1), (54, 1), (59, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (5, 1), (9, 1), (34, 1), (37, 1), (59, 1), (60, 1)] }, { coefficient := -1, powers := [(0, 1), (5, 1), (20, 1), (43, 1), (49, 1), (59, 1), (60, 1)] }, { coefficient := -1, powers := [(0, 1), (5, 1), (20, 1), (49, 1), (54, 1), (59, 1), (60, 1)] }, { coefficient := -1, powers := [(0, 1), (5, 1), (25, 1), (43, 1), (49, 1), (59, 1), (60, 1)] }, { coefficient := -1, powers := [(0, 1), (5, 1), (34, 1), (37, 1), (49, 1), (59, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (5, 1), (37, 1), (57, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (13, 1), (31, 1), (37, 1), (59, 1)] }, { coefficient := -1, powers := [(5, 1), (31, 1), (37, 1), (43, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(0, 2), (8, 1), (43, 1), (49, 1), (59, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (3, 1), (8, 1), (25, 1), (57, 1), (59, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (6, 1), (8, 1), (20, 1), (57, 1), (59, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (8, 1), (9, 1), (20, 1), (54, 1), (59, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (8, 1), (9, 1), (34, 1), (37, 1), (59, 1), (60, 1)] }, { coefficient := -1, powers := [(0, 1), (8, 1), (20, 1), (43, 1), (49, 1), (59, 1), (60, 1)] }, { coefficient := -1, powers := [(0, 1), (8, 1), (20, 1), (49, 1), (54, 1), (59, 1), (60, 1)] }, { coefficient := -1, powers := [(0, 1), (8, 1), (25, 1), (43, 1), (49, 1), (59, 1), (60, 1)] }, { coefficient := -1, powers := [(0, 1), (8, 1), (34, 1), (37, 1), (49, 1), (59, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (8, 1), (37, 1), (57, 1), (59, 1)] }, { coefficient := -1, powers := [(13, 1), (19, 1), (31, 1), (37, 1), (53, 1)] }, { coefficient := 1, powers := [(19, 1), (31, 1), (37, 1), (43, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(13, 1), (19, 1), (33, 1), (37, 1)] }, { coefficient := 1, powers := [(19, 1), (33, 1), (37, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (20, 1), (43, 1), (49, 1), (53, 1), (60, 1)] }, { coefficient := -1, powers := [(3, 1), (20, 1), (25, 1), (53, 1), (57, 1), (60, 1)] }, { coefficient := 1, powers := [(6, 1), (13, 1), (31, 1), (37, 1), (53, 1), (58, 1)] }, { coefficient := -1, powers := [(6, 1), (20, 2), (53, 1), (57, 1), (60, 1)] }, { coefficient := -1, powers := [(6, 1), (31, 1), (37, 1), (43, 1), (53, 1), (58, 1)] }, { coefficient := -1, powers := [(9, 1), (18, 1), (21, 1), (33, 1), (37, 1), (53, 1), (54, 1), (56, 1)] }, { coefficient := -1, powers := [(9, 1), (20, 2), (53, 1), (54, 1), (60, 1)] }, { coefficient := -1, powers := [(9, 1), (20, 1), (34, 1), (37, 1), (53, 1), (60, 1)] }, { coefficient := 1, powers := [(13, 1), (31, 1), (37, 1), (53, 1)] }, { coefficient := 1, powers := [(20, 2), (43, 1), (49, 1), (53, 1), (60, 1)] }, { coefficient := 1, powers := [(20, 2), (49, 1), (53, 1), (54, 1), (60, 1)] }, { coefficient := 1, powers := [(20, 1), (25, 1), (43, 1), (49, 1), (53, 1), (60, 1)] }, { coefficient := 1, powers := [(20, 1), (34, 1), (37, 1), (49, 1), (53, 1), (60, 1)] }, { coefficient := -1, powers := [(20, 1), (37, 1), (53, 1), (57, 1)] }, { coefficient := -1, powers := [(31, 1), (37, 1), (43, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (25, 1), (43, 1), (48, 1), (49, 1), (60, 1)] }, { coefficient := -1, powers := [(3, 1), (25, 2), (48, 1), (57, 1), (60, 1)] }, { coefficient := 1, powers := [(3, 1), (31, 1), (48, 1), (54, 1)] }, { coefficient := -1, powers := [(6, 1), (20, 1), (25, 1), (48, 1), (57, 1), (60, 1)] }, { coefficient := -1, powers := [(9, 1), (18, 1), (21, 1), (33, 1), (37, 1), (48, 1), (54, 1), (56, 1)] }, { coefficient := -1, powers := [(9, 1), (20, 1), (25, 1), (48, 1), (54, 1), (60, 1)] }, { coefficient := -1, powers := [(9, 1), (25, 1), (34, 1), (37, 1), (48, 1), (60, 1)] }, { coefficient := 1, powers := [(20, 1), (25, 1), (43, 1), (48, 1), (49, 1), (60, 1)] }, { coefficient := 1, powers := [(20, 1), (25, 1), (48, 1), (49, 1), (54, 1), (60, 1)] }, { coefficient := 1, powers := [(25, 2), (43, 1), (48, 1), (49, 1), (60, 1)] }, { coefficient := 1, powers := [(25, 1), (34, 1), (37, 1), (48, 1), (49, 1), (60, 1)] }, { coefficient := -1, powers := [(25, 1), (37, 1), (48, 1), (57, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1), (48, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (24, 1), (25, 1), (31, 1), (54, 1), (56, 1)] }, { coefficient := 1, powers := [(24, 1), (25, 1), (31, 1), (37, 1), (54, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [(0, 2), (19, 1), (43, 1), (49, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (3, 1), (19, 1), (25, 1), (57, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (6, 1), (19, 1), (20, 1), (57, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (9, 1), (19, 1), (20, 1), (54, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (9, 1), (19, 1), (34, 1), (37, 1), (60, 1)] }, { coefficient := -1, powers := [(0, 1), (19, 1), (20, 1), (43, 1), (49, 1), (60, 1)] }, { coefficient := -1, powers := [(0, 1), (19, 1), (20, 1), (49, 1), (54, 1), (60, 1)] }, { coefficient := -1, powers := [(0, 1), (19, 1), (25, 1), (43, 1), (49, 1), (60, 1)] }, { coefficient := -1, powers := [(0, 1), (19, 1), (34, 1), (37, 1), (49, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (19, 1), (37, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (19, 1), (31, 1), (54, 1)] }, { coefficient := -1, powers := [(9, 1), (18, 1), (19, 1), (21, 1), (33, 1), (37, 1), (54, 1), (56, 1)] }, { coefficient := 1, powers := [(13, 1), (19, 1), (31, 1), (37, 1)] }, { coefficient := -1, powers := [(19, 1), (31, 1), (37, 1), (43, 1)] }],
  [{ coefficient := -1, powers := [(0, 2), (12, 1), (43, 1), (49, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (3, 1), (12, 1), (25, 1), (57, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (6, 1), (12, 1), (20, 1), (57, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (9, 1), (12, 1), (20, 1), (54, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (9, 1), (12, 1), (34, 1), (37, 1), (60, 1)] }, { coefficient := -1, powers := [(0, 1), (12, 1), (20, 1), (43, 1), (49, 1), (60, 1)] }, { coefficient := -1, powers := [(0, 1), (12, 1), (20, 1), (49, 1), (54, 1), (60, 1)] }, { coefficient := -1, powers := [(0, 1), (12, 1), (25, 1), (43, 1), (49, 1), (60, 1)] }, { coefficient := -1, powers := [(0, 1), (12, 1), (34, 1), (37, 1), (49, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (12, 1), (37, 1), (57, 1)] }, { coefficient := -1, powers := [(9, 1), (12, 1), (18, 1), (21, 1), (33, 1), (37, 1), (54, 1), (56, 1)] }, { coefficient := 1, powers := [(12, 1), (13, 1), (31, 1), (37, 1)] }, { coefficient := -1, powers := [(12, 1), (31, 1), (37, 1), (43, 1)] }, { coefficient := -1, powers := [(12, 1), (31, 1), (37, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (31, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (33, 1), (37, 1)] }, { coefficient := -1, powers := [(33, 1), (37, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (31, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (24, 1), (31, 1), (54, 1), (56, 1)] }, { coefficient := 1, powers := [(24, 1), (31, 1), (37, 1), (54, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (9, 1), (21, 1), (33, 2), (37, 1), (54, 1), (56, 2)] }],
  [{ coefficient := 1, powers := [(9, 1), (33, 1), (37, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (5, 1), (33, 1), (43, 1), (56, 1)] }, { coefficient := -1, powers := [(5, 1), (25, 1), (33, 1), (43, 1), (56, 1)] }, { coefficient := -1, powers := [(5, 1), (33, 1), (34, 1), (37, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(49, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (5, 1), (33, 1), (43, 1), (45, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (25, 1), (33, 1), (43, 1), (45, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (34, 1), (37, 1), (45, 1), (56, 1)] }, { coefficient := 1, powers := [(43, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 2), (43, 1), (49, 1), (60, 1)] }, { coefficient := -1, powers := [(0, 1), (3, 1), (25, 1), (57, 1), (60, 1)] }, { coefficient := -1, powers := [(0, 1), (6, 1), (20, 1), (57, 1), (60, 1)] }, { coefficient := -1, powers := [(0, 1), (9, 1), (20, 1), (54, 1), (60, 1)] }, { coefficient := -1, powers := [(0, 1), (9, 1), (34, 1), (37, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (20, 1), (43, 1), (49, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (20, 1), (49, 1), (54, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (25, 1), (43, 1), (49, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (34, 1), (37, 1), (49, 1), (60, 1)] }, { coefficient := -1, powers := [(0, 1), (37, 1), (57, 1)] }, { coefficient := -1, powers := [(3, 1), (31, 1), (54, 1)] }, { coefficient := 1, powers := [(9, 1), (18, 1), (21, 1), (33, 1), (37, 1), (54, 1), (56, 1)] }, { coefficient := -1, powers := [(13, 1), (31, 1), (37, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1), (43, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (5, 1), (33, 1), (43, 1), (49, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (43, 1), (49, 1)] }, { coefficient := 1, powers := [(3, 1), (5, 1), (25, 1), (33, 1), (56, 1), (57, 1)] }, { coefficient := -1, powers := [(3, 1), (25, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (6, 1), (20, 1), (33, 1), (56, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (9, 1), (20, 1), (33, 1), (54, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (9, 1), (33, 1), (34, 1), (37, 1), (56, 1)] }, { coefficient := -1, powers := [(5, 1), (20, 1), (33, 1), (43, 1), (49, 1), (56, 1)] }, { coefficient := -1, powers := [(5, 1), (20, 1), (33, 1), (49, 1), (54, 1), (56, 1)] }, { coefficient := -1, powers := [(5, 1), (25, 1), (33, 1), (43, 1), (49, 1), (56, 1)] }, { coefficient := -1, powers := [(5, 1), (33, 1), (34, 1), (37, 1), (49, 1), (56, 1)] }, { coefficient := -1, powers := [(6, 1), (20, 1), (57, 1)] }, { coefficient := -1, powers := [(9, 1), (20, 1), (54, 1)] }, { coefficient := -1, powers := [(9, 1), (34, 1), (37, 1)] }, { coefficient := 1, powers := [(20, 1), (43, 1), (49, 1)] }, { coefficient := 1, powers := [(20, 1), (49, 1), (54, 1)] }, { coefficient := 1, powers := [(25, 1), (43, 1), (49, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1), (49, 1)] }],
  [{ coefficient := -1, powers := [(0, 2), (39, 1), (43, 1), (49, 1), (59, 1), (60, 1)] }, { coefficient := -1, powers := [(0, 2), (43, 1), (48, 1), (49, 1), (53, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (3, 1), (25, 1), (39, 1), (57, 1), (59, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (3, 1), (25, 1), (48, 1), (53, 1), (57, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (6, 1), (20, 1), (39, 1), (57, 1), (59, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (6, 1), (20, 1), (48, 1), (53, 1), (57, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (9, 1), (20, 1), (39, 1), (54, 1), (59, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (9, 1), (20, 1), (48, 1), (53, 1), (54, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (9, 1), (34, 1), (37, 1), (39, 1), (59, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (9, 1), (34, 1), (37, 1), (48, 1), (53, 1), (60, 1)] }, { coefficient := -1, powers := [(0, 1), (20, 1), (39, 1), (43, 1), (49, 1), (59, 1), (60, 1)] }, { coefficient := -1, powers := [(0, 1), (20, 1), (39, 1), (49, 1), (54, 1), (59, 1), (60, 1)] }, { coefficient := -2, powers := [(0, 1), (20, 1), (43, 1), (48, 1), (49, 1), (53, 1), (60, 1)] }, { coefficient := -1, powers := [(0, 1), (20, 1), (48, 1), (49, 1), (53, 1), (54, 1), (60, 1)] }, { coefficient := -1, powers := [(0, 1), (25, 1), (39, 1), (43, 1), (49, 1), (59, 1), (60, 1)] }, { coefficient := -2, powers := [(0, 1), (25, 1), (43, 1), (48, 1), (49, 1), (53, 1), (60, 1)] }, { coefficient := -1, powers := [(0, 1), (34, 1), (37, 1), (39, 1), (49, 1), (59, 1), (60, 1)] }, { coefficient := -1, powers := [(0, 1), (34, 1), (37, 1), (48, 1), (49, 1), (53, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (37, 1), (39, 1), (57, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (37, 1), (48, 1), (53, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (20, 1), (25, 1), (48, 1), (53, 1), (57, 1), (60, 1)] }, { coefficient := 1, powers := [(3, 1), (25, 2), (48, 1), (53, 1), (57, 1), (60, 1)] }, { coefficient := 1, powers := [(3, 1), (31, 1), (39, 1), (54, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (9, 1), (21, 1), (33, 1), (37, 1), (52, 1), (54, 1), (56, 1), (59, 1)] }, { coefficient := -1, powers := [(6, 1), (13, 1), (31, 1), (37, 1), (48, 1), (53, 1), (58, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 2), (48, 1), (53, 1), (57, 1), (60, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1), (25, 1), (48, 1), (53, 1), (57, 1), (60, 1)] }, { coefficient := 1, powers := [(6, 1), (31, 1), (37, 1), (43, 1), (48, 1), (53, 1), (58, 1)] }, { coefficient := 1, powers := [(8, 1), (9, 1), (21, 1), (33, 1), (37, 1), (47, 1), (54, 1), (56, 1), (59, 1)] }, { coefficient := -1, powers := [(9, 1), (12, 1), (21, 1), (33, 1), (37, 1), (48, 1), (52, 1), (54, 1), (56, 1)] }, { coefficient := -1, powers := [(9, 1), (18, 1), (21, 1), (33, 1), (37, 1), (39, 1), (54, 1), (56, 1), (59, 1)] }, { coefficient := 1, powers := [(9, 1), (18, 1), (21, 1), (33, 1), (37, 1), (48, 1), (53, 1), (54, 1), (56, 1)] }, { coefficient := -1, powers := [(9, 1), (19, 1), (21, 1), (33, 1), (37, 1), (47, 1), (53, 1), (54, 1), (56, 1)] }, { coefficient := 1, powers := [(9, 1), (20, 2), (48, 1), (53, 1), (54, 1), (60, 1)] }, { coefficient := 1, powers := [(9, 1), (20, 1), (25, 1), (48, 1), (53, 1), (54, 1), (60, 1)] }, { coefficient := 1, powers := [(9, 1), (20, 1), (34, 1), (37, 1), (48, 1), (53, 1), (60, 1)] }, { coefficient := 1, powers := [(9, 1), (25, 1), (34, 1), (37, 1), (48, 1), (53, 1), (60, 1)] }, { coefficient := 1, powers := [(13, 1), (31, 1), (37, 1), (39, 1), (59, 1)] }, { coefficient := -1, powers := [(20, 2), (43, 1), (48, 1), (49, 1), (53, 1), (60, 1)] }, { coefficient := -1, powers := [(20, 2), (48, 1), (49, 1), (53, 1), (54, 1), (60, 1)] }, { coefficient := -2, powers := [(20, 1), (25, 1), (43, 1), (48, 1), (49, 1), (53, 1), (60, 1)] }, { coefficient := -1, powers := [(20, 1), (25, 1), (48, 1), (49, 1), (53, 1), (54, 1), (60, 1)] }, { coefficient := -1, powers := [(20, 1), (34, 1), (37, 1), (48, 1), (49, 1), (53, 1), (60, 1)] }, { coefficient := 1, powers := [(20, 1), (37, 1), (48, 1), (53, 1), (57, 1)] }, { coefficient := -1, powers := [(25, 2), (43, 1), (48, 1), (49, 1), (53, 1), (60, 1)] }, { coefficient := -1, powers := [(25, 1), (34, 1), (37, 1), (48, 1), (49, 1), (53, 1), (60, 1)] }, { coefficient := 1, powers := [(25, 1), (37, 1), (48, 1), (53, 1), (57, 1)] }, { coefficient := -1, powers := [(31, 1), (37, 1), (39, 1), (43, 1), (59, 1)] }, { coefficient := -1, powers := [(31, 1), (37, 1), (48, 1), (53, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (5, 1), (25, 1), (33, 1), (43, 1), (45, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (54, 1)] }, { coefficient := -1, powers := [(5, 1), (25, 2), (33, 1), (43, 1), (45, 1), (56, 1)] }, { coefficient := -1, powers := [(5, 1), (25, 1), (33, 1), (34, 1), (37, 1), (45, 1), (56, 1)] }, { coefficient := 1, powers := [(6, 1), (34, 1)] }, { coefficient := -1, powers := [(13, 1), (18, 1), (24, 1), (26, 1), (37, 1), (59, 1)] }, { coefficient := -1, powers := [(13, 1), (19, 1), (26, 1), (33, 1), (37, 1), (47, 1)] }, { coefficient := 1, powers := [(13, 1), (25, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (26, 1), (37, 1), (43, 1), (59, 1)] }, { coefficient := 1, powers := [(19, 1), (26, 1), (33, 1), (37, 1), (43, 1), (47, 1)] }, { coefficient := -1, powers := [(25, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (6, 1), (13, 1), (31, 1), (36, 1), (37, 1), (53, 1), (58, 1)] }, { coefficient := -1, powers := [(5, 1), (6, 1), (31, 1), (36, 1), (37, 1), (43, 1), (53, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(0, 2), (2, 1), (43, 1), (49, 1), (56, 1), (60, 1)] }, { coefficient := -1, powers := [(0, 2), (8, 1), (36, 1), (43, 1), (49, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (2, 1), (3, 1), (25, 1), (56, 1), (57, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (2, 1), (6, 1), (20, 1), (56, 1), (57, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (2, 1), (9, 1), (20, 1), (54, 1), (56, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (2, 1), (9, 1), (34, 1), (37, 1), (56, 1), (60, 1)] }, { coefficient := -1, powers := [(0, 1), (2, 1), (20, 1), (43, 1), (49, 1), (56, 1), (60, 1)] }, { coefficient := -1, powers := [(0, 1), (2, 1), (20, 1), (49, 1), (54, 1), (56, 1), (60, 1)] }, { coefficient := -1, powers := [(0, 1), (2, 1), (25, 1), (43, 1), (49, 1), (56, 1), (60, 1)] }, { coefficient := -1, powers := [(0, 1), (2, 1), (34, 1), (37, 1), (49, 1), (56, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (2, 1), (37, 1), (56, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (3, 1), (8, 1), (25, 1), (36, 1), (57, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (6, 1), (8, 1), (20, 1), (36, 1), (57, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (8, 1), (9, 1), (20, 1), (36, 1), (54, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (8, 1), (9, 1), (34, 1), (36, 1), (37, 1), (60, 1)] }, { coefficient := -1, powers := [(0, 1), (8, 1), (20, 1), (36, 1), (43, 1), (49, 1), (60, 1)] }, { coefficient := -1, powers := [(0, 1), (8, 1), (20, 1), (36, 1), (49, 1), (54, 1), (60, 1)] }, { coefficient := -1, powers := [(0, 1), (8, 1), (25, 1), (36, 1), (43, 1), (49, 1), (60, 1)] }, { coefficient := -1, powers := [(0, 1), (8, 1), (34, 1), (36, 1), (37, 1), (49, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (8, 1), (36, 1), (37, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (3, 1), (31, 1), (54, 1), (56, 1)] }, { coefficient := -1, powers := [(2, 1), (9, 1), (18, 1), (21, 1), (33, 1), (37, 1), (54, 1), (56, 2)] }, { coefficient := 1, powers := [(2, 1), (13, 1), (31, 1), (37, 1), (56, 1)] }, { coefficient := -1, powers := [(2, 1), (31, 1), (37, 1), (43, 1), (56, 1)] }, { coefficient := 1, powers := [(3, 1), (8, 1), (31, 1), (36, 1), (54, 1)] }, { coefficient := -1, powers := [(6, 1), (8, 1), (31, 1), (36, 1), (54, 1)] }, { coefficient := -1, powers := [(8, 1), (9, 1), (18, 1), (21, 1), (33, 1), (36, 1), (37, 1), (54, 1), (56, 1)] }, { coefficient := 1, powers := [(8, 1), (13, 1), (31, 1), (36, 1), (37, 1)] }, { coefficient := -1, powers := [(8, 1), (31, 1), (36, 1), (37, 1), (43, 1)] }]
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
    ¬ ∀ index : Fin 44,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component48.SelectedLeafB4_2.selectedHasNoCommonZero

end Krenn.Component48.SelectedLeafB4_2
