import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component60.SelectedLeafB0_0

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "1c456348aa243ff2c90f923ceb98be5bdfada786dc6d3cbd7e738322f75ca73e"
def certificateSHA256 : String := "f8dde4ea7113bd9f8893b2b81e8a05b57951cdf011d45fc453e59a3e6c6aeed6"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 50 → Fin 662 := ![
  7,
  9,
  22,
  25,
  149,
  150,
  151,
  168,
  169,
  179,
  194,
  198,
  206,
  211,
  237,
  256,
  292,
  301,
  302,
  303,
  308,
  314,
  315,
  316,
  359,
  383,
  387,
  422,
  434,
  436,
  443,
  446,
  453,
  460,
  463,
  491,
  556,
  578,
  599,
  600,
  601,
  608,
  645,
  653,
  655,
  656,
  658,
  659,
  660,
  661
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 50 → SparsePoly (Fin 61) := ![
  [{ coefficient := 1, powers := [(5, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (30, 1)] }, { coefficient := 1, powers := [(18, 1), (26, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (26, 1)] }, { coefficient := 1, powers := [(26, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (29, 1)] }, { coefficient := 1, powers := [(29, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (46, 1)] }, { coefficient := 1, powers := [(19, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (24, 1)] }, { coefficient := 1, powers := [(24, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (40, 1)] }, { coefficient := 1, powers := [(29, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (29, 1), (59, 1)] }, { coefficient := 1, powers := [(29, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (24, 1), (59, 1)] }, { coefficient := 1, powers := [(24, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (30, 1), (44, 1)] }, { coefficient := 1, powers := [(8, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (26, 1), (46, 1)] }, { coefficient := 1, powers := [(9, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (25, 1), (46, 1)] }, { coefficient := 1, powers := [(19, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (29, 1), (40, 1)] }, { coefficient := 1, powers := [(29, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1)] }, { coefficient := 1, powers := [(20, 1), (43, 1)] }, { coefficient := 1, powers := [(25, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (48, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1)] }, { coefficient := 1, powers := [(12, 1), (29, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (58, 1)] }, { coefficient := 1, powers := [(9, 1), (42, 1)] }, { coefficient := 1, powers := [(13, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (45, 1)] }, { coefficient := 1, powers := [(12, 1), (56, 1)] }, { coefficient := 1, powers := [(18, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1), (50, 1)] }, { coefficient := 1, powers := [(25, 1), (45, 1), (50, 1)] }, { coefficient := 1, powers := [(50, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1), (54, 1)] }, { coefficient := 1, powers := [(26, 1), (45, 1), (50, 1)] }, { coefficient := 1, powers := [(54, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (48, 1), (51, 1)] }, { coefficient := 1, powers := [(21, 1), (43, 1), (51, 1)] }, { coefficient := 1, powers := [(48, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (30, 1), (57, 1)] }, { coefficient := 1, powers := [(8, 1), (30, 1), (48, 1)] }, { coefficient := 1, powers := [(19, 1), (30, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (20, 1), (56, 1)] }, { coefficient := 1, powers := [(12, 1)] }, { coefficient := 1, powers := [(18, 1), (20, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (25, 1), (44, 1)] }, { coefficient := 1, powers := [(12, 1), (55, 1)] }, { coefficient := 1, powers := [(17, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1)] }, { coefficient := 1, powers := [(25, 1), (40, 1), (43, 1)] }, { coefficient := 1, powers := [(25, 1), (46, 1)] }, { coefficient := 1, powers := [(43, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (60, 1)] }, { coefficient := 1, powers := [(12, 1), (48, 1)] }, { coefficient := 1, powers := [(19, 1), (21, 1), (52, 1)] }, { coefficient := 1, powers := [(19, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (60, 1)] }, { coefficient := 1, powers := [(12, 1), (26, 1), (46, 1)] }, { coefficient := 1, powers := [(12, 1), (57, 1)] }, { coefficient := 1, powers := [(19, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (54, 1)] }, { coefficient := 1, powers := [(29, 1), (41, 1)] }, { coefficient := 1, powers := [(29, 1), (47, 1), (50, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (37, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(43, 1), (52, 1)] }, { coefficient := 1, powers := [(46, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1), (52, 1)] }, { coefficient := 1, powers := [(3, 1), (60, 1)] }, { coefficient := 1, powers := [(20, 1), (43, 1), (52, 1)] }, { coefficient := 1, powers := [(43, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1), (53, 1)] }, { coefficient := 1, powers := [(26, 1), (40, 1)] }, { coefficient := 1, powers := [(26, 1), (45, 1)] }, { coefficient := 1, powers := [(53, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1), (51, 1)] }, { coefficient := 1, powers := [(40, 1), (43, 1)] }, { coefficient := 1, powers := [(43, 1), (51, 1)] }, { coefficient := 1, powers := [(46, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (29, 1), (60, 1)] }, { coefficient := 1, powers := [(3, 1), (32, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (35, 1), (54, 1)] }, { coefficient := 1, powers := [(29, 1), (43, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (43, 1), (53, 1)] }, { coefficient := 1, powers := [(24, 1), (57, 1)] }, { coefficient := 1, powers := [(29, 1), (48, 1)] }, { coefficient := 1, powers := [(35, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1)] }, { coefficient := 1, powers := [(6, 1), (59, 1)] }, { coefficient := 1, powers := [(25, 1), (40, 1)] }, { coefficient := 1, powers := [(25, 1), (45, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (21, 1), (44, 1), (50, 1)] }, { coefficient := 1, powers := [(2, 1), (41, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (55, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (55, 1)] }, { coefficient := 1, powers := [(17, 1), (24, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1)] }, { coefficient := 1, powers := [(3, 1), (33, 1)] }, { coefficient := 1, powers := [(13, 1), (20, 1)] }, { coefficient := 1, powers := [(20, 1), (55, 1)] }, { coefficient := 1, powers := [(25, 1), (42, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (49, 1)] }, { coefficient := 1, powers := [(6, 1), (30, 1)] }, { coefficient := 1, powers := [(9, 1), (25, 1)] }, { coefficient := 1, powers := [(20, 1), (49, 1)] }, { coefficient := 1, powers := [(25, 1), (39, 1)] }, { coefficient := 1, powers := [(30, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (46, 1), (53, 1)] }, { coefficient := 1, powers := [(26, 1), (40, 1), (43, 1)] }, { coefficient := 1, powers := [(26, 1), (46, 1)] }, { coefficient := 1, powers := [(43, 1), (53, 1)] }, { coefficient := 1, powers := [(57, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (40, 1), (55, 1)] }, { coefficient := 1, powers := [(0, 1), (44, 1)] }, { coefficient := 1, powers := [(6, 1), (33, 1), (40, 1)] }, { coefficient := 1, powers := [(13, 1), (25, 1), (40, 1)] }, { coefficient := 1, powers := [(13, 1)] }, { coefficient := 1, powers := [(25, 1), (44, 1)] }, { coefficient := 1, powers := [(55, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (36, 1), (58, 1)] }, { coefficient := 1, powers := [(0, 1), (39, 1), (55, 1)] }, { coefficient := 1, powers := [(0, 1), (42, 1), (49, 1)] }, { coefficient := 1, powers := [(3, 1), (25, 1), (58, 1)] }, { coefficient := 1, powers := [(3, 1), (30, 1), (55, 1)] }, { coefficient := 1, powers := [(3, 1), (33, 1), (49, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1), (58, 1)] }, { coefficient := 1, powers := [(6, 1), (30, 1), (42, 1)] }, { coefficient := 1, powers := [(6, 1), (33, 1), (39, 1)] }, { coefficient := 1, powers := [(9, 1), (20, 1), (55, 1)] }, { coefficient := 1, powers := [(9, 1), (25, 1), (42, 1)] }, { coefficient := 1, powers := [(9, 1), (33, 1), (36, 1)] }, { coefficient := 1, powers := [(13, 1), (20, 1), (49, 1)] }, { coefficient := 1, powers := [(13, 1), (25, 1), (39, 1)] }, { coefficient := 1, powers := [(13, 1), (30, 1), (36, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (41, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (48, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (48, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1), (29, 1), (48, 1)] }, { coefficient := 1, powers := [(12, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (54, 1)] }, { coefficient := 1, powers := [(19, 1), (29, 1), (41, 1)] }, { coefficient := 1, powers := [(19, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1)] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(39, 1)] }],
  [{ coefficient := 1, powers := [(40, 1)] }],
  [{ coefficient := 1, powers := [(41, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 50 → SparsePoly (Fin 61) := ![
  [{ coefficient := 1, powers := [(6, 1), (20, 1), (29, 1), (60, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1), (32, 1), (57, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1), (35, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (13, 1), (20, 1), (29, 1)] }, { coefficient := 1, powers := [(12, 1), (13, 1), (25, 1), (29, 1)] }, { coefficient := -1, powers := [(12, 1), (20, 1), (29, 1), (55, 1)] }, { coefficient := 1, powers := [(12, 1), (25, 1), (29, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (9, 1), (12, 1), (33, 1), (53, 1)] }, { coefficient := -1, powers := [(3, 1), (12, 1), (30, 1), (53, 1), (55, 1)] }, { coefficient := -1, powers := [(3, 1), (12, 1), (33, 1), (49, 1), (53, 1)] }, { coefficient := 1, powers := [(6, 1), (12, 1), (13, 1), (30, 1), (53, 1)] }, { coefficient := -1, powers := [(6, 1), (12, 1), (20, 1), (53, 1), (58, 1)] }, { coefficient := -1, powers := [(6, 1), (12, 1), (30, 1), (42, 1), (53, 1)] }, { coefficient := 1, powers := [(9, 1), (12, 1), (13, 1), (20, 1), (53, 1)] }, { coefficient := 1, powers := [(9, 1), (12, 1), (13, 1), (25, 1), (53, 1)] }, { coefficient := 1, powers := [(9, 1), (12, 1), (25, 1), (42, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (9, 1), (19, 1), (33, 1), (47, 1)] }, { coefficient := -1, powers := [(3, 1), (19, 1), (30, 1), (47, 1), (55, 1)] }, { coefficient := -1, powers := [(3, 1), (19, 1), (33, 1), (47, 1), (49, 1)] }, { coefficient := 1, powers := [(5, 1), (9, 1), (33, 1), (43, 1)] }, { coefficient := -1, powers := [(5, 1), (30, 1), (43, 1), (55, 1)] }, { coefficient := -1, powers := [(5, 1), (33, 1), (43, 1), (49, 1)] }, { coefficient := -1, powers := [(6, 1), (19, 1), (20, 1), (47, 1), (58, 1)] }, { coefficient := 1, powers := [(9, 1), (13, 1), (19, 1), (20, 1), (47, 1)] }, { coefficient := 1, powers := [(9, 1), (13, 1), (19, 1), (25, 1), (47, 1)] }, { coefficient := 1, powers := [(9, 1), (19, 1), (25, 1), (42, 1), (47, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (13, 1), (24, 1), (60, 1)] }, { coefficient := 1, powers := [(6, 1), (13, 1), (32, 1), (48, 1)] }, { coefficient := -1, powers := [(6, 1), (20, 1), (24, 1), (44, 1), (60, 1)] }, { coefficient := 1, powers := [(6, 1), (24, 1), (42, 1), (60, 1)] }, { coefficient := -1, powers := [(6, 1), (32, 1), (42, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (13, 1), (20, 1), (32, 1), (46, 1)] }, { coefficient := 1, powers := [(5, 1), (13, 1), (25, 1), (32, 1), (46, 1)] }, { coefficient := -1, powers := [(5, 1), (20, 1), (32, 1), (46, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (25, 1), (32, 1), (42, 1), (46, 1)] }, { coefficient := -1, powers := [(12, 1), (13, 1), (20, 1), (24, 1), (46, 1)] }, { coefficient := -1, powers := [(12, 1), (13, 1), (24, 1), (25, 1), (46, 1)] }, { coefficient := 1, powers := [(12, 1), (20, 1), (24, 1), (46, 1), (55, 1)] }, { coefficient := -1, powers := [(12, 1), (24, 1), (25, 1), (42, 1), (46, 1)] }, { coefficient := -2, powers := [(13, 1), (19, 1), (20, 1), (24, 1), (45, 1), (50, 1)] }, { coefficient := -1, powers := [(13, 1), (19, 1), (20, 1), (24, 1), (52, 1)] }, { coefficient := -2, powers := [(13, 1), (19, 1), (24, 1), (25, 1), (45, 1), (50, 1)] }, { coefficient := -1, powers := [(13, 1), (19, 1), (24, 1), (25, 1), (52, 1)] }, { coefficient := 2, powers := [(19, 1), (20, 1), (24, 1), (45, 1), (50, 1), (55, 1)] }, { coefficient := 1, powers := [(19, 1), (20, 1), (24, 1), (52, 1), (55, 1)] }, { coefficient := -2, powers := [(19, 1), (24, 1), (25, 1), (42, 1), (45, 1), (50, 1)] }, { coefficient := -1, powers := [(19, 1), (24, 1), (25, 1), (42, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (13, 1), (20, 1), (60, 1)] }, { coefficient := -1, powers := [(5, 1), (13, 1), (25, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (20, 1), (55, 1), (60, 1)] }, { coefficient := -1, powers := [(5, 1), (25, 1), (42, 1), (60, 1)] }, { coefficient := -1, powers := [(6, 1), (12, 1), (20, 1), (42, 1), (48, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (13, 1), (21, 1), (29, 1), (30, 1)] }, { coefficient := -1, powers := [(6, 1), (21, 1), (29, 1), (30, 1), (42, 1)] }, { coefficient := -1, powers := [(9, 1), (13, 1), (20, 1), (21, 1), (29, 1)] }, { coefficient := 1, powers := [(9, 1), (13, 1), (20, 1), (24, 1), (26, 1)] }, { coefficient := 1, powers := [(9, 1), (13, 1), (24, 1), (25, 1), (26, 1)] }, { coefficient := -1, powers := [(9, 1), (20, 1), (24, 1), (26, 1), (55, 1)] }, { coefficient := 1, powers := [(9, 1), (24, 1), (25, 1), (26, 1), (42, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (9, 1), (20, 1), (60, 1)] }, { coefficient := 1, powers := [(9, 1), (12, 1), (20, 1), (57, 1)] }, { coefficient := 1, powers := [(9, 1), (19, 1), (20, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (9, 1), (12, 1), (20, 1), (33, 1), (48, 1)] }, { coefficient := -1, powers := [(3, 1), (12, 1), (20, 1), (30, 1), (48, 1), (55, 1)] }, { coefficient := -1, powers := [(3, 1), (12, 1), (20, 1), (33, 1), (48, 1), (49, 1)] }, { coefficient := 1, powers := [(6, 1), (12, 1), (13, 1), (20, 1), (30, 1), (48, 1)] }, { coefficient := -1, powers := [(6, 1), (12, 1), (20, 1), (30, 1), (42, 1), (48, 1)] }, { coefficient := 1, powers := [(9, 1), (12, 1), (20, 2), (48, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (12, 1), (20, 1), (48, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(9, 1), (13, 1), (19, 1), (20, 1), (50, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (20, 1), (24, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (13, 1), (20, 1), (32, 1)] }, { coefficient := -1, powers := [(5, 1), (13, 1), (25, 1), (32, 1)] }, { coefficient := 1, powers := [(5, 1), (20, 1), (32, 1), (55, 1)] }, { coefficient := -1, powers := [(5, 1), (25, 1), (32, 1), (42, 1)] }, { coefficient := 1, powers := [(12, 1), (13, 1), (20, 1), (24, 1)] }, { coefficient := 1, powers := [(12, 1), (13, 1), (24, 1), (25, 1)] }, { coefficient := -1, powers := [(12, 1), (20, 1), (24, 1), (55, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (25, 1), (42, 1)] }],
  [{ coefficient := -1, powers := [(9, 1), (13, 1), (20, 1), (24, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (9, 1), (20, 1), (25, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (9, 1), (24, 1), (33, 1), (52, 1)] }, { coefficient := -1, powers := [(8, 1), (24, 1), (30, 1), (52, 1), (55, 1)] }, { coefficient := -1, powers := [(8, 1), (24, 1), (33, 1), (49, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (13, 1), (30, 1), (54, 1)] }, { coefficient := 1, powers := [(6, 1), (30, 1), (42, 1), (54, 1)] }, { coefficient := -1, powers := [(9, 1), (13, 1), (20, 1), (54, 1)] }, { coefficient := -1, powers := [(9, 1), (13, 1), (25, 1), (54, 1)] }, { coefficient := -1, powers := [(9, 1), (25, 1), (42, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (9, 1), (33, 1), (48, 1)] }, { coefficient := 1, powers := [(3, 1), (30, 1), (48, 1), (55, 1)] }, { coefficient := 1, powers := [(3, 1), (33, 1), (48, 1), (49, 1)] }, { coefficient := -1, powers := [(6, 1), (13, 1), (30, 1), (48, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1), (48, 1), (58, 1)] }, { coefficient := 1, powers := [(6, 1), (30, 1), (42, 1), (48, 1)] }, { coefficient := -1, powers := [(9, 1), (13, 1), (20, 1), (48, 1)] }, { coefficient := -1, powers := [(9, 1), (13, 1), (25, 1), (48, 1)] }, { coefficient := -1, powers := [(9, 1), (25, 1), (42, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (12, 1), (20, 1), (29, 1), (48, 1), (59, 1)] }, { coefficient := 1, powers := [(25, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (9, 1), (20, 1), (29, 1), (33, 1), (48, 1)] }, { coefficient := 1, powers := [(3, 1), (20, 1), (29, 1), (30, 1), (48, 1), (55, 1)] }, { coefficient := 1, powers := [(3, 1), (20, 1), (29, 1), (33, 1), (48, 1), (49, 1)] }, { coefficient := -1, powers := [(6, 1), (13, 1), (20, 1), (29, 1), (30, 1), (48, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1), (29, 1), (30, 1), (42, 1), (48, 1)] }, { coefficient := -1, powers := [(9, 1), (20, 2), (29, 1), (48, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(9, 1), (13, 1), (19, 1), (20, 1), (24, 1), (53, 1)] }],
  [{ coefficient := 2, powers := [(9, 1), (13, 1), (19, 1), (24, 1), (25, 1)] }, { coefficient := -2, powers := [(9, 1), (19, 1), (20, 1), (24, 1), (55, 1)] }, { coefficient := 2, powers := [(9, 1), (19, 1), (24, 1), (25, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (12, 1), (13, 1), (29, 1), (30, 1)] }, { coefficient := -1, powers := [(6, 1), (12, 1), (29, 1), (30, 1), (42, 1)] }, { coefficient := -1, powers := [(9, 1), (12, 1), (13, 1), (20, 1), (29, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (13, 1), (32, 1)] }, { coefficient := 1, powers := [(6, 1), (32, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (9, 1), (29, 1), (33, 1), (48, 1)] }, { coefficient := -1, powers := [(3, 1), (29, 1), (30, 1), (48, 1), (55, 1)] }, { coefficient := -1, powers := [(3, 1), (29, 1), (33, 1), (48, 1), (49, 1)] }, { coefficient := 1, powers := [(6, 1), (13, 1), (29, 1), (30, 1), (48, 1)] }, { coefficient := -1, powers := [(6, 1), (29, 1), (30, 1), (42, 1), (48, 1)] }, { coefficient := 1, powers := [(9, 1), (20, 1), (29, 1), (48, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (20, 1), (24, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (9, 1), (24, 1), (33, 1), (50, 1)] }, { coefficient := -1, powers := [(8, 1), (24, 1), (30, 1), (50, 1), (55, 1)] }, { coefficient := -1, powers := [(8, 1), (24, 1), (33, 1), (49, 1), (50, 1)] }, { coefficient := 1, powers := [(9, 1), (12, 1), (13, 1), (20, 1), (24, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (13, 1), (29, 1), (30, 1)] }, { coefficient := 1, powers := [(6, 1), (29, 1), (30, 1), (42, 1)] }, { coefficient := 1, powers := [(9, 1), (13, 1), (20, 1), (29, 1)] }],
  [{ coefficient := -1, powers := [(9, 1), (13, 1), (24, 1), (25, 1)] }, { coefficient := 1, powers := [(9, 1), (20, 1), (24, 1), (55, 1)] }, { coefficient := -1, powers := [(9, 1), (24, 1), (25, 1), (42, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (9, 1), (19, 1), (33, 1)] }, { coefficient := 1, powers := [(3, 1), (19, 1), (30, 1), (55, 1)] }, { coefficient := 1, powers := [(3, 1), (19, 1), (33, 1), (49, 1)] }, { coefficient := 1, powers := [(6, 1), (19, 1), (20, 1), (58, 1)] }, { coefficient := -1, powers := [(9, 1), (13, 1), (19, 1), (20, 1)] }, { coefficient := -1, powers := [(9, 1), (13, 1), (19, 1), (25, 1)] }, { coefficient := -1, powers := [(9, 1), (19, 1), (25, 1), (42, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (9, 1), (24, 1), (25, 1), (33, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (25, 1), (30, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (25, 1), (33, 1), (49, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (9, 1), (24, 1), (33, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (30, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (33, 1), (49, 1)] }],
  [{ coefficient := 2, powers := [(9, 1), (13, 1), (19, 1), (20, 1), (24, 1), (50, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (12, 1), (13, 1), (21, 1), (29, 1), (30, 1)] }, { coefficient := 1, powers := [(6, 1), (12, 1), (21, 1), (29, 1), (30, 1), (42, 1)] }, { coefficient := 1, powers := [(9, 1), (12, 1), (13, 1), (20, 1), (21, 1), (29, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (9, 1), (33, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (49, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (9, 1), (12, 1), (33, 1)] }, { coefficient := 1, powers := [(3, 1), (12, 1), (30, 1), (55, 1)] }, { coefficient := 1, powers := [(3, 1), (12, 1), (33, 1), (49, 1)] }, { coefficient := -1, powers := [(6, 1), (12, 1), (13, 1), (30, 1)] }, { coefficient := 1, powers := [(6, 1), (12, 1), (20, 1), (58, 1)] }, { coefficient := 1, powers := [(6, 1), (12, 1), (30, 1), (42, 1)] }, { coefficient := -1, powers := [(9, 1), (12, 1), (13, 1), (20, 1)] }, { coefficient := -1, powers := [(9, 1), (12, 1), (13, 1), (25, 1)] }, { coefficient := -1, powers := [(9, 1), (12, 1), (25, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (13, 1), (19, 1), (20, 1), (24, 1), (50, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(9, 1), (20, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(9, 1)] }],
  [{ coefficient := 1, powers := [(13, 1)] }],
  [{ coefficient := -1, powers := [(9, 1), (12, 1), (13, 1), (20, 1), (24, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (9, 1), (20, 1), (29, 1), (60, 1)] }, { coefficient := -1, powers := [(9, 1), (12, 1), (20, 1), (24, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(3, 1), (9, 1), (33, 1)] }, { coefficient := -1, powers := [(3, 1), (30, 1), (55, 1)] }, { coefficient := -1, powers := [(3, 1), (33, 1), (49, 1)] }, { coefficient := 1, powers := [(6, 1), (13, 1), (30, 1)] }, { coefficient := -1, powers := [(6, 1), (20, 1), (58, 1)] }, { coefficient := -1, powers := [(6, 1), (30, 1), (42, 1)] }, { coefficient := 1, powers := [(9, 1), (13, 1), (20, 1)] }, { coefficient := 1, powers := [(9, 1), (13, 1), (25, 1)] }, { coefficient := 1, powers := [(9, 1), (25, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (9, 1), (20, 1), (29, 1), (44, 1), (60, 1)] }, { coefficient := 1, powers := [(6, 1), (12, 1), (13, 1), (21, 1), (29, 1), (30, 1), (46, 1), (51, 1)] }, { coefficient := -1, powers := [(6, 1), (12, 1), (13, 1), (29, 1), (30, 1), (48, 1), (51, 1)] }, { coefficient := -1, powers := [(6, 1), (12, 1), (21, 1), (29, 1), (30, 1), (42, 1), (46, 1), (51, 1)] }, { coefficient := 1, powers := [(6, 1), (12, 1), (29, 1), (30, 1), (42, 1), (48, 1), (51, 1)] }, { coefficient := 1, powers := [(8, 1), (9, 1), (24, 1), (25, 1), (33, 1), (37, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (9, 1), (24, 1), (25, 1), (33, 1), (46, 1), (52, 1)] }, { coefficient := -1, powers := [(8, 1), (9, 1), (24, 1), (33, 1), (46, 1), (50, 1)] }, { coefficient := -1, powers := [(8, 1), (24, 1), (25, 1), (30, 1), (37, 1), (55, 1), (60, 1)] }, { coefficient := -1, powers := [(8, 1), (24, 1), (25, 1), (30, 1), (46, 1), (52, 1), (55, 1)] }, { coefficient := -1, powers := [(8, 1), (24, 1), (25, 1), (33, 1), (37, 1), (49, 1), (60, 1)] }, { coefficient := -1, powers := [(8, 1), (24, 1), (25, 1), (33, 1), (46, 1), (49, 1), (52, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (30, 1), (46, 1), (50, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (33, 1), (46, 1), (49, 1), (50, 1)] }, { coefficient := -1, powers := [(9, 1), (12, 1), (13, 1), (20, 1), (21, 1), (29, 1), (46, 1), (51, 1)] }, { coefficient := 1, powers := [(9, 1), (12, 1), (13, 1), (20, 1), (29, 1), (48, 1), (51, 1)] }, { coefficient := 1, powers := [(9, 1), (12, 1), (20, 1), (24, 1), (44, 1), (57, 1)] }, { coefficient := -2, powers := [(9, 1), (13, 1), (19, 1), (20, 1), (24, 1), (45, 1), (50, 1), (53, 1)] }, { coefficient := -2, powers := [(9, 1), (13, 1), (19, 1), (24, 1), (25, 1), (45, 1), (54, 1)] }, { coefficient := 2, powers := [(9, 1), (19, 1), (20, 1), (24, 1), (45, 1), (54, 1), (55, 1)] }, { coefficient := -2, powers := [(9, 1), (19, 1), (24, 1), (25, 1), (42, 1), (45, 1), (54, 1)] }, { coefficient := -1, powers := [(9, 1), (42, 1)] }, { coefficient := -1, powers := [(13, 1), (49, 1)] }, { coefficient := 1, powers := [(36, 1), (58, 1)] }, { coefficient := 1, powers := [(42, 1), (49, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (9, 1), (33, 1), (38, 1), (60, 1)] }, { coefficient := 1, powers := [(3, 1), (30, 1), (38, 1), (55, 1), (60, 1)] }, { coefficient := 1, powers := [(3, 1), (33, 1), (38, 1), (49, 1), (60, 1)] }, { coefficient := -1, powers := [(6, 1), (13, 1), (30, 1), (38, 1), (60, 1)] }, { coefficient := 1, powers := [(6, 1), (13, 1), (30, 1), (48, 1), (54, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1), (38, 1), (58, 1), (60, 1)] }, { coefficient := 1, powers := [(6, 1), (30, 1), (38, 1), (42, 1), (60, 1)] }, { coefficient := -1, powers := [(6, 1), (30, 1), (42, 1), (48, 1), (54, 1)] }, { coefficient := -1, powers := [(9, 1), (13, 1), (20, 1), (38, 1), (60, 1)] }, { coefficient := 1, powers := [(9, 1), (13, 1), (20, 1), (48, 1), (54, 1)] }, { coefficient := -1, powers := [(9, 1), (13, 1), (25, 1), (38, 1), (60, 1)] }, { coefficient := 1, powers := [(9, 1), (13, 1), (25, 1), (48, 1), (54, 1)] }, { coefficient := 1, powers := [(9, 1), (20, 1), (21, 1), (44, 1), (50, 1), (57, 1)] }, { coefficient := -1, powers := [(9, 1), (25, 1), (38, 1), (42, 1), (60, 1)] }, { coefficient := 1, powers := [(9, 1), (25, 1), (42, 1), (48, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (55, 1)] }, { coefficient := -1, powers := [(5, 1), (13, 1), (20, 1), (26, 1), (32, 1), (46, 1)] }, { coefficient := 1, powers := [(5, 1), (13, 1), (20, 1), (29, 1), (60, 1)] }, { coefficient := -1, powers := [(5, 1), (13, 1), (25, 1), (26, 1), (32, 1), (46, 1)] }, { coefficient := 1, powers := [(5, 1), (13, 1), (25, 1), (29, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (20, 1), (26, 1), (32, 1), (46, 1), (55, 1)] }, { coefficient := -1, powers := [(5, 1), (20, 1), (29, 1), (55, 1), (60, 1)] }, { coefficient := -1, powers := [(5, 1), (25, 1), (26, 1), (32, 1), (42, 1), (46, 1)] }, { coefficient := 1, powers := [(5, 1), (25, 1), (29, 1), (42, 1), (60, 1)] }, { coefficient := -1, powers := [(6, 1), (12, 1), (13, 1), (20, 1), (29, 1), (48, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (12, 1), (20, 1), (29, 1), (42, 1), (48, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (13, 1), (18, 1), (24, 1), (26, 1), (60, 1)] }, { coefficient := -1, powers := [(6, 1), (13, 1), (18, 1), (26, 1), (32, 1), (48, 1)] }, { coefficient := 1, powers := [(6, 1), (18, 1), (20, 1), (24, 1), (26, 1), (44, 1), (60, 1)] }, { coefficient := -1, powers := [(6, 1), (18, 1), (24, 1), (26, 1), (42, 1), (60, 1)] }, { coefficient := 1, powers := [(6, 1), (18, 1), (26, 1), (32, 1), (42, 1), (48, 1)] }, { coefficient := 1, powers := [(6, 1), (33, 1)] }, { coefficient := 1, powers := [(12, 1), (13, 1), (20, 1), (24, 1), (26, 1), (46, 1)] }, { coefficient := 1, powers := [(12, 1), (13, 1), (24, 1), (25, 1), (26, 1), (46, 1)] }, { coefficient := -1, powers := [(12, 1), (20, 1), (24, 1), (26, 1), (46, 1), (55, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (25, 1), (26, 1), (42, 1), (46, 1)] }, { coefficient := 2, powers := [(13, 1), (19, 1), (20, 1), (24, 1), (26, 1), (45, 1), (50, 1)] }, { coefficient := 1, powers := [(13, 1), (19, 1), (20, 1), (24, 1), (26, 1), (52, 1)] }, { coefficient := 2, powers := [(13, 1), (19, 1), (24, 1), (25, 1), (26, 1), (45, 1), (50, 1)] }, { coefficient := 1, powers := [(13, 1), (19, 1), (24, 1), (25, 1), (26, 1), (52, 1)] }, { coefficient := -1, powers := [(13, 1), (25, 1)] }, { coefficient := -2, powers := [(19, 1), (20, 1), (24, 1), (26, 1), (45, 1), (50, 1), (55, 1)] }, { coefficient := -1, powers := [(19, 1), (20, 1), (24, 1), (26, 1), (52, 1), (55, 1)] }, { coefficient := 2, powers := [(19, 1), (24, 1), (25, 1), (26, 1), (42, 1), (45, 1), (50, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (25, 1), (26, 1), (42, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (5, 1), (9, 1), (20, 1), (29, 1), (55, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (9, 1), (12, 1), (13, 1), (20, 1), (24, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (9, 1), (12, 1), (20, 1), (24, 1), (55, 1), (57, 1)] }, { coefficient := -1, powers := [(3, 1), (9, 1), (12, 1), (20, 1), (29, 1), (33, 1), (48, 1)] }, { coefficient := 1, powers := [(3, 1), (12, 1), (20, 1), (29, 1), (30, 1), (48, 1), (55, 1)] }, { coefficient := 1, powers := [(3, 1), (12, 1), (20, 1), (29, 1), (33, 1), (48, 1), (49, 1)] }, { coefficient := 1, powers := [(5, 1), (6, 1), (9, 1), (20, 1), (29, 1), (33, 1), (60, 1)] }, { coefficient := 1, powers := [(6, 1), (9, 1), (12, 1), (20, 1), (24, 1), (33, 1), (57, 1)] }, { coefficient := -1, powers := [(6, 1), (12, 1), (13, 1), (20, 1), (29, 1), (30, 1), (48, 1)] }, { coefficient := 1, powers := [(6, 1), (12, 1), (13, 1), (21, 1), (29, 1), (30, 1), (43, 1)] }, { coefficient := 1, powers := [(6, 1), (12, 1), (20, 1), (29, 1), (30, 1), (42, 1), (48, 1)] }, { coefficient := -1, powers := [(6, 1), (12, 1), (21, 1), (29, 1), (30, 1), (42, 1), (43, 1)] }, { coefficient := -1, powers := [(8, 1), (9, 1), (24, 1), (25, 1), (33, 1), (43, 1), (50, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (25, 1), (30, 1), (43, 1), (50, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (25, 1), (33, 1), (43, 1), (49, 1), (50, 1)] }, { coefficient := -1, powers := [(9, 1), (12, 1), (13, 1), (20, 1), (21, 1), (29, 1), (43, 1)] }, { coefficient := -1, powers := [(9, 1), (12, 1), (13, 1), (20, 1), (24, 1), (25, 1), (43, 1), (53, 1)] }, { coefficient := 1, powers := [(9, 1), (12, 1), (13, 1), (20, 1), (24, 1), (25, 1), (57, 1)] }, { coefficient := 1, powers := [(9, 1), (12, 1), (13, 1), (20, 1), (24, 1), (26, 1), (43, 1)] }, { coefficient := -1, powers := [(9, 1), (12, 1), (20, 2), (29, 1), (48, 1), (55, 1)] }, { coefficient := -1, powers := [(9, 1), (13, 1), (19, 1), (20, 1), (24, 1), (25, 1), (50, 1), (53, 1)] }, { coefficient := -2, powers := [(9, 1), (13, 1), (19, 1), (20, 1), (24, 1), (26, 1), (50, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (3, 1), (9, 1), (33, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (3, 1), (30, 1), (55, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (3, 1), (33, 1), (49, 1), (57, 1)] }, { coefficient := -1, powers := [(2, 1), (6, 1), (13, 1), (30, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (6, 1), (20, 1), (57, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (6, 1), (30, 1), (42, 1), (57, 1)] }, { coefficient := -1, powers := [(2, 1), (9, 1), (13, 1), (20, 1), (57, 1)] }, { coefficient := -1, powers := [(2, 1), (9, 1), (13, 1), (25, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (9, 1), (20, 1), (55, 1), (57, 1)] }, { coefficient := -1, powers := [(2, 1), (9, 1), (25, 1), (42, 1), (57, 1)] }, { coefficient := -1, powers := [(3, 1), (8, 1), (9, 1), (33, 1), (35, 1)] }, { coefficient := 1, powers := [(3, 1), (8, 1), (30, 1), (35, 1), (55, 1)] }, { coefficient := 1, powers := [(3, 1), (8, 1), (33, 1), (35, 1), (49, 1)] }, { coefficient := -1, powers := [(6, 1), (8, 1), (13, 1), (30, 1), (35, 1)] }, { coefficient := 1, powers := [(6, 1), (8, 1), (20, 1), (35, 1), (58, 1)] }, { coefficient := 1, powers := [(6, 1), (8, 1), (30, 1), (35, 1), (42, 1)] }, { coefficient := -1, powers := [(8, 1), (9, 1), (13, 1), (20, 1), (35, 1)] }, { coefficient := -1, powers := [(8, 1), (9, 1), (13, 1), (25, 1), (35, 1)] }, { coefficient := -1, powers := [(8, 1), (9, 1), (25, 1), (35, 1), (42, 1)] }, { coefficient := -1, powers := [(9, 1), (13, 1), (19, 1), (20, 1), (29, 1)] }]
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
    (values : Fin 61 → R) :
    ¬ ∀ index : Fin 50,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component60.SelectedLeafB0_0.selectedHasNoCommonZero

end Krenn.Component60.SelectedLeafB0_0
