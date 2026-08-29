import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component60.SelectedLeafB6_1_5

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "a97f126eebe0892c6bb2dc68c6307682c2a7d3c7ac95a1a882c68163bd100a64"
def certificateSHA256 : String := "6f33a047e9fa7351dd3619efc4eeba5c91ac76752a7995b24948447fcf3300ef"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 41 → Fin 665 := ![
  13,
  22,
  25,
  149,
  150,
  172,
  173,
  211,
  212,
  236,
  292,
  294,
  298,
  301,
  302,
  303,
  308,
  310,
  312,
  359,
  383,
  404,
  425,
  443,
  454,
  556,
  579,
  582,
  583,
  587,
  600,
  601,
  653,
  655,
  656,
  657,
  658,
  659,
  660,
  663,
  664
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 41 → SparsePoly (Fin 66) := ![
  [{ coefficient := 1, powers := [(15, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (30, 1)] }, { coefficient := 1, powers := [(18, 1), (26, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (26, 1)] }, { coefficient := 1, powers := [(26, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (20, 1)] }, { coefficient := 1, powers := [(18, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (43, 1)] }, { coefficient := 1, powers := [(19, 1), (20, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (26, 1), (46, 1)] }, { coefficient := 1, powers := [(9, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (26, 1), (47, 1)] }, { coefficient := 1, powers := [(30, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (25, 1), (45, 1)] }, { coefficient := 1, powers := [(18, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1)] }, { coefficient := 1, powers := [(20, 1), (43, 1)] }, { coefficient := 1, powers := [(25, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (50, 1)] }, { coefficient := 1, powers := [(20, 1), (50, 1)] }, { coefficient := 1, powers := [(25, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (49, 1)] }, { coefficient := 1, powers := [(15, 1), (22, 1), (49, 1)] }, { coefficient := 1, powers := [(15, 1), (27, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (48, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1)] }, { coefficient := 1, powers := [(12, 1), (29, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (58, 1)] }, { coefficient := 1, powers := [(9, 1), (42, 1)] }, { coefficient := 1, powers := [(13, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (45, 1)] }, { coefficient := 1, powers := [(12, 1), (56, 1)] }, { coefficient := 1, powers := [(18, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (46, 1)] }, { coefficient := 1, powers := [(19, 1), (40, 1)] }, { coefficient := 1, powers := [(19, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1), (51, 1)] }, { coefficient := 1, powers := [(20, 1), (43, 1), (51, 1)] }, { coefficient := 1, powers := [(43, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (30, 1), (57, 1)] }, { coefficient := 1, powers := [(8, 1), (30, 1), (48, 1)] }, { coefficient := 1, powers := [(19, 1), (30, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (20, 1), (56, 1)] }, { coefficient := 1, powers := [(12, 1)] }, { coefficient := 1, powers := [(18, 1), (20, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (25, 1), (46, 1)] }, { coefficient := 1, powers := [(19, 1), (25, 1), (40, 1)] }, { coefficient := 1, powers := [(19, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (53, 1)] }, { coefficient := 1, powers := [(3, 1), (26, 1), (59, 1)] }, { coefficient := 1, powers := [(20, 1), (53, 1)] }, { coefficient := 1, powers := [(26, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (54, 1)] }, { coefficient := 1, powers := [(29, 1), (41, 1)] }, { coefficient := 1, powers := [(29, 1), (47, 1), (50, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1), (53, 1)] }, { coefficient := 1, powers := [(20, 1), (43, 1), (53, 1)] }, { coefficient := 1, powers := [(20, 1), (57, 1)] }, { coefficient := 1, powers := [(26, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (43, 1), (53, 1)] }, { coefficient := 1, powers := [(24, 1), (57, 1)] }, { coefficient := 1, powers := [(29, 1), (48, 1)] }, { coefficient := 1, powers := [(35, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (51, 1)] }, { coefficient := 1, powers := [(3, 1), (59, 1)] }, { coefficient := 1, powers := [(20, 1), (51, 1)] }, { coefficient := 1, powers := [(20, 1), (56, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(3, 1), (30, 1), (56, 1)] }, { coefficient := 1, powers := [(9, 1), (20, 1), (56, 1)] }, { coefficient := 1, powers := [(9, 1)] }, { coefficient := 1, powers := [(39, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (39, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (30, 1), (57, 1)] }, { coefficient := 1, powers := [(9, 1), (20, 1), (57, 1)] }, { coefficient := 1, powers := [(9, 1), (26, 1), (43, 1)] }, { coefficient := 1, powers := [(26, 1), (39, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (36, 1), (58, 1)] }, { coefficient := 1, powers := [(1, 1), (39, 1), (55, 1)] }, { coefficient := 1, powers := [(1, 1), (42, 1), (49, 1)] }, { coefficient := 1, powers := [(14, 1), (22, 1), (49, 1)] }, { coefficient := 1, powers := [(14, 1), (27, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1)] }, { coefficient := 1, powers := [(3, 1), (33, 1)] }, { coefficient := 1, powers := [(13, 1), (20, 1)] }, { coefficient := 1, powers := [(20, 1), (55, 1)] }, { coefficient := 1, powers := [(25, 1), (42, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (49, 1)] }, { coefficient := 1, powers := [(6, 1), (30, 1)] }, { coefficient := 1, powers := [(9, 1), (25, 1)] }, { coefficient := 1, powers := [(20, 1), (49, 1)] }, { coefficient := 1, powers := [(25, 1), (39, 1)] }, { coefficient := 1, powers := [(30, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (36, 1), (58, 1)] }, { coefficient := 1, powers := [(0, 1), (39, 1), (55, 1)] }, { coefficient := 1, powers := [(0, 1), (42, 1), (49, 1)] }, { coefficient := 1, powers := [(3, 1), (25, 1), (58, 1)] }, { coefficient := 1, powers := [(3, 1), (30, 1), (55, 1)] }, { coefficient := 1, powers := [(3, 1), (33, 1), (49, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1), (58, 1)] }, { coefficient := 1, powers := [(6, 1), (30, 1), (42, 1)] }, { coefficient := 1, powers := [(6, 1), (33, 1), (39, 1)] }, { coefficient := 1, powers := [(9, 1), (20, 1), (55, 1)] }, { coefficient := 1, powers := [(9, 1), (25, 1), (42, 1)] }, { coefficient := 1, powers := [(9, 1), (33, 1), (36, 1)] }, { coefficient := 1, powers := [(13, 1), (20, 1), (49, 1)] }, { coefficient := 1, powers := [(13, 1), (25, 1), (39, 1)] }, { coefficient := 1, powers := [(13, 1), (30, 1), (36, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (41, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (48, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (48, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1), (29, 1), (48, 1)] }, { coefficient := 1, powers := [(12, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (54, 1)] }, { coefficient := 1, powers := [(19, 1), (29, 1), (41, 1)] }, { coefficient := 1, powers := [(19, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (61, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(39, 1)] }],
  [{ coefficient := 1, powers := [(40, 1)] }],
  [{ coefficient := 1, powers := [(56, 1)] }],
  [{ coefficient := 1, powers := [(57, 1), (65, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 41 → SparsePoly (Fin 66) := ![
  [{ coefficient := 1, powers := [(0, 1), (14, 1), (22, 2), (62, 2)] }, { coefficient := 2, powers := [(0, 1), (22, 1), (42, 1), (62, 1)] }, { coefficient := 1, powers := [(20, 1), (22, 1), (42, 1), (62, 1)] }, { coefficient := 1, powers := [(20, 1), (22, 1), (55, 1), (62, 1)] }, { coefficient := 1, powers := [(22, 1), (25, 1), (42, 1), (62, 1)] }, { coefficient := 1, powers := [(22, 1), (33, 1), (36, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (13, 1), (30, 1), (36, 1), (53, 1)] }, { coefficient := 1, powers := [(12, 1), (30, 1), (36, 1), (42, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(13, 1), (19, 1), (30, 1), (36, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (30, 1), (36, 1), (42, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (24, 1), (36, 1), (60, 1)] }, { coefficient := -1, powers := [(13, 1), (29, 1), (36, 1), (48, 1), (60, 1), (65, 1)] }, { coefficient := -1, powers := [(13, 1), (32, 1), (36, 1), (48, 1)] }, { coefficient := 1, powers := [(13, 1), (35, 1), (36, 1), (41, 1)] }, { coefficient := -1, powers := [(24, 1), (36, 1), (42, 1), (60, 1)] }, { coefficient := 1, powers := [(29, 1), (36, 1), (42, 1), (48, 1), (60, 1), (65, 1)] }, { coefficient := 1, powers := [(32, 1), (36, 1), (42, 1), (48, 1)] }, { coefficient := -1, powers := [(35, 1), (36, 1), (41, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (19, 1), (29, 1), (36, 1), (47, 1), (60, 1), (65, 1)] }, { coefficient := 1, powers := [(13, 1), (19, 1), (32, 1), (36, 1), (47, 1)] }, { coefficient := -1, powers := [(19, 1), (29, 1), (36, 1), (42, 1), (47, 1), (60, 1), (65, 1)] }, { coefficient := -1, powers := [(19, 1), (32, 1), (36, 1), (42, 1), (47, 1)] }, { coefficient := 1, powers := [(20, 1), (46, 1), (55, 1), (65, 1)] }, { coefficient := -1, powers := [(43, 1), (55, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (24, 1), (30, 1), (36, 1), (43, 1), (54, 1), (61, 1)] }, { coefficient := 1, powers := [(13, 1), (24, 1), (30, 1), (36, 1), (46, 1), (54, 1)] }, { coefficient := 1, powers := [(13, 1), (29, 1), (30, 1), (36, 1), (48, 1), (50, 1), (61, 1)] }, { coefficient := 1, powers := [(13, 1), (29, 1), (30, 1), (36, 1), (48, 1), (52, 1)] }, { coefficient := -1, powers := [(24, 1), (30, 1), (36, 1), (42, 1), (43, 1), (54, 1), (61, 1)] }, { coefficient := -1, powers := [(24, 1), (30, 1), (36, 1), (42, 1), (46, 1), (54, 1)] }, { coefficient := -1, powers := [(29, 1), (30, 1), (36, 1), (42, 1), (48, 1), (50, 1), (61, 1)] }, { coefficient := -1, powers := [(29, 1), (30, 1), (36, 1), (42, 1), (48, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (24, 1), (30, 1), (36, 1), (54, 1)] }, { coefficient := -1, powers := [(24, 1), (30, 1), (36, 1), (42, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(20, 1), (55, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(13, 1), (19, 1), (29, 1), (36, 1), (60, 1), (65, 1)] }, { coefficient := -1, powers := [(13, 1), (19, 1), (32, 1), (36, 1)] }, { coefficient := 1, powers := [(19, 1), (29, 1), (36, 1), (42, 1), (60, 1), (65, 1)] }, { coefficient := 1, powers := [(19, 1), (32, 1), (36, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (29, 1), (30, 1), (36, 1), (48, 1)] }, { coefficient := -1, powers := [(29, 1), (30, 1), (36, 1), (42, 1), (48, 1)] }],
  [{ coefficient := -1, powers := [(13, 1), (18, 1), (24, 1), (30, 1), (36, 1), (54, 1), (61, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (30, 1), (36, 1), (42, 1), (54, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(13, 1), (18, 1), (29, 1), (30, 1), (36, 1), (48, 1), (61, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (30, 1), (36, 1), (42, 1), (48, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (14, 1), (22, 1), (62, 2)] }, { coefficient := -2, powers := [(0, 1), (42, 1), (62, 1)] }, { coefficient := -1, powers := [(20, 1), (42, 1), (62, 1)] }, { coefficient := -1, powers := [(20, 1), (55, 1), (62, 1)] }, { coefficient := -1, powers := [(25, 1), (42, 1), (62, 1)] }, { coefficient := -1, powers := [(33, 1), (36, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (30, 1), (36, 1), (54, 1)] }, { coefficient := -1, powers := [(30, 1), (36, 1), (42, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (30, 1), (36, 1), (48, 1)] }, { coefficient := -1, powers := [(30, 1), (36, 1), (42, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(25, 1)] }],
  [{ coefficient := -1, powers := [(13, 1), (25, 1), (29, 1), (30, 1), (36, 1), (48, 1)] }, { coefficient := 1, powers := [(25, 1), (29, 1), (30, 1), (36, 1), (42, 1), (48, 1)] }],
  [{ coefficient := -1, powers := [(13, 1), (20, 1), (24, 1), (30, 1), (36, 1), (54, 1)] }, { coefficient := 1, powers := [(20, 1), (24, 1), (30, 1), (36, 1), (42, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (26, 1), (58, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (29, 1), (36, 1), (60, 1), (65, 1)] }, { coefficient := 1, powers := [(13, 1), (32, 1), (36, 1)] }, { coefficient := -1, powers := [(29, 1), (36, 1), (42, 1), (60, 1), (65, 1)] }, { coefficient := -1, powers := [(32, 1), (36, 1), (42, 1)] }],
  [{ coefficient := -1, powers := [(13, 1), (29, 1), (30, 1), (36, 1), (48, 1)] }, { coefficient := 1, powers := [(29, 1), (30, 1), (36, 1), (42, 1), (48, 1)] }],
  [{ coefficient := -1, powers := [(13, 1), (24, 1), (30, 1), (36, 1), (54, 1)] }, { coefficient := 1, powers := [(24, 1), (30, 1), (36, 1), (42, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (43, 1), (58, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (19, 1), (30, 1), (36, 1)] }, { coefficient := -1, powers := [(19, 1), (30, 1), (36, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (58, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (13, 1), (30, 1), (36, 1)] }, { coefficient := -1, powers := [(12, 1), (30, 1), (36, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (26, 1), (43, 1), (58, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (55, 1)] }, { coefficient := -1, powers := [(25, 1), (42, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(55, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(49, 1)] }],
  [{ coefficient := 1, powers := [(42, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(13, 1), (30, 1), (36, 1)] }, { coefficient := 1, powers := [(30, 1), (36, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (18, 1), (24, 1), (30, 1), (36, 1), (43, 1), (54, 1)] }, { coefficient := 1, powers := [(13, 1), (18, 1), (29, 1), (30, 1), (36, 1), (48, 1), (50, 1)] }, { coefficient := -1, powers := [(18, 1), (24, 1), (30, 1), (36, 1), (42, 1), (43, 1), (54, 1)] }, { coefficient := -1, powers := [(18, 1), (29, 1), (30, 1), (36, 1), (42, 1), (48, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (14, 1), (22, 1), (49, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 1), (36, 1), (58, 1)] }, { coefficient := 1, powers := [(0, 1), (42, 1), (49, 1)] }, { coefficient := 1, powers := [(20, 1), (42, 1), (49, 1)] }, { coefficient := 1, powers := [(20, 1), (49, 1), (55, 1)] }, { coefficient := 1, powers := [(25, 1), (42, 1), (49, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (30, 1), (36, 1), (38, 1), (60, 1)] }, { coefficient := 1, powers := [(13, 1), (30, 1), (36, 1), (41, 1), (57, 1)] }, { coefficient := -1, powers := [(13, 1), (30, 1), (36, 1), (48, 1), (54, 1)] }, { coefficient := -1, powers := [(30, 1), (36, 1), (38, 1), (42, 1), (60, 1)] }, { coefficient := -1, powers := [(30, 1), (36, 1), (41, 1), (42, 1), (57, 1)] }, { coefficient := 1, powers := [(30, 1), (36, 1), (42, 1), (48, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (1, 1), (55, 1), (62, 1)] }, { coefficient := 1, powers := [(0, 1), (14, 1), (15, 1), (22, 1), (27, 1), (62, 2)] }, { coefficient := -1, powers := [(0, 1), (14, 1), (27, 1), (62, 1)] }, { coefficient := 2, powers := [(0, 1), (15, 1), (27, 1), (42, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 1), (20, 1), (55, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (25, 1), (42, 1), (56, 1)] }, { coefficient := -1, powers := [(0, 1), (33, 1), (36, 1), (56, 1)] }, { coefficient := -1, powers := [(0, 1), (55, 1), (57, 1), (65, 1)] }, { coefficient := 1, powers := [(0, 1), (55, 1)] }, { coefficient := 1, powers := [(6, 1), (33, 1)] }, { coefficient := -1, powers := [(13, 1), (18, 1), (24, 1), (26, 1), (36, 1), (60, 1)] }, { coefficient := 1, powers := [(13, 1), (18, 1), (26, 1), (29, 1), (36, 1), (48, 1), (60, 1), (65, 1)] }, { coefficient := 1, powers := [(13, 1), (18, 1), (26, 1), (32, 1), (36, 1), (48, 1)] }, { coefficient := -1, powers := [(13, 1), (18, 1), (26, 1), (35, 1), (36, 1), (41, 1)] }, { coefficient := -1, powers := [(13, 1), (19, 1), (26, 1), (29, 1), (36, 1), (47, 1), (60, 1), (65, 1)] }, { coefficient := -1, powers := [(13, 1), (19, 1), (26, 1), (32, 1), (36, 1), (47, 1)] }, { coefficient := 1, powers := [(15, 1), (20, 1), (27, 1), (42, 1), (62, 1)] }, { coefficient := 1, powers := [(15, 1), (20, 1), (27, 1), (55, 1), (62, 1)] }, { coefficient := 1, powers := [(15, 1), (25, 1), (27, 1), (42, 1), (62, 1)] }, { coefficient := 1, powers := [(15, 1), (27, 1), (33, 1), (36, 1), (62, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (26, 1), (36, 1), (42, 1), (60, 1)] }, { coefficient := -1, powers := [(18, 1), (26, 1), (29, 1), (36, 1), (42, 1), (48, 1), (60, 1), (65, 1)] }, { coefficient := -1, powers := [(18, 1), (26, 1), (32, 1), (36, 1), (42, 1), (48, 1)] }, { coefficient := 1, powers := [(18, 1), (26, 1), (35, 1), (36, 1), (41, 1), (42, 1)] }, { coefficient := 1, powers := [(19, 1), (26, 1), (29, 1), (36, 1), (42, 1), (47, 1), (60, 1), (65, 1)] }, { coefficient := 1, powers := [(19, 1), (26, 1), (32, 1), (36, 1), (42, 1), (47, 1)] }, { coefficient := -1, powers := [(20, 1), (26, 1), (46, 1), (55, 1), (65, 1)] }, { coefficient := -1, powers := [(20, 1), (55, 1)] }, { coefficient := -1, powers := [(33, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (19, 1), (20, 1), (24, 1), (30, 1), (36, 1), (54, 1)] }, { coefficient := 1, powers := [(13, 1), (19, 1), (24, 1), (25, 1), (30, 1), (36, 1), (54, 1)] }, { coefficient := -1, powers := [(19, 1), (20, 1), (24, 1), (30, 1), (36, 1), (42, 1), (54, 1)] }, { coefficient := -1, powers := [(19, 1), (24, 1), (25, 1), (30, 1), (36, 1), (42, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (20, 1), (30, 1), (55, 1)] }, { coefficient := 1, powers := [(3, 1), (25, 1), (30, 1), (42, 1)] }, { coefficient := -1, powers := [(3, 1), (30, 1), (33, 1), (36, 1)] }, { coefficient := -1, powers := [(6, 1), (20, 1), (26, 1), (43, 1), (58, 1), (65, 1)] }, { coefficient := -1, powers := [(9, 1), (20, 2), (55, 1)] }, { coefficient := 1, powers := [(9, 1), (20, 1), (25, 1), (42, 1)] }, { coefficient := -1, powers := [(9, 1), (20, 1), (33, 1), (36, 1)] }, { coefficient := 1, powers := [(12, 1), (13, 1), (20, 1), (29, 1), (30, 1), (36, 1), (48, 1)] }, { coefficient := 1, powers := [(12, 1), (13, 1), (25, 1), (29, 1), (30, 1), (36, 1), (48, 1)] }, { coefficient := -1, powers := [(12, 1), (20, 1), (29, 1), (30, 1), (36, 1), (42, 1), (48, 1)] }, { coefficient := -1, powers := [(12, 1), (25, 1), (29, 1), (30, 1), (36, 1), (42, 1), (48, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (30, 1), (55, 1)] }, { coefficient := -1, powers := [(5, 1), (13, 1), (29, 1), (30, 1), (36, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (30, 1), (36, 1), (42, 1), (60, 1)] }, { coefficient := -1, powers := [(6, 1), (20, 1), (58, 1)] }]
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
    (values : Fin 66 → R) :
    ¬ ∀ index : Fin 41,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component60.SelectedLeafB6_1_5.selectedHasNoCommonZero

end Krenn.Component60.SelectedLeafB6_1_5
