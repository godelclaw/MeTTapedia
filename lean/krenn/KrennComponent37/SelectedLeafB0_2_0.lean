import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component37.SelectedLeafB0_2_0

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "6f05bf1f944e030d201d28a860dd12701dc3960f161f39f156f5b455cf7398de"
def certificateSHA256 : String := "9874c59a732b0d57ab7f043639251a8f138311f87507334ea3ff09f9e39eba70"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 64 → Fin 667 := ![
  20,
  168,
  170,
  171,
  175,
  176,
  177,
  179,
  180,
  181,
  256,
  285,
  294,
  295,
  297,
  301,
  307,
  310,
  311,
  312,
  316,
  317,
  393,
  411,
  412,
  426,
  427,
  431,
  433,
  438,
  446,
  450,
  454,
  455,
  466,
  471,
  472,
  475,
  476,
  479,
  500,
  526,
  562,
  566,
  570,
  580,
  581,
  583,
  602,
  603,
  608,
  609,
  612,
  642,
  645,
  655,
  657,
  658,
  660,
  661,
  663,
  664,
  665,
  666
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 64 → SparsePoly (Fin 63) := ![
  [{ coefficient := 1, powers := [(19, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (26, 1)] }, { coefficient := 1, powers := [(18, 1), (20, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (44, 1)] }, { coefficient := 1, powers := [(19, 1), (20, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (20, 1)] }, { coefficient := 1, powers := [(18, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (44, 1)] }, { coefficient := 1, powers := [(19, 1), (20, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (49, 1)] }, { coefficient := 1, powers := [(19, 1), (21, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (55, 1)] }, { coefficient := 1, powers := [(30, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (44, 1)] }, { coefficient := 1, powers := [(28, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (54, 1)] }, { coefficient := 1, powers := [(30, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (25, 1), (46, 1)] }, { coefficient := 1, powers := [(18, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(29, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1)] }, { coefficient := 1, powers := [(20, 1), (44, 1)] }, { coefficient := 1, powers := [(25, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (49, 1)] }, { coefficient := 1, powers := [(21, 1), (44, 1)] }, { coefficient := 1, powers := [(25, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (55, 1)] }, { coefficient := 1, powers := [(20, 1), (55, 1)] }, { coefficient := 1, powers := [(26, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (59, 1)] }, { coefficient := 1, powers := [(9, 1), (43, 1)] }, { coefficient := 1, powers := [(13, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (46, 1)] }, { coefficient := 1, powers := [(12, 1), (57, 1)] }, { coefficient := 1, powers := [(18, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (41, 1)] }, { coefficient := 1, powers := [(19, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (52, 1)] }, { coefficient := 1, powers := [(24, 1), (57, 1)] }, { coefficient := 1, powers := [(29, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (54, 1)] }, { coefficient := 1, powers := [(30, 1), (41, 1)] }, { coefficient := 1, powers := [(30, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1), (55, 1)] }, { coefficient := 1, powers := [(26, 1), (46, 1), (51, 1)] }, { coefficient := 1, powers := [(55, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (49, 1), (52, 1)] }, { coefficient := 1, powers := [(21, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(49, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (20, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1)] }, { coefficient := 1, powers := [(18, 1), (20, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (25, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (25, 1), (41, 1)] }, { coefficient := 1, powers := [(19, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (20, 1), (50, 1)] }, { coefficient := 1, powers := [(19, 1), (25, 1), (40, 1)] }, { coefficient := 1, powers := [(19, 1), (31, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (53, 1)] }, { coefficient := 1, powers := [(20, 1), (51, 1), (57, 1)] }, { coefficient := 1, powers := [(20, 1), (53, 1)] }, { coefficient := 1, powers := [(51, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (54, 1)] }, { coefficient := 1, powers := [(3, 1), (26, 1), (60, 1)] }, { coefficient := 1, powers := [(20, 1), (54, 1)] }, { coefficient := 1, powers := [(26, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (47, 1)] }, { coefficient := 1, powers := [(18, 1), (28, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (28, 1), (41, 1)] }, { coefficient := 1, powers := [(19, 1), (29, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (49, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1)] }, { coefficient := 1, powers := [(18, 1), (28, 1), (49, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1)] }, { coefficient := 1, powers := [(12, 1), (30, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (61, 1)] }, { coefficient := 1, powers := [(12, 1), (49, 1)] }, { coefficient := 1, powers := [(19, 1), (21, 1), (53, 1)] }, { coefficient := 1, powers := [(19, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (61, 1)] }, { coefficient := 1, powers := [(12, 1), (26, 1), (47, 1)] }, { coefficient := 1, powers := [(12, 1), (58, 1)] }, { coefficient := 1, powers := [(19, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (55, 1)] }, { coefficient := 1, powers := [(30, 1), (42, 1)] }, { coefficient := 1, powers := [(30, 1), (48, 1), (51, 1)] }, { coefficient := 1, powers := [(33, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (41, 1)] }, { coefficient := 1, powers := [(29, 1), (46, 1)] }, { coefficient := 1, powers := [(29, 1), (52, 1)] }, { coefficient := 1, powers := [(29, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1), (54, 1)] }, { coefficient := 1, powers := [(20, 1), (44, 1), (54, 1)] }, { coefficient := 1, powers := [(20, 1), (58, 1)] }, { coefficient := 1, powers := [(26, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1), (53, 1)] }, { coefficient := 1, powers := [(46, 1), (51, 1)] }, { coefficient := 1, powers := [(51, 1), (57, 1)] }, { coefficient := 1, powers := [(53, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1), (54, 1)] }, { coefficient := 1, powers := [(26, 1), (41, 1)] }, { coefficient := 1, powers := [(26, 1), (46, 1)] }, { coefficient := 1, powers := [(54, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1), (52, 1)] }, { coefficient := 1, powers := [(41, 1), (44, 1)] }, { coefficient := 1, powers := [(44, 1), (52, 1)] }, { coefficient := 1, powers := [(47, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1), (55, 1)] }, { coefficient := 1, powers := [(26, 1), (47, 1), (51, 1)] }, { coefficient := 1, powers := [(44, 1), (55, 1)] }, { coefficient := 1, powers := [(51, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (48, 1), (52, 1)] }, { coefficient := 1, powers := [(21, 1), (52, 1)] }, { coefficient := 1, powers := [(21, 1), (57, 1)] }, { coefficient := 1, powers := [(48, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (29, 1), (60, 1)] }, { coefficient := 1, powers := [(23, 1), (52, 1)] }, { coefficient := 1, powers := [(23, 1), (57, 1)] }, { coefficient := 1, powers := [(29, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (29, 1), (60, 1)] }, { coefficient := 1, powers := [(28, 1), (41, 1)] }, { coefficient := 1, powers := [(28, 1), (46, 1)] }, { coefficient := 1, powers := [(29, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (26, 1), (47, 1)] }, { coefficient := 1, powers := [(18, 1), (58, 1)] }, { coefficient := 1, powers := [(19, 1), (26, 1), (41, 1)] }, { coefficient := 1, powers := [(19, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (44, 1), (54, 1)] }, { coefficient := 1, powers := [(24, 1), (58, 1)] }, { coefficient := 1, powers := [(30, 1), (49, 1)] }, { coefficient := 1, powers := [(36, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (44, 1), (54, 1)] }, { coefficient := 1, powers := [(29, 1), (58, 1)] }, { coefficient := 1, powers := [(30, 1), (41, 1), (44, 1)] }, { coefficient := 1, powers := [(30, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1)] }, { coefficient := 1, powers := [(6, 1), (60, 1)] }, { coefficient := 1, powers := [(25, 1), (41, 1)] }, { coefficient := 1, powers := [(25, 1), (46, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (52, 1)] }, { coefficient := 1, powers := [(3, 1), (60, 1)] }, { coefficient := 1, powers := [(20, 1), (52, 1)] }, { coefficient := 1, powers := [(20, 1), (57, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (31, 1), (57, 1)] }, { coefficient := 1, powers := [(9, 1), (20, 1), (57, 1)] }, { coefficient := 1, powers := [(9, 1)] }, { coefficient := 1, powers := [(40, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1)] }, { coefficient := 1, powers := [(3, 1), (34, 1)] }, { coefficient := 1, powers := [(13, 1), (20, 1)] }, { coefficient := 1, powers := [(20, 1), (56, 1)] }, { coefficient := 1, powers := [(25, 1), (43, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (50, 1)] }, { coefficient := 1, powers := [(6, 1), (31, 1)] }, { coefficient := 1, powers := [(9, 1), (25, 1)] }, { coefficient := 1, powers := [(20, 1), (50, 1)] }, { coefficient := 1, powers := [(25, 1), (40, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (41, 1), (58, 1)] }, { coefficient := 1, powers := [(0, 1), (47, 1), (54, 1)] }, { coefficient := 1, powers := [(26, 1), (41, 1), (44, 1)] }, { coefficient := 1, powers := [(26, 1), (47, 1)] }, { coefficient := 1, powers := [(44, 1), (54, 1)] }, { coefficient := 1, powers := [(58, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (48, 1), (53, 1)] }, { coefficient := 1, powers := [(21, 1), (51, 1), (57, 1)] }, { coefficient := 1, powers := [(21, 1), (53, 1)] }, { coefficient := 1, powers := [(42, 1)] }, { coefficient := 1, powers := [(48, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1), (50, 1)] }, { coefficient := 1, powers := [(6, 1), (31, 1), (45, 1)] }, { coefficient := 1, powers := [(6, 1), (59, 1)] }, { coefficient := 1, powers := [(9, 1), (25, 1), (45, 1)] }, { coefficient := 1, powers := [(9, 1), (56, 1)] }, { coefficient := 1, powers := [(13, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (44, 1), (55, 1)] }, { coefficient := 1, powers := [(24, 1), (51, 1), (58, 1)] }, { coefficient := 1, powers := [(30, 1), (42, 1), (44, 1)] }, { coefficient := 1, powers := [(30, 1), (49, 1), (51, 1)] }, { coefficient := 1, powers := [(33, 1), (39, 1), (44, 1)] }, { coefficient := 1, powers := [(36, 1), (39, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (38, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (41, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(41, 1)] }, { coefficient := 1, powers := [(46, 1)] }, { coefficient := 1, powers := [(52, 1)] }, { coefficient := 1, powers := [(57, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (37, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (40, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (43, 1), (50, 1)] }, { coefficient := 1, powers := [(3, 1), (25, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (31, 1), (56, 1)] }, { coefficient := 1, powers := [(3, 1), (34, 1), (50, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (31, 1), (43, 1)] }, { coefficient := 1, powers := [(6, 1), (34, 1), (40, 1)] }, { coefficient := 1, powers := [(9, 1), (20, 1), (56, 1)] }, { coefficient := 1, powers := [(9, 1), (25, 1), (43, 1)] }, { coefficient := 1, powers := [(9, 1), (34, 1), (37, 1)] }, { coefficient := 1, powers := [(13, 1), (20, 1), (50, 1)] }, { coefficient := 1, powers := [(13, 1), (25, 1), (40, 1)] }, { coefficient := 1, powers := [(13, 1), (31, 1), (37, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (39, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (42, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (49, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (49, 1)] }, { coefficient := 1, powers := [(8, 1), (36, 1), (42, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (58, 1)] }, { coefficient := 1, powers := [(12, 1), (30, 1), (49, 1)] }, { coefficient := 1, powers := [(12, 1), (36, 1), (39, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (55, 1)] }, { coefficient := 1, powers := [(19, 1), (30, 1), (42, 1)] }, { coefficient := 1, powers := [(19, 1), (33, 1), (39, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1)] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(40, 1)] }],
  [{ coefficient := 1, powers := [(42, 1)] }],
  [{ coefficient := 1, powers := [(56, 1)] }],
  [{ coefficient := 1, powers := [(57, 1)] }],
  [{ coefficient := 1, powers := [(58, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 64 → SparsePoly (Fin 63) := ![
  [{ coefficient := -2, powers := [(13, 1), (20, 1), (24, 1), (55, 1)] }, { coefficient := -1, powers := [(24, 1), (25, 1), (43, 1), (55, 1)] }, { coefficient := -1, powers := [(24, 1), (34, 1), (37, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (47, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (24, 1), (30, 1), (49, 1), (54, 1)] }, { coefficient := -1, powers := [(12, 1), (24, 1), (36, 1), (39, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (24, 2), (26, 1), (44, 1), (54, 1)] }, { coefficient := -2, powers := [(24, 1), (26, 1)] }],
  [{ coefficient := -2, powers := [(12, 1), (24, 1), (30, 1), (44, 1), (49, 1), (53, 1), (54, 1)] }, { coefficient := 2, powers := [(30, 1), (49, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(24, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (24, 1), (28, 1), (44, 1), (54, 1), (55, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (30, 1), (44, 1), (51, 1), (54, 1)] }, { coefficient := -1, powers := [(28, 1), (55, 1)] }, { coefficient := -1, powers := [(30, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (18, 1), (24, 1), (44, 1), (49, 1), (54, 1)] }, { coefficient := -1, powers := [(18, 1), (49, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (20, 1), (52, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (20, 1), (41, 1), (44, 1)] }, { coefficient := -1, powers := [(12, 1), (20, 1), (47, 1)] }, { coefficient := -1, powers := [(12, 1), (44, 1)] }, { coefficient := -1, powers := [(19, 1), (51, 1)] }],
  [{ coefficient := -2, powers := [(12, 1), (24, 1), (30, 1), (44, 1), (49, 1), (54, 1)] }, { coefficient := 2, powers := [(30, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (20, 1), (54, 1)] }, { coefficient := 1, powers := [(12, 1), (25, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (24, 1), (52, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (23, 1), (52, 1), (54, 1)] }, { coefficient := -1, powers := [(12, 1), (30, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(18, 1), (24, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (24, 1), (25, 1), (55, 1)] }],
  [{ coefficient := 2, powers := [(12, 1), (24, 1), (25, 1), (30, 1), (44, 1), (49, 1), (54, 1)] }, { coefficient := -2, powers := [(25, 1), (30, 1), (49, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (24, 2), (25, 1), (44, 1), (54, 1), (55, 1)] }, { coefficient := 1, powers := [(24, 1), (25, 1), (55, 1)] }, { coefficient := -1, powers := [(24, 1), (26, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (19, 1), (24, 1), (25, 1), (44, 1), (54, 1), (55, 1)] }, { coefficient := -1, powers := [(12, 1), (20, 1), (44, 1), (54, 1)] }, { coefficient := -1, powers := [(19, 1), (25, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (25, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (19, 1), (24, 2), (44, 1), (54, 1)] }, { coefficient := -2, powers := [(19, 1), (24, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (23, 1), (54, 1)] }],
  [{ coefficient := 2, powers := [(12, 1), (24, 1), (30, 1), (44, 1), (49, 1), (54, 1)] }, { coefficient := -2, powers := [(30, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (24, 2), (44, 1), (54, 1), (55, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (28, 1), (44, 1), (48, 1), (54, 1), (55, 1)] }, { coefficient := -1, powers := [(24, 1), (55, 1)] }, { coefficient := -1, powers := [(28, 1), (48, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (24, 1), (55, 1)] }, { coefficient := 1, powers := [(20, 1), (24, 1), (45, 1), (55, 1)] }, { coefficient := -1, powers := [(24, 1), (43, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (19, 1), (24, 1), (30, 1), (49, 1), (54, 1)] }, { coefficient := 1, powers := [(12, 1), (19, 1), (24, 1), (36, 1), (39, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (29, 1), (49, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (24, 1), (25, 1), (44, 1), (48, 1), (54, 1), (55, 1)] }, { coefficient := 1, powers := [(25, 1), (48, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (24, 1), (44, 1), (54, 1), (55, 1)] }, { coefficient := 1, powers := [(55, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (24, 1), (44, 1), (49, 1), (54, 1)] }, { coefficient := 1, powers := [(49, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (24, 1), (30, 1), (44, 1), (54, 1)] }, { coefficient := 1, powers := [(30, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (24, 2), (44, 1), (54, 1)] }, { coefficient := 1, powers := [(24, 1)] }],
  [{ coefficient := 1, powers := [(19, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (20, 1), (25, 1), (49, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (24, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (19, 1), (24, 2), (26, 1), (44, 1), (54, 1)] }, { coefficient := 2, powers := [(19, 1), (24, 1), (26, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (23, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (20, 1), (24, 1), (54, 1)] }, { coefficient := -1, powers := [(12, 1), (24, 1), (26, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (24, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (19, 1), (24, 1), (28, 1), (44, 1), (54, 1), (55, 1)] }, { coefficient := -1, powers := [(12, 1), (19, 1), (24, 1), (30, 1), (44, 1), (51, 1), (54, 1)] }, { coefficient := 1, powers := [(12, 1), (30, 1), (44, 1)] }, { coefficient := 1, powers := [(19, 1), (28, 1), (55, 1)] }, { coefficient := 1, powers := [(19, 1), (30, 1), (51, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (25, 1), (49, 1), (54, 1)] }, { coefficient := 1, powers := [(12, 1), (26, 1), (49, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (20, 1), (49, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(12, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (20, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (20, 1), (29, 1), (49, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (25, 1), (29, 1), (49, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(19, 1), (24, 1), (25, 1), (43, 1), (55, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (34, 1), (37, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (24, 1), (50, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(19, 1), (20, 1), (24, 1), (45, 1), (55, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (43, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (19, 1), (24, 1), (30, 1), (44, 1), (54, 1)] }, { coefficient := -1, powers := [(19, 1), (30, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (20, 1), (24, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (19, 1), (24, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (20, 1), (28, 1), (49, 1), (54, 1)] }, { coefficient := -1, powers := [(12, 1), (23, 1), (26, 1), (49, 1)] }, { coefficient := 1, powers := [(12, 1), (25, 1), (30, 1), (49, 1)] }],
  [{ coefficient := -1, powers := [(19, 1), (24, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (24, 1), (44, 1), (54, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(12, 1), (19, 1), (24, 2), (26, 1), (44, 1), (46, 1), (53, 1), (54, 1)] }, { coefficient := -1, powers := [(12, 1), (19, 1), (24, 2), (44, 1), (46, 1), (54, 1), (55, 1)] }, { coefficient := 1, powers := [(12, 1), (19, 1), (24, 1), (28, 1), (44, 1), (48, 1), (52, 1), (54, 1), (55, 1)] }, { coefficient := 1, powers := [(12, 1), (19, 1), (24, 1), (30, 1), (44, 1), (48, 1), (51, 1), (52, 1), (54, 1)] }, { coefficient := -1, powers := [(12, 1), (19, 1), (24, 1), (30, 1), (44, 1), (48, 1), (53, 1), (54, 1)] }, { coefficient := -1, powers := [(12, 1), (19, 1), (24, 1), (30, 1), (49, 1), (53, 1), (54, 1)] }, { coefficient := -1, powers := [(12, 1), (19, 1), (24, 1), (36, 1), (39, 1), (53, 1), (54, 1)] }, { coefficient := -1, powers := [(12, 1), (20, 1), (24, 1), (47, 1), (52, 1), (54, 1)] }, { coefficient := -1, powers := [(12, 1), (20, 1), (28, 1), (38, 1), (49, 1), (54, 1), (60, 1)] }, { coefficient := -1, powers := [(12, 1), (20, 1), (28, 1), (41, 1), (49, 1), (54, 1), (57, 1)] }, { coefficient := -1, powers := [(12, 1), (20, 1), (28, 1), (46, 1), (49, 1), (52, 1), (54, 1)] }, { coefficient := -1, powers := [(12, 1), (20, 1), (29, 1), (46, 1), (49, 1), (54, 1)] }, { coefficient := 1, powers := [(12, 1), (23, 1), (26, 1), (38, 1), (49, 1), (60, 1)] }, { coefficient := 1, powers := [(12, 1), (23, 1), (26, 1), (41, 1), (49, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1), (23, 1), (26, 1), (46, 1), (49, 1), (52, 1)] }, { coefficient := -1, powers := [(12, 1), (23, 1), (46, 1), (49, 1), (54, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (26, 1), (47, 1), (52, 1)] }, { coefficient := -1, powers := [(12, 1), (24, 1), (41, 1), (58, 1)] }, { coefficient := -1, powers := [(12, 1), (24, 1), (47, 1), (54, 1)] }, { coefficient := -1, powers := [(12, 1), (25, 1), (29, 1), (49, 1), (52, 1), (54, 1)] }, { coefficient := -1, powers := [(12, 1), (25, 1), (30, 1), (38, 1), (49, 1), (60, 1)] }, { coefficient := -1, powers := [(12, 1), (25, 1), (30, 1), (41, 1), (49, 1), (57, 1)] }, { coefficient := -1, powers := [(12, 1), (25, 1), (30, 1), (46, 1), (49, 1), (52, 1)] }, { coefficient := 1, powers := [(12, 1), (29, 1), (49, 1), (54, 1)] }, { coefficient := -1, powers := [(12, 1), (30, 1), (44, 1), (48, 1), (52, 1)] }, { coefficient := 1, powers := [(12, 1), (30, 1), (49, 1), (52, 1)] }, { coefficient := -2, powers := [(19, 1), (24, 1), (26, 1), (46, 1), (53, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (37, 1), (55, 1), (59, 1)] }, { coefficient := -1, powers := [(19, 1), (24, 1), (43, 1), (50, 1), (55, 1)] }, { coefficient := 2, powers := [(19, 1), (24, 1), (46, 1), (55, 1)] }, { coefficient := -1, powers := [(19, 1), (24, 1), (52, 1), (55, 1)] }, { coefficient := -1, powers := [(19, 1), (28, 1), (48, 1), (52, 1), (55, 1)] }, { coefficient := -1, powers := [(19, 1), (30, 1), (48, 1), (51, 1), (52, 1)] }, { coefficient := 1, powers := [(19, 1), (30, 1), (48, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (24, 1), (25, 1), (44, 1), (47, 1), (48, 1), (54, 1), (55, 1)] }, { coefficient := -1, powers := [(12, 1), (24, 1), (39, 1), (44, 1), (54, 1), (61, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (44, 1), (49, 1), (54, 1), (55, 1)] }, { coefficient := -1, powers := [(25, 1), (47, 1), (48, 1), (55, 1)] }, { coefficient := 1, powers := [(39, 1), (61, 1)] }, { coefficient := -1, powers := [(49, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (19, 1), (24, 1), (25, 1), (43, 1), (55, 1), (57, 1)] }, { coefficient := -1, powers := [(0, 1), (19, 1), (24, 1), (34, 1), (37, 1), (55, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (19, 1), (24, 1), (55, 1), (56, 1)] }, { coefficient := 1, powers := [(6, 1), (19, 1), (24, 1), (34, 1), (55, 1)] }, { coefficient := -1, powers := [(13, 1), (19, 1), (24, 1), (25, 1), (55, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (25, 1), (43, 1), (55, 1)] }, { coefficient := -1, powers := [(19, 1), (24, 1), (34, 1), (37, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (12, 1), (19, 1), (24, 1), (30, 1), (44, 1), (54, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (19, 1), (30, 1), (57, 1)] }, { coefficient := -1, powers := [(2, 1), (12, 1), (24, 1), (44, 1), (54, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (58, 1)] }, { coefficient := -1, powers := [(8, 1), (12, 1), (24, 1), (36, 1), (44, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (19, 1), (24, 1), (31, 1), (55, 1)] }, { coefficient := -1, powers := [(19, 1), (20, 1), (24, 1), (50, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (19, 1), (24, 1), (25, 1), (31, 1), (43, 1), (55, 1)] }, { coefficient := -1, powers := [(3, 1), (19, 1), (24, 1), (31, 1), (34, 1), (37, 1), (55, 1)] }, { coefficient := 1, powers := [(9, 1), (19, 1), (20, 1), (24, 1), (25, 1), (43, 1), (55, 1)] }, { coefficient := -1, powers := [(9, 1), (19, 1), (20, 1), (24, 1), (34, 1), (37, 1), (55, 1)] }, { coefficient := -2, powers := [(12, 2), (20, 1), (24, 1), (30, 1), (44, 1), (49, 1), (54, 1)] }, { coefficient := -2, powers := [(12, 2), (24, 1), (25, 1), (30, 1), (44, 1), (49, 1), (54, 1)] }, { coefficient := -1, powers := [(12, 1), (19, 1), (20, 1), (24, 1), (30, 1), (49, 1), (51, 1), (54, 1)] }, { coefficient := -1, powers := [(12, 1), (19, 1), (20, 1), (24, 1), (36, 1), (39, 1), (51, 1), (54, 1)] }, { coefficient := 1, powers := [(12, 1), (19, 1), (21, 1), (24, 1), (28, 1), (44, 1), (54, 1), (55, 1)] }, { coefficient := -1, powers := [(12, 1), (19, 1), (24, 2), (25, 1), (44, 1), (54, 1), (55, 1)] }, { coefficient := 1, powers := [(12, 1), (19, 1), (24, 2), (26, 1), (44, 1), (51, 1), (54, 1)] }, { coefficient := 1, powers := [(12, 1), (20, 1), (24, 1), (44, 1), (54, 1)] }, { coefficient := -1, powers := [(12, 1), (20, 1), (28, 1), (49, 1), (54, 1)] }, { coefficient := 2, powers := [(12, 1), (20, 1), (30, 1), (49, 1)] }, { coefficient := -1, powers := [(12, 1), (21, 1), (30, 1), (44, 1)] }, { coefficient := 1, powers := [(12, 1), (23, 1), (25, 1), (49, 1), (54, 1)] }, { coefficient := 1, powers := [(12, 1), (25, 1), (30, 1), (49, 1)] }, { coefficient := -1, powers := [(19, 1), (21, 1), (28, 1), (55, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (25, 1), (55, 1)] }, { coefficient := -2, powers := [(19, 1), (24, 1), (26, 1), (51, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (12, 1), (24, 1), (33, 1), (44, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1)] }, { coefficient := 1, powers := [(12, 1), (19, 1), (24, 2), (51, 1), (54, 1)] }, { coefficient := -1, powers := [(12, 1), (20, 1), (24, 1), (52, 1)] }, { coefficient := -1, powers := [(12, 1), (20, 1), (29, 1), (48, 1)] }, { coefficient := -2, powers := [(12, 1), (24, 1)] }, { coefficient := -2, powers := [(18, 1), (24, 1), (51, 1)] }]
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
    (values : Fin 63 → R) :
    ¬ ∀ index : Fin 64,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component37.SelectedLeafB0_2_0.selectedHasNoCommonZero

end Krenn.Component37.SelectedLeafB0_2_0
