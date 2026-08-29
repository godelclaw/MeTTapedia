import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component37.SelectedLeafB5_2_7_4

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "6e8ac97360d4df3c7dd1f4138e5921eed6067eee9a9c51e300dbd06614e58ff6"
def certificateSHA256 : String := "bc7e5077682892f2fdb28aa971c4515d38323972b2a77d3b37ed95ceefef9b13"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 58 → Fin 670 := ![
  13,
  17,
  51,
  148,
  149,
  152,
  167,
  168,
  175,
  176,
  177,
  179,
  180,
  181,
  183,
  216,
  221,
  222,
  279,
  294,
  295,
  296,
  297,
  300,
  301,
  311,
  312,
  316,
  317,
  334,
  358,
  410,
  432,
  433,
  435,
  438,
  450,
  453,
  454,
  476,
  566,
  567,
  570,
  584,
  591,
  602,
  603,
  650,
  655,
  657,
  658,
  660,
  661,
  663,
  665,
  666,
  667,
  669
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 58 → SparsePoly (Fin 69) := ![
  [{ coefficient := 1, powers := [(17, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (31, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (31, 1)] }, { coefficient := 1, powers := [(18, 1), (26, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (26, 1)] }, { coefficient := 1, powers := [(26, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (44, 1)] }, { coefficient := 1, powers := [(40, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (25, 1)] }, { coefficient := 1, powers := [(18, 1), (20, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (26, 1)] }, { coefficient := 1, powers := [(18, 1), (20, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (20, 1)] }, { coefficient := 1, powers := [(18, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (44, 1)] }, { coefficient := 1, powers := [(19, 1), (20, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (49, 1)] }, { coefficient := 1, powers := [(19, 1), (21, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (55, 1)] }, { coefficient := 1, powers := [(30, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (44, 1)] }, { coefficient := 1, powers := [(28, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (54, 1)] }, { coefficient := 1, powers := [(30, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(28, 1), (53, 1)] }, { coefficient := -1, powers := [(29, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (31, 1), (45, 1)] }, { coefficient := 1, powers := [(8, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (26, 1), (47, 1)] }, { coefficient := 1, powers := [(9, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (26, 1), (48, 1)] }, { coefficient := 1, powers := [(31, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (25, 1), (44, 1)] }, { coefficient := 1, powers := [(19, 1), (20, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1)] }, { coefficient := 1, powers := [(20, 1), (44, 1)] }, { coefficient := 1, powers := [(25, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (49, 1)] }, { coefficient := 1, powers := [(21, 1), (44, 1)] }, { coefficient := 1, powers := [(25, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (51, 1)] }, { coefficient := 1, powers := [(20, 1), (51, 1)] }, { coefficient := 1, powers := [(25, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (55, 1)] }, { coefficient := 1, powers := [(20, 1), (55, 1)] }, { coefficient := 1, powers := [(26, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (50, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (50, 1)] }, { coefficient := 1, powers := [(18, 1), (28, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (59, 1)] }, { coefficient := 1, powers := [(9, 1), (43, 1)] }, { coefficient := 1, powers := [(13, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (52, 1)] }, { coefficient := 1, powers := [(24, 1), (57, 1)] }, { coefficient := 1, powers := [(29, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (54, 1)] }, { coefficient := 1, powers := [(30, 1), (41, 1)] }, { coefficient := 1, powers := [(30, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1), (55, 1)] }, { coefficient := 1, powers := [(26, 1), (46, 1), (51, 1)] }, { coefficient := 1, powers := [(55, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (49, 1), (52, 1)] }, { coefficient := 1, powers := [(21, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(49, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (39, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (59, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (31, 1), (58, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1), (49, 1)] }, { coefficient := 1, powers := [(19, 1), (31, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (25, 1), (41, 1)] }, { coefficient := 1, powers := [(18, 1), (25, 1), (46, 1)] }, { coefficient := 1, powers := [(18, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (48, 1)] }, { coefficient := 1, powers := [(5, 1), (28, 1), (60, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1)] }, { coefficient := 1, powers := [(18, 1), (28, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (49, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1)] }, { coefficient := 1, powers := [(18, 1), (28, 1), (49, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (52, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (52, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (57, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1)] }, { coefficient := 1, powers := [(12, 1), (30, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (61, 1)] }, { coefficient := 1, powers := [(12, 1), (26, 1), (47, 1)] }, { coefficient := 1, powers := [(12, 1), (58, 1)] }, { coefficient := 1, powers := [(19, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (41, 1)] }, { coefficient := 1, powers := [(18, 1), (46, 1)] }, { coefficient := 1, powers := [(18, 1), (52, 1)] }, { coefficient := 1, powers := [(18, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (55, 1)] }, { coefficient := 1, powers := [(30, 1), (42, 1)] }, { coefficient := 1, powers := [(30, 1), (48, 1), (51, 1)] }, { coefficient := 1, powers := [(33, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1), (55, 1)] }, { coefficient := 1, powers := [(26, 1), (47, 1), (51, 1)] }, { coefficient := 1, powers := [(44, 1), (55, 1)] }, { coefficient := 1, powers := [(51, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (44, 1), (54, 1)] }, { coefficient := 1, powers := [(24, 1), (58, 1)] }, { coefficient := 1, powers := [(30, 1), (49, 1)] }, { coefficient := 1, powers := [(36, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (51, 1), (57, 1)] }, { coefficient := 1, powers := [(24, 1), (53, 1)] }, { coefficient := 1, powers := [(29, 1), (42, 1)] }, { coefficient := 1, powers := [(29, 1), (48, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (44, 1), (54, 1)] }, { coefficient := 1, powers := [(29, 1), (58, 1)] }, { coefficient := 1, powers := [(30, 1), (41, 1), (44, 1)] }, { coefficient := 1, powers := [(30, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (40, 1), (58, 1)] }, { coefficient := 1, powers := [(3, 1), (31, 1), (58, 1)] }, { coefficient := 1, powers := [(9, 1), (20, 1), (58, 1)] }, { coefficient := 1, powers := [(9, 1), (26, 1), (44, 1)] }, { coefficient := 1, powers := [(26, 1), (40, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (37, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (40, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (43, 1), (50, 1)] }, { coefficient := 1, powers := [(17, 1), (23, 1), (50, 1)] }, { coefficient := 1, powers := [(17, 1), (28, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1)] }, { coefficient := 1, powers := [(3, 1), (34, 1)] }, { coefficient := 1, powers := [(13, 1), (20, 1)] }, { coefficient := 1, powers := [(20, 1), (56, 1)] }, { coefficient := 1, powers := [(25, 1), (43, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (50, 1)] }, { coefficient := 1, powers := [(6, 1), (31, 1)] }, { coefficient := 1, powers := [(9, 1), (25, 1)] }, { coefficient := 1, powers := [(20, 1), (50, 1)] }, { coefficient := 1, powers := [(25, 1), (40, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (42, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (48, 1), (53, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1), (29, 1), (48, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (53, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (37, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (40, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (43, 1), (50, 1)] }, { coefficient := 1, powers := [(3, 1), (25, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (31, 1), (56, 1)] }, { coefficient := 1, powers := [(3, 1), (34, 1), (50, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (31, 1), (43, 1)] }, { coefficient := 1, powers := [(6, 1), (34, 1), (40, 1)] }, { coefficient := 1, powers := [(9, 1), (20, 1), (56, 1)] }, { coefficient := 1, powers := [(9, 1), (25, 1), (43, 1)] }, { coefficient := 1, powers := [(9, 1), (34, 1), (37, 1)] }, { coefficient := 1, powers := [(13, 1), (20, 1), (50, 1)] }, { coefficient := 1, powers := [(13, 1), (25, 1), (40, 1)] }, { coefficient := 1, powers := [(13, 1), (31, 1), (37, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (39, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (42, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (49, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (49, 1)] }, { coefficient := 1, powers := [(8, 1), (36, 1), (42, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (58, 1)] }, { coefficient := 1, powers := [(12, 1), (30, 1), (49, 1)] }, { coefficient := 1, powers := [(12, 1), (36, 1), (39, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (55, 1)] }, { coefficient := 1, powers := [(19, 1), (30, 1), (42, 1)] }, { coefficient := 1, powers := [(19, 1), (33, 1), (39, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(40, 1)] }],
  [{ coefficient := 1, powers := [(42, 1)] }],
  [{ coefficient := 1, powers := [(57, 1), (66, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(58, 1), (67, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(25, 1), (68, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(30, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 58 → SparsePoly (Fin 69) := ![
  [{ coefficient := -1, powers := [(0, 1), (23, 1), (63, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (23, 1), (43, 1), (63, 1)] }, { coefficient := 1, powers := [(20, 1), (23, 1), (43, 1), (63, 1)] }, { coefficient := 1, powers := [(20, 1), (23, 1), (56, 1), (63, 1)] }, { coefficient := 1, powers := [(23, 1), (25, 1), (43, 1), (63, 1)] }, { coefficient := 1, powers := [(23, 1), (34, 1), (37, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (36, 1), (37, 1), (55, 1), (66, 1)] }, { coefficient := -1, powers := [(36, 1), (37, 1), (43, 1), (55, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (6, 1), (20, 1), (24, 1), (45, 1), (61, 1), (63, 1)] }, { coefficient := 1, powers := [(13, 1), (24, 1), (37, 1), (61, 1)] }, { coefficient := -1, powers := [(13, 1), (33, 1), (37, 1), (49, 1)] }, { coefficient := -1, powers := [(24, 1), (37, 1), (43, 1), (61, 1)] }, { coefficient := 1, powers := [(33, 1), (37, 1), (43, 1), (49, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (13, 1), (37, 1), (48, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (37, 1), (43, 1), (48, 1), (61, 1)] }, { coefficient := 1, powers := [(13, 1), (19, 1), (33, 1), (37, 1), (48, 1)] }, { coefficient := -1, powers := [(19, 1), (33, 1), (37, 1), (43, 1), (48, 1)] }, { coefficient := 1, powers := [(25, 1), (43, 1), (47, 1), (67, 1)] }, { coefficient := -1, powers := [(34, 1), (37, 1), (47, 1), (67, 1)] }],
  [{ coefficient := -1, powers := [(26, 1), (56, 1), (67, 1)] }],
  [{ coefficient := 2, powers := [(6, 1), (20, 1), (24, 1), (26, 1), (44, 1), (46, 1), (59, 1), (68, 1)] }, { coefficient := -1, powers := [(6, 1), (20, 1), (24, 1), (58, 2), (59, 1), (67, 1), (68, 1)] }, { coefficient := -1, powers := [(6, 1), (20, 1), (24, 1), (58, 1), (59, 1), (68, 1)] }],
  [{ coefficient := -2, powers := [(6, 1), (20, 1), (24, 1), (44, 1), (46, 1), (59, 1)] }, { coefficient := -1, powers := [(6, 1), (20, 1), (24, 1), (47, 1), (58, 1), (59, 1), (67, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (20, 1), (23, 1), (49, 1), (55, 1), (59, 1), (62, 1)] }, { coefficient := -2, powers := [(6, 1), (20, 1), (24, 1), (26, 1), (44, 1), (46, 1), (51, 1), (59, 1), (62, 1)] }, { coefficient := -2, powers := [(6, 1), (20, 1), (24, 1), (26, 1), (44, 1), (46, 1), (51, 1), (59, 1), (68, 1)] }, { coefficient := 2, powers := [(6, 1), (20, 1), (24, 1), (44, 1), (46, 1), (55, 1), (59, 1)] }, { coefficient := -1, powers := [(6, 1), (20, 1), (24, 1), (44, 1), (55, 1), (58, 1), (59, 1), (62, 1), (67, 1)] }, { coefficient := -1, powers := [(6, 1), (20, 1), (24, 1), (44, 1), (55, 1), (59, 1), (62, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1), (24, 1), (51, 1), (58, 2), (59, 1), (67, 1), (68, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1), (24, 1), (51, 1), (58, 1), (59, 1), (68, 1)] }, { coefficient := -1, powers := [(6, 1), (20, 1), (29, 1), (48, 1), (51, 1), (58, 1), (59, 1), (62, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (20, 1), (21, 1), (23, 1), (55, 1), (59, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (20, 2), (23, 1), (55, 1), (59, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (18, 1), (20, 1), (49, 1), (58, 1), (59, 1), (67, 1)] }, { coefficient := -1, powers := [(13, 1), (18, 1), (31, 1), (37, 1), (49, 1)] }, { coefficient := 1, powers := [(18, 1), (31, 1), (37, 1), (43, 1), (49, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (18, 1), (20, 1), (55, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (12, 1), (20, 1), (44, 1), (58, 1), (59, 1), (67, 1)] }, { coefficient := -1, powers := [(12, 1), (13, 1), (31, 1), (37, 1), (44, 1)] }, { coefficient := 1, powers := [(12, 1), (31, 1), (37, 1), (43, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (6, 1), (20, 1), (58, 1), (59, 1), (60, 1), (66, 1)] }, { coefficient := 1, powers := [(6, 1), (18, 1), (20, 1), (48, 1), (58, 1), (59, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (6, 1), (20, 1), (24, 1), (61, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(25, 1), (43, 1), (67, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (13, 1), (37, 1), (61, 1)] }, { coefficient := -1, powers := [(2, 1), (37, 1), (43, 1), (61, 1)] }, { coefficient := -1, powers := [(13, 1), (19, 1), (33, 1), (37, 1)] }, { coefficient := 1, powers := [(19, 1), (33, 1), (37, 1), (43, 1)] }],
  [{ coefficient := -2, powers := [(6, 1), (20, 1), (24, 1), (46, 1), (55, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (18, 1), (20, 1), (24, 1), (55, 1), (58, 1), (59, 1), (62, 1), (67, 1)] }, { coefficient := 1, powers := [(6, 1), (18, 1), (20, 1), (24, 1), (55, 1), (59, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (6, 1), (20, 1), (52, 1), (55, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (18, 1), (20, 1), (23, 1), (55, 1), (59, 1), (62, 1)] }],
  [{ coefficient := 2, powers := [(6, 1), (18, 1), (20, 1), (24, 1), (26, 1), (44, 1), (46, 1), (59, 1), (62, 1)] }, { coefficient := 1, powers := [(6, 1), (18, 1), (20, 1), (29, 1), (48, 1), (58, 1), (59, 1), (62, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (18, 1), (20, 1), (24, 1), (47, 1), (58, 1), (59, 1), (67, 1)] }, { coefficient := 2, powers := [(6, 1), (19, 1), (20, 1), (24, 1), (46, 1), (59, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (43, 1), (63, 1)] }, { coefficient := -1, powers := [(20, 1), (43, 1), (63, 1)] }, { coefficient := -1, powers := [(20, 1), (56, 1), (63, 1)] }, { coefficient := -1, powers := [(25, 1), (43, 1), (63, 1)] }, { coefficient := -1, powers := [(34, 1), (37, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(25, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (18, 1), (20, 1), (25, 1), (53, 1), (58, 1), (59, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (6, 1), (20, 1), (44, 1), (51, 1), (58, 1), (59, 1), (60, 1), (66, 1), (67, 1)] }, { coefficient := 1, powers := [(6, 1), (12, 1), (20, 1), (44, 1), (48, 1), (58, 1), (59, 1), (66, 1), (67, 1)] }, { coefficient := 1, powers := [(6, 1), (18, 1), (20, 1), (25, 1), (44, 1), (48, 1), (53, 1), (58, 1), (59, 1), (66, 1), (67, 1)] }, { coefficient := -1, powers := [(6, 1), (18, 1), (20, 1), (25, 1), (44, 1), (49, 1), (55, 1), (59, 1), (67, 1)] }, { coefficient := -1, powers := [(6, 1), (18, 1), (20, 1), (44, 1), (48, 1), (51, 1), (58, 1), (59, 1), (66, 1), (67, 1)] }],
  [{ coefficient := -2, powers := [(6, 1), (19, 1), (20, 1), (24, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (6, 1), (20, 1), (55, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (6, 1), (20, 1), (61, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (33, 1), (37, 1)] }, { coefficient := -1, powers := [(33, 1), (37, 1), (43, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (20, 1), (23, 1), (49, 1), (55, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1), (24, 1), (53, 1), (58, 1), (59, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (20, 1), (53, 1), (58, 1), (59, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (20, 1), (55, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (20, 1), (25, 1), (49, 1), (55, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (20, 1), (49, 1), (58, 1), (59, 1), (67, 1)] }, { coefficient := 1, powers := [(13, 1), (31, 1), (37, 1), (49, 1)] }, { coefficient := -1, powers := [(31, 1), (37, 1), (43, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (20, 1), (24, 1), (58, 1), (59, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (20, 1), (23, 1), (25, 1), (49, 1), (55, 1), (59, 1)] }, { coefficient := -1, powers := [(6, 1), (20, 1), (24, 1), (25, 1), (53, 1), (58, 1), (59, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (19, 1), (20, 1), (58, 1), (59, 1), (67, 1)] }, { coefficient := 1, powers := [(13, 1), (19, 1), (31, 1), (37, 1)] }, { coefficient := -1, powers := [(19, 1), (31, 1), (37, 1), (43, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (18, 1), (20, 1), (24, 1), (58, 1), (59, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (12, 1), (20, 1), (58, 1), (59, 1), (67, 1)] }, { coefficient := 1, powers := [(12, 1), (13, 1), (31, 1), (37, 1)] }, { coefficient := -1, powers := [(12, 1), (31, 1), (37, 1), (43, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (18, 1), (20, 1), (58, 1), (59, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (6, 1), (20, 1), (51, 1), (58, 1), (59, 1), (60, 1), (66, 1), (67, 1)] }, { coefficient := -1, powers := [(6, 1), (12, 1), (20, 1), (48, 1), (58, 1), (59, 1), (66, 1), (67, 1)] }, { coefficient := -1, powers := [(6, 1), (18, 1), (20, 1), (25, 1), (48, 1), (53, 1), (58, 1), (59, 1), (66, 1), (67, 1)] }, { coefficient := 1, powers := [(6, 1), (18, 1), (20, 1), (25, 1), (49, 1), (55, 1), (59, 1), (67, 1)] }, { coefficient := 1, powers := [(6, 1), (18, 1), (20, 1), (48, 1), (51, 1), (58, 1), (59, 1), (66, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(56, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(50, 1)] }],
  [{ coefficient := 1, powers := [(43, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (20, 1), (58, 1), (59, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(6, 1), (20, 1), (58, 1), (59, 1), (67, 1)] }, { coefficient := -1, powers := [(13, 1), (31, 1), (37, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1), (43, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (18, 1), (20, 1), (23, 1), (49, 1), (55, 1), (59, 1)] }, { coefficient := -2, powers := [(6, 1), (18, 1), (20, 1), (24, 1), (26, 1), (44, 1), (46, 1), (51, 1), (59, 1)] }, { coefficient := -1, powers := [(6, 1), (18, 1), (20, 1), (24, 1), (44, 1), (55, 1), (58, 1), (59, 1), (67, 1)] }, { coefficient := -1, powers := [(6, 1), (18, 1), (20, 1), (24, 1), (44, 1), (55, 1), (59, 1)] }, { coefficient := -1, powers := [(6, 1), (18, 1), (20, 1), (29, 1), (48, 1), (51, 1), (58, 1), (59, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (37, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (43, 1), (50, 1)] }, { coefficient := -1, powers := [(2, 1), (6, 1), (20, 1), (39, 1), (59, 1), (61, 1)] }, { coefficient := 1, powers := [(20, 1), (43, 1), (50, 1)] }, { coefficient := 1, powers := [(20, 1), (50, 1), (56, 1)] }, { coefficient := 1, powers := [(25, 1), (43, 1), (50, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1), (50, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (2, 1), (56, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (17, 1), (28, 1), (63, 1)] }, { coefficient := 2, powers := [(0, 1), (18, 1), (28, 1), (43, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (56, 1), (58, 1), (67, 1)] }, { coefficient := 1, powers := [(0, 1), (56, 1)] }, { coefficient := -1, powers := [(2, 1), (6, 1), (18, 1), (20, 1), (24, 1), (26, 1), (45, 1), (61, 1), (63, 1)] }, { coefficient := 1, powers := [(2, 1), (13, 1), (26, 1), (37, 1), (48, 1), (61, 1)] }, { coefficient := -1, powers := [(2, 1), (26, 1), (37, 1), (43, 1), (48, 1), (61, 1)] }, { coefficient := 1, powers := [(6, 1), (34, 1)] }, { coefficient := -1, powers := [(13, 1), (18, 1), (24, 1), (26, 1), (37, 1), (61, 1)] }, { coefficient := 1, powers := [(13, 1), (18, 1), (26, 1), (33, 1), (37, 1), (49, 1)] }, { coefficient := -1, powers := [(13, 1), (19, 1), (26, 1), (33, 1), (37, 1), (48, 1)] }, { coefficient := 1, powers := [(18, 1), (20, 1), (28, 1), (43, 1), (63, 1)] }, { coefficient := 1, powers := [(18, 1), (20, 1), (28, 1), (56, 1), (63, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (26, 1), (37, 1), (43, 1), (61, 1)] }, { coefficient := 1, powers := [(18, 1), (25, 1), (28, 1), (43, 1), (63, 1)] }, { coefficient := -1, powers := [(18, 1), (26, 1), (33, 1), (37, 1), (43, 1), (49, 1)] }, { coefficient := 1, powers := [(18, 1), (28, 1), (34, 1), (37, 1), (63, 1)] }, { coefficient := 1, powers := [(19, 1), (26, 1), (33, 1), (37, 1), (43, 1), (48, 1)] }, { coefficient := -1, powers := [(25, 1), (26, 1), (43, 1), (47, 1), (67, 1)] }, { coefficient := -1, powers := [(25, 1), (43, 1)] }, { coefficient := 1, powers := [(26, 1), (34, 1), (37, 1), (47, 1), (67, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (6, 1), (20, 1), (57, 1), (58, 1), (59, 1), (66, 1)] }, { coefficient := 1, powers := [(2, 1), (6, 1), (20, 1), (58, 2), (59, 1), (67, 1)] }, { coefficient := 1, powers := [(2, 1), (13, 1), (31, 1), (37, 1), (58, 1)] }, { coefficient := -1, powers := [(2, 1), (31, 1), (37, 1), (43, 1), (58, 1)] }, { coefficient := 1, powers := [(6, 1), (8, 1), (20, 1), (36, 1), (58, 1), (59, 1), (67, 1)] }, { coefficient := 1, powers := [(8, 1), (13, 1), (31, 1), (36, 1), (37, 1)] }, { coefficient := -1, powers := [(8, 1), (31, 1), (36, 1), (37, 1), (43, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (6, 1), (20, 1), (33, 1), (58, 1), (59, 1)] }, { coefficient := -1, powers := [(5, 1), (13, 1), (31, 1), (36, 1), (37, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (36, 1), (37, 1), (43, 1), (55, 1)] }, { coefficient := -1, powers := [(6, 1), (12, 1), (20, 1), (24, 1), (58, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (18, 1), (20, 1), (24, 1), (51, 1), (58, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (6, 1), (20, 1), (39, 1), (59, 1), (61, 1)] }, { coefficient := -1, powers := [(3, 1), (31, 1), (56, 1)] }, { coefficient := -1, powers := [(5, 1), (6, 1), (20, 1), (29, 1), (51, 1), (58, 1), (59, 1), (60, 1), (66, 1)] }, { coefficient := 1, powers := [(5, 1), (6, 1), (20, 1), (33, 1), (58, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (6, 1), (20, 1), (36, 1), (55, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (12, 1), (20, 1), (29, 1), (48, 1), (58, 1), (59, 1), (66, 1)] }, { coefficient := 1, powers := [(6, 1), (18, 1), (20, 1), (25, 1), (29, 1), (48, 1), (53, 1), (58, 1), (59, 1), (66, 1)] }, { coefficient := -1, powers := [(6, 1), (18, 1), (20, 1), (25, 1), (29, 1), (49, 1), (55, 1), (59, 1)] }, { coefficient := -1, powers := [(6, 1), (18, 1), (20, 1), (29, 1), (48, 1), (51, 1), (58, 1), (59, 1), (66, 1)] }, { coefficient := -1, powers := [(6, 1), (19, 1), (20, 1), (24, 1), (55, 1), (59, 1)] }, { coefficient := -1, powers := [(6, 1), (20, 1), (59, 1)] }, { coefficient := -1, powers := [(9, 1), (20, 1), (56, 1)] }, { coefficient := 1, powers := [(9, 1), (25, 1), (43, 1)] }, { coefficient := -1, powers := [(9, 1), (34, 1), (37, 1)] }],
  [{ coefficient := -2, powers := [(6, 1), (12, 1), (20, 1), (24, 1), (26, 1), (44, 1), (46, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (12, 1), (20, 1), (24, 1), (58, 2), (59, 1), (67, 1)] }, { coefficient := 1, powers := [(6, 1), (12, 1), (20, 1), (24, 1), (58, 1), (59, 1)] }, { coefficient := 2, powers := [(6, 1), (18, 1), (20, 1), (24, 1), (26, 1), (44, 1), (46, 1), (51, 1), (59, 1)] }, { coefficient := -1, powers := [(6, 1), (18, 1), (20, 1), (24, 1), (51, 1), (58, 2), (59, 1), (67, 1)] }, { coefficient := -1, powers := [(6, 1), (18, 1), (20, 1), (24, 1), (51, 1), (58, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (5, 1), (6, 1), (20, 1), (59, 1), (61, 1), (63, 1)] }, { coefficient := 1, powers := [(5, 1), (6, 1), (20, 1), (44, 1), (46, 1), (51, 1), (58, 1), (59, 1), (60, 1), (66, 1), (67, 1)] }, { coefficient := -1, powers := [(5, 1), (6, 1), (20, 1), (47, 1), (51, 1), (58, 1), (59, 1), (60, 1), (66, 1), (67, 1)] }, { coefficient := 1, powers := [(5, 1), (6, 1), (20, 1), (58, 1), (59, 1), (61, 1), (67, 1)] }, { coefficient := 1, powers := [(5, 1), (13, 1), (31, 1), (37, 1), (61, 1)] }, { coefficient := -1, powers := [(5, 1), (31, 1), (37, 1), (43, 1), (61, 1)] }, { coefficient := -1, powers := [(6, 1), (12, 1), (20, 1), (44, 1), (46, 1), (48, 1), (58, 1), (59, 1), (66, 1), (67, 1)] }, { coefficient := 1, powers := [(6, 1), (12, 1), (20, 1), (44, 1), (48, 1), (58, 1), (59, 1), (67, 1)] }, { coefficient := 1, powers := [(6, 1), (12, 1), (20, 1), (47, 1), (48, 1), (58, 1), (59, 1), (66, 1), (67, 1)] }, { coefficient := -1, powers := [(6, 1), (12, 1), (20, 1), (49, 1), (58, 1), (59, 1), (67, 1)] }, { coefficient := -1, powers := [(6, 1), (18, 1), (20, 1), (25, 1), (44, 1), (46, 1), (48, 1), (53, 1), (58, 1), (59, 1), (66, 1), (67, 1)] }, { coefficient := 1, powers := [(6, 1), (18, 1), (20, 1), (25, 1), (44, 1), (46, 1), (49, 1), (55, 1), (59, 1), (67, 1)] }, { coefficient := 1, powers := [(6, 1), (18, 1), (20, 1), (25, 1), (47, 1), (48, 1), (53, 1), (58, 1), (59, 1), (66, 1), (67, 1)] }, { coefficient := -1, powers := [(6, 1), (18, 1), (20, 1), (25, 1), (47, 1), (49, 1), (55, 1), (59, 1), (67, 1)] }, { coefficient := 1, powers := [(6, 1), (18, 1), (20, 1), (44, 1), (46, 1), (48, 1), (51, 1), (58, 1), (59, 1), (66, 1), (67, 1)] }, { coefficient := -1, powers := [(6, 1), (18, 1), (20, 1), (47, 1), (48, 1), (51, 1), (58, 1), (59, 1), (66, 1), (67, 1)] }, { coefficient := 1, powers := [(6, 1), (18, 1), (20, 1), (49, 1), (51, 1), (58, 1), (59, 1), (67, 1)] }, { coefficient := -1, powers := [(6, 1), (19, 1), (20, 1), (48, 1), (51, 1), (58, 1), (59, 1), (67, 1)] }, { coefficient := 1, powers := [(12, 1), (13, 1), (31, 1), (37, 1), (44, 1), (48, 1)] }, { coefficient := -1, powers := [(12, 1), (13, 1), (31, 1), (37, 1), (49, 1)] }, { coefficient := -1, powers := [(12, 1), (31, 1), (37, 1), (43, 1), (44, 1), (48, 1)] }, { coefficient := 1, powers := [(12, 1), (31, 1), (37, 1), (43, 1), (49, 1)] }, { coefficient := 1, powers := [(13, 1), (18, 1), (31, 1), (37, 1), (49, 1), (51, 1)] }, { coefficient := -1, powers := [(13, 1), (19, 1), (31, 1), (37, 1), (48, 1), (51, 1)] }, { coefficient := -1, powers := [(18, 1), (31, 1), (37, 1), (43, 1), (49, 1), (51, 1)] }, { coefficient := 1, powers := [(19, 1), (31, 1), (37, 1), (43, 1), (48, 1), (51, 1)] }]
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
    (values : Fin 69 → R) :
    ¬ ∀ index : Fin 58,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component37.SelectedLeafB5_2_7_4.selectedHasNoCommonZero

end Krenn.Component37.SelectedLeafB5_2_7_4
