import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component37.SelectedLeafB5_2_2_4_3

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "29e8a56dfc4dd32febf02295b45eddd6d516d931715437c0d7fe9e386ec429e2"
def certificateSHA256 : String := "4b82f3bcf4ba1597cd8a61259da5764afc2871376adfde5b1419df2d72b7a006"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 52 → Fin 673 := ![
  8,
  13,
  17,
  167,
  168,
  175,
  179,
  180,
  181,
  257,
  279,
  294,
  295,
  296,
  297,
  300,
  301,
  302,
  316,
  356,
  406,
  408,
  410,
  430,
  433,
  438,
  445,
  450,
  451,
  453,
  454,
  466,
  481,
  541,
  566,
  602,
  603,
  606,
  607,
  646,
  655,
  657,
  658,
  660,
  661,
  663,
  664,
  666,
  667,
  669,
  670,
  671
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 52 → SparsePoly (Fin 69) := ![
  [{ coefficient := 1, powers := [(9, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (25, 1)] }, { coefficient := 1, powers := [(18, 1), (20, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (26, 1)] }, { coefficient := 1, powers := [(18, 1), (20, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (20, 1)] }, { coefficient := 1, powers := [(18, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (55, 1)] }, { coefficient := 1, powers := [(30, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (44, 1)] }, { coefficient := 1, powers := [(28, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (54, 1)] }, { coefficient := 1, powers := [(30, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (25, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (25, 1), (44, 1)] }, { coefficient := 1, powers := [(19, 1), (20, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1)] }, { coefficient := 1, powers := [(20, 1), (44, 1)] }, { coefficient := 1, powers := [(25, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (49, 1)] }, { coefficient := 1, powers := [(21, 1), (44, 1)] }, { coefficient := 1, powers := [(25, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (51, 1)] }, { coefficient := 1, powers := [(20, 1), (51, 1)] }, { coefficient := 1, powers := [(25, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (55, 1)] }, { coefficient := 1, powers := [(20, 1), (55, 1)] }, { coefficient := 1, powers := [(26, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (50, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (50, 1)] }, { coefficient := 1, powers := [(18, 1), (28, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (59, 1)] }, { coefficient := 1, powers := [(9, 1), (43, 1)] }, { coefficient := 1, powers := [(13, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (28, 1)] }, { coefficient := 1, powers := [(23, 1), (50, 1)] }, { coefficient := 1, powers := [(28, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1), (55, 1)] }, { coefficient := 1, powers := [(26, 1), (46, 1), (51, 1)] }, { coefficient := 1, powers := [(55, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (25, 1), (60, 1)] }, { coefficient := 1, powers := [(18, 1), (21, 1)] }, { coefficient := 1, powers := [(18, 1), (25, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (20, 1), (50, 1)] }, { coefficient := 1, powers := [(18, 1), (25, 1), (40, 1)] }, { coefficient := 1, powers := [(18, 1), (31, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (20, 1), (58, 1)] }, { coefficient := 1, powers := [(18, 1), (26, 1), (44, 1)] }, { coefficient := 1, powers := [(19, 1), (20, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (25, 1), (41, 1)] }, { coefficient := 1, powers := [(18, 1), (25, 1), (46, 1)] }, { coefficient := 1, powers := [(18, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (46, 1)] }, { coefficient := 1, powers := [(18, 1), (28, 1), (41, 1)] }, { coefficient := 1, powers := [(18, 1), (28, 1), (46, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (49, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1)] }, { coefficient := 1, powers := [(18, 1), (28, 1), (49, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1)] }, { coefficient := 1, powers := [(12, 1), (30, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (60, 1)] }, { coefficient := 1, powers := [(18, 1), (21, 1), (52, 1)] }, { coefficient := 1, powers := [(18, 1), (21, 1), (57, 1)] }, { coefficient := 1, powers := [(18, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (61, 1)] }, { coefficient := 1, powers := [(12, 1), (26, 1), (47, 1)] }, { coefficient := 1, powers := [(12, 1), (58, 1)] }, { coefficient := 1, powers := [(19, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (20, 1)] }, { coefficient := 1, powers := [(18, 1), (20, 1), (56, 1)] }, { coefficient := 1, powers := [(18, 1), (25, 1), (43, 1)] }, { coefficient := 1, powers := [(18, 1), (34, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (41, 1)] }, { coefficient := 1, powers := [(18, 1), (46, 1)] }, { coefficient := 1, powers := [(18, 1), (52, 1)] }, { coefficient := 1, powers := [(18, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (55, 1)] }, { coefficient := 1, powers := [(30, 1), (42, 1)] }, { coefficient := 1, powers := [(30, 1), (48, 1), (51, 1)] }, { coefficient := 1, powers := [(33, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1), (54, 1)] }, { coefficient := 1, powers := [(20, 1), (44, 1), (54, 1)] }, { coefficient := 1, powers := [(20, 1), (58, 1)] }, { coefficient := 1, powers := [(26, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (49, 1), (50, 1)] }, { coefficient := 1, powers := [(6, 1), (31, 1), (49, 1)] }, { coefficient := 1, powers := [(9, 1), (25, 1), (49, 1)] }, { coefficient := 1, powers := [(21, 1), (44, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (20, 1), (61, 1)] }, { coefficient := 1, powers := [(12, 1), (20, 1), (58, 1)] }, { coefficient := 1, powers := [(12, 1), (26, 1), (44, 1)] }, { coefficient := 1, powers := [(19, 1), (20, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (44, 1), (54, 1)] }, { coefficient := 1, powers := [(24, 1), (58, 1)] }, { coefficient := 1, powers := [(30, 1), (49, 1)] }, { coefficient := 1, powers := [(36, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1)] }, { coefficient := 1, powers := [(3, 1), (34, 1)] }, { coefficient := 1, powers := [(13, 1), (20, 1)] }, { coefficient := 1, powers := [(20, 1), (56, 1)] }, { coefficient := 1, powers := [(25, 1), (43, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (50, 1)] }, { coefficient := 1, powers := [(6, 1), (31, 1)] }, { coefficient := 1, powers := [(9, 1), (25, 1)] }, { coefficient := 1, powers := [(20, 1), (50, 1)] }, { coefficient := 1, powers := [(25, 1), (40, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (37, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1)] }, { coefficient := 1, powers := [(3, 1), (25, 1), (60, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1), (60, 1)] }, { coefficient := 1, powers := [(20, 1)] }, { coefficient := 1, powers := [(25, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (37, 1), (61, 1)] }, { coefficient := 1, powers := [(0, 1), (44, 1), (51, 1)] }, { coefficient := 1, powers := [(3, 1), (25, 1), (61, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1), (61, 1)] }, { coefficient := 1, powers := [(20, 1), (44, 1), (51, 1)] }, { coefficient := 1, powers := [(25, 1), (44, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (39, 1), (61, 1)] }, { coefficient := 1, powers := [(0, 1), (42, 1), (58, 1)] }, { coefficient := 1, powers := [(0, 1), (49, 1), (55, 1)] }, { coefficient := 1, powers := [(21, 1), (44, 1), (55, 1)] }, { coefficient := 1, powers := [(21, 1), (51, 1), (58, 1)] }, { coefficient := 1, powers := [(26, 1), (42, 1), (44, 1)] }, { coefficient := 1, powers := [(26, 1), (49, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (37, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (40, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (43, 1), (50, 1)] }, { coefficient := 1, powers := [(3, 1), (25, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (31, 1), (56, 1)] }, { coefficient := 1, powers := [(3, 1), (34, 1), (50, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (31, 1), (43, 1)] }, { coefficient := 1, powers := [(6, 1), (34, 1), (40, 1)] }, { coefficient := 1, powers := [(9, 1), (20, 1), (56, 1)] }, { coefficient := 1, powers := [(9, 1), (25, 1), (43, 1)] }, { coefficient := 1, powers := [(9, 1), (34, 1), (37, 1)] }, { coefficient := 1, powers := [(13, 1), (20, 1), (50, 1)] }, { coefficient := 1, powers := [(13, 1), (25, 1), (40, 1)] }, { coefficient := 1, powers := [(13, 1), (31, 1), (37, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (39, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (42, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (49, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (49, 1)] }, { coefficient := 1, powers := [(8, 1), (36, 1), (42, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (58, 1)] }, { coefficient := 1, powers := [(12, 1), (30, 1), (49, 1)] }, { coefficient := 1, powers := [(12, 1), (36, 1), (39, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (55, 1)] }, { coefficient := 1, powers := [(19, 1), (30, 1), (42, 1)] }, { coefficient := 1, powers := [(19, 1), (33, 1), (39, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(40, 1)] }],
  [{ coefficient := 1, powers := [(42, 1)] }],
  [{ coefficient := 1, powers := [(56, 1)] }],
  [{ coefficient := 1, powers := [(58, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (66, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(30, 1)] }],
  [{ coefficient := 1, powers := [(59, 1)] }],
  [{ coefficient := 1, powers := [(60, 1), (67, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 52 → SparsePoly (Fin 69) := ![
  [{ coefficient := -1, powers := [(2, 1), (25, 1), (34, 1), (37, 1), (55, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(20, 1), (23, 1), (25, 1), (49, 1), (55, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (25, 1), (28, 1), (43, 1), (49, 1), (55, 1), (62, 1)] }, { coefficient := -1, powers := [(2, 1), (13, 1), (20, 1), (23, 1), (25, 1), (49, 1), (55, 1), (62, 1), (63, 1)] }, { coefficient := 1, powers := [(2, 1), (13, 1), (21, 1), (23, 1), (25, 1), (44, 1), (55, 1), (62, 1), (63, 1)] }, { coefficient := -1, powers := [(2, 1), (23, 1), (25, 1), (34, 1), (37, 1), (49, 1), (55, 1), (62, 1), (63, 1)] }, { coefficient := 1, powers := [(13, 1), (20, 1), (25, 1), (28, 1), (49, 1), (55, 1), (62, 1)] }, { coefficient := 1, powers := [(25, 2), (28, 1), (43, 1), (49, 1), (55, 1), (62, 1)] }, { coefficient := 1, powers := [(25, 1), (28, 1), (34, 1), (37, 1), (49, 1), (55, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(24, 1), (26, 1), (44, 1), (62, 1), (66, 1)] }, { coefficient := 1, powers := [(25, 1), (26, 1), (29, 1), (49, 1), (62, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (44, 1), (62, 1)] }, { coefficient := -1, powers := [(25, 1), (29, 1), (49, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(21, 1), (36, 1), (41, 1), (55, 1), (62, 1), (67, 1)] }, { coefficient := -1, powers := [(21, 1), (36, 1), (46, 1), (55, 1), (62, 1), (67, 1)] }, { coefficient := -1, powers := [(24, 1), (25, 1), (44, 1), (55, 1), (62, 2)] }, { coefficient := 1, powers := [(24, 1), (26, 1), (44, 1), (51, 1), (62, 2)] }, { coefficient := 1, powers := [(24, 1), (26, 1), (44, 1), (51, 1), (62, 1), (66, 1)] }, { coefficient := -1, powers := [(24, 1), (44, 1), (55, 1), (62, 1)] }, { coefficient := -1, powers := [(25, 1), (26, 1), (29, 1), (49, 1), (51, 1), (62, 2)] }, { coefficient := -1, powers := [(25, 1), (26, 1), (29, 1), (49, 1), (51, 1), (62, 1), (66, 1)] }, { coefficient := -1, powers := [(25, 1), (28, 1), (41, 1), (49, 1), (55, 1), (62, 1)] }, { coefficient := -1, powers := [(25, 1), (28, 1), (46, 1), (49, 1), (55, 1), (62, 1)] }, { coefficient := 1, powers := [(36, 1), (48, 1), (55, 1), (62, 1), (67, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (18, 1), (49, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(18, 1), (25, 1), (55, 1), (62, 1)] }, { coefficient := 1, powers := [(18, 1), (26, 1), (51, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (12, 1), (44, 1), (62, 1)] }, { coefficient := 1, powers := [(12, 1), (25, 1), (44, 1), (62, 1)] }, { coefficient := 1, powers := [(19, 1), (20, 1), (51, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (26, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (55, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (24, 1), (54, 1), (62, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (25, 1), (55, 1), (62, 2)] }],
  [{ coefficient := 1, powers := [(2, 1), (25, 1), (43, 1), (50, 1), (55, 1), (62, 1)] }, { coefficient := -1, powers := [(2, 1), (55, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (24, 1), (44, 1), (60, 1), (62, 1)] }, { coefficient := -1, powers := [(18, 1), (24, 1), (26, 1), (44, 1), (62, 2)] }, { coefficient := 1, powers := [(18, 1), (25, 1), (26, 1), (29, 1), (49, 1), (62, 2)] }],
  [{ coefficient := -1, powers := [(2, 1), (25, 1), (46, 1), (49, 1), (62, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (13, 1), (20, 1), (25, 1), (49, 1), (55, 1), (62, 1), (63, 1)] }, { coefficient := -1, powers := [(2, 1), (13, 1), (21, 1), (25, 1), (44, 1), (55, 1), (62, 1), (63, 1)] }, { coefficient := 1, powers := [(2, 1), (25, 1), (34, 1), (37, 1), (49, 1), (55, 1), (62, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (25, 2), (28, 1), (49, 1), (55, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (20, 1), (25, 1), (49, 1), (55, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (25, 1), (49, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(36, 1), (55, 1), (62, 1), (67, 1)] }],
  [{ coefficient := -1, powers := [(13, 1), (25, 1), (28, 1), (49, 1), (55, 1), (62, 1)] }, { coefficient := 1, powers := [(25, 1), (28, 1), (43, 1), (49, 1), (55, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(24, 1), (51, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (36, 1), (55, 1), (62, 1), (67, 1)] }, { coefficient := 1, powers := [(25, 1), (28, 1), (49, 1), (55, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (25, 1), (49, 1), (55, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (55, 1), (62, 1)] }, { coefficient := -1, powers := [(26, 1), (51, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (49, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(20, 1), (36, 1), (55, 1), (62, 1), (67, 1)] }],
  [{ coefficient := -1, powers := [(24, 1), (25, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(9, 1), (25, 1), (28, 1), (49, 1), (55, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (21, 1), (36, 1), (55, 1), (62, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (19, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (24, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (13, 1), (25, 1), (55, 1), (62, 1)] }, { coefficient := -1, powers := [(2, 1), (25, 1), (43, 1), (55, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(24, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (12, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (25, 1), (49, 1), (50, 1), (55, 1), (62, 1)] }, { coefficient := -1, powers := [(18, 1), (25, 1), (28, 1), (49, 1), (50, 1), (55, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (13, 1), (25, 1), (49, 1), (55, 1), (62, 1)] }, { coefficient := -1, powers := [(18, 1), (25, 1), (28, 1), (43, 1), (49, 1), (55, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (24, 1), (61, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (24, 1), (60, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (25, 1), (49, 1), (55, 1), (62, 1)] }, { coefficient := 1, powers := [(18, 1), (25, 1), (28, 1), (49, 1), (55, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(18, 1), (24, 1), (25, 1), (44, 1), (55, 1), (62, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (26, 1), (44, 1), (51, 1), (62, 1)] }, { coefficient := -1, powers := [(18, 1), (25, 1), (26, 1), (29, 1), (49, 1), (51, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(2, 1), (13, 1), (20, 1), (25, 1), (49, 1), (50, 1), (55, 1), (62, 1)] }, { coefficient := 1, powers := [(2, 1), (13, 1), (21, 1), (25, 1), (44, 1), (50, 1), (55, 1), (62, 1)] }, { coefficient := -1, powers := [(2, 1), (25, 1), (34, 1), (37, 1), (49, 1), (50, 1), (55, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (2, 1), (25, 1), (49, 1), (55, 1), (56, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 1), (18, 1), (25, 1), (28, 1), (49, 1), (55, 1), (56, 1), (62, 1)] }, { coefficient := -1, powers := [(2, 1), (6, 1), (25, 1), (34, 1), (49, 1), (55, 1), (62, 1)] }, { coefficient := -1, powers := [(2, 1), (13, 1), (18, 1), (20, 1), (25, 1), (28, 1), (49, 1), (55, 1), (62, 1), (63, 1)] }, { coefficient := 1, powers := [(2, 1), (13, 1), (18, 1), (21, 1), (25, 1), (28, 1), (44, 1), (55, 1), (62, 1), (63, 1)] }, { coefficient := -1, powers := [(2, 1), (18, 1), (25, 1), (28, 1), (34, 1), (37, 1), (49, 1), (55, 1), (62, 1), (63, 1)] }, { coefficient := -1, powers := [(6, 1), (18, 1), (25, 1), (28, 1), (34, 1), (49, 1), (55, 1), (62, 1)] }, { coefficient := -1, powers := [(13, 1), (18, 1), (25, 2), (28, 1), (49, 1), (55, 1), (62, 1)] }, { coefficient := -1, powers := [(17, 1), (20, 1), (25, 1), (28, 1), (49, 1), (55, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (8, 1), (36, 1), (62, 1)] }, { coefficient := -1, powers := [(2, 1), (26, 1), (44, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (3, 1), (25, 1), (31, 1), (49, 1), (55, 1), (62, 1)] }, { coefficient := -1, powers := [(2, 1), (9, 1), (20, 1), (25, 1), (49, 1), (55, 1), (62, 1)] }, { coefficient := 1, powers := [(2, 1), (20, 1), (25, 1), (49, 1), (50, 1), (55, 1), (62, 1)] }, { coefficient := -1, powers := [(3, 1), (18, 1), (25, 1), (28, 1), (31, 1), (49, 1), (55, 1), (62, 1)] }, { coefficient := 1, powers := [(18, 1), (20, 1), (25, 1), (28, 1), (49, 1), (50, 1), (55, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (5, 1), (33, 1), (62, 1)] }, { coefficient := -1, powers := [(2, 1), (21, 1), (51, 1), (62, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (25, 1), (62, 1)] }, { coefficient := 1, powers := [(18, 1), (20, 1), (24, 1), (51, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (24, 1), (26, 1), (44, 1), (62, 1)] }, { coefficient := -1, powers := [(12, 1), (25, 1), (26, 1), (29, 1), (49, 1), (62, 1)] }, { coefficient := -1, powers := [(18, 1), (24, 1), (26, 1), (44, 1), (51, 1), (62, 1)] }, { coefficient := 1, powers := [(18, 1), (25, 1), (26, 1), (29, 1), (49, 1), (51, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (5, 1), (61, 1), (62, 1)] }, { coefficient := 1, powers := [(0, 1), (12, 1), (44, 1), (48, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 1), (12, 1), (49, 1), (62, 1)] }, { coefficient := 1, powers := [(0, 1), (18, 1), (49, 1), (51, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 1), (19, 1), (48, 1), (51, 1), (62, 1)] }, { coefficient := -1, powers := [(12, 1), (25, 1), (44, 1), (48, 1), (62, 1)] }, { coefficient := -1, powers := [(19, 1), (20, 1), (48, 1), (51, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (2, 1), (25, 1), (37, 1), (49, 1), (55, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 1), (18, 1), (25, 1), (28, 1), (37, 1), (49, 1), (55, 1), (62, 1)] }, { coefficient := -1, powers := [(2, 1), (3, 1), (25, 2), (49, 1), (55, 1), (62, 1)] }, { coefficient := -1, powers := [(2, 1), (6, 1), (20, 1), (25, 1), (49, 1), (55, 1), (62, 1)] }, { coefficient := -2, powers := [(3, 1), (18, 1), (25, 2), (28, 1), (49, 1), (55, 1), (62, 1)] }, { coefficient := -1, powers := [(6, 1), (18, 1), (20, 1), (25, 1), (28, 1), (49, 1), (55, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (20, 1), (36, 1), (55, 1), (62, 1)] }, { coefficient := 1, powers := [(5, 1), (25, 1), (36, 1), (55, 1), (62, 1)] }]
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
    ¬ ∀ index : Fin 52,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component37.SelectedLeafB5_2_2_4_3.selectedHasNoCommonZero

end Krenn.Component37.SelectedLeafB5_2_2_4_3
