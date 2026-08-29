import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component37.SelectedLeafB5_0_6_5

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "ec4a88a02f63348eef0c055d3fef7530675f8fb48e2298835cf14af3f5a00d55"
def certificateSHA256 : String := "8e5b065b0597de1f7f3c3225854978dafda3f9654097f23ffe6dab13b5a4f7ca"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 56 → Fin 670 := ![
  17,
  151,
  167,
  168,
  171,
  175,
  176,
  178,
  179,
  180,
  183,
  184,
  280,
  294,
  295,
  296,
  297,
  300,
  301,
  302,
  308,
  310,
  313,
  315,
  316,
  317,
  340,
  343,
  411,
  424,
  433,
  435,
  446,
  447,
  450,
  453,
  476,
  478,
  480,
  482,
  499,
  591,
  602,
  627,
  629,
  646,
  655,
  657,
  658,
  660,
  661,
  662,
  663,
  666,
  667,
  669
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 56 → SparsePoly (Fin 68) := ![
  [{ coefficient := 1, powers := [(18, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (30, 1)] }, { coefficient := 1, powers := [(30, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (25, 1)] }, { coefficient := 1, powers := [(18, 1), (20, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (26, 1)] }, { coefficient := 1, powers := [(18, 1), (20, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (20, 1)] }, { coefficient := 1, powers := [(18, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (44, 1)] }, { coefficient := 1, powers := [(19, 1), (20, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (47, 1)] }, { coefficient := -1, powers := [(29, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (55, 1)] }, { coefficient := 1, powers := [(30, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (44, 1)] }, { coefficient := 1, powers := [(28, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(28, 1), (53, 1)] }, { coefficient := -1, powers := [(29, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (55, 1)] }, { coefficient := 1, powers := [(30, 1), (46, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (25, 1), (49, 1)] }, { coefficient := 1, powers := [(19, 1), (21, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1)] }, { coefficient := 1, powers := [(20, 1), (44, 1)] }, { coefficient := 1, powers := [(25, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (49, 1)] }, { coefficient := 1, powers := [(21, 1), (44, 1)] }, { coefficient := 1, powers := [(25, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (51, 1)] }, { coefficient := 1, powers := [(20, 1), (51, 1)] }, { coefficient := 1, powers := [(25, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (55, 1)] }, { coefficient := 1, powers := [(20, 1), (55, 1)] }, { coefficient := 1, powers := [(26, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (50, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (50, 1)] }, { coefficient := 1, powers := [(18, 1), (28, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (59, 1)] }, { coefficient := 1, powers := [(9, 1), (43, 1)] }, { coefficient := 1, powers := [(13, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (28, 1)] }, { coefficient := 1, powers := [(23, 1), (50, 1)] }, { coefficient := 1, powers := [(28, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (23, 1)] }, { coefficient := 1, powers := [(23, 1), (56, 1)] }, { coefficient := 1, powers := [(28, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (41, 1)] }, { coefficient := 1, powers := [(19, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(20, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(44, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1), (51, 1)] }, { coefficient := 1, powers := [(25, 1), (46, 1), (51, 1)] }, { coefficient := 1, powers := [(51, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1), (55, 1)] }, { coefficient := 1, powers := [(26, 1), (46, 1), (51, 1)] }, { coefficient := 1, powers := [(55, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (49, 1), (52, 1)] }, { coefficient := 1, powers := [(21, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(49, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (44, 1)] }, { coefficient := 1, powers := [(19, 1), (23, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (47, 1), (51, 1)] }, { coefficient := 1, powers := [(12, 1), (28, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (29, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (25, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (25, 1), (41, 1)] }, { coefficient := 1, powers := [(19, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1)] }, { coefficient := 1, powers := [(25, 1), (41, 1), (44, 1)] }, { coefficient := 1, powers := [(25, 1), (47, 1)] }, { coefficient := 1, powers := [(44, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (49, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1)] }, { coefficient := 1, powers := [(18, 1), (28, 1), (49, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (52, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (52, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (57, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (61, 1)] }, { coefficient := 1, powers := [(12, 1), (49, 1)] }, { coefficient := 1, powers := [(19, 1), (21, 1), (53, 1)] }, { coefficient := 1, powers := [(19, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (33, 1)] }, { coefficient := 1, powers := [(23, 1), (51, 1)] }, { coefficient := 1, powers := [(28, 1), (51, 1)] }, { coefficient := 1, powers := [(33, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (61, 1)] }, { coefficient := 1, powers := [(12, 1), (26, 1), (47, 1)] }, { coefficient := 1, powers := [(12, 1), (58, 1)] }, { coefficient := 1, powers := [(19, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (41, 1)] }, { coefficient := 1, powers := [(18, 1), (46, 1)] }, { coefficient := 1, powers := [(18, 1), (52, 1)] }, { coefficient := 1, powers := [(18, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1), (55, 1)] }, { coefficient := 1, powers := [(26, 1), (47, 1), (51, 1)] }, { coefficient := 1, powers := [(44, 1), (55, 1)] }, { coefficient := 1, powers := [(51, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (48, 1), (51, 1)] }, { coefficient := 1, powers := [(21, 1), (51, 1)] }, { coefficient := 1, powers := [(25, 1), (42, 1)] }, { coefficient := 1, powers := [(25, 1), (48, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (48, 1), (55, 1)] }, { coefficient := 1, powers := [(21, 1), (55, 1)] }, { coefficient := 1, powers := [(26, 1), (42, 1)] }, { coefficient := 1, powers := [(26, 1), (48, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (49, 1), (53, 1)] }, { coefficient := 1, powers := [(21, 1), (44, 1), (53, 1)] }, { coefficient := 1, powers := [(42, 1), (44, 1)] }, { coefficient := 1, powers := [(49, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (28, 1), (60, 1)] }, { coefficient := 1, powers := [(6, 1), (23, 1), (60, 1)] }, { coefficient := 1, powers := [(23, 1)] }, { coefficient := 1, powers := [(28, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (37, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (40, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (43, 1), (50, 1)] }, { coefficient := 1, powers := [(17, 1), (23, 1), (50, 1)] }, { coefficient := 1, powers := [(17, 1), (28, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1)] }, { coefficient := 1, powers := [(3, 1), (34, 1)] }, { coefficient := 1, powers := [(13, 1), (20, 1)] }, { coefficient := 1, powers := [(20, 1), (56, 1)] }, { coefficient := 1, powers := [(25, 1), (43, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (28, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (23, 1), (59, 1)] }, { coefficient := 1, powers := [(9, 1), (23, 1), (56, 1)] }, { coefficient := 1, powers := [(9, 1), (28, 1), (43, 1)] }, { coefficient := 1, powers := [(13, 1), (23, 1), (50, 1)] }, { coefficient := 1, powers := [(13, 1), (28, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (33, 1), (56, 1)] }, { coefficient := 1, powers := [(6, 1), (33, 1), (43, 1)] }, { coefficient := 1, powers := [(13, 1), (23, 1), (51, 1)] }, { coefficient := 1, powers := [(13, 1), (33, 1), (37, 1)] }, { coefficient := 1, powers := [(23, 1), (51, 1), (56, 1)] }, { coefficient := 1, powers := [(28, 1), (43, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (39, 1), (61, 1)] }, { coefficient := 1, powers := [(0, 1), (42, 1), (58, 1)] }, { coefficient := 1, powers := [(0, 1), (49, 1), (55, 1)] }, { coefficient := 1, powers := [(21, 1), (44, 1), (55, 1)] }, { coefficient := 1, powers := [(21, 1), (51, 1), (58, 1)] }, { coefficient := 1, powers := [(26, 1), (42, 1), (44, 1)] }, { coefficient := 1, powers := [(26, 1), (49, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (37, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (40, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (43, 1), (50, 1)] }, { coefficient := 1, powers := [(3, 1), (25, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (31, 1), (56, 1)] }, { coefficient := 1, powers := [(3, 1), (34, 1), (50, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (31, 1), (43, 1)] }, { coefficient := 1, powers := [(6, 1), (34, 1), (40, 1)] }, { coefficient := 1, powers := [(9, 1), (20, 1), (56, 1)] }, { coefficient := 1, powers := [(9, 1), (25, 1), (43, 1)] }, { coefficient := 1, powers := [(9, 1), (34, 1), (37, 1)] }, { coefficient := 1, powers := [(13, 1), (20, 1), (50, 1)] }, { coefficient := 1, powers := [(13, 1), (25, 1), (40, 1)] }, { coefficient := 1, powers := [(13, 1), (31, 1), (37, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (39, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (42, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (49, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (49, 1)] }, { coefficient := 1, powers := [(8, 1), (36, 1), (42, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (58, 1)] }, { coefficient := 1, powers := [(12, 1), (30, 1), (49, 1)] }, { coefficient := 1, powers := [(12, 1), (36, 1), (39, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (55, 1)] }, { coefficient := 1, powers := [(19, 1), (30, 1), (42, 1)] }, { coefficient := 1, powers := [(19, 1), (33, 1), (39, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(40, 1)] }],
  [{ coefficient := 1, powers := [(41, 1)] }],
  [{ coefficient := 1, powers := [(42, 1)] }],
  [{ coefficient := 1, powers := [(58, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (66, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(30, 1), (67, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 56 → SparsePoly (Fin 68) := ![
  [{ coefficient := 1, powers := [(0, 1), (8, 1), (23, 1), (33, 1), (43, 1), (49, 1), (63, 1)] }, { coefficient := -1, powers := [(8, 1), (20, 1), (23, 1), (33, 1), (43, 1), (49, 1), (63, 1)] }, { coefficient := 1, powers := [(8, 1), (20, 1), (23, 1), (33, 1), (49, 1), (56, 1), (63, 1)] }, { coefficient := 1, powers := [(8, 1), (23, 1), (25, 1), (33, 1), (43, 1), (49, 1), (63, 1)] }, { coefficient := 1, powers := [(8, 1), (23, 1), (33, 1), (34, 1), (37, 1), (49, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (8, 1), (17, 1), (28, 1), (33, 1), (49, 1), (63, 1), (67, 1)] }, { coefficient := 1, powers := [(8, 1), (13, 1), (20, 1), (23, 1), (49, 1), (51, 1), (60, 1), (67, 1)] }, { coefficient := 1, powers := [(8, 1), (13, 1), (20, 1), (28, 1), (49, 1), (51, 1), (60, 1), (67, 1)] }, { coefficient := -1, powers := [(8, 1), (17, 1), (20, 1), (28, 1), (33, 1), (49, 1), (63, 1), (67, 1)] }, { coefficient := 1, powers := [(8, 1), (20, 1), (33, 1), (49, 1), (56, 1), (67, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (34, 1), (37, 1), (49, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(36, 1), (39, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(24, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (20, 1), (21, 1), (26, 1), (28, 1), (46, 1), (52, 1), (63, 1)] }, { coefficient := 1, powers := [(2, 1), (20, 1), (21, 1), (26, 1), (28, 1), (52, 1), (62, 1), (63, 1)] }, { coefficient := 1, powers := [(2, 1), (21, 1), (26, 1), (28, 1), (62, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(24, 1), (44, 1), (55, 1), (62, 1)] }, { coefficient := 1, powers := [(24, 1), (47, 1), (55, 1)] }, { coefficient := -1, powers := [(30, 1), (49, 1), (51, 1), (62, 1)] }, { coefficient := -1, powers := [(33, 1), (39, 1), (44, 1), (62, 1)] }, { coefficient := -1, powers := [(33, 1), (39, 1), (47, 1)] }, { coefficient := -1, powers := [(36, 1), (39, 1), (51, 1), (62, 1)] }, { coefficient := -1, powers := [(36, 1), (39, 1), (51, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(33, 1), (39, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (18, 1), (20, 1), (21, 1), (26, 1), (51, 1), (52, 1), (62, 1), (63, 1)] }, { coefficient := -1, powers := [(2, 1), (18, 1), (21, 1), (26, 1), (51, 1), (62, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (18, 1), (20, 1), (46, 1), (49, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(18, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (19, 1), (20, 1), (21, 1), (26, 1), (46, 1), (52, 1), (63, 1)] }, { coefficient := -1, powers := [(2, 1), (19, 1), (20, 1), (21, 1), (26, 1), (52, 1), (62, 1), (63, 1)] }, { coefficient := -1, powers := [(2, 1), (19, 1), (21, 1), (26, 1), (62, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (18, 1), (20, 1), (49, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(30, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (24, 1), (55, 1), (62, 1)] }, { coefficient := 1, powers := [(18, 1), (33, 1), (39, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (20, 1), (26, 1), (46, 2), (51, 1), (52, 1)] }, { coefficient := 1, powers := [(2, 1), (26, 1), (46, 1), (51, 1), (62, 1)] }, { coefficient := 1, powers := [(18, 1), (30, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (30, 1), (49, 1), (62, 1)] }, { coefficient := 1, powers := [(18, 1), (36, 1), (39, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (20, 1), (21, 1), (44, 1), (52, 2), (62, 1)] }, { coefficient := 1, powers := [(2, 1), (21, 1), (44, 1), (52, 1), (62, 1)] }, { coefficient := 1, powers := [(2, 1), (46, 1), (49, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (8, 1), (33, 1), (43, 1), (49, 1), (63, 1)] }, { coefficient := 1, powers := [(8, 1), (20, 1), (33, 1), (43, 1), (49, 1), (63, 1)] }, { coefficient := -1, powers := [(8, 1), (20, 1), (33, 1), (49, 1), (56, 1), (63, 1)] }, { coefficient := -1, powers := [(8, 1), (25, 1), (33, 1), (43, 1), (49, 1), (63, 1)] }, { coefficient := -1, powers := [(8, 1), (33, 1), (34, 1), (37, 1), (49, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (25, 1), (33, 1), (49, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (8, 1), (17, 1), (33, 1), (49, 1), (63, 1)] }, { coefficient := -1, powers := [(8, 1), (13, 1), (20, 1), (49, 1), (51, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (17, 1), (20, 1), (33, 1), (49, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (9, 1), (20, 1), (49, 1), (51, 1), (60, 1)] }, { coefficient := -1, powers := [(8, 1), (31, 1), (49, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (20, 1), (21, 1), (23, 1), (26, 1), (51, 1), (52, 1), (62, 1), (63, 1)] }, { coefficient := 1, powers := [(2, 1), (21, 1), (23, 1), (26, 1), (51, 1), (62, 1), (63, 1)] }, { coefficient := 1, powers := [(20, 1), (33, 1), (39, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (20, 1), (21, 1), (52, 1), (55, 1), (62, 1)] }, { coefficient := -1, powers := [(2, 1), (21, 1), (55, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (20, 1), (26, 1), (44, 1), (46, 1), (48, 1), (52, 1)] }, { coefficient := -1, powers := [(2, 1), (20, 1), (26, 1), (46, 1), (49, 1), (52, 1)] }, { coefficient := 1, powers := [(2, 1), (26, 1), (44, 1), (48, 1), (62, 1)] }, { coefficient := -1, powers := [(2, 1), (26, 1), (49, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (20, 1), (44, 1), (48, 1), (52, 1)] }, { coefficient := 1, powers := [(2, 1), (20, 1), (49, 1), (52, 1)] }, { coefficient := -1, powers := [(2, 1), (49, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (20, 1), (46, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (20, 1), (21, 1), (26, 1), (51, 1), (52, 1), (62, 1), (63, 1)] }, { coefficient := -1, powers := [(2, 1), (21, 1), (26, 1), (51, 1), (62, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (20, 1), (21, 1), (26, 1), (46, 1), (52, 1), (63, 1)] }, { coefficient := -1, powers := [(2, 1), (20, 1), (21, 1), (26, 1), (52, 1), (62, 1), (63, 1)] }, { coefficient := -1, powers := [(2, 1), (21, 1), (26, 1), (62, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(24, 1), (55, 1)] }, { coefficient := 1, powers := [(33, 1), (39, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (20, 1), (26, 1), (46, 1), (48, 1), (51, 1), (52, 1)] }, { coefficient := -1, powers := [(2, 1), (26, 1), (48, 1), (51, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(55, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (20, 1), (49, 1), (55, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(30, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (20, 1), (49, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(24, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (20, 1), (23, 1), (49, 1), (55, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (20, 1), (21, 1), (52, 1), (62, 1)] }, { coefficient := 1, powers := [(2, 1), (20, 1), (48, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (20, 1), (26, 1), (44, 1), (46, 2), (52, 1)] }, { coefficient := 1, powers := [(2, 1), (20, 1), (26, 1), (46, 1), (47, 1), (52, 1)] }, { coefficient := -1, powers := [(2, 1), (26, 1), (44, 1), (46, 1), (62, 1)] }, { coefficient := 1, powers := [(2, 1), (26, 1), (47, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (20, 1), (44, 1), (46, 1), (52, 1)] }, { coefficient := -1, powers := [(2, 1), (20, 1), (47, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(18, 1), (30, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (20, 1), (49, 1), (51, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (8, 1), (33, 1), (49, 1), (63, 1)] }, { coefficient := -1, powers := [(8, 1), (20, 1), (33, 1), (49, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (33, 1), (49, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (20, 1), (49, 1), (51, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (31, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (33, 1), (49, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(2, 1), (20, 1), (21, 1), (47, 1), (52, 1), (55, 1)] }, { coefficient := -1, powers := [(2, 1), (39, 1), (61, 1)] }, { coefficient := -1, powers := [(2, 1), (49, 1), (55, 1)] }, { coefficient := -1, powers := [(18, 1), (24, 1), (44, 1), (55, 1)] }, { coefficient := -1, powers := [(18, 1), (30, 1), (49, 1), (51, 1)] }, { coefficient := -1, powers := [(18, 1), (33, 1), (39, 1), (44, 1)] }, { coefficient := -1, powers := [(18, 1), (36, 1), (39, 1), (51, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (8, 1), (33, 1), (37, 1), (49, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (20, 1), (21, 1), (26, 1), (44, 1), (51, 1), (52, 2), (62, 1)] }, { coefficient := 1, powers := [(2, 1), (20, 1), (21, 1), (26, 1), (46, 1), (47, 1), (51, 1), (52, 1)] }, { coefficient := 1, powers := [(2, 1), (20, 1), (21, 1), (26, 1), (47, 1), (51, 1), (52, 1), (62, 1)] }, { coefficient := 1, powers := [(2, 1), (20, 1), (49, 1), (52, 1), (55, 1)] }, { coefficient := 1, powers := [(2, 1), (21, 1), (26, 1), (44, 1), (51, 1), (52, 1), (62, 1)] }, { coefficient := 1, powers := [(2, 1), (21, 1), (26, 1), (47, 1), (51, 1), (62, 1)] }, { coefficient := 1, powers := [(8, 1), (20, 1), (33, 1), (37, 1), (49, 1), (59, 1)] }, { coefficient := 1, powers := [(8, 1), (20, 1), (33, 1), (49, 1), (50, 1), (56, 1)] }, { coefficient := 1, powers := [(8, 1), (25, 1), (33, 1), (43, 1), (49, 1), (50, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (34, 1), (37, 1), (49, 1), (50, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (2, 1), (8, 1), (33, 1), (49, 1), (56, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (8, 1), (17, 1), (28, 1), (30, 1), (33, 1), (49, 1), (63, 1), (67, 1)] }, { coefficient := 1, powers := [(0, 1), (8, 1), (18, 1), (28, 1), (33, 1), (43, 1), (49, 1), (63, 1)] }, { coefficient := 1, powers := [(0, 1), (8, 1), (33, 1), (49, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (8, 1), (20, 1), (33, 1), (49, 1), (56, 1), (63, 1)] }, { coefficient := 1, powers := [(6, 1), (8, 1), (33, 1), (34, 1), (49, 1)] }, { coefficient := -1, powers := [(8, 1), (13, 1), (20, 1), (23, 1), (30, 1), (49, 1), (51, 1), (60, 1), (67, 1)] }, { coefficient := -1, powers := [(8, 1), (13, 1), (20, 1), (28, 1), (30, 1), (49, 1), (51, 1), (60, 1), (67, 1)] }, { coefficient := 1, powers := [(8, 1), (17, 1), (20, 1), (28, 1), (30, 1), (33, 1), (49, 1), (63, 1), (67, 1)] }, { coefficient := -1, powers := [(8, 1), (18, 1), (20, 1), (28, 1), (33, 1), (43, 1), (49, 1), (63, 1)] }, { coefficient := 1, powers := [(8, 1), (18, 1), (20, 1), (28, 1), (33, 1), (49, 1), (56, 1), (63, 1)] }, { coefficient := 1, powers := [(8, 1), (18, 1), (25, 1), (28, 1), (33, 1), (43, 1), (49, 1), (63, 1)] }, { coefficient := 1, powers := [(8, 1), (18, 1), (28, 1), (33, 1), (34, 1), (37, 1), (49, 1), (63, 1)] }, { coefficient := -1, powers := [(8, 1), (20, 1), (30, 1), (33, 1), (49, 1), (56, 1), (67, 1)] }, { coefficient := -1, powers := [(8, 1), (30, 1), (33, 1), (34, 1), (37, 1), (49, 1), (67, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (18, 1), (20, 1), (23, 1), (49, 1), (55, 1), (63, 1)] }, { coefficient := -1, powers := [(2, 1), (19, 1), (20, 1), (21, 1), (23, 1), (26, 1), (51, 1), (52, 1), (62, 1), (63, 1)] }, { coefficient := -1, powers := [(2, 1), (19, 1), (21, 1), (23, 1), (26, 1), (51, 1), (62, 1), (63, 1)] }, { coefficient := 1, powers := [(2, 1), (20, 1), (25, 1), (26, 1), (44, 1), (46, 1), (48, 1), (51, 1), (52, 1)] }, { coefficient := 1, powers := [(2, 1), (25, 1), (26, 1), (44, 1), (48, 1), (51, 1), (62, 1)] }, { coefficient := -1, powers := [(19, 1), (20, 1), (33, 1), (39, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (25, 1), (55, 1)] }, { coefficient := -1, powers := [(19, 1), (25, 1), (33, 1), (39, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (2, 1), (58, 1), (62, 1)] }, { coefficient := 1, powers := [(2, 1), (20, 1), (25, 1), (26, 1), (44, 1), (46, 2), (52, 1)] }, { coefficient := -1, powers := [(2, 1), (20, 1), (25, 1), (26, 1), (46, 1), (47, 1), (52, 1)] }, { coefficient := -1, powers := [(2, 1), (20, 1), (26, 1), (44, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(2, 1), (20, 1), (26, 1), (47, 1), (52, 1)] }, { coefficient := 1, powers := [(2, 1), (25, 1), (26, 1), (44, 1), (46, 1), (62, 1)] }, { coefficient := -1, powers := [(2, 1), (25, 1), (26, 1), (47, 1), (62, 1)] }, { coefficient := -1, powers := [(2, 1), (26, 1), (44, 1), (62, 1)] }, { coefficient := 1, powers := [(2, 1), (58, 1)] }, { coefficient := 1, powers := [(8, 1), (36, 1)] }, { coefficient := 1, powers := [(18, 1), (30, 1), (44, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (20, 1), (21, 1), (51, 1), (52, 1), (62, 1)] }, { coefficient := -1, powers := [(2, 1), (20, 1), (48, 1), (51, 1), (52, 1)] }, { coefficient := -1, powers := [(2, 1), (21, 1), (51, 1), (62, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (36, 1), (39, 1)] }, { coefficient := 1, powers := [(18, 1), (36, 1), (39, 1), (51, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (8, 1), (9, 1), (17, 1), (28, 1), (33, 1), (49, 1), (63, 1)] }, { coefficient := -1, powers := [(8, 1), (9, 1), (13, 1), (20, 1), (23, 1), (49, 1), (51, 1), (60, 1)] }, { coefficient := -1, powers := [(8, 1), (9, 1), (13, 1), (20, 1), (28, 1), (49, 1), (51, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (9, 1), (17, 1), (20, 1), (28, 1), (33, 1), (49, 1), (63, 1)] }, { coefficient := -1, powers := [(8, 1), (9, 1), (20, 1), (33, 1), (49, 1), (56, 1)] }, { coefficient := -1, powers := [(8, 1), (9, 1), (33, 1), (34, 1), (37, 1), (49, 1)] }]
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
    (values : Fin 68 → R) :
    ¬ ∀ index : Fin 56,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component37.SelectedLeafB5_0_6_5.selectedHasNoCommonZero

end Krenn.Component37.SelectedLeafB5_0_6_5
