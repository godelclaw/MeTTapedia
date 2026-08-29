import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component37.SelectedLeafB5_3_2_4_3

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "836ea87b8e5da3b9949a80bc651ea33412d9fd64e703cf5a8cc5d0edb02f5c08"
def certificateSHA256 : String := "49fc26f355dfec8baed5825104890709367c6a239173633fb1746a478edb10c6"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 72 → Fin 673 := ![
  7,
  13,
  14,
  17,
  24,
  167,
  168,
  175,
  179,
  181,
  183,
  256,
  257,
  279,
  294,
  295,
  296,
  297,
  298,
  299,
  301,
  302,
  307,
  311,
  315,
  356,
  370,
  406,
  410,
  425,
  426,
  430,
  432,
  438,
  445,
  450,
  451,
  453,
  454,
  455,
  466,
  478,
  479,
  480,
  541,
  542,
  566,
  580,
  596,
  602,
  603,
  605,
  606,
  607,
  645,
  646,
  648,
  655,
  656,
  657,
  658,
  659,
  661,
  663,
  664,
  666,
  667,
  668,
  669,
  670,
  671,
  672
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 72 → SparsePoly (Fin 70) := ![
  [{ coefficient := 1, powers := [(8, 1), (32, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (22, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (25, 1)] }, { coefficient := 1, powers := [(18, 1), (20, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (26, 1)] }, { coefficient := 1, powers := [(18, 1), (20, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (20, 1)] }, { coefficient := 1, powers := [(18, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (55, 1)] }, { coefficient := 1, powers := [(30, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (54, 1)] }, { coefficient := 1, powers := [(30, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(28, 1), (53, 1)] }, { coefficient := -1, powers := [(29, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (25, 1), (46, 1)] }, { coefficient := 1, powers := [(18, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (25, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (25, 1), (44, 1)] }, { coefficient := 1, powers := [(19, 1), (20, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1)] }, { coefficient := 1, powers := [(20, 1), (44, 1)] }, { coefficient := 1, powers := [(25, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (49, 1)] }, { coefficient := 1, powers := [(21, 1), (44, 1)] }, { coefficient := 1, powers := [(25, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (51, 1)] }, { coefficient := 1, powers := [(20, 1), (51, 1)] }, { coefficient := 1, powers := [(25, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (55, 1)] }, { coefficient := 1, powers := [(20, 1), (55, 1)] }, { coefficient := 1, powers := [(26, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (46, 1)] }, { coefficient := 1, powers := [(4, 1), (35, 1)] }, { coefficient := 1, powers := [(15, 1), (22, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (52, 1)] }, { coefficient := 1, powers := [(7, 1), (32, 1)] }, { coefficient := 1, powers := [(10, 1), (27, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (59, 1)] }, { coefficient := 1, powers := [(9, 1), (43, 1)] }, { coefficient := 1, powers := [(13, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (28, 1)] }, { coefficient := 1, powers := [(23, 1), (50, 1)] }, { coefficient := 1, powers := [(28, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (46, 1)] }, { coefficient := 1, powers := [(12, 1), (57, 1)] }, { coefficient := 1, powers := [(18, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (52, 1)] }, { coefficient := 1, powers := [(24, 1), (57, 1)] }, { coefficient := 1, powers := [(29, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1), (51, 1)] }, { coefficient := 1, powers := [(25, 1), (46, 1), (51, 1)] }, { coefficient := 1, powers := [(51, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (25, 1), (60, 1)] }, { coefficient := 1, powers := [(18, 1), (21, 1)] }, { coefficient := 1, powers := [(18, 1), (25, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (22, 1), (61, 1)] }, { coefficient := 1, powers := [(12, 1), (22, 1), (58, 1)] }, { coefficient := 1, powers := [(19, 1), (22, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (20, 1), (50, 1)] }, { coefficient := 1, powers := [(18, 1), (25, 1), (40, 1)] }, { coefficient := 1, powers := [(18, 1), (31, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (25, 1), (41, 1)] }, { coefficient := 1, powers := [(18, 1), (25, 1), (46, 1)] }, { coefficient := 1, powers := [(18, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (48, 1)] }, { coefficient := 1, powers := [(6, 1), (21, 1), (60, 1)] }, { coefficient := 1, powers := [(21, 1)] }, { coefficient := 1, powers := [(25, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (53, 1)] }, { coefficient := 1, powers := [(20, 1), (51, 1), (57, 1)] }, { coefficient := 1, powers := [(20, 1), (53, 1)] }, { coefficient := 1, powers := [(51, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (46, 1)] }, { coefficient := 1, powers := [(18, 1), (28, 1), (41, 1)] }, { coefficient := 1, powers := [(18, 1), (28, 1), (46, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (48, 1)] }, { coefficient := 1, powers := [(5, 1), (28, 1), (60, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1)] }, { coefficient := 1, powers := [(18, 1), (28, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1)] }, { coefficient := 1, powers := [(12, 1), (30, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (60, 1)] }, { coefficient := 1, powers := [(18, 1), (21, 1), (52, 1)] }, { coefficient := 1, powers := [(18, 1), (21, 1), (57, 1)] }, { coefficient := 1, powers := [(18, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (61, 1)] }, { coefficient := 1, powers := [(12, 1), (26, 1), (47, 1)] }, { coefficient := 1, powers := [(12, 1), (58, 1)] }, { coefficient := 1, powers := [(19, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (20, 1)] }, { coefficient := 1, powers := [(18, 1), (20, 1), (56, 1)] }, { coefficient := 1, powers := [(18, 1), (25, 1), (43, 1)] }, { coefficient := 1, powers := [(18, 1), (34, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (41, 1)] }, { coefficient := 1, powers := [(18, 1), (46, 1)] }, { coefficient := 1, powers := [(18, 1), (52, 1)] }, { coefficient := 1, powers := [(18, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (55, 1)] }, { coefficient := 1, powers := [(30, 1), (42, 1)] }, { coefficient := 1, powers := [(30, 1), (48, 1), (51, 1)] }, { coefficient := 1, powers := [(33, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (41, 1)] }, { coefficient := 1, powers := [(29, 1), (46, 1)] }, { coefficient := 1, powers := [(29, 1), (52, 1)] }, { coefficient := 1, powers := [(29, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1), (54, 1)] }, { coefficient := 1, powers := [(20, 1), (44, 1), (54, 1)] }, { coefficient := 1, powers := [(20, 1), (58, 1)] }, { coefficient := 1, powers := [(26, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (48, 1), (51, 1)] }, { coefficient := 1, powers := [(21, 1), (51, 1)] }, { coefficient := 1, powers := [(25, 1), (42, 1)] }, { coefficient := 1, powers := [(25, 1), (48, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (48, 1), (52, 1)] }, { coefficient := 1, powers := [(21, 1), (52, 1)] }, { coefficient := 1, powers := [(21, 1), (57, 1)] }, { coefficient := 1, powers := [(48, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (48, 1), (55, 1)] }, { coefficient := 1, powers := [(21, 1), (55, 1)] }, { coefficient := 1, powers := [(26, 1), (42, 1)] }, { coefficient := 1, powers := [(26, 1), (48, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (20, 1), (61, 1)] }, { coefficient := 1, powers := [(12, 1), (20, 1), (58, 1)] }, { coefficient := 1, powers := [(12, 1), (26, 1), (44, 1)] }, { coefficient := 1, powers := [(19, 1), (20, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (22, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (46, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(18, 1), (22, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (44, 1), (54, 1)] }, { coefficient := 1, powers := [(24, 1), (58, 1)] }, { coefficient := 1, powers := [(30, 1), (49, 1)] }, { coefficient := 1, powers := [(36, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1)] }, { coefficient := 1, powers := [(6, 1), (60, 1)] }, { coefficient := 1, powers := [(25, 1), (41, 1)] }, { coefficient := 1, powers := [(25, 1), (46, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (48, 1), (52, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (60, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (52, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (57, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1)] }, { coefficient := 1, powers := [(3, 1), (34, 1)] }, { coefficient := 1, powers := [(13, 1), (20, 1)] }, { coefficient := 1, powers := [(20, 1), (56, 1)] }, { coefficient := 1, powers := [(25, 1), (43, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (50, 1)] }, { coefficient := 1, powers := [(6, 1), (31, 1)] }, { coefficient := 1, powers := [(9, 1), (25, 1)] }, { coefficient := 1, powers := [(20, 1), (50, 1)] }, { coefficient := 1, powers := [(25, 1), (40, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (52, 1)] }, { coefficient := 1, powers := [(22, 1), (57, 1)] }, { coefficient := 1, powers := [(27, 1), (41, 1)] }, { coefficient := 1, powers := [(27, 1), (46, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1)] }, { coefficient := 1, powers := [(35, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (37, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1)] }, { coefficient := 1, powers := [(3, 1), (25, 1), (60, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1), (60, 1)] }, { coefficient := 1, powers := [(20, 1)] }, { coefficient := 1, powers := [(25, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (37, 1), (61, 1)] }, { coefficient := 1, powers := [(0, 1), (44, 1), (51, 1)] }, { coefficient := 1, powers := [(3, 1), (25, 1), (61, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1), (61, 1)] }, { coefficient := 1, powers := [(20, 1), (44, 1), (51, 1)] }, { coefficient := 1, powers := [(25, 1), (44, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (38, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (41, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(41, 1)] }, { coefficient := 1, powers := [(46, 1)] }, { coefficient := 1, powers := [(52, 1)] }, { coefficient := 1, powers := [(57, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (39, 1), (61, 1)] }, { coefficient := 1, powers := [(0, 1), (42, 1), (58, 1)] }, { coefficient := 1, powers := [(0, 1), (49, 1), (55, 1)] }, { coefficient := 1, powers := [(21, 1), (44, 1), (55, 1)] }, { coefficient := 1, powers := [(21, 1), (51, 1), (58, 1)] }, { coefficient := 1, powers := [(26, 1), (42, 1), (44, 1)] }, { coefficient := 1, powers := [(26, 1), (49, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (41, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (41, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (46, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (52, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (37, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (40, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (43, 1), (50, 1)] }, { coefficient := 1, powers := [(3, 1), (25, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (31, 1), (56, 1)] }, { coefficient := 1, powers := [(3, 1), (34, 1), (50, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (31, 1), (43, 1)] }, { coefficient := 1, powers := [(6, 1), (34, 1), (40, 1)] }, { coefficient := 1, powers := [(9, 1), (20, 1), (56, 1)] }, { coefficient := 1, powers := [(9, 1), (25, 1), (43, 1)] }, { coefficient := 1, powers := [(9, 1), (34, 1), (37, 1)] }, { coefficient := 1, powers := [(13, 1), (20, 1), (50, 1)] }, { coefficient := 1, powers := [(13, 1), (25, 1), (40, 1)] }, { coefficient := 1, powers := [(13, 1), (31, 1), (37, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1), (38, 1), (60, 1)] }, { coefficient := 1, powers := [(1, 1), (41, 1), (57, 1)] }, { coefficient := 1, powers := [(1, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(4, 1), (27, 1), (60, 1)] }, { coefficient := 1, powers := [(4, 1), (32, 1), (57, 1)] }, { coefficient := 1, powers := [(4, 1), (35, 1), (52, 1)] }, { coefficient := 1, powers := [(7, 1), (22, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (32, 1), (46, 1)] }, { coefficient := 1, powers := [(7, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(10, 1), (22, 1), (57, 1)] }, { coefficient := 1, powers := [(10, 1), (27, 1), (46, 1)] }, { coefficient := 1, powers := [(10, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(15, 1), (22, 1), (52, 1)] }, { coefficient := 1, powers := [(15, 1), (27, 1), (41, 1)] }, { coefficient := 1, powers := [(15, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (39, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (42, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (49, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (49, 1)] }, { coefficient := 1, powers := [(8, 1), (36, 1), (42, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (58, 1)] }, { coefficient := 1, powers := [(12, 1), (30, 1), (49, 1)] }, { coefficient := 1, powers := [(12, 1), (36, 1), (39, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (55, 1)] }, { coefficient := 1, powers := [(19, 1), (30, 1), (42, 1)] }, { coefficient := 1, powers := [(19, 1), (33, 1), (39, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1)] }],
  [{ coefficient := 1, powers := [(40, 1)] }],
  [{ coefficient := 1, powers := [(42, 1), (65, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(56, 1)] }],
  [{ coefficient := 1, powers := [(58, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (67, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(27, 1)] }],
  [{ coefficient := 1, powers := [(30, 1)] }],
  [{ coefficient := 1, powers := [(59, 1)] }],
  [{ coefficient := 1, powers := [(60, 1), (68, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(61, 1), (69, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 72 → SparsePoly (Fin 70) := ![
  [{ coefficient := -1, powers := [(4, 1), (20, 1), (36, 1), (42, 1), (57, 1), (62, 1)] }, { coefficient := -1, powers := [(4, 1), (25, 1), (36, 1), (42, 1), (57, 1), (62, 1)] }, { coefficient := 1, powers := [(7, 1), (20, 1), (36, 1), (42, 1), (46, 1), (62, 1)] }, { coefficient := 1, powers := [(7, 1), (25, 1), (36, 1), (42, 1), (46, 1), (62, 1)] }, { coefficient := 1, powers := [(10, 1), (20, 1), (36, 1), (38, 1), (42, 1), (62, 1)] }, { coefficient := 1, powers := [(10, 1), (25, 1), (36, 1), (38, 1), (42, 1), (62, 1)] }, { coefficient := -1, powers := [(15, 1), (20, 1), (36, 1), (38, 1), (42, 1), (62, 1)] }, { coefficient := -1, powers := [(15, 1), (25, 1), (36, 1), (38, 1), (42, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (21, 1), (23, 1), (26, 1), (44, 1), (53, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (20, 1), (36, 1), (42, 1), (54, 1), (62, 1)] }, { coefficient := 1, powers := [(7, 1), (25, 1), (36, 1), (42, 1), (54, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (21, 1), (26, 1), (28, 1), (43, 1), (44, 1), (53, 1), (62, 1)] }, { coefficient := -1, powers := [(13, 1), (20, 1), (21, 1), (26, 1), (28, 1), (44, 1), (53, 1), (62, 1)] }, { coefficient := -1, powers := [(21, 1), (25, 1), (26, 1), (28, 1), (43, 1), (44, 1), (53, 1), (62, 1)] }, { coefficient := -1, powers := [(21, 1), (26, 1), (28, 1), (34, 1), (37, 1), (44, 1), (53, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(10, 1), (19, 1), (20, 1), (36, 1), (42, 1), (52, 1), (62, 1), (69, 1)] }, { coefficient := -1, powers := [(10, 1), (19, 1), (25, 1), (36, 1), (42, 1), (52, 1), (62, 1), (69, 1)] }],
  [{ coefficient := -1, powers := [(24, 1), (26, 1), (44, 1), (57, 1), (62, 1)] }, { coefficient := -1, powers := [(24, 1), (26, 1), (44, 1), (62, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (44, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (26, 1), (29, 1), (44, 1), (48, 1), (51, 1), (62, 2)] }, { coefficient := 1, powers := [(21, 1), (26, 1), (28, 1), (41, 1), (44, 1), (53, 1), (62, 1)] }, { coefficient := 1, powers := [(21, 1), (26, 1), (28, 1), (44, 1), (46, 1), (53, 1), (62, 1)] }, { coefficient := -1, powers := [(21, 1), (36, 1), (41, 1), (55, 1), (62, 1), (68, 1)] }, { coefficient := -1, powers := [(21, 1), (36, 1), (46, 1), (55, 1), (62, 1), (68, 1)] }, { coefficient := 2, powers := [(24, 1), (26, 1), (44, 1), (51, 1), (62, 2)] }, { coefficient := 1, powers := [(24, 1), (26, 1), (44, 1), (51, 1), (62, 1), (67, 1)] }, { coefficient := -1, powers := [(24, 1), (44, 1), (55, 1), (62, 1)] }, { coefficient := 1, powers := [(36, 1), (48, 1), (55, 1), (62, 1), (68, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (18, 1), (49, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (12, 1), (44, 1), (62, 1)] }, { coefficient := 1, powers := [(12, 1), (25, 1), (44, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (5, 1), (26, 1), (44, 1), (60, 1), (62, 1)] }, { coefficient := 1, powers := [(0, 1), (18, 1), (26, 1), (44, 1), (48, 1), (62, 1)] }, { coefficient := -1, powers := [(18, 1), (21, 1), (26, 1), (44, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(24, 1), (26, 1), (44, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (26, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (55, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (24, 1), (54, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (55, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (18, 1), (26, 1), (29, 1), (44, 1), (48, 1), (62, 2)] }, { coefficient := 1, powers := [(2, 1), (26, 1), (44, 2), (48, 1), (53, 1), (60, 1), (62, 1), (69, 1)] }, { coefficient := -1, powers := [(2, 1), (48, 1), (49, 1), (55, 1), (62, 1), (65, 1)] }, { coefficient := -1, powers := [(5, 1), (36, 1), (48, 1), (55, 1), (62, 1), (65, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (44, 1), (60, 1), (62, 1)] }, { coefficient := 1, powers := [(8, 1), (36, 1), (42, 1), (44, 1), (60, 1), (62, 1), (69, 1)] }, { coefficient := -2, powers := [(18, 1), (24, 1), (26, 1), (44, 1), (62, 2)] }, { coefficient := -1, powers := [(19, 1), (24, 1), (48, 1), (55, 1), (62, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (48, 1), (49, 1), (51, 1), (62, 1), (65, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1), (48, 1), (51, 1), (62, 1), (65, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1), (62, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (48, 1), (51, 1), (62, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (20, 1), (36, 1), (42, 1), (52, 1), (62, 1)] }, { coefficient := -1, powers := [(8, 1), (25, 1), (36, 1), (42, 1), (52, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (20, 1), (36, 1), (42, 1), (46, 1), (62, 1)] }, { coefficient := -1, powers := [(8, 1), (25, 1), (36, 1), (42, 1), (46, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(18, 1), (21, 1), (25, 1), (26, 1), (28, 1), (44, 1), (53, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(17, 1), (20, 1), (21, 1), (26, 1), (44, 1), (53, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (25, 1), (26, 1), (44, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (18, 1), (26, 1), (44, 1), (51, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (21, 1), (26, 1), (44, 1), (62, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(26, 1), (28, 1), (44, 1), (53, 1), (62, 1)] }, { coefficient := -1, powers := [(36, 1), (55, 1), (62, 1), (68, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (20, 1), (36, 1), (42, 1), (52, 1), (62, 1), (69, 1)] }, { coefficient := 1, powers := [(10, 1), (25, 1), (36, 1), (42, 1), (52, 1), (62, 1), (69, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (21, 1), (26, 1), (28, 1), (44, 1), (53, 1), (62, 1)] }, { coefficient := -1, powers := [(21, 1), (26, 1), (28, 1), (43, 1), (44, 1), (53, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(21, 1), (26, 1), (28, 1), (44, 1), (53, 1), (62, 1)] }, { coefficient := 1, powers := [(21, 1), (36, 1), (55, 1), (62, 1), (68, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (26, 1), (44, 1), (51, 1), (62, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (24, 1), (26, 1), (44, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(21, 1), (26, 1), (44, 1), (51, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (26, 1), (44, 1), (53, 1), (62, 1)] }, { coefficient := -1, powers := [(20, 1), (26, 1), (44, 1), (53, 1), (62, 1)] }, { coefficient := -1, powers := [(25, 1), (26, 1), (44, 1), (53, 1), (62, 1)] }, { coefficient := 1, powers := [(26, 1), (44, 1), (51, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (49, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (26, 1), (28, 1), (44, 1), (53, 1), (62, 1)] }, { coefficient := -1, powers := [(20, 1), (36, 1), (55, 1), (62, 1), (68, 1)] }, { coefficient := -1, powers := [(26, 1), (28, 1), (44, 1), (51, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(24, 1), (25, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (21, 1), (26, 1), (28, 1), (44, 1), (53, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(20, 1), (21, 1), (26, 1), (28, 1), (44, 1), (53, 1), (62, 1)] }, { coefficient := 1, powers := [(20, 1), (21, 1), (36, 1), (55, 1), (62, 1), (68, 1)] }, { coefficient := 1, powers := [(21, 1), (26, 1), (28, 1), (44, 1), (51, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (19, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (18, 1), (21, 1), (26, 1), (44, 1), (51, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (24, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (26, 1), (44, 1), (62, 1), (67, 1)] }, { coefficient := 1, powers := [(2, 1), (49, 1), (55, 1), (62, 1), (65, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1), (55, 1), (62, 1), (65, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (55, 1), (62, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (26, 1), (44, 1), (51, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (49, 1), (51, 1), (62, 1), (65, 1)] }, { coefficient := -1, powers := [(5, 1), (36, 1), (51, 1), (62, 1), (65, 1)] }, { coefficient := -1, powers := [(19, 1), (24, 1), (51, 1), (62, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(24, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (20, 1), (36, 1), (42, 1), (62, 1)] }, { coefficient := -1, powers := [(7, 1), (25, 1), (36, 1), (42, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (12, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (21, 1), (26, 1), (44, 1), (51, 1), (62, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (26, 1), (44, 1), (51, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (21, 1), (26, 1), (28, 1), (44, 1), (50, 1), (53, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (21, 1), (26, 1), (28, 1), (43, 1), (44, 1), (53, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (10, 1), (20, 1), (36, 1), (42, 1), (62, 1)] }, { coefficient := -1, powers := [(8, 1), (10, 1), (25, 1), (36, 1), (42, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (26, 1), (44, 1), (48, 1), (53, 1), (61, 1), (62, 1), (69, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (61, 1), (62, 1)] }, { coefficient := 1, powers := [(8, 1), (36, 1), (42, 1), (61, 1), (62, 1), (69, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (26, 1), (44, 1), (48, 1), (53, 1), (60, 1), (62, 1), (69, 1)] }, { coefficient := -1, powers := [(8, 1), (24, 1), (60, 1), (62, 1)] }, { coefficient := -1, powers := [(8, 1), (36, 1), (42, 1), (60, 1), (62, 1), (69, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (21, 1), (26, 1), (44, 1), (51, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (21, 1), (26, 1), (44, 1), (51, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(18, 1), (21, 1), (26, 1), (28, 1), (44, 1), (53, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (20, 1), (36, 1), (42, 1), (62, 1)] }, { coefficient := 1, powers := [(8, 1), (25, 1), (36, 1), (42, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (18, 1), (26, 1), (29, 1), (44, 1), (48, 1), (51, 1), (62, 1)] }, { coefficient := 2, powers := [(18, 1), (24, 1), (26, 1), (44, 1), (51, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(8, 1), (20, 1), (36, 1), (38, 1), (42, 1), (60, 1), (62, 1)] }, { coefficient := -1, powers := [(8, 1), (20, 1), (36, 1), (41, 1), (42, 1), (57, 1), (62, 1)] }, { coefficient := 1, powers := [(8, 1), (20, 1), (36, 1), (42, 1), (46, 1), (52, 1), (62, 1)] }, { coefficient := -1, powers := [(8, 1), (25, 1), (36, 1), (38, 1), (42, 1), (60, 1), (62, 1)] }, { coefficient := -1, powers := [(8, 1), (25, 1), (36, 1), (41, 1), (42, 1), (57, 1), (62, 1)] }, { coefficient := 1, powers := [(8, 1), (25, 1), (36, 1), (42, 1), (46, 1), (52, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (18, 1), (21, 1), (26, 1), (28, 1), (44, 1), (53, 1), (56, 1), (62, 1)] }, { coefficient := 1, powers := [(6, 1), (18, 1), (21, 1), (26, 1), (28, 1), (34, 1), (44, 1), (53, 1), (62, 1)] }, { coefficient := 1, powers := [(13, 1), (18, 1), (21, 1), (25, 1), (26, 1), (28, 1), (44, 1), (53, 1), (62, 1)] }, { coefficient := 1, powers := [(17, 1), (20, 1), (21, 1), (26, 1), (28, 1), (44, 1), (53, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (25, 1), (49, 1), (55, 1), (62, 1)] }, { coefficient := 1, powers := [(2, 1), (26, 1), (49, 1), (51, 1), (62, 1)] }, { coefficient := -1, powers := [(5, 1), (25, 1), (36, 1), (55, 1), (62, 1)] }, { coefficient := 1, powers := [(5, 1), (26, 1), (36, 1), (51, 1), (62, 1)] }, { coefficient := -1, powers := [(19, 1), (24, 1), (25, 1), (55, 1), (62, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (26, 1), (51, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (18, 1), (21, 1), (26, 1), (28, 1), (31, 1), (44, 1), (53, 1), (62, 1)] }, { coefficient := -1, powers := [(18, 1), (20, 1), (21, 1), (26, 1), (28, 1), (44, 1), (50, 1), (53, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (5, 1), (33, 1), (62, 1)] }, { coefficient := -1, powers := [(2, 1), (21, 1), (51, 1), (62, 1)] }, { coefficient := -1, powers := [(10, 1), (12, 1), (20, 1), (22, 1), (36, 1), (42, 1), (52, 1), (62, 1), (69, 1)] }, { coefficient := -1, powers := [(10, 1), (12, 1), (22, 1), (25, 1), (36, 1), (42, 1), (52, 1), (62, 1), (69, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (25, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (21, 1), (26, 1), (41, 1), (44, 1), (51, 1), (62, 1)] }, { coefficient := 1, powers := [(2, 1), (26, 1), (42, 1), (44, 1), (62, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (26, 1), (44, 1), (62, 1)] }, { coefficient := -1, powers := [(18, 1), (24, 1), (26, 1), (44, 1), (51, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (8, 1), (20, 1), (36, 1), (42, 1), (60, 1), (62, 1)] }, { coefficient := -1, powers := [(4, 1), (8, 1), (25, 1), (36, 1), (42, 1), (60, 1), (62, 1)] }, { coefficient := 1, powers := [(8, 1), (10, 1), (20, 1), (36, 1), (41, 1), (42, 1), (62, 1)] }, { coefficient := 1, powers := [(8, 1), (10, 1), (20, 1), (36, 1), (42, 1), (46, 1), (62, 1)] }, { coefficient := 1, powers := [(8, 1), (10, 1), (25, 1), (36, 1), (41, 1), (42, 1), (62, 1)] }, { coefficient := 1, powers := [(8, 1), (10, 1), (25, 1), (36, 1), (42, 1), (46, 1), (62, 1)] }, { coefficient := -1, powers := [(8, 1), (15, 1), (20, 1), (36, 1), (41, 1), (42, 1), (62, 1)] }, { coefficient := -1, powers := [(8, 1), (15, 1), (25, 1), (36, 1), (41, 1), (42, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (5, 1), (61, 1), (62, 1)] }, { coefficient := 1, powers := [(0, 1), (12, 1), (44, 1), (48, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 1), (12, 1), (49, 1), (62, 1)] }, { coefficient := 1, powers := [(0, 1), (18, 1), (49, 1), (51, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 1), (19, 1), (48, 1), (51, 1), (62, 1)] }, { coefficient := -1, powers := [(12, 1), (25, 1), (44, 1), (48, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (18, 1), (21, 1), (26, 1), (28, 1), (37, 1), (44, 1), (53, 1), (62, 1)] }, { coefficient := 2, powers := [(3, 1), (18, 1), (21, 1), (25, 1), (26, 1), (28, 1), (44, 1), (53, 1), (62, 1)] }, { coefficient := 1, powers := [(6, 1), (18, 1), (20, 1), (21, 1), (26, 1), (28, 1), (44, 1), (53, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (20, 1), (36, 1), (55, 1), (62, 1)] }, { coefficient := 1, powers := [(5, 1), (25, 1), (36, 1), (55, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (2, 1), (26, 1), (44, 1), (48, 1), (53, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 1), (8, 1), (36, 1), (42, 1), (62, 1)] }, { coefficient := -1, powers := [(2, 1), (20, 1), (26, 1), (44, 1), (48, 1), (53, 1), (62, 1)] }, { coefficient := -1, powers := [(2, 1), (25, 1), (26, 1), (44, 1), (48, 1), (53, 1), (62, 1)] }, { coefficient := -1, powers := [(8, 1), (10, 1), (20, 1), (22, 1), (36, 1), (42, 1), (52, 1), (62, 1)] }, { coefficient := -1, powers := [(8, 1), (10, 1), (22, 1), (25, 1), (36, 1), (42, 1), (52, 1), (62, 1)] }, { coefficient := -1, powers := [(8, 1), (20, 1), (36, 1), (42, 1), (62, 1)] }, { coefficient := -1, powers := [(8, 1), (25, 1), (36, 1), (42, 1), (62, 1)] }]
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
    (values : Fin 70 → R) :
    ¬ ∀ index : Fin 72,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component37.SelectedLeafB5_3_2_4_3.selectedHasNoCommonZero

end Krenn.Component37.SelectedLeafB5_3_2_4_3
