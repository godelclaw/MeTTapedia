import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component37.SelectedLeafB1_2_6_5

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "40a966a0c2705e2d5506edd7cef83b98e0f3db16f42f7678df2ba1c180e90495"
def certificateSHA256 : String := "6651bfaff79f214c541b096cea34ae137a682ff025758aaa71188edb64496243"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 70 → Fin 670 := ![
  6,
  13,
  17,
  42,
  151,
  167,
  170,
  171,
  175,
  176,
  179,
  181,
  183,
  256,
  257,
  279,
  280,
  295,
  297,
  300,
  301,
  303,
  307,
  310,
  311,
  315,
  316,
  343,
  410,
  425,
  430,
  432,
  438,
  445,
  446,
  449,
  450,
  453,
  454,
  455,
  458,
  471,
  472,
  476,
  515,
  516,
  526,
  555,
  562,
  580,
  581,
  586,
  602,
  603,
  609,
  619,
  645,
  648,
  655,
  657,
  658,
  660,
  661,
  662,
  663,
  664,
  665,
  666,
  667,
  669
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 70 → SparsePoly (Fin 68) := ![
  [{ coefficient := 1, powers := [(5, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (30, 1)] }, { coefficient := 1, powers := [(30, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (25, 1)] }, { coefficient := 1, powers := [(18, 1), (20, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (44, 1)] }, { coefficient := 1, powers := [(19, 1), (20, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (20, 1)] }, { coefficient := 1, powers := [(18, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (44, 1)] }, { coefficient := 1, powers := [(19, 1), (20, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (55, 1)] }, { coefficient := 1, powers := [(30, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (54, 1)] }, { coefficient := 1, powers := [(30, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(28, 1), (53, 1)] }, { coefficient := -1, powers := [(29, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (25, 1), (46, 1)] }, { coefficient := 1, powers := [(18, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (25, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (25, 1), (44, 1)] }, { coefficient := 1, powers := [(19, 1), (20, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (25, 1), (49, 1)] }, { coefficient := 1, powers := [(19, 1), (21, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (49, 1)] }, { coefficient := 1, powers := [(21, 1), (44, 1)] }, { coefficient := 1, powers := [(25, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (55, 1)] }, { coefficient := 1, powers := [(20, 1), (55, 1)] }, { coefficient := 1, powers := [(26, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (50, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (50, 1)] }, { coefficient := 1, powers := [(18, 1), (28, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (59, 1)] }, { coefficient := 1, powers := [(9, 1), (43, 1)] }, { coefficient := 1, powers := [(13, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (46, 1)] }, { coefficient := 1, powers := [(9, 1), (57, 1)] }, { coefficient := 1, powers := [(31, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (46, 1)] }, { coefficient := 1, powers := [(12, 1), (57, 1)] }, { coefficient := 1, powers := [(18, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (41, 1)] }, { coefficient := 1, powers := [(19, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (52, 1)] }, { coefficient := 1, powers := [(24, 1), (57, 1)] }, { coefficient := 1, powers := [(29, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1), (51, 1)] }, { coefficient := 1, powers := [(25, 1), (46, 1), (51, 1)] }, { coefficient := 1, powers := [(51, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1), (55, 1)] }, { coefficient := 1, powers := [(26, 1), (46, 1), (51, 1)] }, { coefficient := 1, powers := [(55, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (47, 1), (51, 1)] }, { coefficient := 1, powers := [(12, 1), (28, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (29, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (25, 1), (41, 1)] }, { coefficient := 1, powers := [(18, 1), (25, 1), (46, 1)] }, { coefficient := 1, powers := [(18, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (48, 1)] }, { coefficient := 1, powers := [(6, 1), (21, 1), (60, 1)] }, { coefficient := 1, powers := [(21, 1)] }, { coefficient := 1, powers := [(25, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (46, 1)] }, { coefficient := 1, powers := [(18, 1), (28, 1), (41, 1)] }, { coefficient := 1, powers := [(18, 1), (28, 1), (46, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (48, 1)] }, { coefficient := 1, powers := [(5, 1), (28, 1), (60, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1)] }, { coefficient := 1, powers := [(18, 1), (28, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1)] }, { coefficient := 1, powers := [(12, 1), (30, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (60, 1)] }, { coefficient := 1, powers := [(18, 1), (21, 1), (52, 1)] }, { coefficient := 1, powers := [(18, 1), (21, 1), (57, 1)] }, { coefficient := 1, powers := [(18, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (61, 1)] }, { coefficient := 1, powers := [(12, 1), (49, 1)] }, { coefficient := 1, powers := [(19, 1), (21, 1), (53, 1)] }, { coefficient := 1, powers := [(19, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (60, 1)] }, { coefficient := 1, powers := [(18, 1), (26, 1), (41, 1)] }, { coefficient := 1, powers := [(18, 1), (26, 1), (46, 1)] }, { coefficient := 1, powers := [(18, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (61, 1)] }, { coefficient := 1, powers := [(12, 1), (26, 1), (47, 1)] }, { coefficient := 1, powers := [(12, 1), (58, 1)] }, { coefficient := 1, powers := [(19, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (41, 1)] }, { coefficient := 1, powers := [(18, 1), (46, 1)] }, { coefficient := 1, powers := [(18, 1), (52, 1)] }, { coefficient := 1, powers := [(18, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (55, 1)] }, { coefficient := 1, powers := [(30, 1), (42, 1)] }, { coefficient := 1, powers := [(30, 1), (48, 1), (51, 1)] }, { coefficient := 1, powers := [(33, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (41, 1)] }, { coefficient := 1, powers := [(29, 1), (46, 1)] }, { coefficient := 1, powers := [(29, 1), (52, 1)] }, { coefficient := 1, powers := [(29, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (38, 1), (61, 1)] }, { coefficient := 1, powers := [(0, 1), (47, 1), (53, 1)] }, { coefficient := 1, powers := [(44, 1), (53, 1)] }, { coefficient := 1, powers := [(47, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1), (53, 1)] }, { coefficient := 1, powers := [(46, 1), (51, 1)] }, { coefficient := 1, powers := [(51, 1), (57, 1)] }, { coefficient := 1, powers := [(53, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1), (54, 1)] }, { coefficient := 1, powers := [(26, 1), (41, 1)] }, { coefficient := 1, powers := [(26, 1), (46, 1)] }, { coefficient := 1, powers := [(54, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1), (55, 1)] }, { coefficient := 1, powers := [(26, 1), (47, 1), (51, 1)] }, { coefficient := 1, powers := [(44, 1), (55, 1)] }, { coefficient := 1, powers := [(51, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (25, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (50, 1)] }, { coefficient := 1, powers := [(17, 1), (21, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (25, 1), (61, 1)] }, { coefficient := 1, powers := [(12, 1), (25, 1), (49, 1)] }, { coefficient := 1, powers := [(19, 1), (21, 1), (51, 1)] }, { coefficient := 1, powers := [(19, 1), (25, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (29, 1), (60, 1)] }, { coefficient := 1, powers := [(28, 1), (41, 1)] }, { coefficient := 1, powers := [(28, 1), (46, 1)] }, { coefficient := 1, powers := [(29, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (21, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1), (48, 1)] }, { coefficient := 1, powers := [(18, 1), (21, 1), (53, 1)] }, { coefficient := 1, powers := [(18, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (26, 1), (47, 1)] }, { coefficient := 1, powers := [(18, 1), (58, 1)] }, { coefficient := 1, powers := [(19, 1), (26, 1), (41, 1)] }, { coefficient := 1, powers := [(19, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1)] }, { coefficient := 1, powers := [(6, 1), (60, 1)] }, { coefficient := 1, powers := [(25, 1), (41, 1)] }, { coefficient := 1, powers := [(25, 1), (46, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (52, 1)] }, { coefficient := 1, powers := [(3, 1), (60, 1)] }, { coefficient := 1, powers := [(20, 1), (52, 1)] }, { coefficient := 1, powers := [(20, 1), (57, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1), (52, 1)] }, { coefficient := 1, powers := [(13, 1), (41, 1)] }, { coefficient := 1, powers := [(13, 1), (52, 1)] }, { coefficient := 1, powers := [(34, 1), (38, 1)] }, { coefficient := 1, powers := [(45, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1)] }, { coefficient := 1, powers := [(3, 1), (34, 1)] }, { coefficient := 1, powers := [(13, 1), (20, 1)] }, { coefficient := 1, powers := [(20, 1), (56, 1)] }, { coefficient := 1, powers := [(25, 1), (43, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (50, 1)] }, { coefficient := 1, powers := [(6, 1), (31, 1)] }, { coefficient := 1, powers := [(9, 1), (25, 1)] }, { coefficient := 1, powers := [(20, 1), (50, 1)] }, { coefficient := 1, powers := [(25, 1), (40, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (48, 1), (53, 1)] }, { coefficient := 1, powers := [(21, 1), (51, 1), (57, 1)] }, { coefficient := 1, powers := [(21, 1), (53, 1)] }, { coefficient := 1, powers := [(42, 1)] }, { coefficient := 1, powers := [(48, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (39, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (48, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (60, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (54, 1)] }, { coefficient := 1, powers := [(18, 1), (30, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (38, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (41, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(41, 1)] }, { coefficient := 1, powers := [(46, 1)] }, { coefficient := 1, powers := [(52, 1)] }, { coefficient := 1, powers := [(57, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (41, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (41, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (46, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (52, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (37, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (40, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (43, 1), (50, 1)] }, { coefficient := 1, powers := [(3, 1), (25, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (31, 1), (56, 1)] }, { coefficient := 1, powers := [(3, 1), (34, 1), (50, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (31, 1), (43, 1)] }, { coefficient := 1, powers := [(6, 1), (34, 1), (40, 1)] }, { coefficient := 1, powers := [(9, 1), (20, 1), (56, 1)] }, { coefficient := 1, powers := [(9, 1), (25, 1), (43, 1)] }, { coefficient := 1, powers := [(9, 1), (34, 1), (37, 1)] }, { coefficient := 1, powers := [(13, 1), (20, 1), (50, 1)] }, { coefficient := 1, powers := [(13, 1), (25, 1), (40, 1)] }, { coefficient := 1, powers := [(13, 1), (31, 1), (37, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (39, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (42, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (49, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (49, 1)] }, { coefficient := 1, powers := [(8, 1), (36, 1), (42, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (58, 1)] }, { coefficient := 1, powers := [(12, 1), (30, 1), (49, 1)] }, { coefficient := 1, powers := [(12, 1), (36, 1), (39, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (55, 1)] }, { coefficient := 1, powers := [(19, 1), (30, 1), (42, 1)] }, { coefficient := 1, powers := [(19, 1), (33, 1), (39, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(40, 1)] }],
  [{ coefficient := 1, powers := [(41, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(42, 1)] }],
  [{ coefficient := 1, powers := [(56, 1), (64, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(57, 1), (65, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(58, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (66, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(30, 1), (67, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 70 → SparsePoly (Fin 68) := ![
  [{ coefficient := 1, powers := [(3, 2), (25, 1), (36, 1), (55, 1), (60, 1)] }, { coefficient := -1, powers := [(3, 1), (6, 1), (20, 1), (36, 1), (55, 1), (60, 1)] }, { coefficient := 1, powers := [(3, 1), (13, 1), (25, 1), (36, 1), (37, 1), (55, 1), (60, 1), (64, 1)] }, { coefficient := -1, powers := [(3, 1), (25, 1), (36, 1), (37, 1), (43, 1), (55, 1), (60, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(3, 2), (21, 1), (36, 1), (55, 1), (60, 1)] }, { coefficient := 1, powers := [(3, 1), (13, 1), (21, 1), (36, 1), (37, 1), (55, 1), (60, 1), (64, 1)] }, { coefficient := -1, powers := [(3, 1), (21, 1), (36, 1), (37, 1), (43, 1), (55, 1), (60, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (5, 1), (13, 1), (20, 1), (23, 1), (36, 1), (55, 1), (60, 1), (62, 1)] }, { coefficient := -1, powers := [(3, 1), (5, 1), (13, 1), (23, 1), (34, 1), (36, 1), (37, 1), (55, 1), (60, 1), (62, 1), (64, 1)] }, { coefficient := -1, powers := [(3, 1), (5, 1), (20, 1), (23, 1), (36, 1), (43, 1), (55, 1), (60, 1), (62, 1)] }, { coefficient := 1, powers := [(3, 1), (5, 1), (23, 1), (34, 1), (36, 1), (37, 1), (43, 1), (55, 1), (60, 1), (62, 1), (64, 1)] }, { coefficient := 1, powers := [(13, 1), (20, 1), (23, 1), (37, 1), (41, 1), (60, 1), (62, 1), (65, 1)] }, { coefficient := 1, powers := [(13, 1), (20, 1), (23, 1), (37, 1), (52, 1), (60, 1), (62, 1), (65, 1)] }, { coefficient := -1, powers := [(20, 1), (23, 1), (25, 1), (38, 1), (43, 1), (60, 1), (62, 1), (65, 1)] }, { coefficient := 1, powers := [(20, 1), (23, 1), (37, 1), (45, 1), (60, 1), (62, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (20, 2), (60, 1), (62, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (5, 1), (20, 1), (36, 1), (55, 1), (56, 1), (60, 1), (67, 1)] }, { coefficient := 1, powers := [(3, 1), (5, 1), (25, 1), (36, 1), (43, 1), (55, 1), (60, 1), (67, 1)] }, { coefficient := -1, powers := [(3, 1), (5, 1), (34, 1), (36, 1), (37, 1), (55, 1), (60, 1), (67, 1)] }, { coefficient := 1, powers := [(3, 1), (20, 1), (46, 1), (56, 1), (60, 1), (65, 1), (67, 1)] }, { coefficient := 1, powers := [(3, 1), (20, 1), (56, 1), (57, 1), (60, 1), (65, 1), (67, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1), (43, 1), (46, 1), (60, 1), (65, 1), (67, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1), (43, 1), (57, 1), (60, 1), (65, 1), (67, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1), (46, 1), (56, 1), (60, 1), (65, 1), (67, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1), (56, 1), (57, 1), (60, 1), (65, 1), (67, 1)] }, { coefficient := 1, powers := [(13, 1), (20, 1), (37, 1), (46, 1), (60, 1), (65, 1), (67, 1)] }, { coefficient := 1, powers := [(13, 1), (20, 1), (37, 1), (57, 1), (60, 1), (65, 1), (67, 1)] }, { coefficient := -1, powers := [(20, 2), (38, 1), (56, 1), (60, 1), (65, 1), (67, 1)] }, { coefficient := -1, powers := [(20, 1), (25, 1), (38, 1), (56, 1), (60, 1), (65, 1), (67, 1)] }, { coefficient := -1, powers := [(20, 1), (34, 1), (37, 1), (38, 1), (60, 1), (65, 1), (67, 1)] }, { coefficient := 1, powers := [(20, 1), (37, 1), (46, 1), (56, 1), (60, 1), (65, 1), (67, 1)] }, { coefficient := 1, powers := [(20, 1), (37, 1), (56, 1), (57, 1), (60, 1), (65, 1), (67, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (30, 1), (47, 1), (48, 1), (60, 1)] }, { coefficient := -1, powers := [(3, 1), (36, 1), (39, 1), (41, 1), (60, 1), (63, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (30, 1), (48, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (18, 1), (21, 1), (28, 1), (30, 1), (60, 1), (62, 1)] }, { coefficient := -1, powers := [(3, 1), (18, 1), (24, 1), (26, 1), (28, 1), (60, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (30, 1), (47, 1), (48, 1), (51, 1), (60, 1)] }, { coefficient := 1, powers := [(3, 1), (36, 1), (39, 1), (41, 1), (51, 1), (60, 1), (63, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (24, 1), (55, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (18, 1), (49, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (18, 1), (61, 1)] }, { coefficient := 1, powers := [(3, 1), (19, 1), (51, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (18, 1), (19, 1), (21, 1), (30, 1), (60, 1), (62, 1)] }, { coefficient := 1, powers := [(3, 1), (18, 1), (19, 1), (24, 1), (26, 1), (60, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (30, 1), (49, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (24, 1), (26, 1), (60, 1), (66, 1)] }, { coefficient := 1, powers := [(3, 1), (30, 1), (48, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (30, 1), (48, 1), (53, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (30, 1), (53, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (12, 1), (30, 1), (46, 1), (60, 1)] }, { coefficient := -1, powers := [(3, 1), (18, 1), (30, 1), (53, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (19, 1), (24, 1), (52, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (5, 1), (13, 1), (20, 1), (36, 1), (55, 1), (60, 1), (62, 1)] }, { coefficient := 1, powers := [(3, 1), (5, 1), (13, 1), (34, 1), (36, 1), (37, 1), (55, 1), (60, 1), (62, 1), (64, 1)] }, { coefficient := 1, powers := [(3, 1), (5, 1), (20, 1), (36, 1), (43, 1), (55, 1), (60, 1), (62, 1)] }, { coefficient := -1, powers := [(3, 1), (5, 1), (34, 1), (36, 1), (37, 1), (43, 1), (55, 1), (60, 1), (62, 1), (64, 1)] }, { coefficient := -1, powers := [(13, 1), (20, 1), (37, 1), (41, 1), (60, 1), (62, 1), (65, 1)] }, { coefficient := -1, powers := [(13, 1), (20, 1), (37, 1), (52, 1), (60, 1), (62, 1), (65, 1)] }, { coefficient := 1, powers := [(20, 1), (25, 1), (38, 1), (43, 1), (60, 1), (62, 1), (65, 1)] }, { coefficient := -1, powers := [(20, 1), (37, 1), (45, 1), (60, 1), (62, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (5, 1), (25, 1), (36, 1), (55, 1), (60, 1)] }, { coefficient := -1, powers := [(20, 1), (25, 1), (38, 1), (60, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (20, 1), (56, 1), (60, 1), (65, 1)] }, { coefficient := -1, powers := [(6, 1), (20, 1), (43, 1), (60, 1), (65, 1)] }, { coefficient := -1, powers := [(6, 1), (20, 1), (56, 1), (60, 1), (65, 1)] }, { coefficient := -1, powers := [(13, 1), (20, 1), (37, 1), (60, 1), (65, 1)] }, { coefficient := -1, powers := [(20, 1), (37, 1), (56, 1), (60, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (21, 1), (30, 1), (44, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (24, 1), (26, 1), (51, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (18, 1), (25, 1), (54, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (18, 1), (36, 1), (39, 1), (60, 1), (63, 1), (66, 1)] }, { coefficient := -1, powers := [(3, 1), (19, 1), (21, 1), (30, 1), (60, 1), (66, 1)] }, { coefficient := -1, powers := [(3, 1), (19, 1), (24, 1), (26, 1), (60, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (19, 1), (24, 1), (25, 1), (60, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (18, 1), (21, 1), (30, 1), (60, 1), (62, 1)] }, { coefficient := 1, powers := [(3, 1), (18, 1), (24, 1), (26, 1), (60, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (24, 1), (54, 1), (61, 1)] }, { coefficient := -1, powers := [(3, 1), (36, 1), (39, 1), (51, 1), (60, 1), (63, 1), (66, 1)] }, { coefficient := 1, powers := [(20, 1), (29, 1), (52, 1), (62, 1), (65, 1)] }, { coefficient := -1, powers := [(20, 1), (29, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (18, 1), (29, 1), (54, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(20, 1), (52, 1), (62, 1), (65, 1)] }, { coefficient := 1, powers := [(20, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (54, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (49, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (28, 1), (54, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (30, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (24, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (24, 1), (25, 1), (60, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (21, 1), (28, 1), (54, 1), (61, 1)] }, { coefficient := 1, powers := [(3, 1), (24, 1), (25, 1), (54, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (19, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(18, 1), (20, 1), (62, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (18, 1), (21, 1), (30, 1), (60, 1)] }, { coefficient := -1, powers := [(3, 1), (18, 1), (25, 1), (30, 1), (48, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (19, 1), (21, 1), (30, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (18, 1), (24, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (18, 1), (24, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(3, 2), (36, 1), (55, 1), (60, 1)] }, { coefficient := -1, powers := [(3, 1), (13, 1), (36, 1), (37, 1), (55, 1), (60, 1), (64, 1)] }, { coefficient := 1, powers := [(3, 1), (36, 1), (37, 1), (43, 1), (55, 1), (60, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (30, 1), (60, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (18, 1), (21, 1), (54, 1), (61, 1)] }, { coefficient := 1, powers := [(18, 1), (20, 1), (52, 1), (62, 1), (65, 1)] }, { coefficient := -1, powers := [(18, 1), (20, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (30, 1), (44, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (24, 1), (51, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(18, 1), (20, 1), (29, 1), (52, 1), (62, 1), (65, 1)] }, { coefficient := 1, powers := [(18, 1), (20, 1), (29, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(20, 1), (37, 1), (50, 1), (60, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(20, 1), (38, 1), (50, 1), (60, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (5, 1), (36, 1), (43, 1), (55, 1), (60, 1)] }, { coefficient := 1, powers := [(20, 1), (38, 1), (56, 1), (60, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (19, 1), (30, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(20, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (62, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (5, 1), (36, 1), (55, 1), (60, 1)] }, { coefficient := 1, powers := [(20, 1), (38, 1), (60, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (5, 1), (36, 1), (37, 1), (55, 1), (59, 1), (60, 1)] }, { coefficient := -1, powers := [(3, 1), (12, 1), (30, 1), (46, 1), (49, 1), (60, 1)] }, { coefficient := -1, powers := [(3, 1), (18, 1), (21, 1), (30, 1), (38, 1), (60, 1), (61, 1)] }, { coefficient := -1, powers := [(3, 1), (18, 1), (21, 1), (30, 1), (47, 1), (53, 1), (60, 1)] }, { coefficient := 1, powers := [(3, 1), (18, 1), (24, 1), (46, 1), (54, 1), (61, 1)] }, { coefficient := 1, powers := [(3, 1), (18, 1), (24, 1), (47, 1), (55, 1), (60, 1)] }, { coefficient := 1, powers := [(3, 1), (18, 1), (25, 1), (30, 1), (38, 1), (48, 1), (60, 1), (61, 1)] }, { coefficient := 1, powers := [(3, 1), (18, 1), (25, 1), (30, 1), (47, 1), (48, 1), (53, 1), (60, 1)] }, { coefficient := -1, powers := [(3, 1), (18, 1), (29, 1), (48, 1), (54, 1), (61, 1)] }, { coefficient := 1, powers := [(3, 1), (18, 1), (30, 1), (49, 1), (53, 1), (60, 1)] }, { coefficient := -1, powers := [(3, 1), (18, 1), (36, 1), (39, 1), (46, 1), (51, 1), (60, 1), (63, 1), (66, 1)] }, { coefficient := 1, powers := [(3, 1), (19, 1), (21, 1), (30, 1), (46, 1), (51, 1), (60, 1), (66, 1)] }, { coefficient := -1, powers := [(3, 1), (19, 1), (21, 1), (30, 1), (46, 1), (53, 1), (60, 1)] }, { coefficient := -1, powers := [(3, 1), (19, 1), (24, 1), (25, 1), (46, 1), (55, 1), (60, 1), (66, 1)] }, { coefficient := 1, powers := [(3, 1), (19, 1), (24, 1), (26, 1), (46, 1), (51, 1), (60, 1), (66, 1)] }, { coefficient := 1, powers := [(3, 1), (19, 1), (24, 1), (52, 1), (55, 1), (60, 1)] }, { coefficient := 1, powers := [(3, 1), (19, 1), (30, 1), (48, 1), (53, 1), (60, 1)] }, { coefficient := 1, powers := [(18, 1), (20, 1), (29, 1), (46, 1), (52, 1), (62, 1), (65, 1)] }, { coefficient := -1, powers := [(18, 1), (20, 1), (29, 1), (46, 1), (62, 1)] }, { coefficient := -1, powers := [(20, 1), (37, 1), (38, 1), (59, 1), (60, 1), (65, 1)] }, { coefficient := -1, powers := [(20, 1), (37, 1), (45, 1), (50, 1), (52, 1), (60, 1), (65, 1)] }, { coefficient := -1, powers := [(20, 1), (38, 1), (50, 1), (56, 1), (60, 1), (65, 1)] }, { coefficient := 1, powers := [(20, 1), (38, 1), (60, 1)] }, { coefficient := 1, powers := [(20, 1), (41, 1), (57, 1)] }, { coefficient := 1, powers := [(20, 1), (46, 1), (52, 1)] }, { coefficient := -1, powers := [(52, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (5, 1), (13, 1), (20, 1), (36, 1), (50, 1), (55, 1), (60, 1)] }, { coefficient := -1, powers := [(3, 1), (5, 1), (13, 1), (34, 1), (36, 1), (37, 1), (50, 1), (55, 1), (60, 1), (64, 1)] }, { coefficient := -1, powers := [(3, 1), (5, 1), (20, 1), (36, 1), (43, 1), (50, 1), (55, 1), (60, 1)] }, { coefficient := 1, powers := [(3, 1), (5, 1), (34, 1), (36, 1), (37, 1), (43, 1), (50, 1), (55, 1), (60, 1), (64, 1)] }, { coefficient := 1, powers := [(3, 1), (18, 1), (21, 1), (30, 1), (47, 1), (51, 1), (60, 1)] }, { coefficient := -1, powers := [(3, 1), (18, 1), (24, 1), (26, 1), (47, 1), (51, 1), (60, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 2), (38, 1), (59, 1), (60, 1), (65, 1)] }, { coefficient := 1, powers := [(13, 1), (20, 1), (37, 1), (41, 1), (50, 1), (60, 1), (65, 1)] }, { coefficient := 1, powers := [(13, 1), (20, 1), (37, 1), (50, 1), (52, 1), (60, 1), (65, 1)] }, { coefficient := -1, powers := [(20, 1), (25, 1), (38, 1), (43, 1), (50, 1), (60, 1), (65, 1)] }, { coefficient := 1, powers := [(20, 1), (37, 1), (45, 1), (50, 1), (60, 1), (65, 1)] }, { coefficient := -1, powers := [(20, 1), (38, 1), (60, 1), (65, 1)] }, { coefficient := -1, powers := [(20, 1), (41, 1), (57, 1), (65, 1)] }, { coefficient := -1, powers := [(20, 1), (46, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (3, 1), (5, 1), (36, 1), (55, 1), (56, 1), (60, 1)] }, { coefficient := -1, powers := [(0, 1), (20, 1), (38, 1), (56, 1), (60, 1), (65, 1)] }, { coefficient := -1, powers := [(3, 1), (5, 1), (6, 1), (34, 1), (36, 1), (55, 1), (60, 1)] }, { coefficient := 1, powers := [(3, 1), (5, 1), (13, 1), (18, 1), (20, 1), (28, 1), (36, 1), (55, 1), (60, 1), (62, 1)] }, { coefficient := -1, powers := [(3, 1), (5, 1), (13, 1), (18, 1), (28, 1), (34, 1), (36, 1), (37, 1), (55, 1), (60, 1), (62, 1), (64, 1)] }, { coefficient := -1, powers := [(3, 1), (5, 1), (18, 1), (20, 1), (28, 1), (36, 1), (43, 1), (55, 1), (60, 1), (62, 1)] }, { coefficient := 1, powers := [(3, 1), (5, 1), (18, 1), (28, 1), (34, 1), (36, 1), (37, 1), (43, 1), (55, 1), (60, 1), (62, 1), (64, 1)] }, { coefficient := 1, powers := [(3, 1), (5, 1), (20, 1), (30, 1), (36, 1), (55, 1), (56, 1), (60, 1), (67, 1)] }, { coefficient := -1, powers := [(3, 1), (5, 1), (25, 1), (30, 1), (36, 1), (43, 1), (55, 1), (60, 1), (67, 1)] }, { coefficient := 1, powers := [(3, 1), (5, 1), (25, 1), (36, 1), (43, 1), (55, 1), (60, 1)] }, { coefficient := 1, powers := [(3, 1), (5, 1), (30, 1), (34, 1), (36, 1), (37, 1), (55, 1), (60, 1), (67, 1)] }, { coefficient := -1, powers := [(3, 1), (20, 1), (30, 1), (46, 1), (56, 1), (60, 1), (65, 1), (67, 1)] }, { coefficient := -1, powers := [(3, 1), (20, 1), (30, 1), (56, 1), (57, 1), (60, 1), (65, 1), (67, 1)] }, { coefficient := -1, powers := [(6, 1), (20, 1), (30, 1), (43, 1), (46, 1), (60, 1), (65, 1), (67, 1)] }, { coefficient := -1, powers := [(6, 1), (20, 1), (30, 1), (43, 1), (57, 1), (60, 1), (65, 1), (67, 1)] }, { coefficient := -1, powers := [(6, 1), (20, 1), (30, 1), (46, 1), (56, 1), (60, 1), (65, 1), (67, 1)] }, { coefficient := -1, powers := [(6, 1), (20, 1), (30, 1), (56, 1), (57, 1), (60, 1), (65, 1), (67, 1)] }, { coefficient := -1, powers := [(6, 1), (20, 1), (34, 1), (38, 1), (60, 1), (65, 1)] }, { coefficient := 1, powers := [(13, 1), (18, 1), (20, 1), (28, 1), (37, 1), (41, 1), (60, 1), (62, 1), (65, 1)] }, { coefficient := 1, powers := [(13, 1), (18, 1), (20, 1), (28, 1), (37, 1), (52, 1), (60, 1), (62, 1), (65, 1)] }, { coefficient := -1, powers := [(13, 1), (20, 1), (30, 1), (37, 1), (46, 1), (60, 1), (65, 1), (67, 1)] }, { coefficient := -1, powers := [(13, 1), (20, 1), (30, 1), (37, 1), (57, 1), (60, 1), (65, 1), (67, 1)] }, { coefficient := -1, powers := [(18, 1), (20, 1), (25, 1), (28, 1), (38, 1), (43, 1), (60, 1), (62, 1), (65, 1)] }, { coefficient := 1, powers := [(18, 1), (20, 1), (28, 1), (37, 1), (45, 1), (60, 1), (62, 1), (65, 1)] }, { coefficient := 1, powers := [(20, 2), (30, 1), (38, 1), (56, 1), (60, 1), (65, 1), (67, 1)] }, { coefficient := 1, powers := [(20, 1), (25, 1), (30, 1), (38, 1), (56, 1), (60, 1), (65, 1), (67, 1)] }, { coefficient := -1, powers := [(20, 1), (25, 1), (38, 1), (56, 1), (60, 1), (65, 1)] }, { coefficient := 1, powers := [(20, 1), (30, 1), (34, 1), (37, 1), (38, 1), (60, 1), (65, 1), (67, 1)] }, { coefficient := -1, powers := [(20, 1), (30, 1), (37, 1), (46, 1), (56, 1), (60, 1), (65, 1), (67, 1)] }, { coefficient := -1, powers := [(20, 1), (30, 1), (37, 1), (56, 1), (57, 1), (60, 1), (65, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (12, 1), (36, 1), (39, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (3, 1), (19, 1), (30, 1), (57, 1), (60, 1)] }, { coefficient := -1, powers := [(2, 1), (3, 1), (58, 1), (60, 1)] }, { coefficient := -1, powers := [(3, 1), (8, 1), (36, 1), (60, 1)] }, { coefficient := -1, powers := [(3, 1), (18, 1), (30, 1), (44, 1), (60, 1)] }, { coefficient := -1, powers := [(3, 1), (19, 1), (25, 1), (30, 1), (60, 1), (66, 1)] }, { coefficient := 2, powers := [(3, 1), (19, 1), (30, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (5, 1), (13, 1), (31, 1), (36, 1), (37, 1), (55, 1), (60, 1)] }, { coefficient := -1, powers := [(3, 1), (5, 1), (31, 1), (36, 1), (37, 1), (43, 1), (55, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(20, 1), (41, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (5, 1), (33, 1), (60, 1)] }, { coefficient := 1, powers := [(3, 1), (12, 1), (24, 1), (25, 1), (60, 1), (66, 1)] }, { coefficient := -1, powers := [(3, 1), (12, 1), (24, 1), (60, 1)] }, { coefficient := 2, powers := [(3, 1), (18, 1), (24, 1), (51, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (5, 1), (30, 1), (60, 1), (61, 1)] }, { coefficient := 1, powers := [(3, 1), (8, 1), (24, 1), (60, 1), (61, 1)] }, { coefficient := -1, powers := [(3, 1), (12, 1), (30, 1), (49, 1), (60, 1)] }, { coefficient := 1, powers := [(3, 1), (12, 1), (36, 1), (39, 1), (41, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(3, 1), (19, 1), (21, 1), (30, 1), (46, 1), (51, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (5, 1), (9, 1), (20, 1), (36, 1), (55, 1), (56, 1), (60, 1)] }, { coefficient := -1, powers := [(3, 1), (5, 1), (9, 1), (25, 1), (36, 1), (43, 1), (55, 1), (60, 1)] }, { coefficient := 1, powers := [(3, 1), (5, 1), (9, 1), (34, 1), (36, 1), (37, 1), (55, 1), (60, 1)] }, { coefficient := -1, powers := [(3, 1), (9, 1), (20, 1), (46, 1), (56, 1), (60, 1), (65, 1)] }, { coefficient := -1, powers := [(3, 1), (9, 1), (20, 1), (56, 1), (57, 1), (60, 1), (65, 1)] }, { coefficient := -1, powers := [(6, 1), (9, 1), (20, 1), (43, 1), (46, 1), (60, 1), (65, 1)] }, { coefficient := -1, powers := [(6, 1), (9, 1), (20, 1), (43, 1), (57, 1), (60, 1), (65, 1)] }, { coefficient := -1, powers := [(6, 1), (9, 1), (20, 1), (46, 1), (56, 1), (60, 1), (65, 1)] }, { coefficient := -1, powers := [(6, 1), (9, 1), (20, 1), (56, 1), (57, 1), (60, 1), (65, 1)] }, { coefficient := -1, powers := [(9, 1), (13, 1), (20, 1), (37, 1), (46, 1), (60, 1), (65, 1)] }, { coefficient := -1, powers := [(9, 1), (13, 1), (20, 1), (37, 1), (57, 1), (60, 1), (65, 1)] }, { coefficient := 1, powers := [(9, 1), (20, 2), (38, 1), (56, 1), (60, 1), (65, 1)] }, { coefficient := 1, powers := [(9, 1), (20, 1), (25, 1), (38, 1), (56, 1), (60, 1), (65, 1)] }, { coefficient := 1, powers := [(9, 1), (20, 1), (34, 1), (37, 1), (38, 1), (60, 1), (65, 1)] }, { coefficient := -1, powers := [(9, 1), (20, 1), (37, 1), (46, 1), (56, 1), (60, 1), (65, 1)] }, { coefficient := -1, powers := [(9, 1), (20, 1), (37, 1), (56, 1), (57, 1), (60, 1), (65, 1)] }]
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
    ¬ ∀ index : Fin 70,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component37.SelectedLeafB1_2_6_5.selectedHasNoCommonZero

end Krenn.Component37.SelectedLeafB1_2_6_5
