import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component37.SelectedLeafB1_2_2

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "70c3ffb1d6058e7ae0d261fc7c65403ac155cd6b835d2a01d0799aa6359445d8"
def certificateSHA256 : String := "590bb7475d739254dde765bb632c2a155c79044e25fb5139f5e0d35249be3fd6"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 70 → Fin 667 := ![
  8,
  17,
  68,
  149,
  167,
  168,
  170,
  171,
  175,
  176,
  180,
  181,
  222,
  255,
  260,
  279,
  280,
  294,
  295,
  296,
  297,
  300,
  301,
  307,
  311,
  313,
  316,
  317,
  342,
  349,
  364,
  393,
  406,
  407,
  408,
  426,
  432,
  438,
  445,
  446,
  450,
  451,
  453,
  454,
  459,
  466,
  471,
  472,
  479,
  481,
  483,
  499,
  526,
  566,
  567,
  580,
  581,
  602,
  603,
  609,
  612,
  645,
  655,
  657,
  658,
  660,
  661,
  663,
  664,
  666
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 70 → SparsePoly (Fin 65) := ![
  [{ coefficient := 1, powers := [(9, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (21, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (26, 1)] }, { coefficient := 1, powers := [(26, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (25, 1)] }, { coefficient := 1, powers := [(18, 1), (20, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (26, 1)] }, { coefficient := 1, powers := [(18, 1), (20, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (44, 1)] }, { coefficient := 1, powers := [(19, 1), (20, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (20, 1)] }, { coefficient := 1, powers := [(18, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (44, 1)] }, { coefficient := 1, powers := [(19, 1), (20, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (44, 1)] }, { coefficient := 1, powers := [(28, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (54, 1)] }, { coefficient := 1, powers := [(30, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (26, 1), (48, 1)] }, { coefficient := 1, powers := [(31, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (25, 1), (44, 1)] }, { coefficient := 1, powers := [(19, 1), (20, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (26, 1), (46, 1)] }, { coefficient := 1, powers := [(18, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (25, 1), (44, 1)] }, { coefficient := 1, powers := [(19, 1), (20, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (25, 1), (49, 1)] }, { coefficient := 1, powers := [(19, 1), (21, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1)] }, { coefficient := 1, powers := [(20, 1), (44, 1)] }, { coefficient := 1, powers := [(25, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (49, 1)] }, { coefficient := 1, powers := [(21, 1), (44, 1)] }, { coefficient := 1, powers := [(25, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (51, 1)] }, { coefficient := 1, powers := [(20, 1), (51, 1)] }, { coefficient := 1, powers := [(25, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (55, 1)] }, { coefficient := 1, powers := [(20, 1), (55, 1)] }, { coefficient := 1, powers := [(26, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (50, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (50, 1)] }, { coefficient := 1, powers := [(18, 1), (28, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (59, 1)] }, { coefficient := 1, powers := [(9, 1), (43, 1)] }, { coefficient := 1, powers := [(13, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (46, 1)] }, { coefficient := 1, powers := [(12, 1), (57, 1)] }, { coefficient := 1, powers := [(18, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (52, 1)] }, { coefficient := 1, powers := [(24, 1), (57, 1)] }, { coefficient := 1, powers := [(29, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(20, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(44, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1), (55, 1)] }, { coefficient := 1, powers := [(26, 1), (46, 1), (51, 1)] }, { coefficient := 1, powers := [(55, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (49, 1), (52, 1)] }, { coefficient := 1, powers := [(21, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(49, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (46, 1), (51, 1)] }, { coefficient := 1, powers := [(12, 1), (28, 1), (46, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (30, 1), (60, 1)] }, { coefficient := 1, powers := [(23, 1), (54, 1)] }, { coefficient := 1, powers := [(30, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (24, 1), (60, 1)] }, { coefficient := 1, powers := [(24, 1)] }, { coefficient := 1, powers := [(28, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (20, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1)] }, { coefficient := 1, powers := [(18, 1), (20, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (20, 1), (50, 1)] }, { coefficient := 1, powers := [(18, 1), (25, 1), (40, 1)] }, { coefficient := 1, powers := [(18, 1), (31, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (20, 1), (52, 1)] }, { coefficient := 1, powers := [(18, 1), (20, 1), (57, 1)] }, { coefficient := 1, powers := [(18, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (20, 1), (58, 1)] }, { coefficient := 1, powers := [(18, 1), (26, 1), (44, 1)] }, { coefficient := 1, powers := [(19, 1), (20, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (53, 1)] }, { coefficient := 1, powers := [(20, 1), (51, 1), (57, 1)] }, { coefficient := 1, powers := [(20, 1), (53, 1)] }, { coefficient := 1, powers := [(51, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (48, 1)] }, { coefficient := 1, powers := [(5, 1), (28, 1), (60, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1)] }, { coefficient := 1, powers := [(18, 1), (28, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1)] }, { coefficient := 1, powers := [(12, 1), (30, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (60, 1)] }, { coefficient := 1, powers := [(18, 1), (21, 1), (52, 1)] }, { coefficient := 1, powers := [(18, 1), (21, 1), (57, 1)] }, { coefficient := 1, powers := [(18, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (61, 1)] }, { coefficient := 1, powers := [(12, 1), (49, 1)] }, { coefficient := 1, powers := [(19, 1), (21, 1), (53, 1)] }, { coefficient := 1, powers := [(19, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (61, 1)] }, { coefficient := 1, powers := [(12, 1), (26, 1), (47, 1)] }, { coefficient := 1, powers := [(12, 1), (58, 1)] }, { coefficient := 1, powers := [(19, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (20, 1)] }, { coefficient := 1, powers := [(18, 1), (20, 1), (56, 1)] }, { coefficient := 1, powers := [(18, 1), (25, 1), (43, 1)] }, { coefficient := 1, powers := [(18, 1), (34, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (41, 1)] }, { coefficient := 1, powers := [(18, 1), (46, 1)] }, { coefficient := 1, powers := [(18, 1), (52, 1)] }, { coefficient := 1, powers := [(18, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (55, 1)] }, { coefficient := 1, powers := [(30, 1), (42, 1)] }, { coefficient := 1, powers := [(30, 1), (48, 1), (51, 1)] }, { coefficient := 1, powers := [(33, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (39, 1), (59, 1)] }, { coefficient := 1, powers := [(9, 1), (21, 1), (26, 1), (45, 1)] }, { coefficient := 1, powers := [(9, 1), (34, 1), (39, 1)] }, { coefficient := 1, powers := [(13, 1), (31, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1), (54, 1)] }, { coefficient := 1, powers := [(20, 1), (44, 1), (54, 1)] }, { coefficient := 1, powers := [(20, 1), (58, 1)] }, { coefficient := 1, powers := [(26, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1), (53, 1)] }, { coefficient := 1, powers := [(46, 1), (51, 1)] }, { coefficient := 1, powers := [(51, 1), (57, 1)] }, { coefficient := 1, powers := [(53, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1), (54, 1)] }, { coefficient := 1, powers := [(26, 1), (41, 1)] }, { coefficient := 1, powers := [(26, 1), (46, 1)] }, { coefficient := 1, powers := [(54, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (48, 1), (52, 1)] }, { coefficient := 1, powers := [(21, 1), (52, 1)] }, { coefficient := 1, powers := [(21, 1), (57, 1)] }, { coefficient := 1, powers := [(48, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (49, 1), (50, 1)] }, { coefficient := 1, powers := [(6, 1), (31, 1), (49, 1)] }, { coefficient := 1, powers := [(9, 1), (25, 1), (49, 1)] }, { coefficient := 1, powers := [(21, 1), (44, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (49, 1), (54, 1)] }, { coefficient := 1, powers := [(21, 1), (44, 1), (54, 1)] }, { coefficient := 1, powers := [(21, 1), (58, 1)] }, { coefficient := 1, powers := [(26, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (28, 1), (60, 1)] }, { coefficient := 1, powers := [(6, 1), (23, 1), (60, 1)] }, { coefficient := 1, powers := [(23, 1)] }, { coefficient := 1, powers := [(28, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (29, 1), (60, 1)] }, { coefficient := 1, powers := [(28, 1), (41, 1)] }, { coefficient := 1, powers := [(28, 1), (46, 1)] }, { coefficient := 1, powers := [(29, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (44, 1), (54, 1)] }, { coefficient := 1, powers := [(24, 1), (58, 1)] }, { coefficient := 1, powers := [(30, 1), (49, 1)] }, { coefficient := 1, powers := [(36, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (51, 1), (57, 1)] }, { coefficient := 1, powers := [(24, 1), (53, 1)] }, { coefficient := 1, powers := [(29, 1), (42, 1)] }, { coefficient := 1, powers := [(29, 1), (48, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1)] }, { coefficient := 1, powers := [(6, 1), (60, 1)] }, { coefficient := 1, powers := [(25, 1), (41, 1)] }, { coefficient := 1, powers := [(25, 1), (46, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (52, 1)] }, { coefficient := 1, powers := [(3, 1), (60, 1)] }, { coefficient := 1, powers := [(20, 1), (52, 1)] }, { coefficient := 1, powers := [(20, 1), (57, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1)] }, { coefficient := 1, powers := [(3, 1), (34, 1)] }, { coefficient := 1, powers := [(13, 1), (20, 1)] }, { coefficient := 1, powers := [(20, 1), (56, 1)] }, { coefficient := 1, powers := [(25, 1), (43, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (50, 1)] }, { coefficient := 1, powers := [(6, 1), (31, 1)] }, { coefficient := 1, powers := [(9, 1), (25, 1)] }, { coefficient := 1, powers := [(20, 1), (50, 1)] }, { coefficient := 1, powers := [(25, 1), (40, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (48, 1), (53, 1)] }, { coefficient := 1, powers := [(21, 1), (51, 1), (57, 1)] }, { coefficient := 1, powers := [(21, 1), (53, 1)] }, { coefficient := 1, powers := [(42, 1)] }, { coefficient := 1, powers := [(48, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1), (50, 1)] }, { coefficient := 1, powers := [(6, 1), (31, 1), (45, 1)] }, { coefficient := 1, powers := [(6, 1), (59, 1)] }, { coefficient := 1, powers := [(9, 1), (25, 1), (45, 1)] }, { coefficient := 1, powers := [(9, 1), (56, 1)] }, { coefficient := 1, powers := [(13, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (38, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (41, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(41, 1)] }, { coefficient := 1, powers := [(46, 1)] }, { coefficient := 1, powers := [(52, 1)] }, { coefficient := 1, powers := [(57, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (37, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (40, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (43, 1), (50, 1)] }, { coefficient := 1, powers := [(3, 1), (25, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (31, 1), (56, 1)] }, { coefficient := 1, powers := [(3, 1), (34, 1), (50, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (31, 1), (43, 1)] }, { coefficient := 1, powers := [(6, 1), (34, 1), (40, 1)] }, { coefficient := 1, powers := [(9, 1), (20, 1), (56, 1)] }, { coefficient := 1, powers := [(9, 1), (25, 1), (43, 1)] }, { coefficient := 1, powers := [(9, 1), (34, 1), (37, 1)] }, { coefficient := 1, powers := [(13, 1), (20, 1), (50, 1)] }, { coefficient := 1, powers := [(13, 1), (25, 1), (40, 1)] }, { coefficient := 1, powers := [(13, 1), (31, 1), (37, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (39, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (42, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (49, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (49, 1)] }, { coefficient := 1, powers := [(8, 1), (36, 1), (42, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (58, 1)] }, { coefficient := 1, powers := [(12, 1), (30, 1), (49, 1)] }, { coefficient := 1, powers := [(12, 1), (36, 1), (39, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (55, 1)] }, { coefficient := 1, powers := [(19, 1), (30, 1), (42, 1)] }, { coefficient := 1, powers := [(19, 1), (33, 1), (39, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(40, 1)] }],
  [{ coefficient := 1, powers := [(42, 1)] }],
  [{ coefficient := 1, powers := [(56, 1)] }],
  [{ coefficient := 1, powers := [(58, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 70 → SparsePoly (Fin 65) := ![
  [{ coefficient := 2, powers := [(12, 1), (25, 1), (30, 1), (43, 1)] }, { coefficient := -2, powers := [(12, 1), (30, 1), (34, 1), (37, 1)] }],
  [{ coefficient := 2, powers := [(2, 1), (13, 1), (20, 1), (23, 1), (39, 1), (61, 1), (62, 1)] }, { coefficient := -2, powers := [(2, 1), (20, 2), (23, 1), (39, 1), (45, 1), (61, 1), (62, 1)] }, { coefficient := 2, powers := [(2, 1), (23, 1), (25, 1), (39, 1), (43, 1), (61, 1), (62, 1)] }, { coefficient := 2, powers := [(2, 1), (23, 1), (34, 1), (37, 1), (39, 1), (61, 1), (62, 1)] }, { coefficient := 2, powers := [(3, 1), (12, 1), (23, 1), (30, 1), (34, 1), (49, 1), (62, 1)] }, { coefficient := -2, powers := [(12, 1), (13, 1), (20, 1), (23, 1), (30, 1), (49, 1), (62, 1)] }, { coefficient := -2, powers := [(12, 1), (13, 1), (23, 1), (25, 1), (30, 1), (49, 1), (62, 1)] }, { coefficient := -2, powers := [(12, 1), (20, 1), (23, 1), (25, 1), (30, 1), (45, 1), (49, 1), (62, 1)] }, { coefficient := 2, powers := [(12, 1), (23, 1), (25, 1), (30, 1), (43, 1), (49, 1), (62, 1)] }, { coefficient := -2, powers := [(13, 1), (20, 1), (28, 1), (49, 1), (55, 1)] }, { coefficient := 2, powers := [(13, 1), (25, 1), (28, 1), (49, 1), (55, 1)] }, { coefficient := -2, powers := [(25, 1), (28, 1), (43, 1), (49, 1), (55, 1)] }, { coefficient := -2, powers := [(28, 1), (34, 1), (37, 1), (49, 1), (55, 1)] }],
  [{ coefficient := -2, powers := [(2, 1), (26, 1), (37, 1), (61, 1)] }],
  [{ coefficient := -2, powers := [(2, 1), (6, 1), (43, 1), (48, 1), (61, 1)] }, { coefficient := -2, powers := [(2, 1), (20, 1), (37, 1), (45, 1), (48, 1), (61, 1)] }, { coefficient := -4, powers := [(12, 1), (28, 1), (43, 1), (49, 1)] }, { coefficient := 2, powers := [(17, 1), (28, 1), (49, 1), (51, 1)] }],
  [{ coefficient := -2, powers := [(30, 1), (49, 1), (52, 1)] }],
  [{ coefficient := -4, powers := [(3, 1), (28, 1), (49, 1), (59, 1)] }, { coefficient := 1, powers := [(24, 1), (44, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [(24, 1), (54, 1)] }],
  [{ coefficient := -2, powers := [(24, 1), (26, 1)] }],
  [{ coefficient := 4, powers := [(3, 1), (28, 1), (49, 1), (55, 1), (59, 1)] }, { coefficient := -2, powers := [(5, 1), (20, 1), (29, 1), (36, 1), (41, 1), (55, 1), (62, 1)] }, { coefficient := -2, powers := [(5, 1), (20, 1), (29, 1), (36, 1), (46, 1), (55, 1), (62, 1)] }, { coefficient := 2, powers := [(6, 1), (28, 1), (49, 1), (55, 1), (59, 1)] }, { coefficient := 2, powers := [(12, 1), (23, 1), (24, 1), (41, 1), (44, 1), (54, 1), (62, 1)] }, { coefficient := 2, powers := [(12, 1), (23, 1), (24, 1), (44, 1), (46, 1), (54, 1), (62, 1)] }, { coefficient := -2, powers := [(19, 1), (20, 1), (24, 1), (29, 1), (41, 1), (55, 1), (62, 1)] }, { coefficient := -2, powers := [(19, 1), (20, 1), (24, 1), (29, 1), (46, 1), (55, 1), (62, 1)] }, { coefficient := -2, powers := [(23, 1), (41, 1), (49, 1), (55, 1)] }, { coefficient := -2, powers := [(23, 1), (46, 1), (49, 1), (55, 1)] }, { coefficient := -1, powers := [(24, 1), (44, 1), (53, 1), (54, 1)] }, { coefficient := -1, powers := [(24, 1), (44, 1), (55, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [(24, 1), (55, 1)] }],
  [{ coefficient := 2, powers := [(12, 1), (26, 1), (57, 1)] }],
  [{ coefficient := -2, powers := [(3, 1), (12, 1), (44, 1), (60, 1)] }, { coefficient := -2, powers := [(12, 1), (44, 1)] }, { coefficient := -2, powers := [(19, 1), (51, 1)] }],
  [{ coefficient := 2, powers := [(2, 1), (6, 1), (43, 1), (61, 1)] }, { coefficient := 2, powers := [(2, 1), (20, 1), (37, 1), (45, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (54, 1), (57, 1)] }],
  [{ coefficient := 2, powers := [(5, 1), (28, 1), (36, 1), (62, 1)] }, { coefficient := 2, powers := [(19, 1), (24, 1), (28, 1), (62, 1)] }, { coefficient := 1, powers := [(24, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (53, 1), (54, 1)] }, { coefficient := 1, powers := [(24, 1), (55, 1), (57, 1)] }],
  [{ coefficient := -2, powers := [(30, 1), (51, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (24, 1), (54, 1), (57, 1)] }],
  [{ coefficient := -2, powers := [(12, 1), (13, 1), (30, 1), (50, 1)] }, { coefficient := -2, powers := [(12, 1), (20, 1), (30, 1), (45, 1), (50, 1)] }, { coefficient := 2, powers := [(12, 1), (30, 1), (43, 1), (50, 1)] }, { coefficient := 2, powers := [(12, 1), (30, 1), (52, 1)] }],
  [{ coefficient := 2, powers := [(18, 1), (30, 1), (49, 1), (52, 1)] }],
  [{ coefficient := 2, powers := [(5, 1), (18, 1), (29, 1), (36, 1), (62, 1)] }, { coefficient := -2, powers := [(9, 1), (17, 1), (28, 1), (49, 1)] }, { coefficient := 2, powers := [(18, 1), (19, 1), (24, 1), (29, 1), (62, 1)] }, { coefficient := -3, powers := [(19, 1), (24, 1), (41, 1)] }, { coefficient := -3, powers := [(19, 1), (24, 1), (46, 1)] }, { coefficient := -2, powers := [(19, 1), (24, 1), (57, 1)] }, { coefficient := 2, powers := [(19, 1), (29, 1), (48, 1)] }],
  [{ coefficient := -2, powers := [(2, 1), (13, 1), (20, 1), (39, 1), (61, 1), (62, 1)] }, { coefficient := 2, powers := [(2, 1), (20, 2), (39, 1), (45, 1), (61, 1), (62, 1)] }, { coefficient := -2, powers := [(2, 1), (25, 1), (39, 1), (43, 1), (61, 1), (62, 1)] }, { coefficient := -2, powers := [(2, 1), (34, 1), (37, 1), (39, 1), (61, 1), (62, 1)] }, { coefficient := -2, powers := [(3, 1), (12, 1), (30, 1), (34, 1), (49, 1), (62, 1)] }, { coefficient := 2, powers := [(12, 1), (13, 1), (20, 1), (30, 1), (49, 1), (62, 1)] }, { coefficient := 2, powers := [(12, 1), (13, 1), (25, 1), (30, 1), (49, 1), (62, 1)] }, { coefficient := 2, powers := [(12, 1), (20, 1), (25, 1), (30, 1), (45, 1), (49, 1), (62, 1)] }, { coefficient := -2, powers := [(12, 1), (25, 1), (30, 1), (43, 1), (49, 1), (62, 1)] }],
  [{ coefficient := 2, powers := [(2, 1), (25, 1), (39, 1), (61, 1)] }, { coefficient := -2, powers := [(12, 1), (25, 1), (30, 1), (49, 1)] }, { coefficient := 4, powers := [(12, 1), (26, 1), (28, 1), (49, 1)] }, { coefficient := -2, powers := [(18, 1), (25, 1), (28, 1), (49, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(24, 1), (26, 1), (44, 1)] }],
  [{ coefficient := -2, powers := [(19, 1), (20, 1), (55, 1)] }],
  [{ coefficient := -2, powers := [(12, 1), (24, 1), (54, 1)] }],
  [{ coefficient := 2, powers := [(2, 1), (5, 1), (36, 1), (62, 1)] }, { coefficient := 2, powers := [(2, 1), (19, 1), (24, 1), (62, 1)] }, { coefficient := -4, powers := [(19, 1), (24, 1)] }],
  [{ coefficient := -2, powers := [(12, 1), (28, 1), (54, 1)] }, { coefficient := -2, powers := [(12, 1), (30, 1)] }],
  [{ coefficient := -2, powers := [(5, 1), (26, 1), (36, 1), (62, 1)] }, { coefficient := -2, powers := [(19, 1), (24, 1), (26, 1), (62, 1)] }],
  [{ coefficient := 2, powers := [(12, 1), (44, 1), (48, 1)] }],
  [{ coefficient := 2, powers := [(12, 1), (18, 1), (23, 1), (44, 1), (54, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (44, 1), (54, 1)] }],
  [{ coefficient := 2, powers := [(13, 1), (28, 1), (49, 1), (55, 1)] }, { coefficient := -2, powers := [(25, 1), (28, 1), (45, 1), (49, 1), (55, 1)] }, { coefficient := -2, powers := [(28, 1), (43, 1), (49, 1), (55, 1)] }],
  [{ coefficient := -2, powers := [(5, 1), (20, 1), (29, 1), (36, 1), (55, 1), (62, 1)] }, { coefficient := -2, powers := [(5, 1), (28, 1), (36, 1), (55, 1), (62, 1)] }, { coefficient := 2, powers := [(12, 1), (23, 1), (24, 1), (44, 1), (54, 1), (62, 1)] }, { coefficient := -2, powers := [(19, 1), (20, 1), (24, 1), (29, 1), (55, 1), (62, 1)] }, { coefficient := -2, powers := [(19, 1), (24, 1), (28, 1), (55, 1), (62, 1)] }, { coefficient := -2, powers := [(23, 1), (49, 1), (55, 1)] }, { coefficient := -2, powers := [(28, 1), (49, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(19, 1), (24, 1), (54, 1)] }],
  [{ coefficient := -2, powers := [(12, 1), (23, 1), (44, 1), (54, 1), (62, 1)] }],
  [{ coefficient := 2, powers := [(49, 1)] }],
  [{ coefficient := 2, powers := [(12, 1), (23, 1), (28, 1), (44, 1), (54, 1), (62, 1)] }],
  [{ coefficient := 2, powers := [(30, 1)] }],
  [{ coefficient := 2, powers := [(24, 1)] }],
  [{ coefficient := 2, powers := [(9, 1), (28, 1), (49, 1), (55, 1)] }],
  [{ coefficient := 2, powers := [(5, 1), (20, 2), (29, 1), (36, 1), (55, 1), (62, 1)] }, { coefficient := 2, powers := [(5, 1), (20, 1), (28, 1), (36, 1), (55, 1), (62, 1)] }, { coefficient := -2, powers := [(12, 1), (20, 1), (23, 1), (24, 1), (44, 1), (54, 1), (62, 1)] }, { coefficient := 2, powers := [(19, 1), (20, 2), (24, 1), (29, 1), (55, 1), (62, 1)] }, { coefficient := 2, powers := [(19, 1), (20, 1), (24, 1), (28, 1), (55, 1), (62, 1)] }, { coefficient := 2, powers := [(20, 1), (23, 1), (49, 1), (55, 1)] }],
  [{ coefficient := 2, powers := [(19, 1)] }],
  [{ coefficient := 2, powers := [(2, 1), (37, 1), (61, 1)] }],
  [{ coefficient := -2, powers := [(12, 1), (24, 1), (57, 1)] }],
  [{ coefficient := 4, powers := [(19, 1), (24, 1), (26, 1)] }],
  [{ coefficient := 2, powers := [(12, 1), (28, 1), (49, 1)] }, { coefficient := 3, powers := [(19, 1), (24, 1), (51, 1)] }],
  [{ coefficient := -2, powers := [(12, 1), (18, 1), (23, 1), (28, 1), (44, 1), (54, 1), (62, 1)] }, { coefficient := 2, powers := [(19, 1), (30, 1), (51, 1)] }],
  [{ coefficient := 2, powers := [(12, 1), (13, 1), (30, 1)] }, { coefficient := 2, powers := [(12, 1), (20, 1), (30, 1), (45, 1)] }, { coefficient := -2, powers := [(12, 1), (30, 1), (43, 1)] }],
  [{ coefficient := 2, powers := [(12, 1), (28, 1), (52, 1)] }],
  [{ coefficient := -2, powers := [(18, 1), (49, 1), (55, 1)] }],
  [{ coefficient := -2, powers := [(5, 1), (18, 1), (20, 1), (36, 1), (55, 1), (62, 1)] }, { coefficient := -2, powers := [(18, 1), (19, 1), (20, 1), (24, 1), (55, 1), (62, 1)] }],
  [{ coefficient := 2, powers := [(12, 1)] }],
  [{ coefficient := -2, powers := [(19, 1), (26, 1)] }],
  [{ coefficient := 2, powers := [(5, 1), (18, 1), (20, 1), (29, 1), (36, 1), (55, 1), (62, 1)] }, { coefficient := -2, powers := [(12, 1), (18, 1), (23, 1), (24, 1), (44, 1), (54, 1), (62, 1)] }, { coefficient := 2, powers := [(18, 1), (19, 1), (20, 1), (24, 1), (29, 1), (55, 1), (62, 1)] }, { coefficient := 2, powers := [(18, 1), (23, 1), (49, 1), (55, 1)] }],
  [{ coefficient := 2, powers := [(12, 1), (24, 1), (44, 1), (54, 1)] }, { coefficient := 2, powers := [(18, 1), (28, 1), (49, 1), (55, 1)] }],
  [{ coefficient := 2, powers := [(2, 1), (39, 1), (50, 1), (61, 1)] }, { coefficient := 2, powers := [(18, 1), (28, 1), (49, 1), (50, 1), (55, 1)] }],
  [{ coefficient := -2, powers := [(2, 1), (20, 1), (39, 1), (45, 1), (61, 1)] }, { coefficient := -2, powers := [(12, 1), (13, 1), (30, 1), (49, 1)] }, { coefficient := 2, powers := [(18, 1), (25, 1), (28, 1), (45, 1), (49, 1), (55, 1)] }, { coefficient := 2, powers := [(18, 1), (28, 1), (43, 1), (49, 1), (55, 1)] }],
  [{ coefficient := -2, powers := [(19, 1), (30, 1)] }],
  [{ coefficient := 2, powers := [(2, 1), (20, 1), (39, 1), (61, 1)] }, { coefficient := -2, powers := [(12, 1), (20, 1), (30, 1), (49, 1)] }, { coefficient := -2, powers := [(18, 1), (25, 1), (28, 1), (49, 1), (55, 1)] }],
  [{ coefficient := -2, powers := [(12, 1), (26, 1), (28, 1), (49, 1)] }, { coefficient := 3, powers := [(19, 1), (20, 1), (24, 1), (55, 1)] }],
  [{ coefficient := -2, powers := [(2, 1), (39, 1), (61, 1)] }, { coefficient := 2, powers := [(12, 1), (30, 1), (49, 1)] }, { coefficient := -2, powers := [(18, 1), (28, 1), (49, 1), (55, 1)] }],
  [{ coefficient := -2, powers := [] }],
  [{ coefficient := -2, powers := [(2, 1), (5, 1), (36, 1), (46, 1), (55, 1), (62, 1)] }, { coefficient := -2, powers := [(2, 1), (19, 1), (24, 1), (46, 1), (55, 1), (62, 1)] }, { coefficient := -2, powers := [(5, 1), (18, 1), (20, 1), (29, 1), (36, 1), (46, 1), (55, 1), (62, 1)] }, { coefficient := -2, powers := [(5, 1), (18, 1), (29, 1), (36, 1), (55, 1), (62, 1)] }, { coefficient := 2, powers := [(9, 1), (17, 1), (28, 1), (49, 1), (55, 1)] }, { coefficient := 2, powers := [(12, 1), (13, 1), (30, 1), (49, 1), (50, 1)] }, { coefficient := 2, powers := [(12, 1), (18, 1), (23, 1), (24, 1), (44, 1), (46, 1), (54, 1), (62, 1)] }, { coefficient := 2, powers := [(12, 1), (18, 1), (23, 1), (28, 1), (44, 1), (48, 1), (52, 1), (54, 1), (62, 1)] }, { coefficient := 2, powers := [(12, 1), (20, 1), (30, 1), (45, 1), (49, 1), (50, 1)] }, { coefficient := 3, powers := [(12, 1), (24, 1), (44, 1), (54, 1), (57, 1)] }, { coefficient := 2, powers := [(12, 1), (26, 1), (28, 1), (38, 1), (49, 1), (60, 1)] }, { coefficient := 2, powers := [(12, 1), (26, 1), (28, 1), (41, 1), (49, 1), (57, 1)] }, { coefficient := 2, powers := [(12, 1), (26, 1), (28, 1), (46, 1), (49, 1), (52, 1)] }, { coefficient := -2, powers := [(12, 1), (28, 1), (46, 1), (49, 1), (54, 1)] }, { coefficient := -2, powers := [(12, 1), (30, 1), (37, 1), (49, 1), (59, 1)] }, { coefficient := -2, powers := [(12, 1), (30, 1), (43, 1), (49, 1), (50, 1)] }, { coefficient := -2, powers := [(18, 1), (19, 1), (20, 1), (24, 1), (29, 1), (46, 1), (55, 1), (62, 1)] }, { coefficient := -2, powers := [(18, 1), (19, 1), (24, 1), (29, 1), (55, 1), (62, 1)] }, { coefficient := -2, powers := [(18, 1), (23, 1), (46, 1), (49, 1), (55, 1)] }, { coefficient := 2, powers := [(18, 1), (28, 1), (37, 1), (49, 1), (55, 1), (59, 1)] }, { coefficient := -2, powers := [(18, 1), (28, 1), (43, 1), (49, 1), (50, 1), (55, 1)] }, { coefficient := -2, powers := [(18, 1), (28, 1), (49, 1), (52, 1), (55, 1)] }, { coefficient := -2, powers := [(18, 1), (30, 1), (49, 1), (51, 1), (52, 1)] }, { coefficient := -3, powers := [(19, 1), (20, 1), (24, 1), (38, 1), (55, 1), (60, 1)] }, { coefficient := -3, powers := [(19, 1), (20, 1), (24, 1), (41, 1), (55, 1), (57, 1)] }, { coefficient := -3, powers := [(19, 1), (20, 1), (24, 1), (46, 1), (52, 1), (55, 1)] }, { coefficient := -4, powers := [(19, 1), (24, 1), (26, 1), (46, 1), (53, 1)] }, { coefficient := 3, powers := [(19, 1), (24, 1), (41, 1), (55, 1)] }, { coefficient := -3, powers := [(19, 1), (24, 1), (46, 1), (51, 1), (54, 1)] }, { coefficient := 7, powers := [(19, 1), (24, 1), (46, 1), (55, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (53, 1), (54, 1)] }, { coefficient := 2, powers := [(19, 1), (24, 1), (55, 1), (57, 1)] }, { coefficient := -2, powers := [(19, 1), (29, 1), (48, 1), (55, 1)] }, { coefficient := -2, powers := [(19, 1), (30, 1), (48, 1), (51, 1), (52, 1)] }, { coefficient := 2, powers := [(19, 1), (30, 1), (48, 1), (53, 1)] }],
  [{ coefficient := 2, powers := [(2, 1), (13, 1), (20, 1), (39, 1), (50, 1), (61, 1)] }, { coefficient := -2, powers := [(2, 1), (20, 2), (39, 1), (45, 1), (50, 1), (61, 1)] }, { coefficient := 2, powers := [(2, 1), (25, 1), (39, 1), (43, 1), (50, 1), (61, 1)] }, { coefficient := 2, powers := [(2, 1), (34, 1), (37, 1), (39, 1), (50, 1), (61, 1)] }, { coefficient := 2, powers := [(3, 1), (12, 1), (30, 1), (34, 1), (49, 1), (50, 1)] }, { coefficient := -2, powers := [(5, 1), (36, 1), (55, 1)] }, { coefficient := -2, powers := [(12, 1), (13, 1), (20, 1), (30, 1), (49, 1), (50, 1)] }, { coefficient := -2, powers := [(12, 1), (13, 1), (25, 1), (30, 1), (49, 1), (50, 1)] }, { coefficient := -2, powers := [(12, 1), (20, 1), (25, 1), (30, 1), (45, 1), (49, 1), (50, 1)] }, { coefficient := 2, powers := [(12, 1), (23, 1), (44, 1), (48, 1), (54, 1)] }, { coefficient := 2, powers := [(12, 1), (25, 1), (30, 1), (43, 1), (49, 1), (50, 1)] }, { coefficient := -2, powers := [(19, 1), (24, 1), (55, 1)] }],
  [{ coefficient := 2, powers := [(2, 1), (6, 1), (26, 1), (43, 1), (48, 1), (61, 1)] }, { coefficient := 2, powers := [(2, 1), (6, 1), (34, 1), (39, 1), (61, 1)] }, { coefficient := 2, powers := [(2, 1), (13, 1), (18, 1), (20, 1), (28, 1), (39, 1), (61, 1), (62, 1)] }, { coefficient := -2, powers := [(2, 1), (18, 1), (20, 2), (28, 1), (39, 1), (45, 1), (61, 1), (62, 1)] }, { coefficient := 2, powers := [(2, 1), (18, 1), (25, 1), (28, 1), (39, 1), (43, 1), (61, 1), (62, 1)] }, { coefficient := 2, powers := [(2, 1), (18, 1), (28, 1), (34, 1), (37, 1), (39, 1), (61, 1), (62, 1)] }, { coefficient := 2, powers := [(2, 1), (20, 1), (25, 1), (39, 1), (45, 1), (61, 1)] }, { coefficient := 2, powers := [(2, 1), (20, 1), (26, 1), (37, 1), (45, 1), (48, 1), (61, 1)] }, { coefficient := 2, powers := [(3, 1), (12, 1), (18, 1), (28, 1), (30, 1), (34, 1), (49, 1), (62, 1)] }, { coefficient := -2, powers := [(6, 1), (12, 1), (30, 1), (34, 1), (49, 1)] }, { coefficient := 2, powers := [(6, 1), (18, 1), (28, 1), (34, 1), (49, 1), (55, 1)] }, { coefficient := -2, powers := [(12, 1), (13, 1), (18, 1), (20, 1), (28, 1), (30, 1), (49, 1), (62, 1)] }, { coefficient := -2, powers := [(12, 1), (13, 1), (18, 1), (25, 1), (28, 1), (30, 1), (49, 1), (62, 1)] }, { coefficient := 2, powers := [(12, 1), (13, 1), (25, 1), (30, 1), (49, 1)] }, { coefficient := -4, powers := [(12, 1), (13, 1), (26, 1), (28, 1), (49, 1)] }, { coefficient := -2, powers := [(12, 1), (18, 1), (20, 1), (25, 1), (28, 1), (30, 1), (45, 1), (49, 1), (62, 1)] }, { coefficient := 2, powers := [(12, 1), (18, 1), (25, 1), (28, 1), (30, 1), (43, 1), (49, 1), (62, 1)] }, { coefficient := 4, powers := [(12, 1), (26, 1), (28, 1), (43, 1), (49, 1)] }, { coefficient := 2, powers := [(13, 1), (18, 1), (25, 1), (28, 1), (49, 1), (55, 1)] }, { coefficient := -2, powers := [(17, 1), (26, 1), (28, 1), (49, 1), (51, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (19, 1), (30, 1), (57, 1)] }, { coefficient := 2, powers := [(8, 1), (36, 1)] }, { coefficient := 2, powers := [(19, 1), (26, 1), (29, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (2, 1), (39, 1), (40, 1), (61, 1)] }, { coefficient := -2, powers := [(0, 1), (12, 1), (30, 1), (40, 1), (49, 1)] }, { coefficient := 2, powers := [(0, 1), (18, 1), (28, 1), (40, 1), (49, 1), (55, 1)] }, { coefficient := 2, powers := [(2, 1), (3, 1), (31, 1), (39, 1), (61, 1)] }, { coefficient := -2, powers := [(2, 1), (20, 1), (39, 1), (50, 1), (61, 1)] }, { coefficient := -2, powers := [(3, 1), (12, 1), (30, 1), (31, 1), (49, 1)] }, { coefficient := 2, powers := [(3, 1), (18, 1), (28, 1), (31, 1), (49, 1), (55, 1)] }, { coefficient := 2, powers := [(9, 1), (18, 1), (25, 1), (28, 1), (49, 1), (55, 1)] }, { coefficient := -2, powers := [(18, 1), (20, 1), (28, 1), (49, 1), (50, 1), (55, 1)] }],
  [{ coefficient := 2, powers := [(2, 1), (42, 1)] }, { coefficient := 2, powers := [(5, 1), (33, 1)] }, { coefficient := 2, powers := [(12, 1), (20, 1), (24, 1), (57, 1)] }, { coefficient := -2, powers := [(12, 1), (21, 1), (28, 1), (52, 1)] }, { coefficient := -2, powers := [(12, 1), (24, 1)] }, { coefficient := -1, powers := [(18, 1), (20, 1), (24, 1), (53, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
/-- Lean replays the exact selected-row integer certificate. -/
theorem constantIdentity :
    ∑ index, (multipliers index).toPoly *
      (selectedEquations index).toPoly = C (2 : ℤ) := by
  simp (config := { maxSteps := 1000000 })
    [Fin.sum_univ_succ, multipliers, selectedEquations,
    SparsePoly.toPoly, SparseTerm.toPoly]
  ring

/-- The selected rows have no common zero in a characteristic-zero ring. -/
theorem selectedHasNoCommonZero {R : Type*} [CommRing R] [Nontrivial R] [CharZero R]
    (values : Fin 65 → R) :
    ¬ ∀ index : Fin 70,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((2 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (2 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (2 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component37.SelectedLeafB1_2_2.selectedHasNoCommonZero

end Krenn.Component37.SelectedLeafB1_2_2
