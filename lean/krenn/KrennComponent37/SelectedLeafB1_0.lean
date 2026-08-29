import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component37.SelectedLeafB1_0

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "aa71a34ba56a6002a49bc0c5856bcc6ed4e461c7040092a1d0be5e17b9900b2c"
def certificateSHA256 : String := "c8d84cfd28d35406d8e8714d2f6c91a17fb6aee60c22b19b74042c839dbdacba"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 53 → Fin 664 := ![
  167,
  171,
  175,
  178,
  179,
  180,
  181,
  183,
  256,
  260,
  280,
  295,
  296,
  307,
  310,
  311,
  312,
  313,
  315,
  316,
  317,
  340,
  342,
  343,
  393,
  410,
  425,
  430,
  432,
  433,
  440,
  445,
  446,
  449,
  453,
  454,
  458,
  472,
  475,
  479,
  487,
  499,
  526,
  580,
  581,
  608,
  619,
  645,
  657,
  658,
  660,
  662,
  663
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 53 → SparsePoly (Fin 63) := ![
  [{ coefficient := 1, powers := [(12, 1), (25, 1)] }, { coefficient := 1, powers := [(18, 1), (20, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (20, 1)] }, { coefficient := 1, powers := [(18, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (47, 1)] }, { coefficient := -1, powers := [(29, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (55, 1)] }, { coefficient := 1, powers := [(30, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (44, 1)] }, { coefficient := 1, powers := [(28, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (54, 1)] }, { coefficient := 1, powers := [(30, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(28, 1), (53, 1)] }, { coefficient := -1, powers := [(29, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (25, 1), (46, 1)] }, { coefficient := 1, powers := [(18, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (26, 1), (46, 1)] }, { coefficient := 1, powers := [(18, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (25, 1), (49, 1)] }, { coefficient := 1, powers := [(19, 1), (21, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (49, 1)] }, { coefficient := 1, powers := [(21, 1), (44, 1)] }, { coefficient := 1, powers := [(25, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (51, 1)] }, { coefficient := 1, powers := [(20, 1), (51, 1)] }, { coefficient := 1, powers := [(25, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (46, 1)] }, { coefficient := 1, powers := [(12, 1), (57, 1)] }, { coefficient := 1, powers := [(18, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (41, 1)] }, { coefficient := 1, powers := [(19, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (52, 1)] }, { coefficient := 1, powers := [(24, 1), (57, 1)] }, { coefficient := 1, powers := [(29, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (54, 1)] }, { coefficient := 1, powers := [(30, 1), (41, 1)] }, { coefficient := 1, powers := [(30, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(20, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(44, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1), (51, 1)] }, { coefficient := 1, powers := [(25, 1), (46, 1), (51, 1)] }, { coefficient := 1, powers := [(51, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1), (55, 1)] }, { coefficient := 1, powers := [(26, 1), (46, 1), (51, 1)] }, { coefficient := 1, powers := [(55, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (49, 1), (52, 1)] }, { coefficient := 1, powers := [(21, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(49, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (44, 1)] }, { coefficient := 1, powers := [(19, 1), (23, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (46, 1), (51, 1)] }, { coefficient := 1, powers := [(12, 1), (28, 1), (46, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (47, 1), (51, 1)] }, { coefficient := 1, powers := [(12, 1), (28, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (29, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (20, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1)] }, { coefficient := 1, powers := [(18, 1), (20, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (25, 1), (41, 1)] }, { coefficient := 1, powers := [(18, 1), (25, 1), (46, 1)] }, { coefficient := 1, powers := [(18, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (48, 1)] }, { coefficient := 1, powers := [(6, 1), (21, 1), (60, 1)] }, { coefficient := 1, powers := [(21, 1)] }, { coefficient := 1, powers := [(25, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (46, 1)] }, { coefficient := 1, powers := [(18, 1), (28, 1), (41, 1)] }, { coefficient := 1, powers := [(18, 1), (28, 1), (46, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (48, 1)] }, { coefficient := 1, powers := [(5, 1), (28, 1), (60, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1)] }, { coefficient := 1, powers := [(18, 1), (28, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (49, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1)] }, { coefficient := 1, powers := [(18, 1), (28, 1), (49, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (36, 1)] }, { coefficient := 1, powers := [(23, 1), (44, 1)] }, { coefficient := 1, powers := [(28, 1), (44, 1)] }, { coefficient := 1, powers := [(36, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (60, 1)] }, { coefficient := 1, powers := [(18, 1), (21, 1), (52, 1)] }, { coefficient := 1, powers := [(18, 1), (21, 1), (57, 1)] }, { coefficient := 1, powers := [(18, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (61, 1)] }, { coefficient := 1, powers := [(12, 1), (49, 1)] }, { coefficient := 1, powers := [(19, 1), (21, 1), (53, 1)] }, { coefficient := 1, powers := [(19, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (60, 1)] }, { coefficient := 1, powers := [(18, 1), (26, 1), (41, 1)] }, { coefficient := 1, powers := [(18, 1), (26, 1), (46, 1)] }, { coefficient := 1, powers := [(18, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (41, 1)] }, { coefficient := 1, powers := [(18, 1), (46, 1)] }, { coefficient := 1, powers := [(18, 1), (52, 1)] }, { coefficient := 1, powers := [(18, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (55, 1)] }, { coefficient := 1, powers := [(30, 1), (42, 1)] }, { coefficient := 1, powers := [(30, 1), (48, 1), (51, 1)] }, { coefficient := 1, powers := [(33, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (38, 1), (61, 1)] }, { coefficient := 1, powers := [(0, 1), (47, 1), (53, 1)] }, { coefficient := 1, powers := [(44, 1), (53, 1)] }, { coefficient := 1, powers := [(47, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1), (54, 1)] }, { coefficient := 1, powers := [(26, 1), (41, 1)] }, { coefficient := 1, powers := [(26, 1), (46, 1)] }, { coefficient := 1, powers := [(54, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1), (52, 1)] }, { coefficient := 1, powers := [(41, 1), (44, 1)] }, { coefficient := 1, powers := [(44, 1), (52, 1)] }, { coefficient := 1, powers := [(47, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (48, 1), (52, 1)] }, { coefficient := 1, powers := [(21, 1), (52, 1)] }, { coefficient := 1, powers := [(21, 1), (57, 1)] }, { coefficient := 1, powers := [(48, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (37, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1)] }, { coefficient := 1, powers := [(18, 1), (28, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (28, 1), (60, 1)] }, { coefficient := 1, powers := [(6, 1), (23, 1), (60, 1)] }, { coefficient := 1, powers := [(23, 1)] }, { coefficient := 1, powers := [(28, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (29, 1), (60, 1)] }, { coefficient := 1, powers := [(28, 1), (41, 1)] }, { coefficient := 1, powers := [(28, 1), (46, 1)] }, { coefficient := 1, powers := [(29, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1)] }, { coefficient := 1, powers := [(6, 1), (60, 1)] }, { coefficient := 1, powers := [(25, 1), (41, 1)] }, { coefficient := 1, powers := [(25, 1), (46, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (52, 1)] }, { coefficient := 1, powers := [(3, 1), (60, 1)] }, { coefficient := 1, powers := [(20, 1), (52, 1)] }, { coefficient := 1, powers := [(20, 1), (57, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (41, 1), (58, 1)] }, { coefficient := 1, powers := [(0, 1), (47, 1), (54, 1)] }, { coefficient := 1, powers := [(26, 1), (41, 1), (44, 1)] }, { coefficient := 1, powers := [(26, 1), (47, 1)] }, { coefficient := 1, powers := [(44, 1), (54, 1)] }, { coefficient := 1, powers := [(58, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (39, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (48, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (60, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (54, 1)] }, { coefficient := 1, powers := [(18, 1), (30, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (38, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (41, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(41, 1)] }, { coefficient := 1, powers := [(46, 1)] }, { coefficient := 1, powers := [(52, 1)] }, { coefficient := 1, powers := [(57, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (39, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (42, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (49, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (49, 1)] }, { coefficient := 1, powers := [(8, 1), (36, 1), (42, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (58, 1)] }, { coefficient := 1, powers := [(12, 1), (30, 1), (49, 1)] }, { coefficient := 1, powers := [(12, 1), (36, 1), (39, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (55, 1)] }, { coefficient := 1, powers := [(19, 1), (30, 1), (42, 1)] }, { coefficient := 1, powers := [(19, 1), (33, 1), (39, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(41, 1)] }],
  [{ coefficient := 1, powers := [(42, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 53 → SparsePoly (Fin 63) := ![
  [{ coefficient := -2, powers := [(29, 1), (49, 1), (54, 1)] }],
  [{ coefficient := -2, powers := [(18, 1), (21, 1), (28, 1), (30, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (28, 1), (36, 1), (39, 1), (52, 1), (62, 1)] }, { coefficient := -1, powers := [(12, 1), (28, 1), (36, 1), (39, 1), (57, 1), (62, 1)] }, { coefficient := -2, powers := [(28, 1), (39, 1), (52, 1), (61, 1)] }, { coefficient := -2, powers := [(28, 1), (39, 1), (57, 1), (61, 1)] }, { coefficient := -2, powers := [(28, 1), (49, 1), (52, 1), (55, 1)] }, { coefficient := -2, powers := [(28, 1), (49, 1), (55, 1), (57, 1)] }],
  [{ coefficient := 2, powers := [(2, 1), (18, 1), (21, 1), (55, 1), (62, 1)] }, { coefficient := 2, powers := [(5, 1), (18, 1), (20, 1), (33, 1), (54, 1), (62, 1)] }, { coefficient := 2, powers := [(5, 1), (18, 1), (26, 1), (33, 1), (62, 1)] }, { coefficient := -2, powers := [(8, 1), (18, 1), (21, 1), (33, 1), (62, 1)] }, { coefficient := -1, powers := [(12, 1), (18, 1), (20, 1), (23, 1), (39, 1), (60, 1), (62, 1)] }, { coefficient := 2, powers := [(12, 1), (18, 1), (20, 1), (24, 1), (54, 1), (62, 1)] }, { coefficient := -1, powers := [(12, 1), (18, 1), (20, 1), (28, 1), (39, 1), (60, 1), (62, 1)] }, { coefficient := 2, powers := [(12, 1), (18, 1), (24, 1), (26, 1), (62, 1)] }, { coefficient := -2, powers := [(18, 2), (20, 1), (24, 1), (55, 1), (62, 1)] }],
  [{ coefficient := 2, powers := [(18, 1), (49, 1)] }],
  [{ coefficient := -2, powers := [(18, 1), (55, 1)] }],
  [{ coefficient := 2, powers := [(18, 1), (37, 1), (61, 1)] }, { coefficient := -2, powers := [(19, 1), (51, 1)] }],
  [{ coefficient := 2, powers := [(18, 1), (19, 1), (21, 1), (30, 1), (62, 1)] }],
  [{ coefficient := -2, powers := [(30, 1), (49, 1)] }],
  [{ coefficient := 2, powers := [(28, 1), (49, 1)] }],
  [{ coefficient := -2, powers := [(30, 1), (53, 1)] }],
  [{ coefficient := 2, powers := [(18, 1), (30, 1), (53, 1)] }],
  [{ coefficient := -2, powers := [(2, 1), (46, 1), (49, 1), (54, 1)] }],
  [{ coefficient := -2, powers := [(20, 1), (28, 1), (49, 1), (54, 1)] }],
  [{ coefficient := -2, powers := [(2, 1), (21, 1), (23, 1), (55, 1), (62, 1)] }, { coefficient := -2, powers := [(5, 1), (20, 1), (23, 1), (33, 1), (54, 1), (62, 1)] }, { coefficient := -2, powers := [(5, 1), (23, 1), (26, 1), (33, 1), (62, 1)] }, { coefficient := 2, powers := [(8, 1), (21, 1), (23, 1), (33, 1), (62, 1)] }, { coefficient := 1, powers := [(12, 1), (20, 1), (23, 2), (39, 1), (60, 1), (62, 1)] }, { coefficient := -2, powers := [(12, 1), (20, 1), (23, 1), (24, 1), (54, 1), (62, 1)] }, { coefficient := 1, powers := [(12, 1), (20, 1), (23, 1), (28, 1), (39, 1), (60, 1), (62, 1)] }, { coefficient := -2, powers := [(12, 1), (23, 1), (24, 1), (26, 1), (62, 1)] }, { coefficient := 2, powers := [(18, 1), (20, 1), (23, 1), (24, 1), (55, 1), (62, 1)] }],
  [{ coefficient := -2, powers := [(18, 1), (25, 1), (37, 1), (54, 1), (61, 1)] }],
  [{ coefficient := 2, powers := [(12, 1), (25, 1), (49, 1)] }],
  [{ coefficient := -2, powers := [(5, 1), (33, 1), (54, 1)] }, { coefficient := 1, powers := [(12, 1), (23, 1), (39, 1), (60, 1)] }, { coefficient := -2, powers := [(12, 1), (24, 1), (54, 1)] }, { coefficient := 1, powers := [(12, 1), (28, 1), (39, 1), (60, 1)] }, { coefficient := 2, powers := [(18, 1), (24, 1), (55, 1)] }],
  [{ coefficient := 2, powers := [(2, 1), (49, 1), (54, 1)] }],
  [{ coefficient := 2, powers := [(2, 1), (49, 1)] }, { coefficient := -2, powers := [(19, 1), (24, 1)] }],
  [{ coefficient := -2, powers := [(2, 1), (55, 1)] }, { coefficient := 2, powers := [(8, 1), (33, 1)] }],
  [{ coefficient := 2, powers := [(2, 1), (21, 1), (55, 1), (62, 1)] }, { coefficient := 2, powers := [(5, 1), (20, 1), (33, 1), (54, 1), (62, 1)] }, { coefficient := 2, powers := [(5, 1), (26, 1), (33, 1), (62, 1)] }, { coefficient := -2, powers := [(8, 1), (21, 1), (33, 1), (62, 1)] }, { coefficient := -1, powers := [(12, 1), (20, 1), (23, 1), (39, 1), (60, 1), (62, 1)] }, { coefficient := 2, powers := [(12, 1), (20, 1), (24, 1), (54, 1), (62, 1)] }, { coefficient := -1, powers := [(12, 1), (20, 1), (28, 1), (39, 1), (60, 1), (62, 1)] }, { coefficient := 2, powers := [(12, 1), (24, 1), (26, 1), (62, 1)] }, { coefficient := -2, powers := [(18, 1), (20, 1), (24, 1), (55, 1), (62, 1)] }],
  [{ coefficient := 2, powers := [(20, 1), (49, 1), (54, 1)] }],
  [{ coefficient := 2, powers := [(18, 1), (21, 1), (30, 1), (62, 1)] }],
  [{ coefficient := 2, powers := [(28, 1), (49, 1), (54, 1)] }],
  [{ coefficient := 2, powers := [(8, 1), (24, 1), (25, 1), (29, 1), (61, 1), (62, 1)] }, { coefficient := -1, powers := [(12, 1), (20, 1), (29, 1), (36, 1), (39, 1), (62, 1)] }, { coefficient := -1, powers := [(12, 1), (23, 1), (36, 1), (39, 1), (62, 1)] }, { coefficient := -1, powers := [(12, 1), (28, 1), (36, 1), (39, 1), (62, 1)] }, { coefficient := -2, powers := [(23, 1), (39, 1), (61, 1)] }, { coefficient := -2, powers := [(23, 1), (49, 1), (55, 1)] }, { coefficient := -2, powers := [(24, 1), (37, 1), (54, 1), (61, 1)] }, { coefficient := -2, powers := [(28, 1), (39, 1), (61, 1)] }, { coefficient := -2, powers := [(28, 1), (49, 1), (55, 1)] }],
  [{ coefficient := 2, powers := [(18, 1), (29, 1), (37, 1), (54, 1), (61, 1)] }],
  [{ coefficient := -2, powers := [(8, 1), (24, 1), (25, 1), (61, 1), (62, 1)] }, { coefficient := 1, powers := [(12, 1), (20, 1), (36, 1), (39, 1), (62, 1)] }],
  [{ coefficient := 2, powers := [(37, 1), (54, 1), (61, 1)] }],
  [{ coefficient := 2, powers := [(55, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (39, 1), (60, 1)] }],
  [{ coefficient := -2, powers := [(28, 1), (37, 1), (54, 1), (61, 1)] }, { coefficient := 2, powers := [(30, 1), (37, 1), (61, 1)] }],
  [{ coefficient := 2, powers := [(30, 1)] }],
  [{ coefficient := -2, powers := [(6, 1), (24, 1), (61, 1)] }, { coefficient := 2, powers := [(24, 1), (37, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (25, 1), (28, 1), (36, 1), (39, 1), (62, 1)] }, { coefficient := 2, powers := [(21, 1), (28, 1), (37, 1), (54, 1), (61, 1)] }, { coefficient := -2, powers := [(21, 1), (30, 1), (37, 1), (61, 1)] }, { coefficient := 2, powers := [(24, 1), (25, 1), (37, 1), (54, 1), (61, 1)] }, { coefficient := 2, powers := [(25, 1), (28, 1), (39, 1), (61, 1)] }, { coefficient := 2, powers := [(25, 1), (28, 1), (49, 1), (55, 1)] }],
  [{ coefficient := 2, powers := [(19, 1)] }],
  [{ coefficient := -2, powers := [(18, 1), (21, 1), (30, 1)] }],
  [{ coefficient := -2, powers := [(2, 1), (49, 1), (51, 1)] }, { coefficient := 2, powers := [(6, 1), (18, 1), (24, 1), (61, 1)] }, { coefficient := -2, powers := [(12, 1), (28, 1), (49, 1)] }, { coefficient := -2, powers := [(18, 1), (24, 1), (37, 1), (61, 1)] }, { coefficient := 2, powers := [(19, 1), (24, 1), (51, 1)] }],
  [{ coefficient := -2, powers := [(5, 1), (26, 1), (33, 1)] }, { coefficient := -2, powers := [(12, 1), (24, 1), (26, 1)] }],
  [{ coefficient := -2, powers := [(18, 1), (30, 1), (37, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (36, 1), (39, 1), (62, 1)] }, { coefficient := 2, powers := [(39, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (18, 1), (36, 1), (39, 1), (62, 1)] }, { coefficient := -2, powers := [(18, 1), (39, 1), (61, 1)] }, { coefficient := -2, powers := [(18, 1), (49, 1), (55, 1)] }],
  [{ coefficient := 2, powers := [(8, 1), (18, 1), (24, 1), (25, 1), (61, 1), (62, 1)] }, { coefficient := -1, powers := [(12, 1), (18, 1), (20, 1), (36, 1), (39, 1), (62, 1)] }, { coefficient := -2, powers := [(18, 1), (21, 1), (37, 1), (54, 1), (61, 1)] }],
  [{ coefficient := -2, powers := [(8, 1), (18, 1), (24, 1), (25, 1), (29, 1), (61, 1), (62, 1)] }, { coefficient := 2, powers := [(8, 1), (24, 1), (61, 1)] }, { coefficient := 1, powers := [(12, 1), (18, 1), (20, 1), (29, 1), (36, 1), (39, 1), (62, 1)] }, { coefficient := 1, powers := [(12, 1), (18, 1), (23, 1), (36, 1), (39, 1), (62, 1)] }, { coefficient := 2, powers := [(18, 1), (23, 1), (39, 1), (61, 1)] }, { coefficient := 2, powers := [(18, 1), (23, 1), (49, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (18, 1), (28, 1), (36, 1), (39, 1), (62, 1)] }, { coefficient := 1, powers := [(12, 1), (36, 1), (39, 1)] }, { coefficient := 2, powers := [(18, 1), (28, 1), (39, 1), (61, 1)] }, { coefficient := 2, powers := [(18, 1), (28, 1), (49, 1), (55, 1)] }],
  [{ coefficient := 2, powers := [(5, 1), (33, 1)] }, { coefficient := 2, powers := [(12, 1), (24, 1)] }],
  [{ coefficient := -2, powers := [(37, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (20, 1), (36, 1), (39, 1)] }, { coefficient := 2, powers := [(18, 1), (21, 1), (30, 1), (37, 1), (61, 1)] }],
  [{ coefficient := -2, powers := [] }],
  [{ coefficient := 2, powers := [(2, 1), (46, 1), (49, 1), (51, 1), (54, 1)] }, { coefficient := -2, powers := [(2, 1), (46, 1), (49, 1), (55, 1)] }, { coefficient := 2, powers := [(2, 1), (49, 1), (52, 1), (55, 1)] }, { coefficient := 2, powers := [(5, 1), (26, 1), (33, 1), (47, 1), (52, 1)] }, { coefficient := 2, powers := [(5, 1), (33, 1), (44, 1), (52, 1), (54, 1)] }, { coefficient := -2, powers := [(5, 1), (33, 1), (47, 1), (54, 1)] }, { coefficient := -2, powers := [(6, 1), (18, 1), (24, 1), (46, 1), (54, 1), (61, 1)] }, { coefficient := 2, powers := [(8, 1), (18, 1), (24, 1), (25, 1), (29, 1), (46, 1), (61, 1), (62, 1)] }, { coefficient := -2, powers := [(8, 1), (24, 1), (46, 1), (61, 1)] }, { coefficient := -2, powers := [(8, 1), (33, 1), (49, 1), (52, 1)] }, { coefficient := -1, powers := [(12, 1), (18, 1), (20, 1), (29, 1), (36, 1), (39, 1), (46, 1), (62, 1)] }, { coefficient := -1, powers := [(12, 1), (18, 1), (23, 1), (36, 1), (39, 1), (46, 1), (62, 1)] }, { coefficient := -1, powers := [(12, 1), (18, 1), (28, 1), (36, 1), (39, 1), (52, 1), (62, 1)] }, { coefficient := 1, powers := [(12, 1), (20, 1), (36, 1), (38, 1), (39, 1), (60, 1)] }, { coefficient := 1, powers := [(12, 1), (20, 1), (36, 1), (39, 1), (46, 1), (52, 1)] }, { coefficient := -1, powers := [(12, 1), (23, 1), (39, 1), (44, 1), (52, 1), (60, 1)] }, { coefficient := 2, powers := [(12, 1), (24, 1), (26, 1), (47, 1), (52, 1)] }, { coefficient := 2, powers := [(12, 1), (24, 1), (44, 1), (52, 1), (54, 1)] }, { coefficient := -2, powers := [(12, 1), (24, 1), (47, 1), (54, 1)] }, { coefficient := -1, powers := [(12, 1), (28, 1), (39, 1), (44, 1), (52, 1), (60, 1)] }, { coefficient := 2, powers := [(12, 1), (28, 1), (46, 1), (49, 1), (54, 1)] }, { coefficient := -1, powers := [(12, 1), (36, 1), (39, 1), (52, 1)] }, { coefficient := -2, powers := [(18, 1), (21, 1), (30, 1), (37, 1), (38, 1), (60, 1), (61, 1)] }, { coefficient := -2, powers := [(18, 1), (21, 1), (30, 1), (37, 1), (46, 1), (52, 1), (61, 1)] }, { coefficient := 2, powers := [(18, 1), (21, 1), (30, 1), (38, 1), (61, 1)] }, { coefficient := 2, powers := [(18, 1), (21, 1), (30, 1), (47, 1), (53, 1)] }, { coefficient := -2, powers := [(18, 1), (23, 1), (39, 1), (46, 1), (61, 1)] }, { coefficient := -2, powers := [(18, 1), (23, 1), (46, 1), (49, 1), (55, 1)] }, { coefficient := 2, powers := [(18, 1), (24, 1), (37, 1), (46, 1), (54, 1), (61, 1)] }, { coefficient := -2, powers := [(18, 1), (24, 1), (44, 1), (52, 1), (55, 1)] }, { coefficient := -2, powers := [(18, 1), (28, 1), (39, 1), (52, 1), (61, 1)] }, { coefficient := -2, powers := [(18, 1), (28, 1), (49, 1), (52, 1), (55, 1)] }, { coefficient := -2, powers := [(18, 1), (29, 1), (37, 1), (48, 1), (54, 1), (61, 1)] }, { coefficient := 2, powers := [(18, 1), (30, 1), (37, 1), (48, 1), (52, 1), (61, 1)] }, { coefficient := -2, powers := [(18, 1), (30, 1), (49, 1), (53, 1)] }, { coefficient := -2, powers := [(19, 1), (24, 1), (46, 1), (51, 1), (54, 1)] }, { coefficient := 2, powers := [(19, 1), (24, 1), (46, 1), (55, 1)] }],
  [{ coefficient := -2, powers := [(2, 1), (21, 1), (44, 1), (52, 1), (55, 1)] }, { coefficient := -2, powers := [(5, 1), (20, 1), (33, 1), (44, 1), (52, 1), (54, 1)] }, { coefficient := -2, powers := [(5, 1), (26, 1), (33, 1), (44, 1), (52, 1)] }, { coefficient := 2, powers := [(8, 1), (21, 1), (33, 1), (44, 1), (52, 1)] }, { coefficient := 2, powers := [(8, 1), (24, 1), (25, 1), (46, 1), (61, 1)] }, { coefficient := 1, powers := [(12, 1), (20, 1), (23, 1), (39, 1), (44, 1), (52, 1), (60, 1)] }, { coefficient := -2, powers := [(12, 1), (20, 1), (24, 1), (44, 1), (52, 1), (54, 1)] }, { coefficient := 1, powers := [(12, 1), (20, 1), (28, 1), (39, 1), (44, 1), (52, 1), (60, 1)] }, { coefficient := -1, powers := [(12, 1), (20, 1), (36, 1), (39, 1), (46, 1)] }, { coefficient := -2, powers := [(12, 1), (24, 1), (26, 1), (44, 1), (52, 1)] }, { coefficient := -1, powers := [(12, 1), (36, 1), (37, 1), (39, 1), (60, 1)] }, { coefficient := -1, powers := [(12, 1), (36, 1), (39, 1)] }, { coefficient := 2, powers := [(18, 1), (20, 1), (24, 1), (44, 1), (52, 1), (55, 1)] }, { coefficient := -2, powers := [(18, 1), (21, 1), (30, 1), (47, 1), (51, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (5, 1), (33, 1), (58, 1)] }, { coefficient := 1, powers := [(0, 1), (12, 1), (20, 1), (36, 1), (39, 1), (57, 1)] }, { coefficient := -2, powers := [(0, 1), (12, 1), (24, 1), (58, 1)] }, { coefficient := -2, powers := [(0, 1), (18, 1), (21, 1), (30, 1), (37, 1), (57, 1), (61, 1)] }, { coefficient := 2, powers := [(2, 1), (19, 1), (21, 1), (23, 1), (55, 1), (62, 1)] }, { coefficient := 2, powers := [(2, 1), (26, 1), (49, 1), (51, 1)] }, { coefficient := 2, powers := [(5, 1), (19, 1), (20, 1), (23, 1), (33, 1), (54, 1), (62, 1)] }, { coefficient := 2, powers := [(5, 1), (19, 1), (23, 1), (26, 1), (33, 1), (62, 1)] }, { coefficient := -2, powers := [(8, 1), (19, 1), (21, 1), (23, 1), (33, 1), (62, 1)] }, { coefficient := -2, powers := [(8, 1), (24, 1), (25, 1), (61, 1)] }, { coefficient := -1, powers := [(12, 1), (19, 1), (20, 1), (23, 2), (39, 1), (60, 1), (62, 1)] }, { coefficient := 2, powers := [(12, 1), (19, 1), (20, 1), (23, 1), (24, 1), (54, 1), (62, 1)] }, { coefficient := -1, powers := [(12, 1), (19, 1), (20, 1), (23, 1), (28, 1), (39, 1), (60, 1), (62, 1)] }, { coefficient := 2, powers := [(12, 1), (19, 1), (23, 1), (24, 1), (26, 1), (62, 1)] }, { coefficient := 1, powers := [(12, 1), (20, 1), (36, 1), (39, 1)] }, { coefficient := -2, powers := [(12, 1), (25, 1), (30, 1), (49, 1)] }, { coefficient := 2, powers := [(12, 1), (26, 1), (28, 1), (49, 1)] }, { coefficient := -2, powers := [(18, 1), (19, 1), (20, 1), (23, 1), (24, 1), (55, 1), (62, 1)] }, { coefficient := -2, powers := [(19, 1), (24, 1), (26, 1), (51, 1)] }],
  [{ coefficient := 2, powers := [(2, 1), (58, 1)] }, { coefficient := 2, powers := [(8, 1), (36, 1)] }, { coefficient := -2, powers := [(19, 1), (30, 1)] }]
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
    (values : Fin 63 → R) :
    ¬ ∀ index : Fin 53,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((2 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (2 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (2 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component37.SelectedLeafB1_0.selectedHasNoCommonZero

end Krenn.Component37.SelectedLeafB1_0
