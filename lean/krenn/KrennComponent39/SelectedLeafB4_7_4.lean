import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component39.SelectedLeafB4_7_4

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "4c3eaeda2a740c98db43a2efa77edcaa8799a7b1f8e80554f757918ac4f94be9"
def certificateSHA256 : String := "ef9cb7037a7bcf1c1256955219b837f0b12a4e750603e56497c31f43eb34ef0f"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 55 → Fin 670 := ![
  14,
  19,
  30,
  92,
  170,
  183,
  184,
  187,
  191,
  193,
  194,
  195,
  250,
  268,
  302,
  303,
  305,
  313,
  316,
  317,
  318,
  320,
  350,
  365,
  382,
  412,
  413,
  425,
  430,
  434,
  440,
  451,
  453,
  458,
  467,
  468,
  505,
  508,
  520,
  562,
  567,
  580,
  581,
  603,
  608,
  659,
  660,
  661,
  662,
  663,
  664,
  666,
  667,
  668,
  669
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 55 → SparsePoly (Fin 66) := ![
  [{ coefficient := 1, powers := [(10, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (34, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (34, 1)] }, { coefficient := 1, powers := [(10, 1), (26, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (42, 1)] }, { coefficient := 1, powers := [(17, 1), (18, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (45, 1)] }, { coefficient := 1, powers := [(17, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (18, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (54, 1)] }, { coefficient := 1, powers := [(28, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (53, 1)] }, { coefficient := 1, powers := [(28, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (40, 1)] }, { coefficient := 1, powers := [(25, 1), (46, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(26, 1), (52, 1)] }, { coefficient := -1, powers := [(27, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (23, 1), (44, 1)] }, { coefficient := 1, powers := [(16, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (19, 1), (52, 1)] }, { coefficient := 1, powers := [(14, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (49, 1)] }, { coefficient := 1, powers := [(18, 1), (49, 1)] }, { coefficient := 1, powers := [(23, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (54, 1)] }, { coefficient := 1, powers := [(18, 1), (54, 1)] }, { coefficient := 1, powers := [(24, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (51, 1)] }, { coefficient := 1, powers := [(7, 1), (30, 1)] }, { coefficient := 1, powers := [(10, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (44, 1)] }, { coefficient := 1, powers := [(12, 1), (56, 1)] }, { coefficient := 1, powers := [(16, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (45, 1)] }, { coefficient := 1, powers := [(17, 1), (39, 1)] }, { coefficient := 1, powers := [(17, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (51, 1)] }, { coefficient := 1, powers := [(22, 1), (56, 1)] }, { coefficient := 1, powers := [(27, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (53, 1)] }, { coefficient := 1, powers := [(28, 1), (39, 1)] }, { coefficient := 1, powers := [(28, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1), (54, 1)] }, { coefficient := 1, powers := [(13, 1), (54, 1)] }, { coefficient := 1, powers := [(24, 1), (43, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (28, 1), (59, 1)] }, { coefficient := 1, powers := [(21, 1), (53, 1)] }, { coefficient := 1, powers := [(28, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (22, 1), (59, 1)] }, { coefficient := 1, powers := [(22, 1)] }, { coefficient := 1, powers := [(26, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (18, 1), (56, 1)] }, { coefficient := 1, powers := [(12, 1)] }, { coefficient := 1, powers := [(16, 1), (18, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (52, 1)] }, { coefficient := 1, powers := [(18, 1), (49, 1), (56, 1)] }, { coefficient := 1, powers := [(18, 1), (52, 1)] }, { coefficient := 1, powers := [(49, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (53, 1)] }, { coefficient := 1, powers := [(3, 1), (24, 1), (59, 1)] }, { coefficient := 1, powers := [(18, 1), (53, 1)] }, { coefficient := 1, powers := [(24, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1)] }, { coefficient := 1, powers := [(12, 1), (28, 1)] }, { coefficient := 1, powers := [(16, 1), (21, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (60, 1)] }, { coefficient := 1, powers := [(12, 1), (47, 1)] }, { coefficient := 1, powers := [(17, 1), (19, 1), (52, 1)] }, { coefficient := 1, powers := [(17, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (60, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (45, 1)] }, { coefficient := 1, powers := [(12, 1), (57, 1)] }, { coefficient := 1, powers := [(17, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (54, 1)] }, { coefficient := 1, powers := [(28, 1), (40, 1)] }, { coefficient := 1, powers := [(28, 1), (46, 1), (49, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1), (52, 1)] }, { coefficient := 1, powers := [(3, 1), (60, 1)] }, { coefficient := 1, powers := [(18, 1), (42, 1), (52, 1)] }, { coefficient := 1, powers := [(42, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1), (49, 1)] }, { coefficient := 1, powers := [(13, 1), (49, 1)] }, { coefficient := 1, powers := [(23, 1), (43, 1), (49, 1)] }, { coefficient := 1, powers := [(49, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1), (53, 1)] }, { coefficient := 1, powers := [(24, 1), (39, 1)] }, { coefficient := 1, powers := [(24, 1), (44, 1)] }, { coefficient := 1, powers := [(53, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1), (51, 1)] }, { coefficient := 1, powers := [(19, 1), (51, 1)] }, { coefficient := 1, powers := [(19, 1), (56, 1)] }, { coefficient := 1, powers := [(46, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1), (54, 1)] }, { coefficient := 1, powers := [(19, 1), (54, 1)] }, { coefficient := 1, powers := [(24, 1), (40, 1)] }, { coefficient := 1, powers := [(24, 1), (46, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (27, 1), (59, 1)] }, { coefficient := 1, powers := [(21, 1), (51, 1)] }, { coefficient := 1, powers := [(21, 1), (56, 1)] }, { coefficient := 1, powers := [(27, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (31, 1), (56, 1)] }, { coefficient := 1, powers := [(21, 1), (49, 1), (56, 1)] }, { coefficient := 1, powers := [(21, 1), (52, 1)] }, { coefficient := 1, powers := [(27, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (34, 1), (51, 1)] }, { coefficient := 1, powers := [(7, 1), (34, 1), (39, 1)] }, { coefficient := 1, powers := [(10, 1), (27, 1), (45, 1)] }, { coefficient := 1, powers := [(10, 1), (34, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (24, 1), (45, 1)] }, { coefficient := 1, powers := [(16, 1), (57, 1)] }, { coefficient := 1, powers := [(17, 1), (24, 1), (39, 1)] }, { coefficient := 1, powers := [(17, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (49, 1), (56, 1)] }, { coefficient := 1, powers := [(22, 1), (52, 1)] }, { coefficient := 1, powers := [(27, 1), (40, 1)] }, { coefficient := 1, powers := [(27, 1), (46, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1)] }, { coefficient := 1, powers := [(6, 1), (59, 1)] }, { coefficient := 1, powers := [(23, 1), (39, 1)] }, { coefficient := 1, powers := [(23, 1), (44, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (51, 1)] }, { coefficient := 1, powers := [(3, 1), (59, 1)] }, { coefficient := 1, powers := [(18, 1), (51, 1)] }, { coefficient := 1, powers := [(18, 1), (56, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(20, 1), (51, 1)] }, { coefficient := 1, powers := [(20, 1), (56, 1)] }, { coefficient := 1, powers := [(25, 1), (39, 1)] }, { coefficient := 1, powers := [(25, 1), (44, 1)] }, { coefficient := 1, powers := [(30, 1), (36, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (40, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(19, 1), (49, 1), (56, 1)] }, { coefficient := 1, powers := [(19, 1), (52, 1)] }, { coefficient := 1, powers := [(40, 1)] }, { coefficient := 1, powers := [(46, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (36, 1), (59, 1)] }, { coefficient := 1, powers := [(1, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(1, 1), (44, 1), (51, 1)] }, { coefficient := 1, powers := [(4, 1), (25, 1), (59, 1)] }, { coefficient := 1, powers := [(4, 1), (30, 1), (56, 1)] }, { coefficient := 1, powers := [(4, 1), (33, 1), (51, 1)] }, { coefficient := 1, powers := [(7, 1), (20, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (30, 1), (44, 1)] }, { coefficient := 1, powers := [(7, 1), (33, 1), (39, 1)] }, { coefficient := 1, powers := [(10, 1), (20, 1), (56, 1)] }, { coefficient := 1, powers := [(10, 1), (25, 1), (44, 1)] }, { coefficient := 1, powers := [(10, 1), (33, 1), (36, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1), (51, 1)] }, { coefficient := 1, powers := [(14, 1), (25, 1), (39, 1)] }, { coefficient := 1, powers := [(14, 1), (30, 1), (36, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (37, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (47, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (28, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (22, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1), (47, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (40, 1)] }, { coefficient := 1, powers := [(12, 1), (22, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1), (28, 1), (47, 1)] }, { coefficient := 1, powers := [(12, 1), (34, 1), (37, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (54, 1)] }, { coefficient := 1, powers := [(17, 1), (28, 1), (40, 1)] }, { coefficient := 1, powers := [(17, 1), (31, 1), (37, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (61, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1)] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(38, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(40, 1), (64, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(55, 1), (65, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(56, 1)] }],
  [{ coefficient := 1, powers := [(57, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 55 → SparsePoly (Fin 66) := ![
  [{ coefficient := -1, powers := [(5, 1), (25, 1), (26, 1), (54, 1), (59, 1)] }, { coefficient := -1, powers := [(5, 1), (27, 1), (33, 1), (54, 1)] }, { coefficient := -1, powers := [(8, 1), (25, 1), (26, 1), (40, 1), (59, 1)] }, { coefficient := -1, powers := [(8, 1), (27, 1), (33, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (19, 1), (33, 1), (34, 1), (36, 1), (54, 1), (64, 1)] }, { coefficient := 1, powers := [(8, 1), (19, 1), (33, 1), (34, 1), (36, 1), (40, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (14, 1), (34, 1), (44, 1), (49, 1), (54, 1), (64, 1)] }, { coefficient := 1, powers := [(8, 1), (14, 1), (34, 1), (40, 1), (44, 1), (49, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (20, 1), (54, 1), (59, 1), (62, 1)] }, { coefficient := 1, powers := [(8, 1), (20, 1), (40, 1), (59, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (25, 1), (54, 1), (59, 1)] }, { coefficient := 1, powers := [(8, 1), (25, 1), (40, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(28, 1), (46, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (22, 1), (24, 1), (59, 1)] }, { coefficient := -1, powers := [(22, 1), (24, 1)] }],
  [{ coefficient := -1, powers := [(28, 1), (42, 1), (46, 1), (49, 1), (61, 1)] }, { coefficient := -1, powers := [(28, 1), (42, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(28, 1), (47, 1), (52, 1)] }, { coefficient := -1, powers := [(34, 1), (37, 1), (49, 1), (61, 1)] }, { coefficient := -1, powers := [(34, 1), (37, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (17, 1), (46, 1), (59, 1)] }, { coefficient := -1, powers := [(16, 1), (47, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (17, 1), (44, 1), (49, 1)] }, { coefficient := -2, powers := [(3, 1), (17, 1), (49, 1), (59, 1)] }, { coefficient := -1, powers := [(6, 1), (17, 1), (49, 1), (59, 1)] }, { coefficient := -3, powers := [(17, 1), (49, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (14, 1), (34, 1), (44, 1), (54, 1), (64, 1)] }, { coefficient := -1, powers := [(8, 1), (14, 1), (34, 1), (40, 1), (44, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (17, 1), (46, 1), (53, 1)] }, { coefficient := 1, powers := [(17, 1), (18, 1), (46, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(28, 1), (42, 1), (46, 1)] }, { coefficient := 1, powers := [(28, 1), (47, 1)] }, { coefficient := -1, powers := [(34, 1), (37, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (33, 1), (34, 1), (36, 1), (54, 1), (64, 1)] }, { coefficient := -1, powers := [(8, 1), (33, 1), (34, 1), (36, 1), (40, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (28, 1), (42, 1), (46, 1), (61, 1)] }, { coefficient := 1, powers := [(16, 1), (34, 1), (37, 1), (61, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (24, 1), (39, 1), (43, 1), (65, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (24, 1), (43, 1), (44, 1), (65, 1)] }, { coefficient := -1, powers := [(17, 1), (22, 1), (51, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (17, 1), (22, 1), (39, 1), (43, 1), (65, 1)] }, { coefficient := 1, powers := [(0, 1), (17, 1), (22, 1), (43, 1), (44, 1), (65, 1)] }, { coefficient := 1, powers := [(13, 1), (17, 1), (22, 1), (39, 1), (65, 1)] }, { coefficient := 1, powers := [(13, 1), (17, 1), (22, 1), (44, 1), (65, 1)] }, { coefficient := 1, powers := [(17, 1), (21, 1), (46, 1), (51, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (39, 1), (55, 1), (65, 1)] }, { coefficient := -1, powers := [(17, 1), (22, 1), (39, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (44, 1), (55, 1), (65, 1)] }, { coefficient := -1, powers := [(17, 1), (22, 1), (44, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (34, 1), (44, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (40, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (28, 1), (42, 1), (46, 1)] }, { coefficient := -1, powers := [(23, 1), (28, 1), (47, 1)] }, { coefficient := 1, powers := [(23, 1), (34, 1), (37, 1)] }],
  [{ coefficient := -1, powers := [(22, 1), (24, 1), (49, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (17, 1), (49, 1), (53, 1)] }, { coefficient := -1, powers := [(17, 1), (18, 1), (49, 1), (53, 1)] }, { coefficient := 1, powers := [(17, 1), (23, 1), (49, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(17, 1), (23, 1), (46, 1), (49, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (17, 1), (22, 1), (39, 1), (65, 1)] }, { coefficient := -1, powers := [(0, 1), (17, 1), (22, 1), (44, 1), (65, 1)] }, { coefficient := -1, powers := [(17, 1), (18, 1), (22, 1), (39, 1), (65, 1)] }, { coefficient := -1, powers := [(17, 1), (18, 1), (22, 1), (44, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (46, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (49, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(28, 1), (42, 1), (46, 1)] }, { coefficient := -1, powers := [(28, 1), (47, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (22, 1), (42, 1), (59, 1)] }, { coefficient := -1, powers := [(17, 1), (21, 1), (46, 1), (53, 1)] }, { coefficient := -2, powers := [(17, 1), (22, 1), (53, 1)] }, { coefficient := -1, powers := [(17, 1), (26, 1), (46, 1), (53, 1)] }, { coefficient := 1, powers := [(17, 1), (28, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (22, 1), (52, 1)] }, { coefficient := -1, powers := [(17, 1), (27, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(47, 1)] }],
  [{ coefficient := 1, powers := [(28, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (22, 1), (59, 1)] }, { coefficient := 1, powers := [(22, 1)] }],
  [{ coefficient := 1, powers := [(17, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (22, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(17, 1), (22, 1), (24, 1), (39, 1), (65, 1)] }, { coefficient := -1, powers := [(17, 1), (22, 1), (24, 1), (44, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (22, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (21, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(17, 1), (21, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (24, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (17, 1), (46, 1), (53, 1)] }, { coefficient := 1, powers := [(17, 1), (18, 1), (46, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (33, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (17, 1), (53, 1)] }, { coefficient := 1, powers := [(17, 1), (18, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (28, 1), (46, 1), (49, 1)] }],
  [{ coefficient := -1, powers := [(17, 1), (21, 1), (46, 1), (54, 1)] }, { coefficient := 2, powers := [(17, 1), (22, 1), (49, 1), (53, 1)] }, { coefficient := -1, powers := [(17, 1), (22, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (14, 1), (34, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (14, 1), (34, 1), (40, 1)] }],
  [{ coefficient := -1, powers := [(17, 1), (28, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (34, 1), (54, 1)] }, { coefficient := -1, powers := [(8, 1), (34, 1), (40, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(16, 1), (28, 1), (42, 1), (46, 1), (49, 1)] }, { coefficient := -1, powers := [(16, 1), (34, 1), (37, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (34, 1), (36, 1), (54, 1), (59, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (36, 1), (40, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(37, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (7, 1), (20, 1), (34, 1), (54, 1), (59, 1)] }, { coefficient := -1, powers := [(7, 1), (8, 1), (20, 1), (34, 1), (40, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (14, 1), (25, 1), (34, 1), (44, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (14, 1), (33, 1), (34, 1), (36, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (14, 1), (25, 1), (34, 1), (40, 1), (44, 1)] }, { coefficient := 1, powers := [(8, 1), (14, 1), (33, 1), (34, 1), (36, 1), (40, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (17, 1), (22, 1), (39, 1), (54, 1)] }, { coefficient := -1, powers := [(0, 1), (17, 1), (22, 1), (44, 1), (54, 1)] }, { coefficient := -1, powers := [(17, 1), (18, 1), (22, 1), (39, 1), (54, 1)] }, { coefficient := -1, powers := [(17, 1), (18, 1), (22, 1), (44, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (3, 1), (17, 1), (31, 1), (46, 1), (53, 1)] }, { coefficient := -1, powers := [(0, 1), (17, 1), (21, 1), (46, 1), (49, 1), (53, 1)] }, { coefficient := 1, powers := [(0, 1), (17, 1), (28, 1), (40, 1)] }, { coefficient := 1, powers := [(1, 1), (5, 1), (34, 1), (39, 1), (54, 1)] }, { coefficient := 1, powers := [(1, 1), (8, 1), (34, 1), (39, 1), (40, 1)] }, { coefficient := -1, powers := [(3, 1), (17, 1), (18, 1), (31, 1), (46, 1), (53, 1)] }, { coefficient := 1, powers := [(4, 1), (5, 1), (30, 1), (34, 1), (54, 1)] }, { coefficient := 1, powers := [(4, 1), (8, 1), (30, 1), (34, 1), (40, 1)] }, { coefficient := 1, powers := [(5, 1), (10, 1), (20, 1), (34, 1), (54, 1)] }, { coefficient := -1, powers := [(5, 1), (14, 1), (20, 1), (34, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (10, 1), (20, 1), (34, 1), (40, 1)] }, { coefficient := -1, powers := [(8, 1), (14, 1), (20, 1), (34, 1), (40, 1)] }, { coefficient := -1, powers := [(8, 1), (18, 1), (22, 1), (42, 1), (49, 1), (59, 1)] }, { coefficient := -1, powers := [(12, 1), (18, 1), (28, 1), (42, 1), (46, 1)] }, { coefficient := 1, powers := [(12, 1), (18, 1), (28, 1), (47, 1)] }, { coefficient := -1, powers := [(12, 1), (18, 1), (34, 1), (37, 1)] }, { coefficient := -1, powers := [(12, 1), (23, 1), (28, 1), (42, 1), (46, 1)] }, { coefficient := 1, powers := [(12, 1), (23, 1), (28, 1), (47, 1)] }, { coefficient := -1, powers := [(12, 1), (23, 1), (34, 1), (37, 1)] }, { coefficient := 1, powers := [(17, 1), (18, 1), (21, 1), (46, 1), (54, 1)] }, { coefficient := 1, powers := [(17, 1), (18, 1), (22, 1), (54, 1)] }, { coefficient := 1, powers := [(17, 1), (18, 1), (26, 1), (46, 1), (49, 1), (53, 1)] }, { coefficient := -1, powers := [(17, 1), (18, 1), (28, 1), (46, 1), (49, 1)] }, { coefficient := -1, powers := [(17, 1), (19, 1), (21, 1), (54, 1)] }, { coefficient := 1, powers := [(17, 1), (19, 1), (28, 1), (49, 1)] }, { coefficient := -1, powers := [(17, 1), (21, 1), (24, 1), (40, 1)] }, { coefficient := -1, powers := [(17, 1), (22, 1), (23, 1), (49, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (40, 1)] }, { coefficient := -1, powers := [(3, 1), (12, 1), (22, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1)] }, { coefficient := -1, powers := [(16, 1), (22, 1), (49, 1)] }]
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
    ¬ ∀ index : Fin 55,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component39.SelectedLeafB4_7_4.selectedHasNoCommonZero

end Krenn.Component39.SelectedLeafB4_7_4
