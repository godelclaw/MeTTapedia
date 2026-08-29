import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component39.SelectedLeafB1_6_6_5

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "8eda3773a43729260684cd7488b60baf67e82d9ec4be3994b96fb7e73ec8bb01"
def certificateSHA256 : String := "a50d3a54ec96149ebcf0965d568e1229eabb6d632a74127054020e5123268808"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 65 → Fin 673 := ![
  26,
  175,
  176,
  179,
  180,
  184,
  187,
  188,
  189,
  191,
  192,
  195,
  197,
  251,
  276,
  277,
  301,
  304,
  305,
  311,
  318,
  319,
  324,
  342,
  347,
  354,
  394,
  396,
  397,
  415,
  419,
  422,
  425,
  427,
  429,
  430,
  434,
  439,
  444,
  462,
  467,
  475,
  476,
  477,
  501,
  505,
  515,
  562,
  570,
  581,
  602,
  603,
  644,
  659,
  660,
  661,
  662,
  663,
  664,
  666,
  667,
  669,
  670,
  671,
  672
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 65 → SparsePoly (Fin 68) := ![
  [{ coefficient := 1, powers := [(20, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (26, 1)] }, { coefficient := 1, powers := [(14, 1), (21, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (28, 1)] }, { coefficient := 1, powers := [(14, 1), (21, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (53, 1)] }, { coefficient := -1, powers := [(16, 1), (24, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (23, 1)] }, { coefficient := 1, powers := [(16, 1), (18, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (45, 1)] }, { coefficient := 1, powers := [(17, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (18, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (42, 1)] }, { coefficient := 1, powers := [(17, 1), (18, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (47, 1)] }, { coefficient := 1, powers := [(17, 1), (19, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (54, 1)] }, { coefficient := 1, powers := [(28, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (42, 1)] }, { coefficient := 1, powers := [(26, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(26, 1), (52, 1)] }, { coefficient := -1, powers := [(27, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(30, 1), (37, 1)] }, { coefficient := 1, powers := [(33, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (23, 1), (45, 1)] }, { coefficient := 1, powers := [(17, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (23, 1), (42, 1)] }, { coefficient := 1, powers := [(17, 1), (18, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (23, 1), (47, 1)] }, { coefficient := 1, powers := [(17, 1), (19, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (42, 1)] }, { coefficient := 1, powers := [(23, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (44, 1)] }, { coefficient := 1, powers := [(4, 1), (33, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (51, 1)] }, { coefficient := 1, powers := [(7, 1), (30, 1)] }, { coefficient := 1, powers := [(10, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (42, 1)] }, { coefficient := 1, powers := [(17, 1), (18, 1), (50, 1)] }, { coefficient := 1, powers := [(17, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (53, 1)] }, { coefficient := 1, powers := [(28, 1), (39, 1)] }, { coefficient := 1, powers := [(28, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1), (51, 1)] }, { coefficient := 1, powers := [(18, 1), (42, 1), (51, 1)] }, { coefficient := 1, powers := [(42, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1), (51, 1)] }, { coefficient := 1, powers := [(19, 1), (42, 1), (51, 1)] }, { coefficient := 1, powers := [(47, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (42, 1), (51, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1), (42, 1)] }, { coefficient := 1, powers := [(17, 1), (21, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (45, 1), (49, 1)] }, { coefficient := 1, powers := [(12, 1), (26, 1), (45, 1)] }, { coefficient := 1, powers := [(17, 1), (27, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (34, 1), (51, 1)] }, { coefficient := 1, powers := [(21, 1), (42, 1), (51, 1)] }, { coefficient := 1, powers := [(27, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (18, 1), (57, 1)] }, { coefficient := 1, powers := [(16, 1), (24, 1), (42, 1)] }, { coefficient := 1, powers := [(17, 1), (18, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (23, 1), (39, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1), (44, 1)] }, { coefficient := 1, powers := [(16, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (23, 1), (45, 1)] }, { coefficient := 1, powers := [(17, 1), (23, 1), (39, 1)] }, { coefficient := 1, powers := [(17, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (42, 1)] }, { coefficient := 1, powers := [(16, 1), (26, 1), (42, 1)] }, { coefficient := 1, powers := [(16, 1), (34, 1), (35, 1)] }, { coefficient := 1, powers := [(17, 1), (21, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (47, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1)] }, { coefficient := 1, powers := [(16, 1), (26, 1), (47, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (51, 1)] }, { coefficient := 1, powers := [(16, 1), (21, 1), (51, 1)] }, { coefficient := 1, powers := [(16, 1), (21, 1), (56, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1)] }, { coefficient := 1, powers := [(12, 1), (28, 1)] }, { coefficient := 1, powers := [(16, 1), (21, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (34, 1)] }, { coefficient := 1, powers := [(21, 1), (42, 1)] }, { coefficient := 1, powers := [(26, 1), (42, 1)] }, { coefficient := 1, powers := [(34, 1), (35, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (59, 1)] }, { coefficient := 1, powers := [(16, 1), (19, 1), (51, 1)] }, { coefficient := 1, powers := [(16, 1), (19, 1), (56, 1)] }, { coefficient := 1, powers := [(16, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (60, 1)] }, { coefficient := 1, powers := [(12, 1), (47, 1)] }, { coefficient := 1, powers := [(17, 1), (19, 1), (52, 1)] }, { coefficient := 1, powers := [(17, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (60, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (45, 1)] }, { coefficient := 1, powers := [(12, 1), (57, 1)] }, { coefficient := 1, powers := [(17, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (39, 1)] }, { coefficient := 1, powers := [(16, 1), (44, 1)] }, { coefficient := 1, powers := [(16, 1), (51, 1)] }, { coefficient := 1, powers := [(16, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (36, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (45, 1), (52, 1)] }, { coefficient := 1, powers := [(42, 1), (52, 1)] }, { coefficient := 1, powers := [(45, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1), (51, 1)] }, { coefficient := 1, powers := [(39, 1), (42, 1)] }, { coefficient := 1, powers := [(42, 1), (51, 1)] }, { coefficient := 1, powers := [(45, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1), (51, 1)] }, { coefficient := 1, powers := [(19, 1), (51, 1)] }, { coefficient := 1, powers := [(19, 1), (56, 1)] }, { coefficient := 1, powers := [(46, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (37, 1), (59, 1)] }, { coefficient := 1, powers := [(1, 1), (46, 1), (53, 1)] }, { coefficient := 1, powers := [(10, 1), (33, 1), (37, 1)] }, { coefficient := 1, powers := [(14, 1), (30, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (38, 1), (56, 1)] }, { coefficient := 1, powers := [(1, 1), (50, 1)] }, { coefficient := 1, powers := [(7, 1), (33, 1), (38, 1)] }, { coefficient := 1, powers := [(14, 1), (25, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (39, 1), (55, 1)] }, { coefficient := 1, powers := [(1, 1), (43, 1)] }, { coefficient := 1, powers := [(4, 1), (30, 1), (55, 1)] }, { coefficient := 1, powers := [(10, 1), (20, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (47, 1), (51, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (51, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1), (47, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (27, 1), (59, 1)] }, { coefficient := 1, powers := [(21, 1), (51, 1)] }, { coefficient := 1, powers := [(21, 1), (56, 1)] }, { coefficient := 1, powers := [(27, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (28, 1), (59, 1)] }, { coefficient := 1, powers := [(10, 1), (28, 1), (44, 1)] }, { coefficient := 1, powers := [(14, 1), (27, 1), (53, 1)] }, { coefficient := 1, powers := [(14, 1), (28, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (24, 1), (45, 1)] }, { coefficient := 1, powers := [(16, 1), (57, 1)] }, { coefficient := 1, powers := [(17, 1), (24, 1), (39, 1)] }, { coefficient := 1, powers := [(17, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (42, 1), (53, 1)] }, { coefficient := 1, powers := [(27, 1), (57, 1)] }, { coefficient := 1, powers := [(28, 1), (39, 1), (42, 1)] }, { coefficient := 1, powers := [(28, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (51, 1)] }, { coefficient := 1, powers := [(3, 1), (59, 1)] }, { coefficient := 1, powers := [(18, 1), (51, 1)] }, { coefficient := 1, powers := [(18, 1), (56, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(4, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (59, 1)] }, { coefficient := 1, powers := [(10, 1), (44, 1)] }, { coefficient := 1, powers := [(10, 1), (56, 1)] }, { coefficient := 1, powers := [(14, 1), (39, 1)] }, { coefficient := 1, powers := [(14, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (51, 1)] }, { coefficient := 1, powers := [(20, 1), (56, 1)] }, { coefficient := 1, powers := [(25, 1), (39, 1)] }, { coefficient := 1, powers := [(25, 1), (44, 1)] }, { coefficient := 1, powers := [(30, 1), (36, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (36, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (44, 1), (51, 1)] }, { coefficient := 1, powers := [(39, 1)] }, { coefficient := 1, powers := [(44, 1)] }, { coefficient := 1, powers := [(51, 1)] }, { coefficient := 1, powers := [(56, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (36, 1), (59, 1)] }, { coefficient := 1, powers := [(1, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(1, 1), (44, 1), (51, 1)] }, { coefficient := 1, powers := [(4, 1), (25, 1), (59, 1)] }, { coefficient := 1, powers := [(4, 1), (30, 1), (56, 1)] }, { coefficient := 1, powers := [(4, 1), (33, 1), (51, 1)] }, { coefficient := 1, powers := [(7, 1), (20, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (30, 1), (44, 1)] }, { coefficient := 1, powers := [(7, 1), (33, 1), (39, 1)] }, { coefficient := 1, powers := [(10, 1), (20, 1), (56, 1)] }, { coefficient := 1, powers := [(10, 1), (25, 1), (44, 1)] }, { coefficient := 1, powers := [(10, 1), (33, 1), (36, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1), (51, 1)] }, { coefficient := 1, powers := [(14, 1), (25, 1), (39, 1)] }, { coefficient := 1, powers := [(14, 1), (30, 1), (36, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (37, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (47, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (28, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (22, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1), (47, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (40, 1)] }, { coefficient := 1, powers := [(12, 1), (22, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1), (28, 1), (47, 1)] }, { coefficient := 1, powers := [(12, 1), (34, 1), (37, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (54, 1)] }, { coefficient := 1, powers := [(17, 1), (28, 1), (40, 1)] }, { coefficient := 1, powers := [(17, 1), (31, 1), (37, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1)] }],
  [{ coefficient := 1, powers := [(1, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (61, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(38, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(40, 1)] }],
  [{ coefficient := 1, powers := [(55, 1), (64, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(57, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (66, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(25, 1)] }],
  [{ coefficient := 1, powers := [(28, 1), (67, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 65 → SparsePoly (Fin 68) := ![
  [{ coefficient := 1, powers := [(2, 1), (10, 1), (26, 1), (37, 1), (51, 1), (60, 1), (67, 1)] }, { coefficient := -1, powers := [(2, 1), (10, 1), (27, 1), (37, 1), (60, 1), (67, 1)] }, { coefficient := 1, powers := [(10, 1), (12, 1), (26, 1), (34, 1), (37, 1), (51, 1), (67, 1)] }, { coefficient := -1, powers := [(10, 1), (12, 1), (27, 1), (34, 1), (37, 1), (67, 1)] }, { coefficient := 1, powers := [(10, 1), (17, 1), (26, 1), (31, 1), (37, 1), (51, 1), (67, 1)] }, { coefficient := -1, powers := [(10, 1), (17, 1), (27, 1), (31, 1), (37, 1), (67, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (20, 1), (37, 1), (51, 1), (53, 1), (60, 1), (67, 1)] }, { coefficient := -1, powers := [(12, 1), (20, 1), (34, 1), (37, 1), (51, 1), (53, 1), (67, 1)] }, { coefficient := -1, powers := [(17, 1), (20, 1), (31, 1), (37, 1), (51, 1), (53, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (20, 1), (37, 1), (51, 1), (60, 1), (67, 1)] }, { coefficient := 1, powers := [(12, 1), (20, 1), (34, 1), (37, 1), (51, 1), (67, 1)] }, { coefficient := 1, powers := [(17, 1), (20, 1), (31, 1), (37, 1), (51, 1), (67, 1)] }],
  [{ coefficient := -1, powers := [(22, 1), (42, 1), (49, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(28, 1), (47, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(16, 1), (19, 1), (26, 1), (28, 1), (61, 1)] }, { coefficient := 1, powers := [(22, 1), (23, 1), (53, 1)] }, { coefficient := -1, powers := [(22, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (14, 1), (20, 1), (27, 1), (37, 1), (51, 1), (60, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (14, 1), (20, 1), (27, 1), (37, 1), (56, 1), (60, 1), (61, 1)] }, { coefficient := 1, powers := [(12, 1), (14, 1), (20, 1), (27, 1), (34, 1), (37, 1), (51, 1), (61, 1)] }, { coefficient := 1, powers := [(12, 1), (14, 1), (20, 1), (27, 1), (34, 1), (37, 1), (56, 1), (61, 1)] }, { coefficient := 1, powers := [(14, 1), (17, 1), (20, 1), (27, 1), (31, 1), (37, 1), (51, 1), (61, 1)] }, { coefficient := 1, powers := [(14, 1), (17, 1), (20, 1), (27, 1), (31, 1), (37, 1), (56, 1), (61, 1)] }, { coefficient := -1, powers := [(18, 1), (27, 1), (47, 1), (51, 1), (54, 1)] }, { coefficient := -1, powers := [(18, 1), (27, 1), (47, 1), (54, 1), (56, 1)] }, { coefficient := -1, powers := [(22, 1), (42, 1), (54, 1), (56, 1)] }, { coefficient := 1, powers := [(27, 1), (47, 1), (54, 1)] }, { coefficient := 1, powers := [(28, 1), (47, 1), (49, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(26, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(16, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (18, 1), (54, 1), (56, 1)] }, { coefficient := -1, powers := [(16, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (17, 1), (19, 1), (28, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (14, 1), (36, 1), (60, 1)] }, { coefficient := -1, powers := [(12, 1), (14, 1), (34, 1), (36, 1)] }, { coefficient := -1, powers := [(14, 1), (17, 1), (31, 1), (36, 1)] }],
  [{ coefficient := -1, powers := [(22, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (54, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [(26, 1), (51, 1), (54, 1)] }, { coefficient := -1, powers := [(28, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (28, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (37, 1), (51, 1), (60, 1)] }, { coefficient := 1, powers := [(12, 1), (34, 1), (37, 1), (51, 1)] }, { coefficient := 1, powers := [(17, 1), (31, 1), (37, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (37, 1), (44, 1), (60, 1)] }, { coefficient := 1, powers := [(12, 1), (34, 1), (37, 1), (44, 1)] }, { coefficient := 1, powers := [(17, 1), (31, 1), (37, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (49, 1), (53, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (10, 1), (20, 1), (37, 1), (60, 1), (67, 1)] }, { coefficient := 1, powers := [(2, 1), (14, 1), (20, 1), (37, 1), (60, 1), (67, 1)] }, { coefficient := -1, powers := [(2, 1), (19, 1), (42, 1), (54, 1), (67, 1)] }, { coefficient := 1, powers := [(10, 1), (12, 1), (20, 1), (34, 1), (37, 1), (67, 1)] }, { coefficient := 1, powers := [(10, 1), (17, 1), (20, 1), (31, 1), (37, 1), (67, 1)] }, { coefficient := 1, powers := [(12, 1), (14, 1), (20, 1), (34, 1), (37, 1), (67, 1)] }, { coefficient := 1, powers := [(14, 1), (17, 1), (20, 1), (31, 1), (37, 1), (67, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (19, 1), (54, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (18, 1), (54, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [(19, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (19, 1), (28, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (19, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(22, 1), (49, 1), (50, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (14, 1), (20, 1), (27, 1), (37, 1), (60, 1), (61, 1)] }, { coefficient := 1, powers := [(12, 1), (14, 1), (20, 1), (27, 1), (34, 1), (37, 1), (61, 1)] }, { coefficient := 1, powers := [(14, 1), (17, 1), (20, 1), (27, 1), (31, 1), (37, 1), (61, 1)] }, { coefficient := -1, powers := [(18, 1), (27, 1), (47, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (24, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(19, 1), (54, 1), (56, 1)] }, { coefficient := -1, powers := [(46, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(18, 1), (54, 1), (56, 1)] }, { coefficient := 1, powers := [(23, 1), (51, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (14, 1), (20, 1), (37, 1), (60, 1), (61, 1)] }, { coefficient := -1, powers := [(12, 1), (14, 1), (20, 1), (34, 1), (37, 1), (61, 1)] }, { coefficient := -1, powers := [(14, 1), (17, 1), (20, 1), (31, 1), (37, 1), (61, 1)] }, { coefficient := 1, powers := [(18, 1), (47, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(47, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (19, 1), (54, 1), (56, 1)] }, { coefficient := 1, powers := [(16, 1), (46, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (34, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(28, 1)] }],
  [{ coefficient := 1, powers := [(22, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (14, 1), (20, 1), (23, 1), (27, 1), (37, 1), (60, 1), (61, 1)] }, { coefficient := -1, powers := [(12, 1), (14, 1), (20, 1), (23, 1), (27, 1), (34, 1), (37, 1), (61, 1)] }, { coefficient := -1, powers := [(14, 1), (17, 1), (20, 1), (23, 1), (27, 1), (31, 1), (37, 1), (61, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (27, 1), (47, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(16, 1), (19, 1), (28, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (19, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (42, 1), (54, 1)] }, { coefficient := -1, powers := [(16, 1), (21, 1), (42, 1), (54, 1)] }, { coefficient := 1, powers := [(17, 1), (21, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (36, 1), (60, 1)] }, { coefficient := 1, powers := [(12, 1), (34, 1), (36, 1)] }, { coefficient := 1, powers := [(17, 1), (31, 1), (36, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (37, 1), (44, 1), (60, 1), (62, 1)] }, { coefficient := -1, powers := [(2, 1), (37, 1), (51, 1), (60, 1), (62, 1)] }, { coefficient := -1, powers := [(2, 1), (37, 1), (56, 1), (60, 1), (62, 1)] }, { coefficient := -1, powers := [(12, 1), (34, 1), (37, 1), (44, 1), (62, 1)] }, { coefficient := -1, powers := [(12, 1), (34, 1), (37, 1), (51, 1), (62, 1)] }, { coefficient := -1, powers := [(12, 1), (34, 1), (37, 1), (56, 1), (62, 1)] }, { coefficient := -1, powers := [(17, 1), (31, 1), (37, 1), (44, 1), (62, 1)] }, { coefficient := -1, powers := [(17, 1), (31, 1), (37, 1), (51, 1), (62, 1)] }, { coefficient := -1, powers := [(17, 1), (31, 1), (37, 1), (56, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (37, 1), (56, 1), (60, 1), (64, 1)] }, { coefficient := 1, powers := [(12, 1), (34, 1), (37, 1), (56, 1), (64, 1)] }, { coefficient := 1, powers := [(17, 1), (31, 1), (37, 1), (56, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(18, 1), (54, 1)] }, { coefficient := -1, powers := [(23, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (14, 1), (16, 1), (20, 1), (37, 1), (60, 1), (61, 1)] }, { coefficient := 1, powers := [(12, 1), (14, 1), (16, 1), (20, 1), (34, 1), (37, 1), (61, 1)] }, { coefficient := 1, powers := [(14, 1), (16, 1), (17, 1), (20, 1), (31, 1), (37, 1), (61, 1)] }, { coefficient := -1, powers := [(16, 1), (18, 1), (47, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (20, 1), (37, 1), (60, 1), (67, 1)] }, { coefficient := -1, powers := [(12, 1), (20, 1), (34, 1), (37, 1), (67, 1)] }, { coefficient := -1, powers := [(17, 1), (20, 1), (31, 1), (37, 1), (67, 1)] }],
  [{ coefficient := -1, powers := [(22, 1), (23, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (19, 1), (54, 1), (67, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (14, 1), (16, 1), (20, 1), (27, 1), (37, 1), (60, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (54, 1)] }, { coefficient := -1, powers := [(12, 1), (14, 1), (16, 1), (20, 1), (27, 1), (34, 1), (37, 1), (61, 1)] }, { coefficient := -1, powers := [(14, 1), (16, 1), (17, 1), (20, 1), (27, 1), (31, 1), (37, 1), (61, 1)] }, { coefficient := 1, powers := [(16, 1), (18, 1), (27, 1), (47, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (20, 1), (28, 1), (37, 1), (60, 1), (67, 1)] }, { coefficient := 1, powers := [(12, 1), (20, 1), (28, 1), (34, 1), (37, 1), (67, 1)] }, { coefficient := 1, powers := [(17, 1), (20, 1), (28, 1), (31, 1), (37, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (14, 1), (37, 1), (60, 1)] }, { coefficient := 1, powers := [(12, 1), (14, 1), (34, 1), (37, 1)] }, { coefficient := 1, powers := [(14, 1), (17, 1), (31, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (7, 1), (33, 1), (37, 1), (60, 1)] }, { coefficient := -1, powers := [(2, 1), (10, 1), (20, 1), (37, 1), (60, 1)] }, { coefficient := -1, powers := [(2, 1), (14, 1), (20, 1), (37, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (19, 1), (42, 1), (54, 1)] }, { coefficient := 1, powers := [(7, 1), (12, 1), (33, 1), (34, 1), (37, 1)] }, { coefficient := 1, powers := [(7, 1), (17, 1), (31, 1), (33, 1), (37, 1)] }, { coefficient := -1, powers := [(10, 1), (12, 1), (20, 1), (34, 1), (37, 1)] }, { coefficient := -1, powers := [(10, 1), (17, 1), (20, 1), (31, 1), (37, 1)] }, { coefficient := -1, powers := [(12, 1), (14, 1), (20, 1), (34, 1), (37, 1)] }, { coefficient := -1, powers := [(14, 1), (17, 1), (20, 1), (31, 1), (37, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (37, 1), (60, 1)] }, { coefficient := -1, powers := [(12, 1), (34, 1), (37, 1)] }, { coefficient := -1, powers := [(17, 1), (31, 1), (37, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(2, 1), (7, 1), (33, 1), (36, 1), (37, 1), (59, 1), (60, 1)] }, { coefficient := -1, powers := [(2, 1), (7, 1), (33, 1), (37, 1), (39, 1), (56, 1), (60, 1)] }, { coefficient := -1, powers := [(2, 1), (7, 1), (33, 1), (37, 1), (44, 1), (51, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (10, 1), (20, 1), (36, 1), (37, 1), (59, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (10, 1), (20, 1), (37, 1), (39, 1), (56, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (10, 1), (20, 1), (37, 1), (44, 1), (51, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (14, 1), (16, 1), (20, 1), (27, 1), (37, 1), (51, 1), (60, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (14, 1), (20, 1), (36, 1), (37, 1), (59, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (14, 1), (20, 1), (37, 1), (39, 1), (56, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (14, 1), (20, 1), (37, 1), (44, 1), (51, 1), (60, 1)] }, { coefficient := -1, powers := [(2, 1), (18, 1), (47, 1), (51, 1), (54, 1), (56, 1)] }, { coefficient := -1, powers := [(2, 1), (19, 1), (36, 1), (42, 1), (54, 1), (59, 1)] }, { coefficient := -1, powers := [(2, 1), (19, 1), (39, 1), (42, 1), (54, 1), (56, 1)] }, { coefficient := -1, powers := [(2, 1), (19, 1), (42, 1), (44, 1), (51, 1), (54, 1)] }, { coefficient := 1, powers := [(2, 1), (19, 1), (42, 1), (51, 1), (54, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (19, 1), (45, 1), (51, 1), (54, 1)] }, { coefficient := -1, powers := [(2, 1), (42, 1), (46, 1), (51, 1), (54, 1)] }, { coefficient := -1, powers := [(5, 1), (34, 1), (51, 1), (54, 1)] }, { coefficient := -1, powers := [(7, 1), (12, 1), (33, 1), (34, 1), (36, 1), (37, 1), (59, 1)] }, { coefficient := -1, powers := [(7, 1), (12, 1), (33, 1), (34, 1), (37, 1), (39, 1), (56, 1)] }, { coefficient := -1, powers := [(7, 1), (12, 1), (33, 1), (34, 1), (37, 1), (44, 1), (51, 1)] }, { coefficient := -1, powers := [(7, 1), (17, 1), (31, 1), (33, 1), (36, 1), (37, 1), (59, 1)] }, { coefficient := -1, powers := [(7, 1), (17, 1), (31, 1), (33, 1), (37, 1), (39, 1), (56, 1)] }, { coefficient := -1, powers := [(7, 1), (17, 1), (31, 1), (33, 1), (37, 1), (44, 1), (51, 1)] }, { coefficient := 1, powers := [(10, 1), (12, 1), (20, 1), (34, 1), (36, 1), (37, 1), (59, 1)] }, { coefficient := 1, powers := [(10, 1), (12, 1), (20, 1), (34, 1), (37, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(10, 1), (12, 1), (20, 1), (34, 1), (37, 1), (44, 1), (51, 1)] }, { coefficient := 1, powers := [(10, 1), (17, 1), (20, 1), (31, 1), (36, 1), (37, 1), (59, 1)] }, { coefficient := 1, powers := [(10, 1), (17, 1), (20, 1), (31, 1), (37, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(10, 1), (17, 1), (20, 1), (31, 1), (37, 1), (44, 1), (51, 1)] }, { coefficient := 1, powers := [(12, 1), (14, 1), (16, 1), (20, 1), (27, 1), (34, 1), (37, 1), (51, 1), (61, 1)] }, { coefficient := 1, powers := [(12, 1), (14, 1), (20, 1), (34, 1), (36, 1), (37, 1), (59, 1)] }, { coefficient := 1, powers := [(12, 1), (14, 1), (20, 1), (34, 1), (37, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(12, 1), (14, 1), (20, 1), (34, 1), (37, 1), (44, 1), (51, 1)] }, { coefficient := 1, powers := [(14, 1), (16, 1), (17, 1), (20, 1), (27, 1), (31, 1), (37, 1), (51, 1), (61, 1)] }, { coefficient := 1, powers := [(14, 1), (17, 1), (20, 1), (31, 1), (36, 1), (37, 1), (59, 1)] }, { coefficient := 1, powers := [(14, 1), (17, 1), (20, 1), (31, 1), (37, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(14, 1), (17, 1), (20, 1), (31, 1), (37, 1), (44, 1), (51, 1)] }, { coefficient := -1, powers := [(16, 1), (18, 1), (27, 1), (47, 1), (51, 1), (54, 1)] }, { coefficient := 1, powers := [(16, 1), (19, 1), (28, 1), (36, 1), (60, 1)] }, { coefficient := 1, powers := [(16, 1), (19, 1), (28, 1), (45, 1), (52, 1)] }, { coefficient := 1, powers := [(16, 1), (21, 1), (42, 1), (46, 1), (51, 1), (54, 1)] }, { coefficient := -1, powers := [(16, 1), (28, 1), (47, 1), (52, 1)] }, { coefficient := -1, powers := [(17, 1), (21, 1), (46, 1), (51, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (36, 1), (46, 1), (53, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (37, 1), (38, 1), (44, 1), (56, 1), (60, 1), (62, 1)] }, { coefficient := 1, powers := [(2, 1), (37, 1), (38, 1), (51, 1), (56, 1), (60, 1), (62, 1)] }, { coefficient := 1, powers := [(2, 1), (37, 1), (38, 1), (56, 2), (60, 1), (62, 1)] }, { coefficient := -1, powers := [(2, 1), (37, 1), (39, 1), (55, 1), (56, 1), (60, 1), (64, 1)] }, { coefficient := 1, powers := [(2, 1), (37, 1), (39, 1), (56, 1), (60, 1)] }, { coefficient := -1, powers := [(2, 1), (37, 1), (43, 1), (56, 1), (60, 1), (64, 1)] }, { coefficient := 1, powers := [(2, 1), (37, 1), (44, 1), (50, 1), (60, 1), (62, 1)] }, { coefficient := -1, powers := [(2, 1), (37, 1), (44, 1), (51, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (37, 1), (50, 1), (51, 1), (60, 1), (62, 1)] }, { coefficient := 1, powers := [(2, 1), (37, 1), (50, 1), (56, 1), (60, 1), (62, 1)] }, { coefficient := -1, powers := [(12, 1), (34, 1), (36, 1), (46, 1), (53, 1)] }, { coefficient := 1, powers := [(12, 1), (34, 1), (37, 1), (38, 1), (44, 1), (56, 1), (62, 1)] }, { coefficient := 1, powers := [(12, 1), (34, 1), (37, 1), (38, 1), (51, 1), (56, 1), (62, 1)] }, { coefficient := 1, powers := [(12, 1), (34, 1), (37, 1), (38, 1), (56, 2), (62, 1)] }, { coefficient := -1, powers := [(12, 1), (34, 1), (37, 1), (39, 1), (55, 1), (56, 1), (64, 1)] }, { coefficient := 1, powers := [(12, 1), (34, 1), (37, 1), (39, 1), (56, 1)] }, { coefficient := -1, powers := [(12, 1), (34, 1), (37, 1), (43, 1), (56, 1), (64, 1)] }, { coefficient := 1, powers := [(12, 1), (34, 1), (37, 1), (44, 1), (50, 1), (62, 1)] }, { coefficient := -1, powers := [(12, 1), (34, 1), (37, 1), (44, 1), (51, 1)] }, { coefficient := 1, powers := [(12, 1), (34, 1), (37, 1), (50, 1), (51, 1), (62, 1)] }, { coefficient := 1, powers := [(12, 1), (34, 1), (37, 1), (50, 1), (56, 1), (62, 1)] }, { coefficient := -1, powers := [(17, 1), (31, 1), (36, 1), (46, 1), (53, 1)] }, { coefficient := 1, powers := [(17, 1), (31, 1), (37, 1), (38, 1), (44, 1), (56, 1), (62, 1)] }, { coefficient := 1, powers := [(17, 1), (31, 1), (37, 1), (38, 1), (51, 1), (56, 1), (62, 1)] }, { coefficient := 1, powers := [(17, 1), (31, 1), (37, 1), (38, 1), (56, 2), (62, 1)] }, { coefficient := -1, powers := [(17, 1), (31, 1), (37, 1), (39, 1), (55, 1), (56, 1), (64, 1)] }, { coefficient := 1, powers := [(17, 1), (31, 1), (37, 1), (39, 1), (56, 1)] }, { coefficient := -1, powers := [(17, 1), (31, 1), (37, 1), (43, 1), (56, 1), (64, 1)] }, { coefficient := 1, powers := [(17, 1), (31, 1), (37, 1), (44, 1), (50, 1), (62, 1)] }, { coefficient := -1, powers := [(17, 1), (31, 1), (37, 1), (44, 1), (51, 1)] }, { coefficient := 1, powers := [(17, 1), (31, 1), (37, 1), (50, 1), (51, 1), (62, 1)] }, { coefficient := 1, powers := [(17, 1), (31, 1), (37, 1), (50, 1), (56, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (14, 1), (20, 1), (37, 1), (51, 1), (60, 1)] }, { coefficient := 1, powers := [(12, 1), (14, 1), (20, 1), (34, 1), (37, 1), (51, 1)] }, { coefficient := 1, powers := [(14, 1), (17, 1), (20, 1), (31, 1), (37, 1), (51, 1)] }, { coefficient := -1, powers := [(16, 1), (19, 1), (28, 1), (45, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (7, 1), (33, 1), (37, 1), (44, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (7, 1), (33, 1), (37, 1), (51, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (7, 1), (33, 1), (37, 1), (56, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (12, 1), (33, 1), (34, 1), (37, 1), (44, 1)] }, { coefficient := 1, powers := [(7, 1), (12, 1), (33, 1), (34, 1), (37, 1), (51, 1)] }, { coefficient := 1, powers := [(7, 1), (12, 1), (33, 1), (34, 1), (37, 1), (56, 1)] }, { coefficient := 1, powers := [(7, 1), (17, 1), (31, 1), (33, 1), (37, 1), (44, 1)] }, { coefficient := 1, powers := [(7, 1), (17, 1), (31, 1), (33, 1), (37, 1), (51, 1)] }, { coefficient := 1, powers := [(7, 1), (17, 1), (31, 1), (33, 1), (37, 1), (56, 1)] }, { coefficient := -1, powers := [(17, 1), (22, 1), (49, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (34, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (4, 1), (30, 1), (37, 1), (56, 1), (60, 1)] }, { coefficient := -1, powers := [(2, 1), (10, 1), (20, 1), (37, 1), (56, 1), (60, 1)] }, { coefficient := -1, powers := [(4, 1), (12, 1), (30, 1), (34, 1), (37, 1), (56, 1)] }, { coefficient := -1, powers := [(4, 1), (17, 1), (30, 1), (31, 1), (37, 1), (56, 1)] }, { coefficient := -1, powers := [(10, 1), (12, 1), (20, 1), (34, 1), (37, 1), (56, 1)] }, { coefficient := -1, powers := [(10, 1), (17, 1), (20, 1), (31, 1), (37, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (19, 1), (27, 1), (54, 1), (67, 1)] }, { coefficient := 1, powers := [(2, 1), (40, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1)] }, { coefficient := 1, powers := [(16, 1), (18, 1), (22, 1), (49, 1), (50, 1), (62, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1), (23, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (28, 1), (47, 1)] }, { coefficient := -1, powers := [(16, 1), (28, 1), (47, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (4, 1), (37, 1), (59, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (14, 1), (37, 1), (38, 1), (44, 1), (60, 1), (62, 1)] }, { coefficient := 1, powers := [(2, 1), (14, 1), (37, 1), (38, 1), (51, 1), (60, 1), (62, 1)] }, { coefficient := 1, powers := [(2, 1), (14, 1), (37, 1), (38, 1), (56, 1), (60, 1), (62, 1)] }, { coefficient := -1, powers := [(2, 1), (14, 1), (37, 1), (44, 1), (60, 1)] }, { coefficient := 1, powers := [(4, 1), (12, 1), (34, 1), (37, 1), (59, 1)] }, { coefficient := 1, powers := [(4, 1), (17, 1), (31, 1), (37, 1), (59, 1)] }, { coefficient := 1, powers := [(12, 1), (14, 1), (34, 1), (37, 1), (38, 1), (44, 1), (62, 1)] }, { coefficient := 1, powers := [(12, 1), (14, 1), (34, 1), (37, 1), (38, 1), (51, 1), (62, 1)] }, { coefficient := 1, powers := [(12, 1), (14, 1), (34, 1), (37, 1), (38, 1), (56, 1), (62, 1)] }, { coefficient := -1, powers := [(12, 1), (14, 1), (34, 1), (37, 1), (44, 1)] }, { coefficient := 1, powers := [(14, 1), (17, 1), (31, 1), (37, 1), (38, 1), (44, 1), (62, 1)] }, { coefficient := 1, powers := [(14, 1), (17, 1), (31, 1), (37, 1), (38, 1), (51, 1), (62, 1)] }, { coefficient := 1, powers := [(14, 1), (17, 1), (31, 1), (37, 1), (38, 1), (56, 1), (62, 1)] }, { coefficient := -1, powers := [(14, 1), (17, 1), (31, 1), (37, 1), (44, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (7, 1), (20, 1), (37, 1), (59, 1), (60, 1)] }, { coefficient := -1, powers := [(2, 1), (10, 1), (20, 1), (37, 1), (39, 1), (60, 1)] }, { coefficient := -1, powers := [(2, 1), (10, 1), (20, 1), (37, 1), (44, 1), (60, 1)] }, { coefficient := -1, powers := [(2, 1), (10, 1), (20, 1), (37, 1), (51, 1), (60, 1)] }, { coefficient := -1, powers := [(2, 1), (10, 1), (20, 1), (37, 1), (56, 1), (60, 1)] }, { coefficient := -1, powers := [(2, 1), (14, 1), (20, 1), (37, 1), (39, 1), (60, 1)] }, { coefficient := -1, powers := [(2, 1), (14, 1), (20, 1), (37, 1), (44, 1), (60, 1)] }, { coefficient := -1, powers := [(2, 1), (14, 1), (20, 1), (37, 1), (51, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (19, 1), (42, 1), (44, 1), (54, 1)] }, { coefficient := -1, powers := [(2, 1), (19, 1), (45, 1), (54, 1)] }, { coefficient := -1, powers := [(7, 1), (12, 1), (20, 1), (34, 1), (37, 1), (59, 1)] }, { coefficient := -1, powers := [(7, 1), (17, 1), (20, 1), (31, 1), (37, 1), (59, 1)] }, { coefficient := -1, powers := [(10, 1), (12, 1), (20, 1), (34, 1), (37, 1), (39, 1)] }, { coefficient := -1, powers := [(10, 1), (12, 1), (20, 1), (34, 1), (37, 1), (44, 1)] }, { coefficient := -1, powers := [(10, 1), (12, 1), (20, 1), (34, 1), (37, 1), (51, 1)] }, { coefficient := -1, powers := [(10, 1), (12, 1), (20, 1), (34, 1), (37, 1), (56, 1)] }, { coefficient := -1, powers := [(10, 1), (17, 1), (20, 1), (31, 1), (37, 1), (39, 1)] }, { coefficient := -1, powers := [(10, 1), (17, 1), (20, 1), (31, 1), (37, 1), (44, 1)] }, { coefficient := -1, powers := [(10, 1), (17, 1), (20, 1), (31, 1), (37, 1), (51, 1)] }, { coefficient := -1, powers := [(10, 1), (17, 1), (20, 1), (31, 1), (37, 1), (56, 1)] }, { coefficient := -1, powers := [(12, 1), (14, 1), (20, 1), (34, 1), (37, 1), (39, 1)] }, { coefficient := -1, powers := [(12, 1), (14, 1), (20, 1), (34, 1), (37, 1), (44, 1)] }, { coefficient := -1, powers := [(12, 1), (14, 1), (20, 1), (34, 1), (37, 1), (51, 1)] }, { coefficient := -1, powers := [(14, 1), (17, 1), (20, 1), (31, 1), (37, 1), (39, 1)] }, { coefficient := -1, powers := [(14, 1), (17, 1), (20, 1), (31, 1), (37, 1), (44, 1)] }, { coefficient := -1, powers := [(14, 1), (17, 1), (20, 1), (31, 1), (37, 1), (51, 1)] }]
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
    ¬ ∀ index : Fin 65,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component39.SelectedLeafB1_6_6_5.selectedHasNoCommonZero

end Krenn.Component39.SelectedLeafB1_6_6_5
