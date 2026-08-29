import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component39.SelectedLeafB4_2_6_5_1

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "c08d0a1607fbc9f663e93a01e68a013de7c155375639c92644745a1674adafdc"
def certificateSHA256 : String := "3f5a2cc009e9f748e0021a0efc7bdb1af076a2db17129217fb30ced0dac75bb2"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 57 → Fin 676 := ![
  21,
  23,
  171,
  180,
  181,
  187,
  191,
  192,
  193,
  250,
  264,
  277,
  282,
  300,
  301,
  302,
  303,
  304,
  305,
  313,
  315,
  316,
  317,
  324,
  350,
  365,
  419,
  425,
  430,
  434,
  439,
  463,
  470,
  471,
  503,
  532,
  563,
  580,
  581,
  602,
  603,
  604,
  637,
  659,
  660,
  661,
  662,
  663,
  666,
  667,
  668,
  669,
  670,
  671,
  672,
  674,
  675
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 57 → SparsePoly (Fin 68) := ![
  [{ coefficient := 1, powers := [(16, 1), (20, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (20, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (23, 1)] }, { coefficient := 1, powers := [(16, 1), (18, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (24, 1)] }, { coefficient := 1, powers := [(16, 1), (18, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (18, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (54, 1)] }, { coefficient := 1, powers := [(28, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (42, 1)] }, { coefficient := 1, powers := [(26, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (53, 1)] }, { coefficient := 1, powers := [(28, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (23, 1), (44, 1)] }, { coefficient := 1, powers := [(16, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (22, 1), (53, 1)] }, { coefficient := 1, powers := [(19, 1), (28, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (23, 1), (47, 1)] }, { coefficient := 1, powers := [(17, 1), (19, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (42, 1), (51, 1)] }, { coefficient := 1, powers := [(27, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1)] }, { coefficient := 1, powers := [(18, 1), (42, 1)] }, { coefficient := 1, powers := [(23, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (42, 1)] }, { coefficient := 1, powers := [(23, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (49, 1)] }, { coefficient := 1, powers := [(18, 1), (49, 1)] }, { coefficient := 1, powers := [(23, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (54, 1)] }, { coefficient := 1, powers := [(18, 1), (54, 1)] }, { coefficient := 1, powers := [(24, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (44, 1)] }, { coefficient := 1, powers := [(4, 1), (33, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (51, 1)] }, { coefficient := 1, powers := [(7, 1), (30, 1)] }, { coefficient := 1, powers := [(10, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (44, 1)] }, { coefficient := 1, powers := [(12, 1), (56, 1)] }, { coefficient := 1, powers := [(16, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (22, 1)] }, { coefficient := 1, powers := [(19, 1), (26, 1), (43, 1)] }, { coefficient := 1, powers := [(22, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (45, 1)] }, { coefficient := 1, powers := [(17, 1), (39, 1)] }, { coefficient := 1, powers := [(17, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (51, 1)] }, { coefficient := 1, powers := [(22, 1), (56, 1)] }, { coefficient := 1, powers := [(27, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1), (51, 1)] }, { coefficient := 1, powers := [(19, 1), (42, 1), (51, 1)] }, { coefficient := 1, powers := [(47, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (28, 1), (59, 1)] }, { coefficient := 1, powers := [(21, 1), (53, 1)] }, { coefficient := 1, powers := [(28, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (22, 1), (59, 1)] }, { coefficient := 1, powers := [(22, 1)] }, { coefficient := 1, powers := [(26, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (47, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1)] }, { coefficient := 1, powers := [(16, 1), (26, 1), (47, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1)] }, { coefficient := 1, powers := [(12, 1), (28, 1)] }, { coefficient := 1, powers := [(16, 1), (21, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (60, 1)] }, { coefficient := 1, powers := [(12, 1), (47, 1)] }, { coefficient := 1, powers := [(17, 1), (19, 1), (52, 1)] }, { coefficient := 1, powers := [(17, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (60, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (45, 1)] }, { coefficient := 1, powers := [(12, 1), (57, 1)] }, { coefficient := 1, powers := [(17, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (39, 1)] }, { coefficient := 1, powers := [(16, 1), (44, 1)] }, { coefficient := 1, powers := [(16, 1), (51, 1)] }, { coefficient := 1, powers := [(16, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1), (54, 1)] }, { coefficient := 1, powers := [(24, 1), (45, 1), (49, 1)] }, { coefficient := 1, powers := [(42, 1), (54, 1)] }, { coefficient := 1, powers := [(49, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1), (52, 1)] }, { coefficient := 1, powers := [(19, 1), (42, 1), (52, 1)] }, { coefficient := 1, powers := [(40, 1), (42, 1)] }, { coefficient := 1, powers := [(47, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1), (53, 1)] }, { coefficient := 1, powers := [(19, 1), (42, 1), (53, 1)] }, { coefficient := 1, powers := [(19, 1), (57, 1)] }, { coefficient := 1, powers := [(24, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (26, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (21, 1), (59, 1)] }, { coefficient := 1, powers := [(21, 1)] }, { coefficient := 1, powers := [(26, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (27, 1), (59, 1)] }, { coefficient := 1, powers := [(26, 1), (39, 1)] }, { coefficient := 1, powers := [(26, 1), (44, 1)] }, { coefficient := 1, powers := [(27, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (25, 1), (45, 1)] }, { coefficient := 1, powers := [(17, 1), (20, 1), (51, 1)] }, { coefficient := 1, powers := [(17, 1), (25, 1), (39, 1)] }, { coefficient := 1, powers := [(17, 1), (30, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1)] }, { coefficient := 1, powers := [(6, 1), (59, 1)] }, { coefficient := 1, powers := [(23, 1), (39, 1)] }, { coefficient := 1, powers := [(23, 1), (44, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (51, 1)] }, { coefficient := 1, powers := [(3, 1), (59, 1)] }, { coefficient := 1, powers := [(18, 1), (51, 1)] }, { coefficient := 1, powers := [(18, 1), (56, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(4, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (59, 1)] }, { coefficient := 1, powers := [(10, 1), (44, 1)] }, { coefficient := 1, powers := [(10, 1), (56, 1)] }, { coefficient := 1, powers := [(14, 1), (39, 1)] }, { coefficient := 1, powers := [(14, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (51, 1)] }, { coefficient := 1, powers := [(20, 1), (56, 1)] }, { coefficient := 1, powers := [(25, 1), (39, 1)] }, { coefficient := 1, powers := [(25, 1), (44, 1)] }, { coefficient := 1, powers := [(30, 1), (36, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (35, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1)] }, { coefficient := 1, powers := [(3, 1), (23, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (18, 1), (59, 1)] }, { coefficient := 1, powers := [(18, 1)] }, { coefficient := 1, powers := [(23, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (42, 1), (54, 1)] }, { coefficient := 1, powers := [(22, 1), (49, 1), (57, 1)] }, { coefficient := 1, powers := [(28, 1), (40, 1), (42, 1)] }, { coefficient := 1, powers := [(28, 1), (47, 1), (49, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1), (42, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (36, 1), (59, 1)] }, { coefficient := 1, powers := [(1, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(1, 1), (44, 1), (51, 1)] }, { coefficient := 1, powers := [(4, 1), (25, 1), (59, 1)] }, { coefficient := 1, powers := [(4, 1), (30, 1), (56, 1)] }, { coefficient := 1, powers := [(4, 1), (33, 1), (51, 1)] }, { coefficient := 1, powers := [(7, 1), (20, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (30, 1), (44, 1)] }, { coefficient := 1, powers := [(7, 1), (33, 1), (39, 1)] }, { coefficient := 1, powers := [(10, 1), (20, 1), (56, 1)] }, { coefficient := 1, powers := [(10, 1), (25, 1), (44, 1)] }, { coefficient := 1, powers := [(10, 1), (33, 1), (36, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1), (51, 1)] }, { coefficient := 1, powers := [(14, 1), (25, 1), (39, 1)] }, { coefficient := 1, powers := [(14, 1), (30, 1), (36, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (37, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (47, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (28, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (22, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1), (47, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (40, 1)] }, { coefficient := 1, powers := [(12, 1), (22, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1), (28, 1), (47, 1)] }, { coefficient := 1, powers := [(12, 1), (34, 1), (37, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (54, 1)] }, { coefficient := 1, powers := [(17, 1), (28, 1), (40, 1)] }, { coefficient := 1, powers := [(17, 1), (31, 1), (37, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (61, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1)] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(40, 1)] }],
  [{ coefficient := 1, powers := [(55, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(56, 1), (64, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(57, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (65, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(25, 1)] }],
  [{ coefficient := 1, powers := [(28, 1), (66, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(59, 1)] }],
  [{ coefficient := 1, powers := [(60, 1), (67, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 57 → SparsePoly (Fin 68) := ![
  [{ coefficient := -1, powers := [(14, 1), (31, 1), (37, 1), (45, 1)] }],
  [{ coefficient := -1, powers := [(10, 1), (31, 1), (37, 1), (44, 1)] }, { coefficient := -1, powers := [(10, 1), (31, 1), (37, 1), (56, 1)] }, { coefficient := -1, powers := [(14, 1), (31, 1), (37, 1), (39, 1)] }, { coefficient := -3, powers := [(14, 1), (31, 1), (37, 1), (51, 1)] }],
  [{ coefficient := -1, powers := [(16, 1), (31, 1), (33, 1), (37, 1), (45, 1), (67, 1)] }, { coefficient := 1, powers := [(17, 1), (30, 1), (31, 1), (37, 1), (56, 1), (67, 1)] }, { coefficient := -1, powers := [(17, 1), (31, 1), (33, 1), (37, 1), (51, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(34, 1), (37, 1), (51, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [(22, 1), (45, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (34, 1), (37, 1), (49, 1), (61, 1), (65, 1)] }, { coefficient := -1, powers := [(22, 1), (42, 1), (54, 1), (61, 1)] }, { coefficient := -1, powers := [(28, 1), (47, 1), (49, 1), (61, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1), (42, 1), (61, 1)] }, { coefficient := -1, powers := [(34, 1), (37, 1), (44, 1), (49, 1)] }, { coefficient := -1, powers := [(34, 1), (37, 1), (49, 1), (51, 1)] }, { coefficient := -1, powers := [(34, 1), (37, 1), (49, 1), (56, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(16, 1), (47, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (24, 1), (39, 1), (51, 1), (64, 1)] }, { coefficient := -1, powers := [(12, 1), (24, 1), (44, 1), (51, 1), (64, 1)] }, { coefficient := -1, powers := [(12, 1), (24, 1), (51, 1)] }, { coefficient := -1, powers := [(16, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(13, 1), (17, 1), (26, 1), (54, 1), (63, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (34, 1), (37, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (26, 1), (54, 1), (63, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(28, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (24, 1), (51, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (22, 1), (54, 1), (61, 1)] }, { coefficient := -1, powers := [(16, 1), (31, 1), (37, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (28, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (16, 1), (34, 1), (37, 1), (61, 1), (65, 1)] }, { coefficient := 1, powers := [(16, 1), (28, 1), (47, 1), (61, 1)] }, { coefficient := 1, powers := [(16, 1), (34, 1), (37, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (22, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (31, 1), (37, 1), (45, 1)] }, { coefficient := 2, powers := [(17, 1), (31, 1), (37, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (31, 1), (37, 1), (44, 1)] }, { coefficient := -1, powers := [(17, 1), (31, 1), (37, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (34, 1), (37, 1)] }],
  [{ coefficient := -1, powers := [(17, 1), (54, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (31, 1), (33, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (24, 1), (42, 1), (51, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (28, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (12, 1), (47, 1), (51, 1)] }, { coefficient := 1, powers := [(12, 1), (19, 1), (42, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (24, 1), (39, 1), (42, 1), (51, 1), (64, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (42, 1), (44, 1), (51, 1), (64, 1)] }, { coefficient := 1, powers := [(13, 1), (17, 1), (54, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(54, 1)] }],
  [{ coefficient := 1, powers := [(47, 1)] }],
  [{ coefficient := 1, powers := [(28, 1)] }],
  [{ coefficient := 1, powers := [(22, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (34, 1), (37, 1), (49, 1)] }],
  [{ coefficient := -1, powers := [(16, 1), (22, 1)] }],
  [{ coefficient := -1, powers := [(16, 1), (28, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (21, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (24, 1), (47, 1), (51, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (24, 1), (42, 1), (46, 1), (51, 1), (64, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (47, 1), (51, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(10, 1), (31, 1), (37, 1)] }, { coefficient := 1, powers := [(14, 1), (31, 1), (37, 1)] }],
  [{ coefficient := -1, powers := [(16, 1), (34, 1), (37, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (34, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (20, 1), (31, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (17, 1), (31, 1), (37, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (34, 1), (37, 1), (51, 1)] }, { coefficient := -1, powers := [(12, 1), (34, 1), (37, 1), (56, 1)] }, { coefficient := -1, powers := [(16, 1), (34, 1), (37, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(16, 1)] }],
  [{ coefficient := -1, powers := [(17, 1), (31, 1), (37, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(0, 1), (16, 1), (34, 1), (37, 1), (49, 1), (65, 1)] }, { coefficient := -1, powers := [(16, 1), (22, 1), (42, 1), (54, 1)] }, { coefficient := -1, powers := [(16, 1), (28, 1), (47, 1), (49, 1)] }, { coefficient := 1, powers := [(16, 1), (31, 1), (37, 1), (42, 1)] }],
  [{ coefficient := -1, powers := [(16, 1), (31, 1), (37, 1), (44, 1), (45, 1)] }, { coefficient := 1, powers := [(17, 1), (31, 1), (36, 1), (37, 1), (59, 1)] }, { coefficient := 1, powers := [(17, 1), (31, 1), (37, 1), (39, 1), (56, 1)] }, { coefficient := -2, powers := [(17, 1), (31, 1), (37, 1), (44, 1), (51, 1)] }, { coefficient := 1, powers := [(17, 1), (31, 1), (37, 1), (51, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(37, 1), (60, 1)] }, { coefficient := 1, powers := [(40, 1), (57, 1)] }, { coefficient := -1, powers := [(47, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (34, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (22, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (22, 1), (24, 1), (42, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (31, 1)] }, { coefficient := 1, powers := [(12, 1), (19, 1), (21, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (12, 1), (34, 1), (37, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (17, 1), (31, 1), (37, 1), (59, 1)] }, { coefficient := 1, powers := [(10, 1), (16, 1), (31, 1), (37, 1), (45, 1)] }, { coefficient := -1, powers := [(10, 1), (17, 1), (31, 1), (37, 1), (44, 1)] }, { coefficient := 1, powers := [(10, 1), (17, 1), (31, 1), (37, 1), (56, 1)] }, { coefficient := -1, powers := [(14, 1), (16, 1), (31, 1), (37, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (17, 1), (26, 1), (46, 1), (54, 1), (63, 1)] }, { coefficient := -1, powers := [(17, 1), (19, 1), (26, 1), (43, 1), (54, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (3, 1), (12, 1), (28, 1), (47, 1), (51, 1)] }, { coefficient := 1, powers := [(0, 1), (12, 1), (34, 1), (35, 1), (37, 1), (51, 1)] }, { coefficient := 1, powers := [(0, 1), (12, 1), (34, 1), (35, 1), (37, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (16, 1), (34, 1), (35, 1), (37, 1), (52, 1)] }, { coefficient := -1, powers := [(3, 1), (12, 1), (19, 1), (28, 1), (42, 1), (51, 1)] }, { coefficient := 1, powers := [(3, 1), (12, 1), (23, 1), (34, 1), (37, 1), (51, 1)] }, { coefficient := 1, powers := [(3, 1), (12, 1), (23, 1), (34, 1), (37, 1), (56, 1)] }, { coefficient := -1, powers := [(3, 1), (12, 1), (24, 1), (26, 1), (47, 1), (51, 1)] }, { coefficient := -1, powers := [(3, 1), (12, 1), (34, 1), (37, 1)] }, { coefficient := 1, powers := [(3, 1), (16, 1), (23, 1), (34, 1), (37, 1), (52, 1)] }, { coefficient := -1, powers := [(4, 1), (17, 1), (20, 1), (31, 1), (37, 1)] }, { coefficient := 1, powers := [(6, 1), (12, 1), (18, 1), (34, 1), (37, 1), (51, 1)] }, { coefficient := 1, powers := [(6, 1), (12, 1), (18, 1), (34, 1), (37, 1), (56, 1)] }, { coefficient := -1, powers := [(6, 1), (12, 1), (21, 1), (24, 1), (47, 1), (51, 1)] }, { coefficient := -1, powers := [(6, 1), (12, 1), (22, 1), (24, 1), (39, 1), (42, 1), (51, 1), (64, 1)] }, { coefficient := -1, powers := [(6, 1), (12, 1), (22, 1), (24, 1), (42, 1), (44, 1), (51, 1), (64, 1)] }, { coefficient := 1, powers := [(6, 1), (12, 1), (24, 1), (27, 1), (42, 1), (46, 1), (51, 1), (64, 1)] }, { coefficient := -1, powers := [(6, 1), (12, 1), (24, 1), (27, 1), (47, 1), (51, 1), (64, 1)] }, { coefficient := -1, powers := [(6, 1), (13, 1), (17, 1), (22, 1), (54, 1), (63, 1)] }, { coefficient := 1, powers := [(6, 1), (16, 1), (18, 1), (34, 1), (37, 1), (52, 1)] }, { coefficient := 1, powers := [(6, 1), (16, 1), (34, 1), (37, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (16, 1), (31, 1), (33, 1), (37, 1), (45, 1)] }, { coefficient := -1, powers := [(4, 1), (17, 1), (30, 1), (31, 1), (37, 1), (56, 1)] }, { coefficient := 1, powers := [(4, 1), (17, 1), (31, 1), (33, 1), (37, 1), (51, 1)] }, { coefficient := 1, powers := [(7, 1), (16, 1), (31, 1), (33, 1), (37, 1), (45, 1)] }, { coefficient := -1, powers := [(7, 1), (17, 1), (30, 1), (31, 1), (37, 1), (56, 1)] }, { coefficient := 1, powers := [(7, 1), (17, 1), (31, 1), (33, 1), (37, 1), (51, 1)] }]
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
    ¬ ∀ index : Fin 57,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component39.SelectedLeafB4_2_6_5_1.selectedHasNoCommonZero

end Krenn.Component39.SelectedLeafB4_2_6_5_1
