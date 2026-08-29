import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component39.SelectedLeafB4_3_4

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "913ba2b2f7a3cb35c490b419c4a01c63bb56c9967e899cd333c33107d5693d05"
def certificateSHA256 : String := "6ecdeab09186d15b3d889bc6195c7467069a8618549e79c2ed8a098771ccaef8"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 50 → Fin 670 := ![
  10,
  11,
  14,
  19,
  21,
  22,
  23,
  30,
  170,
  171,
  172,
  187,
  188,
  191,
  192,
  194,
  197,
  250,
  268,
  300,
  302,
  304,
  305,
  313,
  316,
  317,
  356,
  360,
  363,
  369,
  382,
  417,
  419,
  425,
  433,
  439,
  479,
  542,
  563,
  602,
  603,
  659,
  660,
  661,
  662,
  663,
  665,
  666,
  668,
  669
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 50 → SparsePoly (Fin 65) := ![
  [{ coefficient := 1, powers := [(5, 1), (33, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (30, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (20, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (20, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (34, 1)] }, { coefficient := 1, powers := [(10, 1), (26, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (31, 1)] }, { coefficient := 1, powers := [(14, 1), (21, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (18, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (42, 1)] }, { coefficient := 1, powers := [(17, 1), (18, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (54, 1)] }, { coefficient := 1, powers := [(28, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (42, 1)] }, { coefficient := 1, powers := [(26, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (40, 1)] }, { coefficient := 1, powers := [(25, 1), (46, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(30, 1), (37, 1)] }, { coefficient := 1, powers := [(33, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (23, 1), (44, 1)] }, { coefficient := 1, powers := [(16, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (19, 1), (52, 1)] }, { coefficient := 1, powers := [(14, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1)] }, { coefficient := 1, powers := [(18, 1), (42, 1)] }, { coefficient := 1, powers := [(23, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (49, 1)] }, { coefficient := 1, powers := [(18, 1), (49, 1)] }, { coefficient := 1, powers := [(23, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (44, 1)] }, { coefficient := 1, powers := [(4, 1), (33, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (51, 1)] }, { coefficient := 1, powers := [(7, 1), (30, 1)] }, { coefficient := 1, powers := [(10, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (44, 1)] }, { coefficient := 1, powers := [(12, 1), (56, 1)] }, { coefficient := 1, powers := [(16, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (45, 1)] }, { coefficient := 1, powers := [(17, 1), (39, 1)] }, { coefficient := 1, powers := [(17, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (51, 1)] }, { coefficient := 1, powers := [(22, 1), (56, 1)] }, { coefficient := 1, powers := [(27, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (28, 1), (60, 1)] }, { coefficient := 1, powers := [(4, 1), (31, 1), (57, 1)] }, { coefficient := 1, powers := [(4, 1), (34, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (30, 1), (57, 1)] }, { coefficient := 1, powers := [(8, 1), (30, 1), (47, 1)] }, { coefficient := 1, powers := [(17, 1), (30, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (33, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (40, 1)] }, { coefficient := 1, powers := [(12, 1), (33, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (22, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (31, 1), (47, 1)] }, { coefficient := 1, powers := [(7, 1), (34, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (18, 1), (56, 1)] }, { coefficient := 1, powers := [(12, 1)] }, { coefficient := 1, powers := [(16, 1), (18, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (45, 1)] }, { coefficient := 1, powers := [(16, 1), (26, 1), (45, 1)] }, { coefficient := 1, powers := [(17, 1), (26, 1), (39, 1)] }, { coefficient := 1, powers := [(17, 1), (27, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (47, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1)] }, { coefficient := 1, powers := [(16, 1), (26, 1), (47, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1)] }, { coefficient := 1, powers := [(12, 1), (28, 1)] }, { coefficient := 1, powers := [(16, 1), (21, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (59, 1)] }, { coefficient := 1, powers := [(16, 1), (24, 1), (39, 1)] }, { coefficient := 1, powers := [(16, 1), (24, 1), (44, 1)] }, { coefficient := 1, powers := [(16, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (39, 1)] }, { coefficient := 1, powers := [(16, 1), (44, 1)] }, { coefficient := 1, powers := [(16, 1), (51, 1)] }, { coefficient := 1, powers := [(16, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (40, 1), (56, 1)] }, { coefficient := 1, powers := [(1, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(7, 1), (33, 1), (40, 1)] }, { coefficient := 1, powers := [(14, 1), (25, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (20, 1), (59, 1)] }, { coefficient := 1, powers := [(8, 1), (30, 1), (44, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (39, 1)] }, { coefficient := 1, powers := [(16, 1), (20, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (25, 1), (45, 1)] }, { coefficient := 1, powers := [(17, 1), (20, 1), (51, 1)] }, { coefficient := 1, powers := [(17, 1), (25, 1), (39, 1)] }, { coefficient := 1, powers := [(17, 1), (30, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (59, 1)] }, { coefficient := 1, powers := [(10, 1), (44, 1)] }, { coefficient := 1, powers := [(10, 1), (56, 1)] }, { coefficient := 1, powers := [(14, 1), (39, 1)] }, { coefficient := 1, powers := [(14, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (51, 1)] }, { coefficient := 1, powers := [(20, 1), (56, 1)] }, { coefficient := 1, powers := [(25, 1), (39, 1)] }, { coefficient := 1, powers := [(25, 1), (44, 1)] }, { coefficient := 1, powers := [(30, 1), (36, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (36, 1), (59, 1)] }, { coefficient := 1, powers := [(1, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(1, 1), (44, 1), (51, 1)] }, { coefficient := 1, powers := [(4, 1), (25, 1), (59, 1)] }, { coefficient := 1, powers := [(4, 1), (30, 1), (56, 1)] }, { coefficient := 1, powers := [(4, 1), (33, 1), (51, 1)] }, { coefficient := 1, powers := [(7, 1), (20, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (30, 1), (44, 1)] }, { coefficient := 1, powers := [(7, 1), (33, 1), (39, 1)] }, { coefficient := 1, powers := [(10, 1), (20, 1), (56, 1)] }, { coefficient := 1, powers := [(10, 1), (25, 1), (44, 1)] }, { coefficient := 1, powers := [(10, 1), (33, 1), (36, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1), (51, 1)] }, { coefficient := 1, powers := [(14, 1), (25, 1), (39, 1)] }, { coefficient := 1, powers := [(14, 1), (30, 1), (36, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (37, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (47, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (28, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (22, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1), (47, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (40, 1)] }, { coefficient := 1, powers := [(12, 1), (22, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1), (28, 1), (47, 1)] }, { coefficient := 1, powers := [(12, 1), (34, 1), (37, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (54, 1)] }, { coefficient := 1, powers := [(17, 1), (28, 1), (40, 1)] }, { coefficient := 1, powers := [(17, 1), (31, 1), (37, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (61, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1)] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(39, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(40, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(56, 1)] }],
  [{ coefficient := 1, powers := [(57, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 50 → SparsePoly (Fin 65) := ![
  [{ coefficient := 1, powers := [(10, 1), (28, 1), (36, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(10, 1), (22, 1), (36, 1), (44, 1), (60, 1), (62, 1)] }, { coefficient := 1, powers := [(10, 1), (31, 1), (36, 1), (47, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (20, 1), (26, 1), (54, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(17, 1), (20, 1), (21, 1), (37, 1), (59, 1)] }, { coefficient := 1, powers := [(19, 1), (20, 1), (51, 1), (63, 1)] }, { coefficient := 1, powers := [(19, 1), (33, 1), (36, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(10, 1), (22, 1), (24, 1), (36, 1), (51, 1), (60, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (10, 1), (20, 1), (28, 1), (40, 1), (45, 1), (59, 1)] }, { coefficient := 1, powers := [(10, 2), (22, 1), (33, 1), (36, 1), (45, 1), (54, 1)] }, { coefficient := 1, powers := [(10, 2), (28, 1), (33, 1), (36, 1), (40, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(7, 2), (20, 1), (28, 1), (40, 1), (59, 2)] }, { coefficient := 1, powers := [(7, 1), (10, 1), (22, 1), (33, 1), (36, 1), (54, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (10, 1), (28, 1), (33, 1), (36, 1), (40, 1), (59, 1)] }, { coefficient := -1, powers := [(7, 1), (14, 1), (20, 1), (28, 1), (40, 1), (51, 1), (59, 1)] }, { coefficient := -1, powers := [(10, 1), (14, 1), (22, 1), (33, 1), (36, 1), (51, 1), (54, 1)] }, { coefficient := -1, powers := [(10, 1), (14, 1), (28, 1), (33, 1), (36, 1), (40, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(7, 2), (17, 1), (20, 1), (28, 1), (40, 1), (49, 1), (59, 2), (63, 1)] }, { coefficient := 2, powers := [(7, 1), (10, 1), (17, 1), (20, 1), (28, 1), (40, 1), (44, 1), (49, 1), (59, 1), (63, 1)] }, { coefficient := 1, powers := [(7, 1), (10, 1), (17, 1), (22, 1), (33, 1), (36, 1), (49, 1), (54, 1), (59, 1), (63, 1)] }, { coefficient := 1, powers := [(7, 1), (10, 1), (17, 1), (28, 1), (33, 1), (36, 1), (40, 1), (49, 1), (59, 1), (63, 1)] }, { coefficient := -1, powers := [(7, 1), (14, 1), (16, 1), (20, 1), (28, 1), (40, 1), (45, 1), (49, 1), (59, 1), (63, 1)] }, { coefficient := -1, powers := [(7, 1), (14, 1), (17, 1), (20, 1), (28, 1), (40, 1), (49, 1), (51, 1), (59, 1), (63, 1)] }, { coefficient := 1, powers := [(7, 1), (49, 1), (59, 1), (63, 1)] }, { coefficient := 2, powers := [(10, 2), (17, 1), (22, 1), (33, 1), (36, 1), (44, 1), (49, 1), (54, 1), (63, 1)] }, { coefficient := 2, powers := [(10, 2), (17, 1), (28, 1), (33, 1), (36, 1), (40, 1), (44, 1), (49, 1), (63, 1)] }, { coefficient := -1, powers := [(10, 1), (14, 1), (16, 1), (22, 1), (33, 1), (36, 1), (45, 1), (49, 1), (54, 1), (63, 1)] }, { coefficient := -1, powers := [(10, 1), (14, 1), (16, 1), (28, 1), (33, 1), (36, 1), (40, 1), (45, 1), (49, 1), (63, 1)] }, { coefficient := -1, powers := [(10, 1), (14, 1), (17, 1), (22, 1), (33, 1), (36, 1), (49, 1), (51, 1), (54, 1), (63, 1)] }, { coefficient := -1, powers := [(10, 1), (14, 1), (17, 1), (28, 1), (33, 1), (36, 1), (40, 1), (49, 1), (51, 1), (63, 1)] }, { coefficient := 1, powers := [(10, 1), (44, 1), (49, 1), (63, 1)] }, { coefficient := 2, powers := [(14, 1), (39, 1), (49, 1), (63, 1)] }, { coefficient := 1, powers := [(14, 1), (44, 1), (49, 1), (63, 1)] }, { coefficient := 1, powers := [(14, 1), (49, 1), (51, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (20, 1), (54, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (20, 1), (28, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (20, 1), (37, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (20, 1), (26, 1), (42, 1), (46, 1), (54, 1), (59, 1), (61, 1)] }, { coefficient := -1, powers := [(7, 1), (20, 1), (28, 1), (47, 1), (49, 1), (59, 1), (61, 1)] }, { coefficient := -1, powers := [(7, 1), (20, 1), (28, 1), (47, 1), (52, 1), (59, 1)] }, { coefficient := -1, powers := [(7, 1), (20, 1), (34, 1), (37, 1), (49, 1), (59, 1), (61, 1)] }, { coefficient := -1, powers := [(7, 1), (20, 1), (34, 1), (37, 1), (52, 1), (59, 1)] }, { coefficient := -1, powers := [(10, 1), (28, 1), (33, 1), (36, 1), (47, 1), (49, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (20, 1), (22, 1), (54, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (20, 1), (26, 1), (46, 1), (54, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(10, 1), (16, 1), (33, 1), (36, 1), (47, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (16, 1), (20, 1), (54, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(7, 2), (17, 1), (20, 1), (28, 1), (40, 1), (59, 2), (63, 1)] }, { coefficient := -2, powers := [(7, 1), (10, 1), (17, 1), (20, 1), (28, 1), (40, 1), (44, 1), (59, 1), (63, 1)] }, { coefficient := -1, powers := [(7, 1), (10, 1), (17, 1), (22, 1), (33, 1), (36, 1), (54, 1), (59, 1), (63, 1)] }, { coefficient := -1, powers := [(7, 1), (10, 1), (17, 1), (28, 1), (33, 1), (36, 1), (40, 1), (59, 1), (63, 1)] }, { coefficient := 1, powers := [(7, 1), (14, 1), (16, 1), (20, 1), (28, 1), (40, 1), (45, 1), (59, 1), (63, 1)] }, { coefficient := 1, powers := [(7, 1), (14, 1), (17, 1), (20, 1), (28, 1), (40, 1), (51, 1), (59, 1), (63, 1)] }, { coefficient := -1, powers := [(7, 1), (59, 1), (63, 1)] }, { coefficient := -2, powers := [(10, 2), (17, 1), (22, 1), (33, 1), (36, 1), (44, 1), (54, 1), (63, 1)] }, { coefficient := -2, powers := [(10, 2), (17, 1), (28, 1), (33, 1), (36, 1), (40, 1), (44, 1), (63, 1)] }, { coefficient := 1, powers := [(10, 1), (14, 1), (16, 1), (22, 1), (33, 1), (36, 1), (45, 1), (54, 1), (63, 1)] }, { coefficient := 1, powers := [(10, 1), (14, 1), (16, 1), (28, 1), (33, 1), (36, 1), (40, 1), (45, 1), (63, 1)] }, { coefficient := 1, powers := [(10, 1), (14, 1), (17, 1), (22, 1), (33, 1), (36, 1), (51, 1), (54, 1), (63, 1)] }, { coefficient := 1, powers := [(10, 1), (14, 1), (17, 1), (28, 1), (33, 1), (36, 1), (40, 1), (51, 1), (63, 1)] }, { coefficient := -1, powers := [(10, 1), (44, 1), (63, 1)] }, { coefficient := -2, powers := [(14, 1), (39, 1), (63, 1)] }, { coefficient := -1, powers := [(14, 1), (44, 1), (63, 1)] }, { coefficient := -1, powers := [(14, 1), (51, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (17, 1), (31, 1), (36, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (20, 1), (28, 1), (47, 1), (59, 1)] }, { coefficient := -1, powers := [(7, 1), (20, 1), (34, 1), (37, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(20, 1), (51, 1), (63, 1)] }, { coefficient := -1, powers := [(33, 1), (36, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (16, 1), (20, 1), (26, 1), (46, 1), (54, 1), (59, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (16, 1), (20, 1), (28, 1), (47, 1), (59, 1), (61, 1)] }, { coefficient := 1, powers := [(7, 1), (16, 1), (20, 1), (34, 1), (37, 1), (59, 1), (61, 1)] }, { coefficient := 1, powers := [(10, 1), (16, 1), (28, 1), (33, 1), (36, 1), (47, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (17, 1), (20, 1), (28, 1), (40, 1), (51, 1), (59, 1)] }, { coefficient := 1, powers := [(10, 1), (17, 1), (22, 1), (33, 1), (36, 1), (51, 1), (54, 1)] }, { coefficient := 1, powers := [(10, 1), (17, 1), (28, 1), (33, 1), (36, 1), (40, 1), (51, 1)] }, { coefficient := 1, powers := [(51, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (17, 1), (20, 1), (28, 1), (40, 1), (44, 1), (59, 1)] }, { coefficient := 1, powers := [(10, 1), (17, 1), (22, 1), (33, 1), (36, 1), (44, 1), (54, 1)] }, { coefficient := 1, powers := [(10, 1), (17, 1), (28, 1), (33, 1), (36, 1), (40, 1), (44, 1)] }, { coefficient := 1, powers := [(44, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (20, 1), (23, 1), (28, 1), (47, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (20, 1), (23, 1), (34, 1), (37, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(7, 2), (20, 1), (28, 1), (33, 1), (40, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (10, 1), (22, 1), (33, 2), (36, 1), (54, 1)] }, { coefficient := 1, powers := [(7, 1), (10, 1), (28, 1), (33, 2), (36, 1), (40, 1)] }, { coefficient := -1, powers := [(7, 1), (14, 1), (20, 1), (25, 1), (28, 1), (40, 1), (59, 1)] }, { coefficient := -1, powers := [(7, 1), (18, 1), (20, 1), (26, 1), (46, 1), (54, 1), (59, 1)] }, { coefficient := -1, powers := [(10, 1), (14, 1), (22, 1), (25, 1), (33, 1), (36, 1), (54, 1)] }, { coefficient := -1, powers := [(10, 1), (14, 1), (25, 1), (28, 1), (33, 1), (36, 1), (40, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (17, 1), (18, 1), (20, 1), (54, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (20, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(10, 1), (31, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (34, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (20, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (20, 1), (28, 1), (47, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (20, 1), (34, 1), (37, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (18, 1), (20, 1), (46, 1), (54, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (20, 1), (54, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (33, 1), (36, 1), (47, 1)] }],
  [{ coefficient := -1, powers := [(10, 1), (20, 1), (22, 1), (36, 1), (60, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (20, 1), (22, 1), (24, 1), (36, 1), (60, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (16, 1), (20, 1), (28, 1), (40, 1), (45, 1), (59, 1), (63, 1)] }, { coefficient := -1, powers := [(7, 1), (17, 1), (20, 1), (28, 1), (40, 1), (51, 1), (59, 1), (63, 1)] }, { coefficient := -1, powers := [(10, 1), (16, 1), (22, 1), (33, 1), (36, 1), (45, 1), (54, 1), (63, 1)] }, { coefficient := -1, powers := [(10, 1), (16, 1), (28, 1), (33, 1), (36, 1), (40, 1), (45, 1), (63, 1)] }, { coefficient := -1, powers := [(10, 1), (17, 1), (22, 1), (33, 1), (36, 1), (51, 1), (54, 1), (63, 1)] }, { coefficient := -1, powers := [(10, 1), (17, 1), (28, 1), (33, 1), (36, 1), (40, 1), (51, 1), (63, 1)] }, { coefficient := 1, powers := [(39, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (22, 1), (36, 1), (60, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (10, 1), (20, 1), (28, 1), (40, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (14, 1), (20, 1), (28, 1), (40, 1), (59, 1)] }, { coefficient := -1, powers := [(10, 2), (22, 1), (33, 1), (36, 1), (54, 1)] }, { coefficient := -1, powers := [(10, 2), (28, 1), (33, 1), (36, 1), (40, 1)] }, { coefficient := 1, powers := [(10, 1), (14, 1), (22, 1), (33, 1), (36, 1), (54, 1)] }, { coefficient := 1, powers := [(10, 1), (14, 1), (28, 1), (33, 1), (36, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (17, 1), (20, 1), (25, 1), (28, 1), (40, 1), (59, 1)] }, { coefficient := 1, powers := [(10, 1), (17, 1), (22, 1), (25, 1), (33, 1), (36, 1), (54, 1)] }, { coefficient := 1, powers := [(10, 1), (17, 1), (25, 1), (28, 1), (33, 1), (36, 1), (40, 1)] }, { coefficient := 1, powers := [(25, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (10, 1), (17, 1), (20, 1), (28, 1), (40, 1), (59, 1)] }, { coefficient := 1, powers := [(10, 2), (17, 1), (22, 1), (33, 1), (36, 1), (54, 1)] }, { coefficient := 1, powers := [(10, 2), (17, 1), (28, 1), (33, 1), (36, 1), (40, 1)] }, { coefficient := 1, powers := [(14, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (17, 1), (20, 1), (28, 1), (40, 1), (59, 1)] }, { coefficient := -1, powers := [(10, 1), (17, 1), (22, 1), (33, 1), (36, 1), (54, 1)] }, { coefficient := -1, powers := [(10, 1), (17, 1), (28, 1), (33, 1), (36, 1), (40, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(7, 1), (20, 1), (59, 1)] }, { coefficient := -1, powers := [(10, 1), (33, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (16, 1), (20, 1), (26, 1), (42, 1), (46, 1), (54, 1), (59, 1)] }, { coefficient := -1, powers := [(7, 1), (16, 1), (20, 1), (28, 1), (47, 1), (49, 1), (59, 1)] }, { coefficient := -1, powers := [(7, 1), (16, 1), (20, 1), (34, 1), (37, 1), (49, 1), (59, 1)] }, { coefficient := -1, powers := [(10, 1), (16, 1), (28, 1), (33, 1), (36, 1), (47, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (16, 1), (20, 1), (28, 1), (40, 2), (45, 1), (56, 1), (59, 1), (63, 1)] }, { coefficient := 1, powers := [(7, 1), (16, 1), (20, 1), (28, 1), (40, 1), (45, 1), (46, 1), (52, 1), (59, 1), (63, 1)] }, { coefficient := 1, powers := [(7, 1), (17, 1), (20, 1), (28, 1), (36, 1), (40, 1), (59, 2)] }, { coefficient := 1, powers := [(7, 1), (17, 1), (20, 1), (28, 1), (39, 1), (40, 1), (56, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (17, 1), (20, 1), (28, 1), (40, 2), (51, 1), (56, 1), (59, 1), (63, 1)] }, { coefficient := -1, powers := [(7, 1), (17, 1), (20, 1), (28, 1), (40, 1), (44, 1), (51, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (17, 1), (20, 1), (28, 1), (40, 1), (46, 1), (51, 1), (52, 1), (59, 1), (63, 1)] }, { coefficient := 1, powers := [(10, 1), (16, 1), (22, 1), (33, 1), (36, 1), (40, 1), (45, 1), (54, 1), (56, 1), (63, 1)] }, { coefficient := 1, powers := [(10, 1), (16, 1), (22, 1), (33, 1), (36, 1), (45, 1), (46, 1), (52, 1), (54, 1), (63, 1)] }, { coefficient := 1, powers := [(10, 1), (16, 1), (28, 1), (33, 1), (36, 1), (40, 2), (45, 1), (56, 1), (63, 1)] }, { coefficient := 1, powers := [(10, 1), (16, 1), (28, 1), (33, 1), (36, 1), (40, 1), (45, 1), (46, 1), (52, 1), (63, 1)] }, { coefficient := 1, powers := [(10, 1), (17, 1), (22, 1), (33, 1), (36, 2), (54, 1), (59, 1)] }, { coefficient := 1, powers := [(10, 1), (17, 1), (22, 1), (33, 1), (36, 1), (39, 1), (54, 1), (56, 1)] }, { coefficient := 1, powers := [(10, 1), (17, 1), (22, 1), (33, 1), (36, 1), (40, 1), (51, 1), (54, 1), (56, 1), (63, 1)] }, { coefficient := -1, powers := [(10, 1), (17, 1), (22, 1), (33, 1), (36, 1), (44, 1), (51, 1), (54, 1)] }, { coefficient := 1, powers := [(10, 1), (17, 1), (22, 1), (33, 1), (36, 1), (46, 1), (51, 1), (52, 1), (54, 1), (63, 1)] }, { coefficient := 1, powers := [(10, 1), (17, 1), (28, 1), (33, 1), (36, 2), (40, 1), (59, 1)] }, { coefficient := 1, powers := [(10, 1), (17, 1), (28, 1), (33, 1), (36, 1), (39, 1), (40, 1), (56, 1)] }, { coefficient := 1, powers := [(10, 1), (17, 1), (28, 1), (33, 1), (36, 1), (40, 2), (51, 1), (56, 1), (63, 1)] }, { coefficient := -1, powers := [(10, 1), (17, 1), (28, 1), (33, 1), (36, 1), (40, 1), (44, 1), (51, 1)] }, { coefficient := 1, powers := [(10, 1), (17, 1), (28, 1), (33, 1), (36, 1), (40, 1), (46, 1), (51, 1), (52, 1), (63, 1)] }, { coefficient := 1, powers := [(36, 1), (59, 1)] }, { coefficient := -1, powers := [(39, 1), (40, 1), (56, 1), (63, 1)] }, { coefficient := -1, powers := [(39, 1), (46, 1), (52, 1), (63, 1)] }, { coefficient := 1, powers := [(39, 1), (56, 1)] }, { coefficient := -1, powers := [(44, 1), (51, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (18, 1), (20, 1), (45, 1), (46, 1), (54, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (20, 1), (37, 1), (59, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (20, 1), (40, 1), (57, 1), (59, 1)] }, { coefficient := 1, powers := [(10, 1), (33, 1), (36, 1), (37, 1), (60, 1)] }, { coefficient := 1, powers := [(10, 1), (33, 1), (36, 1), (40, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (10, 1), (22, 1), (33, 1), (36, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(7, 2), (16, 1), (20, 1), (28, 1), (33, 1), (40, 1), (45, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 2), (17, 1), (20, 1), (25, 1), (28, 1), (40, 1), (59, 2)] }, { coefficient := 1, powers := [(7, 2), (17, 1), (20, 1), (28, 1), (33, 1), (40, 1), (51, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (10, 1), (16, 1), (22, 1), (33, 2), (36, 1), (45, 1), (54, 1)] }, { coefficient := 1, powers := [(7, 1), (10, 1), (16, 1), (28, 1), (33, 2), (36, 1), (40, 1), (45, 1)] }, { coefficient := 2, powers := [(7, 1), (10, 1), (17, 1), (20, 1), (25, 1), (28, 1), (40, 1), (44, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (10, 1), (17, 1), (22, 1), (25, 1), (33, 1), (36, 1), (54, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (10, 1), (17, 1), (22, 1), (33, 2), (36, 1), (51, 1), (54, 1)] }, { coefficient := 1, powers := [(7, 1), (10, 1), (17, 1), (25, 1), (28, 1), (33, 1), (36, 1), (40, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (10, 1), (17, 1), (28, 1), (33, 2), (36, 1), (40, 1), (51, 1)] }, { coefficient := 1, powers := [(7, 1), (25, 1), (59, 1)] }, { coefficient := -1, powers := [(7, 1), (33, 1), (39, 1)] }, { coefficient := 2, powers := [(10, 2), (17, 1), (22, 1), (25, 1), (33, 1), (36, 1), (44, 1), (54, 1)] }, { coefficient := 2, powers := [(10, 2), (17, 1), (25, 1), (28, 1), (33, 1), (36, 1), (40, 1), (44, 1)] }, { coefficient := 1, powers := [(10, 1), (25, 1), (44, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1), (51, 1)] }, { coefficient := 1, powers := [(14, 1), (25, 1), (39, 1)] }, { coefficient := 1, powers := [(14, 1), (25, 1), (44, 1)] }, { coefficient := 1, powers := [(14, 1), (25, 1), (51, 1)] }, { coefficient := 1, powers := [(14, 1), (33, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (7, 1), (17, 1), (20, 1), (28, 1), (30, 1), (40, 1), (59, 1)] }, { coefficient := 1, powers := [(4, 1), (10, 1), (17, 1), (22, 1), (30, 1), (33, 1), (36, 1), (54, 1)] }, { coefficient := 1, powers := [(4, 1), (10, 1), (17, 1), (28, 1), (30, 1), (33, 1), (36, 1), (40, 1)] }, { coefficient := 1, powers := [(4, 1), (30, 1)] }, { coefficient := -1, powers := [(7, 1), (10, 1), (17, 1), (20, 1), (25, 1), (28, 1), (40, 1), (59, 1)] }, { coefficient := -1, powers := [(7, 1), (12, 1), (18, 1), (20, 1), (28, 1), (47, 1), (59, 1)] }, { coefficient := -1, powers := [(7, 1), (12, 1), (18, 1), (20, 1), (34, 1), (37, 1), (59, 1)] }, { coefficient := -1, powers := [(7, 1), (12, 1), (20, 1), (23, 1), (28, 1), (47, 1), (59, 1)] }, { coefficient := -1, powers := [(7, 1), (12, 1), (20, 1), (23, 1), (34, 1), (37, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (17, 1), (18, 1), (20, 1), (22, 1), (54, 1), (59, 1)] }, { coefficient := -1, powers := [(10, 2), (17, 1), (22, 1), (25, 1), (33, 1), (36, 1), (54, 1)] }, { coefficient := -1, powers := [(10, 2), (17, 1), (25, 1), (28, 1), (33, 1), (36, 1), (40, 1)] }, { coefficient := -1, powers := [(10, 1), (16, 1), (20, 1), (22, 1), (24, 1), (36, 1), (60, 1), (62, 1)] }, { coefficient := 1, powers := [(10, 1), (20, 1)] }, { coefficient := -1, powers := [(10, 1), (25, 1)] }, { coefficient := -1, powers := [(14, 1), (20, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (5, 1), (20, 1), (31, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (7, 1), (20, 1), (31, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (10, 1), (30, 1), (31, 1), (36, 1)] }, { coefficient := 1, powers := [(5, 1), (10, 1), (31, 1), (33, 1), (36, 1)] }, { coefficient := 1, powers := [(7, 1), (12, 1), (20, 1), (22, 1), (59, 1)] }, { coefficient := 1, powers := [(10, 1), (12, 1), (22, 1), (33, 1), (36, 1)] }]
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
    (values : Fin 65 → R) :
    ¬ ∀ index : Fin 50,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component39.SelectedLeafB4_3_4.selectedHasNoCommonZero

end Krenn.Component39.SelectedLeafB4_3_4
