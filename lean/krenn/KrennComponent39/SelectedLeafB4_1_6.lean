import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component39.SelectedLeafB4_1_6

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "f1a19a6fb40d5783b72eb39a87bf4ef76dd792850b058e07d59a36a6b1b7ea5f"
def certificateSHA256 : String := "e9c12ef9a50f07cffdd6c08576b27efc1dd002cf475882a4a653402c1ba71acb"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 54 → Fin 670 := ![
  10,
  11,
  14,
  16,
  19,
  21,
  25,
  30,
  170,
  171,
  172,
  181,
  187,
  188,
  189,
  191,
  194,
  197,
  248,
  250,
  268,
  300,
  302,
  303,
  304,
  305,
  313,
  316,
  318,
  356,
  360,
  363,
  369,
  397,
  417,
  419,
  423,
  425,
  434,
  463,
  477,
  482,
  556,
  602,
  603,
  659,
  660,
  661,
  662,
  663,
  665,
  666,
  667,
  669
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 54 → SparsePoly (Fin 65) := ![
  [{ coefficient := 1, powers := [(5, 1), (33, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (30, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (20, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (34, 1)] }, { coefficient := 1, powers := [(10, 1), (26, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (31, 1)] }, { coefficient := 1, powers := [(14, 1), (21, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (24, 1)] }, { coefficient := 1, powers := [(16, 1), (18, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (18, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (42, 1)] }, { coefficient := 1, powers := [(17, 1), (18, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (47, 1)] }, { coefficient := 1, powers := [(17, 1), (19, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (54, 1)] }, { coefficient := 1, powers := [(28, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (40, 1)] }, { coefficient := 1, powers := [(25, 1), (46, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(30, 1), (37, 1)] }, { coefficient := 1, powers := [(33, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (20, 1), (55, 1)] }, { coefficient := 1, powers := [(15, 1), (20, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (23, 1), (44, 1)] }, { coefficient := 1, powers := [(16, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (19, 1), (52, 1)] }, { coefficient := 1, powers := [(14, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1)] }, { coefficient := 1, powers := [(18, 1), (42, 1)] }, { coefficient := 1, powers := [(23, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (49, 1)] }, { coefficient := 1, powers := [(18, 1), (49, 1)] }, { coefficient := 1, powers := [(23, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (54, 1)] }, { coefficient := 1, powers := [(18, 1), (54, 1)] }, { coefficient := 1, powers := [(24, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (44, 1)] }, { coefficient := 1, powers := [(4, 1), (33, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (51, 1)] }, { coefficient := 1, powers := [(7, 1), (30, 1)] }, { coefficient := 1, powers := [(10, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (44, 1)] }, { coefficient := 1, powers := [(12, 1), (56, 1)] }, { coefficient := 1, powers := [(16, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (45, 1)] }, { coefficient := 1, powers := [(17, 1), (39, 1)] }, { coefficient := 1, powers := [(17, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (53, 1)] }, { coefficient := 1, powers := [(28, 1), (39, 1)] }, { coefficient := 1, powers := [(28, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (28, 1), (60, 1)] }, { coefficient := 1, powers := [(4, 1), (31, 1), (57, 1)] }, { coefficient := 1, powers := [(4, 1), (34, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (30, 1), (57, 1)] }, { coefficient := 1, powers := [(8, 1), (30, 1), (47, 1)] }, { coefficient := 1, powers := [(17, 1), (30, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (33, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (40, 1)] }, { coefficient := 1, powers := [(12, 1), (33, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (22, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (31, 1), (47, 1)] }, { coefficient := 1, powers := [(7, 1), (34, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (23, 1), (45, 1)] }, { coefficient := 1, powers := [(17, 1), (23, 1), (39, 1)] }, { coefficient := 1, powers := [(17, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (45, 1)] }, { coefficient := 1, powers := [(16, 1), (26, 1), (45, 1)] }, { coefficient := 1, powers := [(17, 1), (26, 1), (39, 1)] }, { coefficient := 1, powers := [(17, 1), (27, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (47, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1)] }, { coefficient := 1, powers := [(16, 1), (26, 1), (47, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (52, 1)] }, { coefficient := 1, powers := [(12, 1), (21, 1), (56, 1)] }, { coefficient := 1, powers := [(12, 1), (27, 1)] }, { coefficient := 1, powers := [(16, 1), (21, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1)] }, { coefficient := 1, powers := [(12, 1), (28, 1)] }, { coefficient := 1, powers := [(16, 1), (21, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (60, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (45, 1)] }, { coefficient := 1, powers := [(12, 1), (57, 1)] }, { coefficient := 1, powers := [(17, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1), (54, 1)] }, { coefficient := 1, powers := [(24, 1), (45, 1), (49, 1)] }, { coefficient := 1, powers := [(42, 1), (54, 1)] }, { coefficient := 1, powers := [(49, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (39, 1), (55, 1)] }, { coefficient := 1, powers := [(1, 1), (43, 1)] }, { coefficient := 1, powers := [(4, 1), (30, 1), (55, 1)] }, { coefficient := 1, powers := [(10, 1), (20, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (35, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1)] }, { coefficient := 1, powers := [(16, 1), (21, 1)] }, { coefficient := 1, powers := [(16, 1), (26, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (20, 1), (56, 1)] }, { coefficient := 1, powers := [(12, 1), (25, 1), (44, 1)] }, { coefficient := 1, powers := [(12, 1), (33, 1), (36, 1)] }, { coefficient := 1, powers := [(16, 1), (20, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (59, 1)] }, { coefficient := 1, powers := [(10, 1), (44, 1)] }, { coefficient := 1, powers := [(10, 1), (56, 1)] }, { coefficient := 1, powers := [(14, 1), (39, 1)] }, { coefficient := 1, powers := [(14, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (51, 1)] }, { coefficient := 1, powers := [(20, 1), (56, 1)] }, { coefficient := 1, powers := [(25, 1), (39, 1)] }, { coefficient := 1, powers := [(25, 1), (44, 1)] }, { coefficient := 1, powers := [(30, 1), (36, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (36, 1), (59, 1)] }, { coefficient := 1, powers := [(1, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(1, 1), (44, 1), (51, 1)] }, { coefficient := 1, powers := [(4, 1), (25, 1), (59, 1)] }, { coefficient := 1, powers := [(4, 1), (30, 1), (56, 1)] }, { coefficient := 1, powers := [(4, 1), (33, 1), (51, 1)] }, { coefficient := 1, powers := [(7, 1), (20, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (30, 1), (44, 1)] }, { coefficient := 1, powers := [(7, 1), (33, 1), (39, 1)] }, { coefficient := 1, powers := [(10, 1), (20, 1), (56, 1)] }, { coefficient := 1, powers := [(10, 1), (25, 1), (44, 1)] }, { coefficient := 1, powers := [(10, 1), (33, 1), (36, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1), (51, 1)] }, { coefficient := 1, powers := [(14, 1), (25, 1), (39, 1)] }, { coefficient := 1, powers := [(14, 1), (30, 1), (36, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (37, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (47, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (28, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (22, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1), (47, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (40, 1)] }, { coefficient := 1, powers := [(12, 1), (22, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1), (28, 1), (47, 1)] }, { coefficient := 1, powers := [(12, 1), (34, 1), (37, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (54, 1)] }, { coefficient := 1, powers := [(17, 1), (28, 1), (40, 1)] }, { coefficient := 1, powers := [(17, 1), (31, 1), (37, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (61, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1)] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(39, 1)] }],
  [{ coefficient := 1, powers := [(40, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(55, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(57, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 54 → SparsePoly (Fin 65) := ![
  [{ coefficient := 1, powers := [(10, 1), (28, 1), (36, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (31, 1), (36, 1), (47, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (20, 1), (26, 1), (54, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(7, 2), (20, 1), (28, 1), (47, 1), (59, 2)] }, { coefficient := -1, powers := [(7, 2), (20, 1), (34, 1), (37, 1), (59, 2)] }, { coefficient := -2, powers := [(7, 1), (10, 1), (20, 1), (28, 1), (44, 1), (47, 1), (59, 1)] }, { coefficient := -1, powers := [(7, 1), (10, 1), (20, 1), (28, 1), (47, 1), (56, 1), (59, 1)] }, { coefficient := -2, powers := [(7, 1), (10, 1), (20, 1), (34, 1), (37, 1), (44, 1), (59, 1)] }, { coefficient := -1, powers := [(7, 1), (10, 1), (20, 1), (34, 1), (37, 1), (56, 1), (59, 1)] }, { coefficient := -1, powers := [(7, 1), (14, 1), (20, 1), (28, 1), (47, 1), (51, 1), (59, 1)] }, { coefficient := -1, powers := [(7, 1), (14, 1), (20, 1), (34, 1), (37, 1), (51, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(17, 1), (20, 1), (21, 1), (37, 1), (59, 1)] }, { coefficient := 1, powers := [(19, 1), (20, 1), (51, 1), (62, 1)] }, { coefficient := 1, powers := [(19, 1), (20, 1), (56, 1), (62, 1)] }, { coefficient := 1, powers := [(19, 1), (33, 1), (36, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (14, 1), (20, 1), (28, 1), (47, 1), (52, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (14, 1), (20, 1), (34, 1), (37, 1), (52, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(7, 2), (15, 1), (20, 1), (28, 1), (47, 1), (59, 2), (63, 1)] }, { coefficient := -1, powers := [(7, 2), (15, 1), (20, 1), (34, 1), (37, 1), (59, 2), (63, 1)] }, { coefficient := -1, powers := [(7, 1), (10, 1), (15, 1), (20, 1), (28, 1), (44, 1), (47, 1), (59, 1), (63, 1)] }, { coefficient := -1, powers := [(7, 1), (10, 1), (15, 1), (20, 1), (34, 1), (37, 1), (44, 1), (59, 1), (63, 1)] }, { coefficient := 1, powers := [(7, 1), (14, 1), (15, 1), (20, 1), (28, 1), (47, 1), (51, 1), (59, 1), (63, 1)] }, { coefficient := 1, powers := [(7, 1), (14, 1), (15, 1), (20, 1), (34, 1), (37, 1), (51, 1), (59, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (49, 1), (59, 1), (62, 1)] }, { coefficient := 1, powers := [(10, 1), (44, 1), (49, 1), (62, 1)] }, { coefficient := 1, powers := [(10, 1), (49, 1), (56, 1), (62, 1)] }, { coefficient := 1, powers := [(14, 1), (44, 1), (49, 1), (62, 1)] }, { coefficient := 1, powers := [(14, 1), (49, 1), (51, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (20, 1), (54, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (20, 1), (28, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (20, 1), (37, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(10, 1), (22, 1), (33, 1), (36, 1), (45, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (19, 1), (20, 1), (27, 1), (42, 1), (54, 1), (59, 1), (61, 1)] }, { coefficient := -1, powers := [(7, 1), (19, 1), (20, 1), (27, 1), (45, 1), (54, 1), (59, 1)] }, { coefficient := -1, powers := [(7, 1), (20, 1), (28, 1), (40, 1), (42, 1), (59, 1), (61, 1)] }, { coefficient := -1, powers := [(7, 1), (20, 1), (28, 1), (40, 1), (45, 1), (59, 1)] }, { coefficient := -1, powers := [(10, 1), (22, 1), (33, 1), (36, 1), (42, 1), (54, 1), (61, 1)] }, { coefficient := -1, powers := [(10, 1), (26, 1), (33, 1), (36, 1), (47, 1), (49, 1), (53, 1), (61, 1)] }, { coefficient := -1, powers := [(10, 1), (28, 1), (33, 1), (36, 1), (40, 1), (42, 1), (61, 1)] }, { coefficient := -1, powers := [(10, 1), (28, 1), (33, 1), (36, 1), (40, 1), (45, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (19, 1), (20, 1), (27, 1), (54, 1), (59, 1)] }, { coefficient := -1, powers := [(7, 1), (20, 1), (28, 1), (40, 1), (59, 1)] }, { coefficient := -1, powers := [(10, 1), (28, 1), (33, 1), (36, 1), (40, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (20, 1), (26, 1), (54, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(10, 1), (16, 1), (33, 1), (36, 1), (47, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (59, 1), (62, 1)] }, { coefficient := -1, powers := [(10, 1), (44, 1), (62, 1)] }, { coefficient := -1, powers := [(10, 1), (56, 1), (62, 1)] }, { coefficient := -1, powers := [(14, 1), (44, 1), (62, 1)] }, { coefficient := -1, powers := [(14, 1), (51, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (17, 1), (31, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(7, 2), (20, 1), (28, 1), (47, 1), (59, 2), (63, 1)] }, { coefficient := 1, powers := [(7, 2), (20, 1), (34, 1), (37, 1), (59, 2), (63, 1)] }, { coefficient := 1, powers := [(7, 1), (10, 1), (20, 1), (28, 1), (44, 1), (47, 1), (59, 1), (63, 1)] }, { coefficient := 1, powers := [(7, 1), (10, 1), (20, 1), (34, 1), (37, 1), (44, 1), (59, 1), (63, 1)] }, { coefficient := -1, powers := [(7, 1), (14, 1), (20, 1), (28, 1), (47, 1), (51, 1), (59, 1), (63, 1)] }, { coefficient := -1, powers := [(7, 1), (14, 1), (20, 1), (34, 1), (37, 1), (51, 1), (59, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (21, 1), (33, 1), (36, 1), (47, 1), (53, 1)] }, { coefficient := 1, powers := [(10, 1), (28, 1), (33, 1), (36, 1), (47, 1)] }],
  [{ coefficient := -1, powers := [(20, 1), (51, 1), (62, 1)] }, { coefficient := -1, powers := [(20, 1), (56, 1), (62, 1)] }, { coefficient := -1, powers := [(33, 1), (36, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (16, 1), (19, 1), (20, 1), (27, 1), (54, 1), (59, 1), (61, 1)] }, { coefficient := 1, powers := [(7, 1), (16, 1), (20, 1), (28, 1), (40, 1), (59, 1), (61, 1)] }, { coefficient := 1, powers := [(10, 1), (16, 1), (22, 1), (33, 1), (36, 1), (54, 1), (61, 1)] }, { coefficient := 1, powers := [(10, 1), (16, 1), (28, 1), (33, 1), (36, 1), (40, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (16, 1), (26, 1), (33, 1), (36, 1), (47, 1), (53, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (16, 1), (22, 1), (33, 1), (36, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (12, 1), (20, 1), (28, 1), (47, 1), (51, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (12, 1), (20, 1), (34, 1), (37, 1), (51, 1), (59, 1)] }, { coefficient := 1, powers := [(51, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (12, 1), (20, 1), (28, 1), (44, 1), (47, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (12, 1), (20, 1), (34, 1), (37, 1), (44, 1), (59, 1)] }, { coefficient := 1, powers := [(44, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (7, 1), (20, 1), (28, 1), (30, 1), (47, 1), (59, 1)] }, { coefficient := 1, powers := [(4, 1), (7, 1), (20, 1), (30, 1), (34, 1), (37, 1), (59, 1)] }, { coefficient := -1, powers := [(10, 1), (21, 1), (23, 1), (33, 1), (36, 1), (47, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (18, 1), (19, 1), (20, 1), (27, 1), (54, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (18, 1), (20, 1), (28, 1), (40, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (19, 1), (20, 1), (26, 1), (54, 1), (59, 1)] }, { coefficient := 1, powers := [(10, 1), (18, 1), (28, 1), (33, 1), (36, 1), (40, 1)] }],
  [{ coefficient := -1, powers := [(10, 1), (12, 1), (23, 1), (33, 1), (36, 1), (47, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (20, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(10, 1), (31, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (34, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (20, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (19, 1), (20, 1), (27, 1), (54, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (20, 1), (28, 1), (40, 1), (59, 1)] }, { coefficient := 1, powers := [(10, 1), (28, 1), (33, 1), (36, 1), (40, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (19, 1), (20, 1), (54, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (20, 1), (54, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (23, 1), (33, 1), (36, 1), (47, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (33, 1), (36, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (22, 1), (33, 1), (36, 1)] }],
  [{ coefficient := -1, powers := [(10, 1), (16, 1), (22, 1), (33, 1), (36, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (12, 1), (20, 1), (28, 1), (44, 1), (47, 1), (59, 1), (63, 1)] }, { coefficient := -1, powers := [(7, 1), (12, 1), (20, 1), (34, 1), (37, 1), (44, 1), (59, 1), (63, 1)] }, { coefficient := -1, powers := [(7, 1), (16, 1), (20, 1), (28, 1), (47, 1), (52, 1), (59, 1), (63, 1)] }, { coefficient := -1, powers := [(7, 1), (16, 1), (20, 1), (34, 1), (37, 1), (52, 1), (59, 1), (63, 1)] }, { coefficient := 1, powers := [(56, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(10, 1), (33, 1), (36, 1), (47, 1), (49, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (10, 1), (20, 1), (28, 1), (47, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (10, 1), (20, 1), (34, 1), (37, 1), (59, 1)] }, { coefficient := -1, powers := [(7, 1), (14, 1), (20, 1), (28, 1), (47, 1), (59, 1)] }, { coefficient := -1, powers := [(7, 1), (14, 1), (20, 1), (34, 1), (37, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (12, 1), (20, 1), (25, 1), (28, 1), (47, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (12, 1), (20, 1), (25, 1), (34, 1), (37, 1), (59, 1)] }, { coefficient := 1, powers := [(25, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (12, 1), (14, 1), (20, 1), (28, 1), (47, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (12, 1), (14, 1), (20, 1), (34, 1), (37, 1), (59, 1)] }, { coefficient := 1, powers := [(14, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (12, 1), (20, 1), (28, 1), (47, 1), (59, 1)] }, { coefficient := -1, powers := [(7, 1), (12, 1), (20, 1), (34, 1), (37, 1), (59, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(7, 1), (20, 1), (59, 1)] }, { coefficient := -1, powers := [(10, 1), (33, 1), (36, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (16, 1), (19, 1), (20, 1), (27, 1), (42, 1), (54, 1), (59, 1)] }, { coefficient := -1, powers := [(7, 1), (16, 1), (20, 1), (28, 1), (40, 1), (42, 1), (59, 1)] }, { coefficient := -1, powers := [(10, 1), (16, 1), (22, 1), (33, 1), (36, 1), (42, 1), (54, 1)] }, { coefficient := -1, powers := [(10, 1), (16, 1), (26, 1), (33, 1), (36, 1), (47, 1), (49, 1), (53, 1)] }, { coefficient := -1, powers := [(10, 1), (16, 1), (28, 1), (33, 1), (36, 1), (40, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (12, 1), (20, 1), (28, 1), (36, 1), (47, 1), (59, 2)] }, { coefficient := 1, powers := [(7, 1), (12, 1), (20, 1), (28, 1), (39, 1), (44, 1), (47, 1), (55, 1), (59, 1), (63, 1)] }, { coefficient := 1, powers := [(7, 1), (12, 1), (20, 1), (28, 1), (39, 1), (47, 1), (56, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (12, 1), (20, 1), (28, 1), (43, 1), (44, 1), (47, 1), (59, 1), (63, 1)] }, { coefficient := -1, powers := [(7, 1), (12, 1), (20, 1), (28, 1), (44, 1), (47, 1), (51, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (12, 1), (20, 1), (34, 1), (36, 1), (37, 1), (59, 2)] }, { coefficient := 1, powers := [(7, 1), (12, 1), (20, 1), (34, 1), (37, 1), (39, 1), (44, 1), (55, 1), (59, 1), (63, 1)] }, { coefficient := 1, powers := [(7, 1), (12, 1), (20, 1), (34, 1), (37, 1), (39, 1), (56, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (12, 1), (20, 1), (34, 1), (37, 1), (43, 1), (44, 1), (59, 1), (63, 1)] }, { coefficient := -1, powers := [(7, 1), (12, 1), (20, 1), (34, 1), (37, 1), (44, 1), (51, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (16, 1), (20, 1), (28, 1), (39, 1), (47, 1), (52, 1), (55, 1), (59, 1), (63, 1)] }, { coefficient := 1, powers := [(7, 1), (16, 1), (20, 1), (28, 1), (43, 1), (47, 1), (52, 1), (59, 1), (63, 1)] }, { coefficient := 1, powers := [(7, 1), (16, 1), (20, 1), (34, 1), (37, 1), (39, 1), (52, 1), (55, 1), (59, 1), (63, 1)] }, { coefficient := 1, powers := [(7, 1), (16, 1), (20, 1), (34, 1), (37, 1), (43, 1), (52, 1), (59, 1), (63, 1)] }, { coefficient := 1, powers := [(36, 1), (59, 1)] }, { coefficient := -1, powers := [(39, 1), (55, 1), (56, 1), (63, 1)] }, { coefficient := 1, powers := [(39, 1), (56, 1)] }, { coefficient := -1, powers := [(43, 1), (56, 1), (63, 1)] }, { coefficient := -1, powers := [(44, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (19, 1), (20, 1), (45, 1), (54, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (20, 1), (37, 1), (59, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (20, 1), (40, 1), (57, 1), (59, 1)] }, { coefficient := -1, powers := [(10, 1), (23, 1), (33, 1), (36, 1), (47, 1), (52, 1), (53, 1)] }, { coefficient := 1, powers := [(10, 1), (33, 1), (35, 1), (36, 1), (47, 1), (49, 1), (53, 1), (59, 1)] }, { coefficient := 1, powers := [(10, 1), (33, 1), (36, 1), (37, 1), (60, 1)] }, { coefficient := 1, powers := [(10, 1), (33, 1), (36, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(10, 1), (33, 1), (36, 1), (47, 1), (49, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(7, 2), (12, 1), (20, 1), (28, 1), (33, 1), (47, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 2), (12, 1), (20, 1), (33, 1), (34, 1), (37, 1), (59, 1)] }, { coefficient := -1, powers := [(7, 1), (12, 1), (14, 1), (20, 1), (25, 1), (28, 1), (47, 1), (59, 1)] }, { coefficient := -1, powers := [(7, 1), (12, 1), (14, 1), (20, 1), (25, 1), (34, 1), (37, 1), (59, 1)] }, { coefficient := -1, powers := [(7, 1), (17, 1), (18, 1), (19, 1), (20, 1), (27, 1), (54, 1), (59, 1)] }, { coefficient := -1, powers := [(7, 1), (17, 1), (18, 1), (20, 1), (28, 1), (40, 1), (59, 1)] }, { coefficient := -1, powers := [(7, 1), (17, 1), (19, 1), (20, 1), (23, 1), (27, 1), (54, 1), (59, 1)] }, { coefficient := -1, powers := [(7, 1), (17, 1), (20, 1), (23, 1), (28, 1), (40, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (33, 1)] }, { coefficient := 1, powers := [(10, 1), (12, 1), (23, 1), (28, 1), (33, 1), (36, 1), (47, 1)] }, { coefficient := -1, powers := [(10, 1), (17, 1), (18, 1), (28, 1), (33, 1), (36, 1), (40, 1)] }, { coefficient := -1, powers := [(10, 1), (17, 1), (23, 1), (28, 1), (33, 1), (36, 1), (40, 1)] }, { coefficient := -1, powers := [(14, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (25, 1), (59, 1)] }, { coefficient := 1, powers := [(10, 1), (25, 1), (44, 1)] }, { coefficient := 1, powers := [(10, 1), (25, 1), (56, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1), (51, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1), (56, 1)] }, { coefficient := 1, powers := [(14, 1), (25, 1), (44, 1)] }, { coefficient := 1, powers := [(14, 1), (25, 1), (51, 1)] }, { coefficient := 1, powers := [(14, 1), (33, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (7, 1), (12, 1), (20, 1), (28, 1), (30, 1), (44, 1), (47, 1), (59, 1)] }, { coefficient := 1, powers := [(4, 1), (7, 1), (12, 1), (20, 1), (30, 1), (34, 1), (37, 1), (44, 1), (59, 1)] }, { coefficient := 1, powers := [(4, 1), (7, 1), (16, 1), (20, 1), (28, 1), (30, 1), (47, 1), (52, 1), (59, 1)] }, { coefficient := 1, powers := [(4, 1), (7, 1), (16, 1), (20, 1), (30, 1), (34, 1), (37, 1), (52, 1), (59, 1)] }, { coefficient := -1, powers := [(4, 1), (30, 1), (56, 1)] }, { coefficient := -1, powers := [(7, 2), (12, 1), (20, 2), (28, 1), (47, 1), (59, 2)] }, { coefficient := -1, powers := [(7, 2), (12, 1), (20, 2), (34, 1), (37, 1), (59, 2)] }, { coefficient := 1, powers := [(7, 1), (10, 1), (16, 1), (20, 2), (28, 1), (47, 1), (52, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (10, 1), (16, 1), (20, 2), (34, 1), (37, 1), (52, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (12, 1), (14, 1), (20, 2), (28, 1), (47, 1), (51, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (12, 1), (14, 1), (20, 2), (34, 1), (37, 1), (51, 1), (59, 1)] }, { coefficient := -1, powers := [(10, 1), (20, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (5, 1), (20, 1), (31, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (7, 1), (20, 1), (31, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (10, 1), (30, 1), (31, 1), (36, 1)] }, { coefficient := 1, powers := [(5, 1), (10, 1), (31, 1), (33, 1), (36, 1)] }, { coefficient := 1, powers := [(7, 1), (12, 1), (20, 1), (22, 1), (59, 1)] }, { coefficient := 1, powers := [(10, 1), (16, 1), (22, 1), (33, 1), (36, 1), (49, 1)] }]
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
    ¬ ∀ index : Fin 54,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component39.SelectedLeafB4_1_6.selectedHasNoCommonZero

end Krenn.Component39.SelectedLeafB4_1_6
