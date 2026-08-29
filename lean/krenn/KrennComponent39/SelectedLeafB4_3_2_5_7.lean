import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component39.SelectedLeafB4_3_2_5_7

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "6383d6e9f4820e0920fbafa5fc74725a0d79020281fe280afe3a95e3ce647450"
def certificateSHA256 : String := "e9cd2450ce425786c3260807005a64bc0bf642987a98dca5243ecafff3094704"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 40 → Fin 676 := ![
  11,
  19,
  21,
  23,
  26,
  171,
  175,
  176,
  180,
  187,
  193,
  197,
  268,
  302,
  304,
  305,
  316,
  360,
  363,
  372,
  473,
  542,
  563,
  602,
  603,
  615,
  659,
  660,
  661,
  662,
  663,
  665,
  666,
  669,
  670,
  671,
  672,
  673,
  674,
  675
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 40 → SparsePoly (Fin 70) := ![
  [{ coefficient := 1, powers := [(8, 1), (30, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (20, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (20, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (26, 1)] }, { coefficient := 1, powers := [(14, 1), (21, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (28, 1)] }, { coefficient := 1, powers := [(14, 1), (21, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (23, 1)] }, { coefficient := 1, powers := [(16, 1), (18, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (18, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (53, 1)] }, { coefficient := 1, powers := [(28, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(30, 1), (37, 1)] }, { coefficient := 1, powers := [(33, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (19, 1), (52, 1)] }, { coefficient := 1, powers := [(14, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (49, 1)] }, { coefficient := 1, powers := [(18, 1), (49, 1)] }, { coefficient := 1, powers := [(23, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (44, 1)] }, { coefficient := 1, powers := [(4, 1), (33, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (51, 1)] }, { coefficient := 1, powers := [(7, 1), (30, 1)] }, { coefficient := 1, powers := [(10, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (45, 1)] }, { coefficient := 1, powers := [(17, 1), (39, 1)] }, { coefficient := 1, powers := [(17, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (30, 1), (57, 1)] }, { coefficient := 1, powers := [(8, 1), (30, 1), (47, 1)] }, { coefficient := 1, powers := [(17, 1), (30, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (33, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (40, 1)] }, { coefficient := 1, powers := [(12, 1), (33, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (20, 1), (60, 1)] }, { coefficient := 1, powers := [(12, 1), (20, 1), (57, 1)] }, { coefficient := 1, powers := [(17, 1), (20, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (36, 1), (58, 1)] }, { coefficient := 1, powers := [(1, 1), (43, 1), (50, 1)] }, { coefficient := 1, powers := [(4, 1), (25, 1), (58, 1)] }, { coefficient := 1, powers := [(7, 1), (20, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (20, 1), (59, 1)] }, { coefficient := 1, powers := [(8, 1), (30, 1), (44, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (39, 1)] }, { coefficient := 1, powers := [(16, 1), (20, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (25, 1), (45, 1)] }, { coefficient := 1, powers := [(17, 1), (20, 1), (51, 1)] }, { coefficient := 1, powers := [(17, 1), (25, 1), (39, 1)] }, { coefficient := 1, powers := [(17, 1), (30, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (59, 1)] }, { coefficient := 1, powers := [(10, 1), (44, 1)] }, { coefficient := 1, powers := [(10, 1), (56, 1)] }, { coefficient := 1, powers := [(14, 1), (39, 1)] }, { coefficient := 1, powers := [(14, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (51, 1)] }, { coefficient := 1, powers := [(20, 1), (56, 1)] }, { coefficient := 1, powers := [(25, 1), (39, 1)] }, { coefficient := 1, powers := [(25, 1), (44, 1)] }, { coefficient := 1, powers := [(30, 1), (36, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (37, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (46, 1), (53, 1)] }, { coefficient := 1, powers := [(5, 1), (28, 1), (59, 1)] }, { coefficient := 1, powers := [(8, 1), (22, 1), (59, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1), (53, 1)] }, { coefficient := 1, powers := [(16, 1), (28, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (36, 1), (59, 1)] }, { coefficient := 1, powers := [(1, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(1, 1), (44, 1), (51, 1)] }, { coefficient := 1, powers := [(4, 1), (25, 1), (59, 1)] }, { coefficient := 1, powers := [(4, 1), (30, 1), (56, 1)] }, { coefficient := 1, powers := [(4, 1), (33, 1), (51, 1)] }, { coefficient := 1, powers := [(7, 1), (20, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (30, 1), (44, 1)] }, { coefficient := 1, powers := [(7, 1), (33, 1), (39, 1)] }, { coefficient := 1, powers := [(10, 1), (20, 1), (56, 1)] }, { coefficient := 1, powers := [(10, 1), (25, 1), (44, 1)] }, { coefficient := 1, powers := [(10, 1), (33, 1), (36, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1), (51, 1)] }, { coefficient := 1, powers := [(14, 1), (25, 1), (39, 1)] }, { coefficient := 1, powers := [(14, 1), (30, 1), (36, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (37, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (47, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (28, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (22, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1), (47, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (40, 1)] }, { coefficient := 1, powers := [(12, 1), (22, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1), (28, 1), (47, 1)] }, { coefficient := 1, powers := [(12, 1), (34, 1), (37, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (54, 1)] }, { coefficient := 1, powers := [(17, 1), (28, 1), (40, 1)] }, { coefficient := 1, powers := [(17, 1), (31, 1), (37, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (61, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1)] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(39, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(40, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(57, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (65, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(25, 1)] }],
  [{ coefficient := 1, powers := [(28, 1), (66, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(58, 1), (67, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(59, 1), (68, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(60, 1), (69, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 40 → SparsePoly (Fin 70) := ![
  [{ coefficient := -1, powers := [(10, 1), (31, 1), (36, 1), (44, 1), (47, 1), (62, 1)] }, { coefficient := 1, powers := [(10, 1), (31, 1), (36, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (16, 1), (19, 1), (20, 1), (22, 1), (33, 1), (36, 1), (45, 1), (54, 1), (63, 1)] }, { coefficient := 1, powers := [(10, 1), (16, 1), (19, 1), (20, 1), (28, 1), (33, 1), (36, 1), (40, 1), (45, 1), (63, 1)] }, { coefficient := 1, powers := [(10, 1), (17, 1), (19, 1), (20, 1), (22, 1), (33, 1), (36, 1), (51, 1), (54, 1), (63, 1)] }, { coefficient := 1, powers := [(10, 1), (17, 1), (19, 1), (20, 1), (28, 1), (33, 1), (36, 1), (40, 1), (51, 1), (63, 1)] }, { coefficient := 2, powers := [(19, 1), (20, 1), (51, 1), (63, 1)] }, { coefficient := 1, powers := [(19, 1), (20, 1), (56, 1), (63, 1)] }, { coefficient := 1, powers := [(19, 1), (33, 1), (36, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(10, 1), (31, 1), (36, 1), (47, 1), (53, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (10, 1), (22, 1), (33, 1), (36, 1), (54, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (10, 1), (28, 1), (33, 1), (36, 1), (40, 1), (59, 1)] }, { coefficient := -1, powers := [(10, 1), (14, 1), (22, 1), (33, 1), (36, 1), (51, 1), (54, 1)] }, { coefficient := -1, powers := [(10, 1), (14, 1), (28, 1), (33, 1), (36, 1), (40, 1), (51, 1)] }, { coefficient := 1, powers := [(10, 1), (31, 1), (36, 1), (47, 1), (54, 1), (59, 1), (62, 1), (69, 1)] }],
  [{ coefficient := -1, powers := [(10, 1), (26, 1), (44, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(10, 1), (16, 1), (22, 1), (33, 2), (36, 1), (45, 1), (54, 1), (69, 1)] }, { coefficient := -1, powers := [(10, 1), (16, 1), (28, 1), (33, 2), (36, 1), (40, 1), (45, 1), (69, 1)] }, { coefficient := 1, powers := [(10, 1), (17, 1), (22, 1), (30, 1), (33, 1), (36, 1), (54, 1), (56, 1), (69, 1)] }, { coefficient := -1, powers := [(10, 1), (17, 1), (22, 1), (33, 2), (36, 1), (51, 1), (54, 1), (69, 1)] }, { coefficient := 1, powers := [(10, 1), (17, 1), (28, 1), (30, 1), (33, 1), (36, 1), (40, 1), (56, 1), (69, 1)] }, { coefficient := -1, powers := [(10, 1), (17, 1), (28, 1), (33, 2), (36, 1), (40, 1), (51, 1), (69, 1)] }, { coefficient := -1, powers := [(20, 1), (59, 1), (69, 1)] }, { coefficient := 1, powers := [(30, 1), (56, 1), (69, 1)] }, { coefficient := 1, powers := [(33, 1), (39, 1), (69, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (44, 1), (53, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(20, 1), (44, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (28, 1), (33, 1), (36, 1), (47, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(10, 1), (28, 1), (33, 1), (36, 1), (47, 1), (49, 1), (61, 1)] }, { coefficient := -1, powers := [(10, 1), (28, 1), (33, 1), (36, 1), (47, 1), (49, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(10, 1), (16, 1), (33, 1), (36, 1), (60, 1), (68, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (17, 1), (31, 1), (36, 1)] }],
  [{ coefficient := -1, powers := [(10, 1), (16, 1), (20, 1), (22, 1), (33, 1), (36, 1), (45, 1), (54, 1), (63, 1)] }, { coefficient := -1, powers := [(10, 1), (16, 1), (20, 1), (28, 1), (33, 1), (36, 1), (40, 1), (45, 1), (63, 1)] }, { coefficient := -1, powers := [(10, 1), (17, 1), (20, 1), (22, 1), (33, 1), (36, 1), (51, 1), (54, 1), (63, 1)] }, { coefficient := -1, powers := [(10, 1), (17, 1), (20, 1), (28, 1), (33, 1), (36, 1), (40, 1), (51, 1), (63, 1)] }, { coefficient := -2, powers := [(20, 1), (51, 1), (63, 1)] }, { coefficient := -1, powers := [(20, 1), (56, 1), (63, 1)] }, { coefficient := -1, powers := [(33, 1), (36, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (16, 1), (28, 1), (33, 1), (36, 1), (47, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (16, 1), (22, 1), (33, 1), (36, 1), (45, 1), (54, 1)] }, { coefficient := 1, powers := [(10, 1), (16, 1), (28, 1), (33, 1), (36, 1), (40, 1), (45, 1)] }, { coefficient := 2, powers := [(10, 1), (17, 1), (22, 1), (33, 1), (36, 1), (51, 1), (54, 1)] }, { coefficient := 2, powers := [(10, 1), (17, 1), (28, 1), (33, 1), (36, 1), (40, 1), (51, 1)] }, { coefficient := -1, powers := [(39, 1)] }, { coefficient := 1, powers := [(51, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (17, 1), (22, 1), (33, 1), (36, 1), (44, 1), (54, 1)] }, { coefficient := -1, powers := [(10, 1), (17, 1), (22, 1), (33, 1), (36, 1), (54, 1), (56, 1)] }, { coefficient := 1, powers := [(10, 1), (17, 1), (28, 1), (33, 1), (36, 1), (40, 1), (44, 1)] }, { coefficient := -1, powers := [(10, 1), (17, 1), (28, 1), (33, 1), (36, 1), (40, 1), (56, 1)] }, { coefficient := 1, powers := [(44, 1)] }, { coefficient := -1, powers := [(56, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (10, 1), (22, 1), (33, 2), (36, 1), (54, 1)] }, { coefficient := 1, powers := [(7, 1), (10, 1), (28, 1), (33, 2), (36, 1), (40, 1)] }],
  [{ coefficient := -1, powers := [(10, 1), (31, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (34, 1), (36, 1)] }],
  [{ coefficient := -1, powers := [(10, 1), (31, 1), (36, 1), (47, 1), (59, 1), (62, 1), (69, 1)] }],
  [{ coefficient := 1, powers := [(59, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (31, 1), (36, 1), (47, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(10, 2), (22, 1), (33, 1), (36, 1), (54, 1)] }, { coefficient := -1, powers := [(10, 2), (28, 1), (33, 1), (36, 1), (40, 1)] }, { coefficient := 1, powers := [(10, 1), (14, 1), (22, 1), (33, 1), (36, 1), (54, 1)] }, { coefficient := 1, powers := [(10, 1), (14, 1), (28, 1), (33, 1), (36, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(20, 1)] }],
  [{ coefficient := 1, powers := [(10, 2), (17, 1), (22, 1), (33, 1), (36, 1), (54, 1)] }, { coefficient := 1, powers := [(10, 2), (17, 1), (28, 1), (33, 1), (36, 1), (40, 1)] }, { coefficient := 1, powers := [(14, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (33, 1), (36, 1), (60, 1), (68, 1)] }],
  [{ coefficient := -1, powers := [(10, 1), (17, 1), (22, 1), (33, 1), (36, 1), (54, 1)] }, { coefficient := -1, powers := [(10, 1), (17, 1), (28, 1), (33, 1), (36, 1), (40, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(10, 1), (33, 1), (36, 1)] }],
  [{ coefficient := -1, powers := [(10, 1), (16, 1), (28, 1), (33, 1), (36, 1), (47, 1), (49, 1)] }],
  [{ coefficient := -1, powers := [(10, 1), (16, 1), (22, 1), (33, 1), (36, 1), (44, 1), (45, 1), (54, 1)] }, { coefficient := -1, powers := [(10, 1), (16, 1), (28, 1), (33, 1), (36, 1), (40, 1), (44, 1), (45, 1)] }, { coefficient := 1, powers := [(10, 1), (17, 1), (22, 1), (33, 1), (36, 2), (54, 1), (59, 1)] }, { coefficient := 1, powers := [(10, 1), (17, 1), (22, 1), (33, 1), (36, 1), (39, 1), (54, 1), (56, 1)] }, { coefficient := -2, powers := [(10, 1), (17, 1), (22, 1), (33, 1), (36, 1), (44, 1), (51, 1), (54, 1)] }, { coefficient := 1, powers := [(10, 1), (17, 1), (22, 1), (33, 1), (36, 1), (51, 1), (54, 1), (56, 1)] }, { coefficient := 1, powers := [(10, 1), (17, 1), (28, 1), (33, 1), (36, 2), (40, 1), (59, 1)] }, { coefficient := 1, powers := [(10, 1), (17, 1), (28, 1), (33, 1), (36, 1), (39, 1), (40, 1), (56, 1)] }, { coefficient := -2, powers := [(10, 1), (17, 1), (28, 1), (33, 1), (36, 1), (40, 1), (44, 1), (51, 1)] }, { coefficient := 1, powers := [(10, 1), (17, 1), (28, 1), (33, 1), (36, 1), (40, 1), (51, 1), (56, 1)] }, { coefficient := -1, powers := [(36, 1), (58, 1), (59, 1), (67, 1)] }, { coefficient := 1, powers := [(36, 1), (59, 1)] }, { coefficient := 1, powers := [(39, 1), (44, 1)] }, { coefficient := 1, powers := [(39, 1), (56, 1)] }, { coefficient := -1, powers := [(43, 1), (50, 1), (59, 1), (67, 1)] }, { coefficient := -1, powers := [(44, 1), (51, 1)] }, { coefficient := 1, powers := [(51, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [(10, 1), (33, 1), (36, 1), (37, 1), (59, 1), (60, 1), (68, 1)] }, { coefficient := 1, powers := [(10, 1), (33, 1), (36, 1), (37, 1), (60, 1)] }, { coefficient := 1, powers := [(10, 1), (33, 1), (36, 1), (40, 1), (57, 1)] }, { coefficient := -1, powers := [(10, 1), (33, 1), (36, 1), (46, 1), (53, 1), (60, 1), (68, 1)] }, { coefficient := 1, powers := [(10, 1), (33, 1), (36, 1), (47, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (10, 1), (31, 1), (33, 1), (36, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (14, 1), (16, 1), (20, 1), (22, 1), (33, 1), (36, 1), (45, 1), (54, 1)] }, { coefficient := 1, powers := [(10, 1), (14, 1), (16, 1), (20, 1), (28, 1), (33, 1), (36, 1), (40, 1), (45, 1)] }, { coefficient := 1, powers := [(10, 1), (14, 1), (17, 1), (20, 1), (22, 1), (33, 1), (36, 1), (51, 1), (54, 1)] }, { coefficient := 1, powers := [(10, 1), (14, 1), (17, 1), (20, 1), (28, 1), (33, 1), (36, 1), (40, 1), (51, 1)] }, { coefficient := 2, powers := [(14, 1), (20, 1), (51, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1), (56, 1)] }, { coefficient := 1, powers := [(14, 1), (33, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (10, 1), (30, 1), (31, 1), (36, 1)] }, { coefficient := 1, powers := [(5, 1), (10, 1), (31, 1), (33, 1), (36, 1)] }, { coefficient := 1, powers := [(10, 1), (12, 1), (20, 1), (31, 1), (36, 1), (47, 1), (59, 1), (62, 1), (69, 1)] }, { coefficient := 1, powers := [(10, 1), (12, 1), (22, 1), (33, 1), (36, 1)] }],
  [{ coefficient := -1, powers := [(10, 1), (12, 1), (28, 1), (33, 1), (36, 1), (47, 1)] }, { coefficient := 1, powers := [(10, 1), (16, 1), (28, 1), (33, 1), (36, 1), (47, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (10, 1), (17, 1), (22, 1), (33, 1), (36, 1), (54, 1), (59, 1)] }, { coefficient := 1, powers := [(4, 1), (10, 1), (17, 1), (28, 1), (33, 1), (36, 1), (40, 1), (59, 1)] }, { coefficient := -1, powers := [(4, 1), (58, 1), (59, 1), (67, 1)] }, { coefficient := 1, powers := [(4, 1), (59, 1)] }, { coefficient := 1, powers := [(10, 2), (16, 1), (22, 1), (33, 1), (36, 1), (45, 1), (54, 1)] }, { coefficient := 1, powers := [(10, 2), (16, 1), (28, 1), (33, 1), (36, 1), (40, 1), (45, 1)] }, { coefficient := -1, powers := [(10, 2), (17, 1), (22, 1), (33, 1), (36, 1), (44, 1), (54, 1)] }, { coefficient := 1, powers := [(10, 2), (17, 1), (22, 1), (33, 1), (36, 1), (54, 1), (56, 1)] }, { coefficient := -1, powers := [(10, 2), (17, 1), (28, 1), (33, 1), (36, 1), (40, 1), (44, 1)] }, { coefficient := 1, powers := [(10, 2), (17, 1), (28, 1), (33, 1), (36, 1), (40, 1), (56, 1)] }, { coefficient := -1, powers := [(10, 1), (14, 1), (16, 1), (22, 1), (33, 1), (36, 1), (45, 1), (54, 1)] }, { coefficient := -1, powers := [(10, 1), (14, 1), (16, 1), (28, 1), (33, 1), (36, 1), (40, 1), (45, 1)] }, { coefficient := 1, powers := [(10, 1), (56, 1)] }, { coefficient := -1, powers := [(14, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (20, 1), (44, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (20, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (10, 1), (28, 1), (33, 1), (36, 1), (60, 1)] }, { coefficient := -1, powers := [(8, 1), (10, 1), (22, 1), (33, 1), (36, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (10, 1), (16, 1), (22, 1), (33, 2), (36, 1), (45, 1), (54, 1)] }, { coefficient := 1, powers := [(4, 1), (10, 1), (16, 1), (28, 1), (33, 2), (36, 1), (40, 1), (45, 1)] }, { coefficient := -1, powers := [(4, 1), (10, 1), (17, 1), (22, 1), (30, 1), (33, 1), (36, 1), (54, 1), (56, 1)] }, { coefficient := 1, powers := [(4, 1), (10, 1), (17, 1), (22, 1), (33, 2), (36, 1), (51, 1), (54, 1)] }, { coefficient := -1, powers := [(4, 1), (10, 1), (17, 1), (28, 1), (30, 1), (33, 1), (36, 1), (40, 1), (56, 1)] }, { coefficient := 1, powers := [(4, 1), (10, 1), (17, 1), (28, 1), (33, 2), (36, 1), (40, 1), (51, 1)] }, { coefficient := 1, powers := [(4, 1), (20, 1), (59, 1)] }, { coefficient := -1, powers := [(4, 1), (30, 1), (56, 1)] }, { coefficient := -1, powers := [(4, 1), (33, 1), (39, 1)] }, { coefficient := 1, powers := [(7, 1), (10, 1), (16, 1), (22, 1), (33, 2), (36, 1), (45, 1), (54, 1)] }, { coefficient := 1, powers := [(7, 1), (10, 1), (16, 1), (28, 1), (33, 2), (36, 1), (40, 1), (45, 1)] }, { coefficient := -1, powers := [(7, 1), (10, 1), (17, 1), (22, 1), (30, 1), (33, 1), (36, 1), (54, 1), (56, 1)] }, { coefficient := 1, powers := [(7, 1), (10, 1), (17, 1), (22, 1), (33, 2), (36, 1), (51, 1), (54, 1)] }, { coefficient := -1, powers := [(7, 1), (10, 1), (17, 1), (28, 1), (30, 1), (33, 1), (36, 1), (40, 1), (56, 1)] }, { coefficient := 1, powers := [(7, 1), (10, 1), (17, 1), (28, 1), (33, 2), (36, 1), (40, 1), (51, 1)] }, { coefficient := 1, powers := [(7, 1), (20, 1), (59, 1)] }, { coefficient := -1, powers := [(7, 1), (30, 1), (56, 1)] }, { coefficient := -1, powers := [(7, 1), (33, 1), (39, 1)] }, { coefficient := 1, powers := [(8, 1), (10, 1), (20, 1), (31, 1), (36, 1), (47, 1), (59, 1), (62, 1)] }]
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
    ¬ ∀ index : Fin 40,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component39.SelectedLeafB4_3_2_5_7.selectedHasNoCommonZero

end Krenn.Component39.SelectedLeafB4_3_2_5_7
