import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component39.SelectedLeafB5_2_5_4

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "3dfc688d4403401339fcac873963c0ff48d21ecf0d71660f13085dcebd2b9a82"
def certificateSHA256 : String := "38cb5f9e376f8c8054a274e2220f074afa6da9e0c5ba3e6c1c338a010dfceedc"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 47 → Fin 673 := ![
  14,
  26,
  62,
  187,
  188,
  191,
  193,
  232,
  280,
  300,
  302,
  304,
  305,
  316,
  318,
  371,
  394,
  396,
  412,
  413,
  425,
  426,
  433,
  439,
  440,
  451,
  472,
  482,
  508,
  511,
  562,
  566,
  570,
  581,
  602,
  603,
  625,
  659,
  660,
  662,
  663,
  666,
  668,
  669,
  670,
  671,
  672
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 47 → SparsePoly (Fin 67) := ![
  [{ coefficient := 1, powers := [(10, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (30, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (18, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (42, 1)] }, { coefficient := 1, powers := [(17, 1), (18, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (54, 1)] }, { coefficient := 1, powers := [(28, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (53, 1)] }, { coefficient := 1, powers := [(28, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (24, 1), (45, 1)] }, { coefficient := 1, powers := [(10, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (42, 1), (53, 1)] }, { coefficient := 1, powers := [(20, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1)] }, { coefficient := 1, powers := [(18, 1), (42, 1)] }, { coefficient := 1, powers := [(23, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (49, 1)] }, { coefficient := 1, powers := [(18, 1), (49, 1)] }, { coefficient := 1, powers := [(23, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (44, 1)] }, { coefficient := 1, powers := [(4, 1), (33, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (51, 1)] }, { coefficient := 1, powers := [(7, 1), (30, 1)] }, { coefficient := 1, powers := [(10, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (45, 1)] }, { coefficient := 1, powers := [(17, 1), (39, 1)] }, { coefficient := 1, powers := [(17, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (53, 1)] }, { coefficient := 1, powers := [(28, 1), (39, 1)] }, { coefficient := 1, powers := [(28, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (18, 1), (59, 1)] }, { coefficient := 1, powers := [(16, 1), (18, 1), (53, 1)] }, { coefficient := 1, powers := [(16, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (18, 1), (57, 1)] }, { coefficient := 1, powers := [(16, 1), (24, 1), (42, 1)] }, { coefficient := 1, powers := [(17, 1), (18, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (23, 1), (39, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1), (44, 1)] }, { coefficient := 1, powers := [(16, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (52, 1)] }, { coefficient := 1, powers := [(18, 1), (49, 1), (56, 1)] }, { coefficient := 1, powers := [(18, 1), (52, 1)] }, { coefficient := 1, powers := [(49, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (53, 1)] }, { coefficient := 1, powers := [(3, 1), (24, 1), (59, 1)] }, { coefficient := 1, powers := [(18, 1), (53, 1)] }, { coefficient := 1, powers := [(24, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1)] }, { coefficient := 1, powers := [(12, 1), (28, 1)] }, { coefficient := 1, powers := [(16, 1), (21, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (33, 1)] }, { coefficient := 1, powers := [(6, 1), (30, 1)] }, { coefficient := 1, powers := [(30, 1), (35, 1)] }, { coefficient := 1, powers := [(33, 1), (35, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (59, 1)] }, { coefficient := 1, powers := [(16, 1), (24, 1), (39, 1)] }, { coefficient := 1, powers := [(16, 1), (24, 1), (44, 1)] }, { coefficient := 1, powers := [(16, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (39, 1)] }, { coefficient := 1, powers := [(16, 1), (44, 1)] }, { coefficient := 1, powers := [(16, 1), (51, 1)] }, { coefficient := 1, powers := [(16, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (54, 1)] }, { coefficient := 1, powers := [(28, 1), (40, 1)] }, { coefficient := 1, powers := [(28, 1), (46, 1), (49, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1), (52, 1)] }, { coefficient := 1, powers := [(3, 1), (60, 1)] }, { coefficient := 1, powers := [(18, 1), (42, 1), (52, 1)] }, { coefficient := 1, powers := [(42, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (35, 1), (59, 1)] }, { coefficient := 1, powers := [(1, 1)] }, { coefficient := 1, powers := [(10, 1), (33, 1), (35, 1)] }, { coefficient := 1, powers := [(14, 1), (30, 1), (35, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (35, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1)] }, { coefficient := 1, powers := [(16, 1), (21, 1)] }, { coefficient := 1, powers := [(16, 1), (26, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (31, 1), (56, 1)] }, { coefficient := 1, powers := [(21, 1), (49, 1), (56, 1)] }, { coefficient := 1, powers := [(21, 1), (52, 1)] }, { coefficient := 1, powers := [(27, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (23, 1), (59, 1)] }, { coefficient := 1, powers := [(10, 1), (23, 1), (44, 1)] }, { coefficient := 1, powers := [(14, 1), (23, 1), (39, 1)] }, { coefficient := 1, powers := [(14, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (24, 1), (45, 1)] }, { coefficient := 1, powers := [(16, 1), (57, 1)] }, { coefficient := 1, powers := [(17, 1), (24, 1), (39, 1)] }, { coefficient := 1, powers := [(17, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (42, 1), (53, 1)] }, { coefficient := 1, powers := [(22, 1), (57, 1)] }, { coefficient := 1, powers := [(28, 1), (47, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (42, 1), (53, 1)] }, { coefficient := 1, powers := [(27, 1), (57, 1)] }, { coefficient := 1, powers := [(28, 1), (39, 1), (42, 1)] }, { coefficient := 1, powers := [(28, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (51, 1)] }, { coefficient := 1, powers := [(3, 1), (59, 1)] }, { coefficient := 1, powers := [(18, 1), (51, 1)] }, { coefficient := 1, powers := [(18, 1), (56, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(4, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (59, 1)] }, { coefficient := 1, powers := [(10, 1), (44, 1)] }, { coefficient := 1, powers := [(10, 1), (56, 1)] }, { coefficient := 1, powers := [(14, 1), (39, 1)] }, { coefficient := 1, powers := [(14, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (51, 1)] }, { coefficient := 1, powers := [(20, 1), (56, 1)] }, { coefficient := 1, powers := [(25, 1), (39, 1)] }, { coefficient := 1, powers := [(25, 1), (44, 1)] }, { coefficient := 1, powers := [(30, 1), (36, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (28, 1), (60, 1)] }, { coefficient := 1, powers := [(3, 1), (31, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (34, 1), (54, 1)] }, { coefficient := 1, powers := [(21, 1), (42, 1), (54, 1)] }, { coefficient := 1, powers := [(21, 1), (49, 1), (57, 1)] }, { coefficient := 1, powers := [(28, 1), (42, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (36, 1), (59, 1)] }, { coefficient := 1, powers := [(1, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(1, 1), (44, 1), (51, 1)] }, { coefficient := 1, powers := [(4, 1), (25, 1), (59, 1)] }, { coefficient := 1, powers := [(4, 1), (30, 1), (56, 1)] }, { coefficient := 1, powers := [(4, 1), (33, 1), (51, 1)] }, { coefficient := 1, powers := [(7, 1), (20, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (30, 1), (44, 1)] }, { coefficient := 1, powers := [(7, 1), (33, 1), (39, 1)] }, { coefficient := 1, powers := [(10, 1), (20, 1), (56, 1)] }, { coefficient := 1, powers := [(10, 1), (25, 1), (44, 1)] }, { coefficient := 1, powers := [(10, 1), (33, 1), (36, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1), (51, 1)] }, { coefficient := 1, powers := [(14, 1), (25, 1), (39, 1)] }, { coefficient := 1, powers := [(14, 1), (30, 1), (36, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (37, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (47, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (28, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (22, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1), (47, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (40, 1)] }, { coefficient := 1, powers := [(12, 1), (22, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1), (28, 1), (47, 1)] }, { coefficient := 1, powers := [(12, 1), (34, 1), (37, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (54, 1)] }, { coefficient := 1, powers := [(17, 1), (28, 1), (40, 1)] }, { coefficient := 1, powers := [(17, 1), (31, 1), (37, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(40, 1)] }],
  [{ coefficient := 1, powers := [(56, 1)] }],
  [{ coefficient := 1, powers := [(57, 1), (65, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(23, 1), (66, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(25, 1)] }],
  [{ coefficient := 1, powers := [(28, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 47 → SparsePoly (Fin 67) := ![
  [{ coefficient := 1, powers := [(6, 1), (24, 1), (33, 1), (36, 1), (59, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (7, 1), (42, 1), (51, 1), (59, 1), (65, 1)] }, { coefficient := 1, powers := [(6, 1), (10, 1), (42, 1), (51, 1), (59, 1), (65, 1)] }, { coefficient := -1, powers := [(7, 1), (18, 1), (42, 1), (51, 1), (59, 1), (65, 1)] }, { coefficient := -1, powers := [(7, 1), (42, 1), (59, 1), (65, 1)] }, { coefficient := 1, powers := [(10, 1), (35, 1), (42, 1), (51, 1), (59, 1), (65, 1)] }, { coefficient := -1, powers := [(14, 1), (35, 1), (42, 1), (51, 1), (59, 1), (65, 1)] }, { coefficient := 1, powers := [(14, 1), (35, 1), (42, 1), (59, 1), (65, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(14, 1), (36, 1), (59, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (21, 1), (51, 1), (57, 1), (62, 1), (65, 1), (66, 1)] }, { coefficient := -1, powers := [(0, 1), (26, 1), (51, 1), (57, 1), (62, 1), (65, 1), (66, 1)] }, { coefficient := -1, powers := [(21, 1), (42, 1), (53, 1), (62, 1), (65, 1), (66, 1)] }, { coefficient := -1, powers := [(21, 1), (57, 1), (62, 1), (65, 1), (66, 1)] }, { coefficient := -1, powers := [(26, 1), (42, 1), (53, 1), (62, 1), (65, 1), (66, 1)] }, { coefficient := -1, powers := [(26, 1), (57, 1), (62, 1), (65, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (21, 1), (53, 1), (62, 1), (65, 1), (66, 1)] }, { coefficient := -1, powers := [(0, 1), (26, 1), (53, 1), (62, 1), (65, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (16, 1), (47, 1), (59, 1)] }, { coefficient := -1, powers := [(5, 1), (42, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (12, 1), (42, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (33, 1), (36, 1), (59, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (7, 1), (51, 1), (59, 1), (65, 1)] }, { coefficient := -1, powers := [(6, 1), (10, 1), (51, 1), (59, 1), (65, 1)] }, { coefficient := 1, powers := [(7, 1), (18, 1), (51, 1), (59, 1), (65, 1)] }, { coefficient := 1, powers := [(7, 1), (59, 1), (65, 1)] }, { coefficient := -1, powers := [(10, 1), (35, 1), (51, 1), (59, 1), (65, 1)] }, { coefficient := 1, powers := [(14, 1), (35, 1), (51, 1), (59, 1), (65, 1)] }, { coefficient := -1, powers := [(14, 1), (35, 1), (59, 1), (65, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (21, 1), (59, 1), (62, 1), (65, 1), (66, 1)] }, { coefficient := -1, powers := [(8, 1), (26, 1), (59, 1), (62, 1), (65, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (27, 1), (57, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (51, 1), (59, 1)] }, { coefficient := -1, powers := [(35, 1), (51, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (44, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (39, 1), (59, 1)] }, { coefficient := 1, powers := [(35, 1), (39, 1), (59, 1)] }, { coefficient := -1, powers := [(35, 1), (44, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (21, 1), (24, 1), (62, 1), (65, 1), (66, 1)] }, { coefficient := -1, powers := [(0, 1), (24, 1), (26, 1), (62, 1), (65, 1), (66, 1)] }, { coefficient := -1, powers := [(18, 1), (21, 1), (24, 1), (62, 1), (65, 1), (66, 1)] }, { coefficient := -1, powers := [(18, 1), (24, 1), (26, 1), (62, 1), (65, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (23, 1), (42, 1), (49, 1), (57, 1), (59, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (42, 1), (62, 1), (65, 1), (66, 1)] }, { coefficient := 1, powers := [(26, 1), (42, 1), (62, 1), (65, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (21, 1), (51, 1), (62, 1), (65, 1), (66, 1)] }, { coefficient := 1, powers := [(0, 1), (26, 1), (51, 1), (62, 1), (65, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (21, 1), (57, 1), (62, 1), (65, 1), (66, 1)] }, { coefficient := -1, powers := [(0, 1), (26, 1), (57, 1), (62, 1), (65, 1), (66, 1)] }, { coefficient := -1, powers := [(21, 1), (24, 1), (42, 1), (62, 1), (65, 1), (66, 1)] }, { coefficient := -1, powers := [(24, 1), (26, 1), (42, 1), (62, 1), (65, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (37, 1), (42, 1), (59, 1)] }, { coefficient := -1, powers := [(5, 1), (21, 1), (57, 1), (59, 1)] }, { coefficient := -1, powers := [(8, 1), (22, 1), (42, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(17, 1), (21, 1), (62, 1), (65, 1), (66, 1)] }, { coefficient := -1, powers := [(17, 1), (26, 1), (62, 1), (65, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (47, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (39, 1), (59, 1)] }, { coefficient := -1, powers := [(10, 1), (36, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (21, 1), (42, 1), (62, 1), (65, 1), (66, 1)] }, { coefficient := 1, powers := [(0, 1), (26, 1), (42, 1), (62, 1), (65, 1), (66, 1)] }, { coefficient := 1, powers := [(21, 1), (23, 1), (42, 1), (62, 1), (65, 1), (66, 1)] }, { coefficient := 1, powers := [(23, 1), (26, 1), (42, 1), (62, 1), (65, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (21, 1), (23, 1), (57, 1), (62, 1), (65, 1), (66, 1)] }, { coefficient := -1, powers := [(0, 1), (21, 1), (24, 1), (42, 1), (62, 1), (65, 1), (66, 1)] }, { coefficient := 1, powers := [(0, 1), (23, 1), (26, 1), (57, 1), (62, 1), (65, 1), (66, 1)] }, { coefficient := -1, powers := [(0, 1), (24, 1), (26, 1), (42, 1), (62, 1), (65, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (17, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (37, 1), (59, 1)] }, { coefficient := 1, powers := [(8, 1), (22, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(36, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(62, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (5, 1), (57, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (18, 1), (57, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (35, 1), (59, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (21, 1), (62, 1), (65, 1), (66, 1)] }, { coefficient := 1, powers := [(0, 1), (26, 1), (62, 1), (65, 1), (66, 1)] }, { coefficient := 1, powers := [(18, 1), (21, 1), (62, 1), (65, 1), (66, 1)] }, { coefficient := 1, powers := [(18, 1), (26, 1), (62, 1), (65, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (12, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (23, 1), (49, 1), (57, 1), (59, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (20, 1), (59, 1)] }, { coefficient := 1, powers := [(17, 1), (21, 1), (24, 1), (62, 1), (65, 1), (66, 1)] }, { coefficient := 1, powers := [(17, 1), (24, 1), (26, 1), (62, 1), (65, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(20, 1), (23, 1), (35, 1), (59, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (10, 1), (59, 1)] }, { coefficient := 1, powers := [(10, 1), (35, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (59, 1)] }, { coefficient := 1, powers := [(35, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (36, 1), (59, 2)] }, { coefficient := -1, powers := [(3, 1), (39, 1), (56, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (44, 1), (51, 1), (59, 1)] }, { coefficient := -1, powers := [(6, 1), (39, 1), (51, 1), (59, 1)] }, { coefficient := -1, powers := [(35, 1), (39, 1), (51, 1), (59, 1)] }, { coefficient := -1, powers := [(35, 1), (39, 1), (56, 1), (59, 1)] }, { coefficient := 1, powers := [(35, 1), (44, 1), (51, 1), (59, 1)] }, { coefficient := 1, powers := [(36, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(35, 1), (59, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (3, 1), (57, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (8, 1), (34, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (3, 1), (5, 1), (31, 1), (57, 1), (59, 1)] }, { coefficient := -1, powers := [(0, 1), (5, 1), (21, 1), (49, 1), (57, 1), (59, 1)] }, { coefficient := -1, powers := [(0, 1), (16, 1), (21, 1), (23, 1), (57, 1), (62, 1), (65, 1), (66, 1)] }, { coefficient := 1, powers := [(0, 1), (16, 1), (21, 1), (24, 1), (42, 1), (62, 1), (65, 1), (66, 1)] }, { coefficient := -1, powers := [(0, 1), (16, 1), (23, 1), (26, 1), (57, 1), (62, 1), (65, 1), (66, 1)] }, { coefficient := 1, powers := [(0, 1), (16, 1), (24, 1), (26, 1), (42, 1), (62, 1), (65, 1), (66, 1)] }, { coefficient := 1, powers := [(2, 1), (18, 1), (37, 1), (42, 1), (49, 1), (59, 1)] }, { coefficient := -1, powers := [(3, 1), (4, 1), (30, 1), (59, 1)] }, { coefficient := -1, powers := [(3, 1), (5, 1), (18, 1), (31, 1), (57, 1), (59, 1)] }, { coefficient := -1, powers := [(3, 1), (10, 1), (20, 1), (59, 1)] }, { coefficient := -1, powers := [(4, 1), (30, 1), (35, 1), (59, 1)] }, { coefficient := -1, powers := [(6, 1), (10, 1), (20, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (18, 1), (20, 1), (59, 1)] }, { coefficient := 1, powers := [(8, 1), (18, 1), (22, 1), (42, 1), (49, 1), (59, 1)] }, { coefficient := 1, powers := [(10, 1), (20, 1), (23, 1), (35, 1), (59, 1), (66, 1)] }, { coefficient := -2, powers := [(10, 1), (20, 1), (35, 1), (59, 1)] }, { coefficient := -1, powers := [(17, 1), (18, 1), (21, 1), (24, 1), (62, 1), (65, 1), (66, 1)] }, { coefficient := -1, powers := [(17, 1), (18, 1), (24, 1), (26, 1), (62, 1), (65, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (7, 1), (20, 1), (51, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (14, 1), (30, 1), (36, 1), (59, 1)] }, { coefficient := -1, powers := [(5, 1), (23, 1), (27, 1), (49, 1), (57, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (10, 1), (20, 1), (51, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (10, 1), (33, 1), (36, 1), (59, 1)] }, { coefficient := -1, powers := [(7, 1), (18, 1), (20, 1), (51, 1), (59, 1)] }, { coefficient := -1, powers := [(7, 1), (20, 1), (59, 1)] }, { coefficient := 1, powers := [(10, 1), (20, 1), (35, 1), (51, 1), (59, 1)] }, { coefficient := -1, powers := [(14, 1), (20, 1), (35, 1), (51, 1), (59, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1), (35, 1), (59, 1), (66, 1)] }, { coefficient := 1, powers := [(16, 1), (21, 1), (23, 1), (62, 1), (66, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1), (26, 1), (62, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (20, 1), (35, 1), (59, 2)] }, { coefficient := 1, powers := [(14, 1), (20, 1), (35, 1), (51, 1), (59, 1)] }, { coefficient := 1, powers := [(16, 1), (21, 1), (62, 1)] }, { coefficient := 1, powers := [(16, 1), (26, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (4, 1), (59, 2)] }, { coefficient := -1, powers := [(3, 1), (14, 1), (39, 1), (59, 1)] }, { coefficient := -1, powers := [(4, 1), (35, 1), (59, 2)] }, { coefficient := -2, powers := [(6, 1), (10, 1), (39, 1), (59, 1)] }, { coefficient := -1, powers := [(6, 1), (10, 1), (44, 1), (59, 1)] }, { coefficient := -2, powers := [(10, 1), (35, 1), (39, 1), (59, 1)] }, { coefficient := -1, powers := [(10, 1), (35, 1), (44, 1), (59, 1)] }, { coefficient := -1, powers := [(14, 1), (35, 1), (39, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (12, 1), (42, 1), (46, 1), (59, 1)] }, { coefficient := -1, powers := [(3, 1), (12, 1), (47, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (16, 1), (47, 1), (49, 1), (59, 1)] }, { coefficient := -1, powers := [(3, 1), (17, 1), (46, 1), (49, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (23, 1), (42, 1), (44, 1), (49, 1), (57, 1), (59, 1), (65, 1)] }, { coefficient := -1, powers := [(5, 1), (23, 1), (45, 1), (49, 1), (57, 1), (59, 1), (65, 1)] }]
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
    (values : Fin 67 → R) :
    ¬ ∀ index : Fin 47,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component39.SelectedLeafB5_2_5_4.selectedHasNoCommonZero

end Krenn.Component39.SelectedLeafB5_2_5_4
