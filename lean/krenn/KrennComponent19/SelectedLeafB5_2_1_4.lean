import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component19.SelectedLeafB5_2_1_4

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "44f7a28bb0a304c698f2192c5ec7b069d3f8e3686216c4ff7e37eb48b7191523"
def certificateSHA256 : String := "c8b69c5596f2c70eafe4ade2da74794cd4e86c9462b579e8b8ff8e4967d85823"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 48 → Fin 675 := ![
  0,
  4,
  7,
  9,
  10,
  18,
  20,
  22,
  31,
  122,
  171,
  177,
  179,
  191,
  196,
  316,
  318,
  339,
  403,
  420,
  422,
  424,
  429,
  440,
  442,
  463,
  464,
  466,
  474,
  495,
  565,
  567,
  583,
  606,
  607,
  646,
  654,
  661,
  662,
  663,
  664,
  665,
  668,
  670,
  671,
  672,
  673,
  674
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 48 → SparsePoly (Fin 67) := ![
  [{ coefficient := 1, powers := [(3, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (35, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (26, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(35, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (35, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (55, 1)] }, { coefficient := 1, powers := [(21, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (26, 1)] }, { coefficient := 1, powers := [(16, 1), (21, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (30, 1)] }, { coefficient := 1, powers := [(16, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (21, 1)] }, { coefficient := 1, powers := [(19, 1), (26, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (53, 1)] }, { coefficient := 1, powers := [(25, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (49, 1)] }, { coefficient := 1, powers := [(20, 1), (43, 1)] }, { coefficient := 1, powers := [(20, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (55, 1)] }, { coefficient := 1, powers := [(32, 1), (44, 1)] }, { coefficient := 1, powers := [(35, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (46, 1), (53, 1)] }, { coefficient := 1, powers := [(19, 1), (31, 1), (46, 1)] }, { coefficient := 1, powers := [(20, 1), (24, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (26, 1), (49, 1)] }, { coefficient := 1, powers := [(20, 1), (26, 1), (43, 1)] }, { coefficient := 1, powers := [(20, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (50, 1)] }, { coefficient := 1, powers := [(5, 1), (38, 1)] }, { coefficient := 1, powers := [(19, 1), (30, 1), (50, 1)] }, { coefficient := 1, powers := [(20, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (53, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (53, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (57, 1)] }, { coefficient := 1, powers := [(19, 1), (31, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1)] }, { coefficient := 1, powers := [(13, 1), (32, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (61, 1)] }, { coefficient := 1, powers := [(13, 1), (27, 1), (49, 1)] }, { coefficient := 1, powers := [(13, 1), (58, 1)] }, { coefficient := 1, powers := [(20, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(31, 1), (43, 1)] }, { coefficient := 1, powers := [(31, 1), (48, 1)] }, { coefficient := 1, powers := [(31, 1), (53, 1)] }, { coefficient := 1, powers := [(31, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (41, 1), (61, 1)] }, { coefficient := 1, powers := [(0, 1), (44, 1), (58, 1)] }, { coefficient := 1, powers := [(0, 1), (50, 1), (55, 1)] }, { coefficient := 1, powers := [(27, 1), (44, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (39, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1)] }, { coefficient := 1, powers := [(19, 1), (30, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (39, 1), (61, 1)] }, { coefficient := 1, powers := [(13, 1), (30, 1), (46, 1)] }, { coefficient := 1, powers := [(13, 1), (38, 1), (39, 1)] }, { coefficient := 1, powers := [(20, 1), (35, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (40, 1), (61, 1)] }, { coefficient := 1, powers := [(13, 1), (31, 1), (49, 1)] }, { coefficient := 1, powers := [(13, 1), (38, 1), (40, 1)] }, { coefficient := 1, powers := [(20, 1), (35, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (46, 1), (54, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (58, 1)] }, { coefficient := 1, powers := [(19, 1), (32, 1), (46, 1)] }, { coefficient := 1, powers := [(20, 1), (24, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (26, 1), (60, 1)] }, { coefficient := 1, powers := [(11, 1), (26, 1), (48, 1)] }, { coefficient := 1, powers := [(16, 1), (26, 1), (43, 1)] }, { coefficient := 1, powers := [(16, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (46, 1), (54, 1)] }, { coefficient := 1, powers := [(25, 1), (58, 1)] }, { coefficient := 1, powers := [(32, 1), (50, 1)] }, { coefficient := 1, powers := [(38, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(31, 1), (46, 1), (54, 1)] }, { coefficient := 1, powers := [(31, 1), (58, 1)] }, { coefficient := 1, powers := [(32, 1), (43, 1), (46, 1)] }, { coefficient := 1, powers := [(32, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (53, 1)] }, { coefficient := 1, powers := [(3, 1), (60, 1)] }, { coefficient := 1, powers := [(21, 1), (53, 1)] }, { coefficient := 1, powers := [(21, 1), (57, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(4, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (60, 1)] }, { coefficient := 1, powers := [(11, 1), (48, 1)] }, { coefficient := 1, powers := [(11, 1), (57, 1)] }, { coefficient := 1, powers := [(16, 1), (43, 1)] }, { coefficient := 1, powers := [(16, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (53, 1)] }, { coefficient := 1, powers := [(23, 1), (57, 1)] }, { coefficient := 1, powers := [(29, 1), (43, 1)] }, { coefficient := 1, powers := [(29, 1), (48, 1)] }, { coefficient := 1, powers := [(34, 1), (40, 1)] }, { coefficient := 1, powers := [(37, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (40, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (43, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (48, 1), (53, 1)] }, { coefficient := 1, powers := [(43, 1)] }, { coefficient := 1, powers := [(48, 1)] }, { coefficient := 1, powers := [(53, 1)] }, { coefficient := 1, powers := [(57, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (40, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (43, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (48, 1), (53, 1)] }, { coefficient := 1, powers := [(19, 1), (31, 1), (43, 1)] }, { coefficient := 1, powers := [(19, 1), (31, 1), (48, 1)] }, { coefficient := 1, powers := [(19, 1), (31, 1), (53, 1)] }, { coefficient := 1, powers := [(19, 1), (31, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (40, 1), (60, 1)] }, { coefficient := 1, powers := [(1, 1), (43, 1), (57, 1)] }, { coefficient := 1, powers := [(1, 1), (48, 1), (53, 1)] }, { coefficient := 1, powers := [(4, 1), (29, 1), (60, 1)] }, { coefficient := 1, powers := [(4, 1), (34, 1), (57, 1)] }, { coefficient := 1, powers := [(4, 1), (37, 1), (53, 1)] }, { coefficient := 1, powers := [(7, 1), (23, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (34, 1), (48, 1)] }, { coefficient := 1, powers := [(7, 1), (37, 1), (43, 1)] }, { coefficient := 1, powers := [(11, 1), (23, 1), (57, 1)] }, { coefficient := 1, powers := [(11, 1), (29, 1), (48, 1)] }, { coefficient := 1, powers := [(11, 1), (37, 1), (40, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1), (53, 1)] }, { coefficient := 1, powers := [(16, 1), (29, 1), (43, 1)] }, { coefficient := 1, powers := [(16, 1), (34, 1), (40, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (41, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (44, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (50, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (38, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (25, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (50, 1)] }, { coefficient := 1, powers := [(8, 1), (38, 1), (44, 1)] }, { coefficient := 1, powers := [(13, 1), (25, 1), (58, 1)] }, { coefficient := 1, powers := [(13, 1), (32, 1), (50, 1)] }, { coefficient := 1, powers := [(13, 1), (38, 1), (41, 1)] }, { coefficient := 1, powers := [(20, 1), (25, 1), (55, 1)] }, { coefficient := 1, powers := [(20, 1), (32, 1), (44, 1)] }, { coefficient := 1, powers := [(20, 1), (35, 1), (41, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(44, 1)] }],
  [{ coefficient := 1, powers := [(57, 1)] }],
  [{ coefficient := 1, powers := [(58, 1), (65, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(26, 1), (66, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(29, 1)] }],
  [{ coefficient := 1, powers := [(32, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 48 → SparsePoly (Fin 67) := ![
  [{ coefficient := 2, powers := [(2, 1), (7, 1), (34, 1), (41, 1), (43, 1), (60, 1)] }, { coefficient := -2, powers := [(2, 1), (7, 1), (37, 1), (41, 1), (43, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (16, 1), (23, 1), (39, 1), (41, 1), (60, 2), (66, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (5, 1), (34, 1), (43, 1), (58, 1), (63, 1)] }, { coefficient := 1, powers := [(2, 1), (5, 1), (37, 1), (43, 1), (58, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (7, 1), (25, 1), (34, 1), (43, 1), (58, 1), (63, 1), (66, 1)] }, { coefficient := -1, powers := [(2, 1), (7, 1), (25, 1), (37, 1), (43, 1), (58, 1), (63, 1), (66, 1)] }, { coefficient := 1, powers := [(11, 1), (25, 1), (34, 1), (40, 1), (58, 1), (66, 1)] }, { coefficient := 1, powers := [(11, 1), (34, 1), (38, 1), (40, 1), (41, 1), (66, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1), (25, 1), (39, 1), (58, 1), (60, 1), (66, 2)] }, { coefficient := 1, powers := [(16, 1), (23, 1), (38, 1), (39, 1), (41, 1), (60, 1), (66, 2)] }, { coefficient := -1, powers := [(16, 1), (25, 1), (34, 1), (40, 1), (58, 1), (66, 1)] }, { coefficient := -1, powers := [(16, 1), (34, 1), (38, 1), (40, 1), (41, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (23, 1), (30, 1), (41, 1), (60, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (7, 1), (25, 1), (27, 1), (34, 1), (43, 1), (63, 1)] }, { coefficient := -1, powers := [(2, 1), (7, 1), (25, 1), (27, 1), (37, 1), (43, 1), (63, 1)] }, { coefficient := 1, powers := [(11, 1), (25, 1), (27, 1), (34, 1), (40, 1)] }, { coefficient := 1, powers := [(11, 1), (31, 1), (34, 1), (41, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1), (25, 1), (27, 1), (39, 1), (60, 1), (66, 1)] }, { coefficient := -1, powers := [(16, 1), (25, 1), (27, 1), (34, 1), (40, 1)] }, { coefficient := -1, powers := [(16, 1), (31, 1), (34, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (7, 1), (30, 1), (34, 1), (43, 1), (55, 1), (63, 1)] }, { coefficient := -1, powers := [(2, 1), (7, 1), (30, 1), (37, 1), (43, 1), (55, 1), (63, 1)] }, { coefficient := 1, powers := [(11, 1), (30, 1), (34, 1), (40, 1), (55, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1), (30, 1), (39, 1), (55, 1), (60, 1), (66, 1)] }, { coefficient := -1, powers := [(16, 1), (30, 1), (34, 1), (40, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (7, 1), (19, 1), (34, 1), (43, 1), (50, 1), (63, 1)] }, { coefficient := -1, powers := [(2, 1), (7, 1), (19, 1), (37, 1), (43, 1), (50, 1), (63, 1)] }, { coefficient := 1, powers := [(16, 1), (19, 1), (23, 1), (39, 1), (50, 1), (60, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (7, 1), (13, 1), (34, 1), (43, 1), (46, 1), (63, 1)] }, { coefficient := -1, powers := [(2, 1), (7, 1), (13, 1), (37, 1), (43, 1), (46, 1), (63, 1)] }, { coefficient := 1, powers := [(11, 1), (13, 1), (34, 1), (40, 1), (46, 1)] }, { coefficient := 1, powers := [(13, 1), (16, 1), (23, 1), (39, 1), (46, 1), (60, 1), (66, 1)] }, { coefficient := -1, powers := [(13, 1), (16, 1), (34, 1), (40, 1), (46, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (11, 1), (34, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (16, 1), (34, 1), (58, 1)] }, { coefficient := -1, powers := [(8, 1), (11, 1), (34, 1), (50, 1)] }, { coefficient := 1, powers := [(8, 1), (16, 1), (34, 1), (50, 1)] }, { coefficient := -1, powers := [(11, 1), (20, 1), (34, 1), (41, 1)] }, { coefficient := 1, powers := [(16, 1), (20, 1), (34, 1), (41, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (23, 1), (58, 1), (60, 1), (66, 1)] }],
  [{ coefficient := -2, powers := [(2, 1), (7, 1), (34, 1), (43, 1), (50, 1), (53, 1)] }, { coefficient := 2, powers := [(2, 1), (7, 1), (37, 1), (43, 1), (50, 1), (53, 1)] }, { coefficient := -1, powers := [(2, 1), (16, 1), (23, 1), (39, 1), (50, 1), (53, 1), (60, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (23, 1), (30, 1), (63, 1), (66, 2)] }],
  [{ coefficient := -1, powers := [(19, 1), (23, 1), (63, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(16, 1), (23, 1), (30, 1), (63, 1), (66, 2)] }],
  [{ coefficient := 2, powers := [(2, 1), (7, 1), (20, 1), (26, 1), (34, 1), (43, 1), (55, 1), (63, 1)] }, { coefficient := -2, powers := [(2, 1), (7, 1), (20, 1), (26, 1), (37, 1), (43, 1), (55, 1), (63, 1)] }, { coefficient := 1, powers := [(16, 1), (20, 1), (23, 1), (26, 1), (39, 1), (55, 1), (60, 1), (66, 1)] }],
  [{ coefficient := -2, powers := [(2, 1), (7, 1), (25, 1), (26, 1), (34, 1), (43, 1), (55, 1), (63, 1)] }, { coefficient := 2, powers := [(2, 1), (7, 1), (25, 1), (26, 1), (37, 1), (43, 1), (55, 1), (63, 1)] }, { coefficient := -1, powers := [(16, 1), (23, 1), (25, 1), (26, 1), (39, 1), (55, 1), (60, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (7, 1), (20, 1), (34, 1), (43, 1), (63, 1)] }, { coefficient := 1, powers := [(2, 1), (7, 1), (20, 1), (37, 1), (43, 1), (63, 1)] }, { coefficient := 1, powers := [(11, 1), (20, 1), (34, 1), (40, 1)] }, { coefficient := -1, powers := [(16, 1), (20, 1), (34, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (37, 1), (54, 1), (63, 1), (65, 1)] }, { coefficient := -1, powers := [(7, 1), (34, 1), (54, 1), (63, 1), (65, 1)] }, { coefficient := -1, powers := [(11, 1), (23, 1), (54, 1), (63, 1), (65, 1)] }],
  [{ coefficient := 2, powers := [(2, 1), (7, 1), (25, 1), (34, 1), (43, 1), (55, 1), (63, 1)] }, { coefficient := -2, powers := [(2, 1), (7, 1), (25, 1), (37, 1), (43, 1), (55, 1), (63, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1), (25, 1), (39, 1), (55, 1), (60, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (7, 1), (34, 1), (43, 1), (55, 1), (63, 1)] }, { coefficient := 1, powers := [(2, 1), (7, 1), (37, 1), (43, 1), (55, 1), (63, 1)] }, { coefficient := -1, powers := [(11, 1), (34, 1), (40, 1), (55, 1)] }, { coefficient := -1, powers := [(16, 1), (23, 1), (39, 1), (55, 1), (60, 1), (66, 1)] }, { coefficient := 1, powers := [(16, 1), (34, 1), (40, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (37, 1), (58, 1), (63, 1), (65, 1)] }, { coefficient := -1, powers := [(7, 1), (34, 1), (58, 1), (63, 1), (65, 1)] }, { coefficient := -1, powers := [(11, 1), (23, 1), (58, 1), (63, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (7, 1), (34, 1), (43, 1), (50, 1), (63, 1)] }, { coefficient := 1, powers := [(2, 1), (7, 1), (37, 1), (43, 1), (50, 1), (63, 1)] }, { coefficient := -1, powers := [(16, 1), (23, 1), (39, 1), (50, 1), (60, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (7, 1), (25, 1), (34, 1), (43, 1), (63, 1)] }, { coefficient := 1, powers := [(2, 1), (7, 1), (25, 1), (37, 1), (43, 1), (63, 1)] }, { coefficient := -1, powers := [(11, 1), (25, 1), (34, 1), (40, 1)] }, { coefficient := -1, powers := [(16, 1), (23, 1), (25, 1), (39, 1), (60, 1), (66, 1)] }, { coefficient := 1, powers := [(16, 1), (25, 1), (34, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (7, 1), (19, 1), (34, 1), (63, 1)] }],
  [{ coefficient := 2, powers := [(2, 1), (7, 1), (21, 1), (34, 1), (43, 1), (53, 1), (62, 1)] }, { coefficient := -2, powers := [(2, 1), (7, 1), (21, 1), (37, 1), (43, 1), (53, 1), (62, 1)] }, { coefficient := 2, powers := [(2, 1), (7, 1), (34, 1), (43, 1), (53, 1)] }, { coefficient := 1, powers := [(2, 1), (7, 1), (34, 1), (43, 1), (62, 1)] }, { coefficient := -2, powers := [(2, 1), (7, 1), (37, 1), (43, 1), (53, 1)] }, { coefficient := -1, powers := [(2, 1), (7, 1), (37, 1), (43, 1), (62, 1)] }, { coefficient := 1, powers := [(2, 1), (16, 1), (21, 1), (23, 1), (39, 1), (53, 1), (60, 1), (62, 1), (66, 1)] }, { coefficient := 1, powers := [(2, 1), (16, 1), (23, 1), (39, 1), (53, 1), (60, 1), (66, 1)] }, { coefficient := 1, powers := [(2, 1), (16, 1), (23, 1), (39, 1), (60, 1), (62, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (23, 1), (63, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(16, 1), (23, 1), (41, 1), (60, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(11, 1), (34, 1), (41, 1)] }, { coefficient := 1, powers := [(16, 1), (34, 1), (41, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (37, 1), (53, 1), (63, 1), (65, 1)] }, { coefficient := 1, powers := [(7, 1), (34, 1), (53, 1), (63, 1), (65, 1)] }, { coefficient := 1, powers := [(11, 1), (23, 1), (53, 1), (63, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(23, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (7, 1), (13, 1), (34, 1), (43, 1), (63, 1)] }, { coefficient := 1, powers := [(2, 1), (7, 1), (13, 1), (37, 1), (43, 1), (63, 1)] }, { coefficient := -1, powers := [(11, 1), (13, 1), (34, 1), (40, 1)] }, { coefficient := -1, powers := [(13, 1), (16, 1), (23, 1), (39, 1), (60, 1), (66, 1)] }, { coefficient := 1, powers := [(13, 1), (16, 1), (34, 1), (40, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (19, 1), (37, 1), (63, 1), (65, 1)] }, { coefficient := 1, powers := [(7, 1), (19, 1), (34, 1), (63, 1), (65, 1)] }, { coefficient := 1, powers := [(11, 1), (19, 1), (23, 1), (63, 1), (65, 1)] }],
  [{ coefficient := -2, powers := [(2, 1), (7, 1), (34, 1), (41, 1), (43, 1), (61, 1)] }, { coefficient := 2, powers := [(2, 1), (7, 1), (37, 1), (41, 1), (43, 1), (61, 1)] }, { coefficient := -1, powers := [(2, 1), (16, 1), (23, 1), (39, 1), (41, 1), (60, 1), (61, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(23, 1)] }],
  [{ coefficient := 1, powers := [(11, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (34, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (7, 1), (34, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (7, 1), (34, 1), (43, 1), (63, 1)] }, { coefficient := -1, powers := [(2, 1), (7, 1), (37, 1), (43, 1), (63, 1)] }, { coefficient := 1, powers := [(11, 1), (34, 1), (40, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1), (39, 1), (60, 1), (66, 1)] }, { coefficient := -1, powers := [(16, 1), (34, 1), (40, 1)] }],
  [{ coefficient := -2, powers := [(2, 1), (7, 1), (21, 1), (34, 1), (41, 1), (43, 1), (53, 1), (61, 1)] }, { coefficient := -2, powers := [(2, 1), (7, 1), (21, 1), (34, 1), (43, 1), (50, 1), (53, 1), (55, 1)] }, { coefficient := 2, powers := [(2, 1), (7, 1), (21, 1), (37, 1), (41, 1), (43, 1), (53, 1), (61, 1)] }, { coefficient := 2, powers := [(2, 1), (7, 1), (21, 1), (37, 1), (43, 1), (50, 1), (53, 1), (55, 1)] }, { coefficient := -1, powers := [(2, 1), (7, 1), (34, 1), (41, 1), (43, 1), (61, 1)] }, { coefficient := -1, powers := [(2, 1), (7, 1), (34, 1), (43, 1), (50, 1), (55, 1)] }, { coefficient := 1, powers := [(2, 1), (7, 1), (37, 1), (41, 1), (43, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (7, 1), (37, 1), (43, 1), (50, 1), (55, 1)] }, { coefficient := -1, powers := [(2, 1), (16, 1), (21, 1), (23, 1), (39, 1), (41, 1), (53, 1), (60, 1), (61, 1), (66, 1)] }, { coefficient := -1, powers := [(2, 1), (16, 1), (21, 1), (23, 1), (39, 1), (50, 1), (53, 1), (55, 1), (60, 1), (66, 1)] }, { coefficient := -1, powers := [(2, 1), (16, 1), (23, 1), (39, 1), (41, 1), (60, 1), (61, 1), (66, 1)] }, { coefficient := -1, powers := [(2, 1), (16, 1), (23, 1), (39, 1), (50, 1), (55, 1), (60, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(40, 1), (60, 1)] }, { coefficient := 1, powers := [(48, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (7, 1), (34, 1), (40, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (7, 1), (34, 1), (48, 1), (53, 1)] }, { coefficient := -1, powers := [(2, 1), (7, 1), (34, 1), (41, 1), (43, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (7, 1), (34, 1), (43, 1), (50, 1), (55, 1)] }, { coefficient := 1, powers := [(2, 1), (7, 1), (37, 1), (41, 1), (43, 1), (61, 1)] }, { coefficient := -1, powers := [(2, 1), (7, 1), (37, 1), (43, 1), (50, 1), (55, 1)] }, { coefficient := -1, powers := [(4, 1), (37, 1), (53, 1), (58, 1), (65, 1)] }, { coefficient := 1, powers := [(7, 1), (34, 1), (43, 1)] }, { coefficient := 1, powers := [(7, 1), (34, 1), (53, 1), (58, 1), (65, 1)] }, { coefficient := -1, powers := [(7, 1), (37, 1), (43, 1)] }, { coefficient := 1, powers := [(11, 1), (23, 1), (53, 1), (58, 1), (65, 1)] }, { coefficient := -1, powers := [(16, 1), (23, 1), (39, 1), (60, 1), (66, 1)] }, { coefficient := -1, powers := [(16, 1), (23, 1), (66, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (2, 1), (7, 1), (21, 1), (34, 1), (43, 1), (53, 1), (58, 1), (62, 1)] }, { coefficient := 2, powers := [(0, 1), (2, 1), (7, 1), (21, 1), (37, 1), (43, 1), (53, 1), (58, 1), (62, 1)] }, { coefficient := -2, powers := [(0, 1), (2, 1), (7, 1), (34, 1), (43, 1), (53, 1), (58, 1)] }, { coefficient := -1, powers := [(0, 1), (2, 1), (7, 1), (34, 1), (43, 1), (58, 1), (62, 1)] }, { coefficient := 2, powers := [(0, 1), (2, 1), (7, 1), (37, 1), (43, 1), (53, 1), (58, 1)] }, { coefficient := 1, powers := [(0, 1), (2, 1), (7, 1), (37, 1), (43, 1), (58, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 1), (2, 1), (16, 1), (21, 1), (23, 1), (39, 1), (53, 1), (58, 1), (60, 1), (62, 1), (66, 1)] }, { coefficient := -1, powers := [(0, 1), (2, 1), (16, 1), (23, 1), (39, 1), (53, 1), (58, 1), (60, 1), (66, 1)] }, { coefficient := -1, powers := [(0, 1), (2, 1), (16, 1), (23, 1), (39, 1), (58, 1), (60, 1), (62, 1), (66, 1)] }, { coefficient := -1, powers := [(2, 2), (7, 1), (34, 1), (43, 1), (58, 1), (63, 1)] }, { coefficient := 1, powers := [(2, 2), (7, 1), (37, 1), (43, 1), (58, 1), (63, 1)] }, { coefficient := -1, powers := [(2, 1), (7, 1), (8, 1), (34, 1), (38, 1), (43, 1), (63, 1)] }, { coefficient := 1, powers := [(2, 1), (7, 1), (8, 1), (37, 1), (38, 1), (43, 1), (63, 1)] }, { coefficient := -2, powers := [(2, 1), (7, 1), (21, 1), (27, 1), (34, 1), (43, 1), (46, 1), (53, 1), (62, 1)] }, { coefficient := 2, powers := [(2, 1), (7, 1), (21, 1), (27, 1), (37, 1), (43, 1), (46, 1), (53, 1), (62, 1)] }, { coefficient := -2, powers := [(2, 1), (7, 1), (27, 1), (34, 1), (43, 1), (46, 1), (53, 1)] }, { coefficient := -1, powers := [(2, 1), (7, 1), (27, 1), (34, 1), (43, 1), (46, 1), (62, 1)] }, { coefficient := 2, powers := [(2, 1), (7, 1), (27, 1), (37, 1), (43, 1), (46, 1), (53, 1)] }, { coefficient := 1, powers := [(2, 1), (7, 1), (27, 1), (37, 1), (43, 1), (46, 1), (62, 1)] }, { coefficient := -1, powers := [(2, 1), (11, 1), (34, 1), (40, 1), (58, 1)] }, { coefficient := -1, powers := [(2, 1), (16, 1), (21, 1), (23, 1), (27, 1), (39, 1), (46, 1), (53, 1), (60, 1), (62, 1), (66, 1)] }, { coefficient := -1, powers := [(2, 1), (16, 1), (23, 1), (27, 1), (39, 1), (46, 1), (53, 1), (60, 1), (66, 1)] }, { coefficient := -1, powers := [(2, 1), (16, 1), (23, 1), (27, 1), (39, 1), (46, 1), (60, 1), (62, 1), (66, 1)] }, { coefficient := -1, powers := [(2, 1), (16, 1), (23, 1), (39, 1), (58, 1), (60, 1), (66, 1)] }, { coefficient := 1, powers := [(2, 1), (16, 1), (34, 1), (40, 1), (58, 1)] }, { coefficient := -1, powers := [(8, 1), (11, 1), (34, 1), (38, 1), (40, 1)] }, { coefficient := -1, powers := [(8, 1), (16, 1), (23, 1), (38, 1), (39, 1), (60, 1), (66, 1)] }, { coefficient := 1, powers := [(8, 1), (16, 1), (34, 1), (38, 1), (40, 1)] }, { coefficient := -2, powers := [(11, 1), (20, 1), (32, 1), (34, 1), (40, 1)] }, { coefficient := -1, powers := [(16, 1), (20, 1), (23, 1), (32, 1), (39, 1), (60, 1), (66, 1)] }, { coefficient := 2, powers := [(16, 1), (20, 1), (32, 1), (34, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (2, 1), (7, 1), (34, 1), (43, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (7, 1), (34, 1), (43, 1)] }, { coefficient := 1, powers := [(1, 1), (43, 1)] }, { coefficient := -2, powers := [(2, 1), (7, 1), (20, 1), (25, 1), (26, 1), (34, 1), (43, 1), (55, 1), (63, 1)] }, { coefficient := 2, powers := [(2, 1), (7, 1), (20, 1), (25, 1), (26, 1), (37, 1), (43, 1), (55, 1), (63, 1)] }, { coefficient := 2, powers := [(2, 1), (7, 1), (21, 1), (34, 1), (41, 1), (43, 1), (61, 1)] }, { coefficient := -2, powers := [(2, 1), (7, 1), (21, 1), (37, 1), (41, 1), (43, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (16, 1), (21, 1), (23, 1), (39, 1), (41, 1), (60, 1), (61, 1), (66, 1)] }, { coefficient := -1, powers := [(4, 1), (19, 1), (24, 1), (37, 1), (58, 1), (63, 1), (65, 1)] }, { coefficient := 1, powers := [(4, 1), (34, 1)] }, { coefficient := 1, powers := [(7, 1), (19, 1), (24, 1), (34, 1), (58, 1), (63, 1), (65, 1)] }, { coefficient := -1, powers := [(7, 1), (34, 1)] }, { coefficient := 1, powers := [(11, 1), (19, 1), (23, 1), (24, 1), (58, 1), (63, 1), (65, 1)] }, { coefficient := -1, powers := [(11, 1), (23, 1)] }, { coefficient := -1, powers := [(16, 1), (20, 1), (23, 1), (25, 1), (26, 1), (39, 1), (55, 1), (60, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (37, 1), (53, 1)] }, { coefficient := 1, powers := [(7, 1), (34, 1), (53, 1)] }, { coefficient := 1, powers := [(11, 1), (23, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (7, 1), (13, 1), (25, 1), (34, 1), (43, 1), (58, 1), (63, 1)] }, { coefficient := 1, powers := [(2, 1), (7, 1), (13, 1), (25, 1), (37, 1), (43, 1), (58, 1), (63, 1)] }, { coefficient := 1, powers := [(4, 1), (23, 1), (60, 1)] }, { coefficient := -1, powers := [(11, 1), (13, 1), (25, 1), (34, 1), (40, 1), (58, 1)] }, { coefficient := -1, powers := [(11, 1), (13, 1), (34, 1), (38, 1), (40, 1), (41, 1)] }, { coefficient := -1, powers := [(11, 1), (19, 1), (23, 1), (30, 1), (63, 1), (66, 1)] }, { coefficient := 1, powers := [(11, 1), (23, 1), (48, 1)] }, { coefficient := -1, powers := [(13, 1), (16, 1), (23, 1), (25, 1), (39, 1), (58, 1), (60, 1), (66, 1)] }, { coefficient := -1, powers := [(13, 1), (16, 1), (23, 1), (38, 1), (39, 1), (41, 1), (60, 1), (66, 1)] }, { coefficient := 1, powers := [(13, 1), (16, 1), (25, 1), (34, 1), (40, 1), (58, 1)] }, { coefficient := 1, powers := [(13, 1), (16, 1), (34, 1), (38, 1), (40, 1), (41, 1)] }, { coefficient := 1, powers := [(16, 1), (19, 1), (23, 1), (30, 1), (63, 1), (66, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (60, 1)] }, { coefficient := -1, powers := [(11, 1), (43, 1)] }, { coefficient := 1, powers := [(16, 1), (43, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (5, 1), (7, 1), (34, 1), (43, 1), (61, 1), (63, 1)] }, { coefficient := 1, powers := [(2, 1), (5, 1), (7, 1), (37, 1), (43, 1), (61, 1), (63, 1)] }, { coefficient := 1, powers := [(2, 1), (7, 1), (13, 1), (34, 1), (43, 1), (50, 1), (63, 1)] }, { coefficient := -1, powers := [(2, 1), (7, 1), (13, 1), (37, 1), (43, 1), (50, 1), (63, 1)] }, { coefficient := 1, powers := [(4, 1), (19, 1), (37, 1), (43, 1), (46, 1), (63, 1), (65, 1)] }, { coefficient := 1, powers := [(4, 1), (19, 1), (37, 1), (46, 1), (53, 1), (63, 1), (65, 1)] }, { coefficient := 1, powers := [(4, 1), (19, 1), (37, 1), (49, 1), (63, 1), (65, 1)] }, { coefficient := -1, powers := [(5, 1), (11, 1), (34, 1), (40, 1), (61, 1)] }, { coefficient := -1, powers := [(5, 1), (16, 1), (23, 1), (39, 1), (60, 1), (61, 1), (66, 1)] }, { coefficient := 1, powers := [(5, 1), (16, 1), (34, 1), (40, 1), (61, 1)] }, { coefficient := -1, powers := [(7, 1), (19, 1), (34, 1), (43, 1), (46, 1), (63, 1), (65, 1)] }, { coefficient := -1, powers := [(7, 1), (19, 1), (34, 1), (46, 1), (53, 1), (63, 1), (65, 1)] }, { coefficient := -1, powers := [(7, 1), (19, 1), (34, 1), (49, 1), (63, 1), (65, 1)] }, { coefficient := -1, powers := [(11, 1), (19, 1), (23, 1), (43, 1), (46, 1), (63, 1), (65, 1)] }, { coefficient := -1, powers := [(11, 1), (19, 1), (23, 1), (46, 1), (53, 1), (63, 1), (65, 1)] }, { coefficient := -1, powers := [(11, 1), (19, 1), (23, 1), (49, 1), (63, 1), (65, 1)] }, { coefficient := 1, powers := [(13, 1), (16, 1), (23, 1), (39, 1), (50, 1), (60, 1), (66, 1)] }]
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
    ¬ ∀ index : Fin 48,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component19.SelectedLeafB5_2_1_4.selectedHasNoCommonZero

end Krenn.Component19.SelectedLeafB5_2_1_4
