import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component60.SelectedLeafB4_4_3_6

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "9a8380b1b7c04cab5d955b806a355a3280bce385a55184162d091bffbb56d8cb"
def certificateSHA256 : String := "a136802d579b37480d24b74ea1f74f8c524951f91b20f6c47038c89433f83f66"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 40 → Fin 668 := ![
  6,
  13,
  20,
  48,
  70,
  99,
  148,
  150,
  154,
  155,
  168,
  211,
  213,
  298,
  301,
  302,
  304,
  353,
  372,
  377,
  436,
  443,
  497,
  500,
  537,
  582,
  583,
  602,
  604,
  605,
  654,
  655,
  657,
  658,
  659,
  660,
  661,
  664,
  665,
  667
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 40 → SparsePoly (Fin 67) := ![
  [{ coefficient := 1, powers := [(4, 1), (35, 1)] }],
  [{ coefficient := 1, powers := [(15, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (30, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (26, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(15, 1), (26, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (30, 1)] }, { coefficient := 1, powers := [(15, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (26, 1)] }, { coefficient := 1, powers := [(26, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (25, 1)] }, { coefficient := 1, powers := [(15, 1), (20, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (26, 1)] }, { coefficient := 1, powers := [(15, 1), (20, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (46, 1)] }, { coefficient := 1, powers := [(19, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (26, 1), (46, 1)] }, { coefficient := 1, powers := [(9, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (27, 1), (45, 1)] }, { coefficient := 1, powers := [(23, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (49, 1)] }, { coefficient := 1, powers := [(15, 1), (22, 1), (49, 1)] }, { coefficient := 1, powers := [(15, 1), (27, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (48, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1)] }, { coefficient := 1, powers := [(12, 1), (29, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (45, 1)] }, { coefficient := 1, powers := [(9, 1), (56, 1)] }, { coefficient := 1, powers := [(30, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (30, 1), (56, 1)] }, { coefficient := 1, powers := [(7, 1), (30, 1), (45, 1)] }, { coefficient := 1, powers := [(15, 1), (30, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (23, 1), (56, 1)] }, { coefficient := 1, powers := [(9, 1), (28, 1), (45, 1)] }, { coefficient := 1, powers := [(9, 1), (34, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (25, 1), (46, 1)] }, { coefficient := 1, powers := [(16, 1), (25, 1), (40, 1)] }, { coefficient := 1, powers := [(16, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (60, 1)] }, { coefficient := 1, powers := [(12, 1), (26, 1), (46, 1)] }, { coefficient := 1, powers := [(12, 1), (57, 1)] }, { coefficient := 1, powers := [(19, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (54, 1)] }, { coefficient := 1, powers := [(29, 1), (41, 1)] }, { coefficient := 1, powers := [(29, 1), (47, 1), (50, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (25, 1), (59, 1)] }, { coefficient := 1, powers := [(10, 1), (25, 1), (45, 1)] }, { coefficient := 1, powers := [(15, 1), (25, 1), (40, 1)] }, { coefficient := 1, powers := [(15, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (29, 1), (60, 1)] }, { coefficient := 1, powers := [(4, 1), (32, 1), (57, 1)] }, { coefficient := 1, powers := [(4, 1), (35, 1), (54, 1)] }, { coefficient := 1, powers := [(11, 1), (29, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (26, 1), (46, 1)] }, { coefficient := 1, powers := [(10, 1), (57, 1)] }, { coefficient := 1, powers := [(16, 1), (26, 1), (40, 1)] }, { coefficient := 1, powers := [(16, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(3, 1), (30, 1), (56, 1)] }, { coefficient := 1, powers := [(9, 1), (20, 1), (56, 1)] }, { coefficient := 1, powers := [(9, 1)] }, { coefficient := 1, powers := [(39, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (39, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (30, 1), (57, 1)] }, { coefficient := 1, powers := [(9, 1), (20, 1), (57, 1)] }, { coefficient := 1, powers := [(9, 1), (26, 1), (43, 1)] }, { coefficient := 1, powers := [(26, 1), (39, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (45, 1)] }, { coefficient := 1, powers := [(4, 1), (27, 1), (59, 1)] }, { coefficient := 1, powers := [(4, 1), (34, 1)] }, { coefficient := 1, powers := [(10, 1), (27, 1), (45, 1)] }, { coefficient := 1, powers := [(15, 1), (23, 1)] }, { coefficient := 1, powers := [(15, 1), (27, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (59, 1)] }, { coefficient := 1, powers := [(10, 1), (45, 1)] }, { coefficient := 1, powers := [(10, 1), (56, 1)] }, { coefficient := 1, powers := [(15, 1), (40, 1)] }, { coefficient := 1, powers := [(15, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (51, 1)] }, { coefficient := 1, powers := [(23, 1), (56, 1)] }, { coefficient := 1, powers := [(28, 1), (40, 1)] }, { coefficient := 1, powers := [(28, 1), (45, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (37, 1), (59, 1)] }, { coefficient := 1, powers := [(1, 1), (40, 1), (56, 1)] }, { coefficient := 1, powers := [(1, 1), (45, 1), (51, 1)] }, { coefficient := 1, powers := [(4, 1), (28, 1), (59, 1)] }, { coefficient := 1, powers := [(4, 1), (31, 1), (56, 1)] }, { coefficient := 1, powers := [(4, 1), (34, 1), (51, 1)] }, { coefficient := 1, powers := [(7, 1), (23, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (31, 1), (45, 1)] }, { coefficient := 1, powers := [(7, 1), (34, 1), (40, 1)] }, { coefficient := 1, powers := [(10, 1), (23, 1), (56, 1)] }, { coefficient := 1, powers := [(10, 1), (28, 1), (45, 1)] }, { coefficient := 1, powers := [(10, 1), (34, 1), (37, 1)] }, { coefficient := 1, powers := [(15, 1), (23, 1), (51, 1)] }, { coefficient := 1, powers := [(15, 1), (28, 1), (40, 1)] }, { coefficient := 1, powers := [(15, 1), (31, 1), (37, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (41, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (48, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (48, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1), (29, 1), (48, 1)] }, { coefficient := 1, powers := [(12, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (54, 1)] }, { coefficient := 1, powers := [(19, 1), (29, 1), (41, 1)] }, { coefficient := 1, powers := [(19, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1)] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(39, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(40, 1)] }],
  [{ coefficient := 1, powers := [(41, 1)] }],
  [{ coefficient := 1, powers := [(57, 1), (64, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(25, 1), (65, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(29, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 40 → SparsePoly (Fin 67) := ![
  [{ coefficient := 1, powers := [(5, 1), (9, 1), (34, 1), (51, 1), (54, 1), (62, 1)] }, { coefficient := -1, powers := [(9, 1), (12, 1), (34, 1), (38, 1), (51, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(9, 1), (22, 1), (51, 1), (56, 1), (62, 2)] }, { coefficient := 1, powers := [(20, 1), (23, 1), (56, 1), (62, 1), (65, 1)] }, { coefficient := -1, powers := [(22, 1), (37, 1), (59, 1), (62, 1)] }, { coefficient := -1, powers := [(23, 1), (51, 1), (62, 1)] }, { coefficient := 1, powers := [(23, 1), (62, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (9, 1), (24, 1), (26, 1), (34, 1), (51, 1), (52, 1), (62, 2)] }, { coefficient := 2, powers := [(4, 1), (9, 1), (24, 1), (34, 1), (51, 1), (54, 1), (62, 2)] }],
  [{ coefficient := -1, powers := [(23, 1), (51, 1), (62, 1), (64, 1)] }, { coefficient := -1, powers := [(28, 1), (45, 1), (62, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (31, 1), (46, 1), (62, 1), (64, 1)] }, { coefficient := -1, powers := [(4, 1), (34, 1), (46, 1), (62, 1), (64, 1)] }, { coefficient := 1, powers := [(7, 1), (31, 1), (46, 1), (62, 1), (64, 1)] }, { coefficient := -1, powers := [(10, 1), (28, 1), (46, 1), (62, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (46, 1), (51, 1), (62, 1), (64, 1)] }, { coefficient := -2, powers := [(23, 1), (46, 1), (56, 1), (62, 1), (64, 1)] }, { coefficient := -1, powers := [(23, 1), (46, 1), (62, 1), (64, 1), (65, 1)] }, { coefficient := 1, powers := [(28, 1), (46, 1), (62, 1), (64, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (45, 1), (62, 1)] }, { coefficient := -1, powers := [(27, 1), (37, 1), (59, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(15, 1), (23, 1), (43, 1), (45, 1), (56, 1), (62, 1), (64, 1)] }, { coefficient := -1, powers := [(15, 1), (23, 1), (46, 1), (51, 1), (62, 1), (64, 1)] }, { coefficient := 2, powers := [(15, 1), (23, 1), (46, 1), (56, 1), (62, 1), (64, 1)] }, { coefficient := 1, powers := [(15, 1), (23, 1), (46, 1), (62, 1), (64, 1), (65, 1)] }, { coefficient := -1, powers := [(15, 1), (28, 1), (46, 1), (62, 1), (64, 1), (65, 1)] }, { coefficient := 1, powers := [(43, 1), (56, 1), (62, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (23, 1), (46, 1), (53, 1), (56, 1), (62, 1), (64, 1)] }, { coefficient := 1, powers := [(9, 1), (27, 1), (46, 1), (53, 1), (56, 2), (62, 1), (64, 1)] }, { coefficient := -1, powers := [(23, 1), (49, 1), (56, 1), (62, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(9, 1), (23, 1), (46, 1), (56, 1), (62, 1), (64, 1)] }, { coefficient := -1, powers := [(9, 1), (27, 1), (46, 1), (56, 2), (62, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (9, 1), (24, 1), (26, 1), (34, 1), (51, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (31, 1), (45, 1), (62, 1), (64, 1)] }, { coefficient := 1, powers := [(4, 1), (34, 1), (45, 1), (62, 1), (64, 1)] }, { coefficient := -1, powers := [(7, 1), (31, 1), (45, 1), (62, 1), (64, 1)] }, { coefficient := 1, powers := [(10, 1), (28, 1), (45, 1), (62, 1), (64, 1)] }, { coefficient := 1, powers := [(15, 1), (23, 1), (51, 1), (62, 1), (64, 1)] }, { coefficient := -2, powers := [(15, 1), (23, 1), (56, 1), (62, 1), (64, 1)] }, { coefficient := -1, powers := [(15, 1), (23, 1), (62, 1), (64, 1), (65, 1)] }, { coefficient := 1, powers := [(15, 1), (28, 1), (62, 1), (64, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (59, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (51, 1), (56, 1), (62, 2)] }, { coefficient := 1, powers := [(37, 1), (59, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (9, 1), (34, 1), (51, 1), (54, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (9, 1), (34, 1), (48, 1), (51, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (31, 1), (62, 1)] }, { coefficient := -1, powers := [(4, 1), (34, 1), (62, 1)] }, { coefficient := 1, powers := [(7, 1), (27, 1), (59, 1), (62, 1)] }, { coefficient := 1, powers := [(15, 1), (23, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(23, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(10, 1), (62, 1)] }, { coefficient := 1, powers := [(15, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(9, 1), (23, 1), (53, 1), (56, 1), (62, 1), (64, 1)] }, { coefficient := -1, powers := [(9, 1), (27, 1), (53, 1), (56, 2), (62, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (9, 1), (24, 1), (34, 1), (51, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (9, 1), (19, 1), (34, 1), (51, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (23, 1), (62, 1), (65, 1)] }, { coefficient := -1, powers := [(9, 1), (28, 1), (62, 1), (65, 1)] }, { coefficient := -1, powers := [(23, 1), (49, 1), (62, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (9, 1), (34, 1), (51, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (23, 1), (56, 1), (62, 1), (64, 1)] }, { coefficient := 1, powers := [(9, 1), (27, 1), (56, 2), (62, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(15, 1), (23, 1), (45, 1), (62, 1)] }, { coefficient := 1, powers := [(62, 1)] }],
  [{ coefficient := 1, powers := [(15, 1), (23, 1), (45, 1), (56, 1), (62, 1), (64, 1)] }, { coefficient := -1, powers := [(56, 1), (62, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (56, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(9, 1), (23, 1), (25, 1), (62, 1), (65, 1)] }, { coefficient := 1, powers := [(9, 1), (25, 1), (28, 1), (62, 1), (65, 1)] }, { coefficient := -1, powers := [(9, 1), (27, 1), (56, 1), (62, 1)] }, { coefficient := -1, powers := [(9, 1), (28, 1), (62, 1)] }, { coefficient := 1, powers := [(23, 1), (25, 1), (49, 1), (62, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (30, 1), (62, 1)] }, { coefficient := -1, powers := [(9, 1), (15, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (9, 1), (34, 1), (51, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(9, 1), (37, 1), (59, 1), (62, 1)] }, { coefficient := -1, powers := [(9, 1), (45, 1), (51, 1), (62, 1)] }, { coefficient := -1, powers := [(9, 1), (45, 1), (56, 1), (62, 1)] }, { coefficient := -1, powers := [(9, 1), (49, 1), (51, 1), (56, 1), (62, 2)] }, { coefficient := -1, powers := [(37, 1), (49, 1), (59, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (9, 1), (34, 1), (38, 1), (51, 1), (60, 1), (62, 1)] }, { coefficient := 1, powers := [(4, 1), (9, 1), (34, 1), (48, 1), (51, 1), (54, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (9, 1), (19, 1), (24, 1), (26, 1), (34, 1), (51, 1), (52, 1), (62, 1)] }, { coefficient := -2, powers := [(4, 1), (9, 1), (19, 1), (24, 1), (34, 1), (51, 1), (54, 1), (62, 1)] }, { coefficient := -1, powers := [(9, 1), (15, 1), (27, 1), (51, 1), (56, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(1, 1), (9, 1), (56, 1), (62, 1)] }, { coefficient := -1, powers := [(4, 1), (28, 1), (30, 1), (62, 1)] }, { coefficient := -1, powers := [(7, 1), (9, 1), (34, 1), (62, 1)] }, { coefficient := 1, powers := [(9, 1), (15, 1), (28, 1), (62, 1)] }, { coefficient := 1, powers := [(9, 1), (16, 1), (23, 1), (25, 1), (53, 1), (56, 1), (62, 1), (64, 1)] }, { coefficient := -1, powers := [(9, 1), (16, 1), (23, 1), (26, 1), (56, 1), (62, 1), (64, 1)] }, { coefficient := 1, powers := [(9, 1), (16, 1), (25, 1), (27, 1), (53, 1), (56, 2), (62, 1), (64, 1)] }, { coefficient := -1, powers := [(9, 1), (16, 1), (26, 1), (27, 1), (56, 2), (62, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (4, 1), (9, 1), (34, 1), (51, 1), (57, 1), (62, 1)] }, { coefficient := -1, powers := [(4, 1), (8, 1), (9, 1), (34, 1), (35, 1), (51, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (15, 1), (23, 1), (39, 1), (45, 1), (56, 1), (62, 1)] }, { coefficient := 1, powers := [(0, 1), (39, 1), (56, 1), (62, 1)] }, { coefficient := -1, powers := [(3, 1), (15, 1), (23, 1), (30, 1), (45, 1), (56, 1), (62, 1)] }, { coefficient := 1, powers := [(3, 1), (30, 1), (56, 1), (62, 1)] }, { coefficient := -1, powers := [(4, 1), (9, 1), (31, 1), (45, 1), (62, 1)] }, { coefficient := -1, powers := [(4, 1), (9, 1), (34, 1), (45, 1), (62, 1)] }, { coefficient := 1, powers := [(4, 1), (23, 1), (30, 1), (51, 1), (62, 1)] }, { coefficient := 1, powers := [(4, 1), (28, 1), (30, 1), (45, 1), (62, 1)] }, { coefficient := 1, powers := [(7, 1), (9, 1), (31, 1), (45, 1), (62, 1)] }, { coefficient := -1, powers := [(9, 1), (10, 1), (23, 1), (56, 1), (62, 1)] }, { coefficient := -1, powers := [(9, 1), (10, 1), (27, 1), (56, 2), (62, 1)] }, { coefficient := -1, powers := [(9, 1), (10, 1), (28, 1), (45, 1), (62, 1)] }, { coefficient := -1, powers := [(9, 1), (15, 1), (20, 1), (23, 1), (45, 1), (56, 1), (62, 1)] }, { coefficient := -1, powers := [(9, 1), (15, 1), (23, 1), (51, 1), (62, 1)] }, { coefficient := 2, powers := [(9, 1), (15, 1), (23, 1), (56, 1), (62, 1)] }, { coefficient := 1, powers := [(9, 1), (15, 1), (23, 1), (62, 1), (65, 1)] }, { coefficient := -1, powers := [(9, 1), (15, 1), (28, 1), (62, 1), (65, 1)] }, { coefficient := 1, powers := [(9, 1), (20, 1), (56, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (9, 1), (23, 1), (59, 1), (62, 1)] }, { coefficient := -1, powers := [(7, 1), (9, 1), (28, 1), (59, 1), (62, 1)] }, { coefficient := -1, powers := [(7, 1), (23, 1), (49, 1), (59, 1), (62, 1)] }, { coefficient := 1, powers := [(9, 1), (10, 1), (23, 1), (56, 1), (62, 1)] }, { coefficient := -1, powers := [(9, 1), (10, 1), (28, 1), (56, 1), (62, 1)] }, { coefficient := 1, powers := [(9, 1), (15, 1), (23, 1), (51, 1), (62, 1)] }, { coefficient := -1, powers := [(9, 1), (15, 1), (28, 1), (51, 1), (62, 1)] }, { coefficient := -1, powers := [(15, 1), (23, 1), (49, 1), (51, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (9, 1), (19, 1), (34, 1), (47, 1), (50, 1), (51, 1), (62, 1)] }, { coefficient := 1, powers := [(5, 1), (9, 1), (11, 1), (34, 1), (46, 1), (51, 1), (62, 1)] }]
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
    ¬ ∀ index : Fin 40,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component60.SelectedLeafB4_4_3_6.selectedHasNoCommonZero

end Krenn.Component60.SelectedLeafB4_4_3_6
