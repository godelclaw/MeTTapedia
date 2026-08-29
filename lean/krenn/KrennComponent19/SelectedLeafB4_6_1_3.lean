import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component19.SelectedLeafB4_6_1_3

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "619eb88891601898fbd944b4e26ab8bd3b670a63c30f5be09ad6b245568c5a58"
def certificateSHA256 : String := "0e743747050e04e07b9cfc02e8526635679ce1fe48b868faca56a700ebc51ed7"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 33 → Fin 675 := ![
  2,
  4,
  10,
  18,
  20,
  22,
  29,
  31,
  170,
  177,
  178,
  267,
  304,
  318,
  376,
  403,
  420,
  424,
  429,
  495,
  502,
  548,
  565,
  607,
  661,
  662,
  663,
  664,
  665,
  668,
  670,
  671,
  672
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 33 → SparsePoly (Fin 68) := ![
  [{ coefficient := 1, powers := [(5, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (35, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(31, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(35, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (50, 1)] }, { coefficient := 1, powers := [(26, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (26, 1)] }, { coefficient := 1, powers := [(16, 1), (21, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (27, 1)] }, { coefficient := 1, powers := [(16, 1), (21, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (21, 1), (57, 1)] }, { coefficient := 1, powers := [(13, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (61, 1)] }, { coefficient := 1, powers := [(13, 1), (50, 1)] }, { coefficient := 1, powers := [(20, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (55, 1)] }, { coefficient := 1, powers := [(32, 1), (44, 1)] }, { coefficient := 1, powers := [(35, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (26, 1), (49, 1)] }, { coefficient := 1, powers := [(17, 1), (26, 1), (43, 1)] }, { coefficient := 1, powers := [(17, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (26, 1), (49, 1)] }, { coefficient := 1, powers := [(20, 1), (26, 1), (43, 1)] }, { coefficient := 1, powers := [(20, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (50, 1)] }, { coefficient := 1, powers := [(5, 1), (38, 1)] }, { coefficient := 1, powers := [(19, 1), (30, 1), (50, 1)] }, { coefficient := 1, powers := [(20, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1)] }, { coefficient := 1, powers := [(13, 1), (32, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (61, 1)] }, { coefficient := 1, powers := [(13, 1), (27, 1), (49, 1)] }, { coefficient := 1, powers := [(13, 1), (58, 1)] }, { coefficient := 1, powers := [(20, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (26, 1), (60, 1)] }, { coefficient := 1, powers := [(11, 1), (26, 1), (48, 1)] }, { coefficient := 1, powers := [(16, 1), (26, 1), (43, 1)] }, { coefficient := 1, powers := [(16, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (32, 1), (61, 1)] }, { coefficient := 1, powers := [(4, 1), (35, 1), (58, 1)] }, { coefficient := 1, powers := [(4, 1), (38, 1), (55, 1)] }, { coefficient := 1, powers := [(17, 1), (31, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (27, 1), (49, 1)] }, { coefficient := 1, powers := [(11, 1), (58, 1)] }, { coefficient := 1, powers := [(17, 1), (27, 1), (43, 1)] }, { coefficient := 1, powers := [(17, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (46, 1), (54, 1)] }, { coefficient := 1, powers := [(25, 1), (58, 1)] }, { coefficient := 1, powers := [(32, 1), (50, 1)] }, { coefficient := 1, powers := [(38, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (53, 1)] }, { coefficient := 1, powers := [(23, 1), (57, 1)] }, { coefficient := 1, powers := [(29, 1), (43, 1)] }, { coefficient := 1, powers := [(29, 1), (48, 1)] }, { coefficient := 1, powers := [(34, 1), (40, 1)] }, { coefficient := 1, powers := [(37, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (40, 1), (60, 1)] }, { coefficient := 1, powers := [(1, 1), (43, 1), (57, 1)] }, { coefficient := 1, powers := [(1, 1), (48, 1), (53, 1)] }, { coefficient := 1, powers := [(4, 1), (29, 1), (60, 1)] }, { coefficient := 1, powers := [(4, 1), (34, 1), (57, 1)] }, { coefficient := 1, powers := [(4, 1), (37, 1), (53, 1)] }, { coefficient := 1, powers := [(7, 1), (23, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (34, 1), (48, 1)] }, { coefficient := 1, powers := [(7, 1), (37, 1), (43, 1)] }, { coefficient := 1, powers := [(11, 1), (23, 1), (57, 1)] }, { coefficient := 1, powers := [(11, 1), (29, 1), (48, 1)] }, { coefficient := 1, powers := [(11, 1), (37, 1), (40, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1), (53, 1)] }, { coefficient := 1, powers := [(16, 1), (29, 1), (43, 1)] }, { coefficient := 1, powers := [(16, 1), (34, 1), (40, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (41, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (44, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (50, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (38, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (25, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (50, 1)] }, { coefficient := 1, powers := [(8, 1), (38, 1), (44, 1)] }, { coefficient := 1, powers := [(13, 1), (25, 1), (58, 1)] }, { coefficient := 1, powers := [(13, 1), (32, 1), (50, 1)] }, { coefficient := 1, powers := [(13, 1), (38, 1), (41, 1)] }, { coefficient := 1, powers := [(20, 1), (25, 1), (55, 1)] }, { coefficient := 1, powers := [(20, 1), (32, 1), (44, 1)] }, { coefficient := 1, powers := [(20, 1), (35, 1), (41, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1)] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(44, 1)] }],
  [{ coefficient := 1, powers := [(57, 1)] }],
  [{ coefficient := 1, powers := [(58, 1), (65, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(26, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 33 → SparsePoly (Fin 68) := ![
  [{ coefficient := 1, powers := [(4, 1), (29, 1), (35, 1), (58, 1)] }, { coefficient := 1, powers := [(7, 1), (23, 1), (35, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (34, 1), (48, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (37, 1), (43, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (25, 1), (27, 1), (29, 1), (60, 1)] }, { coefficient := -1, powers := [(4, 1), (25, 1), (27, 1), (37, 1), (53, 1)] }, { coefficient := -1, powers := [(7, 1), (23, 1), (25, 1), (27, 1), (60, 1)] }, { coefficient := -1, powers := [(7, 1), (25, 1), (27, 1), (34, 1), (48, 1)] }, { coefficient := -1, powers := [(7, 1), (25, 1), (27, 1), (37, 1), (43, 1)] }, { coefficient := 1, powers := [(11, 1), (25, 1), (27, 1), (34, 1), (40, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (29, 1), (30, 1), (55, 1), (60, 1)] }, { coefficient := -1, powers := [(7, 1), (23, 1), (30, 1), (55, 1), (60, 1)] }, { coefficient := -1, powers := [(7, 1), (30, 1), (34, 1), (48, 1), (55, 1)] }, { coefficient := -1, powers := [(7, 1), (30, 1), (37, 1), (43, 1), (55, 1)] }, { coefficient := 1, powers := [(11, 1), (30, 1), (34, 1), (40, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (19, 1), (29, 1), (50, 1), (60, 1)] }, { coefficient := -1, powers := [(4, 1), (19, 1), (37, 1), (50, 1), (53, 1)] }, { coefficient := -1, powers := [(7, 1), (19, 1), (23, 1), (50, 1), (60, 1)] }, { coefficient := -1, powers := [(7, 1), (19, 1), (34, 1), (48, 1), (50, 1)] }, { coefficient := -1, powers := [(7, 1), (19, 1), (37, 1), (43, 1), (50, 1)] }, { coefficient := 1, powers := [(11, 1), (19, 1), (34, 1), (40, 1), (50, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (13, 1), (29, 1), (46, 1), (60, 1)] }, { coefficient := -1, powers := [(4, 1), (13, 1), (37, 1), (46, 1), (53, 1)] }, { coefficient := -1, powers := [(7, 1), (13, 1), (23, 1), (46, 1), (60, 1)] }, { coefficient := -1, powers := [(7, 1), (13, 1), (34, 1), (46, 1), (48, 1)] }, { coefficient := -1, powers := [(7, 1), (13, 1), (37, 1), (43, 1), (46, 1)] }, { coefficient := 1, powers := [(11, 1), (13, 1), (34, 1), (40, 1), (46, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (17, 1), (37, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (11, 1), (34, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (13, 1), (29, 1), (32, 1), (60, 1), (62, 1)] }, { coefficient := -1, powers := [(4, 1), (13, 1), (32, 1), (37, 1), (53, 1), (62, 1)] }, { coefficient := -1, powers := [(7, 1), (13, 1), (23, 1), (32, 1), (60, 1), (62, 1)] }, { coefficient := -1, powers := [(7, 1), (13, 1), (32, 1), (34, 1), (48, 1), (62, 1)] }, { coefficient := -1, powers := [(7, 1), (13, 1), (32, 1), (37, 1), (43, 1), (62, 1)] }, { coefficient := 1, powers := [(11, 1), (13, 1), (32, 1), (34, 1), (40, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(23, 1), (49, 1), (53, 1), (54, 1), (65, 1)] }, { coefficient := -1, powers := [(29, 1), (43, 1), (49, 1), (54, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (49, 1), (53, 1), (65, 1)] }, { coefficient := 1, powers := [(29, 1), (43, 1), (49, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (25, 1), (29, 1), (58, 1), (60, 1)] }, { coefficient := -1, powers := [(4, 1), (25, 1), (37, 1), (53, 1), (58, 1)] }, { coefficient := -1, powers := [(4, 1), (29, 1), (32, 1), (50, 1), (60, 1)] }, { coefficient := -1, powers := [(7, 1), (23, 1), (25, 1), (58, 1), (60, 1)] }, { coefficient := -1, powers := [(7, 1), (23, 1), (32, 1), (50, 1), (60, 1)] }, { coefficient := -1, powers := [(7, 1), (25, 1), (34, 1), (48, 1), (58, 1)] }, { coefficient := -1, powers := [(7, 1), (25, 1), (37, 1), (43, 1), (58, 1)] }, { coefficient := -1, powers := [(7, 1), (32, 1), (34, 1), (48, 1), (50, 1)] }, { coefficient := -1, powers := [(7, 1), (32, 1), (37, 1), (43, 1), (50, 1)] }, { coefficient := 1, powers := [(11, 1), (25, 1), (34, 1), (40, 1), (58, 1)] }, { coefficient := 1, powers := [(11, 1), (32, 1), (34, 1), (40, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (29, 1), (32, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (23, 1), (32, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (32, 1), (34, 1), (48, 1)] }, { coefficient := 1, powers := [(7, 1), (32, 1), (37, 1), (43, 1)] }, { coefficient := -1, powers := [(11, 1), (32, 1), (34, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (20, 1), (29, 1), (60, 1)] }, { coefficient := 1, powers := [(4, 1), (20, 1), (37, 1), (53, 1)] }, { coefficient := 1, powers := [(7, 1), (20, 1), (23, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (20, 1), (34, 1), (48, 1)] }, { coefficient := 1, powers := [(7, 1), (20, 1), (37, 1), (43, 1)] }, { coefficient := -1, powers := [(11, 1), (20, 1), (34, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (27, 1), (43, 1), (53, 1), (65, 1)] }, { coefficient := 1, powers := [(23, 1), (53, 1), (54, 1), (65, 1)] }, { coefficient := 1, powers := [(27, 1), (29, 1), (43, 2), (65, 1)] }, { coefficient := 1, powers := [(29, 1), (43, 1), (54, 1), (65, 1)] }],
  [{ coefficient := -2, powers := [(4, 1), (25, 1), (29, 1), (55, 1), (60, 1)] }, { coefficient := -1, powers := [(4, 1), (25, 1), (37, 1), (53, 1), (55, 1)] }, { coefficient := -2, powers := [(7, 1), (23, 1), (25, 1), (55, 1), (60, 1)] }, { coefficient := -2, powers := [(7, 1), (25, 1), (34, 1), (48, 1), (55, 1)] }, { coefficient := -2, powers := [(7, 1), (25, 1), (37, 1), (43, 1), (55, 1)] }, { coefficient := 2, powers := [(11, 1), (25, 1), (34, 1), (40, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (29, 1), (55, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (23, 1), (55, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (34, 1), (48, 1), (55, 1)] }, { coefficient := 1, powers := [(7, 1), (37, 1), (43, 1), (55, 1)] }, { coefficient := -1, powers := [(11, 1), (34, 1), (40, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (29, 1), (50, 1), (60, 1)] }, { coefficient := 1, powers := [(4, 1), (37, 1), (50, 1), (53, 1)] }, { coefficient := 1, powers := [(7, 1), (23, 1), (50, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (34, 1), (48, 1), (50, 1)] }, { coefficient := 1, powers := [(7, 1), (37, 1), (43, 1), (50, 1)] }, { coefficient := -1, powers := [(11, 1), (34, 1), (40, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (25, 1), (29, 1), (60, 1)] }, { coefficient := 1, powers := [(4, 1), (25, 1), (37, 1), (53, 1)] }, { coefficient := 1, powers := [(7, 1), (23, 1), (25, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (25, 1), (34, 1), (48, 1)] }, { coefficient := 1, powers := [(7, 1), (25, 1), (37, 1), (43, 1)] }, { coefficient := -1, powers := [(11, 1), (25, 1), (34, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (53, 1)] }, { coefficient := 1, powers := [(29, 1), (43, 1)] }, { coefficient := 1, powers := [(34, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (37, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(23, 1), (53, 1), (65, 1)] }, { coefficient := -1, powers := [(29, 1), (43, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (13, 1), (29, 1), (60, 1)] }, { coefficient := 1, powers := [(4, 1), (13, 1), (37, 1), (53, 1)] }, { coefficient := 1, powers := [(7, 1), (13, 1), (23, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (13, 1), (34, 1), (48, 1)] }, { coefficient := 1, powers := [(7, 1), (13, 1), (37, 1), (43, 1)] }, { coefficient := -1, powers := [(11, 1), (13, 1), (34, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(11, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(4, 1), (29, 1), (60, 1)] }, { coefficient := -1, powers := [(4, 1), (37, 1), (53, 1)] }, { coefficient := -1, powers := [(7, 1), (23, 1), (60, 1)] }, { coefficient := -1, powers := [(7, 1), (34, 1), (48, 1)] }, { coefficient := -1, powers := [(7, 1), (37, 1), (43, 1)] }, { coefficient := 1, powers := [(11, 1), (34, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (13, 1), (29, 1), (32, 1), (50, 1), (60, 1)] }, { coefficient := 1, powers := [(4, 1), (13, 1), (32, 1), (37, 1), (50, 1), (53, 1)] }, { coefficient := 1, powers := [(7, 1), (13, 1), (23, 1), (32, 1), (50, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (13, 1), (32, 1), (34, 1), (48, 1), (50, 1)] }, { coefficient := 1, powers := [(7, 1), (13, 1), (32, 1), (37, 1), (43, 1), (50, 1)] }, { coefficient := -1, powers := [(11, 1), (13, 1), (32, 1), (34, 1), (40, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(40, 1), (60, 1)] }, { coefficient := 1, powers := [(48, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (29, 1), (41, 1), (60, 1), (61, 1)] }, { coefficient := -1, powers := [(4, 1), (29, 1), (50, 1), (55, 1), (60, 1)] }, { coefficient := 1, powers := [(4, 1), (37, 1), (41, 1), (53, 1), (61, 1)] }, { coefficient := 1, powers := [(7, 1), (23, 1), (41, 1), (60, 1), (61, 1)] }, { coefficient := -1, powers := [(7, 1), (23, 1), (50, 1), (55, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (34, 1), (41, 1), (48, 1), (61, 1)] }, { coefficient := -1, powers := [(7, 1), (34, 1), (48, 1), (50, 1), (55, 1)] }, { coefficient := 1, powers := [(7, 1), (37, 1), (41, 1), (43, 1), (61, 1)] }, { coefficient := -1, powers := [(7, 1), (37, 1), (43, 1), (50, 1), (55, 1)] }, { coefficient := -1, powers := [(11, 1), (34, 1), (40, 1), (41, 1), (61, 1)] }, { coefficient := 1, powers := [(11, 1), (34, 1), (40, 1), (50, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (4, 1), (29, 1), (58, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (4, 1), (37, 1), (53, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (7, 1), (23, 1), (58, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (7, 1), (34, 1), (48, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (7, 1), (37, 1), (43, 1), (58, 1)] }, { coefficient := -1, powers := [(2, 1), (11, 1), (34, 1), (40, 1), (58, 1)] }, { coefficient := 1, powers := [(4, 1), (8, 1), (29, 1), (38, 1), (60, 1)] }, { coefficient := 1, powers := [(4, 1), (8, 1), (37, 1), (38, 1), (53, 1)] }, { coefficient := -1, powers := [(4, 1), (20, 1), (29, 1), (32, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (8, 1), (23, 1), (38, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (8, 1), (34, 1), (38, 1), (48, 1)] }, { coefficient := 1, powers := [(7, 1), (8, 1), (37, 1), (38, 1), (43, 1)] }, { coefficient := -1, powers := [(7, 1), (20, 1), (23, 1), (32, 1), (60, 1)] }, { coefficient := -1, powers := [(7, 1), (20, 1), (32, 1), (34, 1), (48, 1)] }, { coefficient := -1, powers := [(7, 1), (20, 1), (32, 1), (37, 1), (43, 1)] }, { coefficient := -1, powers := [(8, 1), (11, 1), (34, 1), (38, 1), (40, 1)] }, { coefficient := 1, powers := [(11, 1), (20, 1), (32, 1), (34, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (43, 1)] }, { coefficient := 1, powers := [(4, 1), (13, 1), (21, 1), (25, 1), (29, 1), (58, 1), (60, 1)] }, { coefficient := 1, powers := [(4, 1), (13, 1), (21, 1), (25, 1), (37, 1), (53, 1), (58, 1)] }, { coefficient := 1, powers := [(4, 1), (13, 1), (21, 1), (29, 1), (32, 1), (50, 1), (60, 1)] }, { coefficient := 1, powers := [(4, 1), (34, 1)] }, { coefficient := 1, powers := [(7, 1), (13, 1), (21, 1), (23, 1), (25, 1), (58, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (13, 1), (21, 1), (23, 1), (32, 1), (50, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (13, 1), (21, 1), (25, 1), (34, 1), (48, 1), (58, 1)] }, { coefficient := 1, powers := [(7, 1), (13, 1), (21, 1), (25, 1), (37, 1), (43, 1), (58, 1)] }, { coefficient := 1, powers := [(7, 1), (13, 1), (21, 1), (32, 1), (34, 1), (48, 1), (50, 1)] }, { coefficient := 1, powers := [(7, 1), (13, 1), (21, 1), (32, 1), (37, 1), (43, 1), (50, 1)] }, { coefficient := -1, powers := [(11, 1), (13, 1), (21, 1), (25, 1), (34, 1), (40, 1), (58, 1)] }, { coefficient := -1, powers := [(11, 1), (13, 1), (21, 1), (32, 1), (34, 1), (40, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (23, 1), (53, 1)] }, { coefficient := 1, powers := [(11, 1), (29, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (13, 1), (29, 1), (32, 1), (50, 1), (60, 1), (62, 1)] }, { coefficient := 1, powers := [(4, 1), (13, 1), (32, 1), (37, 1), (50, 1), (53, 1), (62, 1)] }, { coefficient := 2, powers := [(4, 1), (19, 1), (25, 1), (29, 1), (49, 1), (55, 1), (60, 1)] }, { coefficient := 1, powers := [(4, 1), (19, 1), (25, 1), (37, 1), (49, 1), (53, 1), (55, 1)] }, { coefficient := 2, powers := [(4, 1), (20, 1), (25, 1), (29, 1), (43, 1), (55, 1), (60, 1)] }, { coefficient := 1, powers := [(4, 1), (20, 1), (25, 1), (37, 1), (43, 1), (53, 1), (55, 1)] }, { coefficient := -1, powers := [(4, 1), (23, 1), (53, 1), (60, 1)] }, { coefficient := -1, powers := [(4, 1), (29, 1), (43, 1), (60, 1)] }, { coefficient := -1, powers := [(4, 1), (34, 1), (40, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (13, 1), (23, 1), (32, 1), (50, 1), (60, 1), (62, 1)] }, { coefficient := 1, powers := [(7, 1), (13, 1), (32, 1), (34, 1), (48, 1), (50, 1), (62, 1)] }, { coefficient := 1, powers := [(7, 1), (13, 1), (32, 1), (37, 1), (43, 1), (50, 1), (62, 1)] }, { coefficient := 2, powers := [(7, 1), (19, 1), (23, 1), (25, 1), (49, 1), (55, 1), (60, 1)] }, { coefficient := 2, powers := [(7, 1), (19, 1), (25, 1), (34, 1), (48, 1), (49, 1), (55, 1)] }, { coefficient := 2, powers := [(7, 1), (19, 1), (25, 1), (37, 1), (43, 1), (49, 1), (55, 1)] }, { coefficient := 2, powers := [(7, 1), (20, 1), (23, 1), (25, 1), (43, 1), (55, 1), (60, 1)] }, { coefficient := 2, powers := [(7, 1), (20, 1), (25, 1), (34, 1), (43, 1), (48, 1), (55, 1)] }, { coefficient := 2, powers := [(7, 1), (20, 1), (25, 1), (37, 1), (43, 2), (55, 1)] }, { coefficient := -1, powers := [(11, 1), (13, 1), (32, 1), (34, 1), (40, 1), (50, 1), (62, 1)] }, { coefficient := -2, powers := [(11, 1), (19, 1), (25, 1), (34, 1), (40, 1), (49, 1), (55, 1)] }, { coefficient := -2, powers := [(11, 1), (20, 1), (25, 1), (34, 1), (40, 1), (43, 1), (55, 1)] }, { coefficient := -1, powers := [(11, 1), (23, 1), (27, 1), (43, 1), (49, 1), (53, 1), (65, 1)] }, { coefficient := -1, powers := [(11, 1), (23, 1), (48, 1), (53, 1)] }, { coefficient := -1, powers := [(11, 1), (27, 1), (29, 1), (43, 2), (49, 1), (65, 1)] }, { coefficient := -1, powers := [(11, 1), (29, 1), (43, 1), (48, 1)] }, { coefficient := -1, powers := [(11, 1), (34, 1), (40, 1), (48, 1)] }, { coefficient := -1, powers := [(16, 1), (23, 1), (43, 1), (53, 1)] }, { coefficient := -1, powers := [(16, 1), (29, 1), (43, 2)] }, { coefficient := -1, powers := [(16, 1), (34, 1), (40, 1), (43, 1)] }, { coefficient := -1, powers := [(17, 1), (23, 1), (27, 1), (43, 2), (53, 1), (65, 1)] }, { coefficient := -1, powers := [(17, 1), (23, 1), (43, 1), (53, 1), (54, 1), (65, 1)] }, { coefficient := -1, powers := [(17, 1), (27, 1), (29, 1), (43, 3), (65, 1)] }, { coefficient := -1, powers := [(17, 1), (29, 1), (43, 2), (54, 1), (65, 1)] }]
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
    ¬ ∀ index : Fin 33,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component19.SelectedLeafB4_6_1_3.selectedHasNoCommonZero

end Krenn.Component19.SelectedLeafB4_6_1_3
