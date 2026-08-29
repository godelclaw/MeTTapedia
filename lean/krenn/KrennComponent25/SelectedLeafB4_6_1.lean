import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component25.SelectedLeafB4_6_1

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "b40566c4a9b98736483d1bf8385f3bd910b773fb00ad1752f0b25bd7be153e63"
def certificateSHA256 : String := "27f8bb2eee12d1c41a716c75369c9198ed6f8f3f5fc365641aa2bf825e57ed52"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 38 → Fin 665 := ![
  2,
  6,
  8,
  11,
  14,
  15,
  16,
  17,
  19,
  21,
  142,
  149,
  150,
  151,
  152,
  153,
  162,
  170,
  175,
  299,
  300,
  312,
  353,
  388,
  430,
  435,
  439,
  450,
  604,
  605,
  654,
  655,
  657,
  658,
  659,
  661,
  663,
  664
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 38 → SparsePoly (Fin 65) := ![
  [{ coefficient := 1, powers := [(9, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (54, 1)] }, { coefficient := 1, powers := [(18, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (35, 1)] }, { coefficient := 1, powers := [(10, 1), (27, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (32, 1)] }, { coefficient := 1, powers := [(14, 1), (22, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (29, 1)] }, { coefficient := 1, powers := [(29, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (24, 1)] }, { coefficient := 1, powers := [(14, 1), (18, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (18, 1)] }, { coefficient := 1, powers := [(16, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (43, 1)] }, { coefficient := 1, powers := [(27, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(57, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (30, 1)] }, { coefficient := 1, powers := [(14, 1), (18, 1), (51, 1)] }, { coefficient := 1, powers := [(14, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (60, 1)] }, { coefficient := 1, powers := [(12, 1), (57, 1)] }, { coefficient := 1, powers := [(17, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (57, 1)] }, { coefficient := 1, powers := [(29, 1), (48, 1)] }, { coefficient := 1, powers := [(35, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (29, 1), (60, 1)] }, { coefficient := 1, powers := [(4, 1), (32, 1), (57, 1)] }, { coefficient := 1, powers := [(4, 1), (35, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (18, 1), (56, 1)] }, { coefficient := 1, powers := [(12, 1)] }, { coefficient := 1, powers := [(16, 1), (18, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (48, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1), (48, 1)] }, { coefficient := 1, powers := [(17, 1), (23, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1)] }, { coefficient := 1, powers := [(12, 1), (29, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (60, 1)] }, { coefficient := 1, powers := [(12, 1), (48, 1)] }, { coefficient := 1, powers := [(17, 1), (19, 1), (53, 1)] }, { coefficient := 1, powers := [(17, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (54, 1)] }, { coefficient := 1, powers := [(29, 1), (41, 1)] }, { coefficient := 1, powers := [(29, 1), (47, 1), (50, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (59, 1)] }, { coefficient := 1, powers := [(10, 1), (45, 1)] }, { coefficient := 1, powers := [(10, 1), (56, 1)] }, { coefficient := 1, powers := [(14, 1), (40, 1)] }, { coefficient := 1, powers := [(14, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (52, 1)] }, { coefficient := 1, powers := [(21, 1), (56, 1)] }, { coefficient := 1, powers := [(26, 1), (40, 1)] }, { coefficient := 1, powers := [(26, 1), (45, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (37, 1), (59, 1)] }, { coefficient := 1, powers := [(1, 1), (40, 1), (56, 1)] }, { coefficient := 1, powers := [(1, 1), (45, 1), (52, 1)] }, { coefficient := 1, powers := [(4, 1), (26, 1), (59, 1)] }, { coefficient := 1, powers := [(4, 1), (31, 1), (56, 1)] }, { coefficient := 1, powers := [(4, 1), (34, 1), (52, 1)] }, { coefficient := 1, powers := [(7, 1), (21, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (31, 1), (45, 1)] }, { coefficient := 1, powers := [(7, 1), (34, 1), (40, 1)] }, { coefficient := 1, powers := [(10, 1), (21, 1), (56, 1)] }, { coefficient := 1, powers := [(10, 1), (26, 1), (45, 1)] }, { coefficient := 1, powers := [(10, 1), (34, 1), (37, 1)] }, { coefficient := 1, powers := [(14, 1), (21, 1), (52, 1)] }, { coefficient := 1, powers := [(14, 1), (26, 1), (40, 1)] }, { coefficient := 1, powers := [(14, 1), (31, 1), (37, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (41, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (48, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (23, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (48, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(12, 1), (23, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1), (29, 1), (48, 1)] }, { coefficient := 1, powers := [(12, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(17, 1), (23, 1), (54, 1)] }, { coefficient := 1, powers := [(17, 1), (29, 1), (41, 1)] }, { coefficient := 1, powers := [(17, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1)] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(39, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(41, 1)] }],
  [{ coefficient := 1, powers := [(56, 1)] }],
  [{ coefficient := 1, powers := [(57, 1), (64, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 38 → SparsePoly (Fin 65) := ![
  [{ coefficient := 2, powers := [(4, 1), (12, 1), (29, 1), (34, 1), (48, 1), (52, 1), (62, 1), (64, 1)] }, { coefficient := -1, powers := [(5, 1), (7, 1), (29, 1), (34, 1), (52, 1), (60, 1), (62, 1), (64, 1)] }, { coefficient := 2, powers := [(7, 1), (12, 1), (26, 1), (29, 1), (30, 1), (48, 1), (52, 1), (62, 2), (64, 1)] }, { coefficient := -2, powers := [(7, 1), (12, 1), (26, 1), (29, 1), (48, 1), (59, 1), (62, 1), (64, 1)] }, { coefficient := -2, powers := [(7, 1), (12, 1), (29, 1), (30, 1), (31, 1), (37, 1), (48, 1), (62, 2), (64, 1)] }, { coefficient := 2, powers := [(7, 1), (12, 1), (29, 1), (31, 1), (45, 1), (48, 1), (62, 1), (64, 1)] }, { coefficient := 2, powers := [(7, 1), (12, 1), (29, 1), (34, 1), (40, 1), (48, 1), (62, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (27, 1), (34, 1), (52, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(21, 1), (52, 1), (64, 1)] }, { coefficient := -1, powers := [(24, 1), (26, 1), (51, 1), (52, 1), (62, 1), (64, 1)] }, { coefficient := 1, powers := [(24, 1), (31, 1), (37, 1), (51, 1), (62, 1), (64, 1)] }, { coefficient := -1, powers := [(26, 1), (40, 1), (64, 1)] }, { coefficient := -1, powers := [(26, 1), (45, 1), (64, 1)] }, { coefficient := -1, powers := [(31, 1), (37, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (22, 1), (26, 1), (30, 1), (52, 1), (57, 1), (62, 1)] }, { coefficient := 1, powers := [(5, 1), (22, 1), (26, 1), (57, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (22, 1), (30, 1), (31, 1), (37, 1), (57, 1), (62, 1)] }, { coefficient := -1, powers := [(5, 1), (22, 1), (31, 1), (45, 1), (57, 1)] }, { coefficient := -1, powers := [(5, 1), (22, 1), (34, 1), (40, 1), (57, 1)] }, { coefficient := -2, powers := [(17, 1), (22, 1), (26, 1), (30, 1), (38, 1), (52, 1), (62, 1)] }, { coefficient := 2, powers := [(17, 1), (22, 1), (26, 1), (38, 1), (59, 1)] }, { coefficient := 2, powers := [(17, 1), (22, 1), (30, 1), (31, 1), (37, 1), (38, 1), (62, 1)] }, { coefficient := -2, powers := [(17, 1), (22, 1), (31, 1), (38, 1), (45, 1)] }, { coefficient := -2, powers := [(17, 1), (22, 1), (34, 1), (38, 1), (40, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (22, 1), (34, 1), (48, 1), (52, 1)] }, { coefficient := -1, powers := [(7, 1), (22, 1), (26, 1), (30, 1), (48, 1), (52, 1), (62, 1)] }, { coefficient := 1, powers := [(7, 1), (22, 1), (26, 1), (48, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (22, 1), (30, 1), (31, 1), (37, 1), (48, 1), (62, 1)] }, { coefficient := -1, powers := [(7, 1), (22, 1), (31, 1), (45, 1), (48, 1)] }, { coefficient := -1, powers := [(7, 1), (22, 1), (34, 1), (40, 1), (48, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (23, 1), (24, 1), (34, 1), (52, 1), (53, 1), (57, 1), (64, 1)] }, { coefficient := 1, powers := [(4, 1), (23, 1), (34, 1), (43, 1), (52, 1), (54, 1), (64, 1)] }, { coefficient := -1, powers := [(7, 1), (23, 1), (24, 1), (26, 1), (30, 1), (52, 1), (53, 1), (57, 1), (62, 1), (64, 1)] }, { coefficient := 1, powers := [(7, 1), (23, 1), (24, 1), (26, 1), (53, 1), (57, 1), (59, 1), (64, 1)] }, { coefficient := 1, powers := [(7, 1), (23, 1), (24, 1), (30, 1), (31, 1), (37, 1), (53, 1), (57, 1), (62, 1), (64, 1)] }, { coefficient := -1, powers := [(7, 1), (23, 1), (24, 1), (31, 1), (45, 1), (53, 1), (57, 1), (64, 1)] }, { coefficient := -1, powers := [(7, 1), (23, 1), (24, 1), (34, 1), (40, 1), (53, 1), (57, 1), (64, 1)] }, { coefficient := 1, powers := [(7, 1), (23, 1), (26, 1), (30, 1), (43, 1), (52, 1), (54, 1), (62, 1), (64, 1)] }, { coefficient := -1, powers := [(7, 1), (23, 1), (26, 1), (43, 1), (54, 1), (59, 1), (64, 1)] }, { coefficient := -1, powers := [(7, 1), (23, 1), (30, 1), (31, 1), (37, 1), (43, 1), (54, 1), (62, 1), (64, 1)] }, { coefficient := 1, powers := [(7, 1), (23, 1), (31, 1), (43, 1), (45, 1), (54, 1), (64, 1)] }, { coefficient := 1, powers := [(7, 1), (23, 1), (34, 1), (40, 1), (43, 1), (54, 1), (64, 1)] }],
  [{ coefficient := -2, powers := [(4, 1), (17, 1), (23, 1), (34, 1), (40, 1), (52, 1), (54, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (17, 1), (29, 1), (34, 1), (52, 1), (53, 1), (64, 1)] }, { coefficient := -1, powers := [(7, 1), (17, 1), (26, 1), (29, 1), (30, 1), (52, 1), (53, 1), (62, 1), (64, 1)] }, { coefficient := 1, powers := [(7, 1), (17, 1), (26, 1), (29, 1), (53, 1), (59, 1), (64, 1)] }, { coefficient := 1, powers := [(7, 1), (17, 1), (29, 1), (30, 1), (31, 1), (37, 1), (53, 1), (62, 1), (64, 1)] }, { coefficient := -1, powers := [(7, 1), (17, 1), (29, 1), (31, 1), (45, 1), (53, 1), (64, 1)] }, { coefficient := -1, powers := [(7, 1), (17, 1), (29, 1), (34, 1), (40, 1), (53, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (59, 1), (64, 1)] }, { coefficient := 1, powers := [(14, 1), (52, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (17, 1), (34, 1), (50, 1), (52, 1)] }, { coefficient := 1, powers := [(7, 1), (17, 1), (26, 1), (30, 1), (50, 1), (52, 1), (62, 1)] }, { coefficient := -1, powers := [(7, 1), (17, 1), (26, 1), (50, 1), (59, 1)] }, { coefficient := -1, powers := [(7, 1), (17, 1), (30, 1), (31, 1), (37, 1), (50, 1), (62, 1)] }, { coefficient := 1, powers := [(7, 1), (17, 1), (31, 1), (45, 1), (50, 1)] }, { coefficient := 1, powers := [(7, 1), (17, 1), (34, 1), (40, 1), (50, 1)] }],
  [{ coefficient := 2, powers := [(4, 1), (17, 1), (23, 1), (34, 1), (40, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (34, 1), (52, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (29, 1), (34, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (26, 1), (30, 1), (52, 1), (57, 1), (62, 1)] }, { coefficient := -1, powers := [(5, 1), (26, 1), (57, 1), (59, 1)] }, { coefficient := -1, powers := [(5, 1), (30, 1), (31, 1), (37, 1), (57, 1), (62, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (45, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (40, 1), (57, 1)] }, { coefficient := 2, powers := [(17, 1), (26, 1), (30, 1), (38, 1), (52, 1), (62, 1)] }, { coefficient := -2, powers := [(17, 1), (26, 1), (38, 1), (59, 1)] }, { coefficient := -2, powers := [(17, 1), (30, 1), (31, 1), (37, 1), (38, 1), (62, 1)] }, { coefficient := 2, powers := [(17, 1), (31, 1), (38, 1), (45, 1)] }, { coefficient := 2, powers := [(17, 1), (34, 1), (38, 1), (40, 1)] }],
  [{ coefficient := -2, powers := [(4, 1), (12, 1), (34, 1), (48, 1), (52, 1), (62, 1)] }, { coefficient := 1, powers := [(5, 1), (7, 1), (34, 1), (52, 1), (60, 1), (62, 1)] }, { coefficient := -2, powers := [(7, 1), (12, 1), (26, 1), (30, 1), (48, 1), (52, 1), (62, 2)] }, { coefficient := 2, powers := [(7, 1), (12, 1), (26, 1), (48, 1), (59, 1), (62, 1)] }, { coefficient := 2, powers := [(7, 1), (12, 1), (30, 1), (31, 1), (37, 1), (48, 1), (62, 2)] }, { coefficient := -2, powers := [(7, 1), (12, 1), (31, 1), (45, 1), (48, 1), (62, 1)] }, { coefficient := -2, powers := [(7, 1), (12, 1), (34, 1), (40, 1), (48, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(26, 1), (51, 1), (52, 1), (62, 1)] }, { coefficient := -1, powers := [(31, 1), (37, 1), (51, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (23, 1), (34, 1), (52, 1), (53, 1), (57, 1)] }, { coefficient := 1, powers := [(7, 1), (23, 1), (26, 1), (30, 1), (52, 1), (53, 1), (57, 1), (62, 1)] }, { coefficient := -1, powers := [(7, 1), (23, 1), (26, 1), (53, 1), (57, 1), (59, 1)] }, { coefficient := -1, powers := [(7, 1), (23, 1), (30, 1), (31, 1), (37, 1), (53, 1), (57, 1), (62, 1)] }, { coefficient := 1, powers := [(7, 1), (23, 1), (31, 1), (45, 1), (53, 1), (57, 1)] }, { coefficient := 1, powers := [(7, 1), (23, 1), (34, 1), (40, 1), (53, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (16, 1), (34, 1), (52, 1), (54, 1)] }, { coefficient := -1, powers := [(7, 1), (16, 1), (26, 1), (30, 1), (52, 1), (54, 1), (62, 1)] }, { coefficient := 1, powers := [(7, 1), (16, 1), (26, 1), (54, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (16, 1), (30, 1), (31, 1), (37, 1), (54, 1), (62, 1)] }, { coefficient := -1, powers := [(7, 1), (16, 1), (31, 1), (45, 1), (54, 1)] }, { coefficient := -1, powers := [(7, 1), (16, 1), (34, 1), (40, 1), (54, 1)] }],
  [{ coefficient := -2, powers := [(4, 1), (17, 1), (23, 1), (34, 1), (52, 1), (54, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(26, 1), (52, 1), (62, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (23, 1), (34, 1), (52, 1)] }, { coefficient := 1, powers := [(7, 1), (23, 1), (26, 1), (30, 1), (52, 1), (62, 1)] }, { coefficient := -1, powers := [(7, 1), (23, 1), (26, 1), (59, 1)] }, { coefficient := -1, powers := [(7, 1), (23, 1), (30, 1), (31, 1), (37, 1), (62, 1)] }, { coefficient := 1, powers := [(7, 1), (23, 1), (31, 1), (45, 1)] }, { coefficient := 1, powers := [(7, 1), (23, 1), (34, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (12, 1), (34, 1), (52, 1)] }, { coefficient := 1, powers := [(7, 1), (12, 1), (26, 1), (30, 1), (52, 1), (62, 1)] }, { coefficient := -1, powers := [(7, 1), (12, 1), (26, 1), (59, 1)] }, { coefficient := -1, powers := [(7, 1), (12, 1), (30, 1), (31, 1), (37, 1), (62, 1)] }, { coefficient := 1, powers := [(7, 1), (12, 1), (31, 1), (45, 1)] }, { coefficient := 1, powers := [(7, 1), (12, 1), (34, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (34, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (23, 1), (34, 1), (52, 1), (57, 1)] }, { coefficient := -1, powers := [(7, 1), (23, 1), (26, 1), (30, 1), (52, 1), (57, 1), (62, 1)] }, { coefficient := 1, powers := [(7, 1), (23, 1), (26, 1), (57, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (23, 1), (30, 1), (31, 1), (37, 1), (57, 1), (62, 1)] }, { coefficient := -1, powers := [(7, 1), (23, 1), (31, 1), (45, 1), (57, 1)] }, { coefficient := -1, powers := [(7, 1), (23, 1), (34, 1), (40, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (34, 1), (52, 1), (54, 1)] }, { coefficient := 1, powers := [(7, 1), (26, 1), (30, 1), (52, 1), (54, 1), (62, 1)] }, { coefficient := -1, powers := [(7, 1), (26, 1), (54, 1), (59, 1)] }, { coefficient := -1, powers := [(7, 1), (30, 1), (31, 1), (37, 1), (54, 1), (62, 1)] }, { coefficient := 1, powers := [(7, 1), (31, 1), (45, 1), (54, 1)] }, { coefficient := 1, powers := [(7, 1), (34, 1), (40, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (34, 1), (48, 1), (52, 1)] }, { coefficient := 1, powers := [(7, 1), (26, 1), (30, 1), (48, 1), (52, 1), (62, 1)] }, { coefficient := -1, powers := [(7, 1), (26, 1), (48, 1), (59, 1)] }, { coefficient := -1, powers := [(7, 1), (30, 1), (31, 1), (37, 1), (48, 1), (62, 1)] }, { coefficient := 1, powers := [(7, 1), (31, 1), (45, 1), (48, 1)] }, { coefficient := 1, powers := [(7, 1), (34, 1), (40, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (29, 1), (34, 1), (52, 1)] }, { coefficient := 1, powers := [(7, 1), (26, 1), (29, 1), (30, 1), (52, 1), (62, 1)] }, { coefficient := -1, powers := [(7, 1), (26, 1), (29, 1), (59, 1)] }, { coefficient := -1, powers := [(7, 1), (29, 1), (30, 1), (31, 1), (37, 1), (62, 1)] }, { coefficient := 1, powers := [(7, 1), (29, 1), (31, 1), (45, 1)] }, { coefficient := 1, powers := [(7, 1), (29, 1), (34, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (17, 1), (34, 1), (52, 1)] }, { coefficient := -1, powers := [(7, 1), (17, 1), (26, 1), (30, 1), (52, 1), (62, 1)] }, { coefficient := 1, powers := [(7, 1), (17, 1), (26, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (17, 1), (30, 1), (31, 1), (37, 1), (62, 1)] }, { coefficient := -1, powers := [(7, 1), (17, 1), (31, 1), (45, 1)] }, { coefficient := -1, powers := [(7, 1), (17, 1), (34, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(26, 1)] }],
  [{ coefficient := 1, powers := [(10, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(4, 1), (34, 1), (52, 1)] }, { coefficient := -1, powers := [(7, 1), (26, 1), (30, 1), (52, 1), (62, 1)] }, { coefficient := 1, powers := [(7, 1), (26, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (30, 1), (31, 1), (37, 1), (62, 1)] }, { coefficient := -1, powers := [(7, 1), (31, 1), (45, 1)] }, { coefficient := -1, powers := [(7, 1), (34, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(37, 1), (59, 1)] }, { coefficient := 1, powers := [(45, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (34, 1), (38, 1), (52, 1), (60, 1)] }, { coefficient := 1, powers := [(4, 1), (34, 1), (41, 1), (52, 1), (57, 1)] }, { coefficient := -1, powers := [(4, 1), (34, 1), (48, 1), (52, 1), (54, 1)] }, { coefficient := 1, powers := [(7, 1), (26, 1), (30, 1), (38, 1), (52, 1), (60, 1), (62, 1)] }, { coefficient := 1, powers := [(7, 1), (26, 1), (30, 1), (41, 1), (52, 1), (57, 1), (62, 1)] }, { coefficient := -1, powers := [(7, 1), (26, 1), (30, 1), (48, 1), (52, 1), (54, 1), (62, 1)] }, { coefficient := -1, powers := [(7, 1), (26, 1), (38, 1), (59, 1), (60, 1)] }, { coefficient := -1, powers := [(7, 1), (26, 1), (41, 1), (57, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (26, 1), (48, 1), (54, 1), (59, 1)] }, { coefficient := -1, powers := [(7, 1), (30, 1), (31, 1), (37, 1), (38, 1), (60, 1), (62, 1)] }, { coefficient := -1, powers := [(7, 1), (30, 1), (31, 1), (37, 1), (41, 1), (57, 1), (62, 1)] }, { coefficient := 1, powers := [(7, 1), (30, 1), (31, 1), (37, 1), (48, 1), (54, 1), (62, 1)] }, { coefficient := 1, powers := [(7, 1), (31, 1), (38, 1), (45, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (31, 1), (41, 1), (45, 1), (57, 1)] }, { coefficient := -1, powers := [(7, 1), (31, 1), (45, 1), (48, 1), (54, 1)] }, { coefficient := 1, powers := [(7, 1), (34, 1), (38, 1), (40, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (34, 1), (40, 1), (41, 1), (57, 1)] }, { coefficient := -1, powers := [(7, 1), (34, 1), (40, 1), (48, 1), (54, 1)] }],
  [{ coefficient := 2, powers := [(4, 1), (12, 1), (29, 1), (34, 1), (48, 1), (52, 1)] }, { coefficient := -1, powers := [(5, 1), (7, 1), (29, 1), (34, 1), (52, 1), (60, 1)] }, { coefficient := 2, powers := [(7, 1), (12, 1), (26, 1), (29, 1), (30, 1), (48, 1), (52, 1), (62, 1)] }, { coefficient := -2, powers := [(7, 1), (12, 1), (26, 1), (29, 1), (48, 1), (59, 1)] }, { coefficient := -2, powers := [(7, 1), (12, 1), (29, 1), (30, 1), (31, 1), (37, 1), (48, 1), (62, 1)] }, { coefficient := 2, powers := [(7, 1), (12, 1), (29, 1), (31, 1), (45, 1), (48, 1)] }, { coefficient := 2, powers := [(7, 1), (12, 1), (29, 1), (34, 1), (40, 1), (48, 1)] }, { coefficient := 1, powers := [(14, 1), (26, 1), (52, 1)] }, { coefficient := -1, powers := [(14, 1), (31, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (8, 1), (34, 1), (35, 1), (52, 1)] }, { coefficient := -1, powers := [(4, 1), (17, 1), (29, 1), (34, 1), (52, 1)] }, { coefficient := 1, powers := [(7, 1), (8, 1), (26, 1), (30, 1), (35, 1), (52, 1), (62, 1)] }, { coefficient := -1, powers := [(7, 1), (8, 1), (26, 1), (35, 1), (59, 1)] }, { coefficient := -1, powers := [(7, 1), (8, 1), (30, 1), (31, 1), (35, 1), (37, 1), (62, 1)] }, { coefficient := 1, powers := [(7, 1), (8, 1), (31, 1), (35, 1), (45, 1)] }, { coefficient := 1, powers := [(7, 1), (8, 1), (34, 1), (35, 1), (40, 1)] }, { coefficient := 1, powers := [(7, 1), (17, 1), (26, 1), (29, 1), (30, 1), (52, 1), (62, 1)] }, { coefficient := -1, powers := [(7, 1), (17, 1), (26, 1), (29, 1), (59, 1)] }, { coefficient := -1, powers := [(7, 1), (17, 1), (29, 1), (30, 1), (31, 1), (37, 1), (62, 1)] }, { coefficient := 1, powers := [(7, 1), (17, 1), (29, 1), (31, 1), (45, 1)] }, { coefficient := 1, powers := [(7, 1), (17, 1), (29, 1), (34, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (40, 1)] }, { coefficient := 1, powers := [(4, 1), (12, 1), (18, 1), (23, 1), (34, 1), (52, 1), (57, 1)] }, { coefficient := 1, powers := [(4, 1), (31, 1)] }, { coefficient := 1, powers := [(7, 1), (12, 1), (18, 1), (23, 1), (26, 1), (30, 1), (52, 1), (57, 1), (62, 1)] }, { coefficient := -1, powers := [(7, 1), (12, 1), (18, 1), (23, 1), (26, 1), (57, 1), (59, 1)] }, { coefficient := -1, powers := [(7, 1), (12, 1), (18, 1), (23, 1), (30, 1), (31, 1), (37, 1), (57, 1), (62, 1)] }, { coefficient := 1, powers := [(7, 1), (12, 1), (18, 1), (23, 1), (31, 1), (45, 1), (57, 1)] }, { coefficient := 1, powers := [(7, 1), (12, 1), (18, 1), (23, 1), (34, 1), (40, 1), (57, 1)] }, { coefficient := -1, powers := [(10, 1), (26, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (4, 1), (17, 1), (23, 1), (34, 1), (40, 1), (52, 1), (54, 1)] }, { coefficient := -2, powers := [(4, 1), (9, 1), (12, 1), (29, 1), (34, 1), (48, 1), (52, 1), (62, 1)] }, { coefficient := 1, powers := [(4, 1), (16, 1), (23, 1), (24, 1), (34, 1), (52, 1), (53, 1), (57, 1)] }, { coefficient := -1, powers := [(4, 1), (16, 1), (23, 1), (34, 1), (43, 1), (52, 1), (54, 1)] }, { coefficient := 2, powers := [(4, 1), (17, 1), (18, 1), (23, 1), (34, 1), (40, 1), (52, 1), (54, 1)] }, { coefficient := 1, powers := [(4, 1), (17, 1), (19, 1), (29, 1), (34, 1), (52, 1), (53, 1)] }, { coefficient := 2, powers := [(4, 1), (17, 1), (23, 1), (34, 1), (52, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (7, 1), (9, 1), (29, 1), (34, 1), (52, 1), (60, 1), (62, 1)] }, { coefficient := -2, powers := [(7, 1), (9, 1), (12, 1), (26, 1), (29, 1), (30, 1), (48, 1), (52, 1), (62, 2)] }, { coefficient := 2, powers := [(7, 1), (9, 1), (12, 1), (26, 1), (29, 1), (48, 1), (59, 1), (62, 1)] }, { coefficient := 2, powers := [(7, 1), (9, 1), (12, 1), (29, 1), (30, 1), (31, 1), (37, 1), (48, 1), (62, 2)] }, { coefficient := -2, powers := [(7, 1), (9, 1), (12, 1), (29, 1), (31, 1), (45, 1), (48, 1), (62, 1)] }, { coefficient := -2, powers := [(7, 1), (9, 1), (12, 1), (29, 1), (34, 1), (40, 1), (48, 1), (62, 1)] }, { coefficient := 1, powers := [(7, 1), (16, 1), (23, 1), (24, 1), (26, 1), (30, 1), (52, 1), (53, 1), (57, 1), (62, 1)] }, { coefficient := -1, powers := [(7, 1), (16, 1), (23, 1), (24, 1), (26, 1), (53, 1), (57, 1), (59, 1)] }, { coefficient := -1, powers := [(7, 1), (16, 1), (23, 1), (24, 1), (30, 1), (31, 1), (37, 1), (53, 1), (57, 1), (62, 1)] }, { coefficient := 1, powers := [(7, 1), (16, 1), (23, 1), (24, 1), (31, 1), (45, 1), (53, 1), (57, 1)] }, { coefficient := 1, powers := [(7, 1), (16, 1), (23, 1), (24, 1), (34, 1), (40, 1), (53, 1), (57, 1)] }, { coefficient := -1, powers := [(7, 1), (16, 1), (23, 1), (26, 1), (30, 1), (43, 1), (52, 1), (54, 1), (62, 1)] }, { coefficient := 1, powers := [(7, 1), (16, 1), (23, 1), (26, 1), (43, 1), (54, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (16, 1), (23, 1), (30, 1), (31, 1), (37, 1), (43, 1), (54, 1), (62, 1)] }, { coefficient := -1, powers := [(7, 1), (16, 1), (23, 1), (31, 1), (43, 1), (45, 1), (54, 1)] }, { coefficient := -1, powers := [(7, 1), (16, 1), (23, 1), (34, 1), (40, 1), (43, 1), (54, 1)] }, { coefficient := 1, powers := [(7, 1), (17, 1), (19, 1), (26, 1), (29, 1), (30, 1), (52, 1), (53, 1), (62, 1)] }, { coefficient := -1, powers := [(7, 1), (17, 1), (19, 1), (26, 1), (29, 1), (53, 1), (59, 1)] }, { coefficient := -1, powers := [(7, 1), (17, 1), (19, 1), (29, 1), (30, 1), (31, 1), (37, 1), (53, 1), (62, 1)] }, { coefficient := 1, powers := [(7, 1), (17, 1), (19, 1), (29, 1), (31, 1), (45, 1), (53, 1)] }, { coefficient := 1, powers := [(7, 1), (17, 1), (19, 1), (29, 1), (34, 1), (40, 1), (53, 1)] }, { coefficient := -1, powers := [(7, 1), (21, 1), (59, 1)] }, { coefficient := 1, powers := [(10, 1), (21, 1), (52, 1)] }, { coefficient := 1, powers := [(10, 1), (24, 1), (26, 1), (51, 1), (52, 1), (62, 1)] }, { coefficient := -1, powers := [(10, 1), (24, 1), (31, 1), (37, 1), (51, 1), (62, 1)] }, { coefficient := 1, powers := [(10, 1), (26, 1), (40, 1)] }, { coefficient := 1, powers := [(10, 1), (26, 1), (45, 1)] }, { coefficient := 1, powers := [(10, 1), (31, 1), (37, 1)] }, { coefficient := -1, powers := [(14, 1), (21, 1), (52, 1)] }]
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
    ¬ ∀ index : Fin 38,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component25.SelectedLeafB4_6_1.selectedHasNoCommonZero

end Krenn.Component25.SelectedLeafB4_6_1
