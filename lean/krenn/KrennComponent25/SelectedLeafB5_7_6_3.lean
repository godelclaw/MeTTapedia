import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component25.SelectedLeafB5_7_6_3

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "63cac9b0046ee83f19af5e9744380c0131241d38620f83381bb49027d78c87cc"
def certificateSHA256 : String := "7a0e38b1925e759a7e2813da6ff1d03c3856a38ee9b7a16285a7f5baee3126da"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 35 → Fin 668 := ![
  3,
  6,
  11,
  14,
  21,
  149,
  150,
  151,
  169,
  170,
  173,
  267,
  293,
  312,
  352,
  353,
  363,
  406,
  430,
  435,
  439,
  450,
  505,
  585,
  602,
  604,
  605,
  654,
  655,
  656,
  657,
  662,
  664,
  665,
  667
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 35 → SparsePoly (Fin 70) := ![
  [{ coefficient := 1, powers := [(10, 1), (29, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (35, 1)] }, { coefficient := 1, powers := [(10, 1), (27, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (32, 1)] }, { coefficient := 1, powers := [(14, 1), (22, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (57, 1)] }, { coefficient := 1, powers := [(29, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (43, 1)] }, { coefficient := 1, powers := [(27, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (40, 1)] }, { coefficient := 1, powers := [(29, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (24, 1), (48, 1)] }, { coefficient := 1, powers := [(17, 1), (19, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (48, 1)] }, { coefficient := 1, powers := [(19, 1), (43, 1)] }, { coefficient := 1, powers := [(24, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (57, 1)] }, { coefficient := 1, powers := [(29, 1), (48, 1)] }, { coefficient := 1, powers := [(35, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (29, 1), (59, 1)] }, { coefficient := 1, powers := [(10, 1), (29, 1), (45, 1)] }, { coefficient := 1, powers := [(14, 1), (29, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (29, 1), (60, 1)] }, { coefficient := 1, powers := [(4, 1), (32, 1), (57, 1)] }, { coefficient := 1, powers := [(4, 1), (35, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (23, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (32, 1), (48, 1)] }, { coefficient := 1, powers := [(7, 1), (35, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (24, 1), (46, 1)] }, { coefficient := 1, powers := [(17, 1), (24, 1), (40, 1)] }, { coefficient := 1, powers := [(17, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (48, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1), (48, 1)] }, { coefficient := 1, powers := [(17, 1), (23, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1)] }, { coefficient := 1, powers := [(12, 1), (29, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (60, 1)] }, { coefficient := 1, powers := [(12, 1), (48, 1)] }, { coefficient := 1, powers := [(17, 1), (19, 1), (53, 1)] }, { coefficient := 1, powers := [(17, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (54, 1)] }, { coefficient := 1, powers := [(29, 1), (41, 1)] }, { coefficient := 1, powers := [(29, 1), (47, 1), (50, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (24, 1), (59, 1)] }, { coefficient := 1, powers := [(10, 1), (24, 1), (45, 1)] }, { coefficient := 1, powers := [(14, 1), (24, 1), (40, 1)] }, { coefficient := 1, powers := [(14, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (40, 1), (55, 1)] }, { coefficient := 1, powers := [(1, 1), (44, 1)] }, { coefficient := 1, powers := [(4, 1), (31, 1), (55, 1)] }, { coefficient := 1, powers := [(10, 1), (21, 1), (55, 1)] }, { coefficient := 1, powers := [(10, 1), (25, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (45, 1)] }, { coefficient := 1, powers := [(4, 1), (25, 1), (59, 1)] }, { coefficient := 1, powers := [(4, 1), (34, 1)] }, { coefficient := 1, powers := [(10, 1), (25, 1), (45, 1)] }, { coefficient := 1, powers := [(14, 1), (21, 1)] }, { coefficient := 1, powers := [(14, 1), (25, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (59, 1)] }, { coefficient := 1, powers := [(10, 1), (45, 1)] }, { coefficient := 1, powers := [(10, 1), (56, 1)] }, { coefficient := 1, powers := [(14, 1), (40, 1)] }, { coefficient := 1, powers := [(14, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (52, 1)] }, { coefficient := 1, powers := [(21, 1), (56, 1)] }, { coefficient := 1, powers := [(26, 1), (40, 1)] }, { coefficient := 1, powers := [(26, 1), (45, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (37, 1), (59, 1)] }, { coefficient := 1, powers := [(1, 1), (40, 1), (56, 1)] }, { coefficient := 1, powers := [(1, 1), (45, 1), (52, 1)] }, { coefficient := 1, powers := [(4, 1), (26, 1), (59, 1)] }, { coefficient := 1, powers := [(4, 1), (31, 1), (56, 1)] }, { coefficient := 1, powers := [(4, 1), (34, 1), (52, 1)] }, { coefficient := 1, powers := [(7, 1), (21, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (31, 1), (45, 1)] }, { coefficient := 1, powers := [(7, 1), (34, 1), (40, 1)] }, { coefficient := 1, powers := [(10, 1), (21, 1), (56, 1)] }, { coefficient := 1, powers := [(10, 1), (26, 1), (45, 1)] }, { coefficient := 1, powers := [(10, 1), (34, 1), (37, 1)] }, { coefficient := 1, powers := [(14, 1), (21, 1), (52, 1)] }, { coefficient := 1, powers := [(14, 1), (26, 1), (40, 1)] }, { coefficient := 1, powers := [(14, 1), (31, 1), (37, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (41, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (48, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (23, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (48, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(12, 1), (23, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1), (29, 1), (48, 1)] }, { coefficient := 1, powers := [(12, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(17, 1), (23, 1), (54, 1)] }, { coefficient := 1, powers := [(17, 1), (29, 1), (41, 1)] }, { coefficient := 1, powers := [(17, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (61, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1)] }],
  [{ coefficient := 1, powers := [(55, 1), (66, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(57, 1)] }],
  [{ coefficient := 1, powers := [(24, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (69, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 35 → SparsePoly (Fin 70) := ![
  [{ coefficient := -1, powers := [(21, 1), (52, 1), (69, 1)] }, { coefficient := -1, powers := [(21, 1), (55, 1), (56, 1), (66, 1), (69, 1)] }, { coefficient := -1, powers := [(21, 1), (56, 1), (69, 1)] }, { coefficient := 1, powers := [(25, 1), (29, 1), (52, 1), (56, 1), (69, 2)] }, { coefficient := -1, powers := [(25, 1), (44, 1), (56, 1), (66, 1), (69, 1)] }, { coefficient := -1, powers := [(25, 1), (52, 1), (56, 1), (69, 1)] }, { coefficient := -1, powers := [(26, 1), (40, 1), (69, 1)] }, { coefficient := -1, powers := [(26, 1), (45, 1), (69, 1)] }, { coefficient := -1, powers := [(31, 1), (37, 1), (69, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (27, 1), (31, 1), (38, 1), (45, 1), (54, 1), (69, 1)] }, { coefficient := 1, powers := [(2, 1), (27, 1), (34, 1), (38, 1), (45, 1), (54, 1), (69, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (22, 1), (31, 1), (45, 1), (48, 1)] }, { coefficient := -1, powers := [(8, 1), (22, 1), (34, 1), (45, 1), (48, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (22, 1), (31, 1), (45, 1), (48, 1)] }, { coefficient := 1, powers := [(7, 1), (22, 1), (34, 1), (45, 1), (48, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (17, 1), (31, 1), (45, 1), (50, 1)] }, { coefficient := 1, powers := [(7, 1), (17, 1), (34, 1), (45, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (31, 1), (38, 1), (45, 1), (54, 1), (69, 1)] }, { coefficient := -1, powers := [(2, 1), (34, 1), (38, 1), (45, 1), (54, 1), (69, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (29, 1), (31, 1), (38, 1), (45, 1), (69, 1)] }, { coefficient := -1, powers := [(2, 1), (29, 1), (34, 1), (38, 1), (45, 1), (69, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (31, 1), (45, 1), (48, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (45, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (7, 1), (19, 1), (31, 1), (45, 1), (54, 1), (61, 1), (69, 1)] }, { coefficient := -1, powers := [(2, 1), (7, 1), (19, 1), (34, 1), (45, 1), (54, 1), (61, 1), (69, 1)] }, { coefficient := 2, powers := [(7, 1), (12, 1), (19, 1), (29, 1), (31, 1), (45, 1), (61, 1), (69, 1)] }, { coefficient := -2, powers := [(7, 1), (12, 1), (19, 1), (29, 1), (34, 1), (45, 1), (61, 1), (69, 1)] }, { coefficient := 1, powers := [(7, 1), (16, 1), (23, 1), (31, 1), (45, 1), (54, 1), (69, 1)] }, { coefficient := -1, powers := [(7, 1), (16, 1), (23, 1), (34, 1), (45, 1), (54, 1), (69, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (16, 1), (31, 1), (45, 1), (54, 1)] }, { coefficient := 1, powers := [(7, 1), (16, 1), (34, 1), (45, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (34, 1), (69, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (29, 1), (31, 1), (45, 1), (53, 1)] }, { coefficient := 1, powers := [(7, 1), (29, 1), (34, 1), (45, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (7, 1), (31, 1), (45, 1), (54, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (7, 1), (34, 1), (45, 1), (54, 1), (61, 1)] }, { coefficient := -2, powers := [(7, 1), (12, 1), (29, 1), (31, 1), (45, 1), (61, 1)] }, { coefficient := 2, powers := [(7, 1), (12, 1), (29, 1), (34, 1), (45, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (12, 1), (31, 1), (45, 1)] }, { coefficient := -1, powers := [(7, 1), (12, 1), (34, 1), (45, 1)] }],
  [{ coefficient := -1, powers := [(21, 1), (69, 1)] }, { coefficient := -1, powers := [(25, 1), (52, 1), (69, 1)] }, { coefficient := 1, powers := [(26, 1), (69, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (31, 1), (38, 1), (45, 1), (69, 1)] }, { coefficient := 1, powers := [(2, 1), (34, 1), (38, 1), (45, 1), (69, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (31, 1), (45, 1)] }, { coefficient := -1, powers := [(8, 1), (34, 1), (45, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (23, 1), (31, 1), (45, 1), (54, 1)] }, { coefficient := 1, powers := [(7, 1), (23, 1), (34, 1), (45, 1), (54, 1)] }, { coefficient := -1, powers := [(7, 1), (29, 1), (31, 1), (41, 1), (45, 1)] }, { coefficient := 1, powers := [(7, 1), (29, 1), (34, 1), (41, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (31, 1), (45, 1), (54, 1)] }, { coefficient := -1, powers := [(7, 1), (34, 1), (45, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (31, 1), (45, 1), (48, 1)] }, { coefficient := -1, powers := [(7, 1), (34, 1), (45, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (29, 1), (31, 1), (45, 1)] }, { coefficient := -1, powers := [(7, 1), (29, 1), (34, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (17, 1), (31, 1), (45, 1)] }, { coefficient := -1, powers := [(7, 1), (17, 1), (34, 1), (45, 1)] }],
  [{ coefficient := -1, powers := [(21, 1), (29, 1), (52, 1), (69, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(56, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (52, 1), (69, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (29, 1), (69, 1)] }, { coefficient := -1, powers := [(26, 1), (29, 1), (69, 1)] }, { coefficient := 1, powers := [(26, 1)] }],
  [{ coefficient := 1, powers := [(10, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(7, 1), (31, 1), (45, 1)] }, { coefficient := 1, powers := [(7, 1), (34, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (7, 1), (31, 1), (45, 1), (48, 1), (54, 1)] }, { coefficient := -1, powers := [(2, 1), (7, 1), (34, 1), (45, 1), (48, 1), (54, 1)] }, { coefficient := 2, powers := [(7, 1), (12, 1), (29, 1), (31, 1), (45, 1), (48, 1)] }, { coefficient := -2, powers := [(7, 1), (12, 1), (29, 1), (34, 1), (45, 1), (48, 1)] }],
  [{ coefficient := -1, powers := [(29, 1), (45, 1), (52, 1), (69, 1)] }, { coefficient := 1, powers := [(37, 1), (59, 1)] }, { coefficient := -1, powers := [(40, 1), (55, 1), (56, 1), (66, 1)] }, { coefficient := 1, powers := [(40, 1), (56, 1)] }, { coefficient := -1, powers := [(44, 1), (56, 1), (66, 1)] }, { coefficient := 1, powers := [(45, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (31, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (4, 1), (31, 1), (32, 1), (38, 1), (45, 1), (69, 1)] }, { coefficient := -1, powers := [(2, 1), (4, 1), (32, 1), (34, 1), (38, 1), (45, 1), (69, 1)] }, { coefficient := -1, powers := [(2, 1), (7, 1), (19, 1), (22, 1), (31, 1), (45, 1), (54, 1), (61, 1), (69, 1)] }, { coefficient := 1, powers := [(2, 1), (7, 1), (19, 1), (22, 1), (34, 1), (45, 1), (54, 1), (61, 1), (69, 1)] }, { coefficient := 1, powers := [(2, 1), (7, 1), (31, 1), (41, 1), (45, 1)] }, { coefficient := -1, powers := [(2, 1), (7, 1), (34, 1), (41, 1), (45, 1)] }, { coefficient := 1, powers := [(5, 1), (7, 1), (31, 1), (32, 1), (45, 1)] }, { coefficient := -1, powers := [(5, 1), (7, 1), (32, 1), (34, 1), (45, 1)] }, { coefficient := -2, powers := [(7, 1), (12, 1), (19, 1), (22, 1), (29, 1), (31, 1), (45, 1), (61, 1), (69, 1)] }, { coefficient := 2, powers := [(7, 1), (12, 1), (19, 1), (22, 1), (29, 1), (34, 1), (45, 1), (61, 1), (69, 1)] }, { coefficient := -1, powers := [(7, 1), (16, 1), (22, 1), (23, 1), (31, 1), (45, 1), (54, 1), (69, 1)] }, { coefficient := 1, powers := [(7, 1), (16, 1), (22, 1), (23, 1), (34, 1), (45, 1), (54, 1), (69, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (7, 1), (31, 1), (45, 1), (48, 1), (54, 1), (61, 1)] }, { coefficient := -1, powers := [(2, 1), (7, 1), (34, 1), (45, 1), (48, 1), (54, 1), (61, 1)] }, { coefficient := 1, powers := [(4, 1), (21, 1), (29, 1), (52, 1), (59, 1), (69, 1)] }, { coefficient := -1, powers := [(4, 1), (31, 1), (37, 1), (59, 1)] }, { coefficient := 2, powers := [(7, 1), (12, 1), (29, 1), (31, 1), (45, 1), (48, 1), (61, 1)] }, { coefficient := -2, powers := [(7, 1), (12, 1), (29, 1), (34, 1), (45, 1), (48, 1), (61, 1)] }, { coefficient := 1, powers := [(7, 1), (16, 1), (23, 1), (31, 1), (45, 1), (46, 1), (54, 1)] }, { coefficient := -1, powers := [(7, 1), (16, 1), (23, 1), (34, 1), (45, 1), (46, 1), (54, 1)] }, { coefficient := 1, powers := [(7, 1), (16, 1), (29, 1), (31, 1), (41, 1), (45, 1), (46, 1)] }, { coefficient := 1, powers := [(7, 1), (16, 1), (29, 1), (31, 1), (45, 1), (48, 1), (53, 1)] }, { coefficient := -1, powers := [(7, 1), (16, 1), (29, 1), (34, 1), (41, 1), (45, 1), (46, 1)] }, { coefficient := -1, powers := [(7, 1), (16, 1), (29, 1), (34, 1), (45, 1), (48, 1), (53, 1)] }, { coefficient := 1, powers := [(7, 1), (17, 1), (23, 1), (31, 1), (40, 1), (45, 1), (54, 1)] }, { coefficient := -1, powers := [(7, 1), (17, 1), (23, 1), (34, 1), (40, 1), (45, 1), (54, 1)] }, { coefficient := 1, powers := [(7, 1), (17, 1), (29, 1), (31, 1), (40, 1), (41, 1), (45, 1)] }, { coefficient := -1, powers := [(7, 1), (17, 1), (29, 1), (34, 1), (40, 1), (41, 1), (45, 1)] }, { coefficient := 1, powers := [(10, 1), (21, 1), (29, 1), (45, 1), (52, 1), (69, 1)] }, { coefficient := -1, powers := [(10, 1), (31, 1), (37, 1), (45, 1)] }, { coefficient := 1, powers := [(14, 1), (21, 1), (29, 1), (40, 1), (52, 1), (69, 1)] }, { coefficient := -1, powers := [(14, 1), (31, 1), (37, 1), (40, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (7, 1), (19, 1), (31, 1), (43, 1), (45, 1), (54, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (7, 1), (19, 1), (34, 1), (43, 1), (45, 1), (54, 1), (61, 1)] }, { coefficient := -1, powers := [(2, 1), (7, 1), (31, 1), (38, 1), (45, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (7, 1), (34, 1), (38, 1), (45, 1), (60, 1)] }, { coefficient := -1, powers := [(4, 1), (34, 1), (52, 1)] }, { coefficient := -2, powers := [(7, 1), (12, 1), (19, 1), (29, 1), (31, 1), (43, 1), (45, 1), (61, 1)] }, { coefficient := 2, powers := [(7, 1), (12, 1), (19, 1), (29, 1), (34, 1), (43, 1), (45, 1), (61, 1)] }, { coefficient := -1, powers := [(7, 1), (16, 1), (23, 1), (31, 1), (43, 1), (45, 1), (54, 1)] }, { coefficient := 1, powers := [(7, 1), (16, 1), (23, 1), (34, 1), (43, 1), (45, 1), (54, 1)] }, { coefficient := -1, powers := [(7, 1), (21, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (26, 1), (59, 1)] }, { coefficient := -1, powers := [(7, 1), (34, 1), (40, 1)] }, { coefficient := -1, powers := [(7, 1), (34, 1), (45, 1)] }, { coefficient := 1, powers := [(10, 1), (21, 1), (52, 1)] }, { coefficient := 1, powers := [(10, 1), (21, 1), (55, 1), (56, 1), (66, 1)] }, { coefficient := -1, powers := [(10, 1), (25, 1), (29, 1), (52, 1), (56, 1), (69, 1)] }, { coefficient := 1, powers := [(10, 1), (25, 1), (44, 1), (56, 1), (66, 1)] }, { coefficient := 1, powers := [(10, 1), (26, 1), (40, 1)] }, { coefficient := 1, powers := [(10, 1), (26, 1), (45, 1)] }, { coefficient := 1, powers := [(10, 1), (26, 1), (56, 1)] }, { coefficient := 1, powers := [(10, 1), (31, 1), (37, 1)] }, { coefficient := -1, powers := [(14, 1), (21, 1), (52, 1)] }, { coefficient := 1, powers := [(14, 1), (26, 1), (52, 1)] }]
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
    ¬ ∀ index : Fin 35,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component25.SelectedLeafB5_7_6_3.selectedHasNoCommonZero

end Krenn.Component25.SelectedLeafB5_7_6_3
