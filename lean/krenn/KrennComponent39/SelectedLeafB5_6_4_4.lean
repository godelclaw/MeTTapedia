import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component39.SelectedLeafB5_6_4_4

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "972cb4e2288af49fcee8922de621fd7bb7eca880cd8c88797bcb1903a9b0c9f4"
def certificateSHA256 : String := "58eae2528ba7f8fde1ab4eb3ae30712bdcbc7372634e60ac5b616687b4417363"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 50 → Fin 673 := ![
  23,
  181,
  184,
  187,
  190,
  191,
  192,
  193,
  195,
  250,
  300,
  301,
  302,
  303,
  304,
  305,
  313,
  316,
  319,
  321,
  322,
  343,
  345,
  382,
  396,
  412,
  416,
  419,
  425,
  434,
  439,
  440,
  452,
  463,
  476,
  563,
  566,
  603,
  645,
  659,
  660,
  661,
  662,
  663,
  664,
  666,
  668,
  669,
  671,
  672
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 50 → SparsePoly (Fin 67) := ![
  [{ coefficient := 1, powers := [(17, 1), (20, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (24, 1)] }, { coefficient := 1, powers := [(16, 1), (18, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (45, 1)] }, { coefficient := 1, powers := [(17, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (18, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (45, 1)] }, { coefficient := -1, powers := [(27, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (54, 1)] }, { coefficient := 1, powers := [(28, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (42, 1)] }, { coefficient := 1, powers := [(26, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (53, 1)] }, { coefficient := 1, powers := [(28, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(26, 1), (52, 1)] }, { coefficient := -1, powers := [(27, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (23, 1), (44, 1)] }, { coefficient := 1, powers := [(16, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1)] }, { coefficient := 1, powers := [(18, 1), (42, 1)] }, { coefficient := 1, powers := [(23, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (42, 1)] }, { coefficient := 1, powers := [(23, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (49, 1)] }, { coefficient := 1, powers := [(18, 1), (49, 1)] }, { coefficient := 1, powers := [(23, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (54, 1)] }, { coefficient := 1, powers := [(18, 1), (54, 1)] }, { coefficient := 1, powers := [(24, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (44, 1)] }, { coefficient := 1, powers := [(4, 1), (33, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (51, 1)] }, { coefficient := 1, powers := [(7, 1), (30, 1)] }, { coefficient := 1, powers := [(10, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (44, 1)] }, { coefficient := 1, powers := [(12, 1), (56, 1)] }, { coefficient := 1, powers := [(16, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (45, 1)] }, { coefficient := 1, powers := [(17, 1), (39, 1)] }, { coefficient := 1, powers := [(17, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1), (51, 1)] }, { coefficient := 1, powers := [(18, 1), (42, 1), (51, 1)] }, { coefficient := 1, powers := [(42, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1), (49, 1)] }, { coefficient := 1, powers := [(23, 1), (44, 1), (49, 1)] }, { coefficient := 1, powers := [(49, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1), (54, 1)] }, { coefficient := 1, powers := [(24, 1), (44, 1), (49, 1)] }, { coefficient := 1, powers := [(54, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (42, 1), (52, 1)] }, { coefficient := 1, powers := [(12, 1), (27, 1), (42, 1)] }, { coefficient := 1, powers := [(17, 1), (21, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (44, 1), (49, 1)] }, { coefficient := 1, powers := [(12, 1), (26, 1), (44, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (18, 1), (56, 1)] }, { coefficient := 1, powers := [(12, 1)] }, { coefficient := 1, powers := [(16, 1), (18, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (23, 1), (39, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1), (44, 1)] }, { coefficient := 1, powers := [(16, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (52, 1)] }, { coefficient := 1, powers := [(18, 1), (49, 1), (56, 1)] }, { coefficient := 1, powers := [(18, 1), (52, 1)] }, { coefficient := 1, powers := [(49, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (44, 1)] }, { coefficient := 1, powers := [(16, 1), (26, 1), (39, 1)] }, { coefficient := 1, powers := [(16, 1), (26, 1), (44, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (47, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1)] }, { coefficient := 1, powers := [(16, 1), (26, 1), (47, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1)] }, { coefficient := 1, powers := [(12, 1), (28, 1)] }, { coefficient := 1, powers := [(16, 1), (21, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (60, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (45, 1)] }, { coefficient := 1, powers := [(12, 1), (57, 1)] }, { coefficient := 1, powers := [(17, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (39, 1)] }, { coefficient := 1, powers := [(16, 1), (44, 1)] }, { coefficient := 1, powers := [(16, 1), (51, 1)] }, { coefficient := 1, powers := [(16, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (54, 1)] }, { coefficient := 1, powers := [(28, 1), (40, 1)] }, { coefficient := 1, powers := [(28, 1), (46, 1), (49, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1), (53, 1)] }, { coefficient := 1, powers := [(18, 1), (42, 1), (53, 1)] }, { coefficient := 1, powers := [(18, 1), (57, 1)] }, { coefficient := 1, powers := [(24, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1), (54, 1)] }, { coefficient := 1, powers := [(24, 1), (45, 1), (49, 1)] }, { coefficient := 1, powers := [(42, 1), (54, 1)] }, { coefficient := 1, powers := [(49, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (38, 1), (56, 1)] }, { coefficient := 1, powers := [(1, 1), (50, 1)] }, { coefficient := 1, powers := [(7, 1), (33, 1), (38, 1)] }, { coefficient := 1, powers := [(14, 1), (25, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (25, 1), (45, 1)] }, { coefficient := 1, powers := [(17, 1), (20, 1), (51, 1)] }, { coefficient := 1, powers := [(17, 1), (25, 1), (39, 1)] }, { coefficient := 1, powers := [(17, 1), (30, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (42, 1), (53, 1)] }, { coefficient := 1, powers := [(22, 1), (57, 1)] }, { coefficient := 1, powers := [(28, 1), (47, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (51, 1)] }, { coefficient := 1, powers := [(20, 1), (56, 1)] }, { coefficient := 1, powers := [(25, 1), (39, 1)] }, { coefficient := 1, powers := [(25, 1), (44, 1)] }, { coefficient := 1, powers := [(30, 1), (36, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (37, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (47, 1), (54, 1)] }, { coefficient := 1, powers := [(19, 1), (42, 1), (54, 1)] }, { coefficient := 1, powers := [(19, 1), (49, 1), (57, 1)] }, { coefficient := 1, powers := [(24, 1), (40, 1), (42, 1)] }, { coefficient := 1, powers := [(24, 1), (47, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (36, 1), (59, 1)] }, { coefficient := 1, powers := [(1, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(1, 1), (44, 1), (51, 1)] }, { coefficient := 1, powers := [(4, 1), (25, 1), (59, 1)] }, { coefficient := 1, powers := [(4, 1), (30, 1), (56, 1)] }, { coefficient := 1, powers := [(4, 1), (33, 1), (51, 1)] }, { coefficient := 1, powers := [(7, 1), (20, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (30, 1), (44, 1)] }, { coefficient := 1, powers := [(7, 1), (33, 1), (39, 1)] }, { coefficient := 1, powers := [(10, 1), (20, 1), (56, 1)] }, { coefficient := 1, powers := [(10, 1), (25, 1), (44, 1)] }, { coefficient := 1, powers := [(10, 1), (33, 1), (36, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1), (51, 1)] }, { coefficient := 1, powers := [(14, 1), (25, 1), (39, 1)] }, { coefficient := 1, powers := [(14, 1), (30, 1), (36, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (37, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (47, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (28, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (22, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1), (47, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (40, 1)] }, { coefficient := 1, powers := [(12, 1), (22, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1), (28, 1), (47, 1)] }, { coefficient := 1, powers := [(12, 1), (34, 1), (37, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (54, 1)] }, { coefficient := 1, powers := [(17, 1), (28, 1), (40, 1)] }, { coefficient := 1, powers := [(17, 1), (31, 1), (37, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (61, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(38, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(40, 1)] }],
  [{ coefficient := 1, powers := [(56, 1)] }],
  [{ coefficient := 1, powers := [(57, 1)] }],
  [{ coefficient := 1, powers := [(25, 1)] }],
  [{ coefficient := 1, powers := [(28, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 50 → SparsePoly (Fin 67) := ![
  [{ coefficient := -2, powers := [(7, 1), (22, 1), (54, 1), (59, 1)] }, { coefficient := 2, powers := [(14, 1), (22, 1), (51, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(22, 1), (45, 1)] }, { coefficient := -2, powers := [(26, 1), (47, 1), (61, 1)] }, { coefficient := 2, powers := [(27, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (19, 1), (21, 1), (24, 1), (61, 1), (62, 1)] }],
  [{ coefficient := -2, powers := [(22, 1), (42, 1), (54, 1), (61, 1)] }, { coefficient := -2, powers := [(24, 1), (26, 1), (47, 1), (52, 1), (61, 1)] }, { coefficient := 2, powers := [(24, 1), (27, 1), (47, 1), (49, 1), (61, 1)] }, { coefficient := 2, powers := [(24, 1), (27, 1), (47, 1), (52, 1)] }, { coefficient := -2, powers := [(26, 1), (47, 1), (51, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (12, 1), (19, 1), (24, 1), (61, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(16, 1), (47, 1)] }],
  [{ coefficient := -1, powers := [(16, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (42, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (16, 1), (19, 1), (24, 1), (42, 1), (61, 1), (62, 1)] }],
  [{ coefficient := -2, powers := [(24, 1), (26, 1), (47, 1), (61, 1)] }, { coefficient := 2, powers := [(24, 1), (27, 1), (47, 1)] }],
  [{ coefficient := 2, powers := [(16, 1), (22, 1), (54, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (24, 1), (44, 1), (49, 1), (61, 1)] }],
  [{ coefficient := -2, powers := [(16, 1), (24, 1), (27, 1), (47, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (19, 1), (42, 1), (51, 1), (61, 1)] }, { coefficient := 2, powers := [(2, 1), (44, 1), (47, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1), (45, 1)] }, { coefficient := 2, powers := [(16, 1), (26, 1), (47, 1), (61, 1)] }],
  [{ coefficient := -2, powers := [(17, 1), (22, 1), (51, 1), (54, 1)] }],
  [{ coefficient := -2, powers := [(17, 1), (22, 1), (44, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (19, 1), (24, 1), (26, 1), (42, 1), (61, 1), (62, 1)] }, { coefficient := 2, powers := [(23, 1), (24, 1), (26, 1), (47, 1), (61, 1)] }, { coefficient := -2, powers := [(23, 1), (24, 1), (27, 1), (47, 1)] }],
  [{ coefficient := -2, powers := [(7, 1), (22, 1), (33, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (19, 1), (49, 1), (53, 1), (61, 1)] }, { coefficient := -1, powers := [(2, 1), (19, 1), (54, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (24, 1), (47, 1), (61, 1)] }],
  [{ coefficient := -2, powers := [(2, 1), (47, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (19, 1), (24, 1), (61, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (19, 1), (24, 1), (42, 1), (61, 1), (62, 1)] }],
  [{ coefficient := 2, powers := [(24, 1), (26, 1), (47, 1), (61, 1)] }, { coefficient := -2, powers := [(24, 1), (27, 1), (47, 1)] }],
  [{ coefficient := -2, powers := [(26, 1), (47, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (19, 1), (42, 1), (53, 1), (61, 1)] }],
  [{ coefficient := -2, powers := [(18, 1), (47, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(54, 1)] }],
  [{ coefficient := 1, powers := [(47, 1)] }],
  [{ coefficient := 1, powers := [(22, 1)] }],
  [{ coefficient := 2, powers := [(18, 1), (26, 1), (47, 1), (54, 1)] }, { coefficient := 2, powers := [(23, 1), (26, 1), (47, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(17, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (19, 1), (49, 1), (51, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (19, 1), (52, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(16, 1), (22, 1)] }],
  [{ coefficient := 2, powers := [(16, 1), (22, 1), (45, 1), (54, 1), (63, 1)] }, { coefficient := 2, powers := [(17, 1), (22, 1), (51, 1), (54, 1), (63, 1)] }],
  [{ coefficient := 2, powers := [(10, 1), (22, 1), (54, 1)] }, { coefficient := -2, powers := [(14, 1), (22, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(12, 1)] }],
  [{ coefficient := -2, powers := [(10, 1), (17, 1), (22, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (61, 1)] }],
  [{ coefficient := 2, powers := [(17, 1), (22, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(2, 1), (37, 1), (60, 1)] }, { coefficient := -1, powers := [(2, 1), (47, 1), (54, 1)] }, { coefficient := -2, powers := [(16, 1), (22, 1), (42, 1), (54, 1)] }, { coefficient := 2, powers := [(16, 1), (24, 1), (27, 1), (47, 1), (49, 1)] }, { coefficient := -2, powers := [(16, 1), (26, 1), (47, 1), (54, 1)] }],
  [{ coefficient := -2, powers := [(16, 1), (22, 1), (38, 1), (45, 1), (54, 1), (56, 1), (63, 1)] }, { coefficient := -2, powers := [(16, 1), (22, 1), (45, 1), (50, 1), (54, 1), (63, 1)] }, { coefficient := -2, powers := [(17, 1), (22, 1), (36, 1), (54, 1), (59, 1)] }, { coefficient := -2, powers := [(17, 1), (22, 1), (38, 1), (51, 1), (54, 1), (56, 1), (63, 1)] }, { coefficient := -2, powers := [(17, 1), (22, 1), (39, 1), (54, 1), (56, 1)] }, { coefficient := 2, powers := [(17, 1), (22, 1), (44, 1), (51, 1), (54, 1)] }, { coefficient := -2, powers := [(17, 1), (22, 1), (50, 1), (51, 1), (54, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (19, 1), (24, 1), (42, 1), (44, 1), (49, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (19, 1), (24, 1), (42, 1), (52, 1), (61, 1)] }],
  [{ coefficient := -2, powers := [(7, 1), (16, 1), (22, 1), (33, 1), (45, 1), (54, 1)] }, { coefficient := -2, powers := [(7, 1), (17, 1), (22, 1), (33, 1), (51, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (24, 1), (42, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (12, 1), (19, 1), (24, 1), (26, 1), (42, 1), (61, 1), (62, 1)] }, { coefficient := 1, powers := [(2, 1), (18, 1), (19, 1), (42, 1), (49, 1), (53, 1), (61, 1)] }, { coefficient := -2, powers := [(4, 1), (17, 1), (22, 1), (30, 1), (54, 1)] }, { coefficient := -2, powers := [(12, 1), (18, 1), (24, 1), (26, 1), (47, 1), (61, 1)] }, { coefficient := 2, powers := [(12, 1), (18, 1), (24, 1), (27, 1), (47, 1)] }, { coefficient := -2, powers := [(12, 1), (23, 1), (24, 1), (26, 1), (47, 1), (61, 1)] }, { coefficient := 2, powers := [(12, 1), (23, 1), (24, 1), (27, 1), (47, 1)] }, { coefficient := -2, powers := [(16, 1), (18, 1), (26, 1), (47, 1), (54, 1)] }, { coefficient := -2, powers := [(16, 1), (23, 1), (26, 1), (47, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (2, 1), (40, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (18, 1), (19, 1), (49, 1), (51, 1), (61, 1)] }, { coefficient := -1, powers := [(2, 1), (18, 1), (19, 1), (52, 1), (61, 1)] }, { coefficient := -1, powers := [(2, 1), (19, 1), (49, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (40, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1)] }, { coefficient := -1, powers := [(12, 1), (22, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1), (49, 1)] }],
  [{ coefficient := -2, powers := [(4, 1), (17, 1), (22, 1), (54, 1), (59, 1)] }, { coefficient := -2, powers := [(10, 1), (16, 1), (22, 1), (45, 1), (54, 1)] }, { coefficient := 2, powers := [(10, 1), (17, 1), (22, 1), (44, 1), (54, 1)] }, { coefficient := -2, powers := [(14, 1), (16, 1), (22, 1), (38, 1), (45, 1), (54, 1), (63, 1)] }, { coefficient := 2, powers := [(14, 1), (16, 1), (22, 1), (45, 1), (54, 1)] }, { coefficient := -2, powers := [(14, 1), (17, 1), (22, 1), (38, 1), (51, 1), (54, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (60, 1)] }, { coefficient := 1, powers := [(12, 1), (42, 1), (46, 1)] }, { coefficient := -1, powers := [(12, 1), (47, 1)] }, { coefficient := 1, powers := [(16, 1), (47, 1), (49, 1)] }, { coefficient := -1, powers := [(17, 1), (46, 1), (49, 1)] }]
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
    ¬ ∀ index : Fin 50,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component39.SelectedLeafB5_6_4_4.selectedHasNoCommonZero

end Krenn.Component39.SelectedLeafB5_6_4_4
