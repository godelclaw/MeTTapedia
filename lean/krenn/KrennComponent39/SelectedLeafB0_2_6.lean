import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component39.SelectedLeafB0_2_6

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "ade6509b6160b686537bb55438b554b647b9f964e0bd937600a086e8d15ce831"
def certificateSHA256 : String := "cd4ff1f2da47e3a935296d40a6032f244ad876e96b9f2fe68ced8ece8fa7885d"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 46 → Fin 670 := ![
  10,
  76,
  180,
  181,
  187,
  191,
  192,
  250,
  254,
  276,
  303,
  304,
  305,
  322,
  345,
  425,
  429,
  433,
  434,
  439,
  440,
  458,
  467,
  477,
  482,
  495,
  502,
  566,
  580,
  602,
  603,
  607,
  618,
  620,
  621,
  623,
  637,
  644,
  659,
  660,
  661,
  662,
  663,
  666,
  667,
  669
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 46 → SparsePoly (Fin 64) := ![
  [{ coefficient := 1, powers := [(5, 1), (33, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (30, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (23, 1)] }, { coefficient := 1, powers := [(16, 1), (18, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (24, 1)] }, { coefficient := 1, powers := [(16, 1), (18, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (18, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (54, 1)] }, { coefficient := 1, powers := [(28, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (42, 1)] }, { coefficient := 1, powers := [(26, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (23, 1), (44, 1)] }, { coefficient := 1, powers := [(16, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (24, 1), (44, 1)] }, { coefficient := 1, powers := [(16, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (23, 1), (42, 1)] }, { coefficient := 1, powers := [(17, 1), (18, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (54, 1)] }, { coefficient := 1, powers := [(18, 1), (54, 1)] }, { coefficient := 1, powers := [(24, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (44, 1)] }, { coefficient := 1, powers := [(4, 1), (33, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (51, 1)] }, { coefficient := 1, powers := [(7, 1), (30, 1)] }, { coefficient := 1, powers := [(10, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1), (54, 1)] }, { coefficient := 1, powers := [(24, 1), (44, 1), (49, 1)] }, { coefficient := 1, powers := [(54, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (44, 1), (49, 1)] }, { coefficient := 1, powers := [(12, 1), (26, 1), (44, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1)] }, { coefficient := 1, powers := [(12, 1), (28, 1)] }, { coefficient := 1, powers := [(16, 1), (21, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (59, 1)] }, { coefficient := 1, powers := [(16, 1), (19, 1), (51, 1)] }, { coefficient := 1, powers := [(16, 1), (19, 1), (56, 1)] }, { coefficient := 1, powers := [(16, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (59, 1)] }, { coefficient := 1, powers := [(16, 1), (24, 1), (39, 1)] }, { coefficient := 1, powers := [(16, 1), (24, 1), (44, 1)] }, { coefficient := 1, powers := [(16, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (60, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (45, 1)] }, { coefficient := 1, powers := [(12, 1), (57, 1)] }, { coefficient := 1, powers := [(17, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (39, 1)] }, { coefficient := 1, powers := [(16, 1), (44, 1)] }, { coefficient := 1, powers := [(16, 1), (51, 1)] }, { coefficient := 1, powers := [(16, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (54, 1)] }, { coefficient := 1, powers := [(28, 1), (40, 1)] }, { coefficient := 1, powers := [(28, 1), (46, 1), (49, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1), (53, 1)] }, { coefficient := 1, powers := [(24, 1), (39, 1)] }, { coefficient := 1, powers := [(24, 1), (44, 1)] }, { coefficient := 1, powers := [(53, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1), (51, 1)] }, { coefficient := 1, powers := [(19, 1), (51, 1)] }, { coefficient := 1, powers := [(19, 1), (56, 1)] }, { coefficient := 1, powers := [(46, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (39, 1), (55, 1)] }, { coefficient := 1, powers := [(1, 1), (43, 1)] }, { coefficient := 1, powers := [(4, 1), (30, 1), (55, 1)] }, { coefficient := 1, powers := [(10, 1), (20, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (35, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1)] }, { coefficient := 1, powers := [(16, 1), (21, 1)] }, { coefficient := 1, powers := [(16, 1), (26, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (44, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1), (44, 1)] }, { coefficient := 1, powers := [(12, 1), (28, 1), (44, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (25, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (30, 1), (56, 1)] }, { coefficient := 1, powers := [(3, 1), (33, 1), (51, 1)] }, { coefficient := 1, powers := [(25, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (42, 1), (53, 1)] }, { coefficient := 1, powers := [(22, 1), (57, 1)] }, { coefficient := 1, powers := [(28, 1), (47, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1)] }, { coefficient := 1, powers := [(6, 1), (59, 1)] }, { coefficient := 1, powers := [(23, 1), (39, 1)] }, { coefficient := 1, powers := [(23, 1), (44, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(4, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (59, 1)] }, { coefficient := 1, powers := [(10, 1), (44, 1)] }, { coefficient := 1, powers := [(10, 1), (56, 1)] }, { coefficient := 1, powers := [(14, 1), (39, 1)] }, { coefficient := 1, powers := [(14, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (51, 1)] }, { coefficient := 1, powers := [(20, 1), (56, 1)] }, { coefficient := 1, powers := [(25, 1), (39, 1)] }, { coefficient := 1, powers := [(25, 1), (44, 1)] }, { coefficient := 1, powers := [(30, 1), (36, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (39, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (45, 1), (53, 1)] }, { coefficient := 1, powers := [(24, 1), (39, 1), (42, 1)] }, { coefficient := 1, powers := [(24, 1), (45, 1)] }, { coefficient := 1, powers := [(42, 1), (53, 1)] }, { coefficient := 1, powers := [(57, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (42, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (21, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1), (42, 1)] }, { coefficient := 1, powers := [(12, 1), (21, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1), (28, 1), (42, 1)] }, { coefficient := 1, powers := [(17, 1), (21, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (46, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1), (46, 1)] }, { coefficient := 1, powers := [(12, 1), (28, 1), (46, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1), (54, 1)] }, { coefficient := 1, powers := [(16, 1), (28, 1), (40, 1)] }, { coefficient := 1, powers := [(16, 1), (31, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (47, 1), (49, 1)] }, { coefficient := 1, powers := [(5, 1), (26, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (49, 1)] }, { coefficient := 1, powers := [(12, 1), (26, 1), (47, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (49, 1)] }, { coefficient := 1, powers := [(17, 1), (26, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (47, 1), (53, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (53, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1), (57, 1)] }, { coefficient := 1, powers := [(16, 1), (28, 1), (47, 1)] }, { coefficient := 1, powers := [(16, 1), (34, 1), (37, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (42, 1), (54, 1)] }, { coefficient := 1, powers := [(22, 1), (49, 1), (57, 1)] }, { coefficient := 1, powers := [(28, 1), (40, 1), (42, 1)] }, { coefficient := 1, powers := [(28, 1), (47, 1), (49, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1), (42, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (36, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (44, 1), (51, 1)] }, { coefficient := 1, powers := [(39, 1)] }, { coefficient := 1, powers := [(44, 1)] }, { coefficient := 1, powers := [(51, 1)] }, { coefficient := 1, powers := [(56, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (36, 1), (59, 1)] }, { coefficient := 1, powers := [(1, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(1, 1), (44, 1), (51, 1)] }, { coefficient := 1, powers := [(4, 1), (25, 1), (59, 1)] }, { coefficient := 1, powers := [(4, 1), (30, 1), (56, 1)] }, { coefficient := 1, powers := [(4, 1), (33, 1), (51, 1)] }, { coefficient := 1, powers := [(7, 1), (20, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (30, 1), (44, 1)] }, { coefficient := 1, powers := [(7, 1), (33, 1), (39, 1)] }, { coefficient := 1, powers := [(10, 1), (20, 1), (56, 1)] }, { coefficient := 1, powers := [(10, 1), (25, 1), (44, 1)] }, { coefficient := 1, powers := [(10, 1), (33, 1), (36, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1), (51, 1)] }, { coefficient := 1, powers := [(14, 1), (25, 1), (39, 1)] }, { coefficient := 1, powers := [(14, 1), (30, 1), (36, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (37, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (47, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (28, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (22, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1), (47, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (40, 1)] }, { coefficient := 1, powers := [(12, 1), (22, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1), (28, 1), (47, 1)] }, { coefficient := 1, powers := [(12, 1), (34, 1), (37, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (54, 1)] }, { coefficient := 1, powers := [(17, 1), (28, 1), (40, 1)] }, { coefficient := 1, powers := [(17, 1), (31, 1), (37, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1)] }],
  [{ coefficient := 1, powers := [(1, 1)] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(40, 1)] }],
  [{ coefficient := 1, powers := [(55, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(57, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 46 → SparsePoly (Fin 64) := ![
  [{ coefficient := -1, powers := [(3, 1), (14, 1), (26, 1), (44, 1), (51, 1), (53, 1), (60, 1)] }, { coefficient := 1, powers := [(3, 1), (14, 1), (28, 1), (44, 1), (51, 1), (60, 1)] }, { coefficient := 1, powers := [(3, 1), (14, 1), (34, 1), (44, 1), (51, 1), (54, 1)] }, { coefficient := 1, powers := [(4, 1), (26, 1), (44, 1), (53, 1), (60, 1)] }, { coefficient := -1, powers := [(4, 1), (26, 1), (51, 1), (53, 1), (60, 1)] }, { coefficient := -1, powers := [(4, 1), (28, 1), (44, 1), (60, 1)] }, { coefficient := 1, powers := [(4, 1), (28, 1), (51, 1), (60, 1)] }, { coefficient := -1, powers := [(4, 1), (34, 1), (44, 1), (54, 1)] }, { coefficient := 1, powers := [(4, 1), (34, 1), (51, 1), (54, 1)] }, { coefficient := -1, powers := [(7, 1), (26, 1), (39, 1), (53, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (28, 1), (39, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (34, 1), (39, 1), (54, 1)] }, { coefficient := -1, powers := [(10, 1), (26, 1), (36, 1), (53, 1), (60, 1)] }, { coefficient := 1, powers := [(10, 1), (28, 1), (36, 1), (60, 1)] }, { coefficient := 1, powers := [(10, 1), (34, 1), (36, 1), (54, 1)] }, { coefficient := 1, powers := [(14, 1), (26, 1), (36, 1), (53, 1), (60, 1)] }, { coefficient := -1, powers := [(14, 1), (28, 1), (36, 1), (60, 1)] }, { coefficient := -1, powers := [(14, 1), (34, 1), (36, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (14, 1), (26, 1), (39, 1), (44, 1), (53, 1), (60, 1), (62, 1)] }, { coefficient := 1, powers := [(3, 1), (14, 1), (26, 1), (44, 2), (53, 1), (60, 1), (62, 1)] }, { coefficient := 1, powers := [(3, 1), (14, 1), (26, 1), (44, 1), (51, 1), (53, 1), (60, 1), (62, 1)] }, { coefficient := -1, powers := [(3, 1), (14, 1), (28, 1), (39, 1), (44, 1), (60, 1), (62, 1)] }, { coefficient := -1, powers := [(3, 1), (14, 1), (28, 1), (44, 2), (60, 1), (62, 1)] }, { coefficient := -1, powers := [(3, 1), (14, 1), (28, 1), (44, 1), (51, 1), (60, 1), (62, 1)] }, { coefficient := -1, powers := [(3, 1), (14, 1), (34, 1), (39, 1), (44, 1), (54, 1), (62, 1)] }, { coefficient := -1, powers := [(3, 1), (14, 1), (34, 1), (44, 2), (54, 1), (62, 1)] }, { coefficient := -1, powers := [(3, 1), (14, 1), (34, 1), (44, 1), (51, 1), (54, 1), (62, 1)] }, { coefficient := 1, powers := [(4, 1), (26, 1), (39, 1), (53, 1), (60, 1), (62, 1)] }, { coefficient := 1, powers := [(4, 1), (26, 1), (51, 1), (53, 1), (60, 1), (62, 1)] }, { coefficient := -1, powers := [(4, 1), (28, 1), (39, 1), (60, 1), (62, 1)] }, { coefficient := -1, powers := [(4, 1), (28, 1), (51, 1), (60, 1), (62, 1)] }, { coefficient := -1, powers := [(4, 1), (34, 1), (39, 1), (54, 1), (62, 1)] }, { coefficient := -1, powers := [(4, 1), (34, 1), (51, 1), (54, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(28, 1), (39, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (42, 1), (44, 1), (46, 1)] }, { coefficient := -1, powers := [(22, 1), (42, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (39, 1), (47, 1), (54, 1)] }, { coefficient := -1, powers := [(21, 1), (42, 1), (44, 1), (46, 1), (54, 1)] }, { coefficient := 1, powers := [(22, 1), (42, 1), (44, 1), (54, 1)] }, { coefficient := 1, powers := [(27, 1), (47, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(16, 1), (18, 1), (39, 1), (47, 1)] }, { coefficient := -1, powers := [(16, 1), (47, 1)] }, { coefficient := -1, powers := [(17, 1), (46, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(28, 1), (47, 1)] }],
  [{ coefficient := -1, powers := [(26, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (44, 1), (46, 1), (54, 1)] }, { coefficient := -1, powers := [(22, 1), (44, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(16, 1), (27, 1), (47, 1)] }, { coefficient := -1, powers := [(17, 1), (21, 1), (44, 1), (46, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (44, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (26, 1), (44, 1), (53, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (28, 1), (44, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (44, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (26, 1), (44, 1), (53, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (28, 1), (44, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (44, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (21, 1), (46, 1)] }, { coefficient := -1, powers := [(17, 1), (22, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (47, 1)] }],
  [{ coefficient := -1, powers := [(23, 1), (39, 1), (47, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (14, 1), (25, 1), (26, 1), (44, 1), (53, 1), (60, 1)] }, { coefficient := 1, powers := [(3, 1), (14, 1), (25, 1), (28, 1), (44, 1), (60, 1)] }, { coefficient := 1, powers := [(3, 1), (14, 1), (25, 1), (34, 1), (44, 1), (54, 1)] }, { coefficient := 1, powers := [(4, 1), (20, 1), (26, 1), (53, 1), (60, 1)] }, { coefficient := -1, powers := [(4, 1), (20, 1), (28, 1), (60, 1)] }, { coefficient := -1, powers := [(4, 1), (20, 1), (34, 1), (54, 1)] }, { coefficient := -1, powers := [(4, 1), (25, 1), (26, 1), (53, 1), (60, 1)] }, { coefficient := 1, powers := [(4, 1), (25, 1), (28, 1), (60, 1)] }, { coefficient := 1, powers := [(4, 1), (25, 1), (34, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (31, 1), (47, 1)] }],
  [{ coefficient := -1, powers := [(21, 1), (46, 1)] }, { coefficient := 1, powers := [(22, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (14, 1), (19, 1), (25, 1), (26, 1), (44, 1), (53, 1), (60, 1)] }, { coefficient := -1, powers := [(3, 1), (14, 1), (19, 1), (25, 1), (28, 1), (44, 1), (60, 1)] }, { coefficient := -1, powers := [(3, 1), (14, 1), (19, 1), (25, 1), (34, 1), (44, 1), (54, 1)] }, { coefficient := -1, powers := [(4, 1), (19, 1), (20, 1), (26, 1), (53, 1), (60, 1)] }, { coefficient := 1, powers := [(4, 1), (19, 1), (20, 1), (28, 1), (60, 1)] }, { coefficient := 1, powers := [(4, 1), (19, 1), (20, 1), (34, 1), (54, 1)] }, { coefficient := 1, powers := [(4, 1), (19, 1), (25, 1), (26, 1), (53, 1), (60, 1)] }, { coefficient := -1, powers := [(4, 1), (19, 1), (25, 1), (28, 1), (60, 1)] }, { coefficient := -1, powers := [(4, 1), (19, 1), (25, 1), (34, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(17, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (16, 1), (31, 1), (47, 1)] }, { coefficient := -1, powers := [(12, 1), (21, 1), (42, 1), (46, 1)] }, { coefficient := 1, powers := [(12, 1), (22, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (14, 1), (16, 1), (25, 1), (26, 1), (44, 1), (53, 1), (60, 1)] }, { coefficient := -1, powers := [(3, 1), (14, 1), (16, 1), (25, 1), (28, 1), (44, 1), (60, 1)] }, { coefficient := -1, powers := [(3, 1), (14, 1), (16, 1), (25, 1), (34, 1), (44, 1), (54, 1)] }, { coefficient := -1, powers := [(4, 1), (16, 1), (20, 1), (26, 1), (53, 1), (60, 1)] }, { coefficient := 1, powers := [(4, 1), (16, 1), (20, 1), (28, 1), (60, 1)] }, { coefficient := 1, powers := [(4, 1), (16, 1), (20, 1), (34, 1), (54, 1)] }, { coefficient := 1, powers := [(4, 1), (16, 1), (25, 1), (26, 1), (53, 1), (60, 1)] }, { coefficient := -1, powers := [(4, 1), (16, 1), (25, 1), (28, 1), (60, 1)] }, { coefficient := -1, powers := [(4, 1), (16, 1), (25, 1), (34, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (26, 1), (44, 1), (53, 1), (60, 1), (62, 1)] }, { coefficient := -1, powers := [(5, 1), (28, 1), (44, 1), (60, 1), (62, 1)] }, { coefficient := -1, powers := [(5, 1), (34, 1), (44, 1), (54, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(47, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(23, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (14, 1), (26, 1), (44, 1), (53, 1), (60, 1)] }, { coefficient := -1, powers := [(5, 1), (14, 1), (28, 1), (44, 1), (60, 1)] }, { coefficient := -1, powers := [(5, 1), (14, 1), (34, 1), (44, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(12, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (31, 1), (47, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (20, 1), (26, 1), (53, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (20, 1), (28, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (20, 1), (34, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (14, 1), (26, 1), (53, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (14, 1), (28, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (14, 1), (34, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (21, 1), (46, 1)] }, { coefficient := -1, powers := [(12, 1), (22, 1)] }],
  [{ coefficient := 1, powers := [(46, 1)] }],
  [{ coefficient := -1, powers := [(42, 1)] }],
  [{ coefficient := 1, powers := [(53, 1)] }],
  [{ coefficient := -1, powers := [(49, 1)] }],
  [{ coefficient := 1, powers := [(16, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (5, 1), (14, 1), (26, 1), (30, 1), (44, 1), (53, 1), (60, 1)] }, { coefficient := 1, powers := [(3, 1), (5, 1), (14, 1), (28, 1), (30, 1), (44, 1), (60, 1)] }, { coefficient := 1, powers := [(3, 1), (5, 1), (14, 1), (30, 1), (34, 1), (44, 1), (54, 1)] }, { coefficient := -1, powers := [(3, 1), (14, 1), (16, 1), (19, 1), (25, 1), (26, 1), (44, 1), (53, 1), (60, 1)] }, { coefficient := 1, powers := [(3, 1), (14, 1), (16, 1), (19, 1), (25, 1), (28, 1), (44, 1), (60, 1)] }, { coefficient := 1, powers := [(3, 1), (14, 1), (16, 1), (19, 1), (25, 1), (34, 1), (44, 1), (54, 1)] }, { coefficient := -1, powers := [(4, 1), (5, 1), (26, 1), (30, 1), (53, 1), (60, 1)] }, { coefficient := 1, powers := [(4, 1), (5, 1), (28, 1), (30, 1), (60, 1)] }, { coefficient := 1, powers := [(4, 1), (5, 1), (30, 1), (34, 1), (54, 1)] }, { coefficient := 1, powers := [(4, 1), (16, 1), (19, 1), (20, 1), (26, 1), (53, 1), (60, 1)] }, { coefficient := -1, powers := [(4, 1), (16, 1), (19, 1), (20, 1), (28, 1), (60, 1)] }, { coefficient := -1, powers := [(4, 1), (16, 1), (19, 1), (20, 1), (34, 1), (54, 1)] }, { coefficient := -1, powers := [(4, 1), (16, 1), (19, 1), (25, 1), (26, 1), (53, 1), (60, 1)] }, { coefficient := 1, powers := [(4, 1), (16, 1), (19, 1), (25, 1), (28, 1), (60, 1)] }, { coefficient := 1, powers := [(4, 1), (16, 1), (19, 1), (25, 1), (34, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (14, 1), (20, 1), (26, 1), (53, 1), (60, 1)] }, { coefficient := -1, powers := [(5, 1), (14, 1), (20, 1), (28, 1), (60, 1)] }, { coefficient := -1, powers := [(5, 1), (14, 1), (20, 1), (34, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (26, 1), (53, 1), (60, 1)] }, { coefficient := -1, powers := [(5, 1), (28, 1), (60, 1)] }, { coefficient := -1, powers := [(5, 1), (34, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(3, 1), (5, 1), (14, 1), (26, 1), (30, 1), (36, 1), (44, 1), (53, 1), (59, 1), (60, 1)] }, { coefficient := 1, powers := [(3, 1), (5, 1), (14, 1), (26, 1), (30, 1), (39, 1), (44, 1), (53, 1), (56, 1), (60, 1)] }, { coefficient := 1, powers := [(3, 1), (5, 1), (14, 1), (26, 1), (30, 1), (44, 2), (51, 1), (53, 1), (60, 1)] }, { coefficient := -1, powers := [(3, 1), (5, 1), (14, 1), (28, 1), (30, 1), (36, 1), (44, 1), (59, 1), (60, 1)] }, { coefficient := -1, powers := [(3, 1), (5, 1), (14, 1), (28, 1), (30, 1), (39, 1), (44, 1), (56, 1), (60, 1)] }, { coefficient := -1, powers := [(3, 1), (5, 1), (14, 1), (28, 1), (30, 1), (44, 2), (51, 1), (60, 1)] }, { coefficient := -1, powers := [(3, 1), (5, 1), (14, 1), (30, 1), (34, 1), (36, 1), (44, 1), (54, 1), (59, 1)] }, { coefficient := -1, powers := [(3, 1), (5, 1), (14, 1), (30, 1), (34, 1), (39, 1), (44, 1), (54, 1), (56, 1)] }, { coefficient := -1, powers := [(3, 1), (5, 1), (14, 1), (30, 1), (34, 1), (44, 2), (51, 1), (54, 1)] }, { coefficient := 1, powers := [(3, 1), (14, 1), (16, 1), (19, 1), (25, 1), (26, 1), (36, 1), (44, 1), (53, 1), (59, 1), (60, 1)] }, { coefficient := 1, powers := [(3, 1), (14, 1), (16, 1), (19, 1), (25, 1), (26, 1), (39, 1), (44, 1), (53, 1), (56, 1), (60, 1)] }, { coefficient := 1, powers := [(3, 1), (14, 1), (16, 1), (19, 1), (25, 1), (26, 1), (44, 2), (51, 1), (53, 1), (60, 1)] }, { coefficient := -1, powers := [(3, 1), (14, 1), (16, 1), (19, 1), (25, 1), (28, 1), (36, 1), (44, 1), (59, 1), (60, 1)] }, { coefficient := -1, powers := [(3, 1), (14, 1), (16, 1), (19, 1), (25, 1), (28, 1), (39, 1), (44, 1), (56, 1), (60, 1)] }, { coefficient := -1, powers := [(3, 1), (14, 1), (16, 1), (19, 1), (25, 1), (28, 1), (44, 2), (51, 1), (60, 1)] }, { coefficient := -1, powers := [(3, 1), (14, 1), (16, 1), (19, 1), (25, 1), (34, 1), (36, 1), (44, 1), (54, 1), (59, 1)] }, { coefficient := -1, powers := [(3, 1), (14, 1), (16, 1), (19, 1), (25, 1), (34, 1), (39, 1), (44, 1), (54, 1), (56, 1)] }, { coefficient := -1, powers := [(3, 1), (14, 1), (16, 1), (19, 1), (25, 1), (34, 1), (44, 2), (51, 1), (54, 1)] }, { coefficient := -1, powers := [(3, 1), (14, 1), (16, 1), (25, 1), (26, 1), (44, 1), (46, 1), (51, 1), (53, 1), (60, 1)] }, { coefficient := 1, powers := [(3, 1), (14, 1), (16, 1), (25, 1), (28, 1), (44, 1), (46, 1), (51, 1), (60, 1)] }, { coefficient := 1, powers := [(3, 1), (14, 1), (16, 1), (25, 1), (34, 1), (44, 1), (46, 1), (51, 1), (54, 1)] }, { coefficient := 1, powers := [(4, 1), (5, 1), (26, 1), (30, 1), (36, 1), (53, 1), (59, 1), (60, 1)] }, { coefficient := 1, powers := [(4, 1), (5, 1), (26, 1), (30, 1), (39, 1), (53, 1), (56, 1), (60, 1)] }, { coefficient := 1, powers := [(4, 1), (5, 1), (26, 1), (30, 1), (44, 1), (51, 1), (53, 1), (60, 1)] }, { coefficient := -1, powers := [(4, 1), (5, 1), (28, 1), (30, 1), (36, 1), (59, 1), (60, 1)] }, { coefficient := -1, powers := [(4, 1), (5, 1), (28, 1), (30, 1), (39, 1), (56, 1), (60, 1)] }, { coefficient := -1, powers := [(4, 1), (5, 1), (28, 1), (30, 1), (44, 1), (51, 1), (60, 1)] }, { coefficient := -1, powers := [(4, 1), (5, 1), (30, 1), (34, 1), (36, 1), (54, 1), (59, 1)] }, { coefficient := -1, powers := [(4, 1), (5, 1), (30, 1), (34, 1), (39, 1), (54, 1), (56, 1)] }, { coefficient := -1, powers := [(4, 1), (5, 1), (30, 1), (34, 1), (44, 1), (51, 1), (54, 1)] }, { coefficient := -1, powers := [(4, 1), (16, 1), (19, 1), (20, 1), (26, 1), (36, 1), (53, 1), (59, 1), (60, 1)] }, { coefficient := -1, powers := [(4, 1), (16, 1), (19, 1), (20, 1), (26, 1), (39, 1), (53, 1), (56, 1), (60, 1)] }, { coefficient := -1, powers := [(4, 1), (16, 1), (19, 1), (20, 1), (26, 1), (44, 1), (51, 1), (53, 1), (60, 1)] }, { coefficient := 1, powers := [(4, 1), (16, 1), (19, 1), (20, 1), (28, 1), (36, 1), (59, 1), (60, 1)] }, { coefficient := 1, powers := [(4, 1), (16, 1), (19, 1), (20, 1), (28, 1), (39, 1), (56, 1), (60, 1)] }, { coefficient := 1, powers := [(4, 1), (16, 1), (19, 1), (20, 1), (28, 1), (44, 1), (51, 1), (60, 1)] }, { coefficient := 1, powers := [(4, 1), (16, 1), (19, 1), (20, 1), (34, 1), (36, 1), (54, 1), (59, 1)] }, { coefficient := 1, powers := [(4, 1), (16, 1), (19, 1), (20, 1), (34, 1), (39, 1), (54, 1), (56, 1)] }, { coefficient := 1, powers := [(4, 1), (16, 1), (19, 1), (20, 1), (34, 1), (44, 1), (51, 1), (54, 1)] }, { coefficient := 1, powers := [(4, 1), (16, 1), (19, 1), (25, 1), (26, 1), (36, 1), (53, 1), (59, 1), (60, 1)] }, { coefficient := 1, powers := [(4, 1), (16, 1), (19, 1), (25, 1), (26, 1), (39, 1), (53, 1), (56, 1), (60, 1)] }, { coefficient := 1, powers := [(4, 1), (16, 1), (19, 1), (25, 1), (26, 1), (44, 1), (51, 1), (53, 1), (60, 1)] }, { coefficient := -1, powers := [(4, 1), (16, 1), (19, 1), (25, 1), (28, 1), (36, 1), (59, 1), (60, 1)] }, { coefficient := -1, powers := [(4, 1), (16, 1), (19, 1), (25, 1), (28, 1), (39, 1), (56, 1), (60, 1)] }, { coefficient := -1, powers := [(4, 1), (16, 1), (19, 1), (25, 1), (28, 1), (44, 1), (51, 1), (60, 1)] }, { coefficient := -1, powers := [(4, 1), (16, 1), (19, 1), (25, 1), (34, 1), (36, 1), (54, 1), (59, 1)] }, { coefficient := -1, powers := [(4, 1), (16, 1), (19, 1), (25, 1), (34, 1), (39, 1), (54, 1), (56, 1)] }, { coefficient := -1, powers := [(4, 1), (16, 1), (19, 1), (25, 1), (34, 1), (44, 1), (51, 1), (54, 1)] }, { coefficient := 1, powers := [(4, 1), (16, 1), (20, 1), (26, 1), (46, 1), (51, 1), (53, 1), (60, 1)] }, { coefficient := -1, powers := [(4, 1), (16, 1), (20, 1), (28, 1), (46, 1), (51, 1), (60, 1)] }, { coefficient := -1, powers := [(4, 1), (16, 1), (20, 1), (34, 1), (46, 1), (51, 1), (54, 1)] }, { coefficient := -1, powers := [(4, 1), (16, 1), (25, 1), (26, 1), (46, 1), (51, 1), (53, 1), (60, 1)] }, { coefficient := 1, powers := [(4, 1), (16, 1), (25, 1), (28, 1), (46, 1), (51, 1), (60, 1)] }, { coefficient := 1, powers := [(4, 1), (16, 1), (25, 1), (34, 1), (46, 1), (51, 1), (54, 1)] }, { coefficient := -1, powers := [(5, 1), (14, 1), (20, 1), (26, 1), (36, 1), (53, 1), (59, 1), (60, 1)] }, { coefficient := -1, powers := [(5, 1), (14, 1), (20, 1), (26, 1), (39, 1), (53, 1), (56, 1), (60, 1)] }, { coefficient := -1, powers := [(5, 1), (14, 1), (20, 1), (26, 1), (44, 1), (51, 1), (53, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (14, 1), (20, 1), (28, 1), (36, 1), (59, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (14, 1), (20, 1), (28, 1), (39, 1), (56, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (14, 1), (20, 1), (28, 1), (44, 1), (51, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (14, 1), (20, 1), (34, 1), (36, 1), (54, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (14, 1), (20, 1), (34, 1), (39, 1), (54, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (14, 1), (20, 1), (34, 1), (44, 1), (51, 1), (54, 1)] }, { coefficient := -1, powers := [(6, 1), (16, 1), (31, 1), (44, 1), (47, 1), (53, 1)] }, { coefficient := -1, powers := [(8, 1), (31, 1), (44, 1), (47, 1)] }, { coefficient := -1, powers := [(12, 1), (21, 1), (39, 1), (46, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1), (21, 1), (42, 1), (44, 1), (46, 1), (53, 1)] }, { coefficient := -1, powers := [(12, 1), (21, 1), (45, 1), (46, 1), (53, 1)] }, { coefficient := 1, powers := [(12, 1), (22, 1), (39, 1), (57, 1)] }, { coefficient := -1, powers := [(12, 1), (22, 1), (42, 1), (44, 1), (53, 1)] }, { coefficient := 1, powers := [(12, 1), (22, 1), (45, 1), (53, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1), (47, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (26, 1), (36, 1), (53, 1), (59, 1), (60, 1)] }, { coefficient := -1, powers := [(5, 1), (26, 1), (39, 1), (44, 1), (53, 1), (55, 1), (60, 1), (62, 1)] }, { coefficient := -1, powers := [(5, 1), (26, 1), (39, 1), (53, 1), (56, 1), (60, 1)] }, { coefficient := -1, powers := [(5, 1), (26, 1), (43, 1), (44, 1), (53, 1), (60, 1), (62, 1)] }, { coefficient := 1, powers := [(5, 1), (26, 1), (44, 2), (53, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (28, 1), (36, 1), (59, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (28, 1), (39, 1), (44, 1), (55, 1), (60, 1), (62, 1)] }, { coefficient := 1, powers := [(5, 1), (28, 1), (39, 1), (56, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (28, 1), (43, 1), (44, 1), (60, 1), (62, 1)] }, { coefficient := -1, powers := [(5, 1), (28, 1), (44, 2), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (36, 1), (54, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (39, 1), (44, 1), (54, 1), (55, 1), (62, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (39, 1), (54, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (43, 1), (44, 1), (54, 1), (62, 1)] }, { coefficient := -1, powers := [(5, 1), (34, 1), (44, 2), (54, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (39, 1), (47, 1), (54, 1)] }, { coefficient := 1, powers := [(23, 1), (44, 1), (47, 1), (54, 1)] }, { coefficient := -1, powers := [(24, 1), (44, 1), (47, 1), (49, 1)] }, { coefficient := -1, powers := [(35, 1), (47, 1), (54, 1), (59, 1)] }, { coefficient := 1, powers := [(37, 1), (60, 1)] }, { coefficient := 1, powers := [(40, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (34, 1)] }, { coefficient := -1, powers := [(17, 1), (26, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (5, 1), (14, 1), (26, 1), (30, 1), (39, 1), (44, 1), (53, 1), (60, 1)] }, { coefficient := -1, powers := [(3, 1), (5, 1), (14, 1), (26, 1), (30, 1), (44, 2), (53, 1), (60, 1)] }, { coefficient := -1, powers := [(3, 1), (5, 1), (14, 1), (26, 1), (30, 1), (44, 1), (51, 1), (53, 1), (60, 1)] }, { coefficient := 1, powers := [(3, 1), (5, 1), (14, 1), (28, 1), (30, 1), (39, 1), (44, 1), (60, 1)] }, { coefficient := 1, powers := [(3, 1), (5, 1), (14, 1), (28, 1), (30, 1), (44, 2), (60, 1)] }, { coefficient := 1, powers := [(3, 1), (5, 1), (14, 1), (28, 1), (30, 1), (44, 1), (51, 1), (60, 1)] }, { coefficient := 1, powers := [(3, 1), (5, 1), (14, 1), (30, 1), (34, 1), (39, 1), (44, 1), (54, 1)] }, { coefficient := 1, powers := [(3, 1), (5, 1), (14, 1), (30, 1), (34, 1), (44, 2), (54, 1)] }, { coefficient := 1, powers := [(3, 1), (5, 1), (14, 1), (30, 1), (34, 1), (44, 1), (51, 1), (54, 1)] }, { coefficient := -1, powers := [(4, 1), (5, 1), (26, 1), (30, 1), (39, 1), (53, 1), (60, 1)] }, { coefficient := -1, powers := [(4, 1), (5, 1), (26, 1), (30, 1), (44, 1), (53, 1), (60, 1)] }, { coefficient := -1, powers := [(4, 1), (5, 1), (26, 1), (30, 1), (51, 1), (53, 1), (60, 1)] }, { coefficient := 1, powers := [(4, 1), (5, 1), (28, 1), (30, 1), (39, 1), (60, 1)] }, { coefficient := 1, powers := [(4, 1), (5, 1), (28, 1), (30, 1), (44, 1), (60, 1)] }, { coefficient := 1, powers := [(4, 1), (5, 1), (28, 1), (30, 1), (51, 1), (60, 1)] }, { coefficient := 1, powers := [(4, 1), (5, 1), (30, 1), (34, 1), (39, 1), (54, 1)] }, { coefficient := 1, powers := [(4, 1), (5, 1), (30, 1), (34, 1), (44, 1), (54, 1)] }, { coefficient := 1, powers := [(4, 1), (5, 1), (30, 1), (34, 1), (51, 1), (54, 1)] }, { coefficient := -1, powers := [(5, 1), (10, 1), (20, 1), (26, 1), (44, 1), (53, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (10, 1), (20, 1), (28, 1), (44, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (10, 1), (20, 1), (34, 1), (44, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (31, 1)] }, { coefficient := -1, powers := [(12, 1), (21, 1), (46, 1)] }]
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
    (values : Fin 64 → R) :
    ¬ ∀ index : Fin 46,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component39.SelectedLeafB0_2_6.selectedHasNoCommonZero

end Krenn.Component39.SelectedLeafB0_2_6
