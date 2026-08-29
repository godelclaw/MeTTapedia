import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component37.SelectedLeafB4_4_2_1

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "f8db4e6ec88f2c92edf5ee560ccfd12d89b624982f7a4aa1f1b7460dbc3aabb4"
def certificateSHA256 : String := "b8a83ca4487f2f75691606889f9e32ba5624b16f880c1b5991cfda52f29a14d2"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 50 → Fin 670 := ![
  16,
  19,
  78,
  79,
  147,
  151,
  171,
  180,
  265,
  267,
  294,
  295,
  298,
  299,
  303,
  308,
  312,
  313,
  317,
  354,
  433,
  446,
  450,
  461,
  463,
  505,
  557,
  580,
  586,
  602,
  603,
  605,
  606,
  617,
  647,
  655,
  656,
  657,
  658,
  659,
  660,
  661,
  662,
  663,
  664,
  665,
  666,
  667,
  668,
  669
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 50 → SparsePoly (Fin 66) := ![
  [{ coefficient := 1, powers := [(18, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (30, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (30, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (31, 1)] }, { coefficient := 1, powers := [(15, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (30, 1)] }, { coefficient := 1, powers := [(30, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (44, 1)] }, { coefficient := 1, powers := [(28, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (23, 1), (52, 1)] }, { coefficient := 1, powers := [(29, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (23, 1), (54, 1)] }, { coefficient := 1, powers := [(30, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1)] }, { coefficient := 1, powers := [(20, 1), (44, 1)] }, { coefficient := 1, powers := [(25, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (49, 1)] }, { coefficient := 1, powers := [(21, 1), (44, 1)] }, { coefficient := 1, powers := [(25, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (46, 1)] }, { coefficient := 1, powers := [(4, 1), (35, 1)] }, { coefficient := 1, powers := [(15, 1), (22, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (52, 1)] }, { coefficient := 1, powers := [(7, 1), (32, 1)] }, { coefficient := 1, powers := [(10, 1), (27, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (46, 1)] }, { coefficient := 1, powers := [(9, 1), (57, 1)] }, { coefficient := 1, powers := [(31, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (23, 1)] }, { coefficient := 1, powers := [(23, 1), (56, 1)] }, { coefficient := 1, powers := [(28, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (54, 1)] }, { coefficient := 1, powers := [(30, 1), (41, 1)] }, { coefficient := 1, powers := [(30, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(20, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(44, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (49, 1), (52, 1)] }, { coefficient := 1, powers := [(21, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(49, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (31, 1), (57, 1)] }, { coefficient := 1, powers := [(7, 1), (31, 1), (46, 1)] }, { coefficient := 1, powers := [(15, 1), (31, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (49, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1)] }, { coefficient := 1, powers := [(18, 1), (28, 1), (49, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (61, 1)] }, { coefficient := 1, powers := [(12, 1), (49, 1)] }, { coefficient := 1, powers := [(19, 1), (21, 1), (53, 1)] }, { coefficient := 1, powers := [(19, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (61, 1)] }, { coefficient := 1, powers := [(12, 1), (26, 1), (47, 1)] }, { coefficient := 1, powers := [(12, 1), (58, 1)] }, { coefficient := 1, powers := [(19, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1), (52, 1)] }, { coefficient := 1, powers := [(3, 1), (34, 1), (52, 1)] }, { coefficient := 1, powers := [(13, 1), (20, 1), (52, 1)] }, { coefficient := 1, powers := [(43, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1), (54, 1)] }, { coefficient := 1, powers := [(3, 1), (34, 1), (54, 1)] }, { coefficient := 1, powers := [(13, 1), (20, 1), (54, 1)] }, { coefficient := 1, powers := [(26, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (25, 1), (60, 1)] }, { coefficient := 1, powers := [(10, 1), (25, 1), (46, 1)] }, { coefficient := 1, powers := [(15, 1), (25, 1), (41, 1)] }, { coefficient := 1, powers := [(15, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (22, 1), (52, 1)] }, { coefficient := 1, powers := [(13, 1), (27, 1), (41, 1)] }, { coefficient := 1, powers := [(13, 1), (32, 1), (38, 1)] }, { coefficient := 1, powers := [(27, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1)] }, { coefficient := 1, powers := [(6, 1), (60, 1)] }, { coefficient := 1, powers := [(25, 1), (41, 1)] }, { coefficient := 1, powers := [(25, 1), (46, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1), (52, 1)] }, { coefficient := 1, powers := [(13, 1), (41, 1)] }, { coefficient := 1, powers := [(13, 1), (52, 1)] }, { coefficient := 1, powers := [(34, 1), (38, 1)] }, { coefficient := 1, powers := [(45, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1)] }, { coefficient := 1, powers := [(3, 1), (34, 1)] }, { coefficient := 1, powers := [(13, 1), (20, 1)] }, { coefficient := 1, powers := [(20, 1), (56, 1)] }, { coefficient := 1, powers := [(25, 1), (43, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (50, 1)] }, { coefficient := 1, powers := [(6, 1), (31, 1)] }, { coefficient := 1, powers := [(9, 1), (25, 1)] }, { coefficient := 1, powers := [(20, 1), (50, 1)] }, { coefficient := 1, powers := [(25, 1), (40, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (52, 1)] }, { coefficient := 1, powers := [(22, 1), (57, 1)] }, { coefficient := 1, powers := [(27, 1), (41, 1)] }, { coefficient := 1, powers := [(27, 1), (46, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1)] }, { coefficient := 1, powers := [(35, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (37, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1)] }, { coefficient := 1, powers := [(3, 1), (25, 1), (60, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1), (60, 1)] }, { coefficient := 1, powers := [(20, 1)] }, { coefficient := 1, powers := [(25, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (37, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (44, 1), (51, 1)] }, { coefficient := 1, powers := [(12, 1), (28, 1), (44, 1)] }, { coefficient := 1, powers := [(12, 1), (36, 1), (37, 1)] }, { coefficient := 1, powers := [(19, 1), (23, 1), (51, 1)] }, { coefficient := 1, powers := [(19, 1), (33, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (41, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (45, 1)] }, { coefficient := 1, powers := [(6, 1), (34, 1), (41, 1)] }, { coefficient := 1, powers := [(13, 1), (25, 1), (41, 1)] }, { coefficient := 1, powers := [(13, 1)] }, { coefficient := 1, powers := [(25, 1), (45, 1)] }, { coefficient := 1, powers := [(56, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (37, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (40, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (43, 1), (50, 1)] }, { coefficient := 1, powers := [(3, 1), (25, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (31, 1), (56, 1)] }, { coefficient := 1, powers := [(3, 1), (34, 1), (50, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (31, 1), (43, 1)] }, { coefficient := 1, powers := [(6, 1), (34, 1), (40, 1)] }, { coefficient := 1, powers := [(9, 1), (20, 1), (56, 1)] }, { coefficient := 1, powers := [(9, 1), (25, 1), (43, 1)] }, { coefficient := 1, powers := [(9, 1), (34, 1), (37, 1)] }, { coefficient := 1, powers := [(13, 1), (20, 1), (50, 1)] }, { coefficient := 1, powers := [(13, 1), (25, 1), (40, 1)] }, { coefficient := 1, powers := [(13, 1), (31, 1), (37, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1), (38, 1), (60, 1)] }, { coefficient := 1, powers := [(1, 1), (41, 1), (57, 1)] }, { coefficient := 1, powers := [(1, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(4, 1), (27, 1), (60, 1)] }, { coefficient := 1, powers := [(4, 1), (32, 1), (57, 1)] }, { coefficient := 1, powers := [(4, 1), (35, 1), (52, 1)] }, { coefficient := 1, powers := [(7, 1), (22, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (32, 1), (46, 1)] }, { coefficient := 1, powers := [(7, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(10, 1), (22, 1), (57, 1)] }, { coefficient := 1, powers := [(10, 1), (27, 1), (46, 1)] }, { coefficient := 1, powers := [(10, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(15, 1), (22, 1), (52, 1)] }, { coefficient := 1, powers := [(15, 1), (27, 1), (41, 1)] }, { coefficient := 1, powers := [(15, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (39, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (42, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (49, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (49, 1)] }, { coefficient := 1, powers := [(8, 1), (36, 1), (42, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (58, 1)] }, { coefficient := 1, powers := [(12, 1), (30, 1), (49, 1)] }, { coefficient := 1, powers := [(12, 1), (36, 1), (39, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (55, 1)] }, { coefficient := 1, powers := [(19, 1), (30, 1), (42, 1)] }, { coefficient := 1, powers := [(19, 1), (33, 1), (39, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1)] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(40, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(41, 1)] }],
  [{ coefficient := 1, powers := [(42, 1)] }],
  [{ coefficient := 1, powers := [(56, 1)] }],
  [{ coefficient := 1, powers := [(57, 1), (64, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(58, 1)] }],
  [{ coefficient := 1, powers := [(25, 1)] }],
  [{ coefficient := 1, powers := [(27, 1)] }],
  [{ coefficient := 1, powers := [(30, 1), (65, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 50 → SparsePoly (Fin 66) := ![
  [{ coefficient := 1, powers := [(0, 1), (24, 1), (37, 1), (44, 1), (55, 1), (59, 1), (63, 1)] }, { coefficient := 1, powers := [(20, 1), (24, 1), (37, 1), (44, 1), (55, 1), (59, 1), (63, 1)] }, { coefficient := -1, powers := [(24, 1), (31, 1), (37, 1), (43, 1), (44, 1), (55, 1), (63, 1)] }, { coefficient := -1, powers := [(24, 1), (34, 1), (37, 1), (44, 1), (50, 1), (55, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (21, 1), (30, 1), (37, 1), (53, 1), (59, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (23, 1), (39, 1), (51, 1), (59, 1), (63, 1)] }, { coefficient := 1, powers := [(0, 1), (24, 1), (26, 1), (37, 1), (53, 1), (59, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (24, 1), (37, 1), (55, 1), (59, 1), (63, 1)] }, { coefficient := -1, powers := [(20, 1), (21, 1), (30, 1), (37, 1), (53, 1), (59, 1), (63, 1)] }, { coefficient := -1, powers := [(20, 1), (23, 1), (39, 1), (51, 1), (59, 1), (63, 1)] }, { coefficient := 1, powers := [(20, 1), (24, 1), (26, 1), (37, 1), (53, 1), (59, 1), (63, 1)] }, { coefficient := -1, powers := [(20, 1), (24, 1), (37, 1), (55, 1), (59, 1), (63, 1)] }, { coefficient := 1, powers := [(21, 1), (30, 1), (31, 1), (37, 1), (43, 1), (53, 1), (63, 1)] }, { coefficient := 1, powers := [(21, 1), (30, 1), (34, 1), (37, 1), (50, 1), (53, 1), (63, 1)] }, { coefficient := 1, powers := [(23, 1), (31, 1), (39, 1), (43, 1), (51, 1), (63, 1)] }, { coefficient := 1, powers := [(23, 1), (34, 1), (39, 1), (50, 1), (51, 1), (63, 1)] }, { coefficient := -1, powers := [(24, 1), (26, 1), (31, 1), (37, 1), (43, 1), (53, 1), (63, 1)] }, { coefficient := -1, powers := [(24, 1), (26, 1), (34, 1), (37, 1), (50, 1), (53, 1), (63, 1)] }, { coefficient := 1, powers := [(24, 1), (31, 1), (37, 1), (43, 1), (55, 1), (63, 1)] }, { coefficient := 1, powers := [(24, 1), (34, 1), (37, 1), (50, 1), (55, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (31, 1), (63, 1), (64, 1), (65, 1)] }, { coefficient := -1, powers := [(31, 1), (37, 1), (63, 1), (64, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (20, 1), (37, 1), (59, 1), (63, 1), (65, 1)] }, { coefficient := -1, powers := [(0, 1), (34, 1), (37, 1), (50, 1), (63, 1), (65, 1)] }, { coefficient := -1, powers := [(6, 1), (20, 2), (59, 1), (63, 1), (65, 1)] }, { coefficient := 1, powers := [(6, 1), (34, 1), (64, 1), (65, 1)] }, { coefficient := -1, powers := [(20, 1), (34, 1), (37, 1), (50, 1), (63, 1), (65, 1)] }, { coefficient := -1, powers := [(34, 1), (37, 1), (64, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (22, 1), (37, 1), (60, 1)] }, { coefficient := -1, powers := [(13, 1), (32, 1), (37, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (20, 1), (37, 1), (46, 1), (59, 1), (63, 1), (65, 1)] }, { coefficient := 1, powers := [(0, 1), (34, 1), (37, 1), (46, 1), (50, 1), (63, 1), (65, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 2), (46, 1), (59, 1), (63, 1), (65, 1)] }, { coefficient := -1, powers := [(6, 1), (31, 1), (45, 1), (63, 1), (64, 1), (65, 1)] }, { coefficient := 1, powers := [(6, 1), (34, 1), (65, 1)] }, { coefficient := -1, powers := [(13, 1), (15, 1), (22, 1), (37, 1), (60, 1), (65, 1)] }, { coefficient := 1, powers := [(13, 1), (15, 1), (32, 1), (37, 1), (46, 1), (65, 1)] }, { coefficient := 1, powers := [(20, 1), (34, 1), (37, 1), (46, 1), (50, 1), (63, 1), (65, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1), (45, 1), (63, 1), (64, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (24, 1), (26, 1), (37, 1), (59, 1)] }, { coefficient := -1, powers := [(20, 1), (24, 1), (26, 1), (37, 1), (59, 1)] }, { coefficient := 1, powers := [(24, 1), (26, 1), (31, 1), (37, 1), (43, 1)] }, { coefficient := 1, powers := [(24, 1), (26, 1), (34, 1), (37, 1), (50, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (18, 1), (37, 1), (55, 1), (59, 1)] }, { coefficient := -1, powers := [(18, 1), (20, 1), (37, 1), (55, 1), (59, 1)] }, { coefficient := 1, powers := [(18, 1), (31, 1), (37, 1), (43, 1), (55, 1)] }, { coefficient := 1, powers := [(18, 1), (34, 1), (37, 1), (50, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (26, 1), (50, 1), (65, 1)] }, { coefficient := 1, powers := [(20, 1), (26, 1), (50, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (50, 1), (65, 1)] }, { coefficient := -1, powers := [(20, 1), (50, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (12, 1), (28, 1), (39, 1), (52, 1), (59, 1)] }, { coefficient := 1, powers := [(12, 1), (20, 1), (28, 1), (39, 1), (52, 1), (59, 1)] }, { coefficient := -1, powers := [(12, 1), (28, 1), (31, 1), (39, 1), (43, 1), (52, 1)] }, { coefficient := -1, powers := [(12, 1), (28, 1), (34, 1), (39, 1), (50, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (8, 1), (33, 1), (37, 1), (52, 1), (59, 1)] }, { coefficient := -1, powers := [(8, 1), (20, 1), (33, 1), (37, 1), (52, 1), (59, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1), (33, 1), (37, 1), (43, 1), (52, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (34, 1), (37, 1), (50, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (31, 1), (37, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (31, 1), (37, 1), (46, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (34, 1), (64, 1)] }, { coefficient := -1, powers := [(13, 1), (15, 1), (32, 1), (37, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (26, 1), (50, 1), (52, 1), (65, 1)] }, { coefficient := 1, powers := [(0, 1), (50, 1), (54, 1), (65, 1)] }, { coefficient := -1, powers := [(20, 1), (26, 1), (50, 1), (52, 1), (65, 1)] }, { coefficient := 1, powers := [(20, 1), (50, 1), (54, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (34, 1), (37, 1), (50, 1), (65, 1)] }, { coefficient := -1, powers := [(20, 1), (34, 1), (37, 1), (50, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (12, 1), (28, 1), (39, 1), (59, 1)] }, { coefficient := -1, powers := [(12, 1), (20, 1), (28, 1), (39, 1), (59, 1)] }, { coefficient := 1, powers := [(12, 1), (28, 1), (31, 1), (39, 1), (43, 1)] }, { coefficient := 1, powers := [(12, 1), (28, 1), (34, 1), (39, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (8, 1), (33, 1), (37, 1), (59, 1)] }, { coefficient := 1, powers := [(8, 1), (20, 1), (33, 1), (37, 1), (59, 1)] }, { coefficient := -1, powers := [(8, 1), (31, 1), (33, 1), (37, 1), (43, 1)] }, { coefficient := -1, powers := [(8, 1), (33, 1), (34, 1), (37, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (32, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (37, 1), (55, 1), (59, 1)] }, { coefficient := 1, powers := [(20, 1), (37, 1), (55, 1), (59, 1)] }, { coefficient := -1, powers := [(31, 1), (37, 1), (43, 1), (55, 1)] }, { coefficient := -1, powers := [(34, 1), (37, 1), (50, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (30, 1), (37, 1), (59, 1)] }, { coefficient := 1, powers := [(20, 1), (30, 1), (37, 1), (59, 1)] }, { coefficient := -1, powers := [(30, 1), (31, 1), (37, 1), (43, 1)] }, { coefficient := -1, powers := [(30, 1), (34, 1), (37, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (24, 1), (37, 1), (59, 1)] }, { coefficient := 1, powers := [(20, 1), (24, 1), (37, 1), (59, 1)] }, { coefficient := -1, powers := [(24, 1), (31, 1), (37, 1), (43, 1)] }, { coefficient := -1, powers := [(24, 1), (34, 1), (37, 1), (50, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (28, 1), (50, 1), (54, 1), (65, 1)] }, { coefficient := -1, powers := [(20, 1), (28, 1), (50, 1), (54, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (28, 1), (50, 1), (52, 1), (65, 1)] }, { coefficient := -1, powers := [(0, 1), (29, 1), (50, 1), (65, 1)] }, { coefficient := 1, powers := [(20, 1), (28, 1), (50, 1), (52, 1), (65, 1)] }, { coefficient := -1, powers := [(20, 1), (29, 1), (50, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (13, 1), (22, 1), (37, 1), (60, 1)] }, { coefficient := 1, powers := [(9, 1), (13, 1), (32, 1), (37, 1), (57, 1)] }, { coefficient := 1, powers := [(13, 1), (31, 1), (32, 1), (37, 1), (38, 1)] }],
  [{ coefficient := -1, powers := [(10, 1), (31, 1), (37, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (20, 2), (59, 1), (62, 1)] }, { coefficient := -1, powers := [(20, 1), (37, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (31, 1), (64, 1)] }, { coefficient := -1, powers := [(31, 1), (37, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (29, 1), (50, 1), (54, 1), (65, 1)] }, { coefficient := 1, powers := [(20, 1), (29, 1), (50, 1), (54, 1), (65, 1)] }, { coefficient := 1, powers := [(50, 1)] }],
  [{ coefficient := 1, powers := [(43, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (13, 1), (31, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (20, 1), (59, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (39, 1), (59, 1)] }, { coefficient := 1, powers := [(20, 1), (39, 1), (59, 1)] }, { coefficient := -1, powers := [(31, 1), (39, 1), (43, 1)] }, { coefficient := -1, powers := [(34, 1), (39, 1), (50, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (31, 1), (52, 1), (64, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1), (52, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(13, 1), (31, 1), (37, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (37, 1), (59, 1)] }, { coefficient := -1, powers := [(20, 1), (37, 1), (59, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1), (43, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (20, 2), (46, 1), (59, 1)] }, { coefficient := -1, powers := [(6, 1), (20, 1), (37, 1), (59, 1), (60, 1)] }, { coefficient := -1, powers := [(6, 1), (20, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (31, 1), (37, 1), (38, 1), (60, 1)] }, { coefficient := -1, powers := [(13, 1), (31, 1), (37, 1), (46, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (39, 1), (44, 1), (51, 1), (59, 1)] }, { coefficient := -1, powers := [(20, 1), (39, 1), (44, 1), (51, 1), (59, 1)] }, { coefficient := 1, powers := [(31, 1), (39, 1), (43, 1), (44, 1), (51, 1)] }, { coefficient := 1, powers := [(34, 1), (39, 1), (44, 1), (50, 1), (51, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (18, 1), (24, 1), (37, 1), (44, 1), (55, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (19, 1), (21, 1), (30, 1), (37, 1), (53, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (19, 1), (23, 1), (39, 1), (51, 1), (59, 1)] }, { coefficient := -1, powers := [(0, 1), (19, 1), (24, 1), (26, 1), (37, 1), (53, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (19, 1), (24, 1), (37, 1), (55, 1), (59, 1)] }, { coefficient := -1, powers := [(0, 1), (20, 1), (37, 1), (46, 1), (59, 1)] }, { coefficient := -1, powers := [(0, 1), (34, 1), (37, 1), (46, 1), (50, 1)] }, { coefficient := -1, powers := [(6, 1), (20, 2), (46, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (31, 1), (45, 1), (64, 1)] }, { coefficient := -1, powers := [(18, 1), (20, 1), (24, 1), (37, 1), (44, 1), (55, 1), (59, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (31, 1), (37, 1), (43, 1), (44, 1), (55, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (34, 1), (37, 1), (44, 1), (50, 1), (55, 1)] }, { coefficient := 1, powers := [(19, 1), (20, 1), (21, 1), (30, 1), (37, 1), (53, 1), (59, 1)] }, { coefficient := 1, powers := [(19, 1), (20, 1), (23, 1), (39, 1), (51, 1), (59, 1)] }, { coefficient := -1, powers := [(19, 1), (20, 1), (24, 1), (26, 1), (37, 1), (53, 1), (59, 1)] }, { coefficient := 1, powers := [(19, 1), (20, 1), (24, 1), (37, 1), (55, 1), (59, 1)] }, { coefficient := -1, powers := [(19, 1), (21, 1), (30, 1), (31, 1), (37, 1), (43, 1), (53, 1)] }, { coefficient := -1, powers := [(19, 1), (21, 1), (30, 1), (34, 1), (37, 1), (50, 1), (53, 1)] }, { coefficient := -1, powers := [(19, 1), (23, 1), (31, 1), (39, 1), (43, 1), (51, 1)] }, { coefficient := -1, powers := [(19, 1), (23, 1), (34, 1), (39, 1), (50, 1), (51, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (26, 1), (31, 1), (37, 1), (43, 1), (53, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (26, 1), (34, 1), (37, 1), (50, 1), (53, 1)] }, { coefficient := -1, powers := [(19, 1), (24, 1), (31, 1), (37, 1), (43, 1), (55, 1)] }, { coefficient := -1, powers := [(19, 1), (24, 1), (34, 1), (37, 1), (50, 1), (55, 1)] }, { coefficient := -1, powers := [(20, 1), (34, 1), (37, 1), (46, 1), (50, 1)] }, { coefficient := -1, powers := [(31, 1), (37, 1), (45, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (6, 1), (31, 1), (52, 1), (56, 1), (64, 1)] }, { coefficient := 1, powers := [(0, 1), (30, 1), (34, 1), (37, 1), (50, 1), (65, 1)] }, { coefficient := -1, powers := [(0, 1), (31, 1), (37, 1), (52, 1), (56, 1), (64, 1)] }, { coefficient := 1, powers := [(1, 1), (13, 1), (31, 1), (37, 1), (57, 1)] }, { coefficient := 1, powers := [(6, 2), (31, 1), (34, 1), (52, 1), (64, 1)] }, { coefficient := -1, powers := [(6, 1), (13, 1), (31, 1), (64, 1)] }, { coefficient := -1, powers := [(6, 1), (31, 1), (34, 1), (37, 1), (52, 1), (64, 1)] }, { coefficient := 1, powers := [(7, 1), (13, 1), (31, 1), (35, 1), (37, 1)] }, { coefficient := 1, powers := [(13, 1), (31, 1), (37, 1), (64, 1)] }, { coefficient := 1, powers := [(20, 1), (30, 1), (34, 1), (37, 1), (50, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (2, 1), (37, 1), (58, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (8, 1), (36, 1), (37, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (20, 1), (37, 1), (58, 1), (59, 1)] }, { coefficient := -1, powers := [(2, 1), (31, 1), (37, 1), (43, 1), (58, 1)] }, { coefficient := -1, powers := [(2, 1), (34, 1), (37, 1), (50, 1), (58, 1)] }, { coefficient := 1, powers := [(8, 1), (20, 1), (36, 1), (37, 1), (59, 1)] }, { coefficient := -1, powers := [(8, 1), (31, 1), (36, 1), (37, 1), (43, 1)] }, { coefficient := -1, powers := [(8, 1), (34, 1), (36, 1), (37, 1), (50, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (20, 1), (29, 1), (50, 1), (54, 1), (65, 1)] }, { coefficient := 1, powers := [(0, 1), (23, 1), (26, 1), (50, 1), (52, 1), (65, 1)] }, { coefficient := -1, powers := [(0, 1), (23, 1), (50, 1), (54, 1), (65, 1)] }, { coefficient := 1, powers := [(0, 1), (40, 1)] }, { coefficient := 1, powers := [(3, 1), (31, 1)] }, { coefficient := 1, powers := [(6, 1), (31, 1), (52, 1), (64, 1)] }, { coefficient := 1, powers := [(9, 1), (20, 1)] }, { coefficient := -1, powers := [(20, 2), (29, 1), (50, 1), (54, 1), (65, 1)] }, { coefficient := 1, powers := [(20, 1), (23, 1), (26, 1), (50, 1), (52, 1), (65, 1)] }, { coefficient := -1, powers := [(20, 1), (23, 1), (50, 1), (54, 1), (65, 1)] }, { coefficient := -1, powers := [(20, 1), (50, 1)] }, { coefficient := -1, powers := [(31, 1), (37, 1), (52, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (9, 1), (34, 1)] }, { coefficient := -1, powers := [(9, 1), (34, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (5, 1), (33, 1), (37, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (20, 1), (33, 1), (37, 1), (59, 1)] }, { coefficient := -1, powers := [(5, 1), (31, 1), (33, 1), (37, 1), (43, 1)] }, { coefficient := -1, powers := [(5, 1), (33, 1), (34, 1), (37, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (8, 1), (33, 1), (37, 1), (49, 1), (52, 1), (59, 1)] }, { coefficient := -1, powers := [(0, 1), (12, 1), (28, 1), (39, 1), (44, 1), (52, 1), (59, 1)] }, { coefficient := -1, powers := [(0, 1), (29, 1), (43, 1), (50, 1), (54, 1), (65, 1)] }, { coefficient := -1, powers := [(3, 1), (6, 1), (20, 1), (59, 1), (60, 1), (62, 1)] }, { coefficient := 1, powers := [(3, 1), (59, 1)] }, { coefficient := -1, powers := [(4, 1), (9, 1), (13, 1), (22, 1), (37, 1), (60, 2)] }, { coefficient := -1, powers := [(4, 1), (9, 1), (13, 1), (32, 1), (37, 1), (57, 1), (60, 1)] }, { coefficient := -1, powers := [(4, 1), (13, 1), (31, 1), (32, 1), (37, 1), (38, 1), (60, 1)] }, { coefficient := 1, powers := [(6, 1), (13, 1), (31, 1), (41, 1), (52, 1), (64, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 2), (41, 1), (59, 1), (62, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 2), (46, 1), (59, 1), (62, 1)] }, { coefficient := -1, powers := [(6, 1), (20, 1), (59, 1), (62, 1)] }, { coefficient := 1, powers := [(6, 1), (31, 1), (45, 1), (52, 1), (64, 1)] }, { coefficient := 1, powers := [(8, 1), (20, 1), (33, 1), (37, 1), (49, 1), (52, 1), (59, 1)] }, { coefficient := -1, powers := [(8, 1), (31, 1), (33, 1), (37, 1), (43, 1), (49, 1), (52, 1)] }, { coefficient := -1, powers := [(8, 1), (33, 1), (34, 1), (37, 1), (49, 1), (50, 1), (52, 1)] }, { coefficient := -1, powers := [(9, 1), (10, 1), (13, 1), (22, 1), (37, 1), (46, 1), (60, 1)] }, { coefficient := -1, powers := [(9, 1), (10, 1), (13, 1), (32, 1), (37, 1), (46, 1), (57, 1)] }, { coefficient := -1, powers := [(9, 1), (13, 1), (15, 1), (22, 1), (37, 1), (41, 1), (60, 1)] }, { coefficient := -1, powers := [(9, 1), (13, 1), (15, 1), (32, 1), (37, 1), (41, 1), (57, 1)] }, { coefficient := -1, powers := [(10, 1), (13, 1), (31, 1), (32, 1), (37, 1), (38, 1), (46, 1)] }, { coefficient := -1, powers := [(12, 1), (20, 1), (28, 1), (39, 1), (44, 1), (52, 1), (59, 1)] }, { coefficient := 1, powers := [(12, 1), (28, 1), (31, 1), (39, 1), (43, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(12, 1), (28, 1), (34, 1), (39, 1), (44, 1), (50, 1), (52, 1)] }, { coefficient := -1, powers := [(13, 1), (15, 1), (31, 1), (32, 1), (37, 1), (38, 1), (41, 1)] }, { coefficient := -1, powers := [(13, 1), (31, 1), (37, 1), (41, 1), (52, 1), (64, 1)] }, { coefficient := 1, powers := [(13, 1), (40, 1)] }, { coefficient := -1, powers := [(20, 1), (29, 1), (43, 1), (50, 1), (54, 1), (65, 1)] }, { coefficient := 1, powers := [(20, 1), (37, 1), (41, 1), (59, 1)] }, { coefficient := 1, powers := [(20, 1), (37, 1), (46, 1), (59, 1)] }, { coefficient := -1, powers := [(31, 1), (37, 1), (45, 1), (52, 1), (64, 1)] }, { coefficient := -1, powers := [(40, 1), (43, 1)] }, { coefficient := -1, powers := [(43, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (13, 1), (31, 1), (37, 1), (60, 1)] }, { coefficient := -1, powers := [(10, 1), (13, 1), (31, 1), (37, 1), (46, 1)] }, { coefficient := 1, powers := [(10, 1), (31, 1), (37, 1), (45, 1)] }, { coefficient := 1, powers := [(13, 1), (15, 1), (31, 1), (37, 1), (41, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (20, 1), (37, 1), (40, 1), (46, 1), (59, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (34, 1), (37, 1), (40, 1), (46, 1), (50, 1), (63, 1)] }, { coefficient := 1, powers := [(0, 1), (34, 1), (37, 1), (46, 1), (50, 1)] }, { coefficient := 1, powers := [(0, 1), (43, 1), (50, 1)] }, { coefficient := -1, powers := [(6, 1), (9, 1), (34, 1), (46, 1), (64, 1)] }, { coefficient := -1, powers := [(6, 1), (9, 1), (34, 1)] }, { coefficient := -1, powers := [(6, 1), (20, 2), (40, 1), (46, 1), (59, 1), (63, 1)] }, { coefficient := 1, powers := [(6, 1), (31, 1), (40, 1), (45, 1), (63, 1), (64, 1)] }, { coefficient := -1, powers := [(6, 1), (34, 1), (40, 1)] }, { coefficient := 1, powers := [(9, 1), (13, 1), (15, 1), (22, 1), (37, 1), (60, 1)] }, { coefficient := -1, powers := [(9, 1), (13, 1), (15, 1), (32, 1), (37, 1), (46, 1)] }, { coefficient := 1, powers := [(9, 1), (34, 1), (37, 1), (46, 1), (64, 1)] }, { coefficient := 1, powers := [(13, 1), (15, 1), (22, 1), (37, 1), (40, 1), (60, 1)] }, { coefficient := -1, powers := [(13, 1), (15, 1), (32, 1), (37, 1), (40, 1), (46, 1)] }, { coefficient := -1, powers := [(20, 1), (34, 1), (37, 1), (40, 1), (46, 1), (50, 1), (63, 1)] }, { coefficient := 1, powers := [(20, 1), (34, 1), (37, 1), (46, 1), (50, 1)] }, { coefficient := 1, powers := [(20, 1), (43, 1), (50, 1)] }, { coefficient := -1, powers := [(31, 1), (37, 1), (40, 1), (45, 1), (63, 1), (64, 1)] }]
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
    (values : Fin 66 → R) :
    ¬ ∀ index : Fin 50,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component37.SelectedLeafB4_4_2_1.selectedHasNoCommonZero

end Krenn.Component37.SelectedLeafB4_4_2_1
