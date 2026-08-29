import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component11.SelectedLeafB6_6_5_3

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "fe15434fbdcb76a231db68a675d9fb57b1a68f0ac83961ff288634c2dfb1b169"
def certificateSHA256 : String := "d7ec5718fab19ec10908ec46d69235f10af95e7a01ee814fe06f87805983c217"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 31 → Fin 675 := ![
  6,
  8,
  16,
  29,
  167,
  168,
  207,
  262,
  286,
  322,
  328,
  329,
  330,
  336,
  341,
  448,
  453,
  462,
  500,
  550,
  588,
  589,
  612,
  620,
  661,
  662,
  665,
  668,
  670,
  671,
  672
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 31 → SparsePoly (Fin 69) := ![
  [{ coefficient := 1, powers := [(5, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (33, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(33, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (24, 1)] }, { coefficient := 1, powers := [(15, 1), (18, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (25, 1)] }, { coefficient := 1, powers := [(15, 1), (18, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (26, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (18, 1), (56, 1)] }, { coefficient := 1, powers := [(12, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (24, 1), (41, 1)] }, { coefficient := 1, powers := [(17, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1)] }, { coefficient := 1, powers := [(18, 1), (44, 1)] }, { coefficient := 1, powers := [(24, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (49, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1)] }, { coefficient := 1, powers := [(17, 1), (23, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1)] }, { coefficient := 1, powers := [(12, 1), (30, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (60, 1)] }, { coefficient := 1, powers := [(12, 1), (49, 1)] }, { coefficient := 1, powers := [(17, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (47, 1)] }, { coefficient := 1, powers := [(16, 1), (41, 1)] }, { coefficient := 1, powers := [(16, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (54, 1)] }, { coefficient := 1, powers := [(30, 1), (42, 1)] }, { coefficient := 1, powers := [(33, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (53, 1)] }, { coefficient := 1, powers := [(3, 1), (25, 1), (59, 1)] }, { coefficient := 1, powers := [(18, 1), (53, 1)] }, { coefficient := 1, powers := [(25, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (60, 1)] }, { coefficient := 1, powers := [(12, 1), (25, 1), (47, 1)] }, { coefficient := 1, powers := [(12, 1), (57, 1)] }, { coefficient := 1, powers := [(17, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1), (53, 1)] }, { coefficient := 1, powers := [(18, 1), (44, 1), (53, 1)] }, { coefficient := 1, powers := [(18, 1), (57, 1)] }, { coefficient := 1, powers := [(25, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (24, 1), (59, 1)] }, { coefficient := 1, powers := [(11, 1), (24, 1), (46, 1)] }, { coefficient := 1, powers := [(15, 1), (24, 1), (41, 1)] }, { coefficient := 1, powers := [(15, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (25, 1), (47, 1)] }, { coefficient := 1, powers := [(11, 1), (57, 1)] }, { coefficient := 1, powers := [(16, 1), (25, 1), (41, 1)] }, { coefficient := 1, powers := [(16, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1)] }, { coefficient := 1, powers := [(6, 1), (59, 1)] }, { coefficient := 1, powers := [(24, 1), (41, 1)] }, { coefficient := 1, powers := [(24, 1), (46, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (52, 1)] }, { coefficient := 1, powers := [(3, 1), (59, 1)] }, { coefficient := 1, powers := [(18, 1), (52, 1)] }, { coefficient := 1, powers := [(18, 1), (56, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(4, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (59, 1)] }, { coefficient := 1, powers := [(11, 1), (46, 1)] }, { coefficient := 1, powers := [(11, 1), (56, 1)] }, { coefficient := 1, powers := [(15, 1), (41, 1)] }, { coefficient := 1, powers := [(15, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (37, 1), (59, 1)] }, { coefficient := 1, powers := [(1, 1)] }, { coefficient := 1, powers := [(11, 1), (26, 1)] }, { coefficient := 1, powers := [(11, 1), (35, 1), (37, 1)] }, { coefficient := 1, powers := [(15, 1), (20, 1)] }, { coefficient := 1, powers := [(15, 1), (32, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (38, 1), (59, 1)] }, { coefficient := 1, powers := [(1, 1), (41, 1), (56, 1)] }, { coefficient := 1, powers := [(1, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(4, 1), (27, 1), (59, 1)] }, { coefficient := 1, powers := [(4, 1), (32, 1), (56, 1)] }, { coefficient := 1, powers := [(4, 1), (35, 1), (52, 1)] }, { coefficient := 1, powers := [(7, 1), (21, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (32, 1), (46, 1)] }, { coefficient := 1, powers := [(7, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(11, 1), (21, 1), (56, 1)] }, { coefficient := 1, powers := [(11, 1), (27, 1), (46, 1)] }, { coefficient := 1, powers := [(11, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(15, 1), (21, 1), (52, 1)] }, { coefficient := 1, powers := [(15, 1), (27, 1), (41, 1)] }, { coefficient := 1, powers := [(15, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (39, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (42, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (49, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (23, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (49, 1)] }, { coefficient := 1, powers := [(8, 1), (36, 1), (42, 1)] }, { coefficient := 1, powers := [(12, 1), (23, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1), (30, 1), (49, 1)] }, { coefficient := 1, powers := [(12, 1), (36, 1), (39, 1)] }, { coefficient := 1, powers := [(17, 1), (23, 1), (54, 1)] }, { coefficient := 1, powers := [(17, 1), (30, 1), (42, 1)] }, { coefficient := 1, powers := [(17, 1), (33, 1), (39, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(42, 1)] }],
  [{ coefficient := 1, powers := [(56, 1)] }],
  [{ coefficient := 1, powers := [(57, 1), (66, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(24, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 31 → SparsePoly (Fin 69) := ![
  [{ coefficient := -1, powers := [(1, 1), (33, 1), (37, 1), (46, 1), (52, 1), (57, 1)] }, { coefficient := 1, powers := [(1, 1), (33, 1), (38, 1), (57, 1)] }, { coefficient := -1, powers := [(4, 1), (26, 1), (33, 1), (52, 1), (57, 1)] }, { coefficient := 1, powers := [(6, 1), (11, 1), (26, 1), (33, 1), (46, 1), (52, 1), (57, 1)] }, { coefficient := 1, powers := [(7, 1), (21, 1), (33, 1), (57, 1)] }, { coefficient := -1, powers := [(7, 1), (27, 1), (33, 1), (57, 1)] }, { coefficient := 1, powers := [(11, 1), (26, 1), (33, 1), (37, 1), (46, 1), (52, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (32, 1), (46, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (41, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (23, 1), (25, 1), (37, 1), (46, 1), (52, 1), (59, 1)] }, { coefficient := -1, powers := [(1, 1), (23, 1), (25, 1), (38, 1), (59, 1)] }, { coefficient := -1, powers := [(4, 1), (23, 1), (25, 1), (35, 1), (52, 1), (57, 1), (66, 1)] }, { coefficient := -1, powers := [(6, 1), (11, 1), (23, 1), (25, 1), (26, 1), (46, 1), (52, 1), (59, 1)] }, { coefficient := -1, powers := [(7, 1), (21, 1), (23, 1), (25, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (23, 1), (25, 1), (27, 1), (59, 1)] }, { coefficient := -1, powers := [(7, 1), (23, 1), (25, 1), (32, 1), (46, 1)] }, { coefficient := -1, powers := [(7, 1), (23, 1), (25, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(11, 1), (23, 1), (25, 1), (35, 1), (37, 1), (46, 1), (52, 1), (57, 1), (66, 1)] }, { coefficient := -1, powers := [(11, 1), (23, 1), (25, 1), (35, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (11, 1), (35, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [(26, 1), (44, 1), (46, 2), (52, 1), (53, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(26, 1), (44, 1), (46, 2), (52, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (33, 1), (52, 1), (57, 1)] }, { coefficient := -1, powers := [(11, 1), (33, 1), (37, 1), (46, 1), (52, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (30, 1), (37, 1), (46, 1), (49, 1), (52, 1), (59, 1)] }, { coefficient := -1, powers := [(1, 1), (30, 1), (38, 1), (49, 1), (59, 1)] }, { coefficient := -1, powers := [(1, 1), (36, 1), (37, 1), (39, 1), (46, 1), (52, 1), (59, 1)] }, { coefficient := 1, powers := [(1, 1), (36, 1), (38, 1), (39, 1), (59, 1)] }, { coefficient := -1, powers := [(4, 1), (30, 1), (35, 1), (49, 1), (52, 1), (57, 1), (66, 1)] }, { coefficient := 1, powers := [(4, 1), (35, 1), (36, 1), (39, 1), (52, 1), (57, 1), (66, 1)] }, { coefficient := -1, powers := [(6, 1), (11, 1), (26, 1), (30, 1), (46, 1), (49, 1), (52, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (11, 1), (26, 1), (36, 1), (39, 1), (46, 1), (52, 1), (59, 1)] }, { coefficient := -1, powers := [(7, 1), (21, 1), (30, 1), (49, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (21, 1), (36, 1), (39, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (27, 1), (30, 1), (49, 1), (59, 1)] }, { coefficient := -1, powers := [(7, 1), (27, 1), (36, 1), (39, 1), (59, 1)] }, { coefficient := -1, powers := [(7, 1), (30, 1), (32, 1), (46, 1), (49, 1)] }, { coefficient := -1, powers := [(7, 1), (30, 1), (35, 1), (41, 1), (49, 1)] }, { coefficient := 1, powers := [(7, 1), (32, 1), (36, 1), (39, 1), (46, 1)] }, { coefficient := 1, powers := [(7, 1), (35, 1), (36, 1), (39, 1), (41, 1)] }, { coefficient := 1, powers := [(11, 1), (30, 1), (35, 1), (37, 1), (46, 1), (49, 1), (52, 1), (57, 1), (66, 1)] }, { coefficient := -1, powers := [(11, 1), (30, 1), (35, 1), (38, 1), (49, 1)] }, { coefficient := -1, powers := [(11, 1), (35, 1), (36, 1), (37, 1), (39, 1), (46, 1), (52, 1), (57, 1), (66, 1)] }, { coefficient := 1, powers := [(11, 1), (35, 1), (36, 1), (38, 1), (39, 1)] }],
  [{ coefficient := 2, powers := [(1, 1), (23, 1), (37, 1), (46, 1), (52, 1), (54, 1), (59, 1)] }, { coefficient := -2, powers := [(1, 1), (23, 1), (38, 1), (54, 1), (59, 1)] }, { coefficient := -2, powers := [(4, 1), (23, 1), (35, 1), (52, 1), (54, 1), (57, 1), (66, 1)] }, { coefficient := -2, powers := [(6, 1), (11, 1), (23, 1), (26, 1), (46, 1), (52, 1), (54, 1), (59, 1)] }, { coefficient := -2, powers := [(7, 1), (21, 1), (23, 1), (54, 1), (59, 1)] }, { coefficient := 2, powers := [(7, 1), (23, 1), (27, 1), (54, 1), (59, 1)] }, { coefficient := -2, powers := [(7, 1), (23, 1), (32, 1), (46, 1), (54, 1)] }, { coefficient := -2, powers := [(7, 1), (23, 1), (35, 1), (41, 1), (54, 1)] }, { coefficient := 2, powers := [(11, 1), (23, 1), (35, 1), (37, 1), (46, 1), (52, 1), (54, 1), (57, 1), (66, 1)] }, { coefficient := -2, powers := [(11, 1), (23, 1), (35, 1), (38, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (26, 1), (46, 2), (52, 1), (53, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(1, 1), (37, 1), (46, 1), (52, 1), (54, 1), (59, 1)] }, { coefficient := 1, powers := [(1, 1), (38, 1), (54, 1), (59, 1)] }, { coefficient := 1, powers := [(4, 1), (35, 1), (52, 1), (54, 1), (57, 1), (66, 1)] }, { coefficient := 1, powers := [(6, 1), (11, 1), (26, 1), (46, 1), (52, 1), (54, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (21, 1), (54, 1), (59, 1)] }, { coefficient := -1, powers := [(7, 1), (27, 1), (54, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (32, 1), (46, 1), (54, 1)] }, { coefficient := 1, powers := [(7, 1), (35, 1), (41, 1), (54, 1)] }, { coefficient := -1, powers := [(11, 1), (35, 1), (37, 1), (46, 1), (52, 1), (54, 1), (57, 1), (66, 1)] }, { coefficient := 1, powers := [(11, 1), (35, 1), (38, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(1, 1), (37, 1), (46, 1), (49, 1), (52, 1), (59, 1)] }, { coefficient := 1, powers := [(1, 1), (38, 1), (49, 1), (59, 1)] }, { coefficient := 1, powers := [(4, 1), (35, 1), (49, 1), (52, 1), (57, 1), (66, 1)] }, { coefficient := 1, powers := [(6, 1), (11, 1), (26, 1), (46, 1), (49, 1), (52, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (21, 1), (49, 1), (59, 1)] }, { coefficient := -1, powers := [(7, 1), (27, 1), (49, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (32, 1), (46, 1), (49, 1)] }, { coefficient := 1, powers := [(7, 1), (35, 1), (41, 1), (49, 1)] }, { coefficient := -1, powers := [(11, 1), (35, 1), (37, 1), (46, 1), (49, 1), (52, 1), (57, 1), (66, 1)] }, { coefficient := 1, powers := [(11, 1), (35, 1), (38, 1), (49, 1)] }],
  [{ coefficient := -1, powers := [(1, 1), (30, 1), (37, 1), (46, 1), (52, 1), (59, 1)] }, { coefficient := 1, powers := [(1, 1), (30, 1), (38, 1), (59, 1)] }, { coefficient := 1, powers := [(4, 1), (30, 1), (35, 1), (52, 1), (57, 1), (66, 1)] }, { coefficient := 1, powers := [(6, 1), (11, 1), (26, 1), (30, 1), (46, 1), (52, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (21, 1), (30, 1), (59, 1)] }, { coefficient := -1, powers := [(7, 1), (27, 1), (30, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (30, 1), (32, 1), (46, 1)] }, { coefficient := 1, powers := [(7, 1), (30, 1), (35, 1), (41, 1)] }, { coefficient := -1, powers := [(11, 1), (30, 1), (35, 1), (37, 1), (46, 1), (52, 1), (57, 1), (66, 1)] }, { coefficient := 1, powers := [(11, 1), (30, 1), (35, 1), (38, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (25, 1), (26, 1), (46, 2), (52, 1), (66, 1)] }, { coefficient := -1, powers := [(18, 1), (25, 1), (26, 1), (46, 2), (52, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(1, 1), (17, 1), (37, 1), (46, 1), (52, 1), (59, 1)] }, { coefficient := 1, powers := [(1, 1), (17, 1), (38, 1), (59, 1)] }, { coefficient := 1, powers := [(4, 1), (17, 1), (35, 1), (52, 1), (57, 1), (66, 1)] }, { coefficient := 1, powers := [(6, 1), (11, 1), (17, 1), (26, 1), (46, 1), (52, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (17, 1), (21, 1), (59, 1)] }, { coefficient := -1, powers := [(7, 1), (17, 1), (27, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (17, 1), (32, 1), (46, 1)] }, { coefficient := 1, powers := [(7, 1), (17, 1), (35, 1), (41, 1)] }, { coefficient := -1, powers := [(11, 1), (17, 1), (35, 1), (37, 1), (46, 1), (52, 1), (57, 1), (66, 1)] }, { coefficient := 1, powers := [(11, 1), (17, 1), (35, 1), (38, 1)] }],
  [{ coefficient := -1, powers := [(16, 1), (26, 1), (46, 2), (52, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(1, 1), (23, 1), (37, 1), (46, 1), (52, 1), (59, 1)] }, { coefficient := 1, powers := [(1, 1), (23, 1), (38, 1), (59, 1)] }, { coefficient := 1, powers := [(4, 1), (23, 1), (35, 1), (52, 1), (57, 1), (66, 1)] }, { coefficient := 1, powers := [(6, 1), (11, 1), (23, 1), (26, 1), (46, 1), (52, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (21, 1), (23, 1), (59, 1)] }, { coefficient := -1, powers := [(7, 1), (23, 1), (27, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (23, 1), (32, 1), (46, 1)] }, { coefficient := 1, powers := [(7, 1), (23, 1), (35, 1), (41, 1)] }, { coefficient := -1, powers := [(11, 1), (23, 1), (35, 1), (37, 1), (46, 1), (52, 1), (57, 1), (66, 1)] }, { coefficient := 1, powers := [(11, 1), (23, 1), (35, 1), (38, 1)] }],
  [{ coefficient := -1, powers := [(11, 1), (26, 1), (46, 2), (52, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(20, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(21, 1), (52, 1)] }, { coefficient := -1, powers := [(27, 1), (52, 1)] }, { coefficient := -1, powers := [(32, 1), (37, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (26, 1), (46, 2), (52, 1), (66, 1)] }, { coefficient := 1, powers := [(18, 1), (26, 1), (46, 2), (52, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(11, 1), (26, 1), (46, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (25, 1), (26, 1), (46, 2), (52, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(27, 1)] }],
  [{ coefficient := 1, powers := [(46, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1), (37, 1), (46, 1), (52, 1), (59, 1)] }, { coefficient := -1, powers := [(1, 1), (38, 1), (59, 1)] }, { coefficient := -1, powers := [(4, 1), (35, 1), (52, 1), (57, 1), (66, 1)] }, { coefficient := -1, powers := [(6, 1), (11, 1), (26, 1), (46, 1), (52, 1), (59, 1)] }, { coefficient := -1, powers := [(7, 1), (21, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (27, 1), (59, 1)] }, { coefficient := -1, powers := [(7, 1), (32, 1), (46, 1)] }, { coefficient := -1, powers := [(7, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(11, 1), (35, 1), (37, 1), (46, 1), (52, 1), (57, 1), (66, 1)] }, { coefficient := -1, powers := [(11, 1), (35, 1), (38, 1)] }],
  [{ coefficient := -1, powers := [(1, 1), (37, 1), (39, 1), (46, 1), (52, 1), (59, 1), (60, 1)] }, { coefficient := 1, powers := [(1, 1), (37, 1), (46, 1), (49, 1), (52, 1), (54, 1), (59, 1)] }, { coefficient := 1, powers := [(1, 1), (38, 1), (39, 1), (59, 1), (60, 1)] }, { coefficient := -1, powers := [(1, 1), (38, 1), (49, 1), (54, 1), (59, 1)] }, { coefficient := 1, powers := [(4, 1), (35, 1), (39, 1), (52, 1), (57, 1), (60, 1), (66, 1)] }, { coefficient := -1, powers := [(4, 1), (35, 1), (49, 1), (52, 1), (54, 1), (57, 1), (66, 1)] }, { coefficient := 1, powers := [(6, 1), (11, 1), (26, 1), (39, 1), (46, 1), (52, 1), (59, 1), (60, 1)] }, { coefficient := -1, powers := [(6, 1), (11, 1), (26, 1), (46, 1), (49, 1), (52, 1), (54, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (21, 1), (39, 1), (59, 1), (60, 1)] }, { coefficient := -1, powers := [(7, 1), (21, 1), (49, 1), (54, 1), (59, 1)] }, { coefficient := -1, powers := [(7, 1), (27, 1), (39, 1), (59, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (27, 1), (49, 1), (54, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (32, 1), (39, 1), (46, 1), (60, 1)] }, { coefficient := -1, powers := [(7, 1), (32, 1), (46, 1), (49, 1), (54, 1)] }, { coefficient := 1, powers := [(7, 1), (35, 1), (39, 1), (41, 1), (60, 1)] }, { coefficient := -1, powers := [(7, 1), (35, 1), (41, 1), (49, 1), (54, 1)] }, { coefficient := -1, powers := [(11, 1), (35, 1), (37, 1), (39, 1), (46, 1), (52, 1), (57, 1), (60, 1), (66, 1)] }, { coefficient := 1, powers := [(11, 1), (35, 1), (37, 1), (46, 1), (49, 1), (52, 1), (54, 1), (57, 1), (66, 1)] }, { coefficient := 1, powers := [(11, 1), (35, 1), (38, 1), (39, 1), (60, 1)] }, { coefficient := -1, powers := [(11, 1), (35, 1), (38, 1), (49, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(1, 1), (2, 1), (37, 1), (46, 1), (52, 1), (57, 1), (59, 1)] }, { coefficient := 1, powers := [(1, 1), (2, 1), (38, 1), (57, 1), (59, 1)] }, { coefficient := -1, powers := [(1, 1), (8, 1), (36, 1), (37, 1), (46, 1), (52, 1), (59, 1)] }, { coefficient := 1, powers := [(1, 1), (8, 1), (36, 1), (38, 1), (59, 1)] }, { coefficient := 1, powers := [(1, 1), (17, 1), (30, 1), (37, 1), (46, 1), (52, 1), (59, 1)] }, { coefficient := -1, powers := [(1, 1), (17, 1), (30, 1), (38, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (4, 1), (35, 1), (52, 1), (57, 2), (66, 1)] }, { coefficient := 1, powers := [(2, 1), (6, 1), (11, 1), (26, 1), (46, 1), (52, 1), (57, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (7, 1), (21, 1), (57, 1), (59, 1)] }, { coefficient := -1, powers := [(2, 1), (7, 1), (27, 1), (57, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (7, 1), (32, 1), (46, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (7, 1), (35, 1), (41, 1), (57, 1)] }, { coefficient := -1, powers := [(2, 1), (11, 1), (35, 1), (37, 1), (46, 1), (52, 1), (57, 2), (66, 1)] }, { coefficient := 1, powers := [(2, 1), (11, 1), (35, 1), (38, 1), (57, 1)] }, { coefficient := 1, powers := [(4, 1), (8, 1), (35, 1), (36, 1), (52, 1), (57, 1), (66, 1)] }, { coefficient := -1, powers := [(4, 1), (17, 1), (30, 1), (35, 1), (52, 1), (57, 1), (66, 1)] }, { coefficient := 1, powers := [(6, 1), (8, 1), (11, 1), (26, 1), (36, 1), (46, 1), (52, 1), (59, 1)] }, { coefficient := -1, powers := [(6, 1), (11, 1), (17, 1), (26, 1), (30, 1), (46, 1), (52, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (8, 1), (21, 1), (36, 1), (59, 1)] }, { coefficient := -1, powers := [(7, 1), (8, 1), (27, 1), (36, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (8, 1), (32, 1), (36, 1), (46, 1)] }, { coefficient := 1, powers := [(7, 1), (8, 1), (35, 1), (36, 1), (41, 1)] }, { coefficient := -1, powers := [(7, 1), (17, 1), (21, 1), (30, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (17, 1), (27, 1), (30, 1), (59, 1)] }, { coefficient := -1, powers := [(7, 1), (17, 1), (30, 1), (32, 1), (46, 1)] }, { coefficient := -1, powers := [(7, 1), (17, 1), (30, 1), (35, 1), (41, 1)] }, { coefficient := -1, powers := [(8, 1), (11, 1), (35, 1), (36, 1), (37, 1), (46, 1), (52, 1), (57, 1), (66, 1)] }, { coefficient := 1, powers := [(8, 1), (11, 1), (35, 1), (36, 1), (38, 1)] }, { coefficient := 1, powers := [(11, 1), (17, 1), (30, 1), (35, 1), (37, 1), (46, 1), (52, 1), (57, 1), (66, 1)] }, { coefficient := -1, powers := [(11, 1), (17, 1), (30, 1), (35, 1), (38, 1)] }],
  [{ coefficient := -1, powers := [(1, 1), (12, 1), (18, 1), (30, 1), (37, 1), (46, 1), (49, 1), (52, 1), (59, 1)] }, { coefficient := 1, powers := [(1, 1), (12, 1), (18, 1), (30, 1), (38, 1), (49, 1), (59, 1)] }, { coefficient := 1, powers := [(1, 1), (12, 1), (18, 1), (36, 1), (37, 1), (39, 1), (46, 1), (52, 1), (59, 1)] }, { coefficient := -1, powers := [(1, 1), (12, 1), (18, 1), (36, 1), (38, 1), (39, 1), (59, 1)] }, { coefficient := 1, powers := [(1, 1), (41, 1)] }, { coefficient := 1, powers := [(4, 1), (12, 1), (18, 1), (30, 1), (35, 1), (49, 1), (52, 1), (57, 1), (66, 1)] }, { coefficient := -1, powers := [(4, 1), (12, 1), (18, 1), (35, 1), (36, 1), (39, 1), (52, 1), (57, 1), (66, 1)] }, { coefficient := 1, powers := [(4, 1), (32, 1)] }, { coefficient := 1, powers := [(6, 1), (11, 1), (12, 1), (18, 1), (26, 1), (30, 1), (46, 1), (49, 1), (52, 1), (59, 1)] }, { coefficient := -1, powers := [(6, 1), (11, 1), (12, 1), (18, 1), (26, 1), (36, 1), (39, 1), (46, 1), (52, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (12, 1), (18, 1), (21, 1), (30, 1), (49, 1), (59, 1)] }, { coefficient := -1, powers := [(7, 1), (12, 1), (18, 1), (21, 1), (36, 1), (39, 1), (59, 1)] }, { coefficient := -1, powers := [(7, 1), (12, 1), (18, 1), (27, 1), (30, 1), (49, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (12, 1), (18, 1), (27, 1), (36, 1), (39, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (12, 1), (18, 1), (30, 1), (32, 1), (46, 1), (49, 1)] }, { coefficient := 1, powers := [(7, 1), (12, 1), (18, 1), (30, 1), (35, 1), (41, 1), (49, 1)] }, { coefficient := -1, powers := [(7, 1), (12, 1), (18, 1), (32, 1), (36, 1), (39, 1), (46, 1)] }, { coefficient := -1, powers := [(7, 1), (12, 1), (18, 1), (35, 1), (36, 1), (39, 1), (41, 1)] }, { coefficient := -1, powers := [(11, 1), (12, 1), (18, 1), (30, 1), (35, 1), (37, 1), (46, 1), (49, 1), (52, 1), (57, 1), (66, 1)] }, { coefficient := 1, powers := [(11, 1), (12, 1), (18, 1), (30, 1), (35, 1), (38, 1), (49, 1)] }, { coefficient := 1, powers := [(11, 1), (12, 1), (18, 1), (35, 1), (36, 1), (37, 1), (39, 1), (46, 1), (52, 1), (57, 1), (66, 1)] }, { coefficient := -1, powers := [(11, 1), (12, 1), (18, 1), (35, 1), (36, 1), (38, 1), (39, 1)] }, { coefficient := 1, powers := [(11, 1), (21, 1)] }, { coefficient := -1, powers := [(11, 1), (27, 1)] }, { coefficient := -1, powers := [(16, 1), (18, 1), (25, 1), (26, 1), (46, 2), (52, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (11, 1), (26, 1), (46, 2), (52, 1)] }, { coefficient := 1, powers := [(4, 1), (5, 1), (33, 1), (35, 1), (52, 1), (57, 1)] }, { coefficient := -1, powers := [(4, 1), (35, 1), (52, 1)] }, { coefficient := -1, powers := [(5, 1), (11, 1), (33, 1), (35, 1), (37, 1), (46, 1), (52, 1), (57, 1)] }, { coefficient := 1, powers := [(11, 1), (35, 1), (37, 1), (46, 1), (52, 1)] }],
  [{ coefficient := -2, powers := [(1, 1), (17, 1), (23, 1), (37, 1), (41, 1), (46, 1), (52, 1), (54, 1), (59, 1)] }, { coefficient := 2, powers := [(1, 1), (17, 1), (23, 1), (38, 1), (41, 1), (54, 1), (59, 1)] }, { coefficient := 2, powers := [(4, 1), (17, 1), (23, 1), (35, 1), (41, 1), (52, 1), (54, 1), (57, 1), (66, 1)] }, { coefficient := 1, powers := [(4, 1), (20, 1), (46, 1), (52, 1), (59, 1)] }, { coefficient := -1, powers := [(4, 1), (21, 1), (52, 1), (59, 1)] }, { coefficient := 1, powers := [(4, 1), (27, 1), (52, 1), (59, 1)] }, { coefficient := 1, powers := [(4, 1), (32, 1), (37, 1), (46, 1), (52, 1), (59, 1)] }, { coefficient := -1, powers := [(4, 1), (32, 1), (38, 1), (59, 1)] }, { coefficient := 2, powers := [(6, 1), (11, 1), (17, 1), (23, 1), (26, 1), (41, 1), (46, 1), (52, 1), (54, 1), (59, 1)] }, { coefficient := 2, powers := [(7, 1), (17, 1), (21, 1), (23, 1), (41, 1), (54, 1), (59, 1)] }, { coefficient := -2, powers := [(7, 1), (17, 1), (23, 1), (27, 1), (41, 1), (54, 1), (59, 1)] }, { coefficient := 2, powers := [(7, 1), (17, 1), (23, 1), (32, 1), (41, 1), (46, 1), (54, 1)] }, { coefficient := 2, powers := [(7, 1), (17, 1), (23, 1), (35, 1), (41, 2), (54, 1)] }, { coefficient := -2, powers := [(11, 1), (17, 1), (23, 1), (35, 1), (37, 1), (41, 1), (46, 1), (52, 1), (54, 1), (57, 1), (66, 1)] }, { coefficient := 2, powers := [(11, 1), (17, 1), (23, 1), (35, 1), (38, 1), (41, 1), (54, 1)] }, { coefficient := 1, powers := [(11, 1), (20, 1), (46, 2), (52, 1)] }, { coefficient := -1, powers := [(11, 1), (21, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(11, 1), (26, 1), (41, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(11, 1), (26, 1), (46, 2), (52, 1)] }, { coefficient := 1, powers := [(11, 1), (27, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(11, 1), (32, 1), (37, 1), (46, 2), (52, 1)] }, { coefficient := -1, powers := [(11, 1), (32, 1), (38, 1), (46, 1)] }, { coefficient := 1, powers := [(15, 1), (20, 1), (41, 1), (46, 1), (52, 1)] }, { coefficient := -1, powers := [(15, 1), (21, 1), (41, 1), (52, 1)] }, { coefficient := 1, powers := [(15, 1), (27, 1), (41, 1), (52, 1)] }, { coefficient := 1, powers := [(15, 1), (32, 1), (37, 1), (41, 1), (46, 1), (52, 1)] }, { coefficient := -1, powers := [(15, 1), (32, 1), (38, 1), (41, 1)] }]
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
    (values : Fin 69 → R) :
    ¬ ∀ index : Fin 31,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component11.SelectedLeafB6_6_5_3.selectedHasNoCommonZero

end Krenn.Component11.SelectedLeafB6_6_5_3
