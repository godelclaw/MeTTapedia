import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component37.SelectedLeafB6_1_6_1

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "0474a179336e312eb3a60c27bed03509a861572917f253a0172b09b3d4849fed"
def certificateSHA256 : String := "00cf4df6c647602e88dd991d21f240c0176ebf4a2862bce90aff1d558470452d"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 27 → Fin 670 := ![
  2,
  3,
  147,
  151,
  298,
  299,
  303,
  312,
  318,
  354,
  505,
  580,
  583,
  602,
  603,
  605,
  606,
  655,
  656,
  658,
  659,
  661,
  662,
  665,
  667,
  668,
  669
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 27 → SparsePoly (Fin 68) := ![
  [{ coefficient := 1, powers := [(1, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (31, 1)] }, { coefficient := 1, powers := [(15, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (30, 1)] }, { coefficient := 1, powers := [(30, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (46, 1)] }, { coefficient := 1, powers := [(4, 1), (35, 1)] }, { coefficient := 1, powers := [(15, 1), (22, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (52, 1)] }, { coefficient := 1, powers := [(7, 1), (32, 1)] }, { coefficient := 1, powers := [(10, 1), (27, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (46, 1)] }, { coefficient := 1, powers := [(9, 1), (57, 1)] }, { coefficient := 1, powers := [(31, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (54, 1)] }, { coefficient := 1, powers := [(30, 1), (41, 1)] }, { coefficient := 1, powers := [(30, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (37, 1), (59, 1)] }, { coefficient := 1, powers := [(1, 1), (40, 1), (56, 1)] }, { coefficient := 1, powers := [(1, 1), (43, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (31, 1), (57, 1)] }, { coefficient := 1, powers := [(7, 1), (31, 1), (46, 1)] }, { coefficient := 1, powers := [(15, 1), (31, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (25, 1), (60, 1)] }, { coefficient := 1, powers := [(10, 1), (25, 1), (46, 1)] }, { coefficient := 1, powers := [(15, 1), (25, 1), (41, 1)] }, { coefficient := 1, powers := [(15, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1)] }, { coefficient := 1, powers := [(6, 1), (60, 1)] }, { coefficient := 1, powers := [(25, 1), (41, 1)] }, { coefficient := 1, powers := [(25, 1), (46, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (31, 1), (57, 1)] }, { coefficient := 1, powers := [(9, 1), (20, 1), (57, 1)] }, { coefficient := 1, powers := [(9, 1)] }, { coefficient := 1, powers := [(40, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1)] }, { coefficient := 1, powers := [(3, 1), (34, 1)] }, { coefficient := 1, powers := [(13, 1), (20, 1)] }, { coefficient := 1, powers := [(20, 1), (56, 1)] }, { coefficient := 1, powers := [(25, 1), (43, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (50, 1)] }, { coefficient := 1, powers := [(6, 1), (31, 1)] }, { coefficient := 1, powers := [(9, 1), (25, 1)] }, { coefficient := 1, powers := [(20, 1), (50, 1)] }, { coefficient := 1, powers := [(25, 1), (40, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (52, 1)] }, { coefficient := 1, powers := [(22, 1), (57, 1)] }, { coefficient := 1, powers := [(27, 1), (41, 1)] }, { coefficient := 1, powers := [(27, 1), (46, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1)] }, { coefficient := 1, powers := [(35, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (37, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1)] }, { coefficient := 1, powers := [(3, 1), (25, 1), (60, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1), (60, 1)] }, { coefficient := 1, powers := [(20, 1)] }, { coefficient := 1, powers := [(25, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (37, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (40, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (43, 1), (50, 1)] }, { coefficient := 1, powers := [(3, 1), (25, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (31, 1), (56, 1)] }, { coefficient := 1, powers := [(3, 1), (34, 1), (50, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (31, 1), (43, 1)] }, { coefficient := 1, powers := [(6, 1), (34, 1), (40, 1)] }, { coefficient := 1, powers := [(9, 1), (20, 1), (56, 1)] }, { coefficient := 1, powers := [(9, 1), (25, 1), (43, 1)] }, { coefficient := 1, powers := [(9, 1), (34, 1), (37, 1)] }, { coefficient := 1, powers := [(13, 1), (20, 1), (50, 1)] }, { coefficient := 1, powers := [(13, 1), (25, 1), (40, 1)] }, { coefficient := 1, powers := [(13, 1), (31, 1), (37, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1), (38, 1), (60, 1)] }, { coefficient := 1, powers := [(1, 1), (41, 1), (57, 1)] }, { coefficient := 1, powers := [(1, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(4, 1), (27, 1), (60, 1)] }, { coefficient := 1, powers := [(4, 1), (32, 1), (57, 1)] }, { coefficient := 1, powers := [(4, 1), (35, 1), (52, 1)] }, { coefficient := 1, powers := [(7, 1), (22, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (32, 1), (46, 1)] }, { coefficient := 1, powers := [(7, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(10, 1), (22, 1), (57, 1)] }, { coefficient := 1, powers := [(10, 1), (27, 1), (46, 1)] }, { coefficient := 1, powers := [(10, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(15, 1), (22, 1), (52, 1)] }, { coefficient := 1, powers := [(15, 1), (27, 1), (41, 1)] }, { coefficient := 1, powers := [(15, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(40, 1)] }],
  [{ coefficient := 1, powers := [(41, 1)] }],
  [{ coefficient := 1, powers := [(57, 1), (66, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(25, 1)] }],
  [{ coefficient := 1, powers := [(27, 1)] }],
  [{ coefficient := 1, powers := [(30, 1), (67, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 27 → SparsePoly (Fin 68) := ![
  [{ coefficient := -2, powers := [(0, 1), (43, 1), (63, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1), (43, 1), (60, 1), (63, 1)] }, { coefficient := -1, powers := [(20, 1), (43, 1), (63, 1)] }, { coefficient := -1, powers := [(20, 1), (56, 1), (63, 1)] }, { coefficient := -1, powers := [(34, 1), (37, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (6, 1), (20, 2), (29, 1), (59, 1), (62, 1), (63, 1), (67, 1)] }, { coefficient := 1, powers := [(1, 1), (13, 1), (29, 1), (31, 1), (37, 1), (52, 1), (63, 1), (67, 1)] }, { coefficient := -1, powers := [(1, 1), (29, 1), (31, 1), (37, 1), (43, 1), (52, 1), (63, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (13, 1), (22, 1), (32, 1), (37, 1), (63, 1)] }, { coefficient := -1, powers := [(10, 1), (22, 1), (32, 1), (37, 1), (43, 1), (63, 1)] }, { coefficient := 1, powers := [(13, 1), (22, 1), (37, 1), (60, 1)] }, { coefficient := -1, powers := [(13, 1), (32, 1), (37, 1), (46, 1)] }, { coefficient := -1, powers := [(22, 1), (37, 1), (43, 1), (60, 1)] }, { coefficient := 1, powers := [(32, 1), (37, 1), (43, 1), (46, 1)] }],
  [{ coefficient := -1, powers := [(1, 1), (13, 1), (37, 1), (46, 1), (60, 1), (67, 1)] }, { coefficient := -1, powers := [(1, 1), (13, 1), (37, 1), (57, 1), (60, 1), (67, 1)] }, { coefficient := 1, powers := [(1, 1), (37, 1), (43, 1), (46, 1), (60, 1), (67, 1)] }, { coefficient := 1, powers := [(1, 1), (37, 1), (43, 1), (57, 1), (60, 1), (67, 1)] }, { coefficient := 1, powers := [(10, 1), (13, 1), (32, 1), (37, 1), (46, 1), (67, 1)] }, { coefficient := 1, powers := [(10, 1), (13, 1), (32, 1), (37, 1), (57, 1), (67, 1)] }, { coefficient := -1, powers := [(10, 1), (32, 1), (37, 1), (43, 1), (46, 1), (67, 1)] }, { coefficient := -1, powers := [(10, 1), (32, 1), (37, 1), (43, 1), (57, 1), (67, 1)] }, { coefficient := 1, powers := [(13, 1), (15, 1), (32, 1), (37, 1), (46, 1), (67, 1)] }, { coefficient := 1, powers := [(13, 1), (15, 1), (32, 1), (37, 1), (57, 1), (67, 1)] }, { coefficient := -1, powers := [(15, 1), (32, 1), (37, 1), (43, 1), (46, 1), (67, 1)] }, { coefficient := -1, powers := [(15, 1), (32, 1), (37, 1), (43, 1), (57, 1), (67, 1)] }, { coefficient := -1, powers := [(20, 1), (56, 1), (57, 1), (66, 1), (67, 1)] }, { coefficient := 1, powers := [(20, 1), (56, 1), (67, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1), (67, 1)] }, { coefficient := -1, powers := [(56, 1), (66, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (31, 1), (37, 1), (52, 1)] }, { coefficient := -1, powers := [(31, 1), (37, 1), (43, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(10, 1), (13, 1), (22, 1), (31, 1), (37, 1), (63, 1)] }, { coefficient := 1, powers := [(10, 1), (22, 1), (31, 1), (37, 1), (43, 1), (63, 1)] }, { coefficient := 1, powers := [(13, 1), (31, 1), (37, 1), (46, 1)] }, { coefficient := -1, powers := [(31, 1), (37, 1), (43, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (13, 1), (37, 1), (60, 1)] }, { coefficient := -1, powers := [(1, 1), (37, 1), (43, 1), (60, 1)] }, { coefficient := -1, powers := [(10, 1), (13, 1), (32, 1), (37, 1)] }, { coefficient := 1, powers := [(10, 1), (32, 1), (37, 1), (43, 1)] }, { coefficient := -1, powers := [(13, 1), (15, 1), (32, 1), (37, 1)] }, { coefficient := 1, powers := [(15, 1), (32, 1), (37, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (6, 1), (20, 2), (59, 1), (62, 1), (67, 1)] }, { coefficient := -1, powers := [(1, 1), (13, 1), (31, 1), (37, 1), (52, 1), (67, 1)] }, { coefficient := 1, powers := [(1, 1), (31, 1), (37, 1), (43, 1), (52, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (63, 1)] }, { coefficient := -1, powers := [(6, 1), (20, 1), (60, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (32, 1), (37, 1)] }, { coefficient := -1, powers := [(32, 1), (37, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (31, 1), (32, 1), (37, 1), (38, 1)] }, { coefficient := -1, powers := [(31, 1), (32, 1), (37, 1), (38, 1), (43, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (20, 2), (59, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(56, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(50, 1)] }],
  [{ coefficient := 1, powers := [(43, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (13, 1), (31, 1), (37, 1)] }, { coefficient := -1, powers := [(10, 1), (31, 1), (37, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (20, 1), (59, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(13, 1), (31, 1), (37, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1), (43, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (20, 1), (37, 1), (59, 1), (60, 1)] }, { coefficient := -1, powers := [(6, 1), (20, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (6, 1), (20, 2), (29, 1), (54, 1), (59, 1), (62, 1), (67, 1)] }, { coefficient := -1, powers := [(0, 1), (37, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (43, 1), (50, 1)] }, { coefficient := -1, powers := [(1, 1), (13, 1), (29, 1), (31, 1), (37, 1), (52, 1), (54, 1), (67, 1)] }, { coefficient := 1, powers := [(1, 1), (29, 1), (31, 1), (37, 1), (43, 1), (52, 1), (54, 1), (67, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1), (37, 1), (59, 1), (60, 1)] }, { coefficient := 1, powers := [(10, 1), (13, 1), (22, 1), (31, 1), (37, 1), (52, 1)] }, { coefficient := -1, powers := [(10, 1), (22, 1), (31, 1), (37, 1), (43, 1), (52, 1)] }, { coefficient := 1, powers := [(20, 1), (43, 1), (50, 1)] }, { coefficient := 1, powers := [(20, 1), (50, 1), (56, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1), (50, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (1, 1), (56, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (56, 1), (57, 1), (66, 1)] }, { coefficient := 1, powers := [(0, 1), (56, 1)] }, { coefficient := 1, powers := [(1, 1), (6, 1), (20, 1), (56, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(1, 1), (13, 1), (30, 1), (37, 1), (46, 1), (60, 1), (67, 1)] }, { coefficient := 1, powers := [(1, 1), (13, 1), (30, 1), (37, 1), (57, 1), (60, 1), (67, 1)] }, { coefficient := -1, powers := [(1, 1), (30, 1), (37, 1), (43, 1), (46, 1), (60, 1), (67, 1)] }, { coefficient := -1, powers := [(1, 1), (30, 1), (37, 1), (43, 1), (57, 1), (60, 1), (67, 1)] }, { coefficient := 1, powers := [(6, 1), (34, 1)] }, { coefficient := -1, powers := [(10, 1), (13, 1), (15, 1), (22, 1), (32, 1), (37, 1), (63, 1)] }, { coefficient := -1, powers := [(10, 1), (13, 1), (30, 1), (32, 1), (37, 1), (46, 1), (67, 1)] }, { coefficient := -1, powers := [(10, 1), (13, 1), (30, 1), (32, 1), (37, 1), (57, 1), (67, 1)] }, { coefficient := 1, powers := [(10, 1), (15, 1), (22, 1), (32, 1), (37, 1), (43, 1), (63, 1)] }, { coefficient := 1, powers := [(10, 1), (30, 1), (32, 1), (37, 1), (43, 1), (46, 1), (67, 1)] }, { coefficient := 1, powers := [(10, 1), (30, 1), (32, 1), (37, 1), (43, 1), (57, 1), (67, 1)] }, { coefficient := -1, powers := [(13, 1), (15, 1), (22, 1), (37, 1), (60, 1)] }, { coefficient := -1, powers := [(13, 1), (15, 1), (30, 1), (32, 1), (37, 1), (46, 1), (67, 1)] }, { coefficient := -1, powers := [(13, 1), (15, 1), (30, 1), (32, 1), (37, 1), (57, 1), (67, 1)] }, { coefficient := 1, powers := [(13, 1), (15, 1), (32, 1), (37, 1), (46, 1)] }, { coefficient := 1, powers := [(15, 1), (22, 1), (37, 1), (43, 1), (60, 1)] }, { coefficient := 1, powers := [(15, 1), (30, 1), (32, 1), (37, 1), (43, 1), (46, 1), (67, 1)] }, { coefficient := 1, powers := [(15, 1), (30, 1), (32, 1), (37, 1), (43, 1), (57, 1), (67, 1)] }, { coefficient := -1, powers := [(15, 1), (32, 1), (37, 1), (43, 1), (46, 1)] }, { coefficient := 1, powers := [(20, 1), (30, 1), (56, 1), (57, 1), (66, 1), (67, 1)] }, { coefficient := -1, powers := [(20, 1), (30, 1), (56, 1), (67, 1)] }, { coefficient := -1, powers := [(30, 1), (34, 1), (37, 1), (67, 1)] }, { coefficient := 1, powers := [(30, 1), (56, 1), (66, 1), (67, 1)] }, { coefficient := -1, powers := [(56, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (6, 1), (20, 2), (30, 1), (59, 1), (62, 1), (67, 1)] }, { coefficient := 1, powers := [(1, 1), (13, 1), (30, 1), (31, 1), (37, 1), (52, 1), (67, 1)] }, { coefficient := 1, powers := [(1, 1), (13, 1), (31, 1), (37, 1), (57, 1)] }, { coefficient := -1, powers := [(1, 1), (30, 1), (31, 1), (37, 1), (43, 1), (52, 1), (67, 1)] }, { coefficient := -1, powers := [(1, 1), (31, 1), (37, 1), (43, 1), (57, 1)] }, { coefficient := 1, powers := [(7, 1), (13, 1), (31, 1), (35, 1), (37, 1)] }, { coefficient := -1, powers := [(7, 1), (31, 1), (35, 1), (37, 1), (43, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (31, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (6, 1), (20, 1), (59, 1), (60, 1), (62, 1)] }, { coefficient := 1, powers := [(3, 1), (59, 1)] }, { coefficient := -1, powers := [(4, 1), (13, 1), (31, 1), (32, 1), (37, 1), (38, 1), (60, 1)] }, { coefficient := 1, powers := [(4, 1), (31, 1), (32, 1), (37, 1), (38, 1), (43, 1), (60, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 2), (41, 1), (59, 1), (62, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 2), (46, 1), (59, 1), (62, 1)] }, { coefficient := -1, powers := [(6, 1), (20, 1), (59, 1), (62, 1)] }, { coefficient := -1, powers := [(10, 1), (13, 1), (31, 1), (32, 1), (37, 1), (38, 1), (46, 1)] }, { coefficient := 1, powers := [(10, 1), (31, 1), (32, 1), (37, 1), (38, 1), (43, 1), (46, 1)] }, { coefficient := -1, powers := [(13, 1), (15, 1), (31, 1), (32, 1), (37, 1), (38, 1), (41, 1)] }, { coefficient := 1, powers := [(13, 1), (40, 1)] }, { coefficient := 1, powers := [(15, 1), (31, 1), (32, 1), (37, 1), (38, 1), (41, 1), (43, 1)] }, { coefficient := -1, powers := [(40, 1), (43, 1)] }, { coefficient := -1, powers := [(43, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (13, 1), (31, 1), (37, 1), (60, 1)] }, { coefficient := -1, powers := [(4, 1), (31, 1), (37, 1), (43, 1), (60, 1)] }, { coefficient := 1, powers := [(10, 2), (13, 1), (22, 1), (31, 1), (37, 1), (63, 1)] }, { coefficient := -1, powers := [(10, 2), (22, 1), (31, 1), (37, 1), (43, 1), (63, 1)] }, { coefficient := -1, powers := [(10, 1), (13, 1), (31, 1), (37, 1), (41, 1)] }, { coefficient := -1, powers := [(10, 1), (13, 1), (31, 1), (37, 1), (46, 1)] }, { coefficient := 1, powers := [(10, 1), (31, 1), (37, 1), (41, 1), (43, 1)] }, { coefficient := 1, powers := [(10, 1), (31, 1), (37, 1), (43, 1), (46, 1)] }, { coefficient := 1, powers := [(13, 1), (15, 1), (31, 1), (37, 1), (41, 1)] }, { coefficient := -1, powers := [(15, 1), (31, 1), (37, 1), (41, 1), (43, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (6, 1), (20, 2), (46, 1), (59, 1), (62, 1)] }, { coefficient := 1, powers := [(1, 1), (9, 1), (13, 1), (37, 1), (46, 1), (60, 1)] }, { coefficient := 1, powers := [(1, 1), (9, 1), (13, 1), (37, 1), (57, 1), (60, 1)] }, { coefficient := -1, powers := [(1, 1), (9, 1), (37, 1), (43, 1), (46, 1), (60, 1)] }, { coefficient := -1, powers := [(1, 1), (9, 1), (37, 1), (43, 1), (57, 1), (60, 1)] }, { coefficient := 1, powers := [(1, 1), (13, 1), (31, 1), (37, 1), (46, 1), (52, 1)] }, { coefficient := -1, powers := [(1, 1), (31, 1), (37, 1), (43, 1), (46, 1), (52, 1)] }, { coefficient := -1, powers := [(9, 1), (10, 1), (13, 1), (32, 1), (37, 1), (46, 1)] }, { coefficient := -1, powers := [(9, 1), (10, 1), (13, 1), (32, 1), (37, 1), (57, 1)] }, { coefficient := 1, powers := [(9, 1), (10, 1), (32, 1), (37, 1), (43, 1), (46, 1)] }, { coefficient := 1, powers := [(9, 1), (10, 1), (32, 1), (37, 1), (43, 1), (57, 1)] }, { coefficient := -1, powers := [(9, 1), (13, 1), (15, 1), (32, 1), (37, 1), (46, 1)] }, { coefficient := -1, powers := [(9, 1), (13, 1), (15, 1), (32, 1), (37, 1), (57, 1)] }, { coefficient := 1, powers := [(9, 1), (15, 1), (32, 1), (37, 1), (43, 1), (46, 1)] }, { coefficient := 1, powers := [(9, 1), (15, 1), (32, 1), (37, 1), (43, 1), (57, 1)] }, { coefficient := 1, powers := [(9, 1), (20, 1), (56, 1), (57, 1), (66, 1)] }, { coefficient := -1, powers := [(9, 1), (20, 1), (56, 1)] }, { coefficient := -1, powers := [(9, 1), (34, 1), (37, 1)] }, { coefficient := 1, powers := [(9, 1), (56, 1), (66, 1)] }]
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
    ¬ ∀ index : Fin 27,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component37.SelectedLeafB6_1_6_1.selectedHasNoCommonZero

end Krenn.Component37.SelectedLeafB6_1_6_1
