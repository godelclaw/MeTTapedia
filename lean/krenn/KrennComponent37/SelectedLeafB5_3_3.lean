import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component37.SelectedLeafB5_3_3

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "9844c86589a5351ffc388f9d1bbdeaf7ff951bb5abc7032a5312632a94690b03"
def certificateSHA256 : String := "b44a6ed58252e7844d87d4f9ca3906c96c33b68d6ba4c8122acb10f69a3b8da5"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 28 → Fin 667 := ![
  17,
  23,
  27,
  42,
  149,
  182,
  221,
  283,
  298,
  299,
  300,
  301,
  303,
  457,
  589,
  590,
  602,
  603,
  604,
  605,
  655,
  656,
  659,
  660,
  661,
  663,
  664,
  666
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 28 → SparsePoly (Fin 68) := ![
  [{ coefficient := 1, powers := [(18, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (26, 1)] }, { coefficient := 1, powers := [(26, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (42, 1)] }, { coefficient := 1, powers := [(27, 1), (48, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (26, 1), (47, 1)] }, { coefficient := 1, powers := [(9, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (44, 1), (54, 1)] }, { coefficient := 1, powers := [(22, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (46, 1)] }, { coefficient := 1, powers := [(4, 1), (35, 1)] }, { coefficient := 1, powers := [(15, 1), (22, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (52, 1)] }, { coefficient := 1, powers := [(7, 1), (32, 1)] }, { coefficient := 1, powers := [(10, 1), (27, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (50, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (50, 1)] }, { coefficient := 1, powers := [(18, 1), (28, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (59, 1)] }, { coefficient := 1, powers := [(9, 1), (43, 1)] }, { coefficient := 1, powers := [(13, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (46, 1)] }, { coefficient := 1, powers := [(9, 1), (57, 1)] }, { coefficient := 1, powers := [(31, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (38, 1), (59, 1)] }, { coefficient := 1, powers := [(9, 1), (34, 1), (38, 1)] }, { coefficient := 1, powers := [(9, 1), (45, 1)] }, { coefficient := 1, powers := [(13, 1), (31, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (41, 1), (58, 1)] }, { coefficient := 1, powers := [(1, 1), (47, 1), (54, 1)] }, { coefficient := 1, powers := [(4, 1), (32, 1), (58, 1)] }, { coefficient := 1, powers := [(10, 1), (22, 1), (58, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (42, 1), (57, 1)] }, { coefficient := 1, powers := [(1, 1), (48, 1), (53, 1)] }, { coefficient := 1, powers := [(7, 1), (35, 1), (42, 1)] }, { coefficient := 1, powers := [(11, 1), (27, 1), (48, 1)] }, { coefficient := 1, powers := [(15, 1), (27, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1)] }, { coefficient := 1, powers := [(3, 1), (34, 1)] }, { coefficient := 1, powers := [(13, 1), (20, 1)] }, { coefficient := 1, powers := [(20, 1), (56, 1)] }, { coefficient := 1, powers := [(25, 1), (43, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (50, 1)] }, { coefficient := 1, powers := [(6, 1), (31, 1)] }, { coefficient := 1, powers := [(9, 1), (25, 1)] }, { coefficient := 1, powers := [(20, 1), (50, 1)] }, { coefficient := 1, powers := [(25, 1), (40, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (60, 1)] }, { coefficient := 1, powers := [(10, 1), (46, 1)] }, { coefficient := 1, powers := [(10, 1), (57, 1)] }, { coefficient := 1, powers := [(15, 1), (41, 1)] }, { coefficient := 1, powers := [(15, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (52, 1)] }, { coefficient := 1, powers := [(22, 1), (57, 1)] }, { coefficient := 1, powers := [(27, 1), (41, 1)] }, { coefficient := 1, powers := [(27, 1), (46, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1)] }, { coefficient := 1, powers := [(35, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (37, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (40, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (43, 1), (50, 1)] }, { coefficient := 1, powers := [(3, 1), (25, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (31, 1), (56, 1)] }, { coefficient := 1, powers := [(3, 1), (34, 1), (50, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (31, 1), (43, 1)] }, { coefficient := 1, powers := [(6, 1), (34, 1), (40, 1)] }, { coefficient := 1, powers := [(9, 1), (20, 1), (56, 1)] }, { coefficient := 1, powers := [(9, 1), (25, 1), (43, 1)] }, { coefficient := 1, powers := [(9, 1), (34, 1), (37, 1)] }, { coefficient := 1, powers := [(13, 1), (20, 1), (50, 1)] }, { coefficient := 1, powers := [(13, 1), (25, 1), (40, 1)] }, { coefficient := 1, powers := [(13, 1), (31, 1), (37, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1), (38, 1), (60, 1)] }, { coefficient := 1, powers := [(1, 1), (41, 1), (57, 1)] }, { coefficient := 1, powers := [(1, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(4, 1), (27, 1), (60, 1)] }, { coefficient := 1, powers := [(4, 1), (32, 1), (57, 1)] }, { coefficient := 1, powers := [(4, 1), (35, 1), (52, 1)] }, { coefficient := 1, powers := [(7, 1), (22, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (32, 1), (46, 1)] }, { coefficient := 1, powers := [(7, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(10, 1), (22, 1), (57, 1)] }, { coefficient := 1, powers := [(10, 1), (27, 1), (46, 1)] }, { coefficient := 1, powers := [(10, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(15, 1), (22, 1), (52, 1)] }, { coefficient := 1, powers := [(15, 1), (27, 1), (41, 1)] }, { coefficient := 1, powers := [(15, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(40, 1)] }],
  [{ coefficient := 1, powers := [(42, 1), (65, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(56, 1)] }],
  [{ coefficient := 1, powers := [(58, 1), (67, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 28 → SparsePoly (Fin 68) := ![
  [{ coefficient := -1, powers := [(0, 1), (10, 1), (23, 1), (32, 1), (38, 1), (43, 1), (63, 1)] }, { coefficient := 1, powers := [(0, 1), (15, 1), (23, 1), (32, 1), (38, 1), (43, 1), (63, 1)] }, { coefficient := -1, powers := [(10, 1), (20, 1), (23, 1), (32, 1), (38, 1), (43, 1), (63, 1)] }, { coefficient := -1, powers := [(10, 1), (23, 1), (25, 1), (32, 1), (38, 1), (43, 1), (63, 1)] }, { coefficient := -1, powers := [(10, 1), (23, 1), (32, 1), (34, 1), (37, 1), (38, 1), (63, 1)] }, { coefficient := 1, powers := [(15, 1), (20, 1), (23, 1), (32, 1), (38, 1), (43, 1), (63, 1)] }, { coefficient := 1, powers := [(15, 1), (23, 1), (25, 1), (32, 1), (38, 1), (43, 1), (63, 1)] }, { coefficient := 1, powers := [(15, 1), (23, 1), (32, 1), (34, 1), (37, 1), (38, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (44, 1), (60, 1), (67, 1)] }, { coefficient := 1, powers := [(10, 1), (44, 1), (52, 1), (67, 1)] }, { coefficient := 1, powers := [(10, 1), (44, 1), (57, 1), (67, 1)] }, { coefficient := -1, powers := [(16, 1), (57, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (51, 1), (60, 1), (65, 1)] }, { coefficient := 1, powers := [(10, 1), (41, 1), (51, 1), (65, 1)] }, { coefficient := 2, powers := [(10, 1), (46, 1), (51, 1), (65, 1)] }, { coefficient := 1, powers := [(10, 1), (51, 1), (57, 1), (65, 1)] }, { coefficient := -1, powers := [(11, 1), (41, 1), (65, 1)] }, { coefficient := 1, powers := [(15, 1), (41, 1), (51, 1), (65, 1)] }, { coefficient := 1, powers := [(15, 1), (51, 1), (52, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (10, 1), (20, 1), (32, 1), (63, 1)] }, { coefficient := 1, powers := [(6, 1), (15, 1), (20, 1), (32, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(10, 1), (25, 1), (32, 1), (38, 1), (43, 1), (47, 1), (67, 1)] }, { coefficient := 1, powers := [(10, 1), (32, 1), (37, 1), (43, 1), (46, 1), (47, 1), (67, 1)] }, { coefficient := 1, powers := [(10, 1), (32, 1), (37, 1), (43, 1), (47, 1), (57, 1), (67, 1)] }, { coefficient := -1, powers := [(10, 1), (32, 1), (37, 1), (45, 1), (47, 1), (67, 1)] }, { coefficient := 1, powers := [(15, 1), (25, 1), (32, 1), (38, 1), (43, 1), (47, 1), (67, 1)] }, { coefficient := -1, powers := [(15, 1), (32, 1), (37, 1), (43, 1), (46, 1), (47, 1), (67, 1)] }, { coefficient := -1, powers := [(15, 1), (32, 1), (37, 1), (43, 1), (47, 1), (57, 1), (67, 1)] }, { coefficient := 1, powers := [(15, 1), (32, 1), (37, 1), (45, 1), (47, 1), (67, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (60, 1), (65, 1)] }, { coefficient := -1, powers := [(10, 1), (41, 1), (65, 1)] }, { coefficient := -2, powers := [(10, 1), (46, 1), (65, 1)] }, { coefficient := -1, powers := [(10, 1), (57, 1), (65, 1)] }, { coefficient := -1, powers := [(15, 1), (41, 1), (65, 1)] }, { coefficient := -1, powers := [(15, 1), (52, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (25, 1), (32, 1), (38, 1), (43, 1), (67, 1)] }, { coefficient := -1, powers := [(10, 1), (32, 1), (37, 1), (43, 1), (46, 1), (67, 1)] }, { coefficient := -1, powers := [(10, 1), (32, 1), (37, 1), (43, 1), (57, 1), (67, 1)] }, { coefficient := 1, powers := [(10, 1), (32, 1), (37, 1), (45, 1), (67, 1)] }, { coefficient := -1, powers := [(15, 1), (25, 1), (32, 1), (38, 1), (43, 1), (67, 1)] }, { coefficient := 1, powers := [(15, 1), (32, 1), (37, 1), (43, 1), (46, 1), (67, 1)] }, { coefficient := 1, powers := [(15, 1), (32, 1), (37, 1), (43, 1), (57, 1), (67, 1)] }, { coefficient := -1, powers := [(15, 1), (32, 1), (37, 1), (45, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (60, 1), (67, 1)] }, { coefficient := -1, powers := [(10, 1), (52, 1), (67, 1)] }, { coefficient := -1, powers := [(10, 1), (57, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(52, 1)] }],
  [{ coefficient := 1, powers := [(46, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (10, 1), (32, 1), (38, 1), (43, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (15, 1), (32, 1), (38, 1), (43, 1), (63, 1)] }, { coefficient := 1, powers := [(10, 1), (20, 1), (32, 1), (38, 1), (43, 1), (63, 1)] }, { coefficient := 1, powers := [(10, 1), (25, 1), (32, 1), (38, 1), (43, 1), (63, 1)] }, { coefficient := 1, powers := [(10, 1), (32, 1), (34, 1), (37, 1), (38, 1), (63, 1)] }, { coefficient := -1, powers := [(15, 1), (20, 1), (32, 1), (38, 1), (43, 1), (63, 1)] }, { coefficient := -1, powers := [(15, 1), (25, 1), (32, 1), (38, 1), (43, 1), (63, 1)] }, { coefficient := -1, powers := [(15, 1), (32, 1), (34, 1), (37, 1), (38, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(10, 1), (25, 1), (32, 1), (38, 1)] }, { coefficient := 1, powers := [(15, 1), (25, 1), (32, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (32, 1), (37, 1), (43, 1)] }, { coefficient := -1, powers := [(15, 1), (32, 1), (37, 1), (43, 1)] }],
  [{ coefficient := -1, powers := [(10, 1), (32, 1), (37, 1)] }, { coefficient := 1, powers := [(15, 1), (32, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(57, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(41, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(10, 1), (32, 1), (38, 1), (50, 1)] }, { coefficient := 1, powers := [(15, 1), (32, 1), (38, 1), (50, 1)] }],
  [{ coefficient := -1, powers := [(10, 1), (32, 1), (38, 1), (43, 1)] }, { coefficient := 1, powers := [(15, 1), (32, 1), (38, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(27, 1)] }],
  [{ coefficient := 1, powers := [(10, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [(15, 1), (32, 1), (38, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(38, 1), (60, 1)] }, { coefficient := -1, powers := [(41, 1), (42, 1), (57, 1), (65, 1)] }, { coefficient := -1, powers := [(41, 1), (48, 1), (53, 1), (65, 1)] }, { coefficient := -1, powers := [(41, 1), (57, 1), (58, 1), (67, 1)] }, { coefficient := 1, powers := [(41, 1), (57, 1)] }, { coefficient := -1, powers := [(46, 1), (52, 1)] }, { coefficient := -1, powers := [(47, 1), (54, 1), (57, 1), (67, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (10, 1), (32, 1), (38, 1), (43, 1), (50, 1)] }, { coefficient := 1, powers := [(0, 1), (15, 1), (32, 1), (38, 1), (43, 1), (50, 1)] }, { coefficient := 1, powers := [(6, 1), (10, 1), (20, 1), (32, 1), (38, 1), (59, 1)] }, { coefficient := -1, powers := [(6, 1), (15, 1), (20, 1), (32, 1), (38, 1), (59, 1)] }, { coefficient := -1, powers := [(10, 1), (20, 1), (32, 1), (38, 1), (43, 1), (50, 1)] }, { coefficient := -1, powers := [(10, 1), (25, 1), (32, 1), (38, 1), (43, 1), (50, 1)] }, { coefficient := -1, powers := [(10, 1), (32, 1), (34, 1), (37, 1), (38, 1), (50, 1)] }, { coefficient := 1, powers := [(15, 1), (20, 1), (32, 1), (38, 1), (43, 1), (50, 1)] }, { coefficient := 1, powers := [(15, 1), (25, 1), (32, 1), (38, 1), (43, 1), (50, 1)] }, { coefficient := 1, powers := [(15, 1), (32, 1), (34, 1), (37, 1), (38, 1), (50, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (10, 1), (18, 1), (28, 1), (32, 1), (38, 1), (43, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (10, 1), (32, 1), (38, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (15, 1), (18, 1), (28, 1), (32, 1), (38, 1), (43, 1), (63, 1)] }, { coefficient := 1, powers := [(0, 1), (15, 1), (32, 1), (38, 1), (56, 1)] }, { coefficient := -1, powers := [(6, 1), (10, 1), (32, 1), (34, 1), (38, 1)] }, { coefficient := 1, powers := [(6, 1), (15, 1), (32, 1), (34, 1), (38, 1)] }, { coefficient := -1, powers := [(10, 1), (18, 1), (20, 1), (28, 1), (32, 1), (38, 1), (43, 1), (63, 1)] }, { coefficient := -1, powers := [(10, 1), (18, 1), (25, 1), (28, 1), (32, 1), (38, 1), (43, 1), (63, 1)] }, { coefficient := -1, powers := [(10, 1), (18, 1), (28, 1), (32, 1), (34, 1), (37, 1), (38, 1), (63, 1)] }, { coefficient := 1, powers := [(10, 1), (25, 1), (26, 1), (32, 1), (38, 1), (43, 1), (47, 1), (67, 1)] }, { coefficient := 1, powers := [(10, 1), (25, 1), (32, 1), (38, 1), (43, 1)] }, { coefficient := -1, powers := [(10, 1), (26, 1), (32, 1), (37, 1), (43, 1), (46, 1), (47, 1), (67, 1)] }, { coefficient := -1, powers := [(10, 1), (26, 1), (32, 1), (37, 1), (43, 1), (47, 1), (57, 1), (67, 1)] }, { coefficient := 1, powers := [(10, 1), (26, 1), (32, 1), (37, 1), (45, 1), (47, 1), (67, 1)] }, { coefficient := 1, powers := [(15, 1), (18, 1), (20, 1), (28, 1), (32, 1), (38, 1), (43, 1), (63, 1)] }, { coefficient := 1, powers := [(15, 1), (18, 1), (25, 1), (28, 1), (32, 1), (38, 1), (43, 1), (63, 1)] }, { coefficient := 1, powers := [(15, 1), (18, 1), (28, 1), (32, 1), (34, 1), (37, 1), (38, 1), (63, 1)] }, { coefficient := -1, powers := [(15, 1), (25, 1), (26, 1), (32, 1), (38, 1), (43, 1), (47, 1), (67, 1)] }, { coefficient := -1, powers := [(15, 1), (25, 1), (32, 1), (38, 1), (43, 1)] }, { coefficient := 1, powers := [(15, 1), (26, 1), (32, 1), (37, 1), (43, 1), (46, 1), (47, 1), (67, 1)] }, { coefficient := 1, powers := [(15, 1), (26, 1), (32, 1), (37, 1), (43, 1), (47, 1), (57, 1), (67, 1)] }, { coefficient := -1, powers := [(15, 1), (26, 1), (32, 1), (37, 1), (45, 1), (47, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (27, 1), (60, 1)] }, { coefficient := -1, powers := [(7, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(10, 1), (27, 1), (41, 1)] }, { coefficient := 2, powers := [(10, 1), (27, 1), (46, 1)] }, { coefficient := 1, powers := [(10, 1), (27, 1), (57, 1)] }, { coefficient := 1, powers := [(15, 1), (27, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (10, 1), (31, 1), (32, 1), (38, 1)] }, { coefficient := 1, powers := [(3, 1), (15, 1), (31, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [(9, 1), (10, 1), (20, 1), (32, 1), (38, 1)] }, { coefficient := 1, powers := [(9, 1), (15, 1), (20, 1), (32, 1), (38, 1)] }, { coefficient := 1, powers := [(10, 1), (20, 1), (32, 1), (38, 1), (50, 1)] }, { coefficient := -1, powers := [(15, 1), (20, 1), (32, 1), (38, 1), (50, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (32, 1), (57, 1)] }, { coefficient := -1, powers := [(7, 1), (22, 1), (60, 1)] }, { coefficient := -1, powers := [(9, 1), (10, 1), (25, 1), (32, 1), (38, 1), (43, 1)] }, { coefficient := 1, powers := [(9, 1), (10, 1), (32, 1), (37, 1), (43, 1), (46, 1)] }, { coefficient := 1, powers := [(9, 1), (10, 1), (32, 1), (37, 1), (43, 1), (57, 1)] }, { coefficient := -1, powers := [(9, 1), (10, 1), (32, 1), (37, 1), (45, 1)] }, { coefficient := 1, powers := [(9, 1), (15, 1), (25, 1), (32, 1), (38, 1), (43, 1)] }, { coefficient := -1, powers := [(9, 1), (15, 1), (32, 1), (37, 1), (43, 1), (46, 1)] }, { coefficient := -1, powers := [(9, 1), (15, 1), (32, 1), (37, 1), (43, 1), (57, 1)] }, { coefficient := 1, powers := [(9, 1), (15, 1), (32, 1), (37, 1), (45, 1)] }, { coefficient := 1, powers := [(10, 1), (22, 1), (52, 1)] }]
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
    ¬ ∀ index : Fin 28,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component37.SelectedLeafB5_3_3.selectedHasNoCommonZero

end Krenn.Component37.SelectedLeafB5_3_3
