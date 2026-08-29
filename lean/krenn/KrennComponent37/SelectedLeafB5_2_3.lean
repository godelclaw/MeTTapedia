import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component37.SelectedLeafB5_2_3

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "3bcb57c0b1f65dc458a734756dd1dd0b7a084890417696c6bef28d31f40a854a"
def certificateSHA256 : String := "d08b1dc57e27341c97675673e55f16e3426f3b9469ca109da2bc813df4cbca2e"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 36 → Fin 667 := ![
  13,
  15,
  17,
  23,
  42,
  147,
  149,
  221,
  283,
  298,
  299,
  300,
  301,
  303,
  435,
  453,
  455,
  457,
  470,
  531,
  589,
  591,
  602,
  603,
  604,
  605,
  612,
  645,
  648,
  655,
  656,
  659,
  660,
  661,
  664,
  666
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 36 → SparsePoly (Fin 67) := ![
  [{ coefficient := 1, powers := [(17, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (27, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (31, 1)] }, { coefficient := 1, powers := [(15, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (26, 1)] }, { coefficient := 1, powers := [(26, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (26, 1), (47, 1)] }, { coefficient := 1, powers := [(9, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (44, 1), (54, 1)] }, { coefficient := 1, powers := [(22, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (46, 1)] }, { coefficient := 1, powers := [(4, 1), (35, 1)] }, { coefficient := 1, powers := [(15, 1), (22, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (52, 1)] }, { coefficient := 1, powers := [(7, 1), (32, 1)] }, { coefficient := 1, powers := [(10, 1), (27, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (50, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (50, 1)] }, { coefficient := 1, powers := [(18, 1), (28, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (59, 1)] }, { coefficient := 1, powers := [(9, 1), (43, 1)] }, { coefficient := 1, powers := [(13, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (46, 1)] }, { coefficient := 1, powers := [(9, 1), (57, 1)] }, { coefficient := 1, powers := [(31, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (52, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (52, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (57, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (41, 1)] }, { coefficient := 1, powers := [(18, 1), (46, 1)] }, { coefficient := 1, powers := [(18, 1), (52, 1)] }, { coefficient := 1, powers := [(18, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (41, 1)] }, { coefficient := 1, powers := [(29, 1), (46, 1)] }, { coefficient := 1, powers := [(29, 1), (52, 1)] }, { coefficient := 1, powers := [(29, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (38, 1), (59, 1)] }, { coefficient := 1, powers := [(9, 1), (34, 1), (38, 1)] }, { coefficient := 1, powers := [(9, 1), (45, 1)] }, { coefficient := 1, powers := [(13, 1), (31, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1), (50, 1)] }, { coefficient := 1, powers := [(6, 1), (31, 1), (46, 1)] }, { coefficient := 1, powers := [(9, 1), (25, 1), (46, 1)] }, { coefficient := 1, powers := [(50, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (20, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (31, 1), (43, 1)] }, { coefficient := 1, powers := [(7, 1), (34, 1), (40, 1)] }, { coefficient := 1, powers := [(14, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (41, 1), (58, 1)] }, { coefficient := 1, powers := [(1, 1), (47, 1), (54, 1)] }, { coefficient := 1, powers := [(4, 1), (32, 1), (58, 1)] }, { coefficient := 1, powers := [(10, 1), (22, 1), (58, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (37, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (40, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (43, 1), (50, 1)] }, { coefficient := 1, powers := [(17, 1), (23, 1), (50, 1)] }, { coefficient := 1, powers := [(17, 1), (28, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1)] }, { coefficient := 1, powers := [(3, 1), (34, 1)] }, { coefficient := 1, powers := [(13, 1), (20, 1)] }, { coefficient := 1, powers := [(20, 1), (56, 1)] }, { coefficient := 1, powers := [(25, 1), (43, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (50, 1)] }, { coefficient := 1, powers := [(6, 1), (31, 1)] }, { coefficient := 1, powers := [(9, 1), (25, 1)] }, { coefficient := 1, powers := [(20, 1), (50, 1)] }, { coefficient := 1, powers := [(25, 1), (40, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (60, 1)] }, { coefficient := 1, powers := [(10, 1), (46, 1)] }, { coefficient := 1, powers := [(10, 1), (57, 1)] }, { coefficient := 1, powers := [(15, 1), (41, 1)] }, { coefficient := 1, powers := [(15, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (52, 1)] }, { coefficient := 1, powers := [(22, 1), (57, 1)] }, { coefficient := 1, powers := [(27, 1), (41, 1)] }, { coefficient := 1, powers := [(27, 1), (46, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1)] }, { coefficient := 1, powers := [(35, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1), (50, 1)] }, { coefficient := 1, powers := [(6, 1), (31, 1), (45, 1)] }, { coefficient := 1, powers := [(6, 1), (59, 1)] }, { coefficient := 1, powers := [(9, 1), (25, 1), (45, 1)] }, { coefficient := 1, powers := [(9, 1), (56, 1)] }, { coefficient := 1, powers := [(13, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (38, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (41, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(41, 1)] }, { coefficient := 1, powers := [(46, 1)] }, { coefficient := 1, powers := [(52, 1)] }, { coefficient := 1, powers := [(57, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (41, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (41, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (46, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (52, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (37, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (40, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (43, 1), (50, 1)] }, { coefficient := 1, powers := [(3, 1), (25, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (31, 1), (56, 1)] }, { coefficient := 1, powers := [(3, 1), (34, 1), (50, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (31, 1), (43, 1)] }, { coefficient := 1, powers := [(6, 1), (34, 1), (40, 1)] }, { coefficient := 1, powers := [(9, 1), (20, 1), (56, 1)] }, { coefficient := 1, powers := [(9, 1), (25, 1), (43, 1)] }, { coefficient := 1, powers := [(9, 1), (34, 1), (37, 1)] }, { coefficient := 1, powers := [(13, 1), (20, 1), (50, 1)] }, { coefficient := 1, powers := [(13, 1), (25, 1), (40, 1)] }, { coefficient := 1, powers := [(13, 1), (31, 1), (37, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1), (38, 1), (60, 1)] }, { coefficient := 1, powers := [(1, 1), (41, 1), (57, 1)] }, { coefficient := 1, powers := [(1, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(4, 1), (27, 1), (60, 1)] }, { coefficient := 1, powers := [(4, 1), (32, 1), (57, 1)] }, { coefficient := 1, powers := [(4, 1), (35, 1), (52, 1)] }, { coefficient := 1, powers := [(7, 1), (22, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (32, 1), (46, 1)] }, { coefficient := 1, powers := [(7, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(10, 1), (22, 1), (57, 1)] }, { coefficient := 1, powers := [(10, 1), (27, 1), (46, 1)] }, { coefficient := 1, powers := [(10, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(15, 1), (22, 1), (52, 1)] }, { coefficient := 1, powers := [(15, 1), (27, 1), (41, 1)] }, { coefficient := 1, powers := [(15, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(40, 1)] }],
  [{ coefficient := 1, powers := [(56, 1)] }],
  [{ coefficient := 1, powers := [(58, 1), (66, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 36 → SparsePoly (Fin 67) := ![
  [{ coefficient := 1, powers := [(0, 1), (7, 1), (23, 1), (27, 1), (60, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (7, 1), (23, 1), (35, 1), (41, 1), (63, 1)] }, { coefficient := 1, powers := [(0, 1), (10, 1), (23, 1), (27, 1), (46, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (23, 1), (41, 1), (63, 1)] }, { coefficient := 1, powers := [(10, 1), (23, 1), (46, 1), (63, 1)] }, { coefficient := -1, powers := [(10, 1), (29, 1), (63, 1)] }, { coefficient := -1, powers := [(15, 1), (23, 1), (41, 1), (63, 1)] }, { coefficient := -1, powers := [(15, 1), (23, 1), (46, 1), (63, 1)] }, { coefficient := 1, powers := [(15, 1), (29, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (7, 1), (23, 1), (27, 1), (43, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(0, 1), (7, 1), (23, 1), (35, 1), (41, 1), (43, 1), (63, 1)] }, { coefficient := -2, powers := [(0, 1), (10, 1), (23, 1), (27, 1), (43, 1), (46, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (10, 1), (23, 1), (32, 1), (38, 1), (43, 1), (63, 1)] }, { coefficient := 1, powers := [(0, 1), (15, 1), (23, 1), (32, 1), (38, 1), (43, 1), (63, 1)] }, { coefficient := -1, powers := [(7, 1), (23, 1), (25, 1), (27, 1), (43, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(7, 1), (23, 1), (25, 1), (35, 1), (41, 1), (43, 1), (63, 1)] }, { coefficient := -1, powers := [(7, 1), (23, 1), (27, 1), (34, 1), (37, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(7, 1), (23, 1), (34, 1), (35, 1), (37, 1), (41, 1), (63, 1)] }, { coefficient := -2, powers := [(10, 1), (13, 1), (20, 1), (23, 1), (27, 1), (46, 1), (63, 1)] }, { coefficient := 1, powers := [(10, 1), (13, 1), (23, 1), (27, 1), (63, 1)] }, { coefficient := 1, powers := [(10, 1), (20, 1), (23, 1), (27, 1), (45, 1), (63, 1)] }, { coefficient := -1, powers := [(10, 1), (20, 1), (23, 1), (32, 1), (38, 1), (43, 1), (63, 1)] }, { coefficient := -1, powers := [(10, 1), (23, 1), (25, 1), (27, 1), (43, 1), (46, 1), (63, 1)] }, { coefficient := -1, powers := [(10, 1), (23, 1), (25, 1), (32, 1), (38, 1), (43, 1), (63, 1)] }, { coefficient := -1, powers := [(10, 1), (23, 1), (27, 1), (34, 1), (37, 1), (46, 1), (63, 1)] }, { coefficient := -1, powers := [(10, 1), (23, 1), (27, 1), (43, 1), (63, 1)] }, { coefficient := -1, powers := [(10, 1), (23, 1), (32, 1), (34, 1), (37, 1), (38, 1), (63, 1)] }, { coefficient := 1, powers := [(15, 1), (20, 1), (23, 1), (32, 1), (38, 1), (43, 1), (63, 1)] }, { coefficient := 1, powers := [(15, 1), (23, 1), (25, 1), (32, 1), (38, 1), (43, 1), (63, 1)] }, { coefficient := 1, powers := [(15, 1), (23, 1), (32, 1), (34, 1), (37, 1), (38, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (44, 1), (60, 1), (66, 1)] }, { coefficient := 1, powers := [(10, 1), (44, 1), (52, 1), (66, 1)] }, { coefficient := 1, powers := [(10, 1), (44, 1), (57, 1), (66, 1)] }, { coefficient := -1, powers := [(16, 1), (57, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (10, 1), (20, 1), (32, 1), (63, 1)] }, { coefficient := 1, powers := [(6, 1), (15, 1), (20, 1), (32, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(13, 1), (27, 1), (37, 1), (60, 1)] }, { coefficient := 1, powers := [(13, 1), (35, 1), (37, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (27, 1), (34, 1), (37, 1), (47, 1), (60, 1), (66, 1)] }, { coefficient := -1, powers := [(7, 1), (34, 1), (35, 1), (37, 1), (41, 1), (47, 1), (66, 1)] }, { coefficient := -1, powers := [(10, 1), (25, 1), (27, 1), (43, 1), (46, 1), (47, 1), (66, 1)] }, { coefficient := -1, powers := [(10, 1), (25, 1), (32, 1), (38, 1), (43, 1), (47, 1), (66, 1)] }, { coefficient := 1, powers := [(10, 1), (27, 1), (34, 1), (37, 1), (46, 1), (47, 1), (66, 1)] }, { coefficient := 1, powers := [(10, 1), (32, 1), (37, 1), (43, 1), (46, 1), (47, 1), (66, 1)] }, { coefficient := 1, powers := [(10, 1), (32, 1), (37, 1), (43, 1), (47, 1), (57, 1), (66, 1)] }, { coefficient := -1, powers := [(10, 1), (32, 1), (37, 1), (45, 1), (47, 1), (66, 1)] }, { coefficient := 1, powers := [(15, 1), (25, 1), (32, 1), (38, 1), (43, 1), (47, 1), (66, 1)] }, { coefficient := -1, powers := [(15, 1), (32, 1), (37, 1), (43, 1), (46, 1), (47, 1), (66, 1)] }, { coefficient := -1, powers := [(15, 1), (32, 1), (37, 1), (43, 1), (47, 1), (57, 1), (66, 1)] }, { coefficient := 1, powers := [(15, 1), (32, 1), (37, 1), (45, 1), (47, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (27, 1), (34, 1), (37, 1), (60, 1), (66, 1)] }, { coefficient := 1, powers := [(7, 1), (34, 1), (35, 1), (37, 1), (41, 1), (66, 1)] }, { coefficient := 1, powers := [(10, 1), (25, 1), (27, 1), (43, 1), (46, 1), (66, 1)] }, { coefficient := 1, powers := [(10, 1), (25, 1), (32, 1), (38, 1), (43, 1), (66, 1)] }, { coefficient := -1, powers := [(10, 1), (27, 1), (34, 1), (37, 1), (46, 1), (66, 1)] }, { coefficient := -1, powers := [(10, 1), (32, 1), (37, 1), (43, 1), (46, 1), (66, 1)] }, { coefficient := -1, powers := [(10, 1), (32, 1), (37, 1), (43, 1), (57, 1), (66, 1)] }, { coefficient := 1, powers := [(10, 1), (32, 1), (37, 1), (45, 1), (66, 1)] }, { coefficient := -1, powers := [(15, 1), (25, 1), (32, 1), (38, 1), (43, 1), (66, 1)] }, { coefficient := 1, powers := [(15, 1), (32, 1), (37, 1), (43, 1), (46, 1), (66, 1)] }, { coefficient := 1, powers := [(15, 1), (32, 1), (37, 1), (43, 1), (57, 1), (66, 1)] }, { coefficient := -1, powers := [(15, 1), (32, 1), (37, 1), (45, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (60, 1), (66, 1)] }, { coefficient := -1, powers := [(10, 1), (52, 1), (66, 1)] }, { coefficient := -1, powers := [(10, 1), (57, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(52, 1)] }],
  [{ coefficient := 1, powers := [(46, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (7, 1), (27, 1), (43, 1), (60, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (7, 1), (35, 1), (41, 1), (43, 1), (63, 1)] }, { coefficient := 2, powers := [(0, 1), (10, 1), (27, 1), (43, 1), (46, 1), (63, 1)] }, { coefficient := 1, powers := [(0, 1), (10, 1), (32, 1), (38, 1), (43, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (15, 1), (32, 1), (38, 1), (43, 1), (63, 1)] }, { coefficient := 1, powers := [(7, 1), (25, 1), (27, 1), (43, 1), (60, 1), (63, 1)] }, { coefficient := -1, powers := [(7, 1), (25, 1), (35, 1), (41, 1), (43, 1), (63, 1)] }, { coefficient := 1, powers := [(7, 1), (27, 1), (34, 1), (37, 1), (60, 1), (63, 1)] }, { coefficient := -1, powers := [(7, 1), (34, 1), (35, 1), (37, 1), (41, 1), (63, 1)] }, { coefficient := 2, powers := [(10, 1), (13, 1), (20, 1), (27, 1), (46, 1), (63, 1)] }, { coefficient := -1, powers := [(10, 1), (13, 1), (27, 1), (63, 1)] }, { coefficient := -1, powers := [(10, 1), (20, 1), (27, 1), (45, 1), (63, 1)] }, { coefficient := 1, powers := [(10, 1), (20, 1), (32, 1), (38, 1), (43, 1), (63, 1)] }, { coefficient := 1, powers := [(10, 1), (25, 1), (27, 1), (43, 1), (46, 1), (63, 1)] }, { coefficient := 1, powers := [(10, 1), (25, 1), (32, 1), (38, 1), (43, 1), (63, 1)] }, { coefficient := 1, powers := [(10, 1), (27, 1), (34, 1), (37, 1), (46, 1), (63, 1)] }, { coefficient := 1, powers := [(10, 1), (27, 1), (43, 1), (63, 1)] }, { coefficient := 1, powers := [(10, 1), (32, 1), (34, 1), (37, 1), (38, 1), (63, 1)] }, { coefficient := -1, powers := [(15, 1), (20, 1), (32, 1), (38, 1), (43, 1), (63, 1)] }, { coefficient := -1, powers := [(15, 1), (25, 1), (32, 1), (38, 1), (43, 1), (63, 1)] }, { coefficient := -1, powers := [(15, 1), (32, 1), (34, 1), (37, 1), (38, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (25, 1), (27, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (25, 1), (35, 1), (41, 1)] }, { coefficient := -1, powers := [(10, 1), (25, 1), (27, 1), (46, 1)] }, { coefficient := -1, powers := [(10, 1), (25, 1), (32, 1), (38, 1)] }, { coefficient := 1, powers := [(15, 1), (25, 1), (32, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (32, 1), (37, 1), (43, 1)] }, { coefficient := -1, powers := [(15, 1), (32, 1), (37, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (27, 1), (63, 1)] }, { coefficient := -1, powers := [(15, 1), (27, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(10, 1), (23, 1), (27, 1), (63, 1)] }, { coefficient := 1, powers := [(15, 1), (23, 1), (27, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (10, 1), (18, 1), (27, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(10, 1), (32, 1), (37, 1)] }, { coefficient := 1, powers := [(15, 1), (32, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (13, 1), (27, 1)] }, { coefficient := 1, powers := [(10, 1), (20, 1), (27, 1), (45, 1)] }, { coefficient := -1, powers := [(10, 1), (27, 1), (43, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (27, 1), (60, 1)] }, { coefficient := 1, powers := [(6, 1), (35, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(57, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (7, 1), (27, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(0, 1), (7, 1), (35, 1), (41, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (10, 1), (27, 1), (46, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (27, 1), (50, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (35, 1), (41, 1), (50, 1)] }, { coefficient := -1, powers := [(10, 1), (27, 1), (46, 1), (50, 1)] }, { coefficient := -1, powers := [(10, 1), (32, 1), (38, 1), (50, 1)] }, { coefficient := 1, powers := [(15, 1), (32, 1), (38, 1), (50, 1)] }],
  [{ coefficient := -1, powers := [(10, 1), (13, 1), (27, 1), (46, 1)] }, { coefficient := -1, powers := [(10, 1), (32, 1), (38, 1), (43, 1)] }, { coefficient := 1, powers := [(15, 1), (32, 1), (38, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(27, 1)] }],
  [{ coefficient := 1, powers := [(10, 1)] }],
  [{ coefficient := -1, powers := [(10, 1), (20, 1), (27, 1), (46, 1)] }],
  [{ coefficient := -1, powers := [(10, 1), (27, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (10, 1), (27, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (27, 1), (60, 1)] }, { coefficient := -1, powers := [(7, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(10, 1), (27, 1), (46, 1)] }, { coefficient := 1, powers := [(10, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [(15, 1), (32, 1), (38, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(38, 1), (60, 1)] }, { coefficient := -1, powers := [(41, 1), (57, 1), (58, 1), (66, 1)] }, { coefficient := 1, powers := [(41, 1), (57, 1)] }, { coefficient := -1, powers := [(46, 1), (52, 1)] }, { coefficient := -1, powers := [(47, 1), (54, 1), (57, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (7, 1), (27, 1), (37, 1), (59, 1), (60, 1)] }, { coefficient := -1, powers := [(0, 1), (7, 1), (35, 1), (37, 1), (41, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (10, 1), (27, 1), (37, 1), (46, 1), (59, 1)] }, { coefficient := -1, powers := [(0, 1), (10, 1), (27, 1), (38, 1), (60, 1)] }, { coefficient := -1, powers := [(0, 1), (10, 1), (27, 1), (41, 1), (57, 1)] }, { coefficient := -1, powers := [(0, 1), (10, 1), (27, 1), (43, 1), (46, 1), (50, 1)] }, { coefficient := -1, powers := [(0, 1), (10, 1), (27, 1), (46, 1), (52, 1)] }, { coefficient := -1, powers := [(0, 1), (10, 1), (32, 1), (38, 1), (43, 1), (50, 1)] }, { coefficient := 1, powers := [(0, 1), (15, 1), (32, 1), (38, 1), (43, 1), (50, 1)] }, { coefficient := 1, powers := [(6, 1), (10, 1), (20, 1), (32, 1), (38, 1), (59, 1)] }, { coefficient := -1, powers := [(6, 1), (15, 1), (20, 1), (32, 1), (38, 1), (59, 1)] }, { coefficient := -1, powers := [(7, 1), (25, 1), (27, 1), (43, 1), (50, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (25, 1), (35, 1), (41, 1), (43, 1), (50, 1)] }, { coefficient := -1, powers := [(7, 1), (27, 1), (34, 1), (37, 1), (50, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (34, 1), (35, 1), (37, 1), (41, 1), (50, 1)] }, { coefficient := -2, powers := [(10, 1), (13, 1), (20, 1), (27, 1), (46, 1), (50, 1)] }, { coefficient := 1, powers := [(10, 1), (13, 1), (27, 1), (50, 1)] }, { coefficient := 1, powers := [(10, 1), (20, 1), (27, 1), (45, 1), (50, 1)] }, { coefficient := -1, powers := [(10, 1), (20, 1), (32, 1), (38, 1), (43, 1), (50, 1)] }, { coefficient := -1, powers := [(10, 1), (25, 1), (27, 1), (43, 1), (46, 1), (50, 1)] }, { coefficient := -1, powers := [(10, 1), (25, 1), (32, 1), (38, 1), (43, 1), (50, 1)] }, { coefficient := -1, powers := [(10, 1), (27, 1), (34, 1), (37, 1), (46, 1), (50, 1)] }, { coefficient := -1, powers := [(10, 1), (27, 1), (43, 1), (50, 1)] }, { coefficient := -1, powers := [(10, 1), (27, 1), (52, 1)] }, { coefficient := -1, powers := [(10, 1), (32, 1), (34, 1), (37, 1), (38, 1), (50, 1)] }, { coefficient := 1, powers := [(15, 1), (20, 1), (32, 1), (38, 1), (43, 1), (50, 1)] }, { coefficient := 1, powers := [(15, 1), (25, 1), (32, 1), (38, 1), (43, 1), (50, 1)] }, { coefficient := 1, powers := [(15, 1), (27, 1), (52, 1)] }, { coefficient := 1, powers := [(15, 1), (32, 1), (34, 1), (37, 1), (38, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (2, 1), (7, 1), (27, 1), (56, 1), (60, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (2, 1), (7, 1), (35, 1), (41, 1), (56, 1), (63, 1)] }, { coefficient := 1, powers := [(0, 1), (2, 1), (10, 1), (27, 1), (46, 1), (56, 1), (63, 1)] }, { coefficient := 1, powers := [(0, 1), (7, 1), (17, 1), (27, 1), (28, 1), (60, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (7, 1), (17, 1), (28, 1), (35, 1), (41, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (7, 1), (18, 1), (27, 1), (28, 1), (43, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(0, 1), (7, 1), (18, 1), (28, 1), (35, 1), (41, 1), (43, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (7, 1), (27, 1), (56, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (7, 1), (35, 1), (41, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (10, 1), (17, 1), (27, 1), (28, 1), (46, 1), (63, 1)] }, { coefficient := -2, powers := [(0, 1), (10, 1), (18, 1), (27, 1), (28, 1), (43, 1), (46, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (10, 1), (18, 1), (28, 1), (32, 1), (38, 1), (43, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (10, 1), (27, 1), (46, 1), (56, 1)] }, { coefficient := -1, powers := [(0, 1), (10, 1), (32, 1), (38, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (15, 1), (18, 1), (28, 1), (32, 1), (38, 1), (43, 1), (63, 1)] }, { coefficient := 1, powers := [(0, 1), (15, 1), (32, 1), (38, 1), (56, 1)] }, { coefficient := -1, powers := [(6, 1), (10, 1), (27, 1), (34, 1), (46, 1)] }, { coefficient := -1, powers := [(6, 1), (10, 1), (32, 1), (34, 1), (38, 1)] }, { coefficient := 1, powers := [(6, 1), (14, 1), (27, 1), (60, 1)] }, { coefficient := -1, powers := [(6, 1), (14, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(6, 1), (15, 1), (32, 1), (34, 1), (38, 1)] }, { coefficient := -1, powers := [(7, 1), (18, 1), (25, 1), (27, 1), (28, 1), (43, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(7, 1), (18, 1), (25, 1), (28, 1), (35, 1), (41, 1), (43, 1), (63, 1)] }, { coefficient := -1, powers := [(7, 1), (18, 1), (27, 1), (28, 1), (34, 1), (37, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(7, 1), (18, 1), (28, 1), (34, 1), (35, 1), (37, 1), (41, 1), (63, 1)] }, { coefficient := -1, powers := [(7, 1), (26, 1), (27, 1), (34, 1), (37, 1), (47, 1), (60, 1), (66, 1)] }, { coefficient := 1, powers := [(7, 1), (26, 1), (34, 1), (35, 1), (37, 1), (41, 1), (47, 1), (66, 1)] }, { coefficient := -2, powers := [(10, 1), (13, 1), (18, 1), (20, 1), (27, 1), (28, 1), (46, 1), (63, 1)] }, { coefficient := 1, powers := [(10, 1), (13, 1), (18, 1), (27, 1), (28, 1), (63, 1)] }, { coefficient := 1, powers := [(10, 1), (13, 1), (25, 1), (27, 1), (46, 1)] }, { coefficient := 1, powers := [(10, 1), (18, 1), (20, 1), (27, 1), (28, 1), (45, 1), (63, 1)] }, { coefficient := -1, powers := [(10, 1), (18, 1), (20, 1), (28, 1), (32, 1), (38, 1), (43, 1), (63, 1)] }, { coefficient := -1, powers := [(10, 1), (18, 1), (25, 1), (27, 1), (28, 1), (43, 1), (46, 1), (63, 1)] }, { coefficient := -1, powers := [(10, 1), (18, 1), (25, 1), (28, 1), (32, 1), (38, 1), (43, 1), (63, 1)] }, { coefficient := -1, powers := [(10, 1), (18, 1), (27, 1), (28, 1), (34, 1), (37, 1), (46, 1), (63, 1)] }, { coefficient := -1, powers := [(10, 1), (18, 1), (27, 1), (28, 1), (43, 1), (63, 1)] }, { coefficient := -1, powers := [(10, 1), (18, 1), (28, 1), (32, 1), (34, 1), (37, 1), (38, 1), (63, 1)] }, { coefficient := 1, powers := [(10, 1), (25, 1), (26, 1), (27, 1), (43, 1), (46, 1), (47, 1), (66, 1)] }, { coefficient := 1, powers := [(10, 1), (25, 1), (26, 1), (32, 1), (38, 1), (43, 1), (47, 1), (66, 1)] }, { coefficient := 1, powers := [(10, 1), (25, 1), (32, 1), (38, 1), (43, 1)] }, { coefficient := -1, powers := [(10, 1), (26, 1), (27, 1), (34, 1), (37, 1), (46, 1), (47, 1), (66, 1)] }, { coefficient := -1, powers := [(10, 1), (26, 1), (32, 1), (37, 1), (43, 1), (46, 1), (47, 1), (66, 1)] }, { coefficient := -1, powers := [(10, 1), (26, 1), (32, 1), (37, 1), (43, 1), (47, 1), (57, 1), (66, 1)] }, { coefficient := 1, powers := [(10, 1), (26, 1), (32, 1), (37, 1), (45, 1), (47, 1), (66, 1)] }, { coefficient := 1, powers := [(13, 1), (15, 1), (27, 1), (37, 1), (60, 1)] }, { coefficient := -1, powers := [(13, 1), (15, 1), (35, 1), (37, 1), (41, 1)] }, { coefficient := 1, powers := [(15, 1), (18, 1), (20, 1), (28, 1), (32, 1), (38, 1), (43, 1), (63, 1)] }, { coefficient := 1, powers := [(15, 1), (18, 1), (25, 1), (28, 1), (32, 1), (38, 1), (43, 1), (63, 1)] }, { coefficient := 1, powers := [(15, 1), (18, 1), (28, 1), (32, 1), (34, 1), (37, 1), (38, 1), (63, 1)] }, { coefficient := -1, powers := [(15, 1), (25, 1), (26, 1), (32, 1), (38, 1), (43, 1), (47, 1), (66, 1)] }, { coefficient := -1, powers := [(15, 1), (25, 1), (32, 1), (38, 1), (43, 1)] }, { coefficient := 1, powers := [(15, 1), (26, 1), (32, 1), (37, 1), (43, 1), (46, 1), (47, 1), (66, 1)] }, { coefficient := 1, powers := [(15, 1), (26, 1), (32, 1), (37, 1), (43, 1), (47, 1), (57, 1), (66, 1)] }, { coefficient := -1, powers := [(15, 1), (26, 1), (32, 1), (37, 1), (45, 1), (47, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (7, 1), (27, 1), (31, 1), (60, 1)] }, { coefficient := 1, powers := [(3, 1), (7, 1), (31, 1), (35, 1), (41, 1)] }, { coefficient := -1, powers := [(3, 1), (10, 1), (27, 1), (31, 1), (46, 1)] }, { coefficient := -1, powers := [(3, 1), (10, 1), (31, 1), (32, 1), (38, 1)] }, { coefficient := 1, powers := [(3, 1), (15, 1), (31, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [(7, 1), (9, 1), (20, 1), (27, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (9, 1), (20, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(7, 1), (20, 1), (27, 1), (50, 1), (60, 1)] }, { coefficient := -1, powers := [(7, 1), (20, 1), (35, 1), (41, 1), (50, 1)] }, { coefficient := -1, powers := [(9, 1), (10, 1), (20, 1), (32, 1), (38, 1)] }, { coefficient := 1, powers := [(9, 1), (15, 1), (20, 1), (32, 1), (38, 1)] }, { coefficient := 1, powers := [(10, 1), (20, 1), (27, 1), (46, 1), (50, 1)] }, { coefficient := 1, powers := [(10, 1), (20, 1), (32, 1), (38, 1), (50, 1)] }, { coefficient := -1, powers := [(15, 1), (20, 1), (32, 1), (38, 1), (50, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (32, 1), (57, 1)] }, { coefficient := 1, powers := [(7, 1), (9, 1), (27, 1), (34, 1), (37, 1), (60, 1)] }, { coefficient := -1, powers := [(7, 1), (9, 1), (34, 1), (35, 1), (37, 1), (41, 1)] }, { coefficient := -1, powers := [(7, 1), (22, 1), (60, 1)] }, { coefficient := -1, powers := [(9, 1), (10, 1), (25, 1), (27, 1), (43, 1), (46, 1)] }, { coefficient := -1, powers := [(9, 1), (10, 1), (25, 1), (32, 1), (38, 1), (43, 1)] }, { coefficient := 1, powers := [(9, 1), (10, 1), (27, 1), (34, 1), (37, 1), (46, 1)] }, { coefficient := 1, powers := [(9, 1), (10, 1), (32, 1), (37, 1), (43, 1), (46, 1)] }, { coefficient := 1, powers := [(9, 1), (10, 1), (32, 1), (37, 1), (43, 1), (57, 1)] }, { coefficient := -1, powers := [(9, 1), (10, 1), (32, 1), (37, 1), (45, 1)] }, { coefficient := 1, powers := [(9, 1), (15, 1), (25, 1), (32, 1), (38, 1), (43, 1)] }, { coefficient := -1, powers := [(9, 1), (15, 1), (32, 1), (37, 1), (43, 1), (46, 1)] }, { coefficient := -1, powers := [(9, 1), (15, 1), (32, 1), (37, 1), (43, 1), (57, 1)] }, { coefficient := 1, powers := [(9, 1), (15, 1), (32, 1), (37, 1), (45, 1)] }, { coefficient := 1, powers := [(10, 1), (22, 1), (52, 1)] }]
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
    ¬ ∀ index : Fin 36,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component37.SelectedLeafB5_2_3.selectedHasNoCommonZero

end Krenn.Component37.SelectedLeafB5_2_3
