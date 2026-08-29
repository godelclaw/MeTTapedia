import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component37.SelectedLeafB5_0_1

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "82f5875038399db1a2d9f0638651e1449d078c164295029d8a950ace04abca6e"
def certificateSHA256 : String := "9102a2ecd8287e2655cab68939aa8a29940404ade3553c95e4b3fa0f0732b3a7"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 28 → Fin 667 := ![
  13,
  17,
  300,
  301,
  313,
  427,
  455,
  466,
  470,
  580,
  581,
  583,
  591,
  602,
  603,
  606,
  612,
  645,
  647,
  648,
  655,
  658,
  660,
  661,
  662,
  664,
  665,
  666
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 28 → SparsePoly (Fin 65) := ![
  [{ coefficient := 1, powers := [(17, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (50, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (50, 1)] }, { coefficient := 1, powers := [(18, 1), (28, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (59, 1)] }, { coefficient := 1, powers := [(9, 1), (43, 1)] }, { coefficient := 1, powers := [(13, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(20, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(44, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (54, 1)] }, { coefficient := 1, powers := [(3, 1), (26, 1), (60, 1)] }, { coefficient := 1, powers := [(20, 1), (54, 1)] }, { coefficient := 1, powers := [(26, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (41, 1)] }, { coefficient := 1, powers := [(29, 1), (46, 1)] }, { coefficient := 1, powers := [(29, 1), (52, 1)] }, { coefficient := 1, powers := [(29, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1), (54, 1)] }, { coefficient := 1, powers := [(20, 1), (44, 1), (54, 1)] }, { coefficient := 1, powers := [(20, 1), (58, 1)] }, { coefficient := 1, powers := [(26, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1), (50, 1)] }, { coefficient := 1, powers := [(6, 1), (31, 1), (46, 1)] }, { coefficient := 1, powers := [(9, 1), (25, 1), (46, 1)] }, { coefficient := 1, powers := [(50, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1)] }, { coefficient := 1, powers := [(6, 1), (60, 1)] }, { coefficient := 1, powers := [(25, 1), (41, 1)] }, { coefficient := 1, powers := [(25, 1), (46, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (52, 1)] }, { coefficient := 1, powers := [(3, 1), (60, 1)] }, { coefficient := 1, powers := [(20, 1), (52, 1)] }, { coefficient := 1, powers := [(20, 1), (57, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (31, 1), (57, 1)] }, { coefficient := 1, powers := [(9, 1), (20, 1), (57, 1)] }, { coefficient := 1, powers := [(9, 1)] }, { coefficient := 1, powers := [(40, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (37, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (40, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (43, 1), (50, 1)] }, { coefficient := 1, powers := [(17, 1), (23, 1), (50, 1)] }, { coefficient := 1, powers := [(17, 1), (28, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1)] }, { coefficient := 1, powers := [(3, 1), (34, 1)] }, { coefficient := 1, powers := [(13, 1), (20, 1)] }, { coefficient := 1, powers := [(20, 1), (56, 1)] }, { coefficient := 1, powers := [(25, 1), (43, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (50, 1)] }, { coefficient := 1, powers := [(6, 1), (31, 1)] }, { coefficient := 1, powers := [(9, 1), (25, 1)] }, { coefficient := 1, powers := [(20, 1), (50, 1)] }, { coefficient := 1, powers := [(25, 1), (40, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (37, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1)] }, { coefficient := 1, powers := [(3, 1), (25, 1), (60, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1), (60, 1)] }, { coefficient := 1, powers := [(20, 1)] }, { coefficient := 1, powers := [(25, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1), (50, 1)] }, { coefficient := 1, powers := [(6, 1), (31, 1), (45, 1)] }, { coefficient := 1, powers := [(6, 1), (59, 1)] }, { coefficient := 1, powers := [(9, 1), (25, 1), (45, 1)] }, { coefficient := 1, powers := [(9, 1), (56, 1)] }, { coefficient := 1, powers := [(13, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (38, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (41, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(41, 1)] }, { coefficient := 1, powers := [(46, 1)] }, { coefficient := 1, powers := [(52, 1)] }, { coefficient := 1, powers := [(57, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (41, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (45, 1)] }, { coefficient := 1, powers := [(6, 1), (34, 1), (41, 1)] }, { coefficient := 1, powers := [(13, 1), (25, 1), (41, 1)] }, { coefficient := 1, powers := [(13, 1)] }, { coefficient := 1, powers := [(25, 1), (45, 1)] }, { coefficient := 1, powers := [(56, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (41, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (41, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (46, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (52, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (37, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (40, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (43, 1), (50, 1)] }, { coefficient := 1, powers := [(3, 1), (25, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (31, 1), (56, 1)] }, { coefficient := 1, powers := [(3, 1), (34, 1), (50, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (31, 1), (43, 1)] }, { coefficient := 1, powers := [(6, 1), (34, 1), (40, 1)] }, { coefficient := 1, powers := [(9, 1), (20, 1), (56, 1)] }, { coefficient := 1, powers := [(9, 1), (25, 1), (43, 1)] }, { coefficient := 1, powers := [(9, 1), (34, 1), (37, 1)] }, { coefficient := 1, powers := [(13, 1), (20, 1), (50, 1)] }, { coefficient := 1, powers := [(13, 1), (25, 1), (40, 1)] }, { coefficient := 1, powers := [(13, 1), (31, 1), (37, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(40, 1)] }],
  [{ coefficient := 1, powers := [(41, 1)] }],
  [{ coefficient := 1, powers := [(56, 1)] }],
  [{ coefficient := 1, powers := [(57, 1)] }],
  [{ coefficient := 1, powers := [(58, 1), (64, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 28 → SparsePoly (Fin 65) := ![
  [{ coefficient := 1, powers := [(0, 2), (23, 1), (46, 1), (63, 1)] }, { coefficient := 1, powers := [(0, 1), (6, 1), (23, 1), (60, 1), (63, 1)] }, { coefficient := 2, powers := [(0, 1), (23, 1), (25, 1), (46, 1), (63, 1)] }, { coefficient := 1, powers := [(0, 1), (23, 1), (37, 1), (60, 1), (63, 1)] }],
  [{ coefficient := -2, powers := [(0, 2), (23, 1), (43, 1), (46, 1), (63, 1)] }, { coefficient := -2, powers := [(0, 1), (6, 1), (23, 1), (43, 1), (60, 1), (63, 1)] }, { coefficient := -2, powers := [(0, 1), (13, 1), (20, 1), (23, 1), (46, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (13, 1), (23, 1), (37, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(0, 1), (13, 1), (23, 1), (63, 1)] }, { coefficient := 1, powers := [(0, 1), (20, 1), (23, 1), (45, 1), (63, 1)] }, { coefficient := -5, powers := [(0, 1), (23, 1), (25, 1), (43, 1), (46, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (23, 1), (34, 1), (37, 1), (46, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (23, 1), (37, 1), (43, 1), (60, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (23, 1), (43, 1), (63, 1)] }, { coefficient := -1, powers := [(6, 1), (13, 1), (20, 1), (23, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 2), (23, 1), (45, 1), (60, 1), (63, 1)] }, { coefficient := -1, powers := [(6, 1), (20, 1), (23, 1), (43, 1), (60, 1), (63, 1)] }, { coefficient := -1, powers := [(6, 1), (23, 1), (25, 1), (43, 1), (60, 1), (63, 1)] }, { coefficient := -1, powers := [(6, 1), (23, 1), (34, 1), (37, 1), (60, 1), (63, 1)] }, { coefficient := -4, powers := [(13, 1), (20, 1), (23, 1), (25, 1), (46, 1), (63, 1)] }, { coefficient := -1, powers := [(13, 1), (20, 1), (23, 1), (37, 1), (60, 1), (63, 1)] }, { coefficient := 2, powers := [(13, 1), (23, 1), (25, 1), (63, 1)] }, { coefficient := 1, powers := [(20, 1), (23, 1), (25, 1), (37, 1), (45, 1), (60, 1), (63, 1)] }, { coefficient := 2, powers := [(20, 1), (23, 1), (25, 1), (45, 1), (63, 1)] }, { coefficient := -2, powers := [(23, 1), (25, 2), (43, 1), (46, 1), (63, 1)] }, { coefficient := -2, powers := [(23, 1), (25, 1), (34, 1), (37, 1), (46, 1), (63, 1)] }, { coefficient := -1, powers := [(23, 1), (25, 1), (37, 1), (43, 1), (60, 1), (63, 1)] }, { coefficient := -2, powers := [(23, 1), (25, 1), (43, 1), (63, 1)] }, { coefficient := -1, powers := [(23, 1), (34, 1), (37, 2), (60, 1), (63, 1)] }],
  [{ coefficient := 2, powers := [(0, 2), (43, 1), (46, 1), (63, 1)] }, { coefficient := 2, powers := [(0, 1), (6, 1), (43, 1), (60, 1), (63, 1)] }, { coefficient := 2, powers := [(0, 1), (13, 1), (20, 1), (46, 1), (63, 1)] }, { coefficient := 1, powers := [(0, 1), (13, 1), (37, 1), (60, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (13, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (20, 1), (45, 1), (63, 1)] }, { coefficient := 5, powers := [(0, 1), (25, 1), (43, 1), (46, 1), (63, 1)] }, { coefficient := 1, powers := [(0, 1), (34, 1), (37, 1), (46, 1), (63, 1)] }, { coefficient := 1, powers := [(0, 1), (37, 1), (43, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(0, 1), (43, 1), (63, 1)] }, { coefficient := 1, powers := [(6, 1), (13, 1), (20, 1), (60, 1), (63, 1)] }, { coefficient := -1, powers := [(6, 1), (20, 2), (45, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1), (43, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(6, 1), (25, 1), (43, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(6, 1), (34, 1), (37, 1), (60, 1), (63, 1)] }, { coefficient := 4, powers := [(13, 1), (20, 1), (25, 1), (46, 1), (63, 1)] }, { coefficient := 1, powers := [(13, 1), (20, 1), (37, 1), (60, 1), (63, 1)] }, { coefficient := -2, powers := [(13, 1), (25, 1), (63, 1)] }, { coefficient := -1, powers := [(20, 1), (25, 1), (37, 1), (45, 1), (60, 1), (63, 1)] }, { coefficient := -2, powers := [(20, 1), (25, 1), (45, 1), (63, 1)] }, { coefficient := 2, powers := [(25, 2), (43, 1), (46, 1), (63, 1)] }, { coefficient := 2, powers := [(25, 1), (34, 1), (37, 1), (46, 1), (63, 1)] }, { coefficient := 1, powers := [(25, 1), (37, 1), (43, 1), (60, 1), (63, 1)] }, { coefficient := 2, powers := [(25, 1), (43, 1), (63, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 2), (60, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (25, 1), (46, 1)] }, { coefficient := -1, powers := [(6, 1), (25, 1), (60, 1)] }, { coefficient := -2, powers := [(25, 2), (46, 1)] }, { coefficient := -1, powers := [(25, 1), (37, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(26, 1), (46, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(44, 1), (46, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (18, 1), (25, 1), (63, 1)] }, { coefficient := 1, powers := [(18, 1), (20, 1), (25, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(46, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (13, 1)] }, { coefficient := 1, powers := [(0, 1), (20, 1), (45, 1)] }, { coefficient := -1, powers := [(0, 1), (43, 1)] }, { coefficient := 2, powers := [(13, 1), (25, 1)] }, { coefficient := 2, powers := [(20, 1), (25, 1), (45, 1)] }, { coefficient := -2, powers := [(25, 1), (43, 1)] }],
  [{ coefficient := -1, powers := [(20, 1), (62, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := -1, powers := [(25, 1), (62, 1)] }, { coefficient := 1, powers := [(26, 1), (44, 1), (46, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (25, 1), (43, 1), (46, 1)] }, { coefficient := -1, powers := [(0, 1), (34, 1), (37, 1), (46, 1)] }, { coefficient := 1, powers := [(6, 1), (25, 1), (43, 1), (60, 1)] }, { coefficient := -1, powers := [(6, 1), (34, 1), (37, 1), (60, 1)] }, { coefficient := 1, powers := [(13, 1), (25, 1), (37, 1), (60, 1)] }, { coefficient := 1, powers := [(20, 1), (25, 1), (37, 1), (45, 1), (60, 1)] }, { coefficient := 2, powers := [(25, 2), (43, 1), (46, 1)] }, { coefficient := -2, powers := [(25, 1), (34, 1), (37, 1), (46, 1)] }, { coefficient := -1, powers := [(34, 1), (37, 2), (60, 1)] }],
  [{ coefficient := -1, powers := [(0, 2), (46, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (6, 1), (60, 1), (63, 1)] }, { coefficient := -2, powers := [(0, 1), (25, 1), (46, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (37, 1), (60, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (46, 1), (50, 1)] }, { coefficient := -1, powers := [(6, 1), (50, 1), (60, 1)] }, { coefficient := -2, powers := [(25, 1), (46, 1), (50, 1)] }, { coefficient := -1, powers := [(37, 1), (50, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (13, 1), (46, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1), (45, 1), (60, 1)] }, { coefficient := -1, powers := [(6, 1), (43, 1), (60, 1)] }, { coefficient := -2, powers := [(13, 1), (25, 1), (46, 1)] }, { coefficient := -1, powers := [(13, 1), (37, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(62, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (20, 1), (46, 1)] }, { coefficient := -1, powers := [(6, 1), (20, 1), (60, 1)] }, { coefficient := -2, powers := [(20, 1), (25, 1), (46, 1)] }, { coefficient := -1, powers := [(20, 1), (37, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (25, 1), (62, 1)] }, { coefficient := 1, powers := [(25, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (37, 1), (50, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (25, 1), (63, 1)] }, { coefficient := -1, powers := [(20, 1), (25, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1)] }, { coefficient := 1, powers := [(6, 1), (60, 1)] }, { coefficient := 2, powers := [(25, 1), (46, 1)] }, { coefficient := 1, powers := [(37, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(20, 1), (25, 1), (38, 1), (60, 1)] }, { coefficient := -1, powers := [(20, 1), (25, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(20, 1), (46, 1)] }, { coefficient := 1, powers := [(25, 1), (52, 1)] }, { coefficient := -1, powers := [(37, 1), (60, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 2), (37, 1), (46, 1), (59, 1)] }, { coefficient := -1, powers := [(0, 2), (43, 1), (46, 1), (50, 1)] }, { coefficient := 1, powers := [(0, 1), (6, 1), (37, 1), (59, 1), (60, 1)] }, { coefficient := -1, powers := [(0, 1), (6, 1), (43, 1), (50, 1), (60, 1)] }, { coefficient := -2, powers := [(0, 1), (13, 1), (20, 1), (46, 1), (50, 1)] }, { coefficient := -1, powers := [(0, 1), (13, 1), (37, 1), (50, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (13, 1), (50, 1)] }, { coefficient := 1, powers := [(0, 1), (20, 1), (45, 1), (50, 1)] }, { coefficient := 2, powers := [(0, 1), (25, 1), (37, 1), (46, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (25, 1), (38, 1), (60, 1)] }, { coefficient := -3, powers := [(0, 1), (25, 1), (43, 1), (46, 1), (50, 1)] }, { coefficient := 1, powers := [(0, 1), (25, 1), (46, 1), (52, 1)] }, { coefficient := -1, powers := [(0, 1), (34, 1), (37, 1), (46, 1), (50, 1)] }, { coefficient := 1, powers := [(0, 1), (37, 2), (59, 1), (60, 1)] }, { coefficient := -1, powers := [(0, 1), (43, 1), (50, 1)] }, { coefficient := -1, powers := [(6, 1), (13, 1), (20, 1), (50, 1), (60, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 2), (45, 1), (50, 1), (60, 1)] }, { coefficient := -1, powers := [(6, 1), (20, 1), (43, 1), (50, 1), (60, 1)] }, { coefficient := -1, powers := [(6, 1), (25, 1), (43, 1), (50, 1), (60, 1)] }, { coefficient := -1, powers := [(6, 1), (34, 1), (37, 1), (50, 1), (60, 1)] }, { coefficient := -4, powers := [(13, 1), (20, 1), (25, 1), (46, 1), (50, 1)] }, { coefficient := -1, powers := [(13, 1), (20, 1), (37, 1), (50, 1), (60, 1)] }, { coefficient := 2, powers := [(13, 1), (25, 1), (50, 1)] }, { coefficient := 1, powers := [(20, 1), (25, 1), (37, 1), (45, 1), (50, 1), (60, 1)] }, { coefficient := 1, powers := [(20, 1), (25, 1), (38, 1), (60, 1)] }, { coefficient := 2, powers := [(20, 1), (25, 1), (45, 1), (50, 1)] }, { coefficient := 1, powers := [(20, 1), (25, 1), (46, 1), (52, 1)] }, { coefficient := -2, powers := [(25, 2), (43, 1), (46, 1), (50, 1)] }, { coefficient := -2, powers := [(25, 1), (34, 1), (37, 1), (46, 1), (50, 1)] }, { coefficient := -1, powers := [(25, 1), (37, 1), (43, 1), (50, 1), (60, 1)] }, { coefficient := -2, powers := [(25, 1), (43, 1), (50, 1)] }, { coefficient := -1, powers := [(34, 1), (37, 2), (50, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(0, 2), (2, 1), (46, 1), (56, 1), (63, 1)] }, { coefficient := 1, powers := [(0, 2), (17, 1), (28, 1), (46, 1), (63, 1)] }, { coefficient := -2, powers := [(0, 2), (18, 1), (28, 1), (43, 1), (46, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 2), (25, 1), (43, 1), (46, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 2), (34, 1), (37, 1), (46, 1), (57, 1)] }, { coefficient := -1, powers := [(0, 2), (46, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (2, 1), (6, 1), (56, 1), (60, 1), (63, 1)] }, { coefficient := 2, powers := [(0, 1), (2, 1), (25, 1), (46, 1), (56, 1), (63, 1)] }, { coefficient := 1, powers := [(0, 1), (2, 1), (37, 1), (56, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(0, 1), (6, 1), (17, 1), (28, 1), (60, 1), (63, 1)] }, { coefficient := -2, powers := [(0, 1), (6, 1), (18, 1), (28, 1), (43, 1), (60, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (6, 1), (25, 1), (43, 1), (57, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (6, 1), (34, 1), (37, 1), (57, 1), (60, 1)] }, { coefficient := -1, powers := [(0, 1), (6, 1), (34, 1), (46, 1)] }, { coefficient := -1, powers := [(0, 1), (6, 1), (56, 1), (60, 1)] }, { coefficient := -2, powers := [(0, 1), (13, 1), (18, 1), (20, 1), (28, 1), (46, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (13, 1), (18, 1), (28, 1), (37, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(0, 1), (13, 1), (18, 1), (28, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (13, 1), (25, 1), (37, 1), (57, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (13, 1), (25, 1), (46, 1)] }, { coefficient := 2, powers := [(0, 1), (17, 1), (25, 1), (28, 1), (46, 1), (63, 1)] }, { coefficient := 1, powers := [(0, 1), (17, 1), (28, 1), (37, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(0, 1), (18, 1), (20, 1), (28, 1), (45, 1), (63, 1)] }, { coefficient := -5, powers := [(0, 1), (18, 1), (25, 1), (28, 1), (43, 1), (46, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (18, 1), (28, 1), (34, 1), (37, 1), (46, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (18, 1), (28, 1), (37, 1), (43, 1), (60, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (18, 1), (28, 1), (43, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (20, 1), (25, 1), (37, 1), (45, 1), (57, 1), (60, 1)] }, { coefficient := -2, powers := [(0, 1), (25, 2), (43, 1), (46, 1), (57, 1)] }, { coefficient := 2, powers := [(0, 1), (25, 1), (34, 1), (37, 1), (46, 1), (57, 1)] }, { coefficient := -1, powers := [(0, 1), (25, 1), (43, 1), (46, 1)] }, { coefficient := -2, powers := [(0, 1), (25, 1), (46, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (34, 1), (37, 2), (57, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (34, 1), (37, 1), (46, 1)] }, { coefficient := -1, powers := [(0, 1), (37, 1), (56, 1), (60, 1)] }, { coefficient := -1, powers := [(6, 2), (34, 1), (60, 1)] }, { coefficient := -1, powers := [(6, 1), (13, 1), (18, 1), (20, 1), (28, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(6, 1), (18, 1), (20, 2), (28, 1), (45, 1), (60, 1), (63, 1)] }, { coefficient := -1, powers := [(6, 1), (18, 1), (20, 1), (28, 1), (43, 1), (60, 1), (63, 1)] }, { coefficient := -1, powers := [(6, 1), (18, 1), (25, 1), (28, 1), (43, 1), (60, 1), (63, 1)] }, { coefficient := -1, powers := [(6, 1), (18, 1), (28, 1), (34, 1), (37, 1), (60, 1), (63, 1)] }, { coefficient := -1, powers := [(6, 1), (20, 1), (25, 1), (45, 1), (60, 1)] }, { coefficient := -2, powers := [(6, 1), (25, 1), (34, 1), (46, 1)] }, { coefficient := -4, powers := [(13, 1), (18, 1), (20, 1), (25, 1), (28, 1), (46, 1), (63, 1)] }, { coefficient := -1, powers := [(13, 1), (18, 1), (20, 1), (28, 1), (37, 1), (60, 1), (63, 1)] }, { coefficient := 2, powers := [(13, 1), (18, 1), (25, 1), (28, 1), (63, 1)] }, { coefficient := 2, powers := [(13, 1), (25, 2), (46, 1)] }, { coefficient := 1, powers := [(18, 1), (20, 1), (25, 1), (28, 1), (37, 1), (45, 1), (60, 1), (63, 1)] }, { coefficient := 2, powers := [(18, 1), (20, 1), (25, 1), (28, 1), (45, 1), (63, 1)] }, { coefficient := -2, powers := [(18, 1), (25, 2), (28, 1), (43, 1), (46, 1), (63, 1)] }, { coefficient := -2, powers := [(18, 1), (25, 1), (28, 1), (34, 1), (37, 1), (46, 1), (63, 1)] }, { coefficient := -1, powers := [(18, 1), (25, 1), (28, 1), (37, 1), (43, 1), (60, 1), (63, 1)] }, { coefficient := -2, powers := [(18, 1), (25, 1), (28, 1), (43, 1), (63, 1)] }, { coefficient := -1, powers := [(18, 1), (28, 1), (34, 1), (37, 2), (60, 1), (63, 1)] }, { coefficient := -1, powers := [(20, 1), (25, 1), (37, 1), (45, 1), (60, 1)] }, { coefficient := -2, powers := [(25, 2), (43, 1), (46, 1)] }, { coefficient := 2, powers := [(25, 1), (34, 1), (37, 1), (46, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 2), (60, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (2, 1), (25, 1), (57, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (20, 1), (25, 1), (57, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 1), (20, 1), (37, 1), (50, 1), (56, 1), (60, 1)] }, { coefficient := -1, powers := [(0, 1), (25, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (20, 1), (25, 1), (57, 1), (63, 1)] }, { coefficient := -1, powers := [(6, 1), (20, 1), (34, 1), (37, 1), (50, 1), (60, 1)] }, { coefficient := -1, powers := [(13, 1), (20, 1), (25, 1), (37, 1), (50, 1), (60, 1)] }, { coefficient := -2, powers := [(25, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (3, 1), (31, 1), (46, 1)] }, { coefficient := 1, powers := [(0, 1), (20, 1), (46, 1), (50, 1)] }, { coefficient := -1, powers := [(3, 1), (6, 1), (31, 1), (60, 1)] }, { coefficient := -2, powers := [(3, 1), (25, 1), (31, 1), (46, 1)] }, { coefficient := -1, powers := [(3, 1), (31, 1), (37, 1), (60, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1), (50, 1), (60, 1)] }, { coefficient := 2, powers := [(20, 1), (25, 1), (46, 1), (50, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (3, 1), (25, 1), (31, 1), (43, 1), (46, 1)] }, { coefficient := 1, powers := [(0, 1), (3, 1), (31, 1), (34, 1), (37, 1), (46, 1)] }, { coefficient := -1, powers := [(0, 1), (9, 1), (20, 1), (25, 1), (43, 1), (46, 1)] }, { coefficient := 1, powers := [(0, 1), (9, 1), (20, 1), (34, 1), (37, 1), (46, 1)] }, { coefficient := -1, powers := [(3, 1), (6, 1), (25, 1), (31, 1), (43, 1), (60, 1)] }, { coefficient := 1, powers := [(3, 1), (6, 1), (31, 1), (34, 1), (37, 1), (60, 1)] }, { coefficient := -1, powers := [(3, 1), (13, 1), (25, 1), (31, 1), (37, 1), (60, 1)] }, { coefficient := -1, powers := [(3, 1), (20, 1), (25, 1), (31, 1), (37, 1), (45, 1), (60, 1)] }, { coefficient := -2, powers := [(3, 1), (25, 2), (31, 1), (43, 1), (46, 1)] }, { coefficient := 2, powers := [(3, 1), (25, 1), (31, 1), (34, 1), (37, 1), (46, 1)] }, { coefficient := 1, powers := [(3, 1), (31, 1), (34, 1), (37, 2), (60, 1)] }, { coefficient := -1, powers := [(6, 1), (9, 1), (20, 1), (25, 1), (43, 1), (60, 1)] }, { coefficient := 1, powers := [(6, 1), (9, 1), (20, 1), (34, 1), (37, 1), (60, 1)] }, { coefficient := -1, powers := [(9, 1), (13, 1), (20, 1), (25, 1), (37, 1), (60, 1)] }, { coefficient := -1, powers := [(9, 1), (20, 2), (25, 1), (37, 1), (45, 1), (60, 1)] }, { coefficient := -2, powers := [(9, 1), (20, 1), (25, 2), (43, 1), (46, 1)] }, { coefficient := 2, powers := [(9, 1), (20, 1), (25, 1), (34, 1), (37, 1), (46, 1)] }, { coefficient := 1, powers := [(9, 1), (20, 1), (34, 1), (37, 2), (60, 1)] }, { coefficient := -1, powers := [(20, 1), (26, 1), (44, 1), (46, 1), (64, 1)] }, { coefficient := -1, powers := [(25, 1)] }],
  [{ coefficient := -1, powers := [(20, 1), (46, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
/-- Lean replays the exact selected-row integer certificate. -/
theorem constantIdentity :
    ∑ index, (multipliers index).toPoly *
      (selectedEquations index).toPoly = C (2 : ℤ) := by
  simp (config := { maxSteps := 1000000 })
    [Fin.sum_univ_succ, multipliers, selectedEquations,
    SparsePoly.toPoly, SparseTerm.toPoly]
  ring

/-- The selected rows have no common zero in a characteristic-zero ring. -/
theorem selectedHasNoCommonZero {R : Type*} [CommRing R] [Nontrivial R] [CharZero R]
    (values : Fin 65 → R) :
    ¬ ∀ index : Fin 28,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((2 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (2 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (2 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component37.SelectedLeafB5_0_1.selectedHasNoCommonZero

end Krenn.Component37.SelectedLeafB5_0_1
