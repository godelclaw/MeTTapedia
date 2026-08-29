import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component60.SelectedLeafB6_1_6_5

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "aea8c480bef82e5377bcba0f91a8b8e5de11e6954842f6f2ac6995def2c069b4"
def certificateSHA256 : String := "ecb4e4b7531007d2e1c9193c2bcb810e0591e4dc6325130cb215a0a819df7e4a"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 28 → Fin 668 := ![
  10,
  13,
  24,
  148,
  151,
  179,
  256,
  298,
  303,
  304,
  353,
  395,
  458,
  578,
  582,
  587,
  600,
  601,
  605,
  612,
  653,
  654,
  657,
  659,
  660,
  663,
  666,
  667
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 28 → SparsePoly (Fin 68) := ![
  [{ coefficient := 1, powers := [(10, 1), (29, 1)] }],
  [{ coefficient := 1, powers := [(15, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (30, 1)] }, { coefficient := 1, powers := [(15, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (29, 1)] }, { coefficient := 1, powers := [(29, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (40, 1)] }, { coefficient := 1, powers := [(29, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (29, 1), (40, 1)] }, { coefficient := 1, powers := [(29, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (49, 1)] }, { coefficient := 1, powers := [(15, 1), (22, 1), (49, 1)] }, { coefficient := 1, powers := [(15, 1), (27, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (58, 1)] }, { coefficient := 1, powers := [(9, 1), (42, 1)] }, { coefficient := 1, powers := [(13, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (45, 1)] }, { coefficient := 1, powers := [(9, 1), (56, 1)] }, { coefficient := 1, powers := [(30, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (30, 1), (56, 1)] }, { coefficient := 1, powers := [(7, 1), (30, 1), (45, 1)] }, { coefficient := 1, powers := [(15, 1), (30, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(15, 1), (20, 1), (49, 1)] }, { coefficient := 1, powers := [(15, 1), (25, 1), (39, 1)] }, { coefficient := 1, powers := [(15, 1), (30, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1), (49, 1)] }, { coefficient := 1, powers := [(6, 1), (30, 1), (45, 1)] }, { coefficient := 1, powers := [(9, 1), (25, 1), (45, 1)] }, { coefficient := 1, powers := [(49, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1)] }, { coefficient := 1, powers := [(6, 1), (59, 1)] }, { coefficient := 1, powers := [(25, 1), (40, 1)] }, { coefficient := 1, powers := [(25, 1), (45, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(3, 1), (30, 1), (56, 1)] }, { coefficient := 1, powers := [(9, 1), (20, 1), (56, 1)] }, { coefficient := 1, powers := [(9, 1)] }, { coefficient := 1, powers := [(39, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (36, 1), (58, 1)] }, { coefficient := 1, powers := [(1, 1), (39, 1), (55, 1)] }, { coefficient := 1, powers := [(1, 1), (42, 1), (49, 1)] }, { coefficient := 1, powers := [(14, 1), (22, 1), (49, 1)] }, { coefficient := 1, powers := [(14, 1), (27, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1)] }, { coefficient := 1, powers := [(3, 1), (33, 1)] }, { coefficient := 1, powers := [(13, 1), (20, 1)] }, { coefficient := 1, powers := [(20, 1), (55, 1)] }, { coefficient := 1, powers := [(25, 1), (42, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (49, 1)] }, { coefficient := 1, powers := [(6, 1), (30, 1)] }, { coefficient := 1, powers := [(9, 1), (25, 1)] }, { coefficient := 1, powers := [(20, 1), (49, 1)] }, { coefficient := 1, powers := [(25, 1), (39, 1)] }, { coefficient := 1, powers := [(30, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (51, 1)] }, { coefficient := 1, powers := [(23, 1), (56, 1)] }, { coefficient := 1, powers := [(28, 1), (40, 1)] }, { coefficient := 1, powers := [(28, 1), (45, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1), (49, 1)] }, { coefficient := 1, powers := [(6, 1), (30, 1), (44, 1)] }, { coefficient := 1, powers := [(6, 1), (58, 1)] }, { coefficient := 1, powers := [(9, 1), (25, 1), (44, 1)] }, { coefficient := 1, powers := [(9, 1), (55, 1)] }, { coefficient := 1, powers := [(13, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (36, 1), (58, 1)] }, { coefficient := 1, powers := [(0, 1), (39, 1), (55, 1)] }, { coefficient := 1, powers := [(0, 1), (42, 1), (49, 1)] }, { coefficient := 1, powers := [(3, 1), (25, 1), (58, 1)] }, { coefficient := 1, powers := [(3, 1), (30, 1), (55, 1)] }, { coefficient := 1, powers := [(3, 1), (33, 1), (49, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1), (58, 1)] }, { coefficient := 1, powers := [(6, 1), (30, 1), (42, 1)] }, { coefficient := 1, powers := [(6, 1), (33, 1), (39, 1)] }, { coefficient := 1, powers := [(9, 1), (20, 1), (55, 1)] }, { coefficient := 1, powers := [(9, 1), (25, 1), (42, 1)] }, { coefficient := 1, powers := [(9, 1), (33, 1), (36, 1)] }, { coefficient := 1, powers := [(13, 1), (20, 1), (49, 1)] }, { coefficient := 1, powers := [(13, 1), (25, 1), (39, 1)] }, { coefficient := 1, powers := [(13, 1), (30, 1), (36, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1), (37, 1), (59, 1)] }, { coefficient := 1, powers := [(1, 1), (40, 1), (56, 1)] }, { coefficient := 1, powers := [(1, 1), (45, 1), (51, 1)] }, { coefficient := 1, powers := [(4, 1), (28, 1), (59, 1)] }, { coefficient := 1, powers := [(4, 1), (31, 1), (56, 1)] }, { coefficient := 1, powers := [(4, 1), (34, 1), (51, 1)] }, { coefficient := 1, powers := [(7, 1), (23, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (31, 1), (45, 1)] }, { coefficient := 1, powers := [(7, 1), (34, 1), (40, 1)] }, { coefficient := 1, powers := [(10, 1), (23, 1), (56, 1)] }, { coefficient := 1, powers := [(10, 1), (28, 1), (45, 1)] }, { coefficient := 1, powers := [(10, 1), (34, 1), (37, 1)] }, { coefficient := 1, powers := [(15, 1), (23, 1), (51, 1)] }, { coefficient := 1, powers := [(15, 1), (28, 1), (40, 1)] }, { coefficient := 1, powers := [(15, 1), (31, 1), (37, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(39, 1)] }],
  [{ coefficient := 1, powers := [(40, 1)] }],
  [{ coefficient := 1, powers := [(56, 1), (65, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(28, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (67, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 28 → SparsePoly (Fin 68) := ![
  [{ coefficient := -1, powers := [(13, 1), (23, 1), (30, 1), (36, 1), (51, 1), (67, 1)] }, { coefficient := -1, powers := [(13, 1), (30, 1), (31, 1), (36, 1), (37, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (22, 1), (42, 1), (62, 1)] }, { coefficient := -1, powers := [(13, 1), (20, 1), (23, 1), (36, 1), (51, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (49, 1), (67, 1)] }, { coefficient := -1, powers := [(20, 1), (49, 1), (67, 1)] }, { coefficient := -1, powers := [(25, 1), (49, 1), (67, 1)] }, { coefficient := -1, powers := [(30, 1), (36, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (23, 1), (36, 1), (59, 1)] }, { coefficient := -1, powers := [(13, 1), (31, 1), (36, 1), (45, 1)] }, { coefficient := -1, powers := [(13, 1), (34, 1), (36, 1), (45, 1), (51, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(1, 1), (13, 1), (36, 1), (45, 1), (59, 1), (67, 1)] }, { coefficient := -1, powers := [(1, 1), (13, 1), (36, 1), (56, 1), (59, 1), (67, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1), (25, 1), (44, 1), (59, 1), (67, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1), (55, 1), (59, 1), (67, 1)] }, { coefficient := 1, powers := [(13, 1), (15, 1), (23, 1), (25, 1), (36, 1), (51, 1), (59, 1), (67, 1)] }, { coefficient := 1, powers := [(13, 1), (15, 1), (34, 1), (36, 1), (45, 1), (51, 1), (65, 1), (67, 1)] }, { coefficient := 1, powers := [(13, 1), (15, 1), (34, 1), (36, 1), (51, 1), (56, 1), (65, 1), (67, 1)] }, { coefficient := -1, powers := [(20, 1), (55, 1), (56, 1), (65, 1), (67, 1)] }, { coefficient := 1, powers := [(20, 1), (55, 1), (67, 1)] }, { coefficient := -1, powers := [(25, 1), (42, 1), (67, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1), (67, 1)] }, { coefficient := -1, powers := [(55, 1), (65, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (6, 1), (20, 2), (44, 1), (49, 1), (59, 1), (67, 1)] }, { coefficient := 1, powers := [(0, 1), (6, 1), (20, 1), (30, 1), (36, 1), (44, 1), (59, 1), (67, 1)] }, { coefficient := -1, powers := [(0, 1), (6, 1), (20, 1), (30, 1), (44, 1), (67, 1)] }, { coefficient := -1, powers := [(0, 1), (6, 1), (20, 1), (58, 1), (67, 1)] }, { coefficient := 1, powers := [(0, 1), (13, 1), (15, 1), (20, 1), (23, 1), (36, 1), (49, 1), (51, 1), (59, 1), (67, 1)] }, { coefficient := 1, powers := [(0, 1), (13, 1), (15, 1), (23, 1), (30, 1), (36, 2), (51, 1), (59, 1), (67, 1)] }, { coefficient := -1, powers := [(0, 1), (13, 1), (15, 1), (23, 1), (30, 1), (36, 1), (51, 1), (67, 1)] }, { coefficient := -1, powers := [(0, 1), (14, 1), (20, 1), (22, 1), (49, 1), (62, 1), (67, 1)] }, { coefficient := -1, powers := [(0, 1), (14, 1), (22, 1), (30, 1), (36, 1), (62, 1), (67, 1)] }, { coefficient := 1, powers := [(1, 1), (13, 1), (30, 1), (36, 1), (51, 1), (67, 1)] }, { coefficient := 1, powers := [(6, 1), (13, 1), (20, 2), (49, 1), (59, 1), (67, 1)] }, { coefficient := 1, powers := [(6, 1), (13, 1), (20, 1), (30, 1), (36, 1), (59, 1), (67, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 3), (44, 1), (49, 1), (59, 1), (67, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 2), (30, 1), (36, 1), (44, 1), (59, 1), (67, 1)] }, { coefficient := -1, powers := [(6, 1), (20, 1), (25, 1), (30, 1), (44, 1), (67, 1)] }, { coefficient := -1, powers := [(6, 1), (20, 1), (25, 1), (58, 1), (67, 1)] }, { coefficient := 1, powers := [(7, 1), (13, 1), (30, 1), (31, 1), (36, 1), (67, 1)] }, { coefficient := 1, powers := [(13, 1), (15, 1), (20, 2), (23, 1), (36, 1), (49, 1), (51, 1), (59, 1), (67, 1)] }, { coefficient := 1, powers := [(13, 1), (15, 1), (20, 1), (23, 1), (30, 1), (36, 2), (51, 1), (59, 1), (67, 1)] }, { coefficient := -1, powers := [(13, 1), (15, 1), (23, 1), (25, 1), (30, 1), (36, 1), (51, 1), (67, 1)] }, { coefficient := -1, powers := [(20, 2), (49, 1), (55, 1), (67, 1)] }, { coefficient := -1, powers := [(20, 1), (30, 1), (36, 1), (55, 1), (67, 1)] }, { coefficient := -1, powers := [(20, 1), (33, 1), (36, 1), (49, 1), (67, 1)] }, { coefficient := -1, powers := [(30, 1), (33, 1), (36, 2), (67, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (20, 2), (49, 1), (59, 1), (67, 1)] }, { coefficient := -1, powers := [(6, 1), (20, 1), (30, 1), (67, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (42, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(25, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (13, 1), (36, 1), (59, 1)] }, { coefficient := -1, powers := [(13, 1), (15, 1), (34, 1), (36, 1), (51, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (31, 1), (36, 1)] }, { coefficient := 1, powers := [(13, 1), (34, 1), (36, 1), (51, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (23, 1), (36, 1), (51, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (6, 1), (20, 1), (44, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (13, 1), (15, 1), (23, 1), (36, 1), (51, 1), (59, 1)] }, { coefficient := -1, powers := [(0, 1), (14, 1), (22, 1), (62, 1)] }, { coefficient := 1, powers := [(6, 1), (13, 1), (20, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 2), (44, 1), (59, 1)] }, { coefficient := 1, powers := [(13, 1), (15, 1), (20, 1), (23, 1), (36, 1), (51, 1), (59, 1)] }, { coefficient := -1, powers := [(20, 1), (55, 1)] }, { coefficient := -1, powers := [(33, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (20, 1), (30, 1), (44, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1), (58, 1)] }, { coefficient := 1, powers := [(13, 1), (15, 1), (23, 1), (30, 1), (36, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(55, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(49, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (6, 1), (20, 1), (44, 1), (45, 1), (59, 1)] }, { coefficient := -1, powers := [(0, 1), (13, 1), (15, 1), (23, 1), (36, 1), (45, 1), (51, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (14, 1), (22, 1), (45, 1), (62, 1)] }, { coefficient := -1, powers := [(6, 1), (13, 1), (20, 1), (45, 1), (59, 1)] }, { coefficient := -1, powers := [(6, 1), (20, 2), (44, 1), (45, 1), (59, 1)] }, { coefficient := -1, powers := [(13, 1), (15, 1), (20, 1), (23, 1), (36, 1), (45, 1), (51, 1), (59, 1)] }, { coefficient := -1, powers := [(13, 1), (15, 1), (23, 1), (36, 1), (51, 1), (59, 1)] }, { coefficient := 1, powers := [(20, 1), (45, 1), (55, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1), (45, 1)] }, { coefficient := 1, powers := [(42, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (13, 1), (30, 1), (36, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (20, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(13, 1), (30, 1), (36, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (36, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (1, 1), (55, 1), (62, 1)] }, { coefficient := 1, powers := [(0, 1), (6, 1), (20, 1), (25, 1), (44, 1), (45, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (13, 1), (15, 1), (23, 1), (25, 1), (36, 1), (45, 1), (51, 1), (59, 1)] }, { coefficient := -1, powers := [(0, 1), (14, 1), (22, 1), (25, 1), (45, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 1), (14, 1), (27, 1), (62, 1)] }, { coefficient := 1, powers := [(0, 1), (15, 1), (27, 1), (42, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 1), (55, 1), (56, 1), (65, 1)] }, { coefficient := 1, powers := [(0, 1), (55, 1)] }, { coefficient := 1, powers := [(1, 1), (13, 1), (29, 1), (36, 1), (45, 1), (59, 1), (67, 1)] }, { coefficient := 1, powers := [(1, 1), (13, 1), (29, 1), (36, 1), (56, 1), (59, 1), (67, 1)] }, { coefficient := 1, powers := [(6, 1), (13, 1), (20, 1), (25, 1), (45, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 2), (25, 1), (44, 1), (45, 1), (59, 1)] }, { coefficient := -1, powers := [(6, 1), (20, 1), (25, 1), (29, 1), (44, 1), (59, 1), (67, 1)] }, { coefficient := -1, powers := [(6, 1), (20, 1), (29, 1), (55, 1), (59, 1), (67, 1)] }, { coefficient := 1, powers := [(6, 1), (33, 1)] }, { coefficient := 1, powers := [(13, 1), (15, 1), (20, 1), (23, 1), (25, 1), (36, 1), (45, 1), (51, 1), (59, 1)] }, { coefficient := -1, powers := [(13, 1), (15, 1), (23, 1), (25, 1), (29, 1), (36, 1), (51, 1), (59, 1), (67, 1)] }, { coefficient := -1, powers := [(13, 1), (15, 1), (23, 1), (36, 1), (59, 1)] }, { coefficient := -1, powers := [(13, 1), (15, 1), (29, 1), (34, 1), (36, 1), (45, 1), (51, 1), (65, 1), (67, 1)] }, { coefficient := -1, powers := [(13, 1), (15, 1), (29, 1), (34, 1), (36, 1), (51, 1), (56, 1), (65, 1), (67, 1)] }, { coefficient := 1, powers := [(13, 1), (15, 1), (31, 1), (36, 1), (45, 1)] }, { coefficient := 1, powers := [(13, 1), (15, 1), (34, 1), (36, 1), (45, 1), (51, 1), (65, 1)] }, { coefficient := -1, powers := [(20, 1), (25, 1), (45, 1), (55, 1)] }, { coefficient := 1, powers := [(20, 1), (29, 1), (55, 1), (56, 1), (65, 1), (67, 1)] }, { coefficient := -1, powers := [(20, 1), (29, 1), (55, 1), (67, 1)] }, { coefficient := 1, powers := [(25, 1), (29, 1), (42, 1), (67, 1)] }, { coefficient := -1, powers := [(25, 1), (33, 1), (36, 1), (45, 1)] }, { coefficient := -1, powers := [(25, 1), (42, 1)] }, { coefficient := -1, powers := [(29, 1), (33, 1), (36, 1), (67, 1)] }, { coefficient := 1, powers := [(29, 1), (55, 1), (65, 1), (67, 1)] }, { coefficient := -1, powers := [(55, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (6, 1), (20, 2), (29, 1), (44, 1), (49, 1), (59, 1), (67, 1)] }, { coefficient := -1, powers := [(0, 1), (6, 1), (20, 1), (29, 1), (30, 1), (36, 1), (44, 1), (59, 1), (67, 1)] }, { coefficient := 1, powers := [(0, 1), (6, 1), (20, 1), (29, 1), (30, 1), (44, 1), (67, 1)] }, { coefficient := 1, powers := [(0, 1), (6, 1), (20, 1), (29, 1), (58, 1), (67, 1)] }, { coefficient := -1, powers := [(0, 1), (13, 1), (15, 1), (20, 1), (23, 1), (29, 1), (36, 1), (49, 1), (51, 1), (59, 1), (67, 1)] }, { coefficient := -1, powers := [(0, 1), (13, 1), (15, 1), (23, 1), (29, 1), (30, 1), (36, 2), (51, 1), (59, 1), (67, 1)] }, { coefficient := 1, powers := [(0, 1), (13, 1), (15, 1), (23, 1), (29, 1), (30, 1), (36, 1), (51, 1), (67, 1)] }, { coefficient := 1, powers := [(0, 1), (14, 1), (20, 1), (22, 1), (29, 1), (49, 1), (62, 1), (67, 1)] }, { coefficient := 1, powers := [(0, 1), (14, 1), (22, 1), (29, 1), (30, 1), (36, 1), (62, 1), (67, 1)] }, { coefficient := -1, powers := [(1, 1), (13, 1), (29, 1), (30, 1), (36, 1), (51, 1), (67, 1)] }, { coefficient := 1, powers := [(1, 1), (13, 1), (30, 1), (36, 1), (56, 1)] }, { coefficient := -1, powers := [(6, 1), (13, 1), (20, 1), (29, 1), (30, 1), (36, 1), (59, 1), (67, 1)] }, { coefficient := 1, powers := [(6, 1), (13, 1), (20, 1), (29, 1), (30, 1), (67, 1)] }, { coefficient := -1, powers := [(6, 1), (20, 3), (29, 1), (44, 1), (49, 1), (59, 1), (67, 1)] }, { coefficient := -1, powers := [(6, 1), (20, 2), (29, 1), (30, 1), (36, 1), (44, 1), (59, 1), (67, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1), (25, 1), (29, 1), (30, 1), (44, 1), (67, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1), (25, 1), (29, 1), (58, 1), (67, 1)] }, { coefficient := -1, powers := [(6, 1), (20, 1), (25, 1), (30, 1), (44, 1)] }, { coefficient := -1, powers := [(6, 1), (20, 1), (25, 1), (58, 1)] }, { coefficient := -1, powers := [(7, 1), (13, 1), (29, 1), (30, 1), (31, 1), (36, 1), (67, 1)] }, { coefficient := 1, powers := [(7, 1), (13, 1), (30, 1), (34, 1), (36, 1)] }, { coefficient := -1, powers := [(13, 1), (15, 1), (20, 2), (23, 1), (29, 1), (36, 1), (49, 1), (51, 1), (59, 1), (67, 1)] }, { coefficient := -1, powers := [(13, 1), (15, 1), (20, 1), (23, 1), (29, 1), (30, 1), (36, 2), (51, 1), (59, 1), (67, 1)] }, { coefficient := 1, powers := [(13, 1), (15, 1), (23, 1), (25, 1), (29, 1), (30, 1), (36, 1), (51, 1), (67, 1)] }, { coefficient := -1, powers := [(13, 1), (15, 1), (23, 1), (25, 1), (30, 1), (36, 1), (51, 1)] }, { coefficient := 1, powers := [(20, 2), (29, 1), (49, 1), (55, 1), (67, 1)] }, { coefficient := 1, powers := [(20, 1), (29, 1), (30, 1), (36, 1), (55, 1), (67, 1)] }, { coefficient := 1, powers := [(20, 1), (29, 1), (33, 1), (36, 1), (49, 1), (67, 1)] }, { coefficient := 1, powers := [(29, 1), (30, 1), (33, 1), (36, 2), (67, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (30, 1), (55, 1)] }, { coefficient := -1, powers := [(4, 1), (13, 1), (30, 1), (34, 1), (36, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (13, 1), (30, 1), (36, 1), (59, 1)] }, { coefficient := -1, powers := [(10, 1), (13, 1), (30, 1), (36, 1), (40, 1)] }, { coefficient := 1, powers := [(13, 1), (15, 1), (30, 1), (36, 1), (40, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (6, 1), (20, 2), (44, 1), (45, 1), (49, 1), (59, 1)] }, { coefficient := -1, powers := [(0, 1), (6, 1), (20, 1), (30, 1), (36, 1), (44, 1), (45, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (6, 1), (20, 1), (30, 1), (44, 1), (45, 1)] }, { coefficient := 1, powers := [(0, 1), (6, 1), (20, 1), (45, 1), (58, 1)] }, { coefficient := -1, powers := [(0, 1), (13, 1), (15, 1), (20, 1), (23, 1), (36, 1), (45, 1), (49, 1), (51, 1), (59, 1)] }, { coefficient := -1, powers := [(0, 1), (13, 1), (15, 1), (23, 1), (30, 1), (36, 2), (45, 1), (51, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (13, 1), (15, 1), (23, 1), (30, 1), (36, 1), (45, 1), (51, 1)] }, { coefficient := 1, powers := [(0, 1), (14, 1), (20, 1), (22, 1), (45, 1), (49, 1), (62, 1)] }, { coefficient := 1, powers := [(0, 1), (14, 1), (22, 1), (30, 1), (36, 1), (45, 1), (62, 1)] }, { coefficient := 1, powers := [(0, 1), (42, 1), (49, 1)] }, { coefficient := 1, powers := [(1, 1), (9, 1), (13, 1), (36, 1), (45, 1), (59, 1)] }, { coefficient := 1, powers := [(1, 1), (9, 1), (13, 1), (36, 1), (56, 1), (59, 1)] }, { coefficient := -1, powers := [(1, 1), (13, 1), (30, 1), (36, 1), (45, 1), (51, 1)] }, { coefficient := -1, powers := [(6, 1), (9, 1), (20, 1), (25, 1), (44, 1), (59, 1)] }, { coefficient := -1, powers := [(6, 1), (9, 1), (20, 1), (55, 1), (59, 1)] }, { coefficient := -1, powers := [(6, 1), (13, 1), (20, 2), (45, 1), (49, 1), (59, 1)] }, { coefficient := -1, powers := [(6, 1), (13, 1), (20, 1), (30, 1), (36, 1), (45, 1), (59, 1)] }, { coefficient := -1, powers := [(6, 1), (20, 3), (44, 1), (45, 1), (49, 1), (59, 1)] }, { coefficient := -1, powers := [(6, 1), (20, 2), (30, 1), (36, 1), (44, 1), (45, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 2), (44, 1), (49, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1), (25, 1), (30, 1), (44, 1), (45, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1), (25, 1), (45, 1), (58, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1), (30, 1), (44, 1)] }, { coefficient := -1, powers := [(7, 1), (13, 1), (30, 1), (31, 1), (36, 1), (45, 1)] }, { coefficient := -1, powers := [(9, 1), (13, 1), (15, 1), (23, 1), (25, 1), (36, 1), (51, 1), (59, 1)] }, { coefficient := -1, powers := [(9, 1), (13, 1), (15, 1), (34, 1), (36, 1), (45, 1), (51, 1), (65, 1)] }, { coefficient := -1, powers := [(9, 1), (13, 1), (15, 1), (34, 1), (36, 1), (51, 1), (56, 1), (65, 1)] }, { coefficient := 1, powers := [(9, 1), (20, 1), (55, 1), (56, 1), (65, 1)] }, { coefficient := -1, powers := [(9, 1), (20, 1), (55, 1)] }, { coefficient := 1, powers := [(9, 1), (25, 1), (42, 1)] }, { coefficient := -1, powers := [(9, 1), (33, 1), (36, 1)] }, { coefficient := 1, powers := [(9, 1), (55, 1), (65, 1)] }, { coefficient := 1, powers := [(10, 1), (13, 1), (23, 1), (30, 1), (36, 1), (51, 1)] }, { coefficient := 1, powers := [(10, 1), (13, 1), (30, 1), (31, 1), (36, 1), (37, 1)] }, { coefficient := -1, powers := [(13, 1), (15, 1), (20, 2), (23, 1), (36, 1), (45, 1), (49, 1), (51, 1), (59, 1)] }, { coefficient := -1, powers := [(13, 1), (15, 1), (20, 1), (23, 1), (30, 1), (36, 2), (45, 1), (51, 1), (59, 1)] }, { coefficient := 1, powers := [(13, 1), (15, 1), (23, 1), (25, 1), (30, 1), (36, 1), (45, 1), (51, 1)] }, { coefficient := 1, powers := [(20, 2), (45, 1), (49, 1), (55, 1)] }, { coefficient := 1, powers := [(20, 1), (30, 1), (36, 1), (45, 1), (55, 1)] }, { coefficient := 1, powers := [(20, 1), (33, 1), (36, 1), (45, 1), (49, 1)] }, { coefficient := 1, powers := [(20, 1), (42, 1), (49, 1)] }, { coefficient := 1, powers := [(25, 1), (42, 1), (49, 1)] }, { coefficient := 1, powers := [(30, 1), (33, 1), (36, 2), (45, 1)] }, { coefficient := 1, powers := [(30, 1), (36, 1), (42, 1)] }]
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

#print axioms Krenn.Component60.SelectedLeafB6_1_6_5.selectedHasNoCommonZero

end Krenn.Component60.SelectedLeafB6_1_6_5
