import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component17.SelectedLeafB5_4_0

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "f46c36650d78120aea476fc7a9ec73b182d92293de4458c2cc6aea9fc533c6b7"
def certificateSHA256 : String := "6fc1cfea9f1904ab70ec0b63099490937d802da27fe132f2806138cde56e8ac6"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 31 → Fin 611 := ![
  5,
  7,
  18,
  32,
  183,
  202,
  206,
  207,
  281,
  285,
  311,
  323,
  325,
  410,
  415,
  427,
  432,
  434,
  441,
  445,
  484,
  486,
  506,
  549,
  550,
  601,
  604,
  606,
  607,
  609,
  610
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 31 → SparsePoly (Fin 62) := ![
  [{ coefficient := 1, powers := [(3, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (52, 1)] }, { coefficient := 1, powers := [(19, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (44, 1)] }, { coefficient := 1, powers := [(13, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (19, 1)] }, { coefficient := 1, powers := [(17, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (43, 1)] }, { coefficient := 1, powers := [(18, 1), (19, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (19, 1), (54, 1)] }, { coefficient := 1, powers := [(13, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (25, 1), (44, 1)] }, { coefficient := 1, powers := [(17, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (58, 1)] }, { coefficient := 1, powers := [(13, 1), (47, 1)] }, { coefficient := 1, powers := [(18, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (45, 1)] }, { coefficient := 1, powers := [(18, 1), (40, 1)] }, { coefficient := 1, powers := [(18, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (52, 1)] }, { coefficient := 1, powers := [(29, 1), (41, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (19, 1), (50, 1)] }, { coefficient := 1, powers := [(17, 1), (19, 1), (54, 1)] }, { coefficient := 1, powers := [(17, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (24, 1), (45, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (40, 1)] }, { coefficient := 1, powers := [(18, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (44, 1)] }, { coefficient := 1, powers := [(17, 1), (27, 1), (40, 1)] }, { coefficient := 1, powers := [(17, 1), (27, 1), (44, 1)] }, { coefficient := 1, powers := [(17, 1), (28, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (50, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (50, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (54, 1)] }, { coefficient := 1, powers := [(17, 1), (28, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (52, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1)] }, { coefficient := 1, powers := [(13, 1), (29, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (58, 1)] }, { coefficient := 1, powers := [(13, 1), (25, 1), (45, 1)] }, { coefficient := 1, powers := [(13, 1), (55, 1)] }, { coefficient := 1, powers := [(18, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (40, 1)] }, { coefficient := 1, powers := [(17, 1), (44, 1)] }, { coefficient := 1, powers := [(17, 1), (50, 1)] }, { coefficient := 1, powers := [(17, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (28, 1), (57, 1)] }, { coefficient := 1, powers := [(22, 1), (50, 1)] }, { coefficient := 1, powers := [(22, 1), (54, 1)] }, { coefficient := 1, powers := [(28, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (29, 1), (58, 1)] }, { coefficient := 1, powers := [(3, 1), (32, 1), (55, 1)] }, { coefficient := 1, powers := [(3, 1), (35, 1), (52, 1)] }, { coefficient := 1, powers := [(22, 1), (43, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (28, 1), (57, 1)] }, { coefficient := 1, powers := [(27, 1), (40, 1)] }, { coefficient := 1, powers := [(27, 1), (44, 1)] }, { coefficient := 1, powers := [(28, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1)] }, { coefficient := 1, powers := [(6, 1), (57, 1)] }, { coefficient := 1, powers := [(24, 1), (40, 1)] }, { coefficient := 1, powers := [(24, 1), (44, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (50, 1)] }, { coefficient := 1, powers := [(3, 1), (57, 1)] }, { coefficient := 1, powers := [(19, 1), (50, 1)] }, { coefficient := 1, powers := [(19, 1), (54, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (41, 1), (55, 1)] }, { coefficient := 1, powers := [(2, 1), (47, 1), (52, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (52, 1)] }, { coefficient := 1, powers := [(8, 1), (23, 1), (58, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (47, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(13, 1), (23, 1), (55, 1)] }, { coefficient := 1, powers := [(13, 1), (29, 1), (47, 1)] }, { coefficient := 1, powers := [(13, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (52, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (41, 1)] }, { coefficient := 1, powers := [(18, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (60, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(40, 1)] }],
  [{ coefficient := 1, powers := [(41, 1)] }],
  [{ coefficient := 1, powers := [(54, 1)] }],
  [{ coefficient := 1, powers := [(55, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 31 → SparsePoly (Fin 62) := ![
  [{ coefficient := -1, powers := [(2, 1), (38, 1), (57, 1)] }, { coefficient := -1, powers := [(3, 1), (5, 1), (29, 1), (57, 2)] }, { coefficient := -1, powers := [(5, 1), (6, 1), (29, 1), (57, 2)] }, { coefficient := -1, powers := [(5, 1), (19, 1), (29, 1), (50, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (24, 1), (29, 1), (50, 1), (57, 1)] }, { coefficient := -1, powers := [(17, 1), (19, 1), (28, 1), (38, 1), (57, 1)] }, { coefficient := 1, powers := [(17, 1), (24, 1), (28, 1), (38, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (38, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (23, 1), (25, 1), (57, 1)] }, { coefficient := 1, powers := [(6, 1), (23, 1), (25, 1), (57, 1)] }, { coefficient := 1, powers := [(19, 1), (23, 1), (25, 1), (50, 1)] }, { coefficient := -1, powers := [(23, 1), (24, 1), (25, 1), (50, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (5, 1), (43, 1), (57, 2)] }, { coefficient := 1, powers := [(3, 1), (17, 1), (47, 1), (57, 1)] }, { coefficient := -1, powers := [(5, 1), (6, 1), (43, 1), (57, 2)] }, { coefficient := -1, powers := [(5, 1), (19, 1), (43, 1), (50, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (24, 1), (43, 1), (50, 1), (57, 1)] }, { coefficient := 1, powers := [(6, 1), (17, 1), (47, 1), (57, 1)] }, { coefficient := 1, powers := [(17, 1), (19, 1), (47, 1), (50, 1)] }, { coefficient := -1, powers := [(17, 1), (24, 1), (47, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (5, 1), (35, 1), (50, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (6, 1), (35, 1), (50, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (19, 1), (35, 1), (50, 2)] }, { coefficient := -1, powers := [(5, 1), (24, 1), (35, 1), (50, 2)] }],
  [{ coefficient := -1, powers := [(3, 1), (23, 1), (25, 1), (43, 1), (57, 1)] }, { coefficient := -1, powers := [(6, 1), (23, 1), (25, 1), (43, 1), (57, 1)] }, { coefficient := -1, powers := [(19, 1), (23, 1), (25, 1), (43, 1), (50, 1)] }, { coefficient := 1, powers := [(23, 1), (24, 1), (25, 1), (43, 1), (50, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (28, 1), (50, 1), (60, 1)] }, { coefficient := -1, powers := [(3, 1), (23, 1), (45, 1), (52, 1), (57, 1)] }, { coefficient := -1, powers := [(6, 1), (23, 1), (45, 1), (52, 1), (57, 1)] }, { coefficient := -1, powers := [(19, 1), (23, 1), (45, 1), (50, 1), (52, 1)] }, { coefficient := 1, powers := [(23, 1), (24, 1), (45, 1), (50, 1), (52, 1)] }, { coefficient := -1, powers := [(24, 1), (28, 1), (50, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (23, 1), (52, 1), (57, 1)] }, { coefficient := -1, powers := [(6, 1), (23, 1), (52, 1), (57, 1)] }, { coefficient := -1, powers := [(19, 1), (23, 1), (50, 1), (52, 1)] }, { coefficient := 1, powers := [(23, 1), (24, 1), (50, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (29, 1), (47, 1), (57, 1)] }, { coefficient := -1, powers := [(3, 1), (35, 1), (38, 1), (57, 1)] }, { coefficient := 1, powers := [(6, 1), (29, 1), (47, 1), (57, 1)] }, { coefficient := -1, powers := [(6, 1), (35, 1), (38, 1), (57, 1)] }, { coefficient := 1, powers := [(19, 1), (29, 1), (47, 1), (50, 1)] }, { coefficient := -1, powers := [(19, 1), (35, 1), (38, 1), (50, 1)] }, { coefficient := -1, powers := [(24, 1), (29, 1), (47, 1), (50, 1)] }, { coefficient := 1, powers := [(24, 1), (35, 1), (38, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (23, 1), (43, 1), (57, 1)] }, { coefficient := 1, powers := [(6, 1), (23, 1), (43, 1), (57, 1)] }, { coefficient := 1, powers := [(19, 1), (23, 1), (43, 1), (50, 1)] }, { coefficient := -1, powers := [(23, 1), (24, 1), (43, 1), (50, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (29, 1), (57, 1)] }, { coefficient := -1, powers := [(6, 1), (29, 1), (57, 1)] }, { coefficient := -1, powers := [(19, 1), (29, 1), (50, 1)] }, { coefficient := 1, powers := [(24, 1), (29, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (19, 1), (23, 1), (52, 1), (57, 1)] }, { coefficient := 1, powers := [(6, 1), (19, 1), (23, 1), (52, 1), (57, 1)] }, { coefficient := 1, powers := [(19, 2), (23, 1), (50, 1), (52, 1)] }, { coefficient := -1, powers := [(19, 1), (23, 1), (24, 1), (50, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (18, 1), (57, 1)] }, { coefficient := -1, powers := [(6, 1), (18, 1), (57, 1)] }, { coefficient := -1, powers := [(18, 1), (19, 1), (50, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (50, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (28, 1), (60, 1)] }, { coefficient := 2, powers := [(24, 1), (28, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (23, 1), (52, 1), (57, 1)] }, { coefficient := 1, powers := [(6, 1), (23, 1), (52, 1), (57, 1)] }, { coefficient := 1, powers := [(19, 1), (23, 1), (50, 1), (52, 1)] }, { coefficient := -1, powers := [(23, 1), (24, 1), (50, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (60, 1)] }, { coefficient := -1, powers := [(24, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (60, 1)] }, { coefficient := -1, powers := [(19, 1), (38, 1), (58, 1)] }, { coefficient := 1, powers := [(24, 1), (38, 1), (58, 1)] }, { coefficient := -1, powers := [(24, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (47, 1), (57, 1)] }, { coefficient := -1, powers := [(6, 1), (47, 1), (57, 1)] }, { coefficient := -1, powers := [(19, 1), (47, 1), (50, 1)] }, { coefficient := 1, powers := [(24, 1), (47, 1), (50, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (23, 1), (57, 1)] }, { coefficient := -1, powers := [(6, 1), (23, 1), (57, 1)] }, { coefficient := -1, powers := [(19, 1), (23, 1), (50, 1)] }, { coefficient := 1, powers := [(23, 1), (24, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(0, 2), (28, 1), (60, 1)] }, { coefficient := 2, powers := [(0, 1), (24, 1), (28, 1), (60, 1)] }, { coefficient := 1, powers := [(24, 2), (28, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (17, 1), (60, 1)] }, { coefficient := 1, powers := [(17, 1), (19, 1), (38, 1), (58, 1)] }, { coefficient := -1, powers := [(17, 1), (24, 1), (38, 1), (58, 1)] }, { coefficient := 1, powers := [(17, 1), (24, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (5, 1), (57, 2)] }, { coefficient := 1, powers := [(5, 1), (6, 1), (57, 2)] }, { coefficient := 1, powers := [(5, 1), (19, 1), (50, 1), (57, 1)] }, { coefficient := -1, powers := [(5, 1), (24, 1), (50, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (17, 1), (60, 1)] }, { coefficient := 1, powers := [(17, 1), (24, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (17, 1), (28, 1), (60, 1)] }, { coefficient := -1, powers := [(17, 1), (24, 1), (28, 1), (60, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := -1, powers := [(0, 1), (17, 1), (28, 1), (60, 1)] }, { coefficient := -1, powers := [(3, 1), (5, 1), (35, 1), (52, 1), (57, 1)] }, { coefficient := -1, powers := [(5, 1), (6, 1), (35, 1), (52, 1), (57, 1)] }, { coefficient := -1, powers := [(5, 1), (19, 1), (35, 1), (50, 1), (52, 1)] }, { coefficient := 1, powers := [(5, 1), (24, 1), (35, 1), (50, 1), (52, 1)] }, { coefficient := -1, powers := [(17, 1), (24, 1), (28, 1), (60, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(3, 1), (57, 1)] }, { coefficient := 1, powers := [(6, 1), (57, 1)] }, { coefficient := 1, powers := [(19, 1), (50, 1)] }, { coefficient := -1, powers := [(24, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1)] }, { coefficient := 1, powers := [(0, 1), (50, 1)] }, { coefficient := 1, powers := [(24, 1), (44, 1)] }, { coefficient := 1, powers := [(24, 1), (50, 1)] }],
  [{ coefficient := -1, powers := [(0, 2), (17, 1), (28, 1), (60, 1)] }, { coefficient := -1, powers := [(0, 1), (17, 1), (24, 1), (28, 1), (60, 1)] }, { coefficient := -1, powers := [(3, 1), (18, 1), (19, 1), (23, 1), (52, 1), (57, 1)] }, { coefficient := -1, powers := [(3, 1), (18, 1), (23, 1), (24, 1), (52, 1), (57, 1)] }, { coefficient := -1, powers := [(6, 1), (18, 1), (19, 1), (23, 1), (52, 1), (57, 1)] }, { coefficient := -1, powers := [(6, 1), (18, 1), (23, 1), (24, 1), (52, 1), (57, 1)] }, { coefficient := -1, powers := [(18, 1), (19, 2), (23, 1), (50, 1), (52, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (24, 2), (50, 1), (52, 1)] }, { coefficient := -1, powers := [(24, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (8, 1), (35, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (18, 1), (29, 1), (57, 1)] }, { coefficient := -1, powers := [(6, 1), (8, 1), (35, 1), (57, 1)] }, { coefficient := 1, powers := [(6, 1), (18, 1), (29, 1), (57, 1)] }, { coefficient := -1, powers := [(8, 1), (19, 1), (35, 1), (50, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (35, 1), (50, 1)] }, { coefficient := 1, powers := [(18, 1), (19, 1), (29, 1), (50, 1)] }, { coefficient := -1, powers := [(18, 1), (24, 1), (29, 1), (50, 1)] }],
  [{ coefficient := -1, powers := [(0, 2), (17, 1), (28, 1), (60, 1)] }, { coefficient := -1, powers := [(0, 1), (17, 1), (19, 1), (28, 1), (60, 1)] }, { coefficient := -2, powers := [(0, 1), (17, 1), (24, 1), (28, 1), (60, 1)] }, { coefficient := 1, powers := [(3, 1), (5, 1), (19, 1), (35, 1), (52, 1), (57, 1)] }, { coefficient := -1, powers := [(3, 1), (13, 1), (19, 1), (29, 1), (47, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (13, 1), (19, 1), (35, 1), (38, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (13, 1), (23, 1), (25, 1), (43, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (6, 1), (19, 1), (35, 1), (52, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (19, 2), (35, 1), (50, 1), (52, 1)] }, { coefficient := -1, powers := [(5, 1), (19, 1), (24, 1), (35, 1), (50, 1), (52, 1)] }, { coefficient := -1, powers := [(6, 1), (13, 1), (19, 1), (29, 1), (47, 1), (57, 1)] }, { coefficient := 1, powers := [(6, 1), (13, 1), (19, 1), (35, 1), (38, 1), (57, 1)] }, { coefficient := 1, powers := [(6, 1), (13, 1), (23, 1), (25, 1), (43, 1), (57, 1)] }, { coefficient := -1, powers := [(13, 1), (19, 2), (29, 1), (47, 1), (50, 1)] }, { coefficient := 1, powers := [(13, 1), (19, 2), (35, 1), (38, 1), (50, 1)] }, { coefficient := 1, powers := [(13, 1), (19, 1), (23, 1), (25, 1), (43, 1), (50, 1)] }, { coefficient := 1, powers := [(13, 1), (19, 1), (24, 1), (29, 1), (47, 1), (50, 1)] }, { coefficient := -1, powers := [(13, 1), (19, 1), (24, 1), (35, 1), (38, 1), (50, 1)] }, { coefficient := -1, powers := [(13, 1), (23, 1), (24, 1), (25, 1), (43, 1), (50, 1)] }, { coefficient := -1, powers := [(17, 1), (19, 1), (24, 1), (28, 1), (60, 1)] }, { coefficient := -1, powers := [(17, 1), (24, 2), (28, 1), (60, 1)] }, { coefficient := -1, powers := [(19, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (3, 1), (41, 1), (57, 1)] }, { coefficient := -1, powers := [(2, 1), (6, 1), (41, 1), (57, 1)] }, { coefficient := -1, powers := [(2, 1), (19, 1), (41, 1), (50, 1)] }, { coefficient := 1, powers := [(2, 1), (24, 1), (41, 1), (50, 1)] }, { coefficient := -1, powers := [(3, 2), (5, 1), (32, 1), (57, 2)] }, { coefficient := -1, powers := [(3, 1), (5, 1), (6, 1), (32, 1), (57, 2)] }, { coefficient := -1, powers := [(3, 1), (5, 1), (19, 1), (32, 1), (50, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (5, 1), (24, 1), (32, 1), (50, 1), (57, 1)] }, { coefficient := -1, powers := [(3, 1), (5, 1), (32, 1), (57, 1)] }, { coefficient := -1, powers := [(5, 1), (6, 1), (32, 1), (57, 1)] }, { coefficient := -1, powers := [(5, 1), (19, 1), (32, 1), (50, 1)] }, { coefficient := 1, powers := [(5, 1), (24, 1), (32, 1), (50, 1)] }]
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
    (values : Fin 62 → R) :
    ¬ ∀ index : Fin 31,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((2 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (2 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (2 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component17.SelectedLeafB5_4_0.selectedHasNoCommonZero

end Krenn.Component17.SelectedLeafB5_4_0
