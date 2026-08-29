import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component19.SelectedLeafB4_7

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "7488a35a7c78b0c76027b0c16281efc6e2f7b87e6f24b3ff994ce24173a4d421"
def certificateSHA256 : String := "e60fa553184ba23068f942ed6ef947b042869c0c8515a07fa7dad0c957a5f154"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 40 → Fin 669 := ![
  2,
  10,
  12,
  13,
  17,
  18,
  20,
  22,
  23,
  25,
  28,
  170,
  191,
  196,
  198,
  203,
  220,
  304,
  318,
  329,
  359,
  403,
  420,
  424,
  429,
  517,
  565,
  583,
  604,
  605,
  606,
  607,
  608,
  655,
  661,
  662,
  664,
  665,
  667,
  668
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 40 → SparsePoly (Fin 66) := ![
  [{ coefficient := 1, powers := [(5, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(26, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(31, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (50, 1)] }, { coefficient := 1, powers := [(26, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (21, 1)] }, { coefficient := 1, powers := [(19, 1), (26, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (53, 1)] }, { coefficient := 1, powers := [(25, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1), (57, 1)] }, { coefficient := 1, powers := [(44, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (50, 1), (53, 1)] }, { coefficient := 1, powers := [(50, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (25, 1), (60, 1)] }, { coefficient := 1, powers := [(25, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (61, 1)] }, { coefficient := 1, powers := [(13, 1), (50, 1)] }, { coefficient := 1, powers := [(20, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (55, 1)] }, { coefficient := 1, powers := [(32, 1), (44, 1)] }, { coefficient := 1, powers := [(35, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (44, 1), (57, 1)] }, { coefficient := 1, powers := [(7, 1), (37, 1), (44, 1)] }, { coefficient := 1, powers := [(16, 1), (29, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (25, 1), (60, 1)] }, { coefficient := 1, powers := [(11, 1), (25, 1), (57, 1)] }, { coefficient := 1, powers := [(16, 1), (25, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (26, 1), (49, 1)] }, { coefficient := 1, powers := [(20, 1), (26, 1), (43, 1)] }, { coefficient := 1, powers := [(20, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (50, 1)] }, { coefficient := 1, powers := [(5, 1), (38, 1)] }, { coefficient := 1, powers := [(19, 1), (30, 1), (50, 1)] }, { coefficient := 1, powers := [(20, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1)] }, { coefficient := 1, powers := [(13, 1), (32, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (61, 1)] }, { coefficient := 1, powers := [(13, 1), (27, 1), (49, 1)] }, { coefficient := 1, powers := [(13, 1), (58, 1)] }, { coefficient := 1, powers := [(20, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (21, 1), (60, 1)] }, { coefficient := 1, powers := [(11, 1), (21, 1), (57, 1)] }, { coefficient := 1, powers := [(11, 1)] }, { coefficient := 1, powers := [(16, 1), (21, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (46, 1), (54, 1)] }, { coefficient := 1, powers := [(25, 1), (58, 1)] }, { coefficient := 1, powers := [(32, 1), (50, 1)] }, { coefficient := 1, powers := [(38, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (53, 1)] }, { coefficient := 1, powers := [(3, 1), (60, 1)] }, { coefficient := 1, powers := [(21, 1), (53, 1)] }, { coefficient := 1, powers := [(21, 1), (57, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1), (48, 1)] }, { coefficient := 1, powers := [(4, 1), (28, 1), (60, 1)] }, { coefficient := 1, powers := [(4, 1), (37, 1)] }, { coefficient := 1, powers := [(11, 1), (28, 1), (48, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1)] }, { coefficient := 1, powers := [(16, 1), (28, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (53, 1)] }, { coefficient := 1, powers := [(7, 1), (22, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (34, 1)] }, { coefficient := 1, powers := [(11, 1), (22, 1), (57, 1)] }, { coefficient := 1, powers := [(11, 1), (29, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (60, 1)] }, { coefficient := 1, powers := [(11, 1), (48, 1)] }, { coefficient := 1, powers := [(11, 1), (57, 1)] }, { coefficient := 1, powers := [(16, 1), (43, 1)] }, { coefficient := 1, powers := [(16, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (53, 1)] }, { coefficient := 1, powers := [(23, 1), (57, 1)] }, { coefficient := 1, powers := [(29, 1), (43, 1)] }, { coefficient := 1, powers := [(29, 1), (48, 1)] }, { coefficient := 1, powers := [(34, 1), (40, 1)] }, { coefficient := 1, powers := [(37, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (39, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1)] }, { coefficient := 1, powers := [(3, 1), (26, 1), (60, 1)] }, { coefficient := 1, powers := [(6, 1), (21, 1), (60, 1)] }, { coefficient := 1, powers := [(21, 1)] }, { coefficient := 1, powers := [(26, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (43, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (49, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (38, 1), (43, 1)] }, { coefficient := 1, powers := [(19, 1), (31, 1), (58, 1)] }, { coefficient := 1, powers := [(19, 1), (32, 1), (49, 1)] }, { coefficient := 1, powers := [(20, 1), (31, 1), (54, 1)] }, { coefficient := 1, powers := [(20, 1), (32, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (40, 1), (60, 1)] }, { coefficient := 1, powers := [(1, 1), (43, 1), (57, 1)] }, { coefficient := 1, powers := [(1, 1), (48, 1), (53, 1)] }, { coefficient := 1, powers := [(4, 1), (29, 1), (60, 1)] }, { coefficient := 1, powers := [(4, 1), (34, 1), (57, 1)] }, { coefficient := 1, powers := [(4, 1), (37, 1), (53, 1)] }, { coefficient := 1, powers := [(7, 1), (23, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (34, 1), (48, 1)] }, { coefficient := 1, powers := [(7, 1), (37, 1), (43, 1)] }, { coefficient := 1, powers := [(11, 1), (23, 1), (57, 1)] }, { coefficient := 1, powers := [(11, 1), (29, 1), (48, 1)] }, { coefficient := 1, powers := [(11, 1), (37, 1), (40, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1), (53, 1)] }, { coefficient := 1, powers := [(16, 1), (29, 1), (43, 1)] }, { coefficient := 1, powers := [(16, 1), (34, 1), (40, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (41, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (44, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (50, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (38, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (25, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (50, 1)] }, { coefficient := 1, powers := [(8, 1), (38, 1), (44, 1)] }, { coefficient := 1, powers := [(13, 1), (25, 1), (58, 1)] }, { coefficient := 1, powers := [(13, 1), (32, 1), (50, 1)] }, { coefficient := 1, powers := [(13, 1), (38, 1), (41, 1)] }, { coefficient := 1, powers := [(20, 1), (25, 1), (55, 1)] }, { coefficient := 1, powers := [(20, 1), (32, 1), (44, 1)] }, { coefficient := 1, powers := [(20, 1), (35, 1), (41, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1)] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(43, 1), (64, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(44, 1), (65, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 40 → SparsePoly (Fin 66) := ![
  [{ coefficient := 1, powers := [(0, 1), (35, 1), (39, 1), (53, 1), (58, 1)] }, { coefficient := 1, powers := [(0, 1), (35, 1), (39, 1), (57, 1), (58, 1)] }, { coefficient := -1, powers := [(3, 1), (35, 1), (58, 1)] }, { coefficient := 1, powers := [(6, 1), (21, 1), (35, 1), (53, 1), (58, 1)] }, { coefficient := 1, powers := [(6, 1), (21, 1), (35, 1), (57, 1), (58, 1)] }],
  [{ coefficient := -2, powers := [(25, 1), (27, 1)] }],
  [{ coefficient := -2, powers := [(6, 1), (13, 1), (21, 1), (34, 1), (43, 1), (48, 1), (53, 1), (58, 1)] }, { coefficient := 2, powers := [(6, 1), (13, 1), (34, 1), (43, 1), (53, 1), (58, 1)] }, { coefficient := -2, powers := [(13, 1), (21, 1), (34, 1), (40, 1), (43, 1), (58, 1)] }, { coefficient := 2, powers := [(13, 1), (22, 1), (43, 1), (48, 1), (58, 1)] }, { coefficient := -2, powers := [(13, 1), (23, 1), (43, 1), (58, 1)] }, { coefficient := -2, powers := [(13, 1), (28, 1), (43, 1), (53, 1), (58, 1)] }],
  [{ coefficient := 2, powers := [(6, 1), (13, 1), (21, 1), (25, 1), (34, 1), (43, 1), (48, 1), (53, 1), (58, 1), (65, 1)] }, { coefficient := 2, powers := [(13, 1), (21, 1), (25, 1), (34, 1), (40, 1), (43, 1), (58, 1), (65, 1)] }, { coefficient := -2, powers := [(13, 1), (22, 1), (25, 1), (43, 1), (48, 1), (58, 1), (65, 1)] }, { coefficient := 2, powers := [(13, 1), (23, 1), (25, 1), (43, 1), (58, 1), (65, 1)] }, { coefficient := 2, powers := [(13, 1), (23, 1), (25, 1), (53, 1), (58, 1), (65, 1)] }, { coefficient := 2, powers := [(13, 1), (25, 1), (28, 1), (43, 1), (53, 1), (58, 1), (65, 1)] }, { coefficient := -2, powers := [(13, 1), (25, 1), (34, 1), (40, 1), (58, 1), (65, 1)] }],
  [{ coefficient := -4, powers := [(21, 1), (25, 1), (49, 1), (55, 1), (65, 1)] }, { coefficient := -2, powers := [(21, 1), (32, 1), (43, 1), (44, 1), (49, 1), (64, 1), (65, 1)] }, { coefficient := -2, powers := [(21, 1), (32, 1), (44, 1), (49, 1), (65, 1)] }, { coefficient := -2, powers := [(32, 1), (44, 1), (49, 1), (64, 1), (65, 1)] }],
  [{ coefficient := -2, powers := [(30, 1), (55, 1)] }],
  [{ coefficient := -2, powers := [(19, 1), (50, 1)] }],
  [{ coefficient := -2, powers := [(13, 1), (46, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (5, 1), (35, 1), (53, 2), (58, 1), (65, 1)] }, { coefficient := -1, powers := [(0, 1), (5, 1), (35, 1), (53, 1), (57, 1), (58, 1), (65, 1)] }, { coefficient := -1, powers := [(5, 1), (21, 1), (35, 1), (53, 2), (58, 1), (65, 1)] }, { coefficient := -2, powers := [(5, 1), (21, 1), (35, 1), (53, 1), (57, 1), (58, 1), (65, 1)] }, { coefficient := -1, powers := [(5, 1), (21, 1), (35, 1), (57, 2), (58, 1), (65, 1)] }, { coefficient := -4, powers := [(13, 1), (32, 1), (50, 1), (53, 1), (65, 1)] }, { coefficient := 4, powers := [(20, 1), (25, 1), (43, 1), (55, 1), (65, 1)] }, { coefficient := 2, powers := [(20, 1), (32, 1), (43, 2), (44, 1), (64, 1), (65, 1)] }, { coefficient := 2, powers := [(20, 1), (32, 1), (43, 1), (44, 1), (65, 1)] }],
  [{ coefficient := -2, powers := [(4, 1), (13, 1), (25, 1), (58, 1), (60, 1), (65, 1)] }, { coefficient := 2, powers := [(11, 1), (13, 1), (25, 1), (43, 1), (58, 1), (65, 1)] }, { coefficient := 2, powers := [(11, 1), (13, 1), (25, 1), (48, 1), (58, 1), (65, 1)] }],
  [{ coefficient := -2, powers := [(19, 1), (44, 1), (58, 1), (64, 1), (65, 1)] }, { coefficient := -2, powers := [(20, 1), (44, 1), (54, 1), (64, 1), (65, 1)] }],
  [{ coefficient := 4, powers := [(13, 1), (32, 1), (53, 1)] }],
  [{ coefficient := 4, powers := [(25, 1), (49, 1), (55, 1)] }, { coefficient := 2, powers := [(32, 1), (43, 1), (44, 1), (49, 1), (64, 1)] }, { coefficient := 2, powers := [(32, 1), (44, 1), (49, 1)] }],
  [{ coefficient := -2, powers := [(4, 1), (13, 1), (34, 1), (58, 1)] }, { coefficient := 2, powers := [(11, 1), (13, 1), (23, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (35, 1), (58, 1), (65, 1)] }],
  [{ coefficient := -4, powers := [(13, 1), (32, 1)] }],
  [{ coefficient := 2, powers := [(4, 1), (13, 1), (34, 1), (53, 1), (58, 1)] }],
  [{ coefficient := 2, powers := [(32, 1)] }],
  [{ coefficient := 2, powers := [(20, 1)] }],
  [{ coefficient := -2, powers := [(13, 1), (25, 1), (43, 1), (58, 1), (65, 1)] }],
  [{ coefficient := -2, powers := [(6, 1), (13, 1), (21, 1), (34, 1), (48, 1), (53, 1), (58, 1)] }, { coefficient := 2, powers := [(6, 1), (13, 1), (34, 1), (53, 1), (58, 1)] }, { coefficient := -2, powers := [(13, 1), (21, 1), (34, 1), (40, 1), (58, 1)] }, { coefficient := 2, powers := [(13, 1), (22, 1), (48, 1), (58, 1)] }, { coefficient := -2, powers := [(13, 1), (23, 1), (58, 1)] }, { coefficient := -2, powers := [(13, 1), (28, 1), (53, 1), (58, 1)] }],
  [{ coefficient := -4, powers := [(25, 1), (55, 1)] }, { coefficient := -2, powers := [(32, 1), (43, 1), (44, 1), (64, 1)] }, { coefficient := -2, powers := [(32, 1), (44, 1)] }],
  [{ coefficient := 2, powers := [(55, 1)] }],
  [{ coefficient := 2, powers := [(50, 1)] }],
  [{ coefficient := 2, powers := [(25, 1)] }],
  [{ coefficient := 2, powers := [(6, 1), (13, 1), (25, 1), (34, 1), (48, 1), (53, 1), (58, 1)] }, { coefficient := 2, powers := [(13, 1), (25, 1), (34, 1), (40, 1), (58, 1)] }],
  [{ coefficient := 2, powers := [(13, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (26, 1), (35, 1), (53, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (26, 1), (35, 1), (57, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (58, 1)] }],
  [{ coefficient := -2, powers := [(13, 1), (25, 1), (53, 1), (58, 1)] }],
  [{ coefficient := -2, powers := [(13, 1), (25, 1), (48, 1), (58, 1)] }],
  [{ coefficient := -2, powers := [(6, 1), (13, 1), (25, 1), (34, 1), (53, 1), (58, 1)] }, { coefficient := 2, powers := [(13, 1), (25, 1), (28, 1), (53, 1), (58, 1)] }],
  [{ coefficient := -2, powers := [(11, 1), (13, 1), (25, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (35, 1), (53, 1), (58, 1)] }, { coefficient := -1, powers := [(5, 1), (35, 1), (57, 1), (58, 1)] }],
  [{ coefficient := 2, powers := [(44, 1), (64, 1)] }],
  [{ coefficient := 2, powers := [(13, 1), (25, 1), (58, 1)] }],
  [{ coefficient := -2, powers := [] }],
  [{ coefficient := -2, powers := [(13, 1), (25, 1), (40, 1), (58, 1), (60, 1)] }, { coefficient := 2, powers := [(13, 1), (25, 1), (43, 1), (44, 1), (57, 1), (58, 1), (65, 1)] }, { coefficient := -2, powers := [(13, 1), (25, 1), (43, 1), (57, 1), (58, 1)] }, { coefficient := 2, powers := [(13, 1), (25, 1), (48, 1), (53, 1), (58, 1)] }],
  [{ coefficient := 2, powers := [(41, 1), (61, 1)] }, { coefficient := -2, powers := [(43, 1), (44, 1), (58, 1), (64, 1)] }, { coefficient := -2, powers := [(44, 1), (49, 1), (54, 1), (64, 1)] }, { coefficient := 2, powers := [(44, 1), (58, 1)] }, { coefficient := -2, powers := [(50, 1), (55, 1)] }],
  [{ coefficient := -2, powers := [(8, 1), (38, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (5, 1), (26, 1), (35, 1), (53, 2), (58, 1)] }, { coefficient := 1, powers := [(0, 1), (5, 1), (26, 1), (35, 1), (53, 1), (57, 1), (58, 1)] }, { coefficient := -1, powers := [(0, 1), (5, 1), (35, 1), (57, 1), (58, 1)] }, { coefficient := 2, powers := [(4, 1), (13, 1), (25, 1), (29, 1), (58, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (21, 1), (26, 1), (35, 1), (53, 2), (58, 1)] }, { coefficient := 2, powers := [(5, 1), (21, 1), (26, 1), (35, 1), (53, 1), (57, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (21, 1), (26, 1), (35, 1), (57, 2), (58, 1)] }, { coefficient := -1, powers := [(5, 1), (35, 1), (58, 1)] }, { coefficient := -2, powers := [(6, 1), (13, 1), (16, 1), (21, 1), (25, 1), (34, 1), (43, 1), (48, 1), (53, 1), (58, 1)] }, { coefficient := 2, powers := [(7, 1), (13, 1), (25, 1), (37, 1), (43, 1), (58, 1)] }, { coefficient := -2, powers := [(11, 1), (13, 1), (25, 1), (29, 1), (43, 1), (58, 1)] }, { coefficient := -2, powers := [(11, 1), (13, 1), (25, 1), (29, 1), (48, 1), (58, 1)] }, { coefficient := -2, powers := [(13, 1), (16, 1), (21, 1), (25, 1), (34, 1), (40, 1), (43, 1), (58, 1)] }, { coefficient := 2, powers := [(13, 1), (16, 1), (22, 1), (25, 1), (43, 1), (48, 1), (58, 1)] }, { coefficient := -2, powers := [(13, 1), (16, 1), (23, 1), (25, 1), (43, 1), (58, 1)] }, { coefficient := -2, powers := [(13, 1), (16, 1), (23, 1), (25, 1), (53, 1), (58, 1)] }, { coefficient := -2, powers := [(13, 1), (16, 1), (25, 1), (28, 1), (43, 1), (53, 1), (58, 1)] }, { coefficient := 2, powers := [(13, 1), (16, 1), (25, 1), (29, 1), (43, 1), (58, 1)] }, { coefficient := 2, powers := [(13, 1), (16, 1), (25, 1), (34, 1), (40, 1), (58, 1)] }, { coefficient := 4, powers := [(13, 1), (26, 1), (32, 1), (50, 1), (53, 1)] }, { coefficient := 4, powers := [(19, 1), (21, 1), (25, 1), (49, 1), (55, 1)] }, { coefficient := 2, powers := [(19, 1), (21, 1), (32, 1), (43, 1), (44, 1), (49, 1), (64, 1)] }, { coefficient := 2, powers := [(19, 1), (21, 1), (32, 1), (44, 1), (49, 1)] }, { coefficient := 2, powers := [(19, 1), (31, 1), (44, 1), (58, 1), (64, 1)] }, { coefficient := 2, powers := [(19, 1), (32, 1), (44, 1), (49, 1), (64, 1)] }, { coefficient := -4, powers := [(20, 1), (25, 1), (26, 1), (43, 1), (55, 1)] }, { coefficient := -2, powers := [(20, 1), (26, 1), (32, 1), (43, 2), (44, 1), (64, 1)] }, { coefficient := -2, powers := [(20, 1), (26, 1), (32, 1), (43, 1), (44, 1)] }, { coefficient := 2, powers := [(20, 1), (31, 1), (44, 1), (54, 1), (64, 1)] }]
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
    (values : Fin 66 → R) :
    ¬ ∀ index : Fin 40,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((2 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (2 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (2 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component19.SelectedLeafB4_7.selectedHasNoCommonZero

end Krenn.Component19.SelectedLeafB4_7
