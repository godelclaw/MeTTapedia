import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component39.SelectedLeafB4_6_2_3

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "7f1f17955269a7f9ca0fd3da6446c6f18dba0d0289a74136090653e5c98811a5"
def certificateSHA256 : String := "5896fef87b5997f1246c4f6529c2f8ff8e6196488e361ad2fcb9ef7966d23ff9"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 25 → Fin 673 := ![
  28,
  68,
  173,
  304,
  305,
  306,
  307,
  318,
  476,
  511,
  515,
  516,
  537,
  600,
  602,
  603,
  658,
  659,
  662,
  664,
  667,
  668,
  670,
  671,
  672
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 25 → SparsePoly (Fin 67) := ![
  [{ coefficient := 1, powers := [(25, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (28, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (23, 1)] }, { coefficient := 1, powers := [(14, 1), (18, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (44, 1)] }, { coefficient := 1, powers := [(4, 1), (33, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (51, 1)] }, { coefficient := 1, powers := [(7, 1), (30, 1)] }, { coefficient := 1, powers := [(10, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (32, 1)] }, { coefficient := 1, powers := [(10, 1), (23, 1), (43, 1)] }, { coefficient := 1, powers := [(10, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (29, 1)] }, { coefficient := 1, powers := [(14, 1), (18, 1), (50, 1)] }, { coefficient := 1, powers := [(14, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (53, 1)] }, { coefficient := 1, powers := [(28, 1), (39, 1)] }, { coefficient := 1, powers := [(28, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (38, 1), (56, 1)] }, { coefficient := 1, powers := [(1, 1), (50, 1)] }, { coefficient := 1, powers := [(7, 1), (33, 1), (38, 1)] }, { coefficient := 1, powers := [(14, 1), (25, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (23, 1), (59, 1)] }, { coefficient := 1, powers := [(10, 1), (23, 1), (44, 1)] }, { coefficient := 1, powers := [(14, 1), (23, 1), (39, 1)] }, { coefficient := 1, powers := [(14, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (28, 1), (59, 1)] }, { coefficient := 1, powers := [(10, 1), (28, 1), (44, 1)] }, { coefficient := 1, powers := [(14, 1), (27, 1), (53, 1)] }, { coefficient := 1, powers := [(14, 1), (28, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (29, 1), (56, 1)] }, { coefficient := 1, powers := [(7, 1), (29, 1), (44, 1)] }, { coefficient := 1, powers := [(14, 1), (29, 1), (36, 1)] }, { coefficient := 1, powers := [(14, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (18, 1), (59, 1)] }, { coefficient := 1, powers := [(10, 1), (18, 1), (56, 1)] }, { coefficient := 1, powers := [(10, 1)] }, { coefficient := 1, powers := [(14, 1), (18, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (41, 1)] }, { coefficient := 1, powers := [(3, 1), (32, 1)] }, { coefficient := 1, powers := [(13, 1), (18, 1)] }, { coefficient := 1, powers := [(18, 1), (55, 1)] }, { coefficient := 1, powers := [(23, 1), (41, 1)] }, { coefficient := 1, powers := [(32, 1), (35, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (59, 1)] }, { coefficient := 1, powers := [(10, 1), (44, 1)] }, { coefficient := 1, powers := [(10, 1), (56, 1)] }, { coefficient := 1, powers := [(14, 1), (39, 1)] }, { coefficient := 1, powers := [(14, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (51, 1)] }, { coefficient := 1, powers := [(20, 1), (56, 1)] }, { coefficient := 1, powers := [(25, 1), (39, 1)] }, { coefficient := 1, powers := [(25, 1), (44, 1)] }, { coefficient := 1, powers := [(30, 1), (36, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (35, 1), (58, 1)] }, { coefficient := 1, powers := [(0, 1), (38, 1), (55, 1)] }, { coefficient := 1, powers := [(0, 1), (41, 1), (48, 1)] }, { coefficient := 1, powers := [(3, 1), (23, 1), (58, 1)] }, { coefficient := 1, powers := [(3, 1), (29, 1), (55, 1)] }, { coefficient := 1, powers := [(3, 1), (32, 1), (48, 1)] }, { coefficient := 1, powers := [(6, 1), (18, 1), (58, 1)] }, { coefficient := 1, powers := [(6, 1), (29, 1), (41, 1)] }, { coefficient := 1, powers := [(6, 1), (32, 1), (38, 1)] }, { coefficient := 1, powers := [(9, 1), (18, 1), (55, 1)] }, { coefficient := 1, powers := [(9, 1), (23, 1), (41, 1)] }, { coefficient := 1, powers := [(9, 1), (32, 1), (35, 1)] }, { coefficient := 1, powers := [(13, 1), (18, 1), (48, 1)] }, { coefficient := 1, powers := [(13, 1), (23, 1), (38, 1)] }, { coefficient := 1, powers := [(13, 1), (29, 1), (35, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1), (36, 1), (59, 1)] }, { coefficient := 1, powers := [(1, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(1, 1), (44, 1), (51, 1)] }, { coefficient := 1, powers := [(4, 1), (25, 1), (59, 1)] }, { coefficient := 1, powers := [(4, 1), (30, 1), (56, 1)] }, { coefficient := 1, powers := [(4, 1), (33, 1), (51, 1)] }, { coefficient := 1, powers := [(7, 1), (20, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (30, 1), (44, 1)] }, { coefficient := 1, powers := [(7, 1), (33, 1), (39, 1)] }, { coefficient := 1, powers := [(10, 1), (20, 1), (56, 1)] }, { coefficient := 1, powers := [(10, 1), (25, 1), (44, 1)] }, { coefficient := 1, powers := [(10, 1), (33, 1), (36, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1), (51, 1)] }, { coefficient := 1, powers := [(14, 1), (25, 1), (39, 1)] }, { coefficient := 1, powers := [(14, 1), (30, 1), (36, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1)] }],
  [{ coefficient := 1, powers := [(38, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(55, 1)] }],
  [{ coefficient := 1, powers := [(56, 1), (64, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(23, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (65, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(28, 1), (66, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 25 → SparsePoly (Fin 67) := ![
  [{ coefficient := 1, powers := [(4, 1), (6, 1), (29, 1), (30, 1), (56, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (30, 1), (35, 1), (56, 1), (66, 1)] }, { coefficient := 1, powers := [(6, 1), (18, 1), (30, 1), (56, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (30, 1), (35, 1), (44, 1), (50, 1), (56, 1), (64, 1)] }, { coefficient := 1, powers := [(25, 1), (44, 1), (51, 1), (56, 1), (64, 1)] }, { coefficient := -1, powers := [(33, 1), (36, 1), (51, 1), (56, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(51, 1), (56, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(44, 1), (56, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (30, 1), (38, 1), (56, 1)] }, { coefficient := 1, powers := [(9, 1), (30, 1), (35, 1), (56, 1)] }, { coefficient := -1, powers := [(30, 1), (35, 1), (48, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [(13, 1), (30, 1), (35, 1), (44, 1), (56, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (18, 1), (25, 1), (44, 1), (56, 1), (64, 1), (66, 1)] }, { coefficient := -1, powers := [(14, 1), (18, 1), (33, 1), (36, 1), (56, 1), (64, 1), (66, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1), (56, 1), (64, 1), (66, 1)] }, { coefficient := -1, powers := [(14, 1), (25, 1), (56, 1), (64, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(39, 1), (56, 1), (62, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(13, 1), (29, 1), (30, 1), (35, 1), (36, 1), (56, 1), (64, 1)] }, { coefficient := 1, powers := [(13, 1), (30, 1), (35, 1), (38, 1), (44, 1), (56, 1), (64, 1)] }, { coefficient := -1, powers := [(13, 1), (30, 1), (35, 1), (50, 1), (56, 1), (64, 1)] }, { coefficient := -1, powers := [(18, 1), (25, 1), (39, 1), (44, 1), (56, 1), (64, 1)] }, { coefficient := -1, powers := [(18, 1), (25, 1), (44, 2), (56, 1), (64, 1)] }, { coefficient := -1, powers := [(18, 1), (25, 1), (44, 1), (51, 1), (56, 1), (64, 1)] }, { coefficient := 1, powers := [(18, 1), (33, 1), (36, 1), (39, 1), (56, 1), (64, 1)] }, { coefficient := 1, powers := [(18, 1), (33, 1), (36, 1), (44, 1), (56, 1), (64, 1)] }, { coefficient := 1, powers := [(18, 1), (33, 1), (36, 1), (51, 1), (56, 1), (64, 1)] }, { coefficient := -1, powers := [(20, 1), (39, 1), (56, 1), (64, 1)] }, { coefficient := -1, powers := [(20, 1), (44, 1), (56, 1), (64, 1)] }, { coefficient := -2, powers := [(20, 1), (51, 1), (56, 1), (64, 1)] }, { coefficient := -1, powers := [(20, 1), (56, 2), (64, 1)] }, { coefficient := -1, powers := [(25, 1), (38, 1), (39, 1), (56, 1), (62, 1), (64, 1)] }, { coefficient := -1, powers := [(33, 1), (36, 1), (56, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(18, 1), (25, 1), (44, 1), (56, 1), (64, 1), (66, 1)] }, { coefficient := 1, powers := [(18, 1), (33, 1), (36, 1), (56, 1), (64, 1), (66, 1)] }, { coefficient := -1, powers := [(20, 1), (56, 1), (64, 1), (66, 1)] }, { coefficient := 1, powers := [(25, 1), (56, 1), (64, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (30, 1), (35, 1), (56, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(25, 1), (44, 1), (56, 1), (64, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1), (56, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (30, 1), (48, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (25, 1), (28, 1), (44, 1), (56, 1), (64, 1), (66, 1)] }, { coefficient := -1, powers := [(18, 1), (28, 1), (33, 1), (36, 1), (56, 1), (64, 1), (66, 1)] }, { coefficient := 1, powers := [(20, 1), (28, 1), (56, 1), (64, 1), (66, 1)] }, { coefficient := -1, powers := [(25, 1), (28, 1), (56, 1), (64, 1), (66, 1)] }, { coefficient := 1, powers := [(25, 1), (56, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (56, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (30, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [(56, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(36, 1), (56, 1), (59, 1), (64, 1)] }, { coefficient := -1, powers := [(38, 1), (39, 1), (56, 2), (62, 1), (64, 1)] }, { coefficient := -1, powers := [(39, 1), (50, 1), (56, 1), (62, 1), (64, 1)] }, { coefficient := 1, powers := [(39, 1), (56, 2), (64, 1)] }, { coefficient := -1, powers := [(44, 1), (51, 1), (56, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (33, 1), (39, 1), (56, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (4, 1), (30, 1), (38, 1), (56, 1)] }, { coefficient := 1, powers := [(3, 1), (4, 1), (29, 1), (30, 1), (56, 1)] }, { coefficient := 1, powers := [(4, 1), (9, 1), (18, 1), (30, 1), (56, 1)] }, { coefficient := -1, powers := [(4, 1), (18, 1), (30, 1), (48, 1), (56, 1)] }, { coefficient := -1, powers := [(6, 1), (10, 1), (30, 1), (38, 1), (56, 1)] }, { coefficient := -1, powers := [(9, 1), (10, 1), (30, 1), (35, 1), (56, 1)] }, { coefficient := 1, powers := [(10, 1), (30, 1), (35, 1), (48, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (13, 1), (29, 1), (30, 1), (35, 1), (56, 1)] }, { coefficient := 1, powers := [(4, 1), (30, 1), (56, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(3, 1), (4, 1), (30, 1), (56, 1), (58, 1)] }, { coefficient := 1, powers := [(4, 1), (9, 1), (30, 1), (41, 1), (56, 1)] }, { coefficient := 1, powers := [(4, 1), (13, 1), (29, 1), (30, 1), (35, 1), (36, 1), (56, 1), (59, 1), (64, 1)] }, { coefficient := -1, powers := [(4, 1), (13, 1), (30, 1), (35, 1), (38, 1), (44, 1), (56, 1), (59, 1), (64, 1)] }, { coefficient := 1, powers := [(4, 1), (13, 1), (30, 1), (35, 1), (50, 1), (56, 1), (59, 1), (64, 1)] }, { coefficient := 1, powers := [(4, 1), (13, 1), (30, 1), (38, 1), (56, 1)] }, { coefficient := 1, powers := [(4, 1), (18, 1), (25, 1), (39, 1), (44, 1), (56, 1), (59, 1), (64, 1)] }, { coefficient := 1, powers := [(4, 1), (18, 1), (25, 1), (44, 2), (56, 1), (59, 1), (64, 1)] }, { coefficient := 1, powers := [(4, 1), (18, 1), (25, 1), (44, 1), (51, 1), (56, 1), (59, 1), (64, 1)] }, { coefficient := -1, powers := [(4, 1), (18, 1), (33, 1), (36, 1), (39, 1), (56, 1), (59, 1), (64, 1)] }, { coefficient := -1, powers := [(4, 1), (18, 1), (33, 1), (36, 1), (44, 1), (56, 1), (59, 1), (64, 1)] }, { coefficient := -1, powers := [(4, 1), (18, 1), (33, 1), (36, 1), (51, 1), (56, 1), (59, 1), (64, 1)] }, { coefficient := 1, powers := [(4, 1), (20, 1), (39, 1), (56, 1), (59, 1), (64, 1)] }, { coefficient := 1, powers := [(4, 1), (20, 1), (44, 1), (56, 1), (59, 1), (64, 1)] }, { coefficient := 2, powers := [(4, 1), (20, 1), (51, 1), (56, 1), (59, 1), (64, 1)] }, { coefficient := 1, powers := [(4, 1), (20, 1), (56, 2), (59, 1), (64, 1)] }, { coefficient := 1, powers := [(4, 1), (25, 1), (38, 1), (39, 1), (56, 1), (59, 1), (62, 1), (64, 1)] }, { coefficient := -1, powers := [(4, 1), (30, 1), (41, 1), (48, 1), (56, 1)] }, { coefficient := 1, powers := [(4, 1), (33, 1), (36, 1), (56, 1), (59, 1), (64, 1)] }, { coefficient := -1, powers := [(6, 1), (10, 1), (30, 1), (38, 1), (43, 1), (56, 1)] }, { coefficient := -1, powers := [(9, 1), (10, 1), (30, 1), (35, 1), (43, 1), (56, 1)] }, { coefficient := 1, powers := [(10, 1), (13, 1), (29, 1), (30, 1), (35, 1), (36, 1), (44, 1), (56, 1), (64, 1)] }, { coefficient := -1, powers := [(10, 1), (13, 1), (30, 1), (35, 1), (38, 1), (44, 2), (56, 1), (64, 1)] }, { coefficient := 1, powers := [(10, 1), (18, 1), (25, 1), (39, 1), (44, 2), (56, 1), (64, 1)] }, { coefficient := 1, powers := [(10, 1), (18, 1), (25, 1), (44, 3), (56, 1), (64, 1)] }, { coefficient := 1, powers := [(10, 1), (18, 1), (25, 1), (44, 2), (51, 1), (56, 1), (64, 1)] }, { coefficient := -1, powers := [(10, 1), (18, 1), (33, 1), (36, 1), (39, 1), (44, 1), (56, 1), (64, 1)] }, { coefficient := -1, powers := [(10, 1), (18, 1), (33, 1), (36, 1), (44, 2), (56, 1), (64, 1)] }, { coefficient := -1, powers := [(10, 1), (18, 1), (33, 1), (36, 1), (44, 1), (51, 1), (56, 1), (64, 1)] }, { coefficient := 1, powers := [(10, 1), (20, 1), (39, 1), (44, 1), (56, 1), (64, 1)] }, { coefficient := 1, powers := [(10, 1), (20, 1), (44, 2), (56, 1), (64, 1)] }, { coefficient := 2, powers := [(10, 1), (20, 1), (44, 1), (51, 1), (56, 1), (64, 1)] }, { coefficient := 1, powers := [(10, 1), (20, 1), (44, 1), (56, 2), (64, 1)] }, { coefficient := 1, powers := [(10, 1), (25, 1), (38, 1), (39, 1), (44, 1), (56, 1), (62, 1), (64, 1)] }, { coefficient := -1, powers := [(10, 1), (25, 1), (44, 1), (51, 1), (56, 1), (64, 1)] }, { coefficient := 1, powers := [(10, 1), (30, 1), (35, 1), (43, 1), (48, 1), (56, 1)] }, { coefficient := 1, powers := [(10, 1), (33, 1), (36, 1), (44, 1), (56, 1), (64, 1)] }, { coefficient := 1, powers := [(10, 1), (33, 1), (36, 1), (51, 1), (56, 1), (64, 1)] }, { coefficient := 1, powers := [(13, 1), (14, 1), (29, 1), (30, 1), (35, 1), (36, 1), (39, 1), (56, 1), (64, 1)] }, { coefficient := -1, powers := [(13, 1), (14, 1), (30, 1), (35, 1), (38, 1), (39, 1), (44, 1), (56, 1), (64, 1)] }, { coefficient := 1, powers := [(13, 1), (14, 1), (30, 1), (35, 1), (39, 1), (50, 1), (56, 1), (64, 1)] }, { coefficient := 1, powers := [(14, 1), (18, 1), (25, 1), (39, 2), (44, 1), (56, 1), (64, 1)] }, { coefficient := 1, powers := [(14, 1), (18, 1), (25, 1), (39, 1), (44, 2), (56, 1), (64, 1)] }, { coefficient := 1, powers := [(14, 1), (18, 1), (25, 1), (39, 1), (44, 1), (51, 1), (56, 1), (64, 1)] }, { coefficient := -1, powers := [(14, 1), (18, 1), (33, 1), (36, 1), (39, 2), (56, 1), (64, 1)] }, { coefficient := -1, powers := [(14, 1), (18, 1), (33, 1), (36, 1), (39, 1), (44, 1), (56, 1), (64, 1)] }, { coefficient := -1, powers := [(14, 1), (18, 1), (33, 1), (36, 1), (39, 1), (51, 1), (56, 1), (64, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1), (39, 2), (56, 1), (64, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1), (39, 1), (44, 1), (56, 1), (64, 1)] }, { coefficient := 2, powers := [(14, 1), (20, 1), (39, 1), (51, 1), (56, 1), (64, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1), (39, 1), (56, 2), (64, 1)] }, { coefficient := 1, powers := [(14, 1), (25, 1), (38, 1), (39, 2), (56, 1), (62, 1), (64, 1)] }, { coefficient := 1, powers := [(14, 1), (33, 1), (36, 1), (39, 1), (56, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (6, 1), (29, 1), (30, 1), (41, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (4, 1), (30, 1), (35, 1), (56, 1), (58, 1)] }, { coefficient := -1, powers := [(4, 1), (6, 1), (18, 1), (30, 1), (56, 1), (58, 1)] }, { coefficient := -1, powers := [(7, 1), (18, 1), (25, 1), (44, 1), (56, 1), (59, 1), (64, 1)] }, { coefficient := 1, powers := [(7, 1), (18, 1), (33, 1), (36, 1), (56, 1), (59, 1), (64, 1)] }, { coefficient := -1, powers := [(7, 1), (20, 1), (56, 1), (59, 1), (64, 1)] }, { coefficient := 1, powers := [(7, 1), (25, 1), (56, 1), (59, 1), (64, 1)] }, { coefficient := -1, powers := [(10, 1), (18, 1), (25, 1), (44, 1), (56, 2), (64, 1)] }, { coefficient := 1, powers := [(10, 1), (18, 1), (33, 1), (36, 1), (56, 2), (64, 1)] }, { coefficient := -1, powers := [(10, 1), (20, 1), (56, 2), (64, 1)] }, { coefficient := 1, powers := [(10, 1), (25, 1), (56, 2), (64, 1)] }, { coefficient := -1, powers := [(14, 1), (18, 1), (25, 1), (39, 1), (44, 1), (56, 1), (64, 1)] }, { coefficient := -1, powers := [(14, 1), (18, 1), (25, 1), (44, 2), (56, 1), (64, 1)] }, { coefficient := -1, powers := [(14, 1), (18, 1), (25, 1), (44, 1), (51, 1), (56, 1), (64, 1)] }, { coefficient := 1, powers := [(14, 1), (18, 1), (33, 1), (36, 1), (39, 1), (56, 1), (64, 1)] }, { coefficient := 1, powers := [(14, 1), (18, 1), (33, 1), (36, 1), (44, 1), (56, 1), (64, 1)] }, { coefficient := 1, powers := [(14, 1), (18, 1), (33, 1), (36, 1), (51, 1), (56, 1), (64, 1)] }, { coefficient := -1, powers := [(14, 1), (20, 1), (39, 1), (56, 1), (64, 1)] }, { coefficient := -1, powers := [(14, 1), (20, 1), (44, 1), (56, 1), (64, 1)] }, { coefficient := -1, powers := [(14, 1), (20, 1), (51, 1), (56, 1), (64, 1)] }, { coefficient := 1, powers := [(14, 1), (25, 1), (39, 1), (56, 1), (64, 1)] }, { coefficient := 1, powers := [(14, 1), (25, 1), (44, 1), (56, 1), (64, 1)] }, { coefficient := 1, powers := [(14, 1), (25, 1), (51, 1), (56, 1), (64, 1)] }]
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
    ¬ ∀ index : Fin 25,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component39.SelectedLeafB4_6_2_3.selectedHasNoCommonZero

end Krenn.Component39.SelectedLeafB4_6_2_3
