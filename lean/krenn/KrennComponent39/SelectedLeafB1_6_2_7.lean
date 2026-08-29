import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component39.SelectedLeafB1_6_2_7

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "241ac16e28cb3416f8337c9da43e9da06cd120be9d80daf2e11ffd0d3de05e89"
def certificateSHA256 : String := "deec03403e8e62782b7455354cb3afe85bb3fd55339dfa09a70d80dafdd59353"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 36 → Fin 673 := ![
  17,
  22,
  28,
  173,
  176,
  270,
  304,
  305,
  314,
  318,
  368,
  379,
  391,
  416,
  439,
  476,
  482,
  511,
  513,
  515,
  600,
  601,
  602,
  603,
  610,
  644,
  658,
  659,
  661,
  662,
  663,
  664,
  667,
  670,
  671,
  672
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 36 → SparsePoly (Fin 68) := ![
  [{ coefficient := 1, powers := [(14, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (23, 1)] }, { coefficient := 1, powers := [(14, 1), (18, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (28, 1)] }, { coefficient := 1, powers := [(14, 1), (21, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (21, 1), (48, 1)] }, { coefficient := 1, powers := [(14, 1), (26, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (44, 1)] }, { coefficient := 1, powers := [(4, 1), (33, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (51, 1)] }, { coefficient := 1, powers := [(7, 1), (30, 1)] }, { coefficient := 1, powers := [(10, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (21, 1)] }, { coefficient := 1, powers := [(21, 1), (55, 1)] }, { coefficient := 1, powers := [(26, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (53, 1)] }, { coefficient := 1, powers := [(28, 1), (39, 1)] }, { coefficient := 1, powers := [(28, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (18, 1), (58, 1)] }, { coefficient := 1, powers := [(7, 1), (29, 1), (41, 1)] }, { coefficient := 1, powers := [(7, 1), (32, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (18, 1), (55, 1)] }, { coefficient := 1, powers := [(10, 1), (23, 1), (41, 1)] }, { coefficient := 1, powers := [(10, 1), (32, 1), (35, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (18, 1), (48, 1)] }, { coefficient := 1, powers := [(14, 1), (23, 1), (38, 1)] }, { coefficient := 1, powers := [(14, 1), (29, 1), (35, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (44, 1)] }, { coefficient := 1, powers := [(16, 1), (26, 1), (39, 1)] }, { coefficient := 1, powers := [(16, 1), (26, 1), (44, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (39, 1)] }, { coefficient := 1, powers := [(16, 1), (44, 1)] }, { coefficient := 1, powers := [(16, 1), (51, 1)] }, { coefficient := 1, powers := [(16, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (38, 1), (56, 1)] }, { coefficient := 1, powers := [(1, 1), (50, 1)] }, { coefficient := 1, powers := [(7, 1), (33, 1), (38, 1)] }, { coefficient := 1, powers := [(14, 1), (25, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (35, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1)] }, { coefficient := 1, powers := [(16, 1), (21, 1)] }, { coefficient := 1, powers := [(16, 1), (26, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (23, 1), (59, 1)] }, { coefficient := 1, powers := [(10, 1), (23, 1), (44, 1)] }, { coefficient := 1, powers := [(14, 1), (23, 1), (39, 1)] }, { coefficient := 1, powers := [(14, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (26, 1), (59, 1)] }, { coefficient := 1, powers := [(10, 1), (26, 1), (44, 1)] }, { coefficient := 1, powers := [(14, 1), (26, 1), (39, 1)] }, { coefficient := 1, powers := [(14, 1), (27, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (28, 1), (59, 1)] }, { coefficient := 1, powers := [(10, 1), (28, 1), (44, 1)] }, { coefficient := 1, powers := [(14, 1), (27, 1), (53, 1)] }, { coefficient := 1, powers := [(14, 1), (28, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (41, 1)] }, { coefficient := 1, powers := [(3, 1), (32, 1)] }, { coefficient := 1, powers := [(13, 1), (18, 1)] }, { coefficient := 1, powers := [(18, 1), (55, 1)] }, { coefficient := 1, powers := [(23, 1), (41, 1)] }, { coefficient := 1, powers := [(32, 1), (35, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (48, 1)] }, { coefficient := 1, powers := [(6, 1), (29, 1)] }, { coefficient := 1, powers := [(9, 1), (23, 1)] }, { coefficient := 1, powers := [(18, 1), (48, 1)] }, { coefficient := 1, powers := [(23, 1), (38, 1)] }, { coefficient := 1, powers := [(29, 1), (35, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (59, 1)] }, { coefficient := 1, powers := [(10, 1), (44, 1)] }, { coefficient := 1, powers := [(10, 1), (56, 1)] }, { coefficient := 1, powers := [(14, 1), (39, 1)] }, { coefficient := 1, powers := [(14, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (51, 1)] }, { coefficient := 1, powers := [(20, 1), (56, 1)] }, { coefficient := 1, powers := [(25, 1), (39, 1)] }, { coefficient := 1, powers := [(25, 1), (44, 1)] }, { coefficient := 1, powers := [(30, 1), (36, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (41, 1), (50, 1)] }, { coefficient := 1, powers := [(3, 1), (32, 1), (50, 1)] }, { coefficient := 1, powers := [(3, 1), (58, 1)] }, { coefficient := 1, powers := [(9, 1), (41, 1)] }, { coefficient := 1, powers := [(13, 1), (18, 1), (50, 1)] }, { coefficient := 1, powers := [(13, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (36, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (44, 1), (51, 1)] }, { coefficient := 1, powers := [(39, 1)] }, { coefficient := 1, powers := [(44, 1)] }, { coefficient := 1, powers := [(51, 1)] }, { coefficient := 1, powers := [(56, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (35, 1), (58, 1)] }, { coefficient := 1, powers := [(0, 1), (38, 1), (55, 1)] }, { coefficient := 1, powers := [(0, 1), (41, 1), (48, 1)] }, { coefficient := 1, powers := [(3, 1), (23, 1), (58, 1)] }, { coefficient := 1, powers := [(3, 1), (29, 1), (55, 1)] }, { coefficient := 1, powers := [(3, 1), (32, 1), (48, 1)] }, { coefficient := 1, powers := [(6, 1), (18, 1), (58, 1)] }, { coefficient := 1, powers := [(6, 1), (29, 1), (41, 1)] }, { coefficient := 1, powers := [(6, 1), (32, 1), (38, 1)] }, { coefficient := 1, powers := [(9, 1), (18, 1), (55, 1)] }, { coefficient := 1, powers := [(9, 1), (23, 1), (41, 1)] }, { coefficient := 1, powers := [(9, 1), (32, 1), (35, 1)] }, { coefficient := 1, powers := [(13, 1), (18, 1), (48, 1)] }, { coefficient := 1, powers := [(13, 1), (23, 1), (38, 1)] }, { coefficient := 1, powers := [(13, 1), (29, 1), (35, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1), (36, 1), (59, 1)] }, { coefficient := 1, powers := [(1, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(1, 1), (44, 1), (51, 1)] }, { coefficient := 1, powers := [(4, 1), (25, 1), (59, 1)] }, { coefficient := 1, powers := [(4, 1), (30, 1), (56, 1)] }, { coefficient := 1, powers := [(4, 1), (33, 1), (51, 1)] }, { coefficient := 1, powers := [(7, 1), (20, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (30, 1), (44, 1)] }, { coefficient := 1, powers := [(7, 1), (33, 1), (39, 1)] }, { coefficient := 1, powers := [(10, 1), (20, 1), (56, 1)] }, { coefficient := 1, powers := [(10, 1), (25, 1), (44, 1)] }, { coefficient := 1, powers := [(10, 1), (33, 1), (36, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1), (51, 1)] }, { coefficient := 1, powers := [(14, 1), (25, 1), (39, 1)] }, { coefficient := 1, powers := [(14, 1), (30, 1), (36, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1)] }],
  [{ coefficient := 1, powers := [(1, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (61, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(38, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(55, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (65, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(25, 1), (66, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(28, 1), (67, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 36 → SparsePoly (Fin 68) := ![
  [{ coefficient := 1, powers := [(13, 1), (18, 2), (33, 1), (36, 1), (65, 1)] }, { coefficient := 1, powers := [(20, 1), (21, 1), (51, 1), (53, 1), (62, 1), (67, 1)] }, { coefficient := -1, powers := [(21, 1), (25, 1), (44, 1), (53, 1), (62, 1), (67, 1)] }, { coefficient := -1, powers := [(21, 1), (25, 1), (51, 1), (53, 1), (62, 1), (67, 1)] }, { coefficient := -1, powers := [(21, 1), (25, 1), (53, 1), (56, 1), (62, 1), (67, 1)] }, { coefficient := 1, powers := [(21, 1), (33, 1), (36, 1), (53, 1), (62, 1), (67, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (21, 1), (30, 1), (56, 1), (61, 1), (66, 1)] }, { coefficient := -1, powers := [(4, 1), (26, 1), (30, 1), (56, 1), (61, 1), (66, 1)] }, { coefficient := 1, powers := [(7, 1), (21, 1), (30, 1), (44, 1), (61, 1), (66, 1)] }, { coefficient := 1, powers := [(7, 1), (26, 1), (30, 1), (44, 1), (61, 1), (66, 1)] }, { coefficient := 1, powers := [(7, 1), (26, 1), (30, 1), (51, 1), (61, 1), (66, 1)] }, { coefficient := 1, powers := [(7, 1), (26, 1), (30, 1), (56, 1), (61, 1), (66, 1)] }, { coefficient := -1, powers := [(7, 1), (27, 1), (30, 1), (61, 1), (66, 1)] }, { coefficient := -1, powers := [(10, 1), (25, 1), (26, 1), (51, 1), (61, 1), (66, 1)] }, { coefficient := -1, powers := [(10, 1), (25, 1), (26, 1), (56, 1), (61, 1), (66, 1)] }, { coefficient := 1, powers := [(10, 1), (25, 1), (27, 1), (61, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (7, 1), (29, 1), (30, 1), (33, 1), (36, 1), (66, 2)] }, { coefficient := 1, powers := [(6, 1), (10, 1), (29, 1), (33, 1), (36, 1), (66, 1)] }, { coefficient := -1, powers := [(9, 1), (10, 1), (23, 1), (33, 1), (36, 1), (66, 1)] }, { coefficient := -1, powers := [(14, 1), (23, 1), (26, 1), (33, 1), (36, 1), (38, 1), (53, 1), (66, 1), (67, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (13, 1), (29, 1), (33, 1), (36, 1), (65, 1)] }, { coefficient := -1, powers := [(9, 1), (13, 1), (23, 1), (33, 1), (36, 1), (65, 1)] }, { coefficient := -1, powers := [(13, 1), (18, 1), (33, 1), (36, 1), (48, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(13, 1), (23, 1), (33, 1), (36, 1), (38, 1), (67, 1)] }],
  [{ coefficient := -1, powers := [(20, 1), (51, 1), (53, 1), (62, 1), (67, 1)] }, { coefficient := 1, powers := [(25, 1), (44, 1), (53, 1), (62, 1), (67, 1)] }, { coefficient := 1, powers := [(25, 1), (51, 1), (53, 1), (62, 1), (67, 1)] }, { coefficient := 1, powers := [(25, 1), (53, 1), (56, 1), (62, 1), (67, 1)] }, { coefficient := -1, powers := [(33, 1), (36, 1), (53, 1), (62, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(51, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (18, 1), (33, 1), (36, 1), (58, 1), (66, 1)] }, { coefficient := 1, powers := [(6, 1), (32, 1), (33, 1), (36, 1), (38, 1), (66, 1)] }, { coefficient := 1, powers := [(44, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (23, 1), (33, 1), (36, 1), (38, 1), (53, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (20, 1), (67, 1)] }, { coefficient := -1, powers := [(14, 1), (25, 1), (67, 1)] }, { coefficient := 1, powers := [(14, 1), (30, 1), (35, 1), (44, 1), (67, 1)] }, { coefficient := 1, powers := [(14, 1), (30, 1), (35, 1), (56, 1), (67, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (30, 1), (33, 1), (36, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (33, 1), (36, 1)] }, { coefficient := 1, powers := [(23, 1), (33, 1), (36, 1), (50, 1)] }, { coefficient := -1, powers := [(33, 1), (36, 1), (48, 1)] }],
  [{ coefficient := -1, powers := [(13, 1), (18, 1), (33, 1), (36, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (30, 1), (61, 1)] }, { coefficient := -1, powers := [(10, 1), (25, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (26, 1), (30, 1), (61, 1)] }, { coefficient := 1, powers := [(10, 1), (25, 1), (26, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(44, 1), (62, 1)] }, { coefficient := -1, powers := [(51, 1), (62, 1)] }, { coefficient := -1, powers := [(56, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (30, 1), (56, 1), (61, 1)] }, { coefficient := -1, powers := [(7, 1), (30, 1), (44, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (26, 1), (51, 1), (53, 1), (67, 1)] }, { coefficient := -1, powers := [(20, 1), (28, 1), (51, 1), (67, 1)] }, { coefficient := -1, powers := [(25, 1), (26, 1), (44, 1), (53, 1), (67, 1)] }, { coefficient := -1, powers := [(25, 1), (26, 1), (51, 1), (53, 1), (67, 1)] }, { coefficient := -1, powers := [(25, 1), (26, 1), (53, 1), (56, 1), (67, 1)] }, { coefficient := 1, powers := [(25, 1), (28, 1), (44, 1), (67, 1)] }, { coefficient := 1, powers := [(25, 1), (28, 1), (51, 1), (67, 1)] }, { coefficient := 1, powers := [(25, 1), (28, 1), (56, 1), (67, 1)] }, { coefficient := 1, powers := [(26, 1), (33, 1), (36, 1), (53, 1), (67, 1)] }, { coefficient := -1, powers := [(28, 1), (33, 1), (36, 1), (67, 1)] }],
  [{ coefficient := -1, powers := [(20, 1), (23, 1), (51, 1), (53, 1), (67, 1)] }, { coefficient := 1, powers := [(23, 1), (25, 1), (44, 1), (53, 1), (67, 1)] }, { coefficient := 1, powers := [(23, 1), (25, 1), (51, 1), (53, 1), (67, 1)] }, { coefficient := 1, powers := [(23, 1), (25, 1), (53, 1), (56, 1), (67, 1)] }, { coefficient := -1, powers := [(23, 1), (33, 1), (36, 1), (53, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (23, 1), (51, 1), (67, 1)] }, { coefficient := -1, powers := [(20, 1), (67, 1)] }, { coefficient := -1, powers := [(23, 1), (25, 1), (44, 1), (67, 1)] }, { coefficient := -1, powers := [(23, 1), (25, 1), (51, 1), (67, 1)] }, { coefficient := -1, powers := [(23, 1), (25, 1), (56, 1), (67, 1)] }, { coefficient := 1, powers := [(23, 1), (33, 1), (36, 1), (67, 1)] }, { coefficient := 1, powers := [(25, 1), (67, 1)] }, { coefficient := -1, powers := [(30, 1), (35, 1), (44, 1), (67, 1)] }, { coefficient := -1, powers := [(30, 1), (35, 1), (56, 1), (67, 1)] }],
  [{ coefficient := -1, powers := [(10, 1), (23, 1), (33, 1), (36, 1), (50, 1)] }, { coefficient := 1, powers := [(10, 1), (33, 1), (36, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (13, 1), (33, 1), (36, 1)] }, { coefficient := 1, powers := [(13, 1), (14, 1), (18, 1), (33, 1), (36, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (28, 1), (67, 1)] }, { coefficient := -1, powers := [(25, 1), (28, 1), (67, 1)] }, { coefficient := 1, powers := [(25, 1)] }, { coefficient := 1, powers := [(28, 1), (30, 1), (35, 1), (44, 1), (67, 1)] }, { coefficient := 1, powers := [(28, 1), (30, 1), (35, 1), (56, 1), (67, 1)] }, { coefficient := -1, powers := [(30, 1), (35, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(14, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (23, 1), (33, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (33, 1)] }, { coefficient := -1, powers := [(14, 1), (20, 1)] }, { coefficient := -1, powers := [(14, 1), (30, 1), (35, 1), (44, 1)] }],
  [{ coefficient := -1, powers := [(10, 1), (33, 1), (36, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(7, 1), (33, 1), (36, 1), (59, 1)] }, { coefficient := -1, powers := [(7, 1), (33, 1), (39, 1), (56, 1)] }, { coefficient := -1, powers := [(7, 1), (33, 1), (44, 1), (51, 1)] }, { coefficient := -1, powers := [(10, 1), (13, 1), (33, 1), (36, 1), (48, 1)] }, { coefficient := 1, powers := [(10, 1), (33, 1), (35, 1), (36, 1), (58, 1)] }, { coefficient := 1, powers := [(10, 1), (33, 1), (36, 1), (38, 1), (55, 1)] }, { coefficient := -1, powers := [(13, 1), (14, 1), (18, 1), (33, 1), (36, 1), (48, 1), (65, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1), (36, 1), (59, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1), (44, 1), (51, 1)] }, { coefficient := 1, powers := [(14, 1), (30, 1), (35, 1), (36, 1), (44, 1), (59, 1)] }, { coefficient := 1, powers := [(14, 1), (30, 1), (35, 1), (39, 1), (44, 1), (56, 1)] }, { coefficient := 1, powers := [(14, 1), (30, 1), (35, 1), (44, 2), (51, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (18, 1), (33, 1), (36, 1), (51, 1), (58, 1), (66, 1)] }, { coefficient := -1, powers := [(6, 1), (32, 1), (33, 1), (36, 1), (38, 1), (51, 1), (66, 1)] }, { coefficient := 1, powers := [(36, 1), (59, 1)] }, { coefficient := 1, powers := [(38, 1), (44, 1), (56, 1), (62, 1)] }, { coefficient := 1, powers := [(38, 1), (51, 1), (56, 1), (62, 1)] }, { coefficient := 1, powers := [(38, 1), (56, 2), (62, 1)] }, { coefficient := 1, powers := [(39, 1), (56, 1)] }, { coefficient := 1, powers := [(44, 1), (50, 1), (62, 1)] }, { coefficient := -1, powers := [(44, 1), (51, 1)] }, { coefficient := 1, powers := [(50, 1), (51, 1), (62, 1)] }, { coefficient := 1, powers := [(50, 1), (56, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (30, 1), (35, 1), (56, 1), (59, 1)] }, { coefficient := -1, powers := [(4, 1), (30, 1), (56, 1)] }, { coefficient := 1, powers := [(7, 1), (30, 1), (35, 1), (44, 1), (59, 1)] }, { coefficient := 1, powers := [(10, 1), (25, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (33, 1), (44, 1)] }, { coefficient := 1, powers := [(7, 1), (33, 1), (51, 1)] }, { coefficient := 1, powers := [(7, 1), (33, 1), (56, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1), (26, 1), (51, 1), (53, 1), (67, 1)] }, { coefficient := -1, powers := [(14, 1), (25, 1), (26, 1), (44, 1), (53, 1), (67, 1)] }, { coefficient := -1, powers := [(14, 1), (25, 1), (26, 1), (51, 1), (53, 1), (67, 1)] }, { coefficient := -1, powers := [(14, 1), (25, 1), (26, 1), (53, 1), (56, 1), (67, 1)] }, { coefficient := 1, powers := [(14, 1), (25, 1), (44, 1)] }, { coefficient := 1, powers := [(14, 1), (25, 1), (51, 1)] }, { coefficient := 1, powers := [(14, 1), (25, 1), (56, 1)] }, { coefficient := 1, powers := [(14, 1), (26, 1), (33, 1), (36, 1), (53, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (10, 1), (29, 1), (33, 1), (36, 1)] }, { coefficient := -1, powers := [(14, 1), (21, 1), (23, 1), (33, 1), (36, 1), (38, 1), (53, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (10, 1), (13, 1), (29, 1), (33, 1), (36, 1)] }, { coefficient := 1, powers := [(9, 1), (10, 1), (13, 1), (23, 1), (33, 1), (36, 1)] }, { coefficient := 1, powers := [(10, 1), (13, 1), (18, 1), (33, 1), (36, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (16, 1), (21, 1), (30, 1), (56, 1), (61, 1)] }, { coefficient := 1, powers := [(4, 1), (16, 1), (26, 1), (30, 1), (56, 1), (61, 1)] }, { coefficient := -1, powers := [(6, 1), (7, 1), (29, 1), (30, 1), (33, 1), (36, 1), (41, 1), (66, 1)] }, { coefficient := -1, powers := [(6, 1), (10, 1), (18, 1), (33, 1), (36, 1), (58, 1)] }, { coefficient := -1, powers := [(6, 1), (10, 1), (29, 1), (33, 1), (36, 1), (41, 1)] }, { coefficient := -1, powers := [(6, 1), (10, 1), (32, 1), (33, 1), (36, 1), (38, 1)] }, { coefficient := -1, powers := [(7, 1), (16, 1), (21, 1), (30, 1), (44, 1), (61, 1)] }, { coefficient := -1, powers := [(7, 1), (16, 1), (26, 1), (30, 1), (44, 1), (61, 1)] }, { coefficient := -1, powers := [(7, 1), (16, 1), (26, 1), (30, 1), (51, 1), (61, 1)] }, { coefficient := -1, powers := [(7, 1), (16, 1), (26, 1), (30, 1), (56, 1), (61, 1)] }, { coefficient := 1, powers := [(7, 1), (16, 1), (27, 1), (30, 1), (61, 1)] }, { coefficient := 1, powers := [(9, 1), (10, 1), (23, 1), (33, 1), (36, 1), (41, 1)] }, { coefficient := 1, powers := [(10, 1), (16, 1), (25, 1), (26, 1), (51, 1), (61, 1)] }, { coefficient := 1, powers := [(10, 1), (16, 1), (25, 1), (26, 1), (56, 1), (61, 1)] }, { coefficient := -1, powers := [(10, 1), (16, 1), (25, 1), (27, 1), (61, 1)] }, { coefficient := 1, powers := [(14, 1), (23, 1), (26, 1), (33, 1), (36, 1), (38, 1), (41, 1), (53, 1), (67, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (20, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (25, 1), (59, 1)] }, { coefficient := -1, powers := [(7, 1), (30, 1), (35, 1), (44, 1), (59, 1)] }, { coefficient := -1, powers := [(7, 1), (30, 1), (35, 1), (56, 1), (59, 1)] }, { coefficient := 1, powers := [(10, 1), (13, 1), (23, 1), (33, 1), (36, 1), (38, 1)] }, { coefficient := -1, powers := [(10, 1), (20, 1), (56, 1)] }, { coefficient := 1, powers := [(10, 1), (25, 1), (56, 1)] }, { coefficient := -1, powers := [(10, 1), (30, 1), (35, 1), (44, 1), (56, 1)] }, { coefficient := -1, powers := [(10, 1), (30, 1), (35, 1), (56, 2)] }, { coefficient := -1, powers := [(14, 1), (20, 1), (39, 1)] }, { coefficient := -1, powers := [(14, 1), (20, 1), (44, 1)] }, { coefficient := 1, powers := [(14, 1), (25, 1), (39, 1)] }, { coefficient := -1, powers := [(14, 1), (25, 1), (56, 1)] }, { coefficient := -1, powers := [(14, 1), (30, 1), (35, 1), (39, 1), (44, 1)] }, { coefficient := -1, powers := [(14, 1), (30, 1), (35, 1), (39, 1), (56, 1)] }, { coefficient := -1, powers := [(14, 1), (30, 1), (35, 1), (44, 2)] }, { coefficient := -1, powers := [(14, 1), (30, 1), (35, 1), (44, 1), (51, 1)] }, { coefficient := -1, powers := [(14, 1), (30, 1), (35, 1), (44, 1), (56, 1)] }, { coefficient := -1, powers := [(14, 1), (30, 1), (35, 1), (51, 1), (56, 1)] }, { coefficient := 1, powers := [(14, 1), (33, 1), (36, 1)] }]
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
    ¬ ∀ index : Fin 36,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component39.SelectedLeafB1_6_2_7.selectedHasNoCommonZero

end Krenn.Component39.SelectedLeafB1_6_2_7
