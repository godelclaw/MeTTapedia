import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component39.SelectedLeafB1_6_6_7

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "86a8a2fc13dc734ca348efb281d8f840495621a87a20334b31c69badd400a49d"
def certificateSHA256 : String := "289ed5e4fe8bd7dacc4a9bca79b0c58b7728796df36d0f5223666bcd08637a5b"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 37 → Fin 673 := ![
  17,
  22,
  26,
  28,
  175,
  176,
  177,
  270,
  304,
  305,
  309,
  318,
  349,
  351,
  368,
  379,
  476,
  477,
  481,
  511,
  513,
  515,
  547,
  600,
  601,
  602,
  603,
  644,
  658,
  659,
  661,
  662,
  663,
  664,
  667,
  671,
  672
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 37 → SparsePoly (Fin 69) := ![
  [{ coefficient := 1, powers := [(14, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (26, 1)] }, { coefficient := 1, powers := [(14, 1), (21, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (28, 1)] }, { coefficient := 1, powers := [(14, 1), (21, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (25, 1)] }, { coefficient := 1, powers := [(16, 1), (25, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (21, 1), (48, 1)] }, { coefficient := 1, powers := [(14, 1), (26, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (44, 1)] }, { coefficient := 1, powers := [(4, 1), (33, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (51, 1)] }, { coefficient := 1, powers := [(7, 1), (30, 1)] }, { coefficient := 1, powers := [(10, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (28, 1)] }, { coefficient := 1, powers := [(21, 1), (24, 1), (50, 1)] }, { coefficient := 1, powers := [(28, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (53, 1)] }, { coefficient := 1, powers := [(28, 1), (39, 1)] }, { coefficient := 1, powers := [(28, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (25, 1), (58, 1)] }, { coefficient := 1, powers := [(9, 1), (25, 1), (41, 1)] }, { coefficient := 1, powers := [(13, 1), (25, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (30, 1), (55, 1)] }, { coefficient := 1, powers := [(6, 1), (30, 1), (41, 1)] }, { coefficient := 1, powers := [(13, 1), (30, 1), (35, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (18, 1), (58, 1)] }, { coefficient := 1, powers := [(7, 1), (29, 1), (41, 1)] }, { coefficient := 1, powers := [(7, 1), (32, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (18, 1), (55, 1)] }, { coefficient := 1, powers := [(10, 1), (23, 1), (41, 1)] }, { coefficient := 1, powers := [(10, 1), (32, 1), (35, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (38, 1), (56, 1)] }, { coefficient := 1, powers := [(1, 1), (50, 1)] }, { coefficient := 1, powers := [(7, 1), (33, 1), (38, 1)] }, { coefficient := 1, powers := [(14, 1), (25, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (39, 1), (55, 1)] }, { coefficient := 1, powers := [(1, 1), (43, 1)] }, { coefficient := 1, powers := [(4, 1), (30, 1), (55, 1)] }, { coefficient := 1, powers := [(10, 1), (20, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (24, 1), (50, 1)] }, { coefficient := 1, powers := [(11, 1), (28, 1)] }, { coefficient := 1, powers := [(16, 1), (21, 1), (24, 1), (50, 1)] }, { coefficient := 1, powers := [(16, 1), (28, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (23, 1), (59, 1)] }, { coefficient := 1, powers := [(10, 1), (23, 1), (44, 1)] }, { coefficient := 1, powers := [(14, 1), (23, 1), (39, 1)] }, { coefficient := 1, powers := [(14, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (26, 1), (59, 1)] }, { coefficient := 1, powers := [(10, 1), (26, 1), (44, 1)] }, { coefficient := 1, powers := [(14, 1), (26, 1), (39, 1)] }, { coefficient := 1, powers := [(14, 1), (27, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (28, 1), (59, 1)] }, { coefficient := 1, powers := [(10, 1), (28, 1), (44, 1)] }, { coefficient := 1, powers := [(14, 1), (27, 1), (53, 1)] }, { coefficient := 1, powers := [(14, 1), (28, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (20, 1), (56, 1)] }, { coefficient := 1, powers := [(9, 1), (25, 1), (44, 1)] }, { coefficient := 1, powers := [(9, 1), (33, 1), (36, 1)] }, { coefficient := 1, powers := [(20, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (41, 1)] }, { coefficient := 1, powers := [(3, 1), (32, 1)] }, { coefficient := 1, powers := [(13, 1), (18, 1)] }, { coefficient := 1, powers := [(18, 1), (55, 1)] }, { coefficient := 1, powers := [(23, 1), (41, 1)] }, { coefficient := 1, powers := [(32, 1), (35, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (48, 1)] }, { coefficient := 1, powers := [(6, 1), (29, 1)] }, { coefficient := 1, powers := [(9, 1), (23, 1)] }, { coefficient := 1, powers := [(18, 1), (48, 1)] }, { coefficient := 1, powers := [(23, 1), (38, 1)] }, { coefficient := 1, powers := [(29, 1), (35, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (59, 1)] }, { coefficient := 1, powers := [(10, 1), (44, 1)] }, { coefficient := 1, powers := [(10, 1), (56, 1)] }, { coefficient := 1, powers := [(14, 1), (39, 1)] }, { coefficient := 1, powers := [(14, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (51, 1)] }, { coefficient := 1, powers := [(20, 1), (56, 1)] }, { coefficient := 1, powers := [(25, 1), (39, 1)] }, { coefficient := 1, powers := [(25, 1), (44, 1)] }, { coefficient := 1, powers := [(30, 1), (36, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (36, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (44, 1), (51, 1)] }, { coefficient := 1, powers := [(39, 1)] }, { coefficient := 1, powers := [(44, 1)] }, { coefficient := 1, powers := [(51, 1)] }, { coefficient := 1, powers := [(56, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (35, 1), (58, 1)] }, { coefficient := 1, powers := [(0, 1), (38, 1), (55, 1)] }, { coefficient := 1, powers := [(0, 1), (41, 1), (48, 1)] }, { coefficient := 1, powers := [(3, 1), (23, 1), (58, 1)] }, { coefficient := 1, powers := [(3, 1), (29, 1), (55, 1)] }, { coefficient := 1, powers := [(3, 1), (32, 1), (48, 1)] }, { coefficient := 1, powers := [(6, 1), (18, 1), (58, 1)] }, { coefficient := 1, powers := [(6, 1), (29, 1), (41, 1)] }, { coefficient := 1, powers := [(6, 1), (32, 1), (38, 1)] }, { coefficient := 1, powers := [(9, 1), (18, 1), (55, 1)] }, { coefficient := 1, powers := [(9, 1), (23, 1), (41, 1)] }, { coefficient := 1, powers := [(9, 1), (32, 1), (35, 1)] }, { coefficient := 1, powers := [(13, 1), (18, 1), (48, 1)] }, { coefficient := 1, powers := [(13, 1), (23, 1), (38, 1)] }, { coefficient := 1, powers := [(13, 1), (29, 1), (35, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1), (36, 1), (59, 1)] }, { coefficient := 1, powers := [(1, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(1, 1), (44, 1), (51, 1)] }, { coefficient := 1, powers := [(4, 1), (25, 1), (59, 1)] }, { coefficient := 1, powers := [(4, 1), (30, 1), (56, 1)] }, { coefficient := 1, powers := [(4, 1), (33, 1), (51, 1)] }, { coefficient := 1, powers := [(7, 1), (20, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (30, 1), (44, 1)] }, { coefficient := 1, powers := [(7, 1), (33, 1), (39, 1)] }, { coefficient := 1, powers := [(10, 1), (20, 1), (56, 1)] }, { coefficient := 1, powers := [(10, 1), (25, 1), (44, 1)] }, { coefficient := 1, powers := [(10, 1), (33, 1), (36, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1), (51, 1)] }, { coefficient := 1, powers := [(14, 1), (25, 1), (39, 1)] }, { coefficient := 1, powers := [(14, 1), (30, 1), (36, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1)] }],
  [{ coefficient := 1, powers := [(1, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (61, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(38, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(55, 1), (64, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(25, 1), (67, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(28, 1), (68, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 37 → SparsePoly (Fin 69) := ![
  [{ coefficient := -2, powers := [(9, 1), (20, 1), (21, 1), (51, 1), (53, 1), (62, 2), (68, 1)] }, { coefficient := 2, powers := [(9, 1), (21, 1), (25, 1), (44, 1), (53, 1), (62, 2), (68, 1)] }, { coefficient := 1, powers := [(9, 1), (21, 1), (25, 1), (51, 1), (53, 1), (62, 2), (68, 1)] }, { coefficient := 1, powers := [(9, 1), (21, 1), (25, 1), (53, 1), (56, 1), (62, 2), (68, 1)] }, { coefficient := 1, powers := [(20, 1), (21, 1), (50, 1), (53, 1), (62, 2), (68, 1)] }],
  [{ coefficient := -1, powers := [(9, 1), (21, 1), (28, 1), (61, 1), (62, 1), (67, 1), (68, 1)] }, { coefficient := -1, powers := [(21, 1), (28, 1), (38, 1), (61, 1), (62, 1), (67, 1), (68, 1)] }],
  [{ coefficient := -2, powers := [(9, 1), (10, 1), (26, 1), (51, 1), (62, 1), (68, 1)] }, { coefficient := 2, powers := [(9, 1), (10, 1), (27, 1), (62, 1), (68, 1)] }, { coefficient := -1, powers := [(9, 1), (14, 1), (27, 1), (62, 1), (68, 1)] }, { coefficient := 1, powers := [(10, 1), (26, 1), (50, 1), (62, 1), (68, 1)] }],
  [{ coefficient := 2, powers := [(6, 1), (7, 1), (9, 1), (29, 1), (30, 1), (44, 1), (62, 1), (67, 1)] }, { coefficient := 2, powers := [(7, 1), (9, 2), (23, 1), (30, 1), (44, 1), (62, 1), (67, 1)] }],
  [{ coefficient := 2, powers := [(9, 1), (20, 1), (51, 1), (53, 1), (62, 1), (68, 1)] }, { coefficient := -1, powers := [(20, 1), (50, 1), (53, 1), (62, 1), (68, 1)] }],
  [{ coefficient := -2, powers := [(9, 1), (20, 1), (51, 1), (62, 1), (68, 1)] }, { coefficient := 1, powers := [(20, 1), (50, 1), (62, 1), (68, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (28, 1), (61, 1), (62, 1), (67, 1), (68, 1)] }],
  [{ coefficient := 2, powers := [(9, 1), (20, 1), (51, 1), (53, 1), (62, 2), (68, 1)] }, { coefficient := -2, powers := [(9, 1), (25, 1), (44, 1), (53, 1), (62, 2), (68, 1)] }, { coefficient := -1, powers := [(9, 1), (25, 1), (51, 1), (53, 1), (62, 2), (68, 1)] }, { coefficient := -1, powers := [(9, 1), (25, 1), (53, 1), (56, 1), (62, 2), (68, 1)] }, { coefficient := -1, powers := [(20, 1), (50, 1), (53, 1), (62, 2), (68, 1)] }],
  [{ coefficient := -1, powers := [(9, 1), (51, 1), (62, 1)] }],
  [{ coefficient := 2, powers := [(3, 1), (9, 2), (32, 1), (44, 1), (62, 1)] }, { coefficient := -2, powers := [(3, 1), (9, 1), (32, 1), (44, 1), (48, 1), (62, 1)] }, { coefficient := 2, powers := [(6, 1), (9, 1), (13, 1), (29, 1), (44, 1), (62, 1)] }, { coefficient := 2, powers := [(9, 2), (13, 1), (18, 1), (44, 1), (62, 1)] }, { coefficient := 2, powers := [(9, 2), (13, 1), (23, 1), (44, 1), (62, 1)] }, { coefficient := 2, powers := [(9, 1), (13, 1), (23, 1), (38, 1), (44, 1), (62, 1)] }, { coefficient := 2, powers := [(9, 1), (13, 1), (29, 1), (35, 1), (44, 1), (62, 1)] }, { coefficient := 1, powers := [(9, 1), (44, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (21, 1), (61, 1), (62, 1), (68, 1)] }, { coefficient := 1, powers := [(62, 1), (68, 1)] }],
  [{ coefficient := -2, powers := [(9, 1), (10, 1), (20, 1), (62, 1), (68, 1)] }, { coefficient := 1, powers := [(9, 1), (14, 1), (25, 1), (62, 1), (68, 1)] }],
  [{ coefficient := -2, powers := [(7, 1), (9, 1), (23, 1), (30, 1), (44, 1), (62, 1), (67, 1)] }],
  [{ coefficient := -2, powers := [(7, 1), (9, 1), (29, 1), (44, 1), (62, 1)] }],
  [{ coefficient := -2, powers := [(6, 1), (9, 1), (30, 1), (44, 1), (62, 1)] }],
  [{ coefficient := 2, powers := [(9, 2), (25, 1), (44, 1), (62, 1)] }, { coefficient := -2, powers := [(9, 1), (25, 1), (44, 1), (48, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (44, 1), (62, 2)] }, { coefficient := 1, powers := [(9, 1), (51, 1), (62, 2)] }, { coefficient := 1, powers := [(9, 1), (56, 1), (62, 2)] }],
  [{ coefficient := -1, powers := [(9, 1), (56, 1), (62, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(21, 1), (61, 1), (62, 1), (68, 1)] }],
  [{ coefficient := -2, powers := [(9, 1), (20, 1), (26, 1), (51, 1), (53, 1), (62, 1), (68, 1)] }, { coefficient := 2, powers := [(9, 1), (20, 1), (28, 1), (51, 1), (62, 1), (68, 1)] }, { coefficient := 2, powers := [(9, 1), (25, 1), (26, 1), (44, 1), (53, 1), (62, 1), (68, 1)] }, { coefficient := 1, powers := [(9, 1), (25, 1), (26, 1), (51, 1), (53, 1), (62, 1), (68, 1)] }, { coefficient := 1, powers := [(9, 1), (25, 1), (26, 1), (53, 1), (56, 1), (62, 1), (68, 1)] }, { coefficient := -2, powers := [(9, 1), (25, 1), (28, 1), (44, 1), (62, 1), (68, 1)] }, { coefficient := -1, powers := [(9, 1), (25, 1), (28, 1), (51, 1), (62, 1), (68, 1)] }, { coefficient := -1, powers := [(9, 1), (25, 1), (28, 1), (56, 1), (62, 1), (68, 1)] }, { coefficient := 1, powers := [(20, 1), (26, 1), (50, 1), (53, 1), (62, 1), (68, 1)] }, { coefficient := -1, powers := [(20, 1), (28, 1), (50, 1), (62, 1), (68, 1)] }],
  [{ coefficient := 2, powers := [(9, 1), (20, 1), (23, 1), (51, 1), (53, 1), (62, 1), (68, 1)] }, { coefficient := -2, powers := [(9, 1), (23, 1), (25, 1), (44, 1), (53, 1), (62, 1), (68, 1)] }, { coefficient := -1, powers := [(9, 1), (23, 1), (25, 1), (51, 1), (53, 1), (62, 1), (68, 1)] }, { coefficient := -1, powers := [(9, 1), (23, 1), (25, 1), (53, 1), (56, 1), (62, 1), (68, 1)] }, { coefficient := -1, powers := [(20, 1), (23, 1), (50, 1), (53, 1), (62, 1), (68, 1)] }],
  [{ coefficient := -2, powers := [(9, 1), (20, 1), (23, 1), (51, 1), (62, 1), (68, 1)] }, { coefficient := 1, powers := [(9, 1), (20, 1), (62, 1), (68, 1)] }, { coefficient := 2, powers := [(9, 1), (23, 1), (25, 1), (44, 1), (62, 1), (68, 1)] }, { coefficient := 1, powers := [(9, 1), (23, 1), (25, 1), (51, 1), (62, 1), (68, 1)] }, { coefficient := 1, powers := [(9, 1), (23, 1), (25, 1), (56, 1), (62, 1), (68, 1)] }, { coefficient := -1, powers := [(9, 1), (25, 1), (62, 1), (68, 1)] }, { coefficient := 1, powers := [(20, 1), (23, 1), (50, 1), (62, 1), (68, 1)] }],
  [{ coefficient := -1, powers := [(10, 1), (62, 1)] }, { coefficient := 1, powers := [(14, 1), (62, 1)] }],
  [{ coefficient := -2, powers := [(7, 1), (9, 2), (30, 1), (44, 1), (62, 1)] }, { coefficient := -2, powers := [(9, 2), (10, 1), (25, 1), (44, 1), (62, 1)] }, { coefficient := 2, powers := [(9, 1), (10, 1), (25, 1), (44, 1), (48, 1), (62, 1)] }],
  [{ coefficient := -2, powers := [(7, 1), (9, 1), (13, 1), (30, 1), (44, 1), (62, 1)] }, { coefficient := -2, powers := [(9, 1), (10, 1), (13, 1), (25, 1), (44, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(9, 1), (20, 1), (28, 1), (62, 1), (68, 1)] }, { coefficient := 1, powers := [(9, 1), (25, 1), (28, 1), (62, 1), (68, 1)] }, { coefficient := -1, powers := [(9, 1), (25, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(9, 1), (14, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (9, 1), (33, 1), (62, 1)] }, { coefficient := 2, powers := [(9, 1), (10, 1), (20, 1), (62, 1)] }],
  [{ coefficient := 2, powers := [(7, 1), (9, 1), (30, 1), (44, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (62, 1)] }],
  [{ coefficient := 2, powers := [(7, 1), (9, 2), (30, 1), (41, 1), (44, 1), (62, 1)] }, { coefficient := 2, powers := [(7, 1), (9, 1), (13, 1), (30, 1), (44, 1), (48, 1), (62, 1)] }, { coefficient := -2, powers := [(7, 1), (9, 1), (30, 1), (35, 1), (44, 1), (58, 1), (62, 1)] }, { coefficient := -2, powers := [(7, 1), (9, 1), (30, 1), (38, 1), (44, 1), (55, 1), (62, 1)] }, { coefficient := -2, powers := [(7, 1), (9, 1), (30, 1), (41, 1), (44, 1), (48, 1), (62, 1)] }, { coefficient := 1, powers := [(7, 1), (9, 1), (33, 1), (36, 1), (59, 1), (62, 1)] }, { coefficient := 1, powers := [(7, 1), (9, 1), (33, 1), (39, 1), (56, 1), (62, 1)] }, { coefficient := 1, powers := [(7, 1), (9, 1), (33, 1), (44, 1), (51, 1), (62, 1)] }, { coefficient := 2, powers := [(9, 2), (10, 1), (25, 1), (41, 1), (44, 1), (62, 1)] }, { coefficient := 2, powers := [(9, 1), (10, 1), (13, 1), (25, 1), (44, 1), (48, 1), (62, 1)] }, { coefficient := -2, powers := [(9, 1), (10, 1), (20, 1), (36, 1), (59, 1), (62, 1)] }, { coefficient := -2, powers := [(9, 1), (10, 1), (20, 1), (39, 1), (56, 1), (62, 1)] }, { coefficient := -2, powers := [(9, 1), (10, 1), (20, 1), (44, 1), (51, 1), (62, 1)] }, { coefficient := -2, powers := [(9, 1), (10, 1), (25, 1), (41, 1), (44, 1), (48, 1), (62, 1)] }],
  [{ coefficient := -2, powers := [(3, 1), (9, 2), (32, 1), (44, 1), (51, 1), (62, 1)] }, { coefficient := 2, powers := [(3, 1), (9, 1), (32, 1), (44, 1), (48, 1), (51, 1), (62, 1)] }, { coefficient := -2, powers := [(6, 1), (9, 1), (13, 1), (29, 1), (44, 1), (51, 1), (62, 1)] }, { coefficient := -2, powers := [(9, 2), (13, 1), (18, 1), (44, 1), (51, 1), (62, 1)] }, { coefficient := -2, powers := [(9, 2), (13, 1), (23, 1), (44, 1), (51, 1), (62, 1)] }, { coefficient := -2, powers := [(9, 1), (13, 1), (23, 1), (38, 1), (44, 1), (51, 1), (62, 1)] }, { coefficient := -2, powers := [(9, 1), (13, 1), (29, 1), (35, 1), (44, 1), (51, 1), (62, 1)] }, { coefficient := -1, powers := [(9, 1), (36, 1), (59, 1), (62, 1)] }, { coefficient := -1, powers := [(9, 1), (38, 1), (44, 1), (56, 1), (62, 2)] }, { coefficient := -1, powers := [(9, 1), (38, 1), (51, 1), (56, 1), (62, 2)] }, { coefficient := -1, powers := [(9, 1), (38, 1), (56, 2), (62, 2)] }, { coefficient := 1, powers := [(9, 1), (39, 1), (55, 1), (56, 1), (62, 1), (64, 1)] }, { coefficient := -1, powers := [(9, 1), (39, 1), (56, 1), (62, 1)] }, { coefficient := 1, powers := [(9, 1), (43, 1), (56, 1), (62, 1), (64, 1)] }, { coefficient := -1, powers := [(9, 1), (44, 1), (50, 1), (62, 2)] }, { coefficient := -1, powers := [(9, 1), (44, 1), (51, 1), (62, 1)] }, { coefficient := -1, powers := [(9, 1), (50, 1), (51, 1), (62, 2)] }, { coefficient := -1, powers := [(9, 1), (50, 1), (56, 1), (62, 2)] }],
  [{ coefficient := 1, powers := [(21, 1), (24, 1), (50, 1), (62, 1), (68, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (9, 1), (33, 1), (44, 1), (62, 1)] }, { coefficient := -1, powers := [(7, 1), (9, 1), (33, 1), (51, 1), (62, 1)] }, { coefficient := -1, powers := [(7, 1), (9, 1), (33, 1), (56, 1), (62, 1)] }, { coefficient := -2, powers := [(9, 1), (14, 1), (20, 1), (26, 1), (51, 1), (53, 1), (62, 1), (68, 1)] }, { coefficient := 2, powers := [(9, 1), (14, 1), (25, 1), (26, 1), (44, 1), (53, 1), (62, 1), (68, 1)] }, { coefficient := 1, powers := [(9, 1), (14, 1), (25, 1), (26, 1), (51, 1), (53, 1), (62, 1), (68, 1)] }, { coefficient := 1, powers := [(9, 1), (14, 1), (25, 1), (26, 1), (53, 1), (56, 1), (62, 1), (68, 1)] }, { coefficient := -1, powers := [(9, 1), (14, 1), (25, 1), (44, 1), (62, 1)] }, { coefficient := -1, powers := [(9, 1), (14, 1), (25, 1), (51, 1), (62, 1)] }, { coefficient := -1, powers := [(9, 1), (14, 1), (25, 1), (56, 1), (62, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1), (26, 1), (50, 1), (53, 1), (62, 1), (68, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(4, 1), (9, 1), (30, 1), (56, 1), (62, 1)] }, { coefficient := 1, powers := [(9, 1), (10, 1), (20, 1), (56, 1), (62, 1)] }],
  [{ coefficient := 2, powers := [(3, 1), (7, 1), (9, 1), (23, 1), (30, 1), (44, 1), (58, 1), (62, 1)] }, { coefficient := -2, powers := [(6, 1), (7, 1), (9, 1), (29, 1), (30, 1), (41, 1), (44, 1), (62, 1)] }, { coefficient := 2, powers := [(7, 1), (9, 1), (13, 1), (23, 1), (30, 1), (38, 1), (44, 1), (62, 1)] }, { coefficient := 1, powers := [(9, 1), (16, 1), (21, 1), (28, 1), (61, 1), (62, 1), (68, 1)] }, { coefficient := -1, powers := [(11, 1), (21, 1), (28, 1), (61, 1), (62, 1), (68, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (9, 1), (20, 1), (59, 1), (62, 1)] }, { coefficient := -1, powers := [(7, 1), (9, 1), (25, 1), (59, 1), (62, 1)] }, { coefficient := 2, powers := [(9, 1), (10, 1), (20, 1), (39, 1), (62, 1)] }, { coefficient := 2, powers := [(9, 1), (10, 1), (20, 1), (44, 1), (62, 1)] }, { coefficient := 2, powers := [(9, 1), (10, 1), (20, 1), (51, 1), (62, 1)] }, { coefficient := 1, powers := [(9, 1), (10, 1), (20, 1), (56, 1), (62, 1)] }, { coefficient := -1, powers := [(9, 1), (10, 1), (25, 1), (56, 1), (62, 1)] }, { coefficient := -1, powers := [(9, 1), (14, 1), (20, 1), (51, 1), (62, 1)] }, { coefficient := -1, powers := [(9, 1), (14, 1), (25, 1), (39, 1), (62, 1)] }, { coefficient := 1, powers := [(9, 1), (14, 1), (25, 1), (44, 1), (62, 1)] }, { coefficient := 1, powers := [(9, 1), (14, 1), (25, 1), (56, 1), (62, 1)] }, { coefficient := -1, powers := [(9, 1), (62, 1)] }, { coefficient := -1, powers := [(10, 1), (20, 1), (50, 1), (62, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1), (50, 1), (62, 1)] }, { coefficient := -1, powers := [(38, 1), (62, 1)] }]
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
    ¬ ∀ index : Fin 37,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component39.SelectedLeafB1_6_6_7.selectedHasNoCommonZero

end Krenn.Component39.SelectedLeafB1_6_6_7
