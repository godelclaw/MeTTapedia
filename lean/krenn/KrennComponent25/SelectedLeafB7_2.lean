import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component25.SelectedLeafB7_2

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "90c9c1a59586ec0d435d1fd89a66e9472f2ebe65860640133186fe23e7ea0d30"
def certificateSHA256 : String := "38fe02fce2ad354f806ce770c639fac6eb712bcbc3b1e824323cc2d192b98f62"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 68 → Fin 662 := ![
  0,
  1,
  2,
  5,
  7,
  9,
  10,
  12,
  14,
  15,
  16,
  17,
  21,
  22,
  142,
  143,
  145,
  146,
  148,
  152,
  162,
  168,
  169,
  173,
  188,
  293,
  294,
  297,
  300,
  311,
  312,
  324,
  326,
  388,
  405,
  427,
  429,
  433,
  435,
  436,
  438,
  440,
  449,
  450,
  460,
  475,
  478,
  513,
  519,
  552,
  578,
  579,
  600,
  601,
  606,
  607,
  613,
  628,
  643,
  647,
  648,
  653,
  655,
  656,
  657,
  658,
  659,
  661
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 68 → SparsePoly (Fin 65) := ![
  [{ coefficient := 1, powers := [(8, 1), (30, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(30, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (54, 1)] }, { coefficient := 1, powers := [(18, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (43, 1)] }, { coefficient := 1, powers := [(10, 1), (25, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (48, 1)] }, { coefficient := 1, powers := [(10, 1), (25, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (50, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (54, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (29, 1)] }, { coefficient := 1, powers := [(29, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (18, 1)] }, { coefficient := 1, powers := [(16, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (54, 1)] }, { coefficient := 1, powers := [(29, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (57, 1)] }, { coefficient := 1, powers := [(29, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (40, 1)] }, { coefficient := 1, powers := [(29, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (29, 1), (59, 1)] }, { coefficient := 1, powers := [(29, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (48, 1)] }, { coefficient := 1, powers := [(19, 1), (43, 1)] }, { coefficient := 1, powers := [(24, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (50, 1)] }, { coefficient := 1, powers := [(18, 1), (50, 1)] }, { coefficient := 1, powers := [(24, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (49, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1), (49, 1)] }, { coefficient := 1, powers := [(14, 1), (25, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (60, 1)] }, { coefficient := 1, powers := [(12, 1), (57, 1)] }, { coefficient := 1, powers := [(17, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (52, 1)] }, { coefficient := 1, powers := [(23, 1), (56, 1)] }, { coefficient := 1, powers := [(28, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (57, 1)] }, { coefficient := 1, powers := [(29, 1), (48, 1)] }, { coefficient := 1, powers := [(35, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (36, 1), (58, 1)] }, { coefficient := 1, powers := [(1, 1), (39, 1), (55, 1)] }, { coefficient := 1, powers := [(1, 1), (42, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (38, 1), (60, 1)] }, { coefficient := 1, powers := [(1, 1), (41, 1), (57, 1)] }, { coefficient := 1, powers := [(1, 1), (48, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (18, 1), (56, 1)] }, { coefficient := 1, powers := [(12, 1)] }, { coefficient := 1, powers := [(16, 1), (18, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (24, 1), (40, 1)] }, { coefficient := 1, powers := [(16, 1), (24, 1), (45, 1)] }, { coefficient := 1, powers := [(16, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (45, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1), (40, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1), (45, 1)] }, { coefficient := 1, powers := [(16, 1), (28, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (47, 1)] }, { coefficient := 1, powers := [(5, 1), (27, 1), (59, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (52, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1), (52, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1), (56, 1)] }, { coefficient := 1, powers := [(16, 1), (28, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1)] }, { coefficient := 1, powers := [(12, 1), (29, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (35, 1)] }, { coefficient := 1, powers := [(22, 1), (43, 1)] }, { coefficient := 1, powers := [(27, 1), (43, 1)] }, { coefficient := 1, powers := [(35, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (59, 1)] }, { coefficient := 1, powers := [(16, 1), (19, 1), (52, 1)] }, { coefficient := 1, powers := [(16, 1), (19, 1), (56, 1)] }, { coefficient := 1, powers := [(16, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (32, 1)] }, { coefficient := 1, powers := [(22, 1), (50, 1)] }, { coefficient := 1, powers := [(27, 1), (50, 1)] }, { coefficient := 1, powers := [(32, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (40, 1)] }, { coefficient := 1, powers := [(16, 1), (45, 1)] }, { coefficient := 1, powers := [(16, 1), (52, 1)] }, { coefficient := 1, powers := [(16, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (54, 1)] }, { coefficient := 1, powers := [(29, 1), (41, 1)] }, { coefficient := 1, powers := [(29, 1), (47, 1), (50, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1), (49, 1)] }, { coefficient := 1, powers := [(6, 1), (30, 1), (45, 1)] }, { coefficient := 1, powers := [(9, 1), (24, 1), (45, 1)] }, { coefficient := 1, powers := [(49, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (36, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (59, 1)] }, { coefficient := 1, powers := [(8, 1), (23, 1), (59, 1)] }, { coefficient := 1, powers := [(16, 1), (29, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (24, 1), (60, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (48, 1)] }, { coefficient := 1, powers := [(17, 1), (19, 1), (50, 1)] }, { coefficient := 1, powers := [(17, 1), (24, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (30, 1), (57, 1)] }, { coefficient := 1, powers := [(8, 1), (30, 1), (48, 1)] }, { coefficient := 1, powers := [(11, 1), (19, 1), (57, 1)] }, { coefficient := 1, powers := [(17, 1), (30, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (19, 1), (56, 1)] }, { coefficient := 1, powers := [(12, 1), (47, 1)] }, { coefficient := 1, powers := [(16, 1), (19, 1), (53, 1)] }, { coefficient := 1, powers := [(16, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1)] }, { coefficient := 1, powers := [(6, 1), (59, 1)] }, { coefficient := 1, powers := [(24, 1), (40, 1)] }, { coefficient := 1, powers := [(24, 1), (45, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (52, 1)] }, { coefficient := 1, powers := [(3, 1), (59, 1)] }, { coefficient := 1, powers := [(18, 1), (52, 1)] }, { coefficient := 1, powers := [(18, 1), (56, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1)] }, { coefficient := 1, powers := [(3, 1), (33, 1)] }, { coefficient := 1, powers := [(13, 1), (18, 1)] }, { coefficient := 1, powers := [(18, 1), (55, 1)] }, { coefficient := 1, powers := [(24, 1), (42, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (49, 1)] }, { coefficient := 1, powers := [(6, 1), (30, 1)] }, { coefficient := 1, powers := [(9, 1), (24, 1)] }, { coefficient := 1, powers := [(18, 1), (49, 1)] }, { coefficient := 1, powers := [(24, 1), (39, 1)] }, { coefficient := 1, powers := [(30, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (36, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1)] }, { coefficient := 1, powers := [(3, 1), (24, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (18, 1), (59, 1)] }, { coefficient := 1, powers := [(18, 1)] }, { coefficient := 1, powers := [(24, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (36, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (43, 1), (50, 1)] }, { coefficient := 1, powers := [(3, 1), (24, 1), (60, 1)] }, { coefficient := 1, powers := [(6, 1), (18, 1), (60, 1)] }, { coefficient := 1, powers := [(18, 1), (43, 1), (50, 1)] }, { coefficient := 1, powers := [(24, 1), (43, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1), (49, 1)] }, { coefficient := 1, powers := [(6, 1), (30, 1), (44, 1)] }, { coefficient := 1, powers := [(6, 1), (58, 1)] }, { coefficient := 1, powers := [(9, 1), (24, 1), (44, 1)] }, { coefficient := 1, powers := [(9, 1), (55, 1)] }, { coefficient := 1, powers := [(13, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (29, 1), (60, 1)] }, { coefficient := 1, powers := [(3, 1), (32, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (35, 1), (54, 1)] }, { coefficient := 1, powers := [(22, 1), (43, 1), (54, 1)] }, { coefficient := 1, powers := [(22, 1), (50, 1), (57, 1)] }, { coefficient := 1, powers := [(29, 1), (43, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (37, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (40, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (45, 1), (52, 1)] }, { coefficient := 1, powers := [(40, 1)] }, { coefficient := 1, powers := [(45, 1)] }, { coefficient := 1, powers := [(52, 1)] }, { coefficient := 1, powers := [(56, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (37, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (40, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (45, 1), (52, 1)] }, { coefficient := 1, powers := [(16, 1), (28, 1), (40, 1)] }, { coefficient := 1, powers := [(16, 1), (28, 1), (45, 1)] }, { coefficient := 1, powers := [(16, 1), (28, 1), (52, 1)] }, { coefficient := 1, powers := [(16, 1), (28, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (41, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (47, 1), (53, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (56, 1)] }, { coefficient := 1, powers := [(12, 1), (23, 1), (56, 1)] }, { coefficient := 1, powers := [(12, 1), (28, 1), (47, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1), (53, 1)] }, { coefficient := 1, powers := [(16, 1), (28, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (36, 1), (58, 1)] }, { coefficient := 1, powers := [(0, 1), (39, 1), (55, 1)] }, { coefficient := 1, powers := [(0, 1), (42, 1), (49, 1)] }, { coefficient := 1, powers := [(3, 1), (24, 1), (58, 1)] }, { coefficient := 1, powers := [(3, 1), (30, 1), (55, 1)] }, { coefficient := 1, powers := [(3, 1), (33, 1), (49, 1)] }, { coefficient := 1, powers := [(6, 1), (18, 1), (58, 1)] }, { coefficient := 1, powers := [(6, 1), (30, 1), (42, 1)] }, { coefficient := 1, powers := [(6, 1), (33, 1), (39, 1)] }, { coefficient := 1, powers := [(9, 1), (18, 1), (55, 1)] }, { coefficient := 1, powers := [(9, 1), (24, 1), (42, 1)] }, { coefficient := 1, powers := [(9, 1), (33, 1), (36, 1)] }, { coefficient := 1, powers := [(13, 1), (18, 1), (49, 1)] }, { coefficient := 1, powers := [(13, 1), (24, 1), (39, 1)] }, { coefficient := 1, powers := [(13, 1), (30, 1), (36, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (41, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (48, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (23, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (48, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(12, 1), (23, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1), (29, 1), (48, 1)] }, { coefficient := 1, powers := [(12, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(17, 1), (23, 1), (54, 1)] }, { coefficient := 1, powers := [(17, 1), (29, 1), (41, 1)] }, { coefficient := 1, powers := [(17, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (61, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(39, 1)] }],
  [{ coefficient := 1, powers := [(41, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 68 → SparsePoly (Fin 65) := ![
  [{ coefficient := -1, powers := [(0, 1), (3, 1), (23, 1), (45, 1), (55, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (32, 1), (36, 1), (48, 1), (52, 1)] }, { coefficient := 1, powers := [(3, 1), (24, 1), (32, 1), (48, 1), (52, 1)] }, { coefficient := 1, powers := [(6, 1), (18, 1), (32, 1), (48, 1), (52, 1)] }, { coefficient := -1, powers := [(6, 1), (32, 1), (48, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (5, 1), (32, 1), (33, 1), (36, 1), (45, 1)] }, { coefficient := 1, powers := [(0, 1), (12, 1), (23, 1), (33, 1), (36, 1), (45, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (12, 1), (22, 1), (24, 1), (25, 1), (38, 1), (45, 1), (58, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 1), (12, 1), (24, 1), (25, 1), (27, 1), (38, 1), (45, 1), (58, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (6, 1), (12, 1), (24, 1), (25, 1), (29, 1), (45, 1), (58, 1), (62, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (25, 1), (29, 1), (52, 1), (62, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (25, 1), (29, 1), (56, 1), (62, 1)] }],
  [{ coefficient := -2, powers := [(0, 2), (20, 1), (42, 1), (45, 1), (62, 1)] }, { coefficient := -2, powers := [(0, 1), (13, 1), (18, 1), (20, 1), (45, 1), (62, 1)] }, { coefficient := 1, powers := [(0, 1), (13, 1), (20, 1), (62, 1)] }, { coefficient := 1, powers := [(0, 1), (18, 1), (20, 1), (44, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 1), (18, 1), (20, 1), (45, 1), (55, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 1), (20, 1), (24, 1), (42, 1), (45, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 1), (20, 1), (33, 1), (36, 1), (45, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 1), (20, 1), (42, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (5, 1), (20, 1), (24, 1), (29, 1), (43, 1), (45, 1), (58, 1), (62, 1)] }, { coefficient := 1, powers := [(0, 1), (8, 1), (20, 1), (22, 1), (24, 1), (45, 1), (48, 1), (58, 1), (62, 1)] }, { coefficient := 1, powers := [(0, 1), (8, 1), (20, 1), (24, 1), (27, 1), (45, 1), (48, 1), (58, 1), (62, 1)] }, { coefficient := 1, powers := [(17, 1), (19, 1), (20, 1), (29, 1), (52, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (2, 1), (3, 1), (20, 1), (24, 1), (45, 1), (48, 1), (58, 1), (62, 1)] }, { coefficient := 1, powers := [(0, 1), (2, 1), (3, 1), (20, 1), (30, 1), (45, 1), (48, 1), (55, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 1), (2, 1), (6, 1), (20, 1), (24, 1), (45, 1), (48, 1), (58, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 1), (2, 1), (9, 1), (20, 1), (33, 1), (36, 1), (45, 1), (48, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 1), (2, 1), (20, 1), (24, 1), (36, 1), (45, 1), (48, 1), (58, 1), (62, 1)] }, { coefficient := 1, powers := [(0, 1), (3, 1), (5, 1), (20, 1), (30, 1), (35, 1), (45, 1), (55, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 1), (3, 1), (17, 1), (20, 1), (23, 1), (24, 1), (45, 1), (58, 1), (62, 1)] }, { coefficient := 1, powers := [(0, 1), (5, 1), (9, 1), (20, 1), (33, 1), (35, 1), (36, 1), (45, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 1), (5, 1), (20, 1), (35, 1), (52, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 1), (9, 1), (17, 1), (20, 1), (23, 1), (33, 1), (36, 1), (45, 1), (62, 1)] }, { coefficient := 1, powers := [(0, 1), (17, 1), (20, 1), (23, 1), (52, 1), (62, 1)] }, { coefficient := 1, powers := [(2, 1), (6, 1), (20, 1), (48, 1), (59, 1), (62, 1)] }, { coefficient := -1, powers := [(2, 1), (18, 1), (20, 1), (48, 1), (52, 1), (62, 1)] }, { coefficient := 1, powers := [(2, 1), (20, 1), (24, 1), (48, 1), (52, 1), (62, 1)] }, { coefficient := 1, powers := [(2, 1), (20, 1), (24, 1), (48, 1), (56, 1), (62, 1)] }, { coefficient := 1, powers := [(5, 1), (6, 1), (20, 1), (35, 1), (59, 1), (62, 1)] }, { coefficient := -1, powers := [(5, 1), (20, 1), (24, 1), (35, 1), (56, 1), (62, 1)] }, { coefficient := -1, powers := [(17, 1), (20, 1), (23, 1), (24, 1), (52, 1), (62, 1)] }, { coefficient := -1, powers := [(17, 1), (20, 1), (24, 1), (28, 1), (47, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (3, 1), (22, 1), (24, 1), (45, 1), (48, 1), (58, 1)] }, { coefficient := 1, powers := [(0, 1), (6, 1), (22, 1), (24, 1), (45, 1), (48, 1), (58, 1)] }, { coefficient := 1, powers := [(0, 1), (9, 1), (22, 1), (33, 1), (36, 1), (45, 1), (48, 1)] }, { coefficient := 1, powers := [(0, 1), (22, 1), (24, 1), (36, 1), (45, 1), (48, 1), (58, 1)] }, { coefficient := -1, powers := [(0, 1), (22, 1), (48, 1), (52, 1)] }, { coefficient := -1, powers := [(22, 1), (24, 1), (48, 1), (52, 1)] }, { coefficient := -1, powers := [(22, 1), (24, 1), (48, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (23, 1), (24, 2), (36, 1), (45, 1), (53, 1), (58, 1)] }, { coefficient := 1, powers := [(6, 1), (19, 1), (32, 1), (52, 1)] }, { coefficient := 1, powers := [(6, 1), (19, 1), (32, 1), (56, 1)] }, { coefficient := 1, powers := [(6, 1), (32, 1), (47, 1)] }, { coefficient := -2, powers := [(19, 1), (24, 1), (28, 1), (53, 1)] }, { coefficient := 2, powers := [(23, 1), (24, 2), (52, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (12, 1), (23, 1), (24, 1), (36, 1), (45, 1), (56, 1), (58, 1)] }, { coefficient := -1, powers := [(5, 1), (32, 1), (52, 1)] }, { coefficient := -2, powers := [(12, 1), (23, 1), (24, 1), (52, 1), (56, 1)] }, { coefficient := 1, powers := [(12, 1), (23, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (3, 1), (11, 1), (32, 1), (45, 1), (55, 1)] }, { coefficient := -1, powers := [(2, 1), (24, 1), (45, 1), (53, 1)] }, { coefficient := -1, powers := [(12, 1), (22, 1), (52, 1)] }, { coefficient := -1, powers := [(12, 1), (24, 1), (28, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (3, 2), (16, 1), (30, 1), (45, 1), (55, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (3, 1), (16, 1), (52, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (3, 1), (17, 1), (24, 1), (45, 1), (50, 1), (58, 1)] }, { coefficient := 1, powers := [(0, 1), (3, 1), (17, 1), (30, 1), (45, 1), (50, 1), (55, 1)] }, { coefficient := 1, powers := [(0, 1), (9, 1), (17, 1), (33, 1), (36, 1), (45, 1), (50, 1)] }, { coefficient := 1, powers := [(3, 1), (16, 1), (24, 1), (56, 1), (60, 1)] }, { coefficient := 1, powers := [(6, 1), (16, 1), (60, 1)] }, { coefficient := 1, powers := [(6, 1), (17, 1), (50, 1), (59, 1)] }, { coefficient := 1, powers := [(17, 1), (18, 1), (50, 1), (52, 1)] }, { coefficient := -1, powers := [(17, 1), (24, 1), (50, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (2, 1), (3, 1), (45, 1), (55, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (3, 1), (17, 1), (32, 1), (45, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (48, 1), (52, 1)] }, { coefficient := -1, powers := [(5, 1), (35, 1), (52, 1)] }, { coefficient := 1, powers := [(17, 1), (23, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (12, 1), (22, 1), (24, 1), (38, 1), (45, 1), (58, 1), (62, 1)] }, { coefficient := 1, powers := [(0, 1), (12, 1), (24, 1), (27, 1), (38, 1), (45, 1), (58, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (6, 1), (12, 1), (24, 1), (29, 1), (45, 1), (58, 1), (62, 1)] }, { coefficient := -1, powers := [(12, 1), (24, 1), (29, 1), (52, 1), (62, 1)] }, { coefficient := -1, powers := [(12, 1), (24, 1), (29, 1), (56, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (5, 1), (24, 1), (29, 1), (43, 1), (45, 1), (58, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 1), (8, 1), (22, 1), (24, 1), (45, 1), (48, 1), (58, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 1), (8, 1), (24, 1), (27, 1), (45, 1), (48, 1), (58, 1), (62, 1)] }, { coefficient := -1, powers := [(17, 1), (19, 1), (29, 1), (52, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (2, 1), (3, 1), (24, 1), (45, 1), (48, 1), (58, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 1), (2, 1), (3, 1), (30, 1), (45, 1), (48, 1), (55, 1), (62, 1)] }, { coefficient := 1, powers := [(0, 1), (2, 1), (6, 1), (24, 1), (45, 1), (48, 1), (58, 1), (62, 1)] }, { coefficient := 1, powers := [(0, 1), (2, 1), (9, 1), (33, 1), (36, 1), (45, 1), (48, 1), (62, 1)] }, { coefficient := 1, powers := [(0, 1), (2, 1), (24, 1), (36, 1), (45, 1), (48, 1), (58, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 1), (3, 1), (5, 1), (30, 1), (35, 1), (45, 1), (55, 1), (62, 1)] }, { coefficient := 1, powers := [(0, 1), (3, 1), (17, 1), (23, 1), (24, 1), (45, 1), (58, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 1), (5, 1), (9, 1), (33, 1), (35, 1), (36, 1), (45, 1), (62, 1)] }, { coefficient := 1, powers := [(0, 1), (5, 1), (35, 1), (52, 1), (62, 1)] }, { coefficient := 1, powers := [(0, 1), (9, 1), (17, 1), (23, 1), (33, 1), (36, 1), (45, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 1), (17, 1), (23, 1), (52, 1), (62, 1)] }, { coefficient := -1, powers := [(2, 1), (6, 1), (48, 1), (59, 1), (62, 1)] }, { coefficient := 1, powers := [(2, 1), (18, 1), (48, 1), (52, 1), (62, 1)] }, { coefficient := -1, powers := [(2, 1), (24, 1), (48, 1), (52, 1), (62, 1)] }, { coefficient := -1, powers := [(2, 1), (24, 1), (48, 1), (56, 1), (62, 1)] }, { coefficient := -1, powers := [(5, 1), (6, 1), (35, 1), (59, 1), (62, 1)] }, { coefficient := 1, powers := [(5, 1), (24, 1), (35, 1), (56, 1), (62, 1)] }, { coefficient := 1, powers := [(17, 1), (23, 1), (24, 1), (52, 1), (62, 1)] }, { coefficient := 1, powers := [(17, 1), (24, 1), (28, 1), (47, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (5, 1), (33, 1), (36, 1), (45, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (12, 1), (33, 1), (36, 1), (45, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (23, 1), (24, 1), (36, 1), (45, 1), (53, 1), (57, 1), (58, 1)] }, { coefficient := -1, powers := [(22, 1), (52, 1), (63, 1)] }, { coefficient := -1, powers := [(22, 1), (56, 1), (63, 1)] }, { coefficient := -2, powers := [(23, 1), (24, 1), (52, 1), (53, 1), (57, 1)] }, { coefficient := -1, powers := [(27, 1), (52, 1), (63, 1)] }, { coefficient := -1, powers := [(27, 1), (56, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (5, 1), (24, 1), (43, 1), (45, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (5, 1), (24, 1), (45, 1), (50, 1), (58, 1)] }, { coefficient := 1, powers := [(12, 1), (19, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (3, 2), (16, 1), (19, 1), (30, 1), (45, 1), (55, 1), (60, 1)] }, { coefficient := -1, powers := [(0, 1), (3, 1), (16, 1), (19, 1), (52, 1), (60, 1)] }, { coefficient := -1, powers := [(3, 1), (16, 1), (19, 1), (24, 1), (56, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (3, 1), (5, 1), (30, 1), (45, 1), (55, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (5, 1), (52, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (24, 1), (56, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (29, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (29, 1), (43, 1), (52, 1), (59, 1)] }],
  [{ coefficient := 2, powers := [(0, 2), (42, 1), (45, 1), (62, 1)] }, { coefficient := 2, powers := [(0, 1), (13, 1), (18, 1), (45, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 1), (13, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 1), (18, 1), (44, 1), (62, 1)] }, { coefficient := 1, powers := [(0, 1), (18, 1), (45, 1), (55, 1), (62, 1)] }, { coefficient := 1, powers := [(0, 1), (24, 1), (42, 1), (45, 1), (62, 1)] }, { coefficient := 1, powers := [(0, 1), (33, 1), (36, 1), (45, 1), (62, 1)] }, { coefficient := 1, powers := [(0, 1), (42, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (3, 1), (23, 1), (24, 1), (45, 1), (58, 1)] }, { coefficient := -1, powers := [(0, 1), (9, 1), (23, 1), (33, 1), (36, 1), (45, 1)] }, { coefficient := -1, powers := [(18, 1), (23, 1), (52, 1)] }, { coefficient := 1, powers := [(23, 1), (24, 1), (56, 1)] }],
  [{ coefficient := -2, powers := [(12, 1), (24, 1), (57, 1)] }, { coefficient := -1, powers := [(17, 1), (24, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (3, 1), (12, 1), (30, 1), (45, 1), (55, 1)] }, { coefficient := -1, powers := [(0, 1), (9, 1), (12, 1), (33, 1), (36, 1), (45, 1)] }, { coefficient := 1, powers := [(0, 1), (12, 1), (24, 1), (36, 1), (45, 1), (58, 1)] }, { coefficient := -1, powers := [(6, 1), (12, 1), (59, 1)] }, { coefficient := -1, powers := [(12, 1), (18, 1), (52, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [(0, 2), (45, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (2, 1), (3, 1), (24, 1), (45, 1), (58, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 1), (2, 1), (9, 1), (33, 1), (36, 1), (45, 1), (62, 1)] }, { coefficient := -1, powers := [(2, 1), (18, 1), (52, 1), (62, 1)] }, { coefficient := 1, powers := [(2, 1), (24, 1), (56, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (23, 1), (24, 1), (36, 1), (45, 1), (57, 1), (58, 1)] }, { coefficient := 2, powers := [(23, 1), (24, 1), (52, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [(22, 1), (63, 1)] }, { coefficient := -1, powers := [(27, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(18, 1), (63, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (53, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [(24, 1), (53, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (3, 1), (24, 1), (45, 1), (48, 1), (58, 1)] }, { coefficient := -1, powers := [(0, 1), (6, 1), (24, 1), (45, 1), (48, 1), (58, 1)] }, { coefficient := -1, powers := [(0, 1), (9, 1), (33, 1), (36, 1), (45, 1), (48, 1)] }, { coefficient := -1, powers := [(0, 1), (24, 1), (36, 1), (45, 1), (48, 1), (58, 1)] }, { coefficient := 1, powers := [(0, 1), (48, 1), (52, 1)] }, { coefficient := 1, powers := [(24, 1), (48, 1), (52, 1)] }, { coefficient := 1, powers := [(24, 1), (48, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (12, 1), (24, 1), (38, 1), (45, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (3, 2), (29, 1), (30, 1), (45, 1), (55, 1), (60, 1)] }, { coefficient := -1, powers := [(0, 1), (3, 1), (29, 1), (52, 1), (60, 1)] }, { coefficient := -1, powers := [(3, 1), (24, 1), (29, 1), (56, 1), (60, 1)] }, { coefficient := -1, powers := [(6, 1), (32, 1), (57, 1)] }, { coefficient := 1, powers := [(24, 1), (27, 1), (53, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (8, 1), (24, 1), (45, 1), (48, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (3, 2), (19, 1), (29, 1), (30, 1), (45, 1), (55, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (3, 1), (19, 1), (29, 1), (52, 1), (60, 1)] }, { coefficient := -1, powers := [(0, 1), (24, 1), (28, 1), (63, 1)] }, { coefficient := 1, powers := [(3, 1), (19, 1), (24, 1), (29, 1), (56, 1), (60, 1)] }, { coefficient := -1, powers := [(18, 1), (24, 1), (28, 1), (63, 1)] }, { coefficient := 1, powers := [(18, 1), (27, 1), (63, 1)] }, { coefficient := -1, powers := [(19, 1), (24, 1), (27, 1), (53, 1), (57, 1)] }, { coefficient := 1, powers := [(22, 1), (24, 1), (63, 1)] }, { coefficient := 1, powers := [(24, 1), (27, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (3, 1), (17, 1), (24, 1), (45, 1), (58, 1)] }, { coefficient := -1, powers := [(0, 1), (3, 1), (17, 1), (30, 1), (45, 1), (55, 1)] }, { coefficient := -1, powers := [(0, 1), (9, 1), (17, 1), (33, 1), (36, 1), (45, 1)] }, { coefficient := -1, powers := [(6, 1), (17, 1), (59, 1)] }, { coefficient := -1, powers := [(17, 1), (18, 1), (52, 1)] }, { coefficient := 1, powers := [(17, 1), (24, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (13, 1)] }, { coefficient := 1, powers := [(0, 1), (18, 1), (44, 1)] }, { coefficient := -1, powers := [(0, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(63, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (3, 1), (32, 1), (45, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (28, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (61, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(24, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (45, 1), (49, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (13, 1), (45, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (29, 1), (52, 1), (60, 1)] }, { coefficient := -1, powers := [(8, 1), (32, 1), (48, 1), (52, 1)] }, { coefficient := -1, powers := [(61, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (29, 1), (52, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (18, 1), (45, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (5, 1), (24, 1), (45, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(18, 1), (24, 1), (61, 1)] }, { coefficient := -1, powers := [(24, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (24, 1), (63, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (3, 1), (24, 1), (45, 1), (58, 1)] }, { coefficient := 1, powers := [(0, 1), (3, 1), (30, 1), (45, 1), (55, 1)] }, { coefficient := 1, powers := [(0, 1), (9, 1), (33, 1), (36, 1), (45, 1)] }, { coefficient := 1, powers := [(6, 1), (59, 1)] }, { coefficient := 1, powers := [(18, 1), (52, 1)] }, { coefficient := -1, powers := [(24, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (24, 1), (37, 1), (59, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (40, 1), (56, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (45, 1), (52, 1)] }, { coefficient := -1, powers := [(18, 1), (45, 1)] }, { coefficient := -1, powers := [(24, 1), (52, 1)] }, { coefficient := 1, powers := [(36, 1), (59, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 2), (36, 1), (45, 1), (58, 1)] }, { coefficient := -1, powers := [(0, 2), (42, 1), (45, 1), (49, 1)] }, { coefficient := 1, powers := [(0, 1), (2, 1), (3, 1), (24, 1), (38, 1), (45, 1), (58, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (2, 1), (3, 1), (30, 1), (45, 1), (48, 1), (54, 1), (55, 1)] }, { coefficient := -1, powers := [(0, 1), (2, 1), (6, 1), (24, 1), (45, 1), (48, 1), (54, 1), (58, 1)] }, { coefficient := 1, powers := [(0, 1), (2, 1), (9, 1), (33, 1), (36, 1), (38, 1), (45, 1), (60, 1)] }, { coefficient := -1, powers := [(0, 1), (2, 1), (24, 1), (36, 1), (45, 1), (48, 1), (54, 1), (58, 1)] }, { coefficient := 1, powers := [(0, 1), (3, 1), (5, 1), (30, 1), (35, 1), (45, 1), (54, 1), (55, 1)] }, { coefficient := -1, powers := [(0, 1), (3, 1), (17, 1), (23, 1), (24, 1), (45, 1), (54, 1), (58, 1)] }, { coefficient := 1, powers := [(0, 1), (5, 1), (9, 1), (33, 1), (35, 1), (36, 1), (45, 1), (54, 1)] }, { coefficient := 1, powers := [(0, 1), (5, 1), (24, 1), (29, 1), (43, 1), (45, 1), (50, 1), (58, 1)] }, { coefficient := -1, powers := [(0, 1), (5, 1), (35, 1), (52, 1), (54, 1)] }, { coefficient := -1, powers := [(0, 1), (6, 1), (12, 1), (24, 1), (29, 1), (45, 1), (48, 1), (58, 1)] }, { coefficient := 1, powers := [(0, 1), (8, 1), (22, 1), (24, 1), (45, 1), (48, 1), (50, 1), (58, 1)] }, { coefficient := 1, powers := [(0, 1), (8, 1), (24, 1), (27, 1), (45, 1), (48, 1), (50, 1), (58, 1)] }, { coefficient := -1, powers := [(0, 1), (9, 1), (17, 1), (23, 1), (33, 1), (36, 1), (45, 1), (54, 1)] }, { coefficient := -1, powers := [(0, 1), (12, 1), (22, 1), (24, 1), (38, 1), (43, 1), (45, 1), (58, 1)] }, { coefficient := -1, powers := [(0, 1), (12, 1), (24, 1), (27, 1), (38, 1), (43, 1), (45, 1), (58, 1)] }, { coefficient := -2, powers := [(0, 1), (13, 1), (18, 1), (45, 1), (49, 1)] }, { coefficient := 1, powers := [(0, 1), (13, 1), (49, 1)] }, { coefficient := 1, powers := [(0, 1), (17, 1), (23, 1), (52, 1), (54, 1)] }, { coefficient := 1, powers := [(0, 1), (18, 1), (44, 1), (49, 1)] }, { coefficient := -1, powers := [(0, 1), (18, 1), (45, 1), (49, 1), (55, 1)] }, { coefficient := -1, powers := [(0, 1), (24, 1), (42, 1), (45, 1), (49, 1)] }, { coefficient := -1, powers := [(0, 1), (33, 1), (36, 1), (45, 1), (49, 1)] }, { coefficient := -1, powers := [(0, 1), (42, 1), (49, 1)] }, { coefficient := 1, powers := [(2, 1), (6, 1), (48, 1), (54, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (18, 1), (38, 1), (52, 1), (60, 1)] }, { coefficient := -1, powers := [(2, 1), (24, 1), (38, 1), (56, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (24, 1), (48, 1), (52, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (6, 1), (35, 1), (54, 1), (59, 1)] }, { coefficient := -1, powers := [(5, 1), (24, 1), (35, 1), (54, 1), (56, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (29, 1), (48, 1), (52, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (29, 1), (48, 1), (56, 1)] }, { coefficient := 1, powers := [(17, 1), (19, 1), (29, 1), (50, 1), (52, 1)] }, { coefficient := -1, powers := [(17, 1), (23, 1), (24, 1), (52, 1), (54, 1)] }, { coefficient := -1, powers := [(17, 1), (24, 1), (28, 1), (47, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (24, 1), (37, 1), (59, 1)] }, { coefficient := -1, powers := [(0, 1), (24, 1), (40, 1), (56, 1)] }, { coefficient := -1, powers := [(0, 1), (24, 1), (45, 1), (52, 1)] }, { coefficient := -1, powers := [(18, 1), (24, 1), (37, 1), (59, 1)] }, { coefficient := -1, powers := [(18, 1), (24, 1), (40, 1), (56, 1)] }, { coefficient := -1, powers := [(18, 1), (24, 1), (45, 1), (52, 1)] }, { coefficient := 1, powers := [(18, 1), (45, 1)] }, { coefficient := -1, powers := [(18, 1), (52, 1)] }, { coefficient := -1, powers := [(36, 1), (59, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 2), (1, 1), (45, 1), (55, 1), (62, 1)] }, { coefficient := -2, powers := [(0, 2), (14, 1), (25, 1), (42, 1), (45, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 2), (45, 1), (55, 1)] }, { coefficient := 1, powers := [(0, 1), (5, 1), (29, 1), (33, 1), (36, 1), (45, 1), (60, 1)] }, { coefficient := -1, powers := [(0, 1), (6, 1), (33, 1), (45, 1)] }, { coefficient := -1, powers := [(0, 1), (12, 1), (29, 1), (33, 1), (36, 1), (45, 1), (48, 1)] }, { coefficient := -2, powers := [(0, 1), (13, 1), (14, 1), (18, 1), (25, 1), (45, 1), (62, 1)] }, { coefficient := 1, powers := [(0, 1), (13, 1), (14, 1), (25, 1), (62, 1)] }, { coefficient := 1, powers := [(0, 1), (14, 1), (18, 1), (25, 1), (44, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 1), (14, 1), (18, 1), (25, 1), (45, 1), (55, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 1), (14, 1), (24, 1), (25, 1), (42, 1), (45, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 1), (14, 1), (25, 1), (33, 1), (36, 1), (45, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 1), (14, 1), (25, 1), (42, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (1, 1), (2, 1), (3, 1), (24, 1), (45, 1), (57, 1), (58, 1), (62, 1)] }, { coefficient := 1, powers := [(0, 1), (1, 1), (2, 1), (9, 1), (33, 1), (36, 1), (45, 1), (57, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 1), (2, 1), (3, 1), (24, 1), (45, 1), (57, 1), (58, 1)] }, { coefficient := -1, powers := [(0, 1), (2, 1), (3, 1), (30, 1), (45, 1), (55, 1), (57, 1)] }, { coefficient := -1, powers := [(0, 1), (2, 1), (9, 1), (33, 1), (36, 1), (45, 1), (57, 1)] }, { coefficient := -1, powers := [(0, 1), (3, 1), (8, 1), (24, 1), (35, 1), (45, 1), (58, 1)] }, { coefficient := -1, powers := [(0, 1), (3, 1), (8, 1), (30, 1), (35, 1), (45, 1), (55, 1)] }, { coefficient := -1, powers := [(0, 1), (8, 1), (9, 1), (33, 1), (35, 1), (36, 1), (45, 1)] }, { coefficient := 1, powers := [(1, 1), (2, 1), (18, 1), (52, 1), (57, 1), (62, 1)] }, { coefficient := -1, powers := [(1, 1), (2, 1), (24, 1), (56, 1), (57, 1), (62, 1)] }, { coefficient := -1, powers := [(2, 1), (6, 1), (57, 1), (59, 1)] }, { coefficient := -1, powers := [(2, 1), (18, 1), (52, 1), (57, 1)] }, { coefficient := -1, powers := [(6, 1), (8, 1), (35, 1), (59, 1)] }, { coefficient := -1, powers := [(8, 1), (18, 1), (35, 1), (52, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (35, 1), (56, 1)] }, { coefficient := -2, powers := [(16, 1), (24, 1), (28, 1), (57, 1)] }, { coefficient := -1, powers := [(17, 1), (24, 1), (29, 1), (52, 1)] }]
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
    (values : Fin 65 → R) :
    ¬ ∀ index : Fin 68,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component25.SelectedLeafB7_2.selectedHasNoCommonZero

end Krenn.Component25.SelectedLeafB7_2
