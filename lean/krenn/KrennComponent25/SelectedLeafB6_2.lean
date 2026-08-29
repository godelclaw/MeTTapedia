import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component25.SelectedLeafB6_2

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "d87a54fd1db41878820e08e0753ec9eb8130355b874d1b20c501b58049bae47b"
def certificateSHA256 : String := "cb06f714c6159840ead08b7cee94acd28a19ddac2761e55f96798c7690686062"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 53 → Fin 662 := ![
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
  157,
  162,
  168,
  169,
  171,
  188,
  238,
  293,
  297,
  300,
  306,
  312,
  324,
  344,
  388,
  434,
  435,
  436,
  440,
  450,
  475,
  478,
  519,
  600,
  601,
  606,
  628,
  653,
  655,
  657,
  658,
  659,
  661
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 53 → SparsePoly (Fin 64) := ![
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
  [{ coefficient := 1, powers := [(12, 1), (24, 1)] }, { coefficient := 1, powers := [(16, 1), (18, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (18, 1)] }, { coefficient := 1, powers := [(16, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (54, 1)] }, { coefficient := 1, powers := [(29, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (57, 1)] }, { coefficient := 1, powers := [(29, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (53, 1)] }, { coefficient := -1, powers := [(28, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (29, 1), (59, 1)] }, { coefficient := 1, powers := [(29, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (24, 1), (45, 1)] }, { coefficient := 1, powers := [(16, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (48, 1)] }, { coefficient := 1, powers := [(19, 1), (43, 1)] }, { coefficient := 1, powers := [(24, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (49, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1), (49, 1)] }, { coefficient := 1, powers := [(14, 1), (25, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (60, 1)] }, { coefficient := 1, powers := [(12, 1), (57, 1)] }, { coefficient := 1, powers := [(17, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (45, 1)] }, { coefficient := 1, powers := [(12, 1), (56, 1)] }, { coefficient := 1, powers := [(16, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (57, 1)] }, { coefficient := 1, powers := [(29, 1), (48, 1)] }, { coefficient := 1, powers := [(35, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (36, 1), (58, 1)] }, { coefficient := 1, powers := [(1, 1), (39, 1), (55, 1)] }, { coefficient := 1, powers := [(1, 1), (42, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (45, 1), (50, 1)] }, { coefficient := 1, powers := [(12, 1), (27, 1), (45, 1)] }, { coefficient := 1, powers := [(16, 1), (28, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (18, 1), (56, 1)] }, { coefficient := 1, powers := [(12, 1)] }, { coefficient := 1, powers := [(16, 1), (18, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (53, 1)] }, { coefficient := 1, powers := [(12, 1), (22, 1), (56, 1)] }, { coefficient := 1, powers := [(12, 1), (28, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1)] }, { coefficient := 1, powers := [(12, 1), (29, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (35, 1)] }, { coefficient := 1, powers := [(22, 1), (43, 1)] }, { coefficient := 1, powers := [(27, 1), (43, 1)] }, { coefficient := 1, powers := [(35, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (32, 1)] }, { coefficient := 1, powers := [(22, 1), (50, 1)] }, { coefficient := 1, powers := [(27, 1), (50, 1)] }, { coefficient := 1, powers := [(32, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (54, 1)] }, { coefficient := 1, powers := [(29, 1), (41, 1)] }, { coefficient := 1, powers := [(29, 1), (47, 1), (50, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (36, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (59, 1)] }, { coefficient := 1, powers := [(8, 1), (23, 1), (59, 1)] }, { coefficient := 1, powers := [(16, 1), (29, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (30, 1), (57, 1)] }, { coefficient := 1, powers := [(8, 1), (30, 1), (48, 1)] }, { coefficient := 1, powers := [(11, 1), (19, 1), (57, 1)] }, { coefficient := 1, powers := [(17, 1), (30, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1)] }, { coefficient := 1, powers := [(3, 1), (33, 1)] }, { coefficient := 1, powers := [(13, 1), (18, 1)] }, { coefficient := 1, powers := [(18, 1), (55, 1)] }, { coefficient := 1, powers := [(24, 1), (42, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (49, 1)] }, { coefficient := 1, powers := [(6, 1), (30, 1)] }, { coefficient := 1, powers := [(9, 1), (24, 1)] }, { coefficient := 1, powers := [(18, 1), (49, 1)] }, { coefficient := 1, powers := [(24, 1), (39, 1)] }, { coefficient := 1, powers := [(30, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (36, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1)] }, { coefficient := 1, powers := [(3, 1), (24, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (18, 1), (59, 1)] }, { coefficient := 1, powers := [(18, 1)] }, { coefficient := 1, powers := [(24, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (29, 1), (60, 1)] }, { coefficient := 1, powers := [(3, 1), (32, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (35, 1), (54, 1)] }, { coefficient := 1, powers := [(22, 1), (43, 1), (54, 1)] }, { coefficient := 1, powers := [(22, 1), (50, 1), (57, 1)] }, { coefficient := 1, powers := [(29, 1), (43, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (36, 1), (58, 1)] }, { coefficient := 1, powers := [(0, 1), (39, 1), (55, 1)] }, { coefficient := 1, powers := [(0, 1), (42, 1), (49, 1)] }, { coefficient := 1, powers := [(3, 1), (24, 1), (58, 1)] }, { coefficient := 1, powers := [(3, 1), (30, 1), (55, 1)] }, { coefficient := 1, powers := [(3, 1), (33, 1), (49, 1)] }, { coefficient := 1, powers := [(6, 1), (18, 1), (58, 1)] }, { coefficient := 1, powers := [(6, 1), (30, 1), (42, 1)] }, { coefficient := 1, powers := [(6, 1), (33, 1), (39, 1)] }, { coefficient := 1, powers := [(9, 1), (18, 1), (55, 1)] }, { coefficient := 1, powers := [(9, 1), (24, 1), (42, 1)] }, { coefficient := 1, powers := [(9, 1), (33, 1), (36, 1)] }, { coefficient := 1, powers := [(13, 1), (18, 1), (49, 1)] }, { coefficient := 1, powers := [(13, 1), (24, 1), (39, 1)] }, { coefficient := 1, powers := [(13, 1), (30, 1), (36, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (41, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (48, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (23, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (48, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(12, 1), (23, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1), (29, 1), (48, 1)] }, { coefficient := 1, powers := [(12, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(17, 1), (23, 1), (54, 1)] }, { coefficient := 1, powers := [(17, 1), (29, 1), (41, 1)] }, { coefficient := 1, powers := [(17, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(39, 1)] }],
  [{ coefficient := 1, powers := [(41, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 53 → SparsePoly (Fin 64) := ![
  [{ coefficient := 1, powers := [(3, 1), (23, 1), (55, 1), (60, 1)] }, { coefficient := -1, powers := [(6, 1), (13, 1), (23, 1), (60, 1)] }, { coefficient := 1, powers := [(6, 1), (23, 1), (42, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (6, 1), (32, 1), (36, 1), (48, 1), (58, 1)] }, { coefficient := 1, powers := [(3, 2), (23, 1), (30, 1), (55, 1), (60, 1)] }, { coefficient := -1, powers := [(3, 1), (6, 1), (13, 1), (23, 1), (30, 1), (60, 1)] }, { coefficient := 1, powers := [(3, 1), (6, 1), (18, 1), (23, 1), (58, 1), (60, 1)] }, { coefficient := 1, powers := [(3, 1), (6, 1), (23, 1), (30, 1), (42, 1), (60, 1)] }, { coefficient := -1, powers := [(3, 1), (6, 1), (24, 1), (32, 1), (48, 1), (58, 1)] }, { coefficient := 1, powers := [(3, 1), (23, 1), (24, 1), (43, 1), (50, 1), (58, 1)] }, { coefficient := -1, powers := [(6, 2), (18, 1), (32, 1), (48, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (13, 1), (24, 1), (32, 1)] }, { coefficient := 1, powers := [(5, 1), (18, 1), (32, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (24, 1), (32, 1), (42, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (33, 1), (36, 1)] }, { coefficient := 1, powers := [(12, 1), (13, 1), (23, 1), (24, 1)] }, { coefficient := -1, powers := [(12, 1), (18, 1), (23, 1), (55, 1)] }, { coefficient := -1, powers := [(12, 1), (23, 1), (24, 1), (42, 1)] }, { coefficient := -1, powers := [(12, 1), (23, 1), (33, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (22, 1), (24, 1), (25, 1), (38, 1), (58, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (12, 1), (24, 1), (25, 1), (29, 1), (58, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (13, 1), (20, 1), (62, 1)] }, { coefficient := 1, powers := [(0, 1), (20, 1), (42, 1), (62, 1)] }, { coefficient := 1, powers := [(13, 1), (18, 1), (20, 1), (62, 1)] }, { coefficient := 1, powers := [(18, 1), (20, 1), (55, 1), (62, 1)] }, { coefficient := 1, powers := [(20, 1), (24, 1), (42, 1), (62, 1)] }, { coefficient := 1, powers := [(20, 1), (33, 1), (36, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (20, 1), (22, 1), (24, 1), (48, 1), (58, 1), (62, 1)] }, { coefficient := -1, powers := [(8, 1), (20, 1), (24, 1), (27, 1), (48, 1), (58, 1), (62, 1)] }, { coefficient := 1, powers := [(16, 1), (20, 1), (24, 1), (27, 1), (38, 1), (43, 1), (58, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (5, 1), (6, 1), (20, 1), (35, 1), (58, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 1), (6, 1), (17, 1), (20, 1), (23, 1), (58, 1), (62, 1)] }, { coefficient := -1, powers := [(3, 1), (5, 1), (20, 1), (30, 1), (35, 1), (55, 1), (62, 1)] }, { coefficient := 1, powers := [(3, 1), (17, 1), (20, 1), (23, 1), (24, 1), (58, 1), (62, 1)] }, { coefficient := 1, powers := [(5, 1), (6, 1), (13, 1), (20, 1), (30, 1), (35, 1), (62, 1)] }, { coefficient := -1, powers := [(5, 1), (6, 1), (20, 1), (30, 1), (35, 1), (42, 1), (62, 1)] }, { coefficient := 1, powers := [(5, 1), (9, 1), (13, 1), (20, 1), (24, 1), (35, 1), (62, 1)] }, { coefficient := -1, powers := [(5, 1), (9, 1), (18, 1), (20, 1), (35, 1), (55, 1), (62, 1)] }, { coefficient := -1, powers := [(5, 1), (9, 1), (20, 1), (24, 1), (35, 1), (42, 1), (62, 1)] }, { coefficient := -1, powers := [(5, 1), (9, 1), (20, 1), (33, 1), (35, 1), (36, 1), (62, 1)] }, { coefficient := -1, powers := [(9, 1), (13, 1), (17, 1), (20, 1), (23, 1), (24, 1), (62, 1)] }, { coefficient := 1, powers := [(9, 1), (17, 1), (18, 1), (20, 1), (23, 1), (55, 1), (62, 1)] }, { coefficient := 1, powers := [(9, 1), (17, 1), (20, 1), (23, 1), (24, 1), (42, 1), (62, 1)] }, { coefficient := 1, powers := [(9, 1), (17, 1), (20, 1), (23, 1), (33, 1), (36, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (6, 1), (22, 1), (48, 1), (58, 1)] }, { coefficient := -1, powers := [(3, 1), (22, 1), (24, 1), (48, 1), (58, 1)] }, { coefficient := 1, powers := [(9, 1), (13, 1), (22, 1), (24, 1), (48, 1)] }, { coefficient := -1, powers := [(9, 1), (18, 1), (22, 1), (48, 1), (55, 1)] }, { coefficient := -1, powers := [(9, 1), (22, 1), (24, 1), (42, 1), (48, 1)] }, { coefficient := -1, powers := [(9, 1), (22, 1), (33, 1), (36, 1), (48, 1)] }, { coefficient := -1, powers := [(22, 1), (24, 1), (36, 1), (48, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (24, 2), (36, 1), (53, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (6, 1), (32, 1), (58, 1)] }, { coefficient := -1, powers := [(6, 1), (12, 1), (23, 1), (58, 1)] }, { coefficient := -1, powers := [(12, 1), (23, 1), (24, 1), (36, 1), (56, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (11, 1), (32, 1), (55, 1)] }, { coefficient := 1, powers := [(6, 1), (11, 1), (13, 1), (32, 1)] }, { coefficient := -1, powers := [(6, 1), (11, 1), (32, 1), (42, 1)] }, { coefficient := 1, powers := [(6, 1), (12, 1), (22, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(3, 2), (16, 1), (30, 1), (55, 1), (60, 1)] }, { coefficient := -1, powers := [(3, 1), (6, 1), (13, 1), (16, 1), (30, 1), (60, 1)] }, { coefficient := 1, powers := [(3, 1), (6, 1), (16, 1), (18, 1), (58, 1), (60, 1)] }, { coefficient := 1, powers := [(3, 1), (6, 1), (16, 1), (30, 1), (42, 1), (60, 1)] }, { coefficient := 1, powers := [(3, 1), (16, 1), (24, 1), (43, 1), (50, 1), (58, 1)] }, { coefficient := -1, powers := [(3, 1), (17, 1), (24, 1), (50, 1), (58, 1)] }, { coefficient := -1, powers := [(3, 1), (17, 1), (30, 1), (50, 1), (55, 1)] }, { coefficient := 1, powers := [(6, 1), (13, 1), (17, 1), (30, 1), (50, 1)] }, { coefficient := -1, powers := [(6, 1), (17, 1), (18, 1), (50, 1), (58, 1)] }, { coefficient := -1, powers := [(6, 1), (17, 1), (30, 1), (42, 1), (50, 1)] }, { coefficient := 1, powers := [(9, 1), (13, 1), (17, 1), (24, 1), (50, 1)] }, { coefficient := -1, powers := [(9, 1), (17, 1), (18, 1), (50, 1), (55, 1)] }, { coefficient := -1, powers := [(9, 1), (17, 1), (24, 1), (42, 1), (50, 1)] }, { coefficient := -1, powers := [(9, 1), (17, 1), (33, 1), (36, 1), (50, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (17, 1), (32, 1), (55, 1)] }, { coefficient := 1, powers := [(6, 1), (13, 1), (17, 1), (32, 1)] }, { coefficient := -1, powers := [(6, 1), (17, 1), (32, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (6, 1), (35, 1), (58, 1)] }, { coefficient := -1, powers := [(6, 1), (17, 1), (23, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (22, 1), (24, 1), (38, 1), (58, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (12, 1), (24, 1), (29, 1), (58, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (22, 1), (24, 1), (48, 1), (58, 1), (62, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (27, 1), (48, 1), (58, 1), (62, 1)] }, { coefficient := -1, powers := [(16, 1), (24, 1), (27, 1), (38, 1), (43, 1), (58, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (5, 1), (6, 1), (35, 1), (58, 1), (62, 1)] }, { coefficient := 1, powers := [(0, 1), (6, 1), (17, 1), (23, 1), (58, 1), (62, 1)] }, { coefficient := 1, powers := [(3, 1), (5, 1), (30, 1), (35, 1), (55, 1), (62, 1)] }, { coefficient := -1, powers := [(3, 1), (17, 1), (23, 1), (24, 1), (58, 1), (62, 1)] }, { coefficient := -1, powers := [(5, 1), (6, 1), (13, 1), (30, 1), (35, 1), (62, 1)] }, { coefficient := 1, powers := [(5, 1), (6, 1), (30, 1), (35, 1), (42, 1), (62, 1)] }, { coefficient := -1, powers := [(5, 1), (9, 1), (13, 1), (24, 1), (35, 1), (62, 1)] }, { coefficient := 1, powers := [(5, 1), (9, 1), (18, 1), (35, 1), (55, 1), (62, 1)] }, { coefficient := 1, powers := [(5, 1), (9, 1), (24, 1), (35, 1), (42, 1), (62, 1)] }, { coefficient := 1, powers := [(5, 1), (9, 1), (33, 1), (35, 1), (36, 1), (62, 1)] }, { coefficient := 1, powers := [(9, 1), (13, 1), (17, 1), (23, 1), (24, 1), (62, 1)] }, { coefficient := -1, powers := [(9, 1), (17, 1), (18, 1), (23, 1), (55, 1), (62, 1)] }, { coefficient := -1, powers := [(9, 1), (17, 1), (23, 1), (24, 1), (42, 1), (62, 1)] }, { coefficient := -1, powers := [(9, 1), (17, 1), (23, 1), (33, 1), (36, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (13, 1), (24, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (18, 1), (55, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (24, 1), (42, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (36, 1), (60, 1)] }, { coefficient := 1, powers := [(12, 1), (13, 1), (24, 1), (48, 1)] }, { coefficient := -1, powers := [(12, 1), (18, 1), (48, 1), (55, 1)] }, { coefficient := -1, powers := [(12, 1), (24, 1), (42, 1), (48, 1)] }, { coefficient := -1, powers := [(12, 1), (33, 1), (36, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (28, 1), (38, 1), (43, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(23, 1), (24, 1), (36, 1), (53, 1), (57, 1), (58, 1)] }, { coefficient := 1, powers := [(24, 1), (27, 1), (38, 1), (43, 1), (53, 1), (58, 1)] }, { coefficient := -1, powers := [(24, 1), (28, 1), (38, 1), (43, 1), (50, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (24, 1), (43, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (24, 1), (50, 1), (58, 1)] }, { coefficient := -1, powers := [(6, 1), (12, 1), (19, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(16, 1), (18, 1), (24, 1), (38, 1), (43, 1), (58, 1)] }, { coefficient := -1, powers := [(16, 1), (24, 2), (38, 1), (43, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (5, 1), (30, 1), (55, 1), (60, 1)] }, { coefficient := -1, powers := [(5, 1), (6, 1), (13, 1), (30, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (6, 1), (18, 1), (58, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (6, 1), (30, 1), (42, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (24, 1), (43, 1), (50, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(22, 1), (24, 1), (38, 1), (43, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (12, 1), (29, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (13, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 1), (42, 1), (62, 1)] }, { coefficient := -1, powers := [(13, 1), (18, 1), (62, 1)] }, { coefficient := -1, powers := [(18, 1), (55, 1), (62, 1)] }, { coefficient := -1, powers := [(24, 1), (42, 1), (62, 1)] }, { coefficient := -1, powers := [(33, 1), (36, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (23, 1), (24, 1), (58, 1)] }, { coefficient := 1, powers := [(6, 1), (18, 1), (23, 1), (58, 1)] }, { coefficient := -1, powers := [(9, 1), (13, 1), (23, 1), (24, 1)] }, { coefficient := 1, powers := [(9, 1), (18, 1), (23, 1), (55, 1)] }, { coefficient := 1, powers := [(9, 1), (23, 1), (24, 1), (42, 1)] }, { coefficient := 1, powers := [(9, 1), (23, 1), (33, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (24, 1), (27, 1), (38, 1), (43, 1), (58, 1)] }, { coefficient := 1, powers := [(22, 1), (24, 2), (38, 1), (43, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (12, 1), (30, 1), (55, 1)] }, { coefficient := -1, powers := [(6, 1), (12, 1), (13, 1), (30, 1)] }, { coefficient := 1, powers := [(6, 1), (12, 1), (18, 1), (58, 1)] }, { coefficient := 1, powers := [(6, 1), (12, 1), (30, 1), (42, 1)] }, { coefficient := -1, powers := [(9, 1), (12, 1), (13, 1), (24, 1)] }, { coefficient := 1, powers := [(9, 1), (12, 1), (18, 1), (55, 1)] }, { coefficient := 1, powers := [(9, 1), (12, 1), (24, 1), (42, 1)] }, { coefficient := 1, powers := [(9, 1), (12, 1), (33, 1), (36, 1)] }, { coefficient := -1, powers := [(12, 1), (24, 1), (36, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(18, 1), (24, 1), (38, 1), (43, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (24, 1), (36, 1), (57, 1), (58, 1)] }, { coefficient := -1, powers := [(24, 1), (27, 1), (38, 1), (43, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(24, 2), (38, 1), (43, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (6, 1), (48, 1), (58, 1)] }, { coefficient := 1, powers := [(3, 1), (24, 1), (48, 1), (58, 1)] }, { coefficient := -1, powers := [(9, 1), (13, 1), (24, 1), (48, 1)] }, { coefficient := 1, powers := [(9, 1), (18, 1), (48, 1), (55, 1)] }, { coefficient := 1, powers := [(9, 1), (24, 1), (42, 1), (48, 1)] }, { coefficient := 1, powers := [(9, 1), (33, 1), (36, 1), (48, 1)] }, { coefficient := 1, powers := [(24, 1), (36, 1), (48, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (24, 1), (38, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (24, 1), (48, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (17, 1), (24, 1), (58, 1)] }, { coefficient := 1, powers := [(3, 1), (17, 1), (30, 1), (55, 1)] }, { coefficient := -1, powers := [(6, 1), (13, 1), (17, 1), (30, 1)] }, { coefficient := 1, powers := [(6, 1), (17, 1), (18, 1), (58, 1)] }, { coefficient := 1, powers := [(6, 1), (17, 1), (30, 1), (42, 1)] }, { coefficient := -1, powers := [(9, 1), (13, 1), (17, 1), (24, 1)] }, { coefficient := 1, powers := [(9, 1), (17, 1), (18, 1), (55, 1)] }, { coefficient := 1, powers := [(9, 1), (17, 1), (24, 1), (42, 1)] }, { coefficient := 1, powers := [(9, 1), (17, 1), (33, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (38, 1), (43, 1), (50, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(3, 2), (30, 1), (55, 1), (60, 1)] }, { coefficient := 1, powers := [(3, 1), (6, 1), (13, 1), (30, 1), (60, 1)] }, { coefficient := -1, powers := [(3, 1), (6, 1), (18, 1), (58, 1), (60, 1)] }, { coefficient := -1, powers := [(3, 1), (6, 1), (30, 1), (42, 1), (60, 1)] }, { coefficient := -1, powers := [(3, 1), (24, 1), (43, 1), (50, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (32, 1), (55, 1)] }, { coefficient := -1, powers := [(6, 1), (13, 1), (32, 1)] }, { coefficient := 1, powers := [(6, 1), (32, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(49, 1)] }],
  [{ coefficient := 1, powers := [(13, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (8, 1), (32, 1), (48, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (24, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(3, 1), (24, 1), (58, 1)] }, { coefficient := -1, powers := [(3, 1), (30, 1), (55, 1)] }, { coefficient := 1, powers := [(6, 1), (13, 1), (30, 1)] }, { coefficient := -1, powers := [(6, 1), (18, 1), (58, 1)] }, { coefficient := -1, powers := [(6, 1), (30, 1), (42, 1)] }, { coefficient := 1, powers := [(9, 1), (13, 1), (24, 1)] }, { coefficient := -1, powers := [(9, 1), (18, 1), (55, 1)] }, { coefficient := -1, powers := [(9, 1), (24, 1), (42, 1)] }, { coefficient := -1, powers := [(9, 1), (33, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (5, 1), (6, 1), (35, 1), (54, 1), (58, 1)] }, { coefficient := -1, powers := [(0, 1), (6, 1), (17, 1), (23, 1), (54, 1), (58, 1)] }, { coefficient := 1, powers := [(0, 1), (13, 1), (49, 1)] }, { coefficient := -1, powers := [(0, 1), (36, 1), (58, 1)] }, { coefficient := -1, powers := [(3, 1), (5, 1), (30, 1), (35, 1), (54, 1), (55, 1)] }, { coefficient := 1, powers := [(3, 1), (17, 1), (23, 1), (24, 1), (54, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (6, 1), (13, 1), (30, 1), (35, 1), (54, 1)] }, { coefficient := -1, powers := [(5, 1), (6, 1), (30, 1), (35, 1), (42, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (9, 1), (13, 1), (24, 1), (35, 1), (54, 1)] }, { coefficient := -1, powers := [(5, 1), (9, 1), (18, 1), (35, 1), (54, 1), (55, 1)] }, { coefficient := -1, powers := [(5, 1), (9, 1), (24, 1), (35, 1), (42, 1), (54, 1)] }, { coefficient := -1, powers := [(5, 1), (9, 1), (33, 1), (35, 1), (36, 1), (54, 1)] }, { coefficient := 1, powers := [(6, 1), (12, 1), (24, 1), (29, 1), (48, 1), (58, 1)] }, { coefficient := -1, powers := [(8, 1), (22, 1), (24, 1), (48, 1), (50, 1), (58, 1)] }, { coefficient := -1, powers := [(8, 1), (24, 1), (27, 1), (48, 1), (50, 1), (58, 1)] }, { coefficient := -1, powers := [(9, 1), (13, 1), (17, 1), (23, 1), (24, 1), (54, 1)] }, { coefficient := 1, powers := [(9, 1), (17, 1), (18, 1), (23, 1), (54, 1), (55, 1)] }, { coefficient := 1, powers := [(9, 1), (17, 1), (23, 1), (24, 1), (42, 1), (54, 1)] }, { coefficient := 1, powers := [(9, 1), (17, 1), (23, 1), (33, 1), (36, 1), (54, 1)] }, { coefficient := 1, powers := [(12, 1), (22, 1), (24, 1), (38, 1), (43, 1), (58, 1)] }, { coefficient := 1, powers := [(13, 1), (18, 1), (49, 1)] }, { coefficient := 1, powers := [(16, 1), (24, 1), (27, 1), (38, 1), (43, 1), (50, 1), (58, 1)] }, { coefficient := 1, powers := [(18, 1), (49, 1), (55, 1)] }, { coefficient := 1, powers := [(24, 1), (42, 1), (49, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (6, 1), (48, 1), (54, 1), (58, 1)] }, { coefficient := 1, powers := [(3, 2), (30, 1), (38, 1), (55, 1), (59, 1), (60, 1)] }, { coefficient := -1, powers := [(3, 1), (6, 1), (13, 1), (30, 1), (38, 1), (59, 1), (60, 1)] }, { coefficient := 1, powers := [(3, 1), (6, 1), (18, 1), (38, 1), (58, 1), (59, 1), (60, 1)] }, { coefficient := 1, powers := [(3, 1), (6, 1), (30, 1), (38, 1), (42, 1), (59, 1), (60, 1)] }, { coefficient := 1, powers := [(3, 1), (24, 1), (38, 1), (43, 1), (50, 1), (58, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (24, 1), (38, 1), (58, 1), (60, 1)] }, { coefficient := 1, powers := [(3, 1), (24, 1), (41, 1), (57, 1), (58, 1)] }, { coefficient := 1, powers := [(3, 1), (30, 1), (38, 1), (55, 1), (60, 1)] }, { coefficient := 1, powers := [(3, 1), (30, 1), (41, 1), (55, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (30, 1), (48, 1), (54, 1), (55, 1)] }, { coefficient := -1, powers := [(6, 1), (13, 1), (30, 1), (38, 1), (60, 1)] }, { coefficient := -1, powers := [(6, 1), (13, 1), (30, 1), (41, 1), (57, 1)] }, { coefficient := -1, powers := [(6, 1), (13, 1), (30, 1), (48, 1), (54, 1)] }, { coefficient := 1, powers := [(6, 1), (18, 1), (38, 1), (58, 1), (60, 1)] }, { coefficient := 1, powers := [(6, 1), (18, 1), (41, 1), (57, 1), (58, 1)] }, { coefficient := 1, powers := [(6, 1), (18, 1), (48, 1), (54, 1), (58, 1)] }, { coefficient := 1, powers := [(6, 1), (30, 1), (38, 1), (42, 1), (60, 1)] }, { coefficient := 1, powers := [(6, 1), (30, 1), (41, 1), (42, 1), (57, 1)] }, { coefficient := 1, powers := [(6, 1), (30, 1), (42, 1), (48, 1), (54, 1)] }, { coefficient := -1, powers := [(9, 1), (13, 1), (24, 1), (38, 1), (60, 1)] }, { coefficient := -1, powers := [(9, 1), (13, 1), (24, 1), (41, 1), (57, 1)] }, { coefficient := 1, powers := [(9, 1), (18, 1), (38, 1), (55, 1), (60, 1)] }, { coefficient := 1, powers := [(9, 1), (18, 1), (41, 1), (55, 1), (57, 1)] }, { coefficient := 1, powers := [(9, 1), (24, 1), (38, 1), (42, 1), (60, 1)] }, { coefficient := 1, powers := [(9, 1), (24, 1), (41, 1), (42, 1), (57, 1)] }, { coefficient := 1, powers := [(9, 1), (33, 1), (36, 1), (38, 1), (60, 1)] }, { coefficient := 1, powers := [(9, 1), (33, 1), (36, 1), (41, 1), (57, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (38, 1), (43, 1), (45, 1), (50, 1), (58, 1)] }, { coefficient := 1, powers := [(24, 2), (38, 1), (43, 1), (53, 1), (58, 1)] }, { coefficient := -1, powers := [(24, 1), (36, 1), (38, 1), (43, 1), (50, 1), (58, 1), (59, 1)] }, { coefficient := -1, powers := [(24, 1), (36, 1), (48, 1), (54, 1), (58, 1)] }, { coefficient := -1, powers := [(24, 1), (38, 1), (43, 1), (50, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (1, 1), (55, 1), (62, 1)] }, { coefficient := 1, powers := [(0, 1), (13, 1), (14, 1), (25, 1), (62, 1)] }, { coefficient := 1, powers := [(0, 1), (14, 1), (25, 1), (42, 1), (62, 1)] }, { coefficient := 1, powers := [(0, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (13, 1), (24, 1), (29, 1), (60, 1)] }, { coefficient := -1, powers := [(5, 1), (18, 1), (29, 1), (55, 1), (60, 1)] }, { coefficient := -1, powers := [(5, 1), (24, 1), (29, 1), (42, 1), (60, 1)] }, { coefficient := -1, powers := [(5, 1), (29, 1), (33, 1), (36, 1), (60, 1)] }, { coefficient := 1, powers := [(6, 1), (33, 1)] }, { coefficient := -1, powers := [(12, 1), (13, 1), (24, 1), (29, 1), (48, 1)] }, { coefficient := 1, powers := [(12, 1), (18, 1), (29, 1), (48, 1), (55, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (29, 1), (42, 1), (48, 1)] }, { coefficient := 1, powers := [(12, 1), (29, 1), (33, 1), (36, 1), (48, 1)] }, { coefficient := 1, powers := [(13, 1), (14, 1), (18, 1), (25, 1), (62, 1)] }, { coefficient := 1, powers := [(14, 1), (18, 1), (25, 1), (55, 1), (62, 1)] }, { coefficient := 1, powers := [(14, 1), (24, 1), (25, 1), (42, 1), (62, 1)] }, { coefficient := 1, powers := [(14, 1), (25, 1), (33, 1), (36, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (8, 1), (24, 1), (35, 1), (58, 1)] }, { coefficient := 1, powers := [(3, 1), (8, 1), (30, 1), (35, 1), (55, 1)] }, { coefficient := -1, powers := [(6, 1), (8, 1), (13, 1), (30, 1), (35, 1)] }, { coefficient := 1, powers := [(6, 1), (8, 1), (18, 1), (35, 1), (58, 1)] }, { coefficient := 1, powers := [(6, 1), (8, 1), (30, 1), (35, 1), (42, 1)] }, { coefficient := -1, powers := [(8, 1), (9, 1), (13, 1), (24, 1), (35, 1)] }, { coefficient := 1, powers := [(8, 1), (9, 1), (18, 1), (35, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (9, 1), (24, 1), (35, 1), (42, 1)] }, { coefficient := 1, powers := [(8, 1), (9, 1), (33, 1), (35, 1), (36, 1)] }]
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
    (values : Fin 64 → R) :
    ¬ ∀ index : Fin 53,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component25.SelectedLeafB6_2.selectedHasNoCommonZero

end Krenn.Component25.SelectedLeafB6_2
