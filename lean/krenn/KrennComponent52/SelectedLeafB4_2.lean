import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component52.SelectedLeafB4_2

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "c6eb38fd1f5a6c4a56eba50608e14e90e1788a367555b581b841fc0632b07998"
def certificateSHA256 : String := "7e3f46475fe9e1d8a9744a8c70330aa0e2aa254879c30bfdd916943f9a93d284"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 24 → Fin 640 := ![
  6,
  7,
  9,
  17,
  24,
  26,
  169,
  221,
  231,
  233,
  293,
  346,
  347,
  353,
  354,
  394,
  460,
  461,
  576,
  631,
  633,
  636,
  637,
  639
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 24 → SparsePoly (Fin 62) := ![
  [{ coefficient := 1, powers := [(3, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (33, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (20, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (32, 1)] }, { coefficient := 1, powers := [(32, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (29, 1), (58, 1)] }, { coefficient := 1, powers := [(29, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (33, 1), (49, 1)] }, { coefficient := 1, powers := [(5, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (23, 1), (58, 1)] }, { coefficient := 1, powers := [(23, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (19, 1), (55, 1)] }, { coefficient := 1, powers := [(13, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (47, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (53, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1)] }, { coefficient := 1, powers := [(13, 1), (29, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (53, 1)] }, { coefficient := 1, powers := [(29, 1), (41, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (56, 1)] }, { coefficient := 1, powers := [(29, 1), (47, 1)] }, { coefficient := 1, powers := [(35, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (32, 1), (54, 1)] }, { coefficient := 1, powers := [(6, 1), (32, 1), (42, 1)] }, { coefficient := 1, powers := [(14, 1), (32, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (59, 1)] }, { coefficient := 1, powers := [(13, 1), (47, 1)] }, { coefficient := 1, powers := [(18, 1), (20, 1), (51, 1)] }, { coefficient := 1, powers := [(18, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (59, 1)] }, { coefficient := 1, powers := [(13, 1), (25, 1), (45, 1)] }, { coefficient := 1, powers := [(13, 1), (56, 1)] }, { coefficient := 1, powers := [(18, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (48, 1)] }, { coefficient := 1, powers := [(6, 1), (30, 1)] }, { coefficient := 1, powers := [(9, 1), (24, 1)] }, { coefficient := 1, powers := [(19, 1), (48, 1)] }, { coefficient := 1, powers := [(24, 1), (39, 1)] }, { coefficient := 1, powers := [(30, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (36, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (39, 1), (54, 1)] }, { coefficient := 1, powers := [(0, 1), (42, 1), (48, 1)] }, { coefficient := 1, powers := [(3, 1), (24, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (30, 1), (54, 1)] }, { coefficient := 1, powers := [(3, 1), (33, 1), (48, 1)] }, { coefficient := 1, powers := [(6, 1), (19, 1), (57, 1)] }, { coefficient := 1, powers := [(6, 1), (30, 1), (42, 1)] }, { coefficient := 1, powers := [(6, 1), (33, 1), (39, 1)] }, { coefficient := 1, powers := [(9, 1), (19, 1), (54, 1)] }, { coefficient := 1, powers := [(9, 1), (24, 1), (42, 1)] }, { coefficient := 1, powers := [(9, 1), (33, 1), (36, 1)] }, { coefficient := 1, powers := [(14, 1), (19, 1), (48, 1)] }, { coefficient := 1, powers := [(14, 1), (24, 1), (39, 1)] }, { coefficient := 1, powers := [(14, 1), (30, 1), (36, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (41, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (47, 1), (53, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (53, 1)] }, { coefficient := 1, powers := [(8, 1), (23, 1), (59, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (47, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(13, 1), (23, 1), (56, 1)] }, { coefficient := 1, powers := [(13, 1), (29, 1), (47, 1)] }, { coefficient := 1, powers := [(13, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (53, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (41, 1)] }, { coefficient := 1, powers := [(18, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(39, 1)] }],
  [{ coefficient := 1, powers := [(41, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 24 → SparsePoly (Fin 62) := ![
  [{ coefficient := -2, powers := [(0, 1), (5, 1), (29, 1), (36, 1), (57, 1), (58, 1)] }, { coefficient := -2, powers := [(3, 1), (5, 1), (24, 1), (29, 1), (57, 1), (58, 1)] }, { coefficient := -2, powers := [(3, 1), (5, 1), (29, 1), (30, 1), (54, 1), (58, 1)] }, { coefficient := -2, powers := [(3, 1), (5, 1), (29, 1), (33, 1), (48, 1), (58, 1)] }, { coefficient := -2, powers := [(5, 1), (6, 1), (19, 1), (29, 1), (57, 1), (58, 1)] }, { coefficient := -2, powers := [(5, 1), (9, 1), (19, 1), (29, 1), (54, 1), (58, 1)] }, { coefficient := -2, powers := [(5, 1), (9, 1), (29, 1), (33, 1), (36, 1), (58, 1)] }, { coefficient := -2, powers := [(5, 1), (14, 1), (19, 1), (29, 1), (48, 1), (58, 1)] }, { coefficient := -2, powers := [(5, 1), (14, 1), (29, 1), (30, 1), (36, 1), (58, 1)] }, { coefficient := 2, powers := [(5, 1), (19, 1), (29, 1), (42, 1), (48, 1), (58, 1)] }, { coefficient := 2, powers := [(5, 1), (29, 1), (30, 1), (36, 1), (42, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (32, 1), (36, 1), (49, 1), (56, 1)] }, { coefficient := -1, powers := [(3, 1), (24, 1), (32, 1), (49, 1), (56, 1)] }, { coefficient := 1, powers := [(3, 1), (32, 1), (48, 1), (56, 1)] }, { coefficient := 1, powers := [(9, 1), (32, 1), (36, 1), (56, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (8, 1), (23, 1), (36, 1), (57, 1), (58, 1)] }, { coefficient := -2, powers := [(3, 1), (8, 1), (23, 1), (24, 1), (57, 1), (58, 1)] }, { coefficient := -2, powers := [(3, 1), (8, 1), (23, 1), (30, 1), (54, 1), (58, 1)] }, { coefficient := -2, powers := [(3, 1), (8, 1), (23, 1), (33, 1), (48, 1), (58, 1)] }, { coefficient := -2, powers := [(6, 1), (8, 1), (19, 1), (23, 1), (57, 1), (58, 1)] }, { coefficient := -2, powers := [(8, 1), (9, 1), (19, 1), (23, 1), (54, 1), (58, 1)] }, { coefficient := -2, powers := [(8, 1), (9, 1), (23, 1), (33, 1), (36, 1), (58, 1)] }, { coefficient := -2, powers := [(8, 1), (14, 1), (19, 1), (23, 1), (48, 1), (58, 1)] }, { coefficient := -2, powers := [(8, 1), (14, 1), (23, 1), (30, 1), (36, 1), (58, 1)] }, { coefficient := 2, powers := [(8, 1), (19, 1), (23, 1), (42, 1), (48, 1), (58, 1)] }, { coefficient := 2, powers := [(8, 1), (23, 1), (30, 1), (36, 1), (42, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (23, 1), (36, 1), (45, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (23, 1), (24, 1), (45, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (23, 1), (30, 1), (45, 1), (54, 1)] }, { coefficient := 1, powers := [(3, 1), (23, 1), (33, 1), (45, 1), (48, 1)] }, { coefficient := 1, powers := [(6, 1), (19, 1), (23, 1), (45, 1), (57, 1)] }, { coefficient := 1, powers := [(9, 1), (19, 1), (23, 1), (45, 1), (54, 1)] }, { coefficient := 1, powers := [(9, 1), (23, 1), (33, 1), (36, 1), (45, 1)] }, { coefficient := 1, powers := [(14, 1), (19, 1), (23, 1), (45, 1), (48, 1)] }, { coefficient := 1, powers := [(14, 1), (23, 1), (30, 1), (36, 1), (45, 1)] }, { coefficient := -1, powers := [(19, 1), (23, 1), (42, 1), (45, 1), (48, 1)] }, { coefficient := -1, powers := [(23, 1), (30, 1), (36, 1), (42, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (29, 1), (36, 1), (51, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (24, 1), (29, 1), (51, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (29, 1), (30, 1), (51, 1), (54, 1)] }, { coefficient := 1, powers := [(3, 1), (29, 1), (33, 1), (48, 1), (51, 1)] }, { coefficient := 1, powers := [(6, 1), (19, 1), (29, 1), (51, 1), (57, 1)] }, { coefficient := 1, powers := [(9, 1), (19, 1), (29, 1), (51, 1), (54, 1)] }, { coefficient := 1, powers := [(9, 1), (29, 1), (33, 1), (36, 1), (51, 1)] }, { coefficient := 1, powers := [(14, 1), (19, 1), (29, 1), (48, 1), (51, 1)] }, { coefficient := 1, powers := [(14, 1), (29, 1), (30, 1), (36, 1), (51, 1)] }, { coefficient := -1, powers := [(19, 1), (29, 1), (42, 1), (48, 1), (51, 1)] }, { coefficient := -1, powers := [(29, 1), (30, 1), (36, 1), (42, 1), (51, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (13, 1), (23, 1), (36, 1), (55, 1), (57, 1)] }, { coefficient := -1, powers := [(3, 1), (13, 1), (23, 1), (24, 1), (55, 1), (57, 1)] }, { coefficient := -1, powers := [(3, 1), (13, 1), (23, 1), (30, 1), (54, 1), (55, 1)] }, { coefficient := -1, powers := [(3, 1), (13, 1), (23, 1), (33, 1), (48, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (6, 1), (32, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (9, 1), (32, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (14, 1), (32, 1), (48, 1)] }, { coefficient := -1, powers := [(5, 1), (32, 1), (42, 1), (48, 1)] }, { coefficient := -1, powers := [(6, 1), (13, 1), (19, 1), (23, 1), (55, 1), (57, 1)] }, { coefficient := -1, powers := [(9, 1), (13, 1), (19, 1), (23, 1), (54, 1), (55, 1)] }, { coefficient := -1, powers := [(9, 1), (13, 1), (23, 1), (33, 1), (36, 1), (55, 1)] }, { coefficient := -1, powers := [(13, 1), (14, 1), (19, 1), (23, 1), (48, 1), (55, 1)] }, { coefficient := -1, powers := [(13, 1), (14, 1), (23, 1), (30, 1), (36, 1), (55, 1)] }, { coefficient := 1, powers := [(13, 1), (19, 1), (23, 1), (42, 1), (48, 1), (55, 1)] }, { coefficient := 1, powers := [(13, 1), (23, 1), (30, 1), (36, 1), (42, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (30, 1), (42, 1), (56, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (5, 1), (36, 1), (57, 1), (59, 1)] }, { coefficient := 2, powers := [(3, 1), (5, 1), (24, 1), (57, 1), (59, 1)] }, { coefficient := 2, powers := [(3, 1), (5, 1), (30, 1), (54, 1), (59, 1)] }, { coefficient := 2, powers := [(3, 1), (5, 1), (33, 1), (48, 1), (59, 1)] }, { coefficient := 2, powers := [(5, 1), (6, 1), (19, 1), (57, 1), (59, 1)] }, { coefficient := 2, powers := [(5, 1), (9, 1), (19, 1), (54, 1), (59, 1)] }, { coefficient := 2, powers := [(5, 1), (9, 1), (33, 1), (36, 1), (59, 1)] }, { coefficient := 2, powers := [(5, 1), (14, 1), (19, 1), (48, 1), (59, 1)] }, { coefficient := 2, powers := [(5, 1), (14, 1), (30, 1), (36, 1), (59, 1)] }, { coefficient := -2, powers := [(5, 1), (19, 1), (42, 1), (48, 1), (59, 1)] }, { coefficient := -2, powers := [(5, 1), (30, 1), (36, 1), (42, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (32, 1), (36, 1), (56, 1)] }, { coefficient := 1, powers := [(3, 1), (24, 1), (32, 1), (56, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (8, 1), (36, 1), (57, 1), (59, 1)] }, { coefficient := 2, powers := [(3, 1), (8, 1), (24, 1), (57, 1), (59, 1)] }, { coefficient := 2, powers := [(3, 1), (8, 1), (30, 1), (54, 1), (59, 1)] }, { coefficient := 2, powers := [(3, 1), (8, 1), (33, 1), (48, 1), (59, 1)] }, { coefficient := 2, powers := [(6, 1), (8, 1), (19, 1), (57, 1), (59, 1)] }, { coefficient := 2, powers := [(8, 1), (9, 1), (19, 1), (54, 1), (59, 1)] }, { coefficient := 2, powers := [(8, 1), (9, 1), (33, 1), (36, 1), (59, 1)] }, { coefficient := 2, powers := [(8, 1), (14, 1), (19, 1), (48, 1), (59, 1)] }, { coefficient := 2, powers := [(8, 1), (14, 1), (30, 1), (36, 1), (59, 1)] }, { coefficient := -2, powers := [(8, 1), (19, 1), (42, 1), (48, 1), (59, 1)] }, { coefficient := -2, powers := [(8, 1), (30, 1), (36, 1), (42, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (23, 1), (36, 1), (56, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (23, 1), (24, 1), (56, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (23, 1), (30, 1), (54, 1), (56, 1)] }, { coefficient := 1, powers := [(3, 1), (23, 1), (33, 1), (48, 1), (56, 1)] }, { coefficient := 1, powers := [(6, 1), (19, 1), (23, 1), (56, 1), (57, 1)] }, { coefficient := 1, powers := [(9, 1), (19, 1), (23, 1), (54, 1), (56, 1)] }, { coefficient := 1, powers := [(9, 1), (23, 1), (33, 1), (36, 1), (56, 1)] }, { coefficient := 1, powers := [(14, 1), (19, 1), (23, 1), (48, 1), (56, 1)] }, { coefficient := 1, powers := [(14, 1), (23, 1), (30, 1), (36, 1), (56, 1)] }, { coefficient := -1, powers := [(19, 1), (23, 1), (42, 1), (48, 1), (56, 1)] }, { coefficient := -1, powers := [(23, 1), (30, 1), (36, 1), (42, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (36, 1), (53, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (24, 1), (53, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (30, 1), (53, 1), (54, 1)] }, { coefficient := 1, powers := [(3, 1), (33, 1), (48, 1), (53, 1)] }, { coefficient := 1, powers := [(6, 1), (19, 1), (53, 1), (57, 1)] }, { coefficient := 1, powers := [(9, 1), (19, 1), (53, 1), (54, 1)] }, { coefficient := 1, powers := [(9, 1), (33, 1), (36, 1), (53, 1)] }, { coefficient := 1, powers := [(14, 1), (19, 1), (48, 1), (53, 1)] }, { coefficient := 1, powers := [(14, 1), (30, 1), (36, 1), (53, 1)] }, { coefficient := -1, powers := [(19, 1), (42, 1), (48, 1), (53, 1)] }, { coefficient := -1, powers := [(30, 1), (36, 1), (42, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (36, 1), (47, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (24, 1), (47, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (30, 1), (47, 1), (54, 1)] }, { coefficient := 1, powers := [(3, 1), (33, 1), (47, 1), (48, 1)] }, { coefficient := 1, powers := [(6, 1), (19, 1), (47, 1), (57, 1)] }, { coefficient := 1, powers := [(9, 1), (19, 1), (47, 1), (54, 1)] }, { coefficient := 1, powers := [(9, 1), (33, 1), (36, 1), (47, 1)] }, { coefficient := 1, powers := [(14, 1), (19, 1), (47, 1), (48, 1)] }, { coefficient := 1, powers := [(14, 1), (30, 1), (36, 1), (47, 1)] }, { coefficient := -1, powers := [(19, 1), (42, 1), (47, 1), (48, 1)] }, { coefficient := -1, powers := [(30, 1), (36, 1), (42, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (18, 1), (36, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (18, 1), (24, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (18, 1), (30, 1), (54, 1)] }, { coefficient := 1, powers := [(3, 1), (18, 1), (33, 1), (48, 1)] }, { coefficient := 1, powers := [(6, 1), (18, 1), (19, 1), (57, 1)] }, { coefficient := 1, powers := [(9, 1), (18, 1), (19, 1), (54, 1)] }, { coefficient := 1, powers := [(9, 1), (18, 1), (33, 1), (36, 1)] }, { coefficient := 1, powers := [(14, 1), (18, 1), (19, 1), (48, 1)] }, { coefficient := 1, powers := [(14, 1), (18, 1), (30, 1), (36, 1)] }, { coefficient := -1, powers := [(18, 1), (19, 1), (42, 1), (48, 1)] }, { coefficient := -1, powers := [(18, 1), (30, 1), (36, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (13, 1), (36, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (13, 1), (24, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (13, 1), (30, 1), (54, 1)] }, { coefficient := 1, powers := [(3, 1), (13, 1), (33, 1), (48, 1)] }, { coefficient := 1, powers := [(6, 1), (13, 1), (19, 1), (57, 1)] }, { coefficient := 1, powers := [(9, 1), (13, 1), (19, 1), (54, 1)] }, { coefficient := 1, powers := [(9, 1), (13, 1), (33, 1), (36, 1)] }, { coefficient := 1, powers := [(13, 1), (14, 1), (19, 1), (48, 1)] }, { coefficient := 1, powers := [(13, 1), (14, 1), (30, 1), (36, 1)] }, { coefficient := -1, powers := [(13, 1), (19, 1), (42, 1), (48, 1)] }, { coefficient := -1, powers := [(13, 1), (30, 1), (36, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (30, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (29, 1), (36, 1), (57, 1)] }, { coefficient := -1, powers := [(3, 1), (24, 1), (29, 1), (57, 1)] }, { coefficient := -1, powers := [(3, 1), (29, 1), (30, 1), (54, 1)] }, { coefficient := -1, powers := [(3, 1), (29, 1), (33, 1), (48, 1)] }, { coefficient := -1, powers := [(6, 1), (19, 1), (29, 1), (57, 1)] }, { coefficient := -1, powers := [(9, 1), (19, 1), (29, 1), (54, 1)] }, { coefficient := -1, powers := [(9, 1), (29, 1), (33, 1), (36, 1)] }, { coefficient := -1, powers := [(14, 1), (19, 1), (29, 1), (48, 1)] }, { coefficient := -1, powers := [(14, 1), (29, 1), (30, 1), (36, 1)] }, { coefficient := 1, powers := [(19, 1), (29, 1), (42, 1), (48, 1)] }, { coefficient := 1, powers := [(29, 1), (30, 1), (36, 1), (42, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (23, 1), (36, 1), (57, 1)] }, { coefficient := -1, powers := [(3, 1), (23, 1), (24, 1), (57, 1)] }, { coefficient := -1, powers := [(3, 1), (23, 1), (30, 1), (54, 1)] }, { coefficient := -1, powers := [(3, 1), (23, 1), (33, 1), (48, 1)] }, { coefficient := -1, powers := [(6, 1), (19, 1), (23, 1), (57, 1)] }, { coefficient := -1, powers := [(9, 1), (19, 1), (23, 1), (54, 1)] }, { coefficient := -1, powers := [(9, 1), (23, 1), (33, 1), (36, 1)] }, { coefficient := -1, powers := [(14, 1), (19, 1), (23, 1), (48, 1)] }, { coefficient := -1, powers := [(14, 1), (23, 1), (30, 1), (36, 1)] }, { coefficient := 1, powers := [(19, 1), (23, 1), (42, 1), (48, 1)] }, { coefficient := 1, powers := [(23, 1), (30, 1), (36, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(42, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(0, 1), (36, 1), (57, 1)] }, { coefficient := -1, powers := [(3, 1), (24, 1), (57, 1)] }, { coefficient := -1, powers := [(3, 1), (30, 1), (54, 1)] }, { coefficient := -1, powers := [(3, 1), (33, 1), (48, 1)] }, { coefficient := -1, powers := [(6, 1), (19, 1), (57, 1)] }, { coefficient := -1, powers := [(9, 1), (19, 1), (54, 1)] }, { coefficient := -1, powers := [(9, 1), (33, 1), (36, 1)] }, { coefficient := -1, powers := [(14, 1), (19, 1), (48, 1)] }, { coefficient := -1, powers := [(14, 1), (30, 1), (36, 1)] }, { coefficient := 1, powers := [(19, 1), (42, 1), (48, 1)] }, { coefficient := 1, powers := [(30, 1), (36, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (36, 1), (38, 1), (57, 1), (59, 1)] }, { coefficient := -1, powers := [(0, 1), (36, 1), (47, 1), (53, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (24, 1), (38, 1), (57, 1), (59, 1)] }, { coefficient := -1, powers := [(3, 1), (24, 1), (47, 1), (53, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (30, 1), (38, 1), (54, 1), (59, 1)] }, { coefficient := -1, powers := [(3, 1), (30, 1), (47, 1), (53, 1), (54, 1)] }, { coefficient := 1, powers := [(3, 1), (33, 1), (38, 1), (48, 1), (59, 1)] }, { coefficient := -1, powers := [(3, 1), (33, 1), (47, 1), (48, 1), (53, 1)] }, { coefficient := 1, powers := [(6, 1), (19, 1), (38, 1), (57, 1), (59, 1)] }, { coefficient := -1, powers := [(6, 1), (19, 1), (47, 1), (53, 1), (57, 1)] }, { coefficient := 1, powers := [(9, 1), (19, 1), (38, 1), (54, 1), (59, 1)] }, { coefficient := -1, powers := [(9, 1), (19, 1), (47, 1), (53, 1), (54, 1)] }, { coefficient := 1, powers := [(9, 1), (33, 1), (36, 1), (38, 1), (59, 1)] }, { coefficient := -1, powers := [(9, 1), (33, 1), (36, 1), (47, 1), (53, 1)] }, { coefficient := 1, powers := [(14, 1), (19, 1), (38, 1), (48, 1), (59, 1)] }, { coefficient := -1, powers := [(14, 1), (19, 1), (47, 1), (48, 1), (53, 1)] }, { coefficient := 1, powers := [(14, 1), (30, 1), (36, 1), (38, 1), (59, 1)] }, { coefficient := -1, powers := [(14, 1), (30, 1), (36, 1), (47, 1), (53, 1)] }, { coefficient := -1, powers := [(19, 1), (38, 1), (42, 1), (48, 1), (59, 1)] }, { coefficient := 1, powers := [(19, 1), (42, 1), (47, 1), (48, 1), (53, 1)] }, { coefficient := -1, powers := [(30, 1), (36, 1), (38, 1), (42, 1), (59, 1)] }, { coefficient := 1, powers := [(30, 1), (36, 1), (42, 1), (47, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (54, 1)] }, { coefficient := 1, powers := [(6, 1), (33, 1)] }, { coefficient := 1, powers := [(14, 1), (24, 1)] }, { coefficient := -1, powers := [(24, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (2, 1), (36, 1), (56, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (8, 1), (35, 1), (36, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (18, 1), (29, 1), (36, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (3, 1), (24, 1), (56, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (3, 1), (30, 1), (54, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (3, 1), (33, 1), (48, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (6, 1), (19, 1), (56, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (9, 1), (19, 1), (54, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (9, 1), (33, 1), (36, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (14, 1), (19, 1), (48, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (14, 1), (30, 1), (36, 1), (56, 1)] }, { coefficient := -1, powers := [(2, 1), (19, 1), (42, 1), (48, 1), (56, 1)] }, { coefficient := -1, powers := [(2, 1), (30, 1), (36, 1), (42, 1), (56, 1)] }, { coefficient := 1, powers := [(3, 1), (8, 1), (24, 1), (35, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (8, 1), (30, 1), (35, 1), (54, 1)] }, { coefficient := 1, powers := [(3, 1), (8, 1), (33, 1), (35, 1), (48, 1)] }, { coefficient := 1, powers := [(3, 1), (18, 1), (24, 1), (29, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (18, 1), (29, 1), (30, 1), (54, 1)] }, { coefficient := 1, powers := [(3, 1), (18, 1), (29, 1), (33, 1), (48, 1)] }, { coefficient := 1, powers := [(6, 1), (8, 1), (19, 1), (35, 1), (57, 1)] }, { coefficient := 1, powers := [(6, 1), (18, 1), (19, 1), (29, 1), (57, 1)] }, { coefficient := 1, powers := [(8, 1), (9, 1), (19, 1), (35, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (9, 1), (33, 1), (35, 1), (36, 1)] }, { coefficient := 1, powers := [(8, 1), (14, 1), (19, 1), (35, 1), (48, 1)] }, { coefficient := 1, powers := [(8, 1), (14, 1), (30, 1), (35, 1), (36, 1)] }, { coefficient := -1, powers := [(8, 1), (19, 1), (35, 1), (42, 1), (48, 1)] }, { coefficient := -1, powers := [(8, 1), (30, 1), (35, 1), (36, 1), (42, 1)] }, { coefficient := 1, powers := [(9, 1), (18, 1), (19, 1), (29, 1), (54, 1)] }, { coefficient := 1, powers := [(9, 1), (18, 1), (29, 1), (33, 1), (36, 1)] }, { coefficient := 1, powers := [(14, 1), (18, 1), (19, 1), (29, 1), (48, 1)] }, { coefficient := 1, powers := [(14, 1), (18, 1), (29, 1), (30, 1), (36, 1)] }, { coefficient := -1, powers := [(18, 1), (19, 1), (29, 1), (42, 1), (48, 1)] }, { coefficient := -1, powers := [(18, 1), (29, 1), (30, 1), (36, 1), (42, 1)] }]
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
    (values : Fin 62 → R) :
    ¬ ∀ index : Fin 24,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component52.SelectedLeafB4_2.selectedHasNoCommonZero

end Krenn.Component52.SelectedLeafB4_2
