import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component55.SelectedLeafB6_1

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "a9ac16effd891717829e108b625cc86674d21b6802a6f8f1bb8e0682ea2f66aa"
def certificateSHA256 : String := "be1ec5150a208dcf4e9aebfb72f3dd8c8b1b40fc798157a17c4f6799f4b5b3da"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 39 → Fin 590 := ![
  8,
  21,
  24,
  25,
  33,
  223,
  227,
  228,
  232,
  233,
  234,
  251,
  256,
  257,
  296,
  337,
  341,
  342,
  345,
  348,
  354,
  360,
  361,
  362,
  366,
  376,
  390,
  490,
  513,
  531,
  542,
  543,
  560,
  583,
  584,
  585,
  586,
  588,
  589
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 39 → SparsePoly (Fin 61) := ![
  [{ coefficient := 1, powers := [(7, 1), (32, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (29, 1)] }],
  [{ coefficient := 1, powers := [(28, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (20, 1)] }, { coefficient := 1, powers := [(18, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (48, 1)] }, { coefficient := 1, powers := [(25, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (49, 1)] }, { coefficient := 1, powers := [(21, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (49, 1)] }, { coefficient := 1, powers := [(24, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(26, 1), (40, 1)] }, { coefficient := 1, powers := [(26, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (40, 1)] }, { coefficient := 1, powers := [(29, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (27, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (21, 1), (56, 1)] }, { coefficient := 1, powers := [(21, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (24, 1), (56, 1)] }, { coefficient := 1, powers := [(24, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (25, 1), (44, 1)] }, { coefficient := 1, powers := [(18, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (48, 1)] }, { coefficient := 1, powers := [(20, 1), (48, 1)] }, { coefficient := 1, powers := [(25, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (46, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (51, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1)] }, { coefficient := 1, powers := [(13, 1), (29, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (56, 1)] }, { coefficient := 1, powers := [(18, 1), (21, 1), (49, 1)] }, { coefficient := 1, powers := [(18, 1), (21, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (56, 1)] }, { coefficient := 1, powers := [(18, 1), (26, 1), (40, 1)] }, { coefficient := 1, powers := [(18, 1), (26, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (44, 1)] }, { coefficient := 1, powers := [(13, 1), (53, 1)] }, { coefficient := 1, powers := [(18, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (45, 1)] }, { coefficient := 1, powers := [(19, 1), (40, 1)] }, { coefficient := 1, powers := [(19, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (51, 1)] }, { coefficient := 1, powers := [(29, 1), (41, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (54, 1)] }, { coefficient := 1, powers := [(29, 1), (46, 1)] }, { coefficient := 1, powers := [(35, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1), (48, 1)] }, { coefficient := 1, powers := [(25, 1), (44, 1), (48, 1)] }, { coefficient := 1, powers := [(48, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (41, 1), (53, 1)] }, { coefficient := 1, powers := [(7, 1), (34, 1), (41, 1)] }, { coefficient := 1, powers := [(15, 1), (28, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (56, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (41, 1), (53, 1)] }, { coefficient := 1, powers := [(21, 1), (48, 1), (53, 1)] }, { coefficient := 1, powers := [(21, 1), (50, 1)] }, { coefficient := 1, powers := [(41, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (41, 1), (53, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (53, 1)] }, { coefficient := 1, powers := [(13, 1), (24, 1), (53, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (24, 1), (57, 1)] }, { coefficient := 1, powers := [(7, 1), (32, 1), (46, 1)] }, { coefficient := 1, powers := [(7, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(16, 1), (24, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1)] }, { coefficient := 1, powers := [(6, 1), (56, 1)] }, { coefficient := 1, powers := [(25, 1), (40, 1)] }, { coefficient := 1, powers := [(25, 1), (44, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (49, 1)] }, { coefficient := 1, powers := [(3, 1), (56, 1)] }, { coefficient := 1, powers := [(20, 1), (49, 1)] }, { coefficient := 1, powers := [(20, 1), (53, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (36, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1)] }, { coefficient := 1, powers := [(3, 1), (25, 1), (56, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1), (56, 1)] }, { coefficient := 1, powers := [(20, 1)] }, { coefficient := 1, powers := [(25, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (41, 1), (54, 1)] }, { coefficient := 1, powers := [(2, 1), (46, 1), (51, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (51, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (57, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (46, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(13, 1), (24, 1), (54, 1)] }, { coefficient := 1, powers := [(13, 1), (29, 1), (46, 1)] }, { coefficient := 1, powers := [(13, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (51, 1)] }, { coefficient := 1, powers := [(19, 1), (29, 1), (41, 1)] }, { coefficient := 1, powers := [(19, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (58, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1), (59, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(40, 1)] }],
  [{ coefficient := 1, powers := [(41, 1), (60, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 39 → SparsePoly (Fin 61) := ![
  [{ coefficient := 1, powers := [(8, 1), (20, 2), (34, 1), (46, 1), (53, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (20, 2), (34, 1), (50, 1), (53, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(20, 2), (45, 1), (51, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(20, 2), (46, 1), (50, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (15, 1), (20, 2), (29, 1), (53, 1), (57, 1), (59, 1), (60, 1)] }, { coefficient := -1, powers := [(8, 1), (15, 1), (20, 2), (24, 1), (53, 1), (57, 1), (59, 1), (60, 1)] }, { coefficient := -1, powers := [(8, 1), (15, 1), (20, 2), (35, 1), (53, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(20, 2), (24, 1), (48, 1), (53, 1), (54, 1), (58, 2)] }],
  [{ coefficient := 1, powers := [(3, 1), (20, 1), (53, 2), (56, 1), (60, 1)] }, { coefficient := -1, powers := [(3, 1), (56, 1), (58, 1), (60, 1)] }, { coefficient := 1, powers := [(20, 1), (53, 2), (60, 1)] }, { coefficient := -1, powers := [(58, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (18, 1), (20, 1), (32, 1), (36, 1), (53, 2), (54, 1)] }, { coefficient := -1, powers := [(0, 1), (18, 1), (20, 1), (35, 1), (36, 1), (51, 1), (53, 2)] }, { coefficient := 1, powers := [(0, 1), (18, 1), (32, 1), (36, 1), (54, 1), (58, 1)] }, { coefficient := 1, powers := [(0, 1), (18, 1), (35, 1), (36, 1), (51, 1), (58, 1)] }, { coefficient := -1, powers := [(3, 1), (18, 1), (20, 1), (32, 1), (53, 1), (54, 1)] }, { coefficient := -1, powers := [(3, 1), (18, 1), (20, 1), (32, 1), (54, 1), (58, 1)] }, { coefficient := -1, powers := [(3, 1), (18, 1), (20, 1), (35, 1), (51, 1), (53, 1)] }, { coefficient := -1, powers := [(3, 1), (18, 1), (20, 1), (35, 1), (51, 1), (58, 1)] }, { coefficient := -1, powers := [(6, 1), (18, 1), (20, 2), (32, 1), (53, 2), (54, 1)] }, { coefficient := -1, powers := [(6, 1), (18, 1), (20, 2), (35, 1), (51, 1), (53, 2)] }, { coefficient := 1, powers := [(6, 1), (18, 1), (20, 1), (32, 1), (54, 1), (58, 1)] }, { coefficient := 1, powers := [(6, 1), (18, 1), (20, 1), (35, 1), (51, 1), (58, 1)] }, { coefficient := -1, powers := [(7, 1), (18, 1), (20, 2), (27, 1), (29, 1), (53, 1), (57, 1), (59, 1)] }, { coefficient := -1, powers := [(20, 2), (50, 1), (58, 1), (60, 1)] }, { coefficient := -1, powers := [(20, 1), (50, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(19, 1), (20, 2), (51, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (18, 1), (20, 1), (32, 1), (36, 1), (46, 1), (53, 2)] }, { coefficient := -1, powers := [(0, 1), (18, 1), (20, 1), (35, 1), (36, 1), (41, 1), (53, 2)] }, { coefficient := 1, powers := [(0, 1), (18, 1), (32, 1), (36, 1), (46, 1), (58, 1)] }, { coefficient := 1, powers := [(0, 1), (18, 1), (35, 1), (36, 1), (41, 1), (58, 1)] }, { coefficient := -1, powers := [(3, 1), (18, 1), (20, 1), (32, 1), (46, 1), (53, 1)] }, { coefficient := -1, powers := [(3, 1), (18, 1), (20, 1), (32, 1), (46, 1), (58, 1)] }, { coefficient := -1, powers := [(3, 1), (18, 1), (20, 1), (35, 1), (41, 1), (53, 1)] }, { coefficient := -1, powers := [(3, 1), (18, 1), (20, 1), (35, 1), (41, 1), (58, 1)] }, { coefficient := -1, powers := [(6, 1), (18, 1), (20, 2), (32, 1), (46, 1), (53, 2)] }, { coefficient := -1, powers := [(6, 1), (18, 1), (20, 2), (35, 1), (41, 1), (53, 2)] }, { coefficient := 1, powers := [(6, 1), (18, 1), (20, 1), (32, 1), (46, 1), (58, 1)] }, { coefficient := 1, powers := [(6, 1), (18, 1), (20, 1), (35, 1), (41, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (20, 2), (46, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (20, 2), (29, 1), (53, 1), (57, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (20, 1), (48, 1), (53, 2), (56, 1), (60, 1)] }, { coefficient := 1, powers := [(3, 1), (48, 1), (56, 1), (58, 1), (60, 1)] }, { coefficient := -1, powers := [(20, 2), (48, 1), (49, 1), (53, 1), (58, 1), (60, 1)] }, { coefficient := -1, powers := [(20, 2), (48, 1), (53, 2), (58, 1), (60, 1)] }, { coefficient := -1, powers := [(20, 1), (48, 1), (49, 1), (53, 1), (60, 1)] }, { coefficient := -2, powers := [(20, 1), (48, 1), (53, 2), (60, 1)] }, { coefficient := 1, powers := [(48, 1), (58, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(13, 1), (20, 2), (53, 1), (54, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(20, 2), (24, 1), (53, 1), (54, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (20, 2), (24, 1), (53, 1), (54, 1), (58, 2)] }],
  [{ coefficient := 1, powers := [(20, 2), (51, 1), (53, 2)] }],
  [{ coefficient := 1, powers := [(20, 2), (46, 1), (53, 2)] }],
  [{ coefficient := 1, powers := [(0, 1), (20, 1), (32, 1), (36, 1), (53, 2), (54, 1)] }, { coefficient := 1, powers := [(0, 1), (20, 1), (35, 1), (36, 1), (51, 1), (53, 2)] }, { coefficient := -1, powers := [(0, 1), (32, 1), (36, 1), (54, 1), (58, 1)] }, { coefficient := -1, powers := [(0, 1), (35, 1), (36, 1), (51, 1), (58, 1)] }, { coefficient := 1, powers := [(3, 1), (20, 1), (32, 1), (53, 1), (54, 1)] }, { coefficient := 1, powers := [(3, 1), (20, 1), (32, 1), (54, 1), (58, 1)] }, { coefficient := 1, powers := [(3, 1), (20, 1), (35, 1), (51, 1), (53, 1)] }, { coefficient := 1, powers := [(3, 1), (20, 1), (35, 1), (51, 1), (58, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 2), (32, 1), (53, 2), (54, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 2), (35, 1), (51, 1), (53, 2)] }, { coefficient := -1, powers := [(6, 1), (20, 1), (32, 1), (54, 1), (58, 1)] }, { coefficient := -1, powers := [(6, 1), (20, 1), (35, 1), (51, 1), (58, 1)] }, { coefficient := 1, powers := [(7, 1), (20, 2), (27, 1), (29, 1), (53, 1), (57, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (20, 1), (32, 1), (36, 1), (46, 1), (53, 2)] }, { coefficient := 1, powers := [(0, 1), (20, 1), (35, 1), (36, 1), (41, 1), (53, 2)] }, { coefficient := -1, powers := [(0, 1), (32, 1), (36, 1), (46, 1), (58, 1)] }, { coefficient := -1, powers := [(0, 1), (35, 1), (36, 1), (41, 1), (58, 1)] }, { coefficient := 1, powers := [(3, 1), (20, 1), (32, 1), (46, 1), (53, 1)] }, { coefficient := 1, powers := [(3, 1), (20, 1), (32, 1), (46, 1), (58, 1)] }, { coefficient := 1, powers := [(3, 1), (20, 1), (35, 1), (41, 1), (53, 1)] }, { coefficient := 1, powers := [(3, 1), (20, 1), (35, 1), (41, 1), (58, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 2), (32, 1), (46, 1), (53, 2)] }, { coefficient := 1, powers := [(6, 1), (20, 2), (35, 1), (41, 1), (53, 2)] }, { coefficient := -1, powers := [(6, 1), (20, 1), (32, 1), (46, 1), (58, 1)] }, { coefficient := -1, powers := [(6, 1), (20, 1), (35, 1), (41, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (20, 2), (24, 1), (53, 1), (54, 1), (58, 1)] }, { coefficient := -1, powers := [(20, 2), (29, 1), (46, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(20, 2), (24, 1), (51, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (19, 1), (20, 1), (36, 1), (53, 2), (56, 1)] }, { coefficient := -1, powers := [(0, 1), (19, 1), (36, 1), (56, 1), (58, 1)] }, { coefficient := 1, powers := [(3, 1), (19, 1), (20, 1), (53, 1), (56, 1)] }, { coefficient := 1, powers := [(3, 1), (19, 1), (20, 1), (56, 1), (58, 1)] }, { coefficient := 1, powers := [(6, 1), (19, 1), (20, 2), (53, 2), (56, 1)] }, { coefficient := -1, powers := [(6, 1), (19, 1), (20, 1), (56, 1), (58, 1)] }, { coefficient := 1, powers := [(19, 1), (20, 2), (53, 2)] }],
  [{ coefficient := 1, powers := [(0, 1), (13, 1), (20, 1), (36, 1), (53, 2), (56, 1)] }, { coefficient := -1, powers := [(0, 1), (13, 1), (36, 1), (56, 1), (58, 1)] }, { coefficient := 1, powers := [(3, 1), (13, 1), (20, 1), (53, 1), (56, 1)] }, { coefficient := 1, powers := [(3, 1), (13, 1), (20, 1), (56, 1), (58, 1)] }, { coefficient := 1, powers := [(6, 1), (13, 1), (20, 2), (53, 2), (56, 1)] }, { coefficient := -1, powers := [(6, 1), (13, 1), (20, 1), (56, 1), (58, 1)] }, { coefficient := 1, powers := [(13, 1), (20, 2), (53, 2)] }],
  [{ coefficient := -1, powers := [(3, 1), (20, 1), (21, 1), (53, 2), (56, 1), (60, 1)] }, { coefficient := 1, powers := [(3, 1), (21, 1), (56, 1), (58, 1), (60, 1)] }, { coefficient := -1, powers := [(20, 2), (21, 1), (49, 1), (53, 1), (58, 1), (60, 1)] }, { coefficient := -1, powers := [(20, 2), (21, 1), (53, 2), (58, 1), (60, 1)] }, { coefficient := -1, powers := [(20, 1), (21, 1), (49, 1), (53, 1), (60, 1)] }, { coefficient := -2, powers := [(20, 1), (21, 1), (53, 2), (60, 1)] }, { coefficient := 1, powers := [(21, 1), (58, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (20, 2), (29, 1), (53, 1), (57, 1), (59, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (20, 2), (24, 1), (53, 1), (57, 1), (59, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (20, 2), (35, 1), (53, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (20, 1), (36, 1), (53, 2), (57, 1)] }, { coefficient := -1, powers := [(0, 1), (36, 1), (57, 1), (58, 1)] }, { coefficient := 1, powers := [(3, 1), (20, 1), (53, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (20, 1), (57, 1), (58, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 2), (53, 2), (57, 1)] }, { coefficient := -1, powers := [(6, 1), (20, 1), (57, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(20, 2), (49, 1), (58, 1), (60, 1)] }, { coefficient := 1, powers := [(20, 2), (53, 1), (58, 1), (60, 1)] }, { coefficient := 1, powers := [(20, 1), (49, 1), (60, 1)] }, { coefficient := 1, powers := [(20, 1), (53, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(20, 2), (53, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (20, 2), (34, 1), (53, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (20, 1), (21, 1), (48, 1), (53, 2), (56, 1), (60, 1)] }, { coefficient := -1, powers := [(3, 1), (21, 1), (48, 1), (56, 1), (58, 1), (60, 1)] }, { coefficient := 1, powers := [(13, 1), (20, 2), (24, 1), (53, 1), (54, 1), (58, 1)] }, { coefficient := 1, powers := [(20, 2), (21, 1), (48, 1), (49, 1), (53, 1), (58, 1), (60, 1)] }, { coefficient := 1, powers := [(20, 2), (21, 1), (48, 1), (53, 2), (58, 1), (60, 1)] }, { coefficient := 1, powers := [(20, 1), (21, 1), (48, 1), (49, 1), (53, 1), (60, 1)] }, { coefficient := 2, powers := [(20, 1), (21, 1), (48, 1), (53, 2), (60, 1)] }, { coefficient := -1, powers := [(21, 1), (48, 1), (58, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(20, 1), (53, 1)] }, { coefficient := -1, powers := [(20, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(20, 1), (53, 2)] }, { coefficient := 1, powers := [(58, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (20, 1), (36, 1), (53, 2), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (36, 1), (56, 1), (58, 1)] }, { coefficient := -1, powers := [(3, 1), (20, 1), (53, 1), (56, 1)] }, { coefficient := -1, powers := [(3, 1), (20, 1), (56, 1), (58, 1)] }, { coefficient := -1, powers := [(6, 1), (20, 2), (53, 2), (56, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1), (56, 1), (58, 1)] }, { coefficient := -1, powers := [(20, 2), (53, 2)] }],
  [{ coefficient := 1, powers := [(13, 1), (20, 2), (24, 1), (53, 2), (54, 1)] }, { coefficient := -1, powers := [(18, 1), (20, 2), (24, 1), (48, 1), (53, 1), (54, 1), (58, 1)] }, { coefficient := 1, powers := [(18, 1), (20, 2), (24, 1), (50, 1), (53, 1), (54, 1)] }, { coefficient := -1, powers := [(20, 2), (49, 1), (53, 1)] }, { coefficient := -1, powers := [(20, 2), (53, 2)] }, { coefficient := 1, powers := [(20, 1), (49, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(5, 1), (20, 2), (29, 1), (53, 2), (57, 1)] }, { coefficient := -1, powers := [(8, 1), (20, 2), (24, 1), (53, 2), (57, 1)] }, { coefficient := -1, powers := [(8, 1), (20, 2), (35, 1), (41, 1), (53, 2)] }],
  [{ coefficient := 1, powers := [(0, 1), (20, 1), (36, 1), (41, 1), (53, 2), (54, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (20, 1), (36, 1), (46, 1), (51, 1), (53, 2), (56, 1)] }, { coefficient := -1, powers := [(0, 1), (36, 1), (41, 1), (54, 1), (56, 1), (58, 1)] }, { coefficient := -1, powers := [(0, 1), (36, 1), (46, 1), (51, 1), (56, 1), (58, 1)] }, { coefficient := 1, powers := [(3, 1), (20, 1), (41, 1), (53, 1), (54, 1), (56, 1)] }, { coefficient := 1, powers := [(3, 1), (20, 1), (41, 1), (54, 1), (56, 1), (58, 1)] }, { coefficient := 1, powers := [(3, 1), (20, 1), (46, 1), (51, 1), (53, 1), (56, 1)] }, { coefficient := 1, powers := [(3, 1), (20, 1), (46, 1), (51, 1), (56, 1), (58, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 2), (41, 1), (53, 2), (54, 1), (56, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 2), (46, 1), (51, 1), (53, 2), (56, 1)] }, { coefficient := -1, powers := [(6, 1), (20, 1), (41, 1), (54, 1), (56, 1), (58, 1)] }, { coefficient := -1, powers := [(6, 1), (20, 1), (46, 1), (51, 1), (56, 1), (58, 1)] }, { coefficient := 1, powers := [(20, 2), (38, 1), (53, 2), (57, 1)] }, { coefficient := -1, powers := [(20, 2), (46, 1), (51, 1), (53, 2)] }],
  [{ coefficient := -1, powers := [(3, 1), (20, 1), (21, 1), (25, 1), (48, 1), (53, 2), (56, 1), (60, 1)] }, { coefficient := 1, powers := [(3, 1), (21, 1), (25, 1), (48, 1), (56, 1), (58, 1), (60, 1)] }, { coefficient := -1, powers := [(13, 1), (20, 2), (24, 1), (25, 1), (53, 1), (54, 1), (58, 1)] }, { coefficient := -1, powers := [(13, 1), (20, 2), (29, 1), (46, 1), (53, 1)] }, { coefficient := -1, powers := [(19, 1), (20, 2), (24, 1), (51, 1), (53, 1)] }, { coefficient := -1, powers := [(20, 2), (21, 1), (25, 1), (48, 1), (49, 1), (53, 1), (58, 1), (60, 1)] }, { coefficient := -1, powers := [(20, 2), (21, 1), (25, 1), (48, 1), (53, 2), (58, 1), (60, 1)] }, { coefficient := -1, powers := [(20, 1), (21, 1), (25, 1), (48, 1), (49, 1), (53, 1), (60, 1)] }, { coefficient := -2, powers := [(20, 1), (21, 1), (25, 1), (48, 1), (53, 2), (60, 1)] }, { coefficient := 1, powers := [(21, 1), (25, 1), (48, 1), (58, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (20, 2), (49, 1), (53, 1), (58, 1)] }, { coefficient := -1, powers := [(0, 1), (20, 2), (53, 2), (58, 1)] }, { coefficient := -1, powers := [(0, 1), (20, 1), (49, 1), (53, 1)] }, { coefficient := -1, powers := [(0, 1), (20, 1), (53, 2)] }, { coefficient := -1, powers := [(1, 1), (5, 1), (20, 2), (29, 1), (53, 2), (57, 1), (59, 1)] }, { coefficient := -1, powers := [(1, 1), (8, 1), (20, 2), (24, 1), (53, 2), (57, 1), (59, 1)] }, { coefficient := -1, powers := [(3, 1), (20, 1), (25, 1), (53, 2), (56, 1)] }, { coefficient := 1, powers := [(3, 1), (25, 1), (56, 1), (58, 1)] }, { coefficient := -1, powers := [(5, 1), (7, 1), (20, 2), (29, 1), (34, 1), (53, 1), (57, 1), (59, 1)] }, { coefficient := -1, powers := [(7, 1), (8, 1), (20, 2), (24, 1), (34, 1), (53, 1), (57, 1), (59, 1)] }, { coefficient := -1, powers := [(20, 2), (49, 1), (58, 1)] }, { coefficient := -1, powers := [(20, 2), (53, 1), (58, 1)] }, { coefficient := -1, powers := [(20, 1), (25, 1), (53, 2)] }, { coefficient := -1, powers := [(20, 1), (49, 1)] }, { coefficient := -1, powers := [(20, 1), (53, 1)] }, { coefficient := 1, powers := [(25, 1), (58, 1)] }]
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
    (values : Fin 61 → R) :
    ¬ ∀ index : Fin 39,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component55.SelectedLeafB6_1.selectedHasNoCommonZero

end Krenn.Component55.SelectedLeafB6_1
