import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component6.SelectedLeafB2

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "5511e69c5fbea62cb2977733528884f041f96d3836209958d3ff3cf3a07323d6"
def certificateSHA256 : String := "88905069baac1cf30a85f3932a9dd6e7259a7ccd5f97ff0150322dce5f758816"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 26 → Fin 606 := ![
  3,
  5,
  12,
  15,
  25,
  193,
  194,
  195,
  206,
  207,
  211,
  310,
  368,
  372,
  373,
  374,
  375,
  385,
  386,
  387,
  512,
  513,
  542,
  602,
  603,
  605
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 26 → SparsePoly (Fin 60) := ![
  [{ coefficient := 1, powers := [(5, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (55, 1)] }, { coefficient := 1, powers := [(26, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (49, 1)] }, { coefficient := 1, powers := [(25, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (51, 1)] }, { coefficient := 1, powers := [(20, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (51, 1)] }, { coefficient := 1, powers := [(24, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(26, 1), (41, 1)] }, { coefficient := 1, powers := [(26, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(41, 1), (44, 1)] }, { coefficient := 1, powers := [(44, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (19, 1), (54, 1)] }, { coefficient := 1, powers := [(13, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1)] }, { coefficient := 1, powers := [(19, 1), (44, 1)] }, { coefficient := 1, powers := [(25, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (47, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (52, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1)] }, { coefficient := 1, powers := [(13, 1), (30, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (58, 1)] }, { coefficient := 1, powers := [(13, 1), (47, 1)] }, { coefficient := 1, powers := [(18, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (58, 1)] }, { coefficient := 1, powers := [(13, 1), (55, 1)] }, { coefficient := 1, powers := [(18, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (52, 1)] }, { coefficient := 1, powers := [(30, 1), (42, 1)] }, { coefficient := 1, powers := [(33, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (55, 1)] }, { coefficient := 1, powers := [(30, 1), (47, 1)] }, { coefficient := 1, powers := [(36, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (41, 1), (55, 1)] }, { coefficient := 1, powers := [(26, 1), (41, 1), (44, 1)] }, { coefficient := 1, powers := [(55, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1)] }, { coefficient := 1, powers := [(6, 1), (57, 1)] }, { coefficient := 1, powers := [(25, 1), (41, 1)] }, { coefficient := 1, powers := [(25, 1), (46, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (51, 1)] }, { coefficient := 1, powers := [(3, 1), (57, 1)] }, { coefficient := 1, powers := [(19, 1), (51, 1)] }, { coefficient := 1, powers := [(19, 1), (54, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (37, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1)] }, { coefficient := 1, powers := [(3, 1), (25, 1), (57, 1)] }, { coefficient := 1, powers := [(6, 1), (19, 1), (57, 1)] }, { coefficient := 1, powers := [(19, 1)] }, { coefficient := 1, powers := [(25, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (39, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (42, 1), (55, 1)] }, { coefficient := 1, powers := [(2, 1), (47, 1), (52, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1), (52, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (58, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (47, 1)] }, { coefficient := 1, powers := [(8, 1), (36, 1), (42, 1)] }, { coefficient := 1, powers := [(13, 1), (24, 1), (55, 1)] }, { coefficient := 1, powers := [(13, 1), (30, 1), (47, 1)] }, { coefficient := 1, powers := [(13, 1), (36, 1), (39, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (52, 1)] }, { coefficient := 1, powers := [(18, 1), (30, 1), (42, 1)] }, { coefficient := 1, powers := [(18, 1), (33, 1), (39, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1)] }],
  [{ coefficient := 1, powers := [(2, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 26 → SparsePoly (Fin 60) := ![
  [{ coefficient := 1, powers := [(3, 1), (5, 1), (19, 1), (30, 1), (33, 1), (51, 1), (55, 1), (58, 1)] }, { coefficient := 1, powers := [(3, 1), (5, 1), (19, 1), (30, 1), (33, 1), (54, 1), (55, 1), (58, 1)] }, { coefficient := 1, powers := [(3, 1), (5, 1), (19, 1), (33, 2), (51, 1), (55, 2)] }, { coefficient := 1, powers := [(3, 1), (5, 1), (19, 1), (33, 2), (54, 1), (55, 2)] }, { coefficient := 1, powers := [(3, 1), (25, 1), (30, 1), (51, 1), (58, 1)] }, { coefficient := 1, powers := [(3, 1), (25, 1), (30, 1), (54, 1), (58, 1)] }, { coefficient := 1, powers := [(3, 1), (25, 1), (33, 1), (51, 1), (55, 1)] }, { coefficient := 1, powers := [(3, 1), (25, 1), (33, 1), (54, 1), (55, 1)] }, { coefficient := -1, powers := [(3, 1), (30, 1), (58, 1)] }, { coefficient := -1, powers := [(3, 1), (33, 1), (55, 1)] }, { coefficient := 1, powers := [(6, 1), (19, 1), (30, 1), (51, 1), (58, 1)] }, { coefficient := 1, powers := [(6, 1), (19, 1), (30, 1), (54, 1), (58, 1)] }, { coefficient := 1, powers := [(6, 1), (19, 1), (33, 1), (51, 1), (55, 1)] }, { coefficient := 1, powers := [(6, 1), (19, 1), (33, 1), (54, 1), (55, 1)] }],
  [{ coefficient := 2, powers := [(3, 1), (5, 1), (19, 1), (24, 1), (33, 1), (51, 1), (55, 1), (58, 1)] }, { coefficient := 2, powers := [(3, 1), (5, 1), (19, 1), (24, 1), (33, 1), (54, 1), (55, 1), (58, 1)] }, { coefficient := 1, powers := [(3, 1), (5, 1), (19, 1), (33, 2), (47, 1), (51, 1), (55, 1)] }, { coefficient := 1, powers := [(3, 1), (5, 1), (19, 1), (33, 2), (47, 1), (54, 1), (55, 1)] }, { coefficient := 1, powers := [(3, 1), (5, 1), (19, 1), (33, 1), (36, 1), (42, 1), (51, 1), (55, 1)] }, { coefficient := 1, powers := [(3, 1), (5, 1), (19, 1), (33, 1), (36, 1), (42, 1), (54, 1), (55, 1)] }, { coefficient := 1, powers := [(3, 1), (20, 1), (36, 1), (49, 1), (51, 1)] }, { coefficient := 1, powers := [(3, 1), (20, 1), (36, 1), (49, 1), (54, 1)] }, { coefficient := -2, powers := [(3, 1), (24, 1), (58, 1)] }, { coefficient := 1, powers := [(3, 1), (25, 1), (33, 1), (47, 1), (51, 1)] }, { coefficient := 1, powers := [(3, 1), (25, 1), (33, 1), (47, 1), (54, 1)] }, { coefficient := 1, powers := [(3, 1), (25, 1), (36, 1), (42, 1), (51, 1)] }, { coefficient := 1, powers := [(3, 1), (25, 1), (36, 1), (42, 1), (54, 1)] }, { coefficient := -1, powers := [(3, 1), (33, 1), (47, 1)] }, { coefficient := -1, powers := [(3, 1), (36, 1), (42, 1)] }, { coefficient := 2, powers := [(6, 1), (19, 1), (24, 1), (51, 1), (58, 1)] }, { coefficient := 2, powers := [(6, 1), (19, 1), (24, 1), (54, 1), (58, 1)] }, { coefficient := 1, powers := [(6, 1), (19, 1), (33, 1), (47, 1), (51, 1)] }, { coefficient := 1, powers := [(6, 1), (19, 1), (33, 1), (47, 1), (54, 1)] }, { coefficient := 1, powers := [(6, 1), (19, 1), (36, 1), (42, 1), (51, 1)] }, { coefficient := 1, powers := [(6, 1), (19, 1), (36, 1), (42, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (51, 1), (55, 1)] }, { coefficient := 1, powers := [(24, 1), (54, 1), (55, 1)] }, { coefficient := -2, powers := [(30, 1), (47, 1), (51, 1)] }, { coefficient := -2, powers := [(30, 1), (47, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (5, 1), (19, 1), (24, 1), (26, 1), (33, 1), (51, 1), (54, 1), (55, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (5, 1), (19, 1), (24, 1), (26, 1), (33, 1), (54, 2), (55, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (24, 1), (25, 1), (26, 1), (51, 1), (54, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (24, 1), (25, 1), (26, 1), (54, 2), (57, 1)] }, { coefficient := -1, powers := [(3, 1), (24, 1), (26, 1), (54, 1), (57, 1)] }, { coefficient := 1, powers := [(6, 1), (19, 1), (24, 1), (26, 1), (51, 1), (54, 1), (57, 1)] }, { coefficient := 1, powers := [(6, 1), (19, 1), (24, 1), (26, 1), (54, 2), (57, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (30, 1), (51, 1)] }, { coefficient := 1, powers := [(20, 1), (30, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (5, 1), (13, 1), (19, 1), (24, 1), (33, 1), (51, 1), (54, 1), (55, 1), (57, 1)] }, { coefficient := -1, powers := [(3, 1), (5, 1), (13, 1), (19, 1), (24, 1), (33, 1), (54, 2), (55, 1), (57, 1)] }, { coefficient := -1, powers := [(3, 1), (13, 1), (24, 1), (25, 1), (51, 1), (54, 1), (57, 1)] }, { coefficient := -1, powers := [(3, 1), (13, 1), (24, 1), (25, 1), (54, 2), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (13, 1), (24, 1), (54, 1), (57, 1)] }, { coefficient := -1, powers := [(5, 1), (6, 1), (33, 1), (51, 1), (57, 1)] }, { coefficient := -1, powers := [(5, 1), (6, 1), (33, 1), (54, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (19, 1), (33, 1), (51, 2)] }, { coefficient := 2, powers := [(5, 1), (19, 1), (33, 1), (51, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (19, 1), (33, 1), (54, 2)] }, { coefficient := 1, powers := [(5, 1), (25, 1), (33, 1), (51, 2)] }, { coefficient := 2, powers := [(5, 1), (25, 1), (33, 1), (51, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (25, 1), (33, 1), (54, 2)] }, { coefficient := -1, powers := [(5, 1), (33, 1), (51, 1)] }, { coefficient := -1, powers := [(5, 1), (33, 1), (54, 1)] }, { coefficient := -1, powers := [(6, 1), (13, 1), (19, 1), (24, 1), (51, 1), (54, 1), (57, 1)] }, { coefficient := -1, powers := [(6, 1), (13, 1), (19, 1), (24, 1), (54, 2), (57, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (36, 1), (51, 1)] }, { coefficient := 1, powers := [(8, 1), (36, 1), (54, 1)] }, { coefficient := -1, powers := [(18, 1), (30, 1), (51, 1)] }, { coefficient := -1, powers := [(18, 1), (30, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (19, 1), (36, 1), (49, 1), (51, 1)] }, { coefficient := 1, powers := [(8, 1), (19, 1), (36, 1), (49, 1), (54, 1)] }],
  [{ coefficient := -2, powers := [(8, 1), (19, 1), (25, 1), (51, 1), (58, 1)] }, { coefficient := -2, powers := [(8, 1), (19, 1), (25, 1), (54, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (25, 1), (33, 1), (44, 1), (51, 1)] }, { coefficient := -1, powers := [(5, 1), (25, 1), (33, 1), (44, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (19, 1), (26, 1), (33, 1), (51, 1)] }, { coefficient := -1, powers := [(5, 1), (19, 1), (26, 1), (33, 1), (54, 1)] }, { coefficient := -1, powers := [(5, 1), (25, 1), (26, 1), (33, 1), (51, 1)] }, { coefficient := -1, powers := [(5, 1), (25, 1), (26, 1), (33, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (5, 1), (19, 1), (24, 1), (33, 1), (51, 1), (55, 2), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (5, 1), (19, 1), (24, 1), (33, 1), (54, 1), (55, 2), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (24, 1), (25, 1), (51, 1), (55, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (24, 1), (25, 1), (54, 1), (55, 1), (57, 1)] }, { coefficient := -1, powers := [(3, 1), (24, 1), (55, 1), (57, 1)] }, { coefficient := 1, powers := [(6, 1), (19, 1), (24, 1), (51, 1), (55, 1), (57, 1)] }, { coefficient := 1, powers := [(6, 1), (19, 1), (24, 1), (54, 1), (55, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (26, 1), (33, 1), (51, 1), (54, 1)] }, { coefficient := -1, powers := [(5, 1), (26, 1), (33, 1), (54, 2)] }],
  [{ coefficient := 1, powers := [(3, 1), (5, 1), (19, 1), (33, 1), (51, 1), (52, 1), (55, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (5, 1), (19, 1), (33, 1), (52, 1), (54, 1), (55, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (25, 1), (51, 1), (52, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (25, 1), (52, 1), (54, 1), (57, 1)] }, { coefficient := -1, powers := [(3, 1), (52, 1), (57, 1)] }, { coefficient := 1, powers := [(6, 1), (19, 1), (51, 1), (52, 1), (57, 1)] }, { coefficient := 1, powers := [(6, 1), (19, 1), (52, 1), (54, 1), (57, 1)] }, { coefficient := 1, powers := [(25, 1), (51, 1), (52, 1)] }, { coefficient := 1, powers := [(25, 1), (52, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (47, 1), (51, 1)] }, { coefficient := 1, powers := [(25, 1), (47, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (30, 1), (51, 1)] }, { coefficient := 1, powers := [(25, 1), (30, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (5, 1), (19, 1), (24, 1), (33, 1), (51, 1), (55, 1), (57, 1)] }, { coefficient := -1, powers := [(3, 1), (5, 1), (19, 1), (24, 1), (33, 1), (54, 1), (55, 1), (57, 1)] }, { coefficient := -1, powers := [(3, 1), (24, 1), (25, 1), (51, 1), (57, 1)] }, { coefficient := -1, powers := [(3, 1), (24, 1), (25, 1), (54, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (24, 1), (57, 1)] }, { coefficient := -1, powers := [(6, 1), (19, 1), (24, 1), (51, 1), (57, 1)] }, { coefficient := -1, powers := [(6, 1), (19, 1), (24, 1), (54, 1), (57, 1)] }, { coefficient := -1, powers := [(24, 1), (25, 1), (51, 1)] }, { coefficient := -1, powers := [(24, 1), (25, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (5, 1), (18, 1), (19, 1), (33, 1), (51, 1), (55, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (5, 1), (18, 1), (19, 1), (33, 1), (54, 1), (55, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (18, 1), (25, 1), (51, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (18, 1), (25, 1), (54, 1), (57, 1)] }, { coefficient := -1, powers := [(3, 1), (18, 1), (57, 1)] }, { coefficient := 1, powers := [(6, 1), (18, 1), (19, 1), (51, 1), (57, 1)] }, { coefficient := 1, powers := [(6, 1), (18, 1), (19, 1), (54, 1), (57, 1)] }, { coefficient := 1, powers := [(18, 1), (25, 1), (51, 1)] }, { coefficient := 1, powers := [(18, 1), (25, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (5, 1), (13, 1), (19, 1), (33, 1), (51, 1), (55, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (5, 1), (13, 1), (19, 1), (33, 1), (54, 1), (55, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (13, 1), (25, 1), (51, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (13, 1), (25, 1), (54, 1), (57, 1)] }, { coefficient := -1, powers := [(3, 1), (13, 1), (57, 1)] }, { coefficient := 1, powers := [(6, 1), (13, 1), (19, 1), (51, 1), (57, 1)] }, { coefficient := 1, powers := [(6, 1), (13, 1), (19, 1), (54, 1), (57, 1)] }, { coefficient := 1, powers := [(13, 1), (25, 1), (51, 1)] }, { coefficient := 1, powers := [(13, 1), (25, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (19, 1), (33, 1), (51, 1)] }, { coefficient := 1, powers := [(5, 1), (19, 1), (33, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (25, 1), (33, 1), (51, 1)] }, { coefficient := 1, powers := [(5, 1), (25, 1), (33, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (26, 1), (33, 1), (44, 1), (51, 1)] }, { coefficient := 1, powers := [(5, 1), (26, 1), (33, 1), (44, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (19, 1), (33, 1), (51, 1), (55, 1)] }, { coefficient := -1, powers := [(5, 1), (19, 1), (33, 1), (54, 1), (55, 1)] }, { coefficient := -1, powers := [(5, 1), (25, 1), (33, 1), (51, 1), (55, 1)] }, { coefficient := -1, powers := [(5, 1), (25, 1), (33, 1), (54, 1), (55, 1)] }, { coefficient := -1, powers := [(8, 1), (20, 1), (36, 1), (49, 1), (51, 1)] }, { coefficient := -1, powers := [(8, 1), (20, 1), (36, 1), (49, 1), (54, 1)] }, { coefficient := 2, powers := [(8, 1), (24, 1), (25, 1), (51, 1), (58, 1)] }, { coefficient := 2, powers := [(8, 1), (24, 1), (25, 1), (54, 1), (58, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(5, 1), (33, 1), (51, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (54, 1), (55, 1)] }, { coefficient := -1, powers := [(51, 1)] }, { coefficient := -1, powers := [(54, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (5, 1), (19, 1), (33, 1), (51, 1), (55, 1), (57, 1)] }, { coefficient := -1, powers := [(3, 1), (5, 1), (19, 1), (33, 1), (54, 1), (55, 1), (57, 1)] }, { coefficient := -1, powers := [(3, 1), (25, 1), (51, 1), (57, 1)] }, { coefficient := -1, powers := [(3, 1), (25, 1), (54, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (57, 1)] }, { coefficient := -1, powers := [(6, 1), (19, 1), (51, 1), (57, 1)] }, { coefficient := -1, powers := [(6, 1), (19, 1), (54, 1), (57, 1)] }, { coefficient := -1, powers := [(25, 1), (51, 1)] }, { coefficient := -1, powers := [(25, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (19, 1), (33, 1), (41, 1), (51, 1), (55, 1)] }, { coefficient := -1, powers := [(5, 1), (19, 1), (33, 1), (41, 1), (54, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (19, 1), (33, 1), (51, 2), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (19, 1), (33, 1), (51, 1), (54, 1), (55, 1)] }, { coefficient := -1, powers := [(5, 1), (25, 1), (33, 1), (41, 1), (51, 1), (55, 1)] }, { coefficient := -1, powers := [(5, 1), (25, 1), (33, 1), (41, 1), (54, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (25, 1), (33, 1), (51, 2), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (25, 1), (33, 1), (51, 1), (54, 1), (55, 1)] }, { coefficient := -1, powers := [(5, 1), (26, 1), (33, 1), (44, 1), (46, 1), (51, 1)] }, { coefficient := -1, powers := [(5, 1), (26, 1), (33, 1), (44, 1), (46, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (26, 1), (33, 1), (44, 1), (51, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (26, 1), (33, 1), (44, 1), (54, 2)] }, { coefficient := -1, powers := [(5, 1), (33, 1), (37, 1), (51, 1), (55, 1), (57, 1)] }, { coefficient := -1, powers := [(5, 1), (33, 1), (37, 1), (54, 1), (55, 1), (57, 1)] }, { coefficient := -1, powers := [(5, 1), (33, 1), (51, 1), (55, 1)] }, { coefficient := -1, powers := [(5, 1), (33, 1), (54, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (20, 1), (36, 1), (49, 1), (51, 2)] }, { coefficient := 1, powers := [(8, 1), (20, 1), (36, 1), (49, 1), (51, 1), (54, 1)] }, { coefficient := -2, powers := [(8, 1), (24, 1), (25, 1), (51, 2), (58, 1)] }, { coefficient := -2, powers := [(8, 1), (24, 1), (25, 1), (51, 1), (54, 1), (58, 1)] }, { coefficient := 1, powers := [(37, 1), (51, 1), (57, 1)] }, { coefficient := 1, powers := [(37, 1), (54, 1), (57, 1)] }, { coefficient := 1, powers := [(54, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (5, 1), (19, 1), (33, 1), (39, 1), (51, 1), (55, 1), (57, 1), (58, 1)] }, { coefficient := 1, powers := [(3, 1), (5, 1), (19, 1), (33, 1), (39, 1), (54, 1), (55, 1), (57, 1), (58, 1)] }, { coefficient := 1, powers := [(3, 1), (5, 1), (19, 1), (33, 1), (42, 1), (51, 1), (55, 2), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (5, 1), (19, 1), (33, 1), (42, 1), (54, 1), (55, 2), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (25, 1), (39, 1), (51, 1), (57, 1), (58, 1)] }, { coefficient := 1, powers := [(3, 1), (25, 1), (39, 1), (54, 1), (57, 1), (58, 1)] }, { coefficient := 1, powers := [(3, 1), (25, 1), (42, 1), (51, 1), (55, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (25, 1), (42, 1), (54, 1), (55, 1), (57, 1)] }, { coefficient := -1, powers := [(3, 1), (39, 1), (57, 1), (58, 1)] }, { coefficient := -1, powers := [(3, 1), (42, 1), (55, 1), (57, 1)] }, { coefficient := 1, powers := [(6, 1), (19, 1), (39, 1), (51, 1), (57, 1), (58, 1)] }, { coefficient := 1, powers := [(6, 1), (19, 1), (39, 1), (54, 1), (57, 1), (58, 1)] }, { coefficient := 1, powers := [(6, 1), (19, 1), (42, 1), (51, 1), (55, 1), (57, 1)] }, { coefficient := 1, powers := [(6, 1), (19, 1), (42, 1), (54, 1), (55, 1), (57, 1)] }, { coefficient := 1, powers := [(25, 1), (39, 1), (51, 1), (58, 1)] }, { coefficient := 1, powers := [(25, 1), (39, 1), (54, 1), (58, 1)] }, { coefficient := 1, powers := [(25, 1), (42, 1), (51, 1), (55, 1)] }, { coefficient := 1, powers := [(25, 1), (42, 1), (54, 1), (55, 1)] }, { coefficient := -1, powers := [(25, 1), (47, 1), (51, 1), (52, 1)] }, { coefficient := -1, powers := [(25, 1), (47, 1), (52, 1), (54, 1)] }]
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
    (values : Fin 60 → R) :
    ¬ ∀ index : Fin 26,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component6.SelectedLeafB2.selectedHasNoCommonZero

end Krenn.Component6.SelectedLeafB2
