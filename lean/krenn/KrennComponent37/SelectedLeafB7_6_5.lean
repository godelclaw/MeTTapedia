import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component37.SelectedLeafB7_6_5

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "114edd2351f0475c59f17feaebea24dbf1a8bbcd31fcfdbd610129b51e935f6a"
def certificateSHA256 : String := "7255605c6bc624062a2acc71c0fff3a1563ab6c05744227a69b92147e0b28d9e"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 25 → Fin 667 := ![
  12,
  16,
  23,
  72,
  150,
  283,
  298,
  299,
  321,
  430,
  435,
  453,
  455,
  487,
  604,
  605,
  620,
  648,
  656,
  660,
  661,
  662,
  664,
  665,
  666
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 25 → SparsePoly (Fin 69) := ![
  [{ coefficient := 1, powers := [(17, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (27, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (27, 1)] }, { coefficient := 1, powers := [(27, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (44, 1), (54, 1)] }, { coefficient := 1, powers := [(22, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (46, 1)] }, { coefficient := 1, powers := [(4, 1), (35, 1)] }, { coefficient := 1, powers := [(15, 1), (22, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (52, 1)] }, { coefficient := 1, powers := [(7, 1), (32, 1)] }, { coefficient := 1, powers := [(10, 1), (27, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(7, 1), (35, 1), (40, 1)] }, { coefficient := 1, powers := [(15, 1), (27, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (46, 1)] }, { coefficient := 1, powers := [(18, 1), (28, 1), (41, 1)] }, { coefficient := 1, powers := [(18, 1), (28, 1), (46, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (52, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (52, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (57, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (41, 1)] }, { coefficient := 1, powers := [(18, 1), (46, 1)] }, { coefficient := 1, powers := [(18, 1), (52, 1)] }, { coefficient := 1, powers := [(18, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (41, 1)] }, { coefficient := 1, powers := [(29, 1), (46, 1)] }, { coefficient := 1, powers := [(29, 1), (52, 1)] }, { coefficient := 1, powers := [(29, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (37, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1)] }, { coefficient := 1, powers := [(18, 1), (28, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (60, 1)] }, { coefficient := 1, powers := [(10, 1), (46, 1)] }, { coefficient := 1, powers := [(10, 1), (57, 1)] }, { coefficient := 1, powers := [(15, 1), (41, 1)] }, { coefficient := 1, powers := [(15, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (52, 1)] }, { coefficient := 1, powers := [(22, 1), (57, 1)] }, { coefficient := 1, powers := [(27, 1), (41, 1)] }, { coefficient := 1, powers := [(27, 1), (46, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1)] }, { coefficient := 1, powers := [(35, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (41, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (45, 1)] }, { coefficient := 1, powers := [(17, 1), (28, 1), (41, 1)] }, { coefficient := 1, powers := [(17, 1), (29, 1)] }, { coefficient := 1, powers := [(18, 1), (28, 1), (45, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (41, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (41, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (46, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (52, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (38, 1), (60, 1)] }, { coefficient := 1, powers := [(1, 1), (41, 1), (57, 1)] }, { coefficient := 1, powers := [(1, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(4, 1), (27, 1), (60, 1)] }, { coefficient := 1, powers := [(4, 1), (32, 1), (57, 1)] }, { coefficient := 1, powers := [(4, 1), (35, 1), (52, 1)] }, { coefficient := 1, powers := [(7, 1), (22, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (32, 1), (46, 1)] }, { coefficient := 1, powers := [(7, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(10, 1), (22, 1), (57, 1)] }, { coefficient := 1, powers := [(10, 1), (27, 1), (46, 1)] }, { coefficient := 1, powers := [(10, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(15, 1), (22, 1), (52, 1)] }, { coefficient := 1, powers := [(15, 1), (27, 1), (41, 1)] }, { coefficient := 1, powers := [(15, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (64, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(40, 1), (65, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(41, 1), (66, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(56, 1), (67, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(57, 1)] }],
  [{ coefficient := 1, powers := [(58, 1), (68, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 25 → SparsePoly (Fin 69) := ![
  [{ coefficient := 1, powers := [(7, 1), (27, 1), (28, 1), (41, 1), (60, 1), (64, 1), (65, 1), (66, 1), (67, 1)] }, { coefficient := 1, powers := [(7, 1), (27, 1), (29, 1), (60, 1), (64, 1), (65, 1), (66, 1), (67, 1)] }, { coefficient := 1, powers := [(10, 1), (27, 1), (28, 1), (41, 1), (64, 1), (65, 1), (67, 1)] }, { coefficient := 1, powers := [(10, 1), (27, 1), (29, 1), (64, 1), (65, 1), (67, 1)] }, { coefficient := 1, powers := [(15, 1), (27, 1), (28, 1), (41, 1), (64, 1), (65, 1), (67, 1)] }, { coefficient := 1, powers := [(15, 1), (27, 1), (29, 1), (64, 1), (65, 1), (67, 1)] }],
  [{ coefficient := -1, powers := [(1, 1), (23, 1), (38, 1), (60, 1), (64, 1), (65, 1)] }, { coefficient := 1, powers := [(1, 1), (23, 1), (46, 1), (52, 1), (64, 1), (65, 1)] }, { coefficient := 1, powers := [(1, 1), (28, 1), (37, 1), (52, 2), (60, 1), (64, 1), (65, 1)] }, { coefficient := -1, powers := [(1, 1), (28, 1), (38, 1), (60, 1), (64, 1), (65, 1)] }, { coefficient := -1, powers := [(1, 1), (29, 1), (37, 1), (52, 1), (60, 1), (64, 1), (65, 1)] }, { coefficient := 1, powers := [(1, 1), (29, 1), (46, 1), (64, 1), (65, 1)] }, { coefficient := 1, powers := [(7, 1), (27, 1), (28, 1), (45, 1), (60, 1), (64, 1), (65, 1), (66, 1), (67, 1)] }, { coefficient := 1, powers := [(7, 1), (27, 1), (29, 1), (56, 1), (60, 1), (64, 1), (65, 1), (66, 1), (67, 1)] }, { coefficient := 1, powers := [(10, 1), (23, 1), (32, 1), (38, 1), (64, 1), (65, 1)] }, { coefficient := 1, powers := [(10, 1), (27, 1), (28, 1), (45, 1), (64, 1), (65, 1), (67, 1)] }, { coefficient := -2, powers := [(10, 1), (27, 1), (28, 1), (52, 1), (64, 1), (65, 1)] }, { coefficient := 1, powers := [(10, 1), (27, 1), (29, 1), (56, 1), (64, 1), (65, 1), (67, 1)] }, { coefficient := 2, powers := [(10, 1), (27, 1), (29, 1), (64, 1), (65, 1)] }, { coefficient := -1, powers := [(10, 1), (28, 1), (32, 1), (37, 1), (52, 2), (64, 1), (65, 1)] }, { coefficient := 1, powers := [(10, 1), (28, 1), (32, 1), (38, 1), (64, 1), (65, 1)] }, { coefficient := 1, powers := [(10, 1), (29, 1), (32, 1), (37, 1), (52, 1), (64, 1), (65, 1)] }, { coefficient := 1, powers := [(15, 1), (23, 1), (27, 1), (52, 1), (64, 1), (65, 1)] }, { coefficient := -1, powers := [(15, 1), (23, 1), (32, 1), (38, 1), (64, 1), (65, 1)] }, { coefficient := 1, powers := [(15, 1), (27, 1), (28, 1), (45, 1), (64, 1), (65, 1), (67, 1)] }, { coefficient := 1, powers := [(15, 1), (27, 1), (29, 1), (56, 1), (64, 1), (65, 1), (67, 1)] }, { coefficient := 1, powers := [(15, 1), (27, 1), (29, 1), (64, 1), (65, 1)] }, { coefficient := 1, powers := [(15, 1), (28, 1), (32, 1), (37, 1), (52, 2), (64, 1), (65, 1)] }, { coefficient := -1, powers := [(15, 1), (28, 1), (32, 1), (38, 1), (64, 1), (65, 1)] }, { coefficient := -1, powers := [(15, 1), (29, 1), (32, 1), (37, 1), (52, 1), (64, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (44, 1), (60, 1), (68, 1)] }, { coefficient := 1, powers := [(10, 1), (44, 1), (52, 1), (68, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (60, 1), (65, 1), (66, 1), (67, 1)] }, { coefficient := -1, powers := [(10, 1), (65, 1), (67, 1)] }, { coefficient := -1, powers := [(15, 1), (65, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (45, 1), (60, 1), (65, 1), (66, 1), (67, 1)] }, { coefficient := 1, powers := [(10, 1), (45, 1), (65, 1), (67, 1)] }, { coefficient := 1, powers := [(15, 1), (45, 1), (65, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (60, 1), (68, 1)] }, { coefficient := -1, powers := [(10, 1), (52, 1), (68, 1)] }],
  [{ coefficient := 1, powers := [(52, 1)] }],
  [{ coefficient := 1, powers := [(46, 1)] }],
  [{ coefficient := 1, powers := [(41, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (37, 1), (52, 1), (60, 1), (64, 1)] }, { coefficient := -2, powers := [(10, 1), (27, 1), (64, 1)] }, { coefficient := -1, powers := [(10, 1), (32, 1), (37, 1), (52, 1), (64, 1)] }, { coefficient := 1, powers := [(15, 1), (32, 1), (37, 1), (52, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(1, 1), (46, 1), (64, 1)] }, { coefficient := -1, powers := [(15, 1), (27, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(1, 1), (28, 1), (37, 1), (52, 1), (60, 1), (64, 1)] }, { coefficient := 2, powers := [(10, 1), (27, 1), (28, 1), (64, 1)] }, { coefficient := 1, powers := [(10, 1), (28, 1), (32, 1), (37, 1), (52, 1), (64, 1)] }, { coefficient := -1, powers := [(15, 1), (28, 1), (32, 1), (37, 1), (52, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (18, 1), (37, 1), (60, 1), (64, 1)] }, { coefficient := -1, powers := [(10, 1), (18, 1), (32, 1), (37, 1), (64, 1)] }, { coefficient := 1, powers := [(15, 1), (18, 1), (32, 1), (37, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (38, 1), (60, 1), (64, 1)] }, { coefficient := -1, powers := [(10, 1), (32, 1), (38, 1), (64, 1)] }, { coefficient := 1, powers := [(15, 1), (32, 1), (38, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(27, 1)] }],
  [{ coefficient := 1, powers := [(10, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (27, 1), (60, 1), (64, 1), (66, 1), (67, 1)] }, { coefficient := -1, powers := [(10, 1), (27, 1), (64, 1), (67, 1)] }, { coefficient := -1, powers := [(15, 1), (27, 1), (64, 1), (67, 1)] }],
  [{ coefficient := -1, powers := [(1, 1), (37, 1), (60, 1), (64, 1)] }, { coefficient := 1, powers := [(10, 1), (32, 1), (37, 1), (64, 1)] }, { coefficient := -1, powers := [(15, 1), (32, 1), (37, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(1, 1), (38, 1), (60, 1)] }, { coefficient := 1, powers := [(1, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(7, 1), (27, 1), (41, 1), (56, 1), (60, 1), (66, 1), (67, 1)] }, { coefficient := 1, powers := [(7, 1), (27, 1), (45, 1), (60, 1), (66, 1), (67, 1)] }, { coefficient := 1, powers := [(10, 1), (27, 1), (41, 1), (56, 1), (67, 1)] }, { coefficient := 1, powers := [(10, 1), (27, 1), (45, 1), (67, 1)] }, { coefficient := 2, powers := [(10, 1), (27, 1), (46, 1)] }, { coefficient := 1, powers := [(10, 1), (32, 1), (38, 1)] }, { coefficient := 1, powers := [(15, 1), (27, 1), (41, 1), (56, 1), (67, 1)] }, { coefficient := 1, powers := [(15, 1), (27, 1), (45, 1), (67, 1)] }, { coefficient := 1, powers := [(15, 1), (27, 1), (52, 1)] }, { coefficient := -1, powers := [(15, 1), (32, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (18, 1), (23, 1), (38, 1), (60, 1), (64, 1)] }, { coefficient := -1, powers := [(1, 1), (18, 1), (23, 1), (46, 1), (52, 1), (64, 1)] }, { coefficient := -1, powers := [(1, 1), (18, 1), (28, 1), (37, 1), (52, 2), (60, 1), (64, 1)] }, { coefficient := 1, powers := [(1, 1), (18, 1), (28, 1), (38, 1), (60, 1), (64, 1)] }, { coefficient := 1, powers := [(1, 1), (18, 1), (29, 1), (37, 1), (52, 1), (60, 1), (64, 1)] }, { coefficient := -1, powers := [(1, 1), (18, 1), (29, 1), (46, 1), (64, 1)] }, { coefficient := -1, powers := [(7, 1), (17, 1), (27, 1), (28, 1), (41, 1), (60, 1), (64, 1), (66, 1), (67, 1)] }, { coefficient := -1, powers := [(7, 1), (17, 1), (27, 1), (29, 1), (60, 1), (64, 1), (66, 1), (67, 1)] }, { coefficient := -1, powers := [(7, 1), (18, 1), (27, 1), (28, 1), (45, 1), (60, 1), (64, 1), (66, 1), (67, 1)] }, { coefficient := -1, powers := [(7, 1), (18, 1), (27, 1), (29, 1), (56, 1), (60, 1), (64, 1), (66, 1), (67, 1)] }, { coefficient := -1, powers := [(7, 1), (27, 1), (45, 1), (60, 1), (66, 1), (67, 1)] }, { coefficient := -1, powers := [(7, 1), (35, 1), (41, 1)] }, { coefficient := -1, powers := [(10, 1), (17, 1), (27, 1), (28, 1), (41, 1), (64, 1), (67, 1)] }, { coefficient := -1, powers := [(10, 1), (17, 1), (27, 1), (29, 1), (64, 1), (67, 1)] }, { coefficient := -1, powers := [(10, 1), (18, 1), (23, 1), (32, 1), (38, 1), (64, 1)] }, { coefficient := -1, powers := [(10, 1), (18, 1), (27, 1), (28, 1), (45, 1), (64, 1), (67, 1)] }, { coefficient := 2, powers := [(10, 1), (18, 1), (27, 1), (28, 1), (52, 1), (64, 1)] }, { coefficient := -1, powers := [(10, 1), (18, 1), (27, 1), (29, 1), (56, 1), (64, 1), (67, 1)] }, { coefficient := -2, powers := [(10, 1), (18, 1), (27, 1), (29, 1), (64, 1)] }, { coefficient := 1, powers := [(10, 1), (18, 1), (28, 1), (32, 1), (37, 1), (52, 2), (64, 1)] }, { coefficient := -1, powers := [(10, 1), (18, 1), (28, 1), (32, 1), (38, 1), (64, 1)] }, { coefficient := -1, powers := [(10, 1), (18, 1), (29, 1), (32, 1), (37, 1), (52, 1), (64, 1)] }, { coefficient := -1, powers := [(10, 1), (27, 1), (45, 1), (67, 1)] }, { coefficient := -1, powers := [(15, 1), (17, 1), (27, 1), (28, 1), (41, 1), (64, 1), (67, 1)] }, { coefficient := -1, powers := [(15, 1), (17, 1), (27, 1), (29, 1), (64, 1), (67, 1)] }, { coefficient := -1, powers := [(15, 1), (18, 1), (23, 1), (27, 1), (52, 1), (64, 1)] }, { coefficient := 1, powers := [(15, 1), (18, 1), (23, 1), (32, 1), (38, 1), (64, 1)] }, { coefficient := -1, powers := [(15, 1), (18, 1), (27, 1), (28, 1), (45, 1), (64, 1), (67, 1)] }, { coefficient := -1, powers := [(15, 1), (18, 1), (27, 1), (29, 1), (56, 1), (64, 1), (67, 1)] }, { coefficient := -1, powers := [(15, 1), (18, 1), (27, 1), (29, 1), (64, 1)] }, { coefficient := -1, powers := [(15, 1), (18, 1), (28, 1), (32, 1), (37, 1), (52, 2), (64, 1)] }, { coefficient := 1, powers := [(15, 1), (18, 1), (28, 1), (32, 1), (38, 1), (64, 1)] }, { coefficient := 1, powers := [(15, 1), (18, 1), (29, 1), (32, 1), (37, 1), (52, 1), (64, 1)] }, { coefficient := -1, powers := [(15, 1), (27, 1), (41, 1)] }, { coefficient := -1, powers := [(15, 1), (27, 1), (45, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (27, 1), (56, 1), (60, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (27, 1), (60, 1)] }, { coefficient := 1, powers := [(10, 1), (27, 1), (41, 1)] }, { coefficient := 1, powers := [(15, 1), (27, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (2, 1), (37, 1), (41, 1), (60, 1), (64, 1)] }, { coefficient := 1, powers := [(1, 1), (18, 1), (23, 1), (46, 1), (64, 1)] }, { coefficient := 1, powers := [(1, 1), (18, 1), (28, 1), (37, 1), (52, 1), (60, 1), (64, 1)] }, { coefficient := -1, powers := [(1, 1), (40, 1), (41, 1), (65, 1)] }, { coefficient := 1, powers := [(1, 1), (41, 1)] }, { coefficient := -1, powers := [(2, 1), (10, 1), (32, 1), (37, 1), (41, 1), (64, 1)] }, { coefficient := 1, powers := [(2, 1), (15, 1), (32, 1), (37, 1), (41, 1), (64, 1)] }, { coefficient := 1, powers := [(4, 1), (32, 1)] }, { coefficient := -2, powers := [(10, 1), (18, 1), (27, 1), (28, 1), (64, 1)] }, { coefficient := -1, powers := [(10, 1), (18, 1), (28, 1), (32, 1), (37, 1), (52, 1), (64, 1)] }, { coefficient := -1, powers := [(10, 1), (27, 1)] }, { coefficient := 1, powers := [(15, 1), (18, 1), (23, 1), (27, 1), (64, 1)] }, { coefficient := 1, powers := [(15, 1), (18, 1), (28, 1), (32, 1), (37, 1), (52, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (22, 1), (60, 1)] }, { coefficient := 1, powers := [(10, 1), (22, 1), (52, 1)] }]
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
    ¬ ∀ index : Fin 25,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component37.SelectedLeafB7_6_5.selectedHasNoCommonZero

end Krenn.Component37.SelectedLeafB7_6_5
