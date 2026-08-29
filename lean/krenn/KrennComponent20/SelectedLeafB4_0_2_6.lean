import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component20.SelectedLeafB4_0_2_6

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "49d0804488bdd41f61e1c63f46f802700eb9ffe7d1d20f8ba2d9968360a4ca13"
def certificateSHA256 : String := "b12212536ff12fd7bd837b8a8e3da75cc19face6f7739ad969d52b7e1635b21c"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 25 → Fin 648 := ![
  29,
  188,
  191,
  198,
  315,
  353,
  399,
  466,
  468,
  480,
  513,
  551,
  577,
  578,
  598,
  633,
  635,
  638,
  639,
  640,
  641,
  642,
  644,
  646,
  647
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 25 → SparsePoly (Fin 64) := ![
  [{ coefficient := 1, powers := [(27, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (53, 1)] }, { coefficient := 1, powers := [(29, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (52, 1)] }, { coefficient := 1, powers := [(29, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(43, 1), (53, 1)] }, { coefficient := 1, powers := [(49, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (25, 1), (40, 1)] }, { coefficient := 1, powers := [(19, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (59, 1)] }, { coefficient := 1, powers := [(13, 1), (56, 1)] }, { coefficient := 1, powers := [(19, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (27, 1), (57, 1)] }, { coefficient := 1, powers := [(9, 1), (27, 1), (42, 1)] }, { coefficient := 1, powers := [(14, 1), (27, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (53, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1)] }, { coefficient := 1, powers := [(13, 1), (29, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (35, 1)] }, { coefficient := 1, powers := [(23, 1), (43, 1)] }, { coefficient := 1, powers := [(28, 1), (43, 1)] }, { coefficient := 1, powers := [(35, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (53, 1)] }, { coefficient := 1, powers := [(29, 1), (41, 1)] }, { coefficient := 1, powers := [(29, 1), (46, 1), (49, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (27, 1), (58, 1)] }, { coefficient := 1, powers := [(3, 1), (31, 1), (55, 1)] }, { coefficient := 1, powers := [(3, 1), (34, 1), (51, 1)] }, { coefficient := 1, powers := [(27, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (43, 1), (52, 1)] }, { coefficient := 1, powers := [(24, 1), (56, 1)] }, { coefficient := 1, powers := [(29, 1), (47, 1)] }, { coefficient := 1, powers := [(35, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1)] }, { coefficient := 1, powers := [(3, 1), (33, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1)] }, { coefficient := 1, powers := [(20, 1), (54, 1)] }, { coefficient := 1, powers := [(25, 1), (42, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (48, 1)] }, { coefficient := 1, powers := [(6, 1), (30, 1)] }, { coefficient := 1, powers := [(9, 1), (25, 1)] }, { coefficient := 1, powers := [(20, 1), (48, 1)] }, { coefficient := 1, powers := [(25, 1), (39, 1)] }, { coefficient := 1, powers := [(30, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (29, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (32, 1), (56, 1)] }, { coefficient := 1, powers := [(3, 1), (35, 1), (53, 1)] }, { coefficient := 1, powers := [(23, 1), (43, 1), (53, 1)] }, { coefficient := 1, powers := [(23, 1), (49, 1), (56, 1)] }, { coefficient := 1, powers := [(29, 1), (43, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (36, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (39, 1), (54, 1)] }, { coefficient := 1, powers := [(0, 1), (42, 1), (48, 1)] }, { coefficient := 1, powers := [(3, 1), (25, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (30, 1), (54, 1)] }, { coefficient := 1, powers := [(3, 1), (33, 1), (48, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1), (57, 1)] }, { coefficient := 1, powers := [(6, 1), (30, 1), (42, 1)] }, { coefficient := 1, powers := [(6, 1), (33, 1), (39, 1)] }, { coefficient := 1, powers := [(9, 1), (20, 1), (54, 1)] }, { coefficient := 1, powers := [(9, 1), (25, 1), (42, 1)] }, { coefficient := 1, powers := [(9, 1), (33, 1), (36, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1), (48, 1)] }, { coefficient := 1, powers := [(14, 1), (25, 1), (39, 1)] }, { coefficient := 1, powers := [(14, 1), (30, 1), (36, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (41, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (47, 1), (53, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (53, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (59, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (47, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(13, 1), (24, 1), (56, 1)] }, { coefficient := 1, powers := [(13, 1), (29, 1), (47, 1)] }, { coefficient := 1, powers := [(13, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (53, 1)] }, { coefficient := 1, powers := [(19, 1), (29, 1), (41, 1)] }, { coefficient := 1, powers := [(19, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(39, 1)] }],
  [{ coefficient := 1, powers := [(40, 1)] }],
  [{ coefficient := 1, powers := [(41, 1)] }],
  [{ coefficient := 1, powers := [(54, 1)] }],
  [{ coefficient := 1, powers := [(56, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(29, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 25 → SparsePoly (Fin 64) := ![
  [{ coefficient := -1, powers := [(0, 1), (48, 1), (63, 1)] }, { coefficient := 1, powers := [(6, 1), (9, 1), (20, 1), (31, 1), (55, 1), (63, 2)] }, { coefficient := 1, powers := [(6, 1), (9, 1), (20, 1), (34, 1), (51, 1), (63, 2)] }, { coefficient := 1, powers := [(6, 1), (9, 1), (20, 1), (58, 1), (63, 1)] }, { coefficient := -1, powers := [(9, 1), (25, 1), (63, 1)] }, { coefficient := -1, powers := [(20, 1), (48, 1), (63, 1)] }, { coefficient := -1, powers := [(25, 1), (48, 1), (63, 1)] }, { coefficient := -1, powers := [(30, 1), (36, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (18, 1), (36, 1), (47, 1), (57, 1)] }, { coefficient := -1, powers := [(9, 1), (18, 1), (33, 1), (36, 1), (47, 1)] }, { coefficient := -1, powers := [(14, 1), (18, 1), (30, 1), (36, 1), (47, 1)] }, { coefficient := 1, powers := [(18, 1), (33, 1), (36, 1), (47, 1), (48, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (13, 1), (36, 1), (43, 1), (57, 1)] }, { coefficient := -1, powers := [(9, 1), (13, 1), (33, 1), (36, 1), (43, 1)] }, { coefficient := -1, powers := [(13, 1), (14, 1), (30, 1), (36, 1), (43, 1)] }, { coefficient := 1, powers := [(13, 1), (33, 1), (36, 1), (43, 1), (48, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (5, 1), (28, 1), (57, 1)] }, { coefficient := -1, powers := [(5, 1), (9, 1), (28, 1), (33, 1)] }, { coefficient := -1, powers := [(5, 1), (14, 1), (28, 1), (30, 1)] }, { coefficient := 1, powers := [(5, 1), (28, 1), (33, 1), (48, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (24, 1), (36, 1), (53, 1), (57, 1)] }, { coefficient := -1, powers := [(9, 1), (24, 1), (33, 1), (36, 1), (53, 1)] }, { coefficient := -1, powers := [(14, 1), (24, 1), (30, 1), (36, 1), (53, 1)] }, { coefficient := 1, powers := [(24, 1), (33, 1), (36, 1), (48, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (24, 1), (36, 1), (57, 1)] }, { coefficient := 1, powers := [(9, 1), (24, 1), (33, 1), (36, 1)] }, { coefficient := 1, powers := [(14, 1), (24, 1), (30, 1), (36, 1)] }, { coefficient := -1, powers := [(24, 1), (33, 1), (36, 1), (48, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (20, 1), (31, 1), (55, 1), (63, 2)] }, { coefficient := -1, powers := [(6, 1), (20, 1), (34, 1), (51, 1), (63, 2)] }, { coefficient := -1, powers := [(6, 1), (20, 1), (58, 1), (63, 1)] }, { coefficient := 1, powers := [(25, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (36, 1), (47, 1), (57, 1)] }, { coefficient := 1, powers := [(9, 1), (33, 1), (36, 1), (47, 1)] }, { coefficient := 1, powers := [(14, 1), (30, 1), (36, 1), (47, 1)] }, { coefficient := -1, powers := [(33, 1), (36, 1), (47, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (5, 1), (53, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (9, 1), (33, 1), (53, 1)] }, { coefficient := 1, powers := [(5, 1), (14, 1), (30, 1), (53, 1)] }, { coefficient := -1, powers := [(5, 1), (33, 1), (48, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (19, 1), (36, 1), (57, 1)] }, { coefficient := 1, powers := [(9, 1), (19, 1), (33, 1), (36, 1)] }, { coefficient := 1, powers := [(14, 1), (19, 1), (30, 1), (36, 1)] }, { coefficient := -1, powers := [(19, 1), (33, 1), (36, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (20, 1), (57, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (13, 1), (36, 1), (57, 1)] }, { coefficient := 1, powers := [(9, 1), (13, 1), (33, 1), (36, 1)] }, { coefficient := 1, powers := [(13, 1), (14, 1), (30, 1), (36, 1)] }, { coefficient := -1, powers := [(13, 1), (33, 1), (36, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(48, 1)] }],
  [{ coefficient := 1, powers := [(42, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (5, 1), (57, 1)] }, { coefficient := -1, powers := [(5, 1), (9, 1), (33, 1)] }, { coefficient := -1, powers := [(5, 1), (14, 1), (30, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (48, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(0, 1), (36, 1), (57, 1)] }, { coefficient := -1, powers := [(9, 1), (33, 1), (36, 1)] }, { coefficient := -1, powers := [(14, 1), (30, 1), (36, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (36, 1), (38, 1), (57, 1), (59, 1)] }, { coefficient := 1, powers := [(9, 1), (33, 1), (36, 1), (38, 1), (59, 1)] }, { coefficient := 1, powers := [(14, 1), (30, 1), (36, 1), (38, 1), (59, 1)] }, { coefficient := -1, powers := [(33, 1), (36, 1), (38, 1), (48, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (14, 1), (20, 1), (27, 1), (31, 1), (55, 1), (63, 2)] }, { coefficient := 1, powers := [(6, 1), (14, 1), (20, 1), (27, 1), (34, 1), (51, 1), (63, 2)] }, { coefficient := 1, powers := [(6, 1), (14, 1), (20, 1), (27, 1), (58, 1), (63, 1)] }, { coefficient := 1, powers := [(6, 1), (33, 1)] }, { coefficient := -1, powers := [(14, 1), (25, 1), (27, 1), (63, 1)] }, { coefficient := 1, powers := [(14, 1), (25, 1)] }, { coefficient := -1, powers := [(25, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (19, 1), (24, 1), (25, 1), (36, 1), (53, 1), (57, 1)] }, { coefficient := 1, powers := [(9, 1), (19, 1), (24, 1), (25, 1), (33, 1), (36, 1), (53, 1)] }, { coefficient := 1, powers := [(14, 1), (19, 1), (24, 1), (25, 1), (30, 1), (36, 1), (53, 1)] }, { coefficient := -1, powers := [(19, 1), (24, 1), (25, 1), (33, 1), (36, 1), (48, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (8, 1), (35, 1), (36, 1), (57, 1)] }, { coefficient := 1, powers := [(8, 1), (9, 1), (33, 1), (35, 1), (36, 1)] }, { coefficient := 1, powers := [(8, 1), (14, 1), (30, 1), (35, 1), (36, 1)] }, { coefficient := -1, powers := [(8, 1), (33, 1), (35, 1), (36, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (39, 1)] }, { coefficient := 1, powers := [(3, 1), (30, 1)] }, { coefficient := 1, powers := [(9, 1), (20, 1)] }, { coefficient := -1, powers := [(20, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (2, 1), (36, 1), (41, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (3, 1), (5, 1), (32, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (5, 1), (23, 1), (49, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (5, 1), (28, 1), (49, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (5, 1), (32, 1), (36, 1), (57, 1)] }, { coefficient := -1, powers := [(0, 1), (13, 1), (24, 1), (36, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (9, 1), (33, 1), (36, 1), (41, 1)] }, { coefficient := 1, powers := [(2, 1), (14, 1), (30, 1), (36, 1), (41, 1)] }, { coefficient := -1, powers := [(2, 1), (33, 1), (36, 1), (41, 1), (48, 1)] }, { coefficient := 1, powers := [(3, 1), (5, 1), (9, 1), (32, 1), (33, 1)] }, { coefficient := 1, powers := [(3, 1), (5, 1), (14, 1), (30, 1), (32, 1)] }, { coefficient := -1, powers := [(3, 1), (5, 1), (32, 1), (33, 1), (48, 1)] }, { coefficient := 1, powers := [(5, 1), (9, 1), (23, 1), (33, 1), (49, 1)] }, { coefficient := 1, powers := [(5, 1), (9, 1), (28, 1), (33, 1), (49, 1)] }, { coefficient := 1, powers := [(5, 1), (9, 1), (32, 1), (33, 1), (36, 1)] }, { coefficient := 1, powers := [(5, 1), (14, 1), (23, 1), (30, 1), (49, 1)] }, { coefficient := 1, powers := [(5, 1), (14, 1), (28, 1), (30, 1), (49, 1)] }, { coefficient := 1, powers := [(5, 1), (14, 1), (30, 1), (32, 1), (36, 1)] }, { coefficient := -1, powers := [(5, 1), (23, 1), (33, 1), (48, 1), (49, 1)] }, { coefficient := -1, powers := [(5, 1), (28, 1), (33, 1), (48, 1), (49, 1)] }, { coefficient := -1, powers := [(5, 1), (32, 1), (33, 1), (36, 1), (48, 1)] }, { coefficient := -1, powers := [(9, 1), (13, 1), (24, 1), (33, 1), (36, 1)] }, { coefficient := -1, powers := [(13, 1), (14, 1), (24, 1), (30, 1), (36, 1)] }, { coefficient := 1, powers := [(13, 1), (24, 1), (33, 1), (36, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1), (48, 1)] }, { coefficient := 1, powers := [(3, 1), (6, 1), (20, 1), (31, 1), (55, 1), (57, 1), (63, 1)] }, { coefficient := 1, powers := [(3, 1), (6, 1), (20, 1), (34, 1), (51, 1), (57, 1), (63, 1)] }, { coefficient := -1, powers := [(3, 1), (25, 1), (57, 1)] }, { coefficient := -1, powers := [(6, 1), (20, 1), (57, 1)] }, { coefficient := 1, powers := [(20, 1), (42, 1), (48, 1)] }, { coefficient := 1, powers := [(25, 1), (42, 1), (48, 1)] }, { coefficient := 1, powers := [(30, 1), (36, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (3, 1), (5, 1), (57, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (5, 1), (36, 1), (57, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (5, 1), (43, 1), (49, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (13, 1), (36, 1), (43, 1), (46, 1), (57, 1)] }, { coefficient := -1, powers := [(0, 1), (13, 1), (36, 1), (47, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (18, 1), (36, 1), (47, 1), (49, 1), (57, 1)] }, { coefficient := -1, powers := [(0, 1), (19, 1), (36, 1), (46, 1), (49, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (5, 1), (9, 1), (33, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (5, 1), (14, 1), (30, 1), (59, 1)] }, { coefficient := -1, powers := [(3, 1), (5, 1), (33, 1), (48, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (9, 1), (33, 1), (36, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (9, 1), (33, 1), (43, 1), (49, 1)] }, { coefficient := 1, powers := [(5, 1), (14, 1), (30, 1), (36, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (14, 1), (30, 1), (43, 1), (49, 1)] }, { coefficient := -1, powers := [(5, 1), (33, 1), (36, 1), (48, 1), (59, 1)] }, { coefficient := -1, powers := [(5, 1), (33, 1), (43, 1), (48, 1), (49, 1)] }, { coefficient := 1, powers := [(9, 1), (13, 1), (33, 1), (36, 1), (43, 1), (46, 1)] }, { coefficient := -1, powers := [(9, 1), (13, 1), (33, 1), (36, 1), (47, 1)] }, { coefficient := 1, powers := [(9, 1), (18, 1), (33, 1), (36, 1), (47, 1), (49, 1)] }, { coefficient := -1, powers := [(9, 1), (19, 1), (33, 1), (36, 1), (46, 1), (49, 1)] }, { coefficient := 1, powers := [(13, 1), (14, 1), (30, 1), (36, 1), (43, 1), (46, 1)] }, { coefficient := -1, powers := [(13, 1), (14, 1), (30, 1), (36, 1), (47, 1)] }, { coefficient := -1, powers := [(13, 1), (33, 1), (36, 1), (43, 1), (46, 1), (48, 1)] }, { coefficient := 1, powers := [(13, 1), (33, 1), (36, 1), (47, 1), (48, 1)] }, { coefficient := 1, powers := [(14, 1), (18, 1), (30, 1), (36, 1), (47, 1), (49, 1)] }, { coefficient := -1, powers := [(14, 1), (19, 1), (30, 1), (36, 1), (46, 1), (49, 1)] }, { coefficient := -1, powers := [(18, 1), (33, 1), (36, 1), (47, 1), (48, 1), (49, 1)] }, { coefficient := 1, powers := [(19, 1), (33, 1), (36, 1), (46, 1), (48, 1), (49, 1)] }]
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
    ¬ ∀ index : Fin 25,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component20.SelectedLeafB4_0_2_6.selectedHasNoCommonZero

end Krenn.Component20.SelectedLeafB4_0_2_6
