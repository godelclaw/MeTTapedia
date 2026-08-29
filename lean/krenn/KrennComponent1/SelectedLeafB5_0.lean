import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component1.SelectedLeafB5_0

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "409ad9856038d6190fd61d81e2f9e8ca3fb33ab0dcbdb918783be9eff47c2f58"
def certificateSHA256 : String := "3d5f0040fdea7a9fdbb7645c81c6185645dbd66cfade1034a0f03f790795091a"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 40 → Fin 588 := ![
  1,
  3,
  21,
  23,
  25,
  32,
  35,
  37,
  48,
  51,
  52,
  219,
  220,
  225,
  226,
  252,
  255,
  260,
  261,
  275,
  354,
  366,
  370,
  382,
  384,
  385,
  389,
  424,
  449,
  493,
  503,
  507,
  545,
  546,
  566,
  581,
  582,
  584,
  586,
  587
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 40 → SparsePoly (Fin 59) := ![
  [{ coefficient := 1, powers := [(3, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (29, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (30, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (20, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(28, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1)] }, { coefficient := 1, powers := [(24, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (50, 1)] }, { coefficient := 1, powers := [(20, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (49, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (36, 1)] }, { coefficient := 1, powers := [(36, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (44, 1)] }, { coefficient := 1, powers := [(14, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (20, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (53, 1)] }, { coefficient := 1, powers := [(30, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(30, 1), (41, 1)] }, { coefficient := 1, powers := [(30, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (29, 1), (55, 1)] }, { coefficient := 1, powers := [(29, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (20, 1), (52, 1)] }, { coefficient := 1, powers := [(14, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (50, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1)] }, { coefficient := 1, powers := [(14, 1), (30, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (56, 1)] }, { coefficient := 1, powers := [(14, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (45, 1)] }, { coefficient := 1, powers := [(19, 1), (41, 1)] }, { coefficient := 1, powers := [(19, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (50, 1)] }, { coefficient := 1, powers := [(30, 1), (42, 1)] }, { coefficient := 1, powers := [(33, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (53, 1)] }, { coefficient := 1, powers := [(30, 1), (47, 1)] }, { coefficient := 1, powers := [(36, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (42, 1), (53, 1)] }, { coefficient := 1, powers := [(0, 1), (47, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (30, 1), (56, 1)] }, { coefficient := 1, powers := [(3, 1), (33, 1), (53, 1)] }, { coefficient := 1, powers := [(3, 1), (36, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (23, 1), (56, 1)] }, { coefficient := 1, powers := [(6, 1), (33, 1), (47, 1)] }, { coefficient := 1, powers := [(6, 1), (36, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (24, 1), (45, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (41, 1)] }, { coefficient := 1, powers := [(19, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (47, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1)] }, { coefficient := 1, powers := [(18, 1), (28, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (23, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (56, 1)] }, { coefficient := 1, powers := [(14, 1), (25, 1), (45, 1)] }, { coefficient := 1, powers := [(14, 1), (53, 1)] }, { coefficient := 1, powers := [(19, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1)] }, { coefficient := 1, powers := [(6, 1), (55, 1)] }, { coefficient := 1, powers := [(24, 1), (41, 1)] }, { coefficient := 1, powers := [(24, 1), (44, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (49, 1)] }, { coefficient := 1, powers := [(3, 1), (55, 1)] }, { coefficient := 1, powers := [(20, 1), (49, 1)] }, { coefficient := 1, powers := [(20, 1), (52, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (45, 1), (50, 1)] }, { coefficient := 1, powers := [(8, 1), (29, 1), (56, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (45, 1)] }, { coefficient := 1, powers := [(14, 1), (29, 1), (53, 1)] }, { coefficient := 1, powers := [(14, 1), (30, 1), (45, 1)] }, { coefficient := 1, powers := [(19, 1), (29, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (42, 1), (53, 1)] }, { coefficient := 1, powers := [(2, 1), (47, 1), (50, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (53, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1), (50, 1)] }, { coefficient := 1, powers := [(8, 1), (23, 1), (56, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (47, 1)] }, { coefficient := 1, powers := [(8, 1), (36, 1), (42, 1)] }, { coefficient := 1, powers := [(14, 1), (23, 1), (53, 1)] }, { coefficient := 1, powers := [(14, 1), (30, 1), (47, 1)] }, { coefficient := 1, powers := [(14, 1), (36, 1), (39, 1)] }, { coefficient := 1, powers := [(19, 1), (23, 1), (50, 1)] }, { coefficient := 1, powers := [(19, 1), (30, 1), (42, 1)] }, { coefficient := 1, powers := [(19, 1), (33, 1), (39, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (57, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (58, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(41, 1)] }],
  [{ coefficient := 1, powers := [(42, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 40 → SparsePoly (Fin 59) := ![
  [{ coefficient := -1, powers := [(0, 1), (2, 1), (18, 1), (29, 1), (39, 1), (55, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (18, 1), (24, 1), (29, 1), (39, 1), (55, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (20, 1), (30, 1), (55, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (55, 1)] }],
  [{ coefficient := -2, powers := [(3, 1), (8, 1), (23, 1), (55, 2)] }, { coefficient := -2, powers := [(8, 1), (20, 1), (23, 1), (52, 1), (55, 1)] }],
  [{ coefficient := -2, powers := [(3, 1), (30, 1), (47, 1), (55, 1), (57, 1)] }, { coefficient := -2, powers := [(20, 1), (30, 1), (47, 1), (52, 1), (57, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (18, 1), (23, 1), (53, 1), (58, 1)] }, { coefficient := 2, powers := [(18, 1), (23, 1), (24, 1), (53, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (18, 1), (23, 1), (30, 1), (58, 1)] }, { coefficient := 1, powers := [(3, 1), (23, 1), (25, 1), (55, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (24, 1), (30, 1), (58, 1)] }, { coefficient := 1, powers := [(20, 1), (23, 1), (25, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (5, 1), (33, 1), (45, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (24, 1), (33, 1), (45, 1), (58, 1)] }],
  [{ coefficient := -2, powers := [(3, 1), (23, 1), (49, 1), (50, 1), (55, 1)] }, { coefficient := -2, powers := [(20, 1), (23, 1), (49, 1), (50, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (5, 1), (33, 1), (55, 1), (57, 1)] }, { coefficient := -1, powers := [(3, 1), (14, 1), (23, 1), (52, 1), (55, 1)] }, { coefficient := -1, powers := [(5, 1), (33, 1), (52, 1)] }, { coefficient := -1, powers := [(14, 1), (20, 1), (23, 1), (52, 2)] }],
  [{ coefficient := 1, powers := [(3, 1), (18, 1), (50, 1), (55, 1)] }, { coefficient := 1, powers := [(18, 1), (20, 1), (50, 1), (52, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (14, 1), (18, 1), (30, 1), (58, 1)] }, { coefficient := 2, powers := [(14, 1), (18, 1), (24, 1), (30, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (5, 1), (18, 1), (36, 1), (58, 1)] }, { coefficient := -1, powers := [(0, 1), (18, 1), (19, 1), (23, 1), (58, 1)] }, { coefficient := -1, powers := [(5, 1), (18, 1), (24, 1), (36, 1), (58, 1)] }, { coefficient := 1, powers := [(18, 1), (19, 1), (23, 1), (24, 1), (58, 1)] }],
  [{ coefficient := 2, powers := [(3, 1), (8, 1), (33, 1), (44, 1), (55, 1)] }, { coefficient := 2, powers := [(3, 1), (14, 1), (30, 1), (55, 1), (57, 1)] }, { coefficient := 2, powers := [(8, 1), (20, 1), (33, 1), (44, 1), (52, 1)] }, { coefficient := 2, powers := [(14, 1), (20, 1), (30, 1), (52, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (36, 1), (37, 1), (55, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (58, 1)] }, { coefficient := -1, powers := [(20, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (20, 1), (50, 1), (55, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (50, 1), (55, 1)] }],
  [{ coefficient := 2, powers := [(3, 1), (20, 1), (30, 1), (47, 1), (55, 1)] }, { coefficient := 2, powers := [(20, 2), (30, 1), (47, 1), (52, 1)] }],
  [{ coefficient := -2, powers := [(3, 1), (23, 1), (45, 1), (50, 1), (55, 1)] }, { coefficient := -2, powers := [(20, 1), (23, 1), (45, 1), (50, 1), (52, 1)] }, { coefficient := 1, powers := [(29, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (5, 1), (18, 1), (33, 1), (58, 1)] }, { coefficient := 1, powers := [(0, 1), (14, 1), (18, 1), (23, 1), (58, 1)] }, { coefficient := -1, powers := [(5, 1), (18, 1), (24, 1), (33, 1), (58, 1)] }, { coefficient := -1, powers := [(14, 1), (18, 1), (23, 1), (24, 1), (58, 1)] }],
  [{ coefficient := -2, powers := [(3, 1), (14, 1), (20, 1), (47, 1), (55, 1)] }, { coefficient := -2, powers := [(14, 1), (20, 2), (47, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (2, 1), (18, 1), (39, 1), (56, 1), (58, 1)] }, { coefficient := -1, powers := [(2, 1), (18, 1), (24, 1), (39, 1), (56, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (23, 1), (53, 1), (55, 1)] }, { coefficient := -2, powers := [(3, 1), (30, 1), (47, 1), (55, 1)] }, { coefficient := 1, powers := [(20, 1), (23, 1), (52, 1), (53, 1)] }, { coefficient := -2, powers := [(20, 1), (30, 1), (47, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (18, 1), (23, 1), (45, 1), (58, 1)] }, { coefficient := 1, powers := [(0, 1), (18, 1), (29, 1), (47, 1), (58, 1)] }, { coefficient := 1, powers := [(3, 1), (47, 1), (55, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (24, 1), (45, 1), (58, 1)] }, { coefficient := -1, powers := [(18, 1), (24, 1), (29, 1), (47, 1), (58, 1)] }, { coefficient := 1, powers := [(20, 1), (47, 1), (52, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (3, 1), (30, 1), (55, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (18, 1), (29, 1), (30, 1), (58, 1)] }, { coefficient := -2, powers := [(0, 1), (20, 1), (30, 1), (52, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (30, 1), (55, 1)] }, { coefficient := -1, powers := [(18, 1), (24, 1), (29, 1), (30, 1), (58, 1)] }, { coefficient := 1, powers := [(20, 1), (30, 1), (52, 1)] }],
  [{ coefficient := 2, powers := [(3, 1), (20, 1), (23, 1), (50, 1), (55, 1)] }, { coefficient := 2, powers := [(20, 2), (23, 1), (50, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (18, 1), (19, 1), (29, 1), (58, 1)] }, { coefficient := -1, powers := [(3, 1), (19, 1), (55, 1)] }, { coefficient := -1, powers := [(18, 1), (19, 1), (24, 1), (29, 1), (58, 1)] }, { coefficient := -1, powers := [(19, 1), (20, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (14, 1), (18, 1), (29, 1), (58, 1)] }, { coefficient := -1, powers := [(3, 1), (14, 1), (55, 1)] }, { coefficient := -1, powers := [(14, 1), (18, 1), (24, 1), (29, 1), (58, 1)] }, { coefficient := -1, powers := [(14, 1), (20, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (3, 1), (55, 1), (57, 1)] }, { coefficient := -1, powers := [(2, 1), (20, 1), (52, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (20, 1), (55, 1), (57, 1)] }, { coefficient := -1, powers := [(5, 1), (55, 1)] }],
  [{ coefficient := 2, powers := [(3, 1), (8, 1), (55, 2)] }, { coefficient := 2, powers := [(8, 1), (20, 1), (52, 1), (55, 1)] }],
  [{ coefficient := 2, powers := [(3, 1), (23, 1), (50, 1), (55, 1)] }, { coefficient := 2, powers := [(20, 1), (23, 1), (50, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (50, 1), (55, 1)] }, { coefficient := -1, powers := [(20, 1), (50, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (23, 1), (55, 1)] }, { coefficient := -1, powers := [(20, 1), (23, 1), (52, 1)] }],
  [{ coefficient := -2, powers := [(3, 1), (8, 1), (33, 1), (47, 1), (55, 1)] }, { coefficient := -2, powers := [(8, 1), (20, 1), (33, 1), (47, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (18, 1), (23, 1), (58, 1)] }, { coefficient := -1, powers := [(18, 1), (23, 1), (24, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (18, 1), (29, 1), (58, 1)] }, { coefficient := 1, powers := [(3, 1), (55, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (29, 1), (58, 1)] }, { coefficient := 1, powers := [(20, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (3, 1), (39, 1), (55, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (3, 1), (47, 1), (50, 1), (55, 1)] }, { coefficient := 1, powers := [(2, 1), (20, 1), (39, 1), (52, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (20, 1), (47, 1), (50, 1), (52, 1)] }, { coefficient := 2, powers := [(3, 1), (5, 1), (30, 1), (55, 1), (56, 1)] }, { coefficient := 2, powers := [(5, 1), (20, 1), (30, 1), (52, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1), (37, 1), (50, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (49, 1)] }, { coefficient := 1, powers := [(20, 1), (49, 1)] }],
  [{ coefficient := 2, powers := [(3, 1), (8, 1), (24, 1), (33, 1), (47, 1), (55, 1)] }, { coefficient := 2, powers := [(3, 1), (14, 1), (20, 1), (30, 1), (47, 1), (55, 1)] }, { coefficient := -2, powers := [(3, 1), (19, 1), (20, 1), (23, 1), (50, 1), (55, 1)] }, { coefficient := -2, powers := [(3, 1), (19, 1), (23, 1), (24, 1), (50, 1), (55, 1)] }, { coefficient := 2, powers := [(8, 1), (20, 1), (24, 1), (33, 1), (47, 1), (52, 1)] }, { coefficient := 2, powers := [(14, 1), (20, 2), (30, 1), (47, 1), (52, 1)] }, { coefficient := -2, powers := [(19, 1), (20, 2), (23, 1), (50, 1), (52, 1)] }, { coefficient := -2, powers := [(19, 1), (20, 1), (23, 1), (24, 1), (50, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (2, 1), (3, 1), (53, 1), (55, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (2, 1), (18, 1), (29, 1), (53, 1), (58, 1)] }, { coefficient := 1, powers := [(0, 1), (2, 1), (20, 1), (52, 1), (53, 1), (57, 1)] }, { coefficient := 2, powers := [(0, 1), (3, 1), (19, 1), (30, 1), (55, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (8, 1), (18, 1), (29, 1), (36, 1), (58, 1)] }, { coefficient := -1, powers := [(0, 1), (18, 1), (19, 1), (29, 1), (30, 1), (58, 1)] }, { coefficient := 2, powers := [(0, 1), (19, 1), (20, 1), (30, 1), (52, 1), (57, 1)] }, { coefficient := -1, powers := [(2, 1), (3, 1), (53, 1), (55, 1)] }, { coefficient := -1, powers := [(2, 1), (18, 1), (24, 1), (29, 1), (53, 1), (58, 1)] }, { coefficient := -1, powers := [(2, 1), (20, 1), (52, 1), (53, 1)] }, { coefficient := -2, powers := [(3, 1), (6, 1), (8, 1), (36, 1), (55, 2)] }, { coefficient := -1, powers := [(3, 1), (8, 1), (36, 1), (55, 1)] }, { coefficient := -1, powers := [(3, 1), (19, 1), (30, 1), (55, 1)] }, { coefficient := -2, powers := [(6, 1), (8, 1), (20, 1), (36, 1), (52, 1), (55, 1)] }, { coefficient := -1, powers := [(8, 1), (18, 1), (24, 1), (29, 1), (36, 1), (58, 1)] }, { coefficient := -1, powers := [(8, 1), (20, 1), (36, 1), (52, 1)] }, { coefficient := 1, powers := [(18, 1), (19, 1), (24, 1), (29, 1), (30, 1), (58, 1)] }, { coefficient := -1, powers := [(19, 1), (20, 1), (30, 1), (52, 1)] }]
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
    (values : Fin 59 → R) :
    ¬ ∀ index : Fin 40,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component1.SelectedLeafB5_0.selectedHasNoCommonZero

end Krenn.Component1.SelectedLeafB5_0
