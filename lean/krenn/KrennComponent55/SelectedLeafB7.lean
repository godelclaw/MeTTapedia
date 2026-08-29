import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component55.SelectedLeafB7

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "064ef149c3fab725673f701b279c532e6f4a684fd3709d6f3fa884be832e5a65"
def certificateSHA256 : String := "7e9de71ec9fe7bcc7b9dfb9fa02f08b105595e2264a1d189ed5bdacf616fbd34"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 34 → Fin 587 := ![
  0,
  1,
  2,
  3,
  4,
  38,
  40,
  44,
  196,
  226,
  228,
  233,
  238,
  268,
  336,
  338,
  343,
  345,
  346,
  348,
  361,
  362,
  367,
  368,
  387,
  388,
  543,
  545,
  554,
  578,
  581,
  583,
  585,
  586
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 34 → SparsePoly (Fin 61) := ![
  [{ coefficient := 1, powers := [(2, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(30, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(33, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (39, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (26, 1)] }, { coefficient := 1, powers := [(26, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (54, 1)] }, { coefficient := 1, powers := [(26, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (49, 1)] }, { coefficient := 1, powers := [(21, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(26, 1), (40, 1)] }, { coefficient := 1, powers := [(26, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (36, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (26, 1), (45, 1)] }, { coefficient := 1, powers := [(9, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1)] }, { coefficient := 1, powers := [(21, 1), (43, 1)] }, { coefficient := 1, powers := [(25, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (51, 1)] }, { coefficient := 1, powers := [(20, 1), (51, 1)] }, { coefficient := 1, powers := [(26, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (55, 1)] }, { coefficient := 1, powers := [(9, 1), (42, 1)] }, { coefficient := 1, powers := [(14, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (56, 1)] }, { coefficient := 1, powers := [(18, 1), (21, 1), (49, 1)] }, { coefficient := 1, powers := [(18, 1), (21, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (55, 1)] }, { coefficient := 1, powers := [(9, 1), (52, 1)] }, { coefficient := 1, powers := [(14, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (56, 1)] }, { coefficient := 1, powers := [(18, 1), (26, 1), (40, 1)] }, { coefficient := 1, powers := [(18, 1), (26, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (51, 1)] }, { coefficient := 1, powers := [(29, 1), (41, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (54, 1)] }, { coefficient := 1, powers := [(29, 1), (46, 1)] }, { coefficient := 1, powers := [(35, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1), (51, 1)] }, { coefficient := 1, powers := [(26, 1), (44, 1), (48, 1)] }, { coefficient := 1, powers := [(51, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1), (49, 1)] }, { coefficient := 1, powers := [(21, 1), (43, 1), (49, 1)] }, { coefficient := 1, powers := [(46, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (36, 1), (55, 1)] }, { coefficient := 1, powers := [(2, 1), (39, 1), (52, 1)] }, { coefficient := 1, powers := [(2, 1), (42, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (37, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (40, 1), (53, 1)] }, { coefficient := 1, powers := [(2, 1), (44, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (49, 1)] }, { coefficient := 1, powers := [(3, 1), (56, 1)] }, { coefficient := 1, powers := [(20, 1), (49, 1)] }, { coefficient := 1, powers := [(20, 1), (53, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (39, 1), (54, 1)] }, { coefficient := 1, powers := [(3, 1), (30, 1), (54, 1)] }, { coefficient := 1, powers := [(9, 1), (20, 1), (54, 1)] }, { coefficient := 1, powers := [(9, 1), (26, 1), (43, 1)] }, { coefficient := 1, powers := [(26, 1), (39, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1)] }, { coefficient := 1, powers := [(3, 1), (33, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1)] }, { coefficient := 1, powers := [(20, 1), (52, 1)] }, { coefficient := 1, powers := [(25, 1), (42, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (37, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (40, 1), (53, 1)] }, { coefficient := 1, powers := [(0, 1), (44, 1), (49, 1)] }, { coefficient := 1, powers := [(40, 1)] }, { coefficient := 1, powers := [(44, 1)] }, { coefficient := 1, powers := [(49, 1)] }, { coefficient := 1, powers := [(53, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (36, 1), (55, 1)] }, { coefficient := 1, powers := [(0, 1), (39, 1), (52, 1)] }, { coefficient := 1, powers := [(0, 1), (42, 1), (47, 1)] }, { coefficient := 1, powers := [(3, 1), (25, 1), (55, 1)] }, { coefficient := 1, powers := [(3, 1), (30, 1), (52, 1)] }, { coefficient := 1, powers := [(3, 1), (33, 1), (47, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1), (55, 1)] }, { coefficient := 1, powers := [(6, 1), (30, 1), (42, 1)] }, { coefficient := 1, powers := [(6, 1), (33, 1), (39, 1)] }, { coefficient := 1, powers := [(9, 1), (20, 1), (52, 1)] }, { coefficient := 1, powers := [(9, 1), (25, 1), (42, 1)] }, { coefficient := 1, powers := [(9, 1), (33, 1), (36, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1), (47, 1)] }, { coefficient := 1, powers := [(14, 1), (25, 1), (39, 1)] }, { coefficient := 1, powers := [(14, 1), (30, 1), (36, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (41, 1), (54, 1)] }, { coefficient := 1, powers := [(2, 1), (46, 1), (51, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (51, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (57, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (46, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(13, 1), (24, 1), (54, 1)] }, { coefficient := 1, powers := [(13, 1), (29, 1), (46, 1)] }, { coefficient := 1, powers := [(13, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (51, 1)] }, { coefficient := 1, powers := [(19, 1), (29, 1), (41, 1)] }, { coefficient := 1, powers := [(19, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1), (59, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (60, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 34 → SparsePoly (Fin 61) := ![
  [{ coefficient := 1, powers := [(0, 1), (2, 1), (6, 1), (39, 1), (41, 1), (54, 1), (56, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (2, 1), (9, 1), (36, 1), (41, 1), (54, 1), (56, 1), (60, 1)] }, { coefficient := -1, powers := [(2, 1), (3, 1), (6, 1), (30, 1), (41, 1), (54, 1), (56, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (6, 1), (25, 1), (39, 1), (41, 1), (54, 1), (56, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (6, 1), (30, 1), (38, 1), (57, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (3, 1), (20, 1), (41, 1), (54, 1), (56, 1), (60, 1)] }, { coefficient := -1, powers := [(2, 1), (20, 2), (41, 1), (53, 1), (54, 1), (60, 1)] }, { coefficient := -1, powers := [(2, 1), (20, 1), (41, 1), (54, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (20, 1), (35, 1), (51, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (3, 1), (26, 1), (33, 1), (36, 1), (39, 1), (41, 1), (56, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (2, 1), (3, 1), (41, 1), (42, 1), (54, 1), (56, 1), (60, 1)] }, { coefficient := -1, powers := [(2, 1), (3, 2), (33, 1), (41, 1), (54, 1), (56, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (3, 1), (33, 1), (38, 1), (57, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (2, 1), (20, 1), (41, 1), (44, 1), (54, 1), (60, 1)] }, { coefficient := -1, powers := [(0, 1), (2, 1), (41, 1), (54, 1), (60, 1)] }, { coefficient := -1, powers := [(2, 1), (20, 2), (41, 1), (44, 1), (54, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (25, 1), (46, 1), (51, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (25, 1), (32, 1), (46, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (3, 1), (52, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (14, 1), (36, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (6, 1), (39, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (9, 1), (36, 1), (57, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (2, 1), (14, 1), (36, 1), (41, 1), (56, 1), (59, 1)] }, { coefficient := -1, powers := [(2, 1), (3, 1), (20, 1), (41, 1), (52, 1), (56, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (6, 1), (14, 1), (20, 1), (41, 1), (56, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (6, 1), (20, 1), (41, 1), (52, 1), (56, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (6, 1), (33, 1), (36, 1), (41, 1), (56, 1), (59, 1)] }, { coefficient := -1, powers := [(2, 1), (14, 1), (20, 1), (36, 1), (41, 1), (56, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (3, 1), (33, 1), (36, 1), (41, 1), (45, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (3, 1), (9, 1), (41, 1), (52, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (3, 1), (39, 1), (41, 1), (52, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (9, 1), (14, 1), (36, 1), (41, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (14, 1), (36, 1), (39, 1), (41, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (40, 1), (41, 1)] }, { coefficient := 1, powers := [(2, 1), (41, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (29, 1), (36, 1), (57, 1)] }, { coefficient := 1, powers := [(18, 1), (32, 1), (36, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (41, 1), (43, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (36, 1), (57, 1)] }, { coefficient := 1, powers := [(18, 1), (35, 1), (36, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (29, 1), (57, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (54, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (57, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (41, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (3, 1), (33, 1), (36, 1), (41, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (49, 1), (51, 1)] }, { coefficient := -1, powers := [(8, 1), (32, 1), (49, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (35, 1), (44, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (2, 1), (36, 1), (41, 1), (54, 1), (56, 1)] }, { coefficient := -1, powers := [(2, 1), (3, 1), (25, 1), (41, 1), (54, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (25, 1), (38, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [(29, 1), (36, 1), (57, 1)] }, { coefficient := -1, powers := [(32, 1), (36, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (3, 1), (20, 1), (41, 1), (54, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (20, 1), (38, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [(24, 1), (36, 1), (57, 1)] }, { coefficient := -1, powers := [(35, 1), (36, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(19, 1)] }],
  [{ coefficient := 1, powers := [(13, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (35, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (51, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (2, 1), (38, 1), (57, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (2, 1), (20, 1), (41, 1), (54, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (20, 1), (41, 1), (44, 1), (54, 1)] }, { coefficient := 1, powers := [(2, 1), (41, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (3, 1), (41, 1), (52, 1), (56, 1)] }, { coefficient := -1, powers := [(2, 1), (14, 1), (36, 1), (41, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (6, 1), (39, 1), (41, 1), (54, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (20, 1), (41, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (3, 1), (41, 1), (54, 1), (56, 1)] }, { coefficient := -1, powers := [(2, 1), (38, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -2, powers := [(0, 1), (2, 1), (14, 1), (36, 1), (39, 1), (41, 1), (54, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (3, 1), (20, 1), (39, 1), (41, 1), (52, 1), (54, 1), (56, 1)] }, { coefficient := -1, powers := [(2, 1), (6, 1), (14, 1), (20, 1), (39, 1), (41, 1), (54, 1), (56, 1)] }, { coefficient := -1, powers := [(2, 1), (6, 1), (20, 1), (39, 1), (41, 1), (52, 1), (54, 1), (56, 1)] }, { coefficient := -1, powers := [(2, 1), (6, 1), (33, 1), (36, 1), (39, 1), (41, 1), (54, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (14, 1), (20, 1), (36, 1), (39, 1), (41, 1), (54, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (2, 1), (3, 1), (41, 1), (42, 1), (47, 1), (54, 1), (56, 1)] }, { coefficient := -1, powers := [(0, 1), (2, 1), (6, 1), (39, 1), (41, 1), (42, 1), (54, 1), (56, 1)] }, { coefficient := -1, powers := [(0, 1), (2, 1), (9, 1), (36, 1), (41, 1), (42, 1), (54, 1), (56, 1)] }, { coefficient := -1, powers := [(0, 1), (2, 1), (20, 1), (37, 1), (41, 1), (54, 1), (56, 1)] }, { coefficient := -1, powers := [(0, 1), (2, 1), (20, 1), (40, 1), (41, 1), (53, 1), (54, 1)] }, { coefficient := -1, powers := [(0, 1), (2, 1), (36, 1), (38, 1), (55, 1), (57, 1)] }, { coefficient := -1, powers := [(0, 1), (2, 1), (38, 1), (39, 1), (52, 1), (57, 1)] }, { coefficient := -1, powers := [(0, 1), (2, 1), (38, 1), (42, 1), (47, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (2, 1), (41, 1), (49, 1), (54, 1)] }, { coefficient := 1, powers := [(2, 1), (3, 2), (33, 1), (41, 1), (47, 1), (54, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (3, 1), (6, 1), (30, 1), (41, 1), (42, 1), (54, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (3, 1), (20, 1), (41, 1), (44, 1), (54, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (3, 1), (26, 1), (33, 1), (36, 1), (39, 1), (41, 1), (45, 1), (56, 1)] }, { coefficient := -1, powers := [(2, 1), (3, 1), (33, 1), (38, 1), (47, 1), (57, 1)] }, { coefficient := -1, powers := [(2, 1), (6, 1), (25, 1), (39, 1), (41, 1), (42, 1), (54, 1), (56, 1)] }, { coefficient := -1, powers := [(2, 1), (6, 1), (30, 1), (38, 1), (42, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (20, 2), (41, 1), (44, 1), (49, 1), (54, 1)] }, { coefficient := 1, powers := [(2, 1), (20, 2), (41, 1), (44, 1), (53, 1), (54, 1)] }, { coefficient := 1, powers := [(2, 1), (20, 1), (41, 1), (44, 1), (54, 1)] }, { coefficient := -1, powers := [(2, 1), (25, 1), (46, 1), (49, 1), (51, 1)] }, { coefficient := -1, powers := [(5, 1), (20, 1), (35, 1), (44, 1), (51, 1)] }, { coefficient := -1, powers := [(5, 1), (29, 1), (36, 1), (56, 1), (57, 1)] }, { coefficient := -1, powers := [(5, 1), (29, 1), (57, 1)] }, { coefficient := -1, powers := [(5, 1), (32, 1), (36, 1), (54, 1), (56, 1)] }, { coefficient := -1, powers := [(5, 1), (32, 1), (54, 1)] }, { coefficient := -1, powers := [(8, 1), (24, 1), (36, 1), (56, 1), (57, 1)] }, { coefficient := -1, powers := [(8, 1), (24, 1), (57, 1)] }, { coefficient := -1, powers := [(8, 1), (25, 1), (32, 1), (46, 1), (49, 1)] }, { coefficient := -1, powers := [(8, 1), (35, 1), (36, 1), (41, 1), (56, 1)] }, { coefficient := -1, powers := [(8, 1), (35, 1), (41, 1)] }]
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
    ¬ ∀ index : Fin 34,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component55.SelectedLeafB7.selectedHasNoCommonZero

end Krenn.Component55.SelectedLeafB7
