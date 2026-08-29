import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component39.SelectedLeafB6_1

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "cbbb132f590d3ff76b6f4d4275b480b06605ac86a764d244c2cda045217c3d7a"
def certificateSHA256 : String := "55aae563ac48d42984e01938e44185cad0eb5bf35428bd1b8c872fce29501913"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 23 → Fin 667 := ![
  0,
  5,
  6,
  7,
  30,
  32,
  91,
  194,
  284,
  325,
  465,
  472,
  476,
  479,
  572,
  600,
  601,
  608,
  610,
  658,
  662,
  664,
  666
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 23 → SparsePoly (Fin 64) := ![
  [{ coefficient := 1, powers := [(1, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (19, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (32, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (40, 1)] }, { coefficient := 1, powers := [(25, 1), (46, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (19, 1), (43, 1), (49, 1)] }, { coefficient := 1, powers := [(1, 1), (40, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (35, 1), (58, 1)] }, { coefficient := 1, powers := [(1, 1), (38, 1), (55, 1)] }, { coefficient := 1, powers := [(1, 1), (41, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1), (49, 1)] }, { coefficient := 1, powers := [(19, 1), (49, 1)] }, { coefficient := 1, powers := [(23, 1), (40, 1)] }, { coefficient := 1, powers := [(23, 1), (46, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (35, 1), (59, 1)] }, { coefficient := 1, powers := [(1, 1)] }, { coefficient := 1, powers := [(10, 1), (33, 1), (35, 1)] }, { coefficient := 1, powers := [(14, 1), (30, 1), (35, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (38, 1), (56, 1)] }, { coefficient := 1, powers := [(1, 1), (50, 1)] }, { coefficient := 1, powers := [(7, 1), (33, 1), (38, 1)] }, { coefficient := 1, powers := [(14, 1), (25, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (40, 1), (56, 1)] }, { coefficient := 1, powers := [(1, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(7, 1), (33, 1), (40, 1)] }, { coefficient := 1, powers := [(14, 1), (25, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (19, 1), (43, 1), (52, 1)] }, { coefficient := 1, powers := [(13, 1), (19, 1), (52, 1)] }, { coefficient := 1, powers := [(13, 1), (40, 1)] }, { coefficient := 1, powers := [(19, 1), (43, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (41, 1)] }, { coefficient := 1, powers := [(3, 1), (32, 1)] }, { coefficient := 1, powers := [(13, 1), (18, 1)] }, { coefficient := 1, powers := [(18, 1), (55, 1)] }, { coefficient := 1, powers := [(23, 1), (41, 1)] }, { coefficient := 1, powers := [(32, 1), (35, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (48, 1)] }, { coefficient := 1, powers := [(6, 1), (29, 1)] }, { coefficient := 1, powers := [(9, 1), (23, 1)] }, { coefficient := 1, powers := [(18, 1), (48, 1)] }, { coefficient := 1, powers := [(23, 1), (38, 1)] }, { coefficient := 1, powers := [(29, 1), (35, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (40, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(19, 1), (49, 1), (56, 1)] }, { coefficient := 1, powers := [(19, 1), (52, 1)] }, { coefficient := 1, powers := [(40, 1)] }, { coefficient := 1, powers := [(46, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (41, 1), (50, 1)] }, { coefficient := 1, powers := [(3, 1), (32, 1), (50, 1)] }, { coefficient := 1, powers := [(3, 1), (58, 1)] }, { coefficient := 1, powers := [(9, 1), (41, 1)] }, { coefficient := 1, powers := [(13, 1), (18, 1), (50, 1)] }, { coefficient := 1, powers := [(13, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (35, 1), (58, 1)] }, { coefficient := 1, powers := [(0, 1), (38, 1), (55, 1)] }, { coefficient := 1, powers := [(0, 1), (41, 1), (48, 1)] }, { coefficient := 1, powers := [(3, 1), (23, 1), (58, 1)] }, { coefficient := 1, powers := [(3, 1), (29, 1), (55, 1)] }, { coefficient := 1, powers := [(3, 1), (32, 1), (48, 1)] }, { coefficient := 1, powers := [(6, 1), (18, 1), (58, 1)] }, { coefficient := 1, powers := [(6, 1), (29, 1), (41, 1)] }, { coefficient := 1, powers := [(6, 1), (32, 1), (38, 1)] }, { coefficient := 1, powers := [(9, 1), (18, 1), (55, 1)] }, { coefficient := 1, powers := [(9, 1), (23, 1), (41, 1)] }, { coefficient := 1, powers := [(9, 1), (32, 1), (35, 1)] }, { coefficient := 1, powers := [(13, 1), (18, 1), (48, 1)] }, { coefficient := 1, powers := [(13, 1), (23, 1), (38, 1)] }, { coefficient := 1, powers := [(13, 1), (29, 1), (35, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(38, 1)] }],
  [{ coefficient := 1, powers := [(40, 1), (63, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 23 → SparsePoly (Fin 64) := ![
  [{ coefficient := -1, powers := [(0, 1), (9, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 1), (23, 1), (50, 1), (62, 1)] }, { coefficient := 1, powers := [(6, 1), (29, 1), (62, 1)] }, { coefficient := -1, powers := [(9, 1), (23, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (13, 1), (62, 1)] }, { coefficient := 1, powers := [(3, 1), (32, 1), (62, 1)] }, { coefficient := 1, powers := [(6, 1), (10, 1), (18, 1), (33, 1), (41, 1), (62, 2)] }, { coefficient := 1, powers := [(6, 1), (14, 1), (18, 1), (30, 1), (41, 1), (62, 2)] }, { coefficient := 1, powers := [(6, 1), (18, 1), (41, 1), (59, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (9, 1), (13, 1), (46, 1), (62, 1), (63, 1)] }, { coefficient := 1, powers := [(1, 1), (3, 1), (9, 1), (19, 1), (32, 1), (56, 1), (62, 2), (63, 1)] }, { coefficient := 1, powers := [(1, 1), (3, 1), (9, 1), (32, 1), (46, 1), (62, 2), (63, 1)] }, { coefficient := 1, powers := [(6, 1), (19, 1), (29, 1), (43, 1), (62, 1), (63, 1)] }, { coefficient := 1, powers := [(9, 1), (13, 1), (19, 1), (62, 1), (63, 1)] }, { coefficient := 1, powers := [(9, 1), (13, 1), (23, 1), (46, 1), (62, 1), (63, 1)] }, { coefficient := 1, powers := [(9, 1), (18, 1), (19, 1), (43, 1), (62, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (1, 1), (3, 1), (9, 1), (32, 1), (46, 1), (62, 2), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (3, 1), (9, 1), (32, 1), (46, 1), (62, 1), (63, 1)] }, { coefficient := 1, powers := [(0, 1), (6, 1), (19, 1), (29, 1), (43, 1), (62, 1), (63, 1)] }, { coefficient := 1, powers := [(0, 1), (9, 1), (18, 1), (19, 1), (43, 1), (62, 1), (63, 1)] }, { coefficient := 1, powers := [(1, 1), (3, 1), (9, 1), (19, 1), (32, 1), (62, 2), (63, 1)] }, { coefficient := 1, powers := [(6, 1), (13, 1), (19, 1), (29, 1), (62, 1), (63, 1)] }, { coefficient := 1, powers := [(9, 1), (13, 1), (18, 1), (19, 1), (62, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (3, 1), (9, 1), (14, 1), (32, 1), (49, 1), (62, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (29, 1), (49, 1), (62, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (3, 1), (9, 1), (33, 1), (62, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (3, 1), (9, 1), (14, 1), (32, 1), (62, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (29, 1), (62, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (62, 1)] }, { coefficient := -1, powers := [(6, 1), (10, 1), (18, 1), (33, 1), (62, 2)] }, { coefficient := -1, powers := [(6, 1), (14, 1), (18, 1), (30, 1), (62, 2)] }, { coefficient := -1, powers := [(6, 1), (18, 1), (59, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(9, 1), (13, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (18, 1), (58, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (23, 1), (32, 1), (62, 1)] }, { coefficient := -1, powers := [(13, 1), (18, 1), (23, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (3, 1), (9, 1), (32, 1), (62, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (29, 1), (63, 1)] }, { coefficient := -1, powers := [(9, 1), (18, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(9, 1)] }],
  [{ coefficient := 1, powers := [(13, 1)] }],
  [{ coefficient := -1, powers := [(1, 1), (3, 1), (9, 1), (32, 1), (62, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(23, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(0, 1), (1, 1), (3, 1), (9, 1), (32, 1), (46, 1), (52, 1), (62, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (6, 1), (19, 1), (29, 1), (43, 1), (52, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (9, 1), (13, 1), (46, 1), (49, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (9, 1), (18, 1), (19, 1), (43, 1), (52, 1), (63, 1)] }, { coefficient := 1, powers := [(0, 1), (9, 1), (41, 1)] }, { coefficient := 1, powers := [(0, 1), (13, 1), (48, 1)] }, { coefficient := 1, powers := [(0, 1), (23, 1), (41, 1), (50, 1)] }, { coefficient := -1, powers := [(0, 1), (35, 1), (58, 1)] }, { coefficient := -1, powers := [(0, 1), (41, 1), (48, 1)] }, { coefficient := -1, powers := [(1, 1), (3, 1), (9, 1), (19, 1), (32, 1), (49, 1), (56, 1), (62, 1), (63, 1)] }, { coefficient := -1, powers := [(1, 1), (3, 1), (9, 1), (19, 1), (32, 1), (52, 1), (62, 1), (63, 1)] }, { coefficient := -1, powers := [(1, 1), (3, 1), (9, 1), (32, 1), (46, 1), (49, 1), (62, 1), (63, 1)] }, { coefficient := 1, powers := [(3, 1), (9, 1), (32, 1)] }, { coefficient := 1, powers := [(3, 1), (23, 1), (32, 1), (50, 1)] }, { coefficient := -1, powers := [(3, 1), (29, 1), (55, 1)] }, { coefficient := -1, powers := [(3, 1), (32, 1), (48, 1)] }, { coefficient := 1, powers := [(6, 1), (10, 1), (18, 1), (33, 1), (35, 1), (58, 1), (62, 1)] }, { coefficient := -1, powers := [(6, 1), (13, 1), (19, 1), (29, 1), (52, 1), (63, 1)] }, { coefficient := 1, powers := [(6, 1), (14, 1), (18, 1), (30, 1), (35, 1), (58, 1), (62, 1)] }, { coefficient := -1, powers := [(6, 1), (18, 1), (58, 1)] }, { coefficient := -1, powers := [(6, 1), (19, 1), (29, 1), (43, 1), (49, 1), (63, 1)] }, { coefficient := -1, powers := [(6, 1), (29, 1), (41, 1)] }, { coefficient := -1, powers := [(9, 1), (13, 1), (18, 1), (19, 1), (52, 1), (63, 1)] }, { coefficient := -1, powers := [(9, 1), (13, 1), (19, 1), (49, 1), (63, 1)] }, { coefficient := -1, powers := [(9, 1), (13, 1), (23, 1), (46, 1), (49, 1), (63, 1)] }, { coefficient := -1, powers := [(9, 1), (18, 1), (19, 1), (43, 1), (49, 1), (63, 1)] }, { coefficient := 1, powers := [(9, 1), (23, 1), (41, 1)] }, { coefficient := 1, powers := [(13, 1), (18, 1), (23, 1), (50, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (1, 1), (55, 1), (62, 1)] }, { coefficient := 1, powers := [(0, 1), (55, 1)] }, { coefficient := 1, powers := [(1, 1), (3, 1), (23, 1), (32, 1), (56, 1), (62, 1)] }, { coefficient := 1, powers := [(1, 1), (6, 1), (10, 1), (18, 1), (33, 1), (55, 1), (62, 2)] }, { coefficient := 1, powers := [(1, 1), (6, 1), (14, 1), (18, 1), (30, 1), (55, 1), (62, 2)] }, { coefficient := 1, powers := [(1, 1), (6, 1), (18, 1), (55, 1), (59, 1), (62, 1)] }, { coefficient := 1, powers := [(1, 1), (13, 1), (18, 1), (23, 1), (56, 1), (62, 1)] }, { coefficient := 1, powers := [(3, 1), (7, 1), (23, 1), (32, 1), (33, 1), (62, 1)] }, { coefficient := 1, powers := [(3, 1), (14, 1), (23, 1), (25, 1), (32, 1), (62, 1)] }, { coefficient := 1, powers := [(6, 1), (32, 1)] }, { coefficient := 1, powers := [(7, 1), (13, 1), (18, 1), (23, 1), (33, 1), (62, 1)] }, { coefficient := 1, powers := [(13, 1), (14, 1), (18, 1), (23, 1), (25, 1), (62, 1)] }, { coefficient := -1, powers := [(13, 1), (23, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (3, 1), (9, 1), (32, 1), (62, 1)] }, { coefficient := -1, powers := [(1, 1), (3, 1), (29, 1), (55, 1), (62, 1)] }, { coefficient := 1, powers := [(6, 1), (13, 1), (29, 1)] }, { coefficient := 1, powers := [(9, 1), (13, 1), (18, 1)] }, { coefficient := 1, powers := [(9, 1), (13, 1), (23, 1)] }]
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
    ¬ ∀ index : Fin 23,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component39.SelectedLeafB6_1.selectedHasNoCommonZero

end Krenn.Component39.SelectedLeafB6_1
