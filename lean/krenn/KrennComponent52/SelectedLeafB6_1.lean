import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component52.SelectedLeafB6_1

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "29d72f12ff9098526b26e506bb1b82a80d6614bbd0307532bd3f0c8a2418646b"
def certificateSHA256 : String := "9d207741df8b8c892ad01cb630c940310a64859e619fc0a80599292a68b5bc4a"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 24 → Fin 640 := ![
  6,
  9,
  11,
  30,
  161,
  162,
  202,
  221,
  233,
  313,
  346,
  353,
  354,
  455,
  467,
  468,
  555,
  556,
  581,
  633,
  634,
  636,
  638,
  639
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 24 → SparsePoly (Fin 63) := ![
  [{ coefficient := 1, powers := [(3, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1)] }, { coefficient := 1, powers := [(24, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1)] }, { coefficient := 1, powers := [(24, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1), (51, 1)] }, { coefficient := 1, powers := [(51, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (29, 1), (58, 1)] }, { coefficient := 1, powers := [(29, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (23, 1), (58, 1)] }, { coefficient := 1, powers := [(23, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (24, 1), (40, 1)] }, { coefficient := 1, powers := [(18, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (47, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (53, 1)] }, { coefficient := 1, powers := [(29, 1), (41, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (56, 1)] }, { coefficient := 1, powers := [(29, 1), (47, 1)] }, { coefficient := 1, powers := [(35, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1), (58, 1)] }, { coefficient := 1, powers := [(20, 1)] }, { coefficient := 1, powers := [(24, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (40, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (45, 1), (52, 1)] }, { coefficient := 1, powers := [(25, 1), (45, 1)] }, { coefficient := 1, powers := [(56, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (41, 1), (55, 1)] }, { coefficient := 1, powers := [(0, 1), (46, 1), (51, 1)] }, { coefficient := 1, powers := [(20, 1), (51, 1)] }, { coefficient := 1, powers := [(41, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1)] }, { coefficient := 1, powers := [(6, 1), (58, 1)] }, { coefficient := 1, powers := [(24, 1), (40, 1)] }, { coefficient := 1, powers := [(24, 1), (44, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (50, 1)] }, { coefficient := 1, powers := [(3, 1), (58, 1)] }, { coefficient := 1, powers := [(19, 1), (50, 1)] }, { coefficient := 1, powers := [(19, 1), (55, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (36, 1), (58, 1)] }, { coefficient := 1, powers := [(0, 1)] }, { coefficient := 1, powers := [(3, 1), (24, 1), (58, 1)] }, { coefficient := 1, powers := [(6, 1), (19, 1), (58, 1)] }, { coefficient := 1, powers := [(19, 1)] }, { coefficient := 1, powers := [(24, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (41, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (47, 1), (53, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (53, 1)] }, { coefficient := 1, powers := [(8, 1), (23, 1), (59, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (47, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(13, 1), (23, 1), (56, 1)] }, { coefficient := 1, powers := [(13, 1), (29, 1), (47, 1)] }, { coefficient := 1, powers := [(13, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (53, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (41, 1)] }, { coefficient := 1, powers := [(18, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (60, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(40, 1)] }],
  [{ coefficient := 1, powers := [(41, 1), (62, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 24 → SparsePoly (Fin 63) := ![
  [{ coefficient := 1, powers := [(0, 1), (5, 1), (29, 1), (41, 1), (55, 1), (58, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 1), (5, 1), (29, 1), (41, 1), (58, 1), (60, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (8, 1), (23, 1), (41, 1), (55, 1), (58, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 1), (8, 1), (23, 1), (41, 1), (58, 1), (60, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(0, 2), (35, 1), (36, 1), (41, 1), (50, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 2), (35, 1), (36, 1), (41, 1), (55, 1), (60, 1)] }, { coefficient := -1, powers := [(0, 1), (3, 1), (35, 1), (41, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (6, 1), (19, 1), (35, 1), (41, 1), (50, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (6, 1), (19, 1), (35, 1), (41, 1), (55, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (3, 1), (8, 1), (35, 1), (41, 1), (50, 1), (58, 1), (60, 1), (62, 1)] }, { coefficient := 1, powers := [(0, 1), (3, 1), (8, 1), (35, 1), (41, 1), (55, 1), (58, 1), (60, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 1), (5, 1), (25, 1), (32, 1), (41, 1), (45, 1), (55, 1), (60, 1), (62, 2)] }, { coefficient := 1, powers := [(0, 1), (5, 1), (25, 1), (32, 1), (41, 1), (45, 1), (60, 2), (62, 2)] }, { coefficient := -1, powers := [(0, 1), (5, 1), (32, 1), (41, 1), (45, 1), (52, 1), (55, 1), (62, 2)] }, { coefficient := 1, powers := [(0, 1), (5, 1), (32, 1), (41, 1), (45, 1), (52, 1), (60, 1), (62, 2)] }, { coefficient := 1, powers := [(0, 1), (8, 1), (32, 1), (41, 1), (47, 1), (55, 1), (60, 1), (62, 2)] }, { coefficient := -1, powers := [(0, 1), (8, 1), (32, 1), (41, 1), (47, 1), (60, 2), (62, 2)] }, { coefficient := 1, powers := [(0, 1), (8, 1), (35, 1), (41, 1), (50, 1), (60, 1), (62, 1)] }, { coefficient := 1, powers := [(0, 1), (8, 1), (35, 1), (41, 1), (55, 1), (60, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 1), (20, 1), (41, 1), (44, 1), (51, 1), (60, 1), (62, 3)] }, { coefficient := 1, powers := [(0, 1), (41, 1), (46, 1), (51, 1), (60, 1), (62, 3)] }],
  [{ coefficient := 1, powers := [(0, 1), (5, 1), (25, 1), (32, 1), (41, 1), (55, 1), (60, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 1), (5, 1), (25, 1), (32, 1), (41, 1), (60, 2), (62, 1)] }, { coefficient := 1, powers := [(0, 1), (5, 1), (32, 1), (41, 1), (52, 1), (55, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 1), (5, 1), (32, 1), (41, 1), (52, 1), (60, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (8, 1), (32, 1), (41, 1), (55, 1), (60, 1), (62, 1)] }, { coefficient := 1, powers := [(0, 1), (8, 1), (32, 1), (41, 1), (60, 2), (62, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (20, 1), (41, 1), (60, 1), (62, 2)] }],
  [{ coefficient := -1, powers := [(0, 1), (5, 1), (41, 1), (55, 1), (59, 1), (62, 1)] }, { coefficient := 1, powers := [(0, 1), (5, 1), (41, 1), (59, 1), (60, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (8, 1), (41, 1), (55, 1), (59, 1), (62, 1)] }, { coefficient := 1, powers := [(0, 1), (8, 1), (41, 1), (59, 1), (60, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (23, 1), (41, 1), (53, 1), (55, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 1), (23, 1), (41, 1), (53, 1), (60, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (41, 1), (53, 1), (55, 1), (62, 1)] }, { coefficient := 1, powers := [(0, 1), (41, 1), (53, 1), (60, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (18, 1), (41, 1), (55, 1), (62, 1)] }, { coefficient := 1, powers := [(0, 1), (18, 1), (41, 1), (60, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (13, 1), (41, 1), (55, 1), (62, 1)] }, { coefficient := 1, powers := [(0, 1), (13, 1), (41, 1), (60, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (41, 1), (51, 1), (60, 1), (62, 2)] }],
  [{ coefficient := -1, powers := [(0, 1), (5, 1), (32, 1), (41, 1), (55, 1), (62, 1)] }, { coefficient := 1, powers := [(0, 1), (5, 1), (32, 1), (41, 1), (60, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (41, 1), (60, 1), (62, 2)] }],
  [{ coefficient := 1, powers := [(0, 1), (20, 1), (41, 1), (51, 1), (60, 1), (62, 2)] }],
  [{ coefficient := 1, powers := [(0, 1), (8, 1), (35, 1), (41, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (8, 1), (35, 1), (41, 1), (50, 1), (60, 1)] }, { coefficient := -1, powers := [(0, 1), (8, 1), (35, 1), (41, 1), (55, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (41, 1), (55, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 1), (41, 1), (60, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (5, 1), (25, 1), (32, 1), (41, 1), (45, 1), (55, 1), (62, 1)] }, { coefficient := 1, powers := [(0, 1), (5, 1), (25, 1), (32, 1), (41, 1), (45, 1), (60, 1), (62, 1)] }, { coefficient := 1, powers := [(0, 1), (8, 1), (32, 1), (41, 1), (47, 1), (55, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 1), (8, 1), (32, 1), (41, 1), (47, 1), (60, 1), (62, 1)] }, { coefficient := 1, powers := [(0, 1), (8, 1), (35, 1), (41, 1), (55, 1)] }, { coefficient := -1, powers := [(0, 1), (41, 2), (55, 1), (62, 2)] }, { coefficient := -2, powers := [(41, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (38, 1), (41, 1), (55, 1), (59, 1), (62, 1)] }, { coefficient := 1, powers := [(0, 1), (38, 1), (41, 1), (59, 1), (60, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 1), (41, 2), (55, 1), (56, 1), (62, 1)] }, { coefficient := 1, powers := [(0, 1), (41, 2), (56, 1), (60, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(0, 2), (5, 1), (32, 1), (41, 1), (55, 1), (56, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 2), (5, 1), (32, 1), (41, 1), (56, 1), (60, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 1), (18, 1), (23, 1), (24, 1), (41, 1), (53, 1), (55, 1), (62, 1)] }, { coefficient := 1, powers := [(0, 1), (18, 1), (23, 1), (24, 1), (41, 1), (53, 1), (60, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 1), (20, 1), (24, 1), (41, 1), (51, 1), (60, 1), (62, 2)] }],
  [{ coefficient := -1, powers := [(0, 1), (3, 1), (8, 1), (24, 1), (35, 1), (41, 1), (50, 1), (58, 1), (60, 1)] }, { coefficient := -1, powers := [(0, 1), (3, 1), (8, 1), (24, 1), (35, 1), (41, 1), (55, 1), (58, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (5, 1), (24, 1), (25, 1), (32, 1), (41, 1), (45, 1), (55, 1), (60, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 1), (5, 1), (24, 1), (25, 1), (32, 1), (41, 1), (45, 1), (60, 2), (62, 1)] }, { coefficient := 1, powers := [(0, 1), (5, 1), (24, 1), (32, 1), (41, 1), (45, 1), (52, 1), (55, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 1), (5, 1), (24, 1), (32, 1), (41, 1), (45, 1), (52, 1), (60, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 1), (8, 1), (24, 1), (32, 1), (41, 1), (47, 1), (55, 1), (60, 1), (62, 1)] }, { coefficient := 1, powers := [(0, 1), (8, 1), (24, 1), (32, 1), (41, 1), (47, 1), (60, 2), (62, 1)] }, { coefficient := -1, powers := [(0, 1), (8, 1), (24, 1), (35, 1), (41, 1), (50, 1), (60, 1)] }, { coefficient := -1, powers := [(0, 1), (8, 1), (24, 1), (35, 1), (41, 1), (55, 1), (60, 1)] }, { coefficient := -1, powers := [(0, 1), (8, 1), (35, 1), (41, 1), (55, 1)] }, { coefficient := 1, powers := [(0, 1), (8, 1), (35, 1), (41, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (20, 1), (24, 1), (41, 1), (44, 1), (51, 1), (60, 1), (62, 2)] }, { coefficient := -1, powers := [(0, 1), (24, 1), (41, 1), (46, 1), (51, 1), (60, 1), (62, 2)] }, { coefficient := -1, powers := [(0, 1), (41, 1), (55, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 1), (41, 1), (60, 1), (62, 1)] }, { coefficient := -2, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
/-- Lean replays the exact selected-row integer certificate. -/
theorem constantIdentity :
    ∑ index, (multipliers index).toPoly *
      (selectedEquations index).toPoly = C (2 : ℤ) := by
  simp (config := { maxSteps := 1000000 })
    [Fin.sum_univ_succ, multipliers, selectedEquations,
    SparsePoly.toPoly, SparseTerm.toPoly]
  ring

/-- The selected rows have no common zero in a characteristic-zero ring. -/
theorem selectedHasNoCommonZero {R : Type*} [CommRing R] [Nontrivial R] [CharZero R]
    (values : Fin 63 → R) :
    ¬ ∀ index : Fin 24,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((2 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (2 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (2 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component52.SelectedLeafB6_1.selectedHasNoCommonZero

end Krenn.Component52.SelectedLeafB6_1
