import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component1.SelectedLeafB5_7

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "a4c5fa1bcdffbcbf7da7087981899ae2fcaad72e8a48fef33e6fede0247aabf2"
def certificateSHA256 : String := "772c79b84e5dc037fb3609274795e7f1b6280b2cf7da37d4cec29de8a7db2e9c"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 32 → Fin 588 := ![
  1,
  6,
  25,
  36,
  37,
  40,
  48,
  49,
  219,
  225,
  260,
  261,
  264,
  276,
  302,
  354,
  384,
  385,
  386,
  390,
  411,
  503,
  507,
  547,
  550,
  564,
  581,
  582,
  584,
  585,
  586,
  587
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 32 → SparsePoly (Fin 62) := ![
  [{ coefficient := 1, powers := [(3, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(28, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1)] }, { coefficient := 1, powers := [(24, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (49, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (53, 1)] }, { coefficient := 1, powers := [(30, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(30, 1), (41, 1)] }, { coefficient := 1, powers := [(30, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1), (52, 1)] }, { coefficient := 1, powers := [(42, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (30, 1), (55, 1)] }, { coefficient := 1, powers := [(30, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (25, 1), (45, 1)] }, { coefficient := 1, powers := [(9, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (20, 1), (52, 1)] }, { coefficient := 1, powers := [(14, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (50, 1)] }, { coefficient := 1, powers := [(30, 1), (42, 1)] }, { coefficient := 1, powers := [(33, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (53, 1)] }, { coefficient := 1, powers := [(30, 1), (47, 1)] }, { coefficient := 1, powers := [(36, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (37, 1), (56, 1)] }, { coefficient := 1, powers := [(3, 1), (24, 1), (56, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (40, 1), (53, 1)] }, { coefficient := 1, powers := [(3, 1), (31, 1), (53, 1)] }, { coefficient := 1, powers := [(9, 1), (20, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (40, 1), (52, 1)] }, { coefficient := 1, powers := [(13, 1), (29, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (47, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1)] }, { coefficient := 1, powers := [(18, 1), (28, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (23, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (56, 1)] }, { coefficient := 1, powers := [(14, 1), (25, 1), (45, 1)] }, { coefficient := 1, powers := [(14, 1), (53, 1)] }, { coefficient := 1, powers := [(19, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (40, 1), (52, 1)] }, { coefficient := 1, powers := [(3, 1), (31, 1), (52, 1)] }, { coefficient := 1, powers := [(9, 1), (20, 1), (52, 1)] }, { coefficient := 1, powers := [(9, 1)] }, { coefficient := 1, powers := [(40, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (41, 1), (53, 1)] }, { coefficient := 1, powers := [(8, 1), (36, 1), (41, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (53, 1)] }, { coefficient := 1, powers := [(18, 1), (30, 1), (45, 1)] }, { coefficient := 1, powers := [(19, 1), (30, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (37, 1), (55, 1)] }, { coefficient := 1, powers := [(0, 1)] }, { coefficient := 1, powers := [(3, 1), (24, 1), (55, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1), (55, 1)] }, { coefficient := 1, powers := [(20, 1)] }, { coefficient := 1, powers := [(24, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (42, 1), (53, 1)] }, { coefficient := 1, powers := [(2, 1), (47, 1), (50, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (53, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1), (50, 1)] }, { coefficient := 1, powers := [(8, 1), (23, 1), (56, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (47, 1)] }, { coefficient := 1, powers := [(8, 1), (36, 1), (42, 1)] }, { coefficient := 1, powers := [(14, 1), (23, 1), (53, 1)] }, { coefficient := 1, powers := [(14, 1), (30, 1), (47, 1)] }, { coefficient := 1, powers := [(14, 1), (36, 1), (39, 1)] }, { coefficient := 1, powers := [(19, 1), (23, 1), (50, 1)] }, { coefficient := 1, powers := [(19, 1), (30, 1), (42, 1)] }, { coefficient := 1, powers := [(19, 1), (33, 1), (39, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (57, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (58, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(40, 1), (59, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(41, 1), (60, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(42, 1), (61, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 32 → SparsePoly (Fin 62) := ![
  [{ coefficient := 1, powers := [(2, 1), (24, 1), (39, 1), (55, 1), (57, 1)] }, { coefficient := -1, powers := [(5, 1), (30, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (25, 1), (33, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(23, 1), (25, 1)] }],
  [{ coefficient := -2, powers := [(23, 1), (50, 1), (59, 1)] }, { coefficient := 1, powers := [(30, 1), (42, 1), (44, 1), (59, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (23, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (3, 1), (39, 1), (55, 1), (56, 1), (57, 1), (61, 1)] }, { coefficient := -1, powers := [(2, 1), (39, 1), (56, 1), (57, 1), (61, 1)] }, { coefficient := -1, powers := [(8, 1), (33, 1), (47, 1), (57, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(18, 1), (50, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (13, 1), (20, 1), (39, 1), (56, 1), (58, 1), (59, 1), (61, 1)] }, { coefficient := -1, powers := [(2, 1), (18, 1), (20, 1), (39, 1), (56, 1), (58, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (33, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (20, 1), (39, 1), (40, 1), (56, 1), (58, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (20, 1), (39, 1), (56, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(18, 1), (42, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(19, 1), (42, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (20, 1), (39, 1), (56, 1), (57, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (33, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(23, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(19, 1)] }],
  [{ coefficient := 1, powers := [(14, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (39, 1), (55, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (33, 1), (52, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (20, 1), (39, 1), (56, 1), (58, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(50, 1)] }],
  [{ coefficient := 1, powers := [(23, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (33, 1), (53, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(42, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (39, 1), (56, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (20, 1), (39, 1), (42, 1), (52, 1), (56, 1), (61, 1)] }, { coefficient := -1, powers := [(2, 1), (39, 1), (56, 1)] }, { coefficient := -1, powers := [(8, 1), (33, 1), (47, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (20, 1), (39, 1), (52, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(2, 2), (20, 1), (39, 1), (49, 1), (56, 1), (58, 1)] }, { coefficient := -1, powers := [(2, 2), (20, 1), (39, 1), (52, 1), (56, 1), (58, 1)] }, { coefficient := -1, powers := [(5, 1), (33, 1), (53, 1)] }, { coefficient := 2, powers := [(19, 1), (23, 1), (50, 1)] }, { coefficient := -1, powers := [(19, 1), (30, 1), (42, 1), (44, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (42, 1), (53, 1)] }, { coefficient := -1, powers := [(8, 1), (36, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (3, 1), (24, 1), (39, 1), (55, 1), (56, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (13, 1), (20, 1), (29, 1), (39, 1), (56, 1), (58, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (18, 1), (20, 1), (29, 1), (39, 1), (56, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (20, 1), (39, 1), (52, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (20, 1), (39, 1), (56, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (24, 1), (39, 1), (56, 1), (57, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (33, 1), (47, 1), (57, 1)] }]
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
    ¬ ∀ index : Fin 32,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component1.SelectedLeafB5_7.selectedHasNoCommonZero

end Krenn.Component1.SelectedLeafB5_7
