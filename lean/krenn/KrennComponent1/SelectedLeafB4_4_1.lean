import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component1.SelectedLeafB4_4_1

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "962af80c83da9d723f23b9eceed058af7c4d400ae6191e7c670a9c3660999767"
def certificateSHA256 : String := "67eba04ea9d26ca3e76d5f7eb8b8e873b4f4563ff8b0f8ed061e062ed0ce78a5"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 21 → Fin 591 := ![
  3,
  6,
  25,
  36,
  48,
  261,
  302,
  354,
  366,
  384,
  385,
  503,
  507,
  545,
  547,
  581,
  584,
  585,
  586,
  587,
  589
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 21 → SparsePoly (Fin 60) := ![
  [{ coefficient := 1, powers := [(6, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(28, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(30, 1), (41, 1)] }, { coefficient := 1, powers := [(30, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (25, 1), (45, 1)] }, { coefficient := 1, powers := [(9, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (20, 1), (52, 1)] }, { coefficient := 1, powers := [(14, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (50, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1)] }, { coefficient := 1, powers := [(14, 1), (30, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (50, 1)] }, { coefficient := 1, powers := [(30, 1), (42, 1)] }, { coefficient := 1, powers := [(33, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (53, 1)] }, { coefficient := 1, powers := [(30, 1), (47, 1)] }, { coefficient := 1, powers := [(36, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (47, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1)] }, { coefficient := 1, powers := [(18, 1), (28, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (23, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (56, 1)] }, { coefficient := 1, powers := [(14, 1), (25, 1), (45, 1)] }, { coefficient := 1, powers := [(14, 1), (53, 1)] }, { coefficient := 1, powers := [(19, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1)] }, { coefficient := 1, powers := [(6, 1), (55, 1)] }, { coefficient := 1, powers := [(24, 1), (41, 1)] }, { coefficient := 1, powers := [(24, 1), (44, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (40, 1), (52, 1)] }, { coefficient := 1, powers := [(3, 1), (31, 1), (52, 1)] }, { coefficient := 1, powers := [(9, 1), (20, 1), (52, 1)] }, { coefficient := 1, powers := [(9, 1)] }, { coefficient := 1, powers := [(40, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (42, 1), (53, 1)] }, { coefficient := 1, powers := [(2, 1), (47, 1), (50, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (53, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1), (50, 1)] }, { coefficient := 1, powers := [(8, 1), (23, 1), (56, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (47, 1)] }, { coefficient := 1, powers := [(8, 1), (36, 1), (42, 1)] }, { coefficient := 1, powers := [(14, 1), (23, 1), (53, 1)] }, { coefficient := 1, powers := [(14, 1), (30, 1), (47, 1)] }, { coefficient := 1, powers := [(14, 1), (36, 1), (39, 1)] }, { coefficient := 1, powers := [(19, 1), (23, 1), (50, 1)] }, { coefficient := 1, powers := [(19, 1), (30, 1), (42, 1)] }, { coefficient := 1, powers := [(19, 1), (33, 1), (39, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(40, 1), (58, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(41, 1)] }],
  [{ coefficient := 1, powers := [(42, 1)] }],
  [{ coefficient := 1, powers := [(52, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 21 → SparsePoly (Fin 60) := ![
  [{ coefficient := -1, powers := [(5, 1), (30, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (25, 1), (33, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(23, 1), (25, 1)] }],
  [{ coefficient := -2, powers := [(23, 1), (50, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(18, 1), (50, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (5, 1), (56, 1)] }, { coefficient := -1, powers := [(5, 1), (24, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (33, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(23, 1), (53, 1)] }, { coefficient := -1, powers := [(30, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(47, 1)] }],
  [{ coefficient := 1, powers := [(19, 1)] }],
  [{ coefficient := 1, powers := [(14, 1)] }],
  [{ coefficient := 1, powers := [(50, 1)] }],
  [{ coefficient := 1, powers := [(23, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (30, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (33, 1), (53, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(39, 1), (56, 1)] }, { coefficient := -1, powers := [(47, 1), (50, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (33, 1), (53, 1)] }, { coefficient := 2, powers := [(19, 1), (23, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (5, 1), (30, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (53, 1)] }, { coefficient := 1, powers := [(8, 1), (36, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (5, 1), (33, 1), (40, 1), (53, 1), (58, 1)] }, { coefficient := -1, powers := [(3, 1), (5, 1), (31, 1), (33, 1), (53, 1), (58, 1)] }, { coefficient := -1, powers := [(5, 1), (9, 1), (20, 1), (33, 1), (53, 1), (58, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1), (23, 1), (53, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1), (30, 1), (47, 1)] }]
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
    ¬ ∀ index : Fin 21,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component1.SelectedLeafB4_4_1.selectedHasNoCommonZero

end Krenn.Component1.SelectedLeafB4_4_1
