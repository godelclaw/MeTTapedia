import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component52.SelectedLeafB1

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "67633c152c268731eb25d551866ba9aa919c15b05c26aaffa1969da9ef56b46f"
def certificateSHA256 : String := "108c80a687911fb5e5989703f8f2c27f61df6f9b50bd5a81ee16ef7ba1a9fb8c"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 19 → Fin 637 := ![
  5,
  6,
  8,
  9,
  11,
  202,
  203,
  205,
  207,
  208,
  221,
  233,
  353,
  354,
  467,
  468,
  487,
  633,
  634
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 19 → SparsePoly (Fin 61) := ![
  [{ coefficient := 1, powers := [(2, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1), (51, 1)] }, { coefficient := 1, powers := [(51, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1), (53, 1)] }, { coefficient := 1, powers := [(53, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1), (50, 1)] }, { coefficient := 1, powers := [(45, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1), (50, 1)] }, { coefficient := 1, powers := [(47, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (36, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (29, 1), (58, 1)] }, { coefficient := 1, powers := [(29, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (23, 1), (58, 1)] }, { coefficient := 1, powers := [(23, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (53, 1)] }, { coefficient := 1, powers := [(29, 1), (41, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (56, 1)] }, { coefficient := 1, powers := [(29, 1), (47, 1)] }, { coefficient := 1, powers := [(35, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (40, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (45, 1), (52, 1)] }, { coefficient := 1, powers := [(25, 1), (45, 1)] }, { coefficient := 1, powers := [(56, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (41, 1), (55, 1)] }, { coefficient := 1, powers := [(0, 1), (46, 1), (51, 1)] }, { coefficient := 1, powers := [(20, 1), (51, 1)] }, { coefficient := 1, powers := [(41, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (58, 1)] }, { coefficient := 1, powers := [(8, 1), (23, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (41, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (47, 1), (53, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (53, 1)] }, { coefficient := 1, powers := [(8, 1), (23, 1), (59, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (47, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(13, 1), (23, 1), (56, 1)] }, { coefficient := 1, powers := [(13, 1), (29, 1), (47, 1)] }, { coefficient := 1, powers := [(13, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (53, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (41, 1)] }, { coefficient := 1, powers := [(18, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 19 → SparsePoly (Fin 61) := ![
  [{ coefficient := 1, powers := [(36, 1), (46, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (29, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (36, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (23, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (36, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (20, 1), (35, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (35, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (25, 1), (41, 1)] }, { coefficient := -1, powers := [(5, 1), (25, 1), (32, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (53, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1)] }],
  [{ coefficient := 1, powers := [(38, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(18, 1)] }],
  [{ coefficient := 1, powers := [(13, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (41, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (35, 1)] }],
  [{ coefficient := -1, powers := [(36, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (25, 1), (41, 1), (45, 1), (50, 1)] }, { coefficient := -1, powers := [(2, 1), (40, 1), (41, 1), (56, 1)] }, { coefficient := -1, powers := [(2, 1), (41, 1), (45, 1), (52, 1)] }, { coefficient := -1, powers := [(2, 1), (47, 1), (50, 1), (53, 1)] }, { coefficient := 1, powers := [(5, 1), (25, 1), (32, 1), (45, 1), (50, 1)] }, { coefficient := -1, powers := [(5, 1), (32, 1), (40, 1), (56, 1)] }, { coefficient := -1, powers := [(5, 1), (32, 1), (45, 1), (52, 1)] }, { coefficient := -1, powers := [(5, 1), (35, 1), (44, 1), (53, 1)] }, { coefficient := 1, powers := [(8, 1), (20, 1), (35, 1), (44, 1), (51, 1)] }, { coefficient := -1, powers := [(8, 1), (32, 1), (47, 1), (50, 1)] }, { coefficient := -1, powers := [(8, 1), (35, 1), (41, 1), (55, 1)] }, { coefficient := -1, powers := [(8, 1), (35, 1), (46, 1), (51, 1)] }]
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
    ¬ ∀ index : Fin 19,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component52.SelectedLeafB1.selectedHasNoCommonZero

end Krenn.Component52.SelectedLeafB1
