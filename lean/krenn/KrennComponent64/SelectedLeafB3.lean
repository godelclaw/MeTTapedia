import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component64.SelectedLeafB3

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "092dde05478dd4212964b18e7ef91e75d2d773bec2d596d005ed2747bfb88188"
def certificateSHA256 : String := "2cef5ffee8d3054630c12db453153d2fb68776eb8a797a9cc65b403a6ce5c0c5"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 23 → Fin 638 := ![
  26,
  29,
  166,
  168,
  170,
  172,
  199,
  200,
  204,
  205,
  207,
  209,
  210,
  235,
  349,
  466,
  468,
  469,
  548,
  556,
  599,
  634,
  635
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 23 → SparsePoly (Fin 62) := ![
  [{ coefficient := 1, powers := [(23, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (45, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (52, 1)] }, { coefficient := 1, powers := [(18, 1), (27, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (58, 1)] }, { coefficient := 1, powers := [(18, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (58, 1)] }, { coefficient := 1, powers := [(18, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (52, 1)] }, { coefficient := 1, powers := [(27, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (38, 1)] }, { coefficient := 1, powers := [(27, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1), (52, 1)] }, { coefficient := 1, powers := [(52, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1), (53, 1)] }, { coefficient := 1, powers := [(53, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1), (50, 1)] }, { coefficient := 1, powers := [(45, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1), (50, 1)] }, { coefficient := 1, powers := [(46, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (34, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (23, 1), (58, 1)] }, { coefficient := 1, powers := [(23, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (46, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1)] }, { coefficient := 1, powers := [(19, 1), (23, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (53, 1)] }, { coefficient := 1, powers := [(27, 1), (39, 1)] }, { coefficient := 1, powers := [(27, 1), (45, 1), (48, 1)] }, { coefficient := 1, powers := [(30, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (38, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(41, 1), (52, 1)] }, { coefficient := 1, powers := [(56, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (39, 1), (55, 1)] }, { coefficient := 1, powers := [(0, 1), (45, 1), (51, 1)] }, { coefficient := 1, powers := [(39, 1)] }, { coefficient := 1, powers := [(45, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (41, 1), (52, 1)] }, { coefficient := 1, powers := [(23, 1), (56, 1)] }, { coefficient := 1, powers := [(27, 1), (46, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1)] }, { coefficient := 1, powers := [(6, 1), (58, 1)] }, { coefficient := 1, powers := [(24, 1), (38, 1)] }, { coefficient := 1, powers := [(24, 1), (43, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (36, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (45, 1), (52, 1)] }, { coefficient := 1, powers := [(5, 1), (27, 1), (58, 1)] }, { coefficient := 1, powers := [(8, 1), (23, 1), (58, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (52, 1)] }, { coefficient := 1, powers := [(18, 1), (27, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (36, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (46, 1), (53, 1)] }, { coefficient := 1, powers := [(5, 1), (27, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (53, 1)] }, { coefficient := 1, powers := [(8, 1), (23, 1), (59, 1)] }, { coefficient := 1, powers := [(8, 1), (30, 1), (46, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (39, 1)] }, { coefficient := 1, powers := [(13, 1), (23, 1), (56, 1)] }, { coefficient := 1, powers := [(13, 1), (27, 1), (46, 1)] }, { coefficient := 1, powers := [(13, 1), (33, 1), (36, 1)] }, { coefficient := 1, powers := [(19, 1), (23, 1), (53, 1)] }, { coefficient := 1, powers := [(19, 1), (27, 1), (39, 1)] }, { coefficient := 1, powers := [(19, 1), (30, 1), (36, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 23 → SparsePoly (Fin 62) := ![
  [{ coefficient := -2, powers := [(13, 1), (52, 1)] }],
  [{ coefficient := -2, powers := [(19, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(34, 1), (52, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(34, 1), (45, 1), (59, 1)] }],
  [{ coefficient := -2, powers := [(6, 1), (27, 1), (59, 1)] }, { coefficient := 2, powers := [(27, 1), (34, 1), (59, 1)] }],
  [{ coefficient := -2, powers := [(6, 1), (23, 1), (59, 1)] }, { coefficient := 2, powers := [(23, 1), (34, 1), (59, 1)] }],
  [{ coefficient := 2, powers := [(6, 1), (18, 1), (59, 1)] }, { coefficient := -1, powers := [(18, 1), (34, 1), (59, 1)] }],
  [{ coefficient := -2, powers := [(5, 1), (24, 1), (59, 1)] }],
  [{ coefficient := -2, powers := [(2, 1), (39, 1), (41, 1)] }, { coefficient := -2, powers := [(5, 1), (30, 1), (41, 1)] }],
  [{ coefficient := -2, powers := [(2, 1), (46, 1)] }, { coefficient := -2, powers := [(19, 1), (23, 1)] }],
  [{ coefficient := -2, powers := [(8, 1), (33, 1), (48, 1)] }],
  [{ coefficient := 2, powers := [(2, 1), (53, 1)] }, { coefficient := 2, powers := [(8, 1), (30, 1)] }],
  [{ coefficient := 2, powers := [(36, 1), (59, 1)] }],
  [{ coefficient := 2, powers := [(8, 1), (59, 1)] }],
  [{ coefficient := 2, powers := [(53, 1)] }],
  [{ coefficient := 2, powers := [(19, 1)] }],
  [{ coefficient := 2, powers := [(2, 1), (39, 1)] }, { coefficient := 2, powers := [(5, 1), (30, 1)] }],
  [{ coefficient := 2, powers := [(8, 1), (33, 1)] }],
  [{ coefficient := 2, powers := [(13, 1)] }],
  [{ coefficient := 2, powers := [(5, 1), (27, 1), (59, 1)] }],
  [{ coefficient := -2, powers := [(34, 1), (59, 1)] }],
  [{ coefficient := -2, powers := [] }],
  [{ coefficient := -2, powers := [(2, 1), (38, 1), (39, 1), (56, 1)] }, { coefficient := 2, powers := [(2, 1), (39, 1), (41, 1), (43, 1), (52, 1)] }, { coefficient := -2, powers := [(2, 1), (39, 1), (44, 1), (52, 1)] }, { coefficient := 2, powers := [(2, 1), (43, 1), (46, 1), (53, 1)] }, { coefficient := -2, powers := [(2, 1), (46, 1), (50, 1), (53, 1)] }, { coefficient := -2, powers := [(5, 1), (27, 1), (43, 1), (59, 1)] }, { coefficient := -2, powers := [(5, 1), (30, 1), (38, 1), (56, 1)] }, { coefficient := 2, powers := [(5, 1), (30, 1), (41, 1), (43, 1), (52, 1)] }, { coefficient := -2, powers := [(5, 1), (30, 1), (44, 1), (52, 1)] }, { coefficient := -2, powers := [(8, 1), (30, 1), (46, 1), (50, 1)] }, { coefficient := -2, powers := [(8, 1), (33, 1), (39, 1), (55, 1)] }, { coefficient := 2, powers := [(8, 1), (33, 1), (45, 1), (48, 1), (50, 1)] }, { coefficient := -2, powers := [(8, 1), (33, 1), (45, 1), (51, 1)] }, { coefficient := 2, powers := [(19, 1), (23, 1), (43, 1), (53, 1)] }]
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
    (values : Fin 62 → R) :
    ¬ ∀ index : Fin 23,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((2 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (2 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (2 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component64.SelectedLeafB3.selectedHasNoCommonZero

end Krenn.Component64.SelectedLeafB3
