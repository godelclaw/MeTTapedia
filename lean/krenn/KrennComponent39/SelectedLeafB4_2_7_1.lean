import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component39.SelectedLeafB4_2_7_1

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "c59c9f1c229e1960afd24755bafc2e43649bf08fcbada527dccb08e5c2a27eb8"
def certificateSHA256 : String := "cf0e9f25e2a82c69803e6ac4cbe03e767075dff899fa07f7223480c591315a67"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 24 → Fin 673 := ![
  14,
  26,
  232,
  280,
  300,
  304,
  305,
  318,
  319,
  452,
  511,
  515,
  580,
  602,
  603,
  604,
  644,
  659,
  661,
  662,
  669,
  670,
  671,
  672
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 24 → SparsePoly (Fin 67) := ![
  [{ coefficient := 1, powers := [(10, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (24, 1), (45, 1)] }, { coefficient := 1, powers := [(10, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (42, 1), (53, 1)] }, { coefficient := 1, powers := [(20, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1)] }, { coefficient := 1, powers := [(18, 1), (42, 1)] }, { coefficient := 1, powers := [(23, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (44, 1)] }, { coefficient := 1, powers := [(4, 1), (33, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (51, 1)] }, { coefficient := 1, powers := [(7, 1), (30, 1)] }, { coefficient := 1, powers := [(10, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (53, 1)] }, { coefficient := 1, powers := [(28, 1), (39, 1)] }, { coefficient := 1, powers := [(28, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1), (51, 1)] }, { coefficient := 1, powers := [(18, 1), (42, 1), (51, 1)] }, { coefficient := 1, powers := [(42, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1), (53, 1)] }, { coefficient := 1, powers := [(18, 1), (42, 1), (53, 1)] }, { coefficient := 1, powers := [(18, 1), (57, 1)] }, { coefficient := 1, powers := [(24, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (23, 1), (59, 1)] }, { coefficient := 1, powers := [(10, 1), (23, 1), (44, 1)] }, { coefficient := 1, powers := [(14, 1), (23, 1), (39, 1)] }, { coefficient := 1, powers := [(14, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (28, 1), (59, 1)] }, { coefficient := 1, powers := [(10, 1), (28, 1), (44, 1)] }, { coefficient := 1, powers := [(14, 1), (27, 1), (53, 1)] }, { coefficient := 1, powers := [(14, 1), (28, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1)] }, { coefficient := 1, powers := [(6, 1), (59, 1)] }, { coefficient := 1, powers := [(23, 1), (39, 1)] }, { coefficient := 1, powers := [(23, 1), (44, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(4, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (59, 1)] }, { coefficient := 1, powers := [(10, 1), (44, 1)] }, { coefficient := 1, powers := [(10, 1), (56, 1)] }, { coefficient := 1, powers := [(14, 1), (39, 1)] }, { coefficient := 1, powers := [(14, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (51, 1)] }, { coefficient := 1, powers := [(20, 1), (56, 1)] }, { coefficient := 1, powers := [(25, 1), (39, 1)] }, { coefficient := 1, powers := [(25, 1), (44, 1)] }, { coefficient := 1, powers := [(30, 1), (36, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (35, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1)] }, { coefficient := 1, powers := [(3, 1), (23, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (18, 1), (59, 1)] }, { coefficient := 1, powers := [(18, 1)] }, { coefficient := 1, powers := [(23, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (36, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (44, 1), (51, 1)] }, { coefficient := 1, powers := [(39, 1)] }, { coefficient := 1, powers := [(44, 1)] }, { coefficient := 1, powers := [(51, 1)] }, { coefficient := 1, powers := [(56, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (36, 1), (59, 1)] }, { coefficient := 1, powers := [(1, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(1, 1), (44, 1), (51, 1)] }, { coefficient := 1, powers := [(4, 1), (25, 1), (59, 1)] }, { coefficient := 1, powers := [(4, 1), (30, 1), (56, 1)] }, { coefficient := 1, powers := [(4, 1), (33, 1), (51, 1)] }, { coefficient := 1, powers := [(7, 1), (20, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (30, 1), (44, 1)] }, { coefficient := 1, powers := [(7, 1), (33, 1), (39, 1)] }, { coefficient := 1, powers := [(10, 1), (20, 1), (56, 1)] }, { coefficient := 1, powers := [(10, 1), (25, 1), (44, 1)] }, { coefficient := 1, powers := [(10, 1), (33, 1), (36, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1), (51, 1)] }, { coefficient := 1, powers := [(14, 1), (25, 1), (39, 1)] }, { coefficient := 1, powers := [(14, 1), (30, 1), (36, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (61, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1)] }],
  [{ coefficient := 1, powers := [(57, 1), (65, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(23, 1)] }],
  [{ coefficient := 1, powers := [(25, 1)] }],
  [{ coefficient := 1, powers := [(28, 1), (66, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 24 → SparsePoly (Fin 67) := ![
  [{ coefficient := -1, powers := [(20, 1), (24, 1), (35, 1), (56, 1), (59, 1), (65, 1)] }, { coefficient := -1, powers := [(24, 1), (30, 1), (35, 1), (44, 1), (56, 1), (65, 1)] }, { coefficient := -1, powers := [(24, 1), (30, 1), (35, 1), (56, 2), (65, 1)] }, { coefficient := -1, powers := [(24, 1), (33, 1), (35, 1), (39, 1), (44, 1), (65, 1)] }, { coefficient := -2, powers := [(24, 1), (33, 1), (35, 1), (39, 1), (56, 1), (65, 1)] }, { coefficient := -1, powers := [(24, 1), (33, 1), (35, 1), (39, 1), (61, 1), (65, 1)] }, { coefficient := -1, powers := [(24, 1), (33, 1), (35, 1), (44, 1), (51, 1), (65, 1)] }, { coefficient := -1, powers := [(24, 1), (33, 1), (35, 1), (44, 1), (61, 1), (65, 1)] }, { coefficient := -1, powers := [(24, 1), (33, 1), (35, 1), (51, 1), (61, 1), (65, 1)] }, { coefficient := -1, powers := [(24, 1), (33, 1), (35, 1), (56, 1), (61, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (35, 1), (42, 1), (56, 1), (59, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (35, 1), (56, 1), (59, 1), (65, 1)] }, { coefficient := 1, powers := [(30, 1), (35, 1), (44, 1), (56, 1), (65, 1)] }, { coefficient := 1, powers := [(30, 1), (35, 1), (56, 2), (65, 1)] }, { coefficient := 1, powers := [(33, 1), (35, 1), (39, 1), (44, 1), (65, 1)] }, { coefficient := 2, powers := [(33, 1), (35, 1), (39, 1), (56, 1), (65, 1)] }, { coefficient := 1, powers := [(33, 1), (35, 1), (39, 1), (61, 1), (65, 1)] }, { coefficient := 1, powers := [(33, 1), (35, 1), (44, 1), (51, 1), (65, 1)] }, { coefficient := 1, powers := [(33, 1), (35, 1), (44, 1), (61, 1), (65, 1)] }, { coefficient := 1, powers := [(33, 1), (35, 1), (51, 1), (61, 1), (65, 1)] }, { coefficient := 1, powers := [(33, 1), (35, 1), (56, 1), (61, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(10, 1), (35, 1), (56, 1), (59, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (44, 1), (51, 1), (65, 1)] }, { coefficient := -1, powers := [(44, 1), (53, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(35, 1), (39, 1), (59, 1)] }, { coefficient := -1, powers := [(35, 1), (51, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(35, 1), (44, 1), (59, 1)] }, { coefficient := 1, powers := [(35, 1), (56, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(14, 1), (20, 1), (35, 1), (59, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(24, 1), (44, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(44, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (35, 1), (44, 1), (59, 1)] }, { coefficient := 2, powers := [(20, 1), (35, 1), (51, 1), (59, 1)] }, { coefficient := 1, powers := [(20, 1), (35, 1), (56, 1), (59, 1)] }, { coefficient := 1, powers := [(30, 1), (35, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(30, 1), (35, 1), (51, 1), (56, 1)] }, { coefficient := 1, powers := [(33, 1), (35, 1), (36, 1), (59, 1)] }, { coefficient := 1, powers := [(33, 1), (35, 1), (39, 2)] }, { coefficient := 1, powers := [(33, 1), (35, 1), (39, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (35, 1), (59, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(18, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(20, 1), (28, 1), (35, 1), (59, 1), (66, 1)] }, { coefficient := -1, powers := [(30, 1), (35, 1), (56, 1)] }, { coefficient := -1, powers := [(33, 1), (35, 1), (39, 1)] }],
  [{ coefficient := -1, powers := [(14, 1), (35, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(61, 1)] }],
  [{ coefficient := -1, powers := [(10, 1), (33, 1), (35, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(35, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (33, 1), (35, 1), (36, 1), (59, 1)] }, { coefficient := 1, powers := [(10, 1), (33, 1), (35, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(10, 1), (33, 1), (35, 1), (44, 1), (51, 1)] }, { coefficient := 1, powers := [(18, 1), (44, 1)] }, { coefficient := -1, powers := [(35, 1), (59, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(35, 1), (36, 1), (59, 2)] }, { coefficient := -1, powers := [(35, 1), (39, 1), (44, 1), (59, 1)] }, { coefficient := -1, powers := [(35, 1), (39, 1), (56, 1), (59, 1)] }, { coefficient := 1, powers := [(35, 1), (44, 1), (51, 1), (59, 1)] }, { coefficient := -1, powers := [(35, 1), (51, 1), (56, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(10, 1), (30, 1), (35, 1), (44, 1), (56, 1)] }, { coefficient := -1, powers := [(10, 1), (30, 1), (35, 1), (56, 2)] }, { coefficient := -1, powers := [(10, 1), (33, 1), (35, 1), (39, 1), (44, 1)] }, { coefficient := -2, powers := [(10, 1), (33, 1), (35, 1), (39, 1), (56, 1)] }, { coefficient := -1, powers := [(10, 1), (33, 1), (35, 1), (39, 1), (61, 1)] }, { coefficient := -1, powers := [(10, 1), (33, 1), (35, 1), (44, 1), (51, 1)] }, { coefficient := -1, powers := [(10, 1), (33, 1), (35, 1), (44, 1), (61, 1)] }, { coefficient := -1, powers := [(10, 1), (33, 1), (35, 1), (51, 1), (61, 1)] }, { coefficient := -1, powers := [(10, 1), (33, 1), (35, 1), (56, 1), (61, 1)] }, { coefficient := -1, powers := [(18, 1), (44, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (59, 1), (61, 1)] }, { coefficient := -1, powers := [(4, 1), (20, 1), (35, 1), (44, 1), (59, 2)] }, { coefficient := -2, powers := [(4, 1), (20, 1), (35, 1), (51, 1), (59, 2)] }, { coefficient := -1, powers := [(4, 1), (20, 1), (35, 1), (56, 1), (59, 2)] }, { coefficient := -1, powers := [(4, 1), (30, 1), (35, 1), (39, 1), (56, 1), (59, 1)] }, { coefficient := -1, powers := [(4, 1), (30, 1), (35, 1), (51, 1), (56, 1), (59, 1)] }, { coefficient := -1, powers := [(4, 1), (33, 1), (35, 1), (36, 1), (59, 2)] }, { coefficient := -1, powers := [(4, 1), (33, 1), (35, 1), (39, 2), (59, 1)] }, { coefficient := -1, powers := [(4, 1), (33, 1), (35, 1), (39, 1), (51, 1), (59, 1)] }, { coefficient := -1, powers := [(10, 1), (20, 1), (35, 1), (44, 2), (59, 1)] }, { coefficient := -2, powers := [(10, 1), (20, 1), (35, 1), (44, 1), (51, 1), (59, 1)] }, { coefficient := -1, powers := [(10, 1), (20, 1), (35, 1), (44, 1), (56, 1), (59, 1)] }, { coefficient := -1, powers := [(10, 1), (30, 1), (35, 1), (39, 1), (44, 1), (56, 1)] }, { coefficient := -1, powers := [(10, 1), (30, 1), (35, 1), (44, 1), (51, 1), (56, 1)] }, { coefficient := -1, powers := [(10, 1), (33, 1), (35, 1), (36, 1), (44, 1), (59, 1)] }, { coefficient := -1, powers := [(10, 1), (33, 1), (35, 1), (39, 2), (44, 1)] }, { coefficient := -1, powers := [(10, 1), (33, 1), (35, 1), (39, 1), (44, 1), (51, 1)] }, { coefficient := -1, powers := [(14, 1), (20, 1), (35, 1), (39, 1), (44, 1), (59, 1)] }, { coefficient := -2, powers := [(14, 1), (20, 1), (35, 1), (39, 1), (51, 1), (59, 1)] }, { coefficient := -1, powers := [(14, 1), (20, 1), (35, 1), (39, 1), (56, 1), (59, 1)] }, { coefficient := -1, powers := [(14, 1), (30, 1), (35, 1), (39, 2), (56, 1)] }, { coefficient := -1, powers := [(14, 1), (30, 1), (35, 1), (39, 1), (51, 1), (56, 1)] }, { coefficient := -1, powers := [(14, 1), (33, 1), (35, 1), (36, 1), (39, 1), (59, 1)] }, { coefficient := -1, powers := [(14, 1), (33, 1), (35, 1), (39, 3)] }, { coefficient := -1, powers := [(14, 1), (33, 1), (35, 1), (39, 2), (51, 1)] }, { coefficient := 1, powers := [(18, 1), (39, 1), (61, 1)] }, { coefficient := 1, powers := [(18, 1), (44, 1), (61, 1)] }, { coefficient := -1, powers := [(24, 1), (42, 1), (44, 1), (51, 1), (65, 1)] }, { coefficient := 1, powers := [(42, 1), (44, 1), (53, 1), (65, 1)] }, { coefficient := -1, powers := [(61, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (35, 1), (59, 2)] }, { coefficient := -1, powers := [(10, 1), (35, 1), (56, 1), (59, 1)] }, { coefficient := 1, powers := [(14, 1), (35, 1), (44, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (20, 1), (35, 1), (59, 2)] }, { coefficient := 1, powers := [(10, 1), (20, 1), (35, 1), (56, 1), (59, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1), (35, 1), (39, 1), (59, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1), (35, 1), (44, 1), (59, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1), (35, 1), (51, 1), (59, 1)] }]
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
    (values : Fin 67 → R) :
    ¬ ∀ index : Fin 24,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component39.SelectedLeafB4_2_7_1.selectedHasNoCommonZero

end Krenn.Component39.SelectedLeafB4_2_7_1
