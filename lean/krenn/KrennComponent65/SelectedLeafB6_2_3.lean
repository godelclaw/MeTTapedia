import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component65.SelectedLeafB6_2_3

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "724c4f480d717a2572bb1fa1f199f007c36d62970c2af259920a1f6a4ad26bb8"
def certificateSHA256 : String := "8028974d13cb8a1cfb5e581b6c5c80ec9e77fe4d399902077cad5c67126dc1e2"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 22 → Fin 671 := ![
  12,
  15,
  18,
  19,
  24,
  26,
  29,
  212,
  302,
  309,
  310,
  320,
  420,
  421,
  423,
  479,
  540,
  661,
  664,
  667,
  669,
  670
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 22 → SparsePoly (Fin 66) := ![
  [{ coefficient := 1, powers := [(5, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (20, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(28, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (23, 1), (59, 1)] }, { coefficient := 1, powers := [(23, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1)] }, { coefficient := 1, powers := [(20, 1), (42, 1)] }, { coefficient := 1, powers := [(24, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (47, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1)] }, { coefficient := 1, powers := [(13, 1), (28, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1), (51, 1)] }, { coefficient := 1, powers := [(20, 1), (42, 1), (51, 1)] }, { coefficient := 1, powers := [(47, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (60, 1)] }, { coefficient := 1, powers := [(13, 1), (47, 1)] }, { coefficient := 1, powers := [(18, 1), (20, 1), (52, 1)] }, { coefficient := 1, powers := [(18, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (60, 1)] }, { coefficient := 1, powers := [(13, 1), (25, 1), (45, 1)] }, { coefficient := 1, powers := [(13, 1), (57, 1)] }, { coefficient := 1, powers := [(18, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (54, 1)] }, { coefficient := 1, powers := [(28, 1), (40, 1)] }, { coefficient := 1, powers := [(28, 1), (46, 1), (49, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (40, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (56, 1)] }, { coefficient := 1, powers := [(13, 1), (23, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (42, 1), (53, 1)] }, { coefficient := 1, powers := [(23, 1), (57, 1)] }, { coefficient := 1, powers := [(28, 1), (47, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (37, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (47, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (28, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (23, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1), (47, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (40, 1)] }, { coefficient := 1, powers := [(13, 1), (23, 1), (57, 1)] }, { coefficient := 1, powers := [(13, 1), (28, 1), (47, 1)] }, { coefficient := 1, powers := [(13, 1), (34, 1), (37, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (54, 1)] }, { coefficient := 1, powers := [(18, 1), (28, 1), (40, 1)] }, { coefficient := 1, powers := [(18, 1), (31, 1), (37, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(40, 1)] }],
  [{ coefficient := 1, powers := [(56, 1), (64, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(57, 1), (65, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 22 → SparsePoly (Fin 66) := ![
  [{ coefficient := -2, powers := [(6, 1), (34, 1), (54, 1), (57, 1), (65, 1)] }, { coefficient := 2, powers := [(6, 1), (34, 1), (54, 1)] }],
  [{ coefficient := -2, powers := [(6, 1), (23, 1), (60, 1)] }],
  [{ coefficient := -2, powers := [(28, 1), (47, 1), (51, 1), (57, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(23, 1), (45, 1), (57, 1), (65, 1)] }, { coefficient := 2, powers := [(23, 1), (45, 1)] }],
  [{ coefficient := -1, powers := [(28, 1), (52, 1), (57, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(13, 1), (53, 1), (57, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(18, 1), (46, 1), (57, 1), (65, 1)] }],
  [{ coefficient := 2, powers := [(8, 1), (60, 1)] }, { coefficient := -2, powers := [(18, 1), (54, 1), (57, 1), (65, 1)] }, { coefficient := 2, powers := [(18, 1), (54, 1)] }],
  [{ coefficient := 2, powers := [(13, 1), (28, 1), (51, 1), (57, 1), (65, 1)] }],
  [{ coefficient := 2, powers := [(6, 1), (54, 1), (57, 1), (59, 1), (65, 1)] }, { coefficient := -2, powers := [(6, 1), (54, 1), (59, 1)] }, { coefficient := 1, powers := [(54, 1), (57, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(47, 1), (57, 1), (65, 1)] }],
  [{ coefficient := -2, powers := [(13, 1), (28, 1), (57, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(28, 1), (57, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (57, 1), (65, 1)] }, { coefficient := -2, powers := [(23, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (57, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(57, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (57, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(57, 1), (65, 1)] }],
  [{ coefficient := -2, powers := [(6, 1), (47, 1), (54, 1), (57, 1), (59, 1), (65, 1)] }, { coefficient := 2, powers := [(6, 1), (47, 1), (54, 1), (59, 1)] }, { coefficient := 1, powers := [(37, 1), (57, 1), (60, 1), (65, 1)] }, { coefficient := -1, powers := [(40, 1), (56, 1), (57, 1), (64, 1)] }, { coefficient := 1, powers := [(40, 1), (57, 2), (65, 1)] }, { coefficient := -1, powers := [(46, 1), (52, 1), (57, 1), (64, 1)] }, { coefficient := -1, powers := [(47, 1), (54, 1), (57, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (34, 1), (57, 1), (65, 1)] }, { coefficient := -1, powers := [(18, 1), (28, 1), (57, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (31, 1), (57, 1)] }, { coefficient := -1, powers := [(13, 1), (23, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (31, 1), (57, 1)] }, { coefficient := -1, powers := [(13, 1), (23, 1), (57, 1)] }, { coefficient := -1, powers := [] }]
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
    (values : Fin 66 → R) :
    ¬ ∀ index : Fin 22,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component65.SelectedLeafB6_2_3.selectedHasNoCommonZero

end Krenn.Component65.SelectedLeafB6_2_3
