import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component47.SelectedLeafB5_3

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "dcd719359398b79fddd29863f5b8d781b5e136c2b82f14ad8f67b966e17cb1a1"
def certificateSHA256 : String := "41a44b511ddfc67b5b133f27884f85d28ddb50b31019de686e230de88a720bb4"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 23 → Fin 593 := ![
  0,
  1,
  21,
  31,
  40,
  261,
  262,
  341,
  365,
  382,
  401,
  481,
  529,
  544,
  545,
  550,
  551,
  577,
  584,
  589,
  590,
  591,
  592
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 23 → SparsePoly (Fin 62) := ![
  [{ coefficient := 1, powers := [(2, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(15, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (36, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (40, 1), (52, 1)] }, { coefficient := 1, powers := [(18, 1), (28, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(15, 1), (21, 1), (50, 1)] }, { coefficient := 1, powers := [(15, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (55, 1)] }, { coefficient := 1, powers := [(9, 1), (52, 1)] }, { coefficient := 1, powers := [(15, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (41, 1), (52, 1)] }, { coefficient := 1, powers := [(6, 1), (33, 1), (41, 1)] }, { coefficient := 1, powers := [(15, 1), (25, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (36, 1), (55, 1)] }, { coefficient := 1, powers := [(2, 1), (39, 1), (52, 1)] }, { coefficient := 1, powers := [(2, 1), (42, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1), (49, 1)] }, { coefficient := 1, powers := [(3, 1), (33, 1), (49, 1)] }, { coefficient := 1, powers := [(15, 1), (20, 1), (49, 1)] }, { coefficient := 1, powers := [(42, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (49, 1)] }, { coefficient := 1, powers := [(3, 1), (56, 1)] }, { coefficient := 1, powers := [(20, 1), (49, 1)] }, { coefficient := 1, powers := [(20, 1), (53, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1)] }, { coefficient := 1, powers := [(3, 1), (33, 1)] }, { coefficient := 1, powers := [(15, 1), (20, 1)] }, { coefficient := 1, powers := [(20, 1), (52, 1)] }, { coefficient := 1, powers := [(25, 1), (42, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1)] }, { coefficient := 1, powers := [(6, 1), (30, 1)] }, { coefficient := 1, powers := [(9, 1), (25, 1)] }, { coefficient := 1, powers := [(20, 1), (47, 1)] }, { coefficient := 1, powers := [(25, 1), (39, 1)] }, { coefficient := 1, powers := [(30, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (36, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1)] }, { coefficient := 1, powers := [(3, 1), (25, 1), (56, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1), (56, 1)] }, { coefficient := 1, powers := [(20, 1)] }, { coefficient := 1, powers := [(25, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1), (48, 1)] }, { coefficient := 1, powers := [(3, 1), (33, 1), (48, 1)] }, { coefficient := 1, powers := [(3, 1), (55, 1)] }, { coefficient := 1, powers := [(9, 1), (42, 1)] }, { coefficient := 1, powers := [(15, 1), (20, 1), (48, 1)] }, { coefficient := 1, powers := [(15, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (39, 1), (53, 1)] }, { coefficient := 1, powers := [(0, 1), (48, 1)] }, { coefficient := 1, powers := [(3, 1), (30, 1), (53, 1)] }, { coefficient := 1, powers := [(9, 1), (20, 1), (53, 1)] }, { coefficient := 1, powers := [(9, 1)] }, { coefficient := 1, powers := [(20, 1), (48, 1)] }, { coefficient := 1, powers := [(39, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (36, 1), (55, 1)] }, { coefficient := 1, powers := [(0, 1), (39, 1), (52, 1)] }, { coefficient := 1, powers := [(0, 1), (42, 1), (47, 1)] }, { coefficient := 1, powers := [(3, 1), (25, 1), (55, 1)] }, { coefficient := 1, powers := [(3, 1), (30, 1), (52, 1)] }, { coefficient := 1, powers := [(3, 1), (33, 1), (47, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1), (55, 1)] }, { coefficient := 1, powers := [(6, 1), (30, 1), (42, 1)] }, { coefficient := 1, powers := [(6, 1), (33, 1), (39, 1)] }, { coefficient := 1, powers := [(9, 1), (20, 1), (52, 1)] }, { coefficient := 1, powers := [(9, 1), (25, 1), (42, 1)] }, { coefficient := 1, powers := [(9, 1), (33, 1), (36, 1)] }, { coefficient := 1, powers := [(15, 1), (20, 1), (47, 1)] }, { coefficient := 1, powers := [(15, 1), (25, 1), (39, 1)] }, { coefficient := 1, powers := [(15, 1), (30, 1), (36, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (59, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(39, 1)] }],
  [{ coefficient := 1, powers := [(40, 1), (60, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(41, 1), (61, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 23 → SparsePoly (Fin 62) := ![
  [{ coefficient := 1, powers := [(0, 1), (9, 1), (25, 1), (49, 1), (59, 1)] }, { coefficient := -1, powers := [(0, 1), (9, 1), (59, 1)] }, { coefficient := -1, powers := [(0, 1), (25, 1), (48, 1), (59, 1)] }, { coefficient := 1, powers := [(9, 1), (20, 1), (25, 1), (49, 1), (59, 1)] }, { coefficient := -1, powers := [(9, 1), (25, 1), (59, 1)] }, { coefficient := -1, powers := [(20, 1), (25, 1), (48, 1), (59, 1)] }, { coefficient := -1, powers := [(30, 1), (36, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (3, 1), (33, 1), (53, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (3, 1), (42, 1), (56, 1), (59, 1)] }, { coefficient := -1, powers := [(0, 1), (42, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (15, 1), (20, 1), (56, 1), (59, 1)] }, { coefficient := -1, powers := [(3, 1), (20, 1), (33, 1), (53, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (33, 1), (59, 1)] }, { coefficient := -1, powers := [(20, 1), (42, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (20, 1), (21, 1), (61, 1)] }, { coefficient := -1, powers := [(21, 1), (30, 1), (36, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (3, 1), (28, 1), (30, 1), (53, 1), (59, 1), (60, 1)] }, { coefficient := -1, powers := [(3, 1), (20, 1), (28, 1), (30, 1), (53, 1), (59, 1), (60, 1)] }, { coefficient := -1, powers := [(3, 1), (28, 1), (30, 1), (59, 1), (60, 1)] }, { coefficient := 1, powers := [(9, 1), (20, 1), (28, 1), (59, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(3, 2), (55, 1), (56, 1), (61, 1)] }, { coefficient := -1, powers := [(3, 1), (9, 1), (33, 1), (53, 1), (61, 1)] }, { coefficient := 1, powers := [(3, 1), (15, 1), (30, 1), (53, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (9, 1), (33, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (3, 1), (30, 1), (53, 1), (59, 1), (60, 1)] }, { coefficient := 1, powers := [(3, 1), (20, 1), (30, 1), (53, 1), (59, 1), (60, 1)] }, { coefficient := 1, powers := [(3, 1), (30, 1), (59, 1), (60, 1)] }, { coefficient := -1, powers := [(9, 1), (20, 1), (59, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(9, 1), (20, 1), (61, 1)] }, { coefficient := 1, powers := [(30, 1), (36, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (20, 1), (56, 1)] }, { coefficient := 1, powers := [(20, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (30, 1), (53, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (3, 1), (56, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (9, 1)] }, { coefficient := 1, powers := [(9, 1), (20, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (20, 1), (52, 1)] }, { coefficient := 1, powers := [(9, 1), (33, 1), (36, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (9, 1), (49, 1)] }, { coefficient := 1, powers := [(0, 1), (48, 1)] }, { coefficient := -1, powers := [(9, 1), (20, 1), (49, 1)] }, { coefficient := 1, powers := [(9, 1)] }, { coefficient := 1, powers := [(20, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (33, 1), (53, 1)] }, { coefficient := 1, powers := [(42, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(0, 1)] }, { coefficient := -1, powers := [(20, 1)] }],
  [{ coefficient := -1, powers := [(20, 1), (52, 1)] }, { coefficient := -1, powers := [(33, 1), (36, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(0, 1), (3, 1), (30, 1), (40, 1), (52, 1), (53, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (3, 1), (33, 1), (47, 1), (53, 1)] }, { coefficient := 1, powers := [(0, 1), (3, 1), (36, 1), (55, 1), (56, 1)] }, { coefficient := -1, powers := [(0, 1), (9, 1), (25, 1), (42, 1), (49, 1)] }, { coefficient := 1, powers := [(0, 1), (9, 1), (42, 1)] }, { coefficient := 1, powers := [(0, 1), (25, 1), (42, 1), (48, 1)] }, { coefficient := -1, powers := [(0, 1), (36, 1), (55, 1)] }, { coefficient := 1, powers := [(3, 1), (9, 1), (33, 1), (36, 1), (56, 1)] }, { coefficient := 1, powers := [(3, 1), (9, 1), (33, 1)] }, { coefficient := -1, powers := [(3, 1), (15, 1), (20, 1), (47, 1), (56, 1)] }, { coefficient := -1, powers := [(3, 1), (20, 1), (30, 1), (40, 1), (52, 1), (53, 1), (60, 1)] }, { coefficient := 1, powers := [(3, 1), (20, 1), (33, 1), (47, 1), (53, 1)] }, { coefficient := -1, powers := [(3, 1), (30, 1), (40, 1), (52, 1), (60, 1)] }, { coefficient := -1, powers := [(3, 1), (33, 1), (47, 1)] }, { coefficient := -1, powers := [(9, 1), (20, 1), (25, 1), (42, 1), (49, 1)] }, { coefficient := 1, powers := [(9, 1), (20, 1), (40, 1), (52, 1), (60, 1)] }, { coefficient := 1, powers := [(9, 1), (25, 1), (42, 1)] }, { coefficient := 1, powers := [(20, 1), (25, 1), (42, 1), (48, 1)] }, { coefficient := 1, powers := [(20, 1), (42, 1), (47, 1)] }, { coefficient := 1, powers := [(30, 1), (36, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (2, 1), (3, 1), (52, 1), (56, 1), (59, 1)] }, { coefficient := -1, powers := [(0, 1), (2, 1), (52, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (15, 1)] }, { coefficient := 1, powers := [(0, 1), (20, 1), (52, 1), (53, 1)] }, { coefficient := 1, powers := [(0, 1), (33, 1), (36, 1), (53, 1)] }, { coefficient := 1, powers := [(0, 1), (52, 1)] }, { coefficient := -1, powers := [(3, 1), (25, 1), (33, 1), (53, 1)] }, { coefficient := 1, powers := [(6, 1), (33, 1)] }, { coefficient := 1, powers := [(15, 1), (20, 1)] }, { coefficient := 1, powers := [(15, 1), (25, 1)] }, { coefficient := 1, powers := [(20, 1), (52, 1)] }, { coefficient := -1, powers := [(25, 1), (42, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (3, 1), (30, 1), (52, 1), (53, 1)] }, { coefficient := -1, powers := [(3, 1), (20, 1), (30, 1), (52, 1), (53, 1)] }, { coefficient := -1, powers := [(3, 1), (30, 1), (52, 1)] }, { coefficient := 1, powers := [(9, 1), (20, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (3, 1), (30, 1), (52, 1), (53, 1)] }, { coefficient := 1, powers := [(3, 2), (25, 1), (55, 1), (56, 1)] }, { coefficient := 1, powers := [(3, 1), (6, 1), (30, 1), (33, 1), (53, 1)] }, { coefficient := 1, powers := [(3, 1), (9, 1), (25, 1), (33, 1), (53, 1)] }, { coefficient := 1, powers := [(9, 1), (15, 1), (20, 1)] }, { coefficient := -1, powers := [(15, 1), (30, 1), (36, 1)] }]
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
    ¬ ∀ index : Fin 23,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component47.SelectedLeafB5_3.selectedHasNoCommonZero

end Krenn.Component47.SelectedLeafB5_3
