import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component6.SelectedLeafB3

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "1ae5fd6df02ffe083a3550461896cda651e123f5a8ae8a4b8edab31783a6e2a2"
def certificateSHA256 : String := "aedc893d9f57b2073430bff2a7c462d33189857f06a31c47aeaf03e327d6f8c1"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 21 → Fin 606 := ![
  1,
  3,
  5,
  15,
  193,
  211,
  228,
  240,
  261,
  310,
  369,
  372,
  375,
  385,
  386,
  387,
  394,
  406,
  602,
  603,
  605
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 21 → SparsePoly (Fin 61) := ![
  [{ coefficient := 1, powers := [(2, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (55, 1)] }, { coefficient := 1, powers := [(26, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(41, 1), (44, 1)] }, { coefficient := 1, powers := [(44, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (37, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (30, 1), (57, 1)] }, { coefficient := 1, powers := [(30, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (24, 1), (57, 1)] }, { coefficient := 1, powers := [(24, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (19, 1), (54, 1)] }, { coefficient := 1, powers := [(13, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1)] }, { coefficient := 1, powers := [(20, 1), (44, 1)] }, { coefficient := 1, powers := [(25, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (47, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (58, 1)] }, { coefficient := 1, powers := [(13, 1), (55, 1)] }, { coefficient := 1, powers := [(18, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (52, 1)] }, { coefficient := 1, powers := [(30, 1), (42, 1)] }, { coefficient := 1, powers := [(33, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (55, 1)] }, { coefficient := 1, powers := [(30, 1), (47, 1)] }, { coefficient := 1, powers := [(36, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (41, 1), (55, 1)] }, { coefficient := 1, powers := [(26, 1), (41, 1), (44, 1)] }, { coefficient := 1, powers := [(55, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1), (51, 1)] }, { coefficient := 1, powers := [(20, 1), (44, 1), (51, 1)] }, { coefficient := 1, powers := [(47, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (39, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (57, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (39, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (42, 1), (55, 1)] }, { coefficient := 1, powers := [(2, 1), (47, 1), (52, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1), (52, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (58, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (47, 1)] }, { coefficient := 1, powers := [(8, 1), (36, 1), (42, 1)] }, { coefficient := 1, powers := [(13, 1), (24, 1), (55, 1)] }, { coefficient := 1, powers := [(13, 1), (30, 1), (47, 1)] }, { coefficient := 1, powers := [(13, 1), (36, 1), (39, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (52, 1)] }, { coefficient := 1, powers := [(18, 1), (30, 1), (42, 1)] }, { coefficient := 1, powers := [(18, 1), (33, 1), (39, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (60, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 21 → SparsePoly (Fin 61) := ![
  [{ coefficient := -1, powers := [(2, 1), (19, 1), (42, 1), (55, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (25, 1), (33, 1), (47, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (30, 1), (58, 1)] }, { coefficient := 1, powers := [(30, 1), (37, 1), (58, 1)] }, { coefficient := -1, powers := [(33, 1), (37, 1), (55, 1)] }],
  [{ coefficient := -2, powers := [(6, 1), (24, 1), (58, 1)] }, { coefficient := 1, powers := [(24, 1), (37, 1), (58, 1)] }, { coefficient := -1, powers := [(36, 1), (37, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (26, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (42, 1), (51, 1)] }, { coefficient := -1, powers := [(13, 1), (24, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (26, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (33, 1), (55, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (36, 1), (42, 1), (60, 1)] }, { coefficient := 1, powers := [(39, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (58, 1)] }],
  [{ coefficient := 2, powers := [(8, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (33, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(52, 1)] }],
  [{ coefficient := -1, powers := [(24, 1)] }],
  [{ coefficient := 1, powers := [(18, 1)] }],
  [{ coefficient := 1, powers := [(13, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (33, 1)] }],
  [{ coefficient := -1, powers := [(37, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(2, 1), (41, 1), (42, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (19, 1), (42, 1), (51, 1), (55, 1)] }, { coefficient := -1, powers := [(5, 1), (33, 1), (37, 1), (55, 1), (57, 1)] }, { coefficient := -1, powers := [(5, 1), (33, 1), (55, 1)] }, { coefficient := -1, powers := [(8, 1), (25, 1), (33, 1), (47, 1), (51, 1)] }, { coefficient := -1, powers := [(8, 1), (36, 1), (37, 1), (42, 1), (57, 1)] }, { coefficient := -1, powers := [(8, 1), (36, 1), (42, 1)] }]
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
    ¬ ∀ index : Fin 21,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component6.SelectedLeafB3.selectedHasNoCommonZero

end Krenn.Component6.SelectedLeafB3
