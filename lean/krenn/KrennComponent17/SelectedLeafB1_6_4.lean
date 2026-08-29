import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component17.SelectedLeafB1_6_4

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "92619a55b0371478a34376d4329a498abb94b0242f23c70b61b70f7d045aacaf"
def certificateSHA256 : String := "fa8aa62410552b8dd0738754d48c0d77d369f088e50e5bea8bdd3ad489f93a6b"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 17 → Fin 611 := ![
  17,
  18,
  19,
  27,
  32,
  214,
  311,
  434,
  441,
  468,
  469,
  601,
  602,
  604,
  607,
  608,
  610
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 17 → SparsePoly (Fin 63) := ![
  [{ coefficient := 1, powers := [(13, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(52, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (58, 1)] }, { coefficient := 1, powers := [(13, 1), (47, 1)] }, { coefficient := 1, powers := [(18, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (52, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1)] }, { coefficient := 1, powers := [(13, 1), (29, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (58, 1)] }, { coefficient := 1, powers := [(13, 1), (25, 1), (45, 1)] }, { coefficient := 1, powers := [(13, 1), (55, 1)] }, { coefficient := 1, powers := [(18, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (36, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1)] }, { coefficient := 1, powers := [(17, 1), (27, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (36, 1), (58, 1)] }, { coefficient := 1, powers := [(13, 1), (27, 1), (43, 1)] }, { coefficient := 1, powers := [(13, 1), (35, 1), (36, 1)] }, { coefficient := 1, powers := [(18, 1), (32, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (41, 1), (55, 1)] }, { coefficient := 1, powers := [(2, 1), (47, 1), (52, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (52, 1)] }, { coefficient := 1, powers := [(8, 1), (23, 1), (58, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (47, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(13, 1), (23, 1), (55, 1)] }, { coefficient := 1, powers := [(13, 1), (29, 1), (47, 1)] }, { coefficient := 1, powers := [(13, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (52, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (41, 1)] }, { coefficient := 1, powers := [(18, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (59, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(41, 1)] }],
  [{ coefficient := 1, powers := [(53, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(55, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 17 → SparsePoly (Fin 63) := ![
  [{ coefficient := 1, powers := [(27, 1), (38, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (25, 1), (36, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (36, 1), (47, 1), (57, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(22, 1), (59, 1), (62, 1)] }, { coefficient := -1, powers := [(27, 1), (59, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (36, 1), (47, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (35, 1), (36, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [(29, 1), (36, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [(36, 1), (47, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [(23, 1), (36, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(59, 1)] }],
  [{ coefficient := -1, powers := [(38, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(36, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (35, 1), (36, 1), (44, 1), (52, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [(36, 1), (57, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(8, 1), (35, 1), (36, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [(13, 1), (29, 1), (36, 1), (47, 1), (57, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (59, 1)] }, { coefficient := 1, powers := [(17, 1), (27, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (36, 1), (41, 1), (57, 1)] }, { coefficient := -1, powers := [(5, 1), (32, 1), (36, 1), (57, 1)] }]
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
    (values : Fin 63 → R) :
    ¬ ∀ index : Fin 17,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component17.SelectedLeafB1_6_4.selectedHasNoCommonZero

end Krenn.Component17.SelectedLeafB1_6_4
