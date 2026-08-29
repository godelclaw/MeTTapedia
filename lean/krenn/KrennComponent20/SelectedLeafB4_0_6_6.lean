import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component20.SelectedLeafB4_0_6_6

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "fad6ae05eba1b6e8fea1efe8306ddaa4915cb049f1ba5770bb408b0482031a46"
def certificateSHA256 : String := "f6a18ec0c847753a0665232dd9b302549371bccc39b500dadcf824538ad70ad4"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 17 → Fin 648 := ![
  30,
  188,
  189,
  191,
  315,
  353,
  462,
  466,
  480,
  551,
  635,
  638,
  640,
  641,
  644,
  646,
  647
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 17 → SparsePoly (Fin 65) := ![
  [{ coefficient := 1, powers := [(27, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (53, 1)] }, { coefficient := 1, powers := [(29, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (43, 1)] }, { coefficient := 1, powers := [(28, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (52, 1)] }, { coefficient := 1, powers := [(29, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (25, 1), (40, 1)] }, { coefficient := 1, powers := [(19, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (59, 1)] }, { coefficient := 1, powers := [(13, 1), (56, 1)] }, { coefficient := 1, powers := [(19, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (47, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1)] }, { coefficient := 1, powers := [(18, 1), (28, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (53, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1)] }, { coefficient := 1, powers := [(13, 1), (29, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (53, 1)] }, { coefficient := 1, powers := [(29, 1), (41, 1)] }, { coefficient := 1, powers := [(29, 1), (46, 1), (49, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (43, 1), (52, 1)] }, { coefficient := 1, powers := [(24, 1), (56, 1)] }, { coefficient := 1, powers := [(29, 1), (47, 1)] }, { coefficient := 1, powers := [(35, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (41, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (47, 1), (53, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (53, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (59, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (47, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(13, 1), (24, 1), (56, 1)] }, { coefficient := 1, powers := [(13, 1), (29, 1), (47, 1)] }, { coefficient := 1, powers := [(13, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (53, 1)] }, { coefficient := 1, powers := [(19, 1), (29, 1), (41, 1)] }, { coefficient := 1, powers := [(19, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(40, 1)] }],
  [{ coefficient := 1, powers := [(41, 1)] }],
  [{ coefficient := 1, powers := [(56, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (64, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(29, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 17 → SparsePoly (Fin 65) := ![
  [{ coefficient := 1, powers := [(18, 1), (24, 1), (53, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(18, 1), (47, 1)] }],
  [{ coefficient := -1, powers := [(18, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(13, 1), (43, 1)] }],
  [{ coefficient := -2, powers := [(24, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(24, 1)] }],
  [{ coefficient := 1, powers := [(53, 1)] }],
  [{ coefficient := 1, powers := [(47, 1)] }],
  [{ coefficient := 1, powers := [(19, 1)] }],
  [{ coefficient := 1, powers := [(13, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(38, 1), (59, 1)] }, { coefficient := 1, powers := [(41, 1), (56, 1)] }, { coefficient := -1, powers := [(47, 1), (53, 1)] }],
  [{ coefficient := 2, powers := [(19, 1), (24, 1), (25, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (35, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (32, 1)] }, { coefficient := -1, powers := [(13, 1), (24, 1)] }],
  [{ coefficient := -1, powers := [(18, 1), (24, 1), (43, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (59, 1)] }, { coefficient := 1, powers := [(13, 1), (43, 1), (46, 1)] }, { coefficient := -1, powers := [(13, 1), (47, 1)] }, { coefficient := 1, powers := [(18, 1), (47, 1), (49, 1)] }, { coefficient := -1, powers := [(19, 1), (46, 1), (49, 1)] }]
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
    (values : Fin 65 → R) :
    ¬ ∀ index : Fin 17,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component20.SelectedLeafB4_0_6_6.selectedHasNoCommonZero

end Krenn.Component20.SelectedLeafB4_0_6_6
