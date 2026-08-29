import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component24.SelectedLeafB1_3

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "a5407ab59affec30957f36275cf8ecaf15d8fea46d86dfa987ac89b4688b35fb"
def certificateSHA256 : String := "d33fd8a675f4ad5c82b1a7bc35b9bb6a6b5ae993de5dfa88a83a51347af5e092"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 15 → Fin 670 := ![
  153,
  316,
  322,
  357,
  368,
  425,
  461,
  480,
  488,
  509,
  571,
  614,
  664,
  666,
  669
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 15 → SparsePoly (Fin 65) := ![
  [{ coefficient := 1, powers := [(18, 1), (20, 1)] }, { coefficient := 1, powers := [(18, 1), (26, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (46, 1)] }, { coefficient := 1, powers := [(14, 1), (57, 1)] }, { coefficient := 1, powers := [(18, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (53, 1)] }, { coefficient := 1, powers := [(25, 1), (57, 1)] }, { coefficient := 1, powers := [(30, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (46, 1), (51, 1)] }, { coefficient := 1, powers := [(14, 1), (29, 1), (46, 1)] }, { coefficient := 1, powers := [(18, 1), (30, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (26, 1), (60, 1)] }, { coefficient := 1, powers := [(18, 1), (21, 1)] }, { coefficient := 1, powers := [(18, 1), (26, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (20, 1), (53, 1)] }, { coefficient := 1, powers := [(18, 1), (20, 1), (57, 1)] }, { coefficient := 1, powers := [(18, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (60, 1)] }, { coefficient := 1, powers := [(18, 1), (21, 1), (53, 1)] }, { coefficient := 1, powers := [(18, 1), (21, 1), (57, 1)] }, { coefficient := 1, powers := [(18, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1), (54, 1)] }, { coefficient := 1, powers := [(46, 1), (51, 1)] }, { coefficient := 1, powers := [(51, 1), (57, 1)] }, { coefficient := 1, powers := [(54, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (48, 1), (53, 1)] }, { coefficient := 1, powers := [(21, 1), (53, 1)] }, { coefficient := 1, powers := [(21, 1), (57, 1)] }, { coefficient := 1, powers := [(48, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (48, 1), (51, 1)] }, { coefficient := 1, powers := [(14, 1), (29, 1), (48, 1)] }, { coefficient := 1, powers := [(18, 1), (25, 1), (51, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (21, 1), (57, 1)] }, { coefficient := 1, powers := [(14, 1), (48, 1)] }, { coefficient := 1, powers := [(18, 1), (21, 1), (54, 1)] }, { coefficient := 1, powers := [(18, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (48, 1), (54, 1)] }, { coefficient := 1, powers := [(21, 1), (51, 1), (57, 1)] }, { coefficient := 1, powers := [(21, 1), (54, 1)] }, { coefficient := 1, powers := [(43, 1)] }, { coefficient := 1, powers := [(48, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(0, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(43, 1), (64, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 15 → SparsePoly (Fin 65) := ![
  [{ coefficient := -1, powers := [(25, 1), (51, 1), (53, 1), (62, 1), (64, 1)] }, { coefficient := -1, powers := [(25, 1), (51, 1), (57, 1), (62, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(21, 1), (29, 1), (62, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (26, 1), (51, 1), (62, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (62, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(30, 1), (51, 1), (62, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (51, 1), (62, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(26, 1), (30, 1), (51, 1), (62, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (21, 1), (62, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(18, 1), (26, 1), (30, 1), (51, 1), (62, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(62, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (62, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (62, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (21, 1), (46, 1), (54, 1), (62, 1), (64, 1)] }, { coefficient := -1, powers := [(2, 1), (43, 1), (57, 1), (62, 1), (64, 1)] }, { coefficient := -1, powers := [(2, 1), (48, 1), (54, 1), (62, 1), (64, 1)] }, { coefficient := 1, powers := [(18, 1), (26, 1), (30, 1), (48, 1), (51, 1), (53, 1), (62, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(43, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [] }]
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
    ¬ ∀ index : Fin 15,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component24.SelectedLeafB1_3.selectedHasNoCommonZero

end Krenn.Component24.SelectedLeafB1_3
