import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component37.SelectedLeafB6_6_1

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "657b23cdf1761448e5ebcf9b7df27b3cb47d257243814ccf2934422409beca39"
def certificateSHA256 : String := "b361bf38c7c7395d1b6c0f911c1e23547752d8601b6655b92db6914faccecfae"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 14 → Fin 667 := ![
  3,
  149,
  221,
  313,
  427,
  581,
  583,
  608,
  658,
  659,
  661,
  662,
  665,
  666
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 14 → SparsePoly (Fin 67) := ![
  [{ coefficient := 1, powers := [(1, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (26, 1)] }, { coefficient := 1, powers := [(26, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (26, 1), (47, 1)] }, { coefficient := 1, powers := [(9, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(20, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(44, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (54, 1)] }, { coefficient := 1, powers := [(3, 1), (26, 1), (60, 1)] }, { coefficient := 1, powers := [(20, 1), (54, 1)] }, { coefficient := 1, powers := [(26, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (52, 1)] }, { coefficient := 1, powers := [(3, 1), (60, 1)] }, { coefficient := 1, powers := [(20, 1), (52, 1)] }, { coefficient := 1, powers := [(20, 1), (57, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (31, 1), (57, 1)] }, { coefficient := 1, powers := [(9, 1), (20, 1), (57, 1)] }, { coefficient := 1, powers := [(9, 1)] }, { coefficient := 1, powers := [(40, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (41, 1), (58, 1)] }, { coefficient := 1, powers := [(0, 1), (47, 1), (54, 1)] }, { coefficient := 1, powers := [(26, 1), (41, 1), (44, 1)] }, { coefficient := 1, powers := [(26, 1), (47, 1)] }, { coefficient := 1, powers := [(44, 1), (54, 1)] }, { coefficient := 1, powers := [(58, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(40, 1), (64, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(41, 1), (65, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(57, 1)] }],
  [{ coefficient := 1, powers := [(58, 1), (66, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 14 → SparsePoly (Fin 67) := ![
  [{ coefficient := 1, powers := [(0, 1), (41, 1), (44, 1), (62, 1), (63, 1), (65, 1), (66, 1)] }, { coefficient := -1, powers := [(0, 1), (47, 1), (62, 1), (63, 1), (65, 1), (66, 1)] }, { coefficient := 1, powers := [(20, 1), (41, 1), (44, 1), (62, 1), (63, 1), (65, 1), (66, 1)] }, { coefficient := -1, powers := [(44, 1), (62, 1), (63, 1), (65, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(47, 1), (62, 1), (64, 1), (65, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(62, 1), (64, 1), (65, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(26, 1), (41, 1), (62, 1), (65, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(41, 1), (44, 1), (62, 1), (65, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(26, 1), (41, 1), (44, 1), (62, 1), (65, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(58, 1), (62, 1), (64, 1), (65, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(62, 1), (65, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(41, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (41, 1), (44, 1), (54, 1), (62, 1), (65, 1), (66, 1)] }, { coefficient := 1, powers := [(0, 1), (47, 1), (54, 1), (62, 1), (65, 1), (66, 1)] }, { coefficient := -1, powers := [(20, 1), (41, 1), (44, 1), (54, 1), (62, 1), (65, 1), (66, 1)] }, { coefficient := 1, powers := [(44, 1), (54, 1), (62, 1), (65, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(26, 1), (47, 1), (62, 1), (65, 1), (66, 1)] }, { coefficient := 1, powers := [(58, 1), (62, 1), (65, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (40, 1), (58, 1), (62, 1), (64, 1), (65, 1), (66, 1)] }, { coefficient := 1, powers := [(3, 1), (31, 1), (58, 1), (62, 1), (64, 1), (65, 1), (66, 1)] }, { coefficient := 1, powers := [(9, 1), (20, 1), (58, 1), (62, 1), (64, 1), (65, 1), (66, 1)] }, { coefficient := -1, powers := [(20, 1), (26, 1), (41, 1), (44, 1), (62, 1), (65, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (41, 1), (62, 1), (65, 1)] }]
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
    ¬ ∀ index : Fin 14,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component37.SelectedLeafB6_6_1.selectedHasNoCommonZero

end Krenn.Component37.SelectedLeafB6_6_1
