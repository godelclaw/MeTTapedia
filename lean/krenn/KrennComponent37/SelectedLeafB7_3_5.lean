import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component37.SelectedLeafB7_3_5

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "90dbed2e5c2a307ec2481cf56b5fd3ac086acd8ab91966d2ffe224a26a87d409"
def certificateSHA256 : String := "eff41227d43f05694c78710afb281cb625a5ae39a5865f3f71faaf92f4f7f0c5"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 13 → Fin 667 := ![
  0,
  175,
  256,
  307,
  393,
  426,
  436,
  502,
  609,
  659,
  660,
  663,
  665
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 13 → SparsePoly (Fin 69) := ![
  [{ coefficient := 1, powers := [(1, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (20, 1)] }, { coefficient := 1, powers := [(18, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (25, 1), (46, 1)] }, { coefficient := 1, powers := [(18, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (46, 1)] }, { coefficient := 1, powers := [(12, 1), (57, 1)] }, { coefficient := 1, powers := [(18, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (20, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1)] }, { coefficient := 1, powers := [(18, 1), (20, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (53, 1)] }, { coefficient := 1, powers := [(20, 1), (51, 1), (57, 1)] }, { coefficient := 1, powers := [(20, 1), (53, 1)] }, { coefficient := 1, powers := [(51, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (53, 1)] }, { coefficient := 1, powers := [(12, 1), (23, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1), (29, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (33, 1), (57, 1)] }, { coefficient := 1, powers := [(23, 1), (51, 1), (57, 1)] }, { coefficient := 1, powers := [(23, 1), (53, 1)] }, { coefficient := 1, powers := [(29, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (48, 1), (53, 1)] }, { coefficient := 1, powers := [(21, 1), (51, 1), (57, 1)] }, { coefficient := 1, powers := [(21, 1), (53, 1)] }, { coefficient := 1, powers := [(42, 1)] }, { coefficient := 1, powers := [(48, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (64, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(42, 1), (66, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(57, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 13 → SparsePoly (Fin 69) := ![
  [{ coefficient := 1, powers := [(20, 1), (53, 1), (63, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(21, 1), (29, 1), (53, 1), (64, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(21, 1), (29, 1), (64, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (25, 1), (29, 1), (64, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (29, 1), (64, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(48, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(21, 1), (64, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (21, 1), (64, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(66, 1)] }],
  [{ coefficient := -1, powers := [(20, 1), (48, 1), (53, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (53, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(0, 1), (42, 1), (66, 1)] }, { coefficient := -1, powers := [(3, 1), (18, 1), (21, 1), (33, 1), (64, 1), (66, 1)] }, { coefficient := -1, powers := [(12, 1), (20, 1), (21, 1), (29, 1), (64, 1), (66, 1)] }, { coefficient := 1, powers := [(12, 1), (21, 1), (23, 1), (64, 1), (66, 1)] }, { coefficient := -1, powers := [(12, 1), (21, 1), (25, 1), (29, 1), (64, 1), (66, 1)] }, { coefficient := -1, powers := [(18, 1), (21, 1), (23, 1), (51, 1), (64, 1), (66, 1)] }, { coefficient := 1, powers := [(20, 1), (48, 1), (51, 1), (66, 1)] }, { coefficient := -1, powers := [(21, 1), (51, 1), (66, 1)] }]
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
    (values : Fin 69 → R) :
    ¬ ∀ index : Fin 13,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component37.SelectedLeafB7_3_5.selectedHasNoCommonZero

end Krenn.Component37.SelectedLeafB7_3_5
