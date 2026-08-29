import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.FrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB3W34NonzeroCertificate

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "4e42ca569c86ea28217fcbb28e3e89bb95e4e7afdda25a454c4bfa7a3a19ef24"
def certificateSHA256 : String := "c06484157b524b396b2b33788a458bceb57757af723a277392408f055c30481f"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 11 → Fin 553 := ![
  139,
  165,
  291,
  416,
  434,
  493,
  511,
  541,
  547,
  549,
  551
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 11 → SparsePoly (Fin 67) := ![
  [{ coefficient := 1, powers := [(37, 1), (47, 1)] }, { coefficient := 1, powers := [(37, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(37, 1), (55, 1)] }, { coefficient := 1, powers := [(43, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (45, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(15, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (63, 1)] }, { coefficient := 1, powers := [(23, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(15, 1), (40, 1)] }, { coefficient := 1, powers := [(23, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(15, 1), (43, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (45, 1), (63, 1)] }, { coefficient := 1, powers := [(12, 1), (37, 1), (63, 1)] }, { coefficient := 1, powers := [(15, 1), (32, 1), (63, 1)] }, { coefficient := 1, powers := [(15, 1), (40, 1), (55, 1)] }, { coefficient := 1, powers := [(15, 1), (43, 1), (48, 1)] }, { coefficient := 1, powers := [(23, 1), (37, 1), (55, 1)] }, { coefficient := 1, powers := [(23, 1), (43, 1), (45, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(5, 1), (47, 1)] }, { coefficient := 1, powers := [(5, 1), (52, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(8, 1), (65, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 11 → SparsePoly (Fin 67) := ![
  [{ coefficient := 2, powers := [(5, 1), (12, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(23, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(32, 1)] }],
  [{ coefficient := -1, powers := [(37, 1)] }],
  [{ coefficient := 1, powers := [(55, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (48, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(15, 1), (43, 1), (48, 1)] }],
  [{ coefficient := -2, powers := [(12, 1), (37, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(9, 1), (45, 1), (63, 1)] }]
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
    ¬ ∀ index : Fin 11,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.FrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB3W34NonzeroCertificate.selectedHasNoCommonZero

end Krenn.FrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB3W34NonzeroCertificate
