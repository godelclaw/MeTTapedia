import KrennSparseCertificate

/-!
A selected-row reflection of the strict frozen certificate for the
chart-3, both-pivots-live, zero-sum `b0z0/w14!=0` leaf.
-/

namespace Krenn.FrozenCase0NoncollapseType01Chart3B0Z0W14NonzeroCertificate

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "5a983de95746210b7e62fc760c4253c90602f8567bd1be0103d955d3a0310286"
def certificateSHA256 : String := "e78e971237c2f28f30bd5a20545adf3ead4cc88652f094f4f63982f1b0f90ef4"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 10 → Fin 499 := ![
  244, 245, 368, 371, 395, 398, 443, 464, 470, 491
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 10 → SparsePoly (Fin 64) := ![
  [{ coefficient := 1, powers := [(8, 1), (35, 1), (58, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(8, 1), (35, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (45, 1)] }, { coefficient := 1, powers := [(24, 1), (40, 1)] }, { coefficient := 1, powers := [(24, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (45, 1)] }, { coefficient := 1, powers := [(24, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (48, 1)] }, { coefficient := 1, powers := [(24, 1), (26, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (62, 1)] }, { coefficient := 1, powers := [(17, 1), (48, 1)] }, { coefficient := 1, powers := [(24, 1), (26, 1), (53, 1)] }, { coefficient := 1, powers := [(24, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (45, 1)] }, { coefficient := 1, powers := [(16, 1), (31, 1), (45, 1)] }, { coefficient := 1, powers := [(24, 1), (31, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (45, 1), (56, 1)] }, { coefficient := 1, powers := [(17, 1), (33, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (48, 1)] }, { coefficient := 1, powers := [(9, 1), (38, 1)] }, { coefficient := 1, powers := [(16, 1), (31, 1), (48, 1)] }, { coefficient := 1, powers := [(24, 1), (28, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (41, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (48, 1), (56, 1)] }, { coefficient := 1, powers := [(9, 1), (33, 1), (62, 1)] }, { coefficient := 1, powers := [(9, 1), (36, 1), (59, 1)] }, { coefficient := 1, powers := [(9, 1), (38, 1), (56, 1)] }, { coefficient := 1, powers := [(17, 1), (28, 1), (59, 1)] }, { coefficient := 1, powers := [(17, 1), (33, 1), (48, 1)] }, { coefficient := 1, powers := [(24, 1), (28, 1), (56, 1)] }, { coefficient := 1, powers := [(24, 1), (33, 1), (41, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 10 → SparsePoly (Fin 64) := ![
  [{ coefficient := -1, powers := [(6, 1), (41, 1), (59, 1)] }, { coefficient := -1, powers := [(9, 1), (36, 1), (59, 1)] }, { coefficient := -1, powers := [(17, 1), (28, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (41, 1), (58, 1)] }, { coefficient := 1, powers := [(9, 1), (36, 1), (58, 1)] }, { coefficient := 1, powers := [(17, 1), (28, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(26, 1), (31, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [(26, 1), (33, 1)] }],
  [{ coefficient := -1, powers := [(31, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(33, 1)] }],
  [{ coefficient := -1, powers := [(26, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(26, 1)] }],
  [{ coefficient := 1, powers := [(56, 1)] }],
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
    (values : Fin 64 → R) :
    ¬ ∀ index : Fin 10,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.FrozenCase0NoncollapseType01Chart3B0Z0W14NonzeroCertificate.selectedHasNoCommonZero

end Krenn.FrozenCase0NoncollapseType01Chart3B0Z0W14NonzeroCertificate
