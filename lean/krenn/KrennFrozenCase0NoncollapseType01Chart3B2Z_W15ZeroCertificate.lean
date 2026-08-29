import KrennSparseCertificate

/-!
A selected-row reflection of the strict frozen certificate for the
chart-3 both-pivots-live, zero-sum b2z/w15=0 leaf.
-/

namespace Krenn.FrozenCase0NoncollapseType01Chart3B2Z_W15ZeroCertificate

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "0be068765a0f50c694eb32b22e4e2bc97557eb3c9d04fc8e674e5a5772c047c2"
def certificateSHA256 : String := "b7586c006335a41b6af132ef59cd136550e1877f9c1bed24daa30ef6cb279267"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 10 → Fin 569 := ![
  13,
  31,
  40,
  84,
  99,
  273,
  277,
  416,
  562,
  568
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 10 → SparsePoly (Fin 64) := ![
  [{ coefficient := 1, powers := [(5, 1), (54, 1)] }, { coefficient := 1, powers := [(7, 1), (61, 1)] }, { coefficient := 1, powers := [(25, 1), (54, 1)] }, { coefficient := 1, powers := [(25, 1), (58, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := -1, powers := [(5, 1), (44, 1)] }, { coefficient := 1, powers := [(10, 1), (61, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := -1, powers := [(5, 1), (44, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (44, 1), (58, 1)] }, { coefficient := 1, powers := [(54, 1)] }, { coefficient := 1, powers := [(58, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (37, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (54, 1)] }, { coefficient := 1, powers := [(27, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (37, 1), (58, 1)] }, { coefficient := -1, powers := [(11, 1), (37, 1), (44, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1), (44, 1)] }, { coefficient := 1, powers := [(1, 1), (54, 1)] }, { coefficient := 1, powers := [(19, 1), (54, 1)] }, { coefficient := 1, powers := [(19, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (4, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(27, 1), (63, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 10 → SparsePoly (Fin 64) := ![
  [{ coefficient := 2, powers := [(5, 1), (44, 1)] }, { coefficient := 2, powers := [] }],
  [{ coefficient := -1, powers := [(5, 1), (54, 1)] }, { coefficient := -1, powers := [(5, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(5, 1)] }],
  [{ coefficient := -2, powers := [(5, 1), (8, 1), (44, 1), (61, 1)] }, { coefficient := -2, powers := [(8, 1), (61, 1)] }],
  [{ coefficient := 2, powers := [(1, 1), (4, 1), (5, 1), (63, 1)] }, { coefficient := 2, powers := [(4, 1), (5, 1), (19, 1), (63, 1)] }, { coefficient := -2, powers := [(5, 2), (44, 1), (63, 1)] }, { coefficient := 1, powers := [(5, 1), (10, 1), (61, 1), (63, 1)] }, { coefficient := -2, powers := [(5, 1), (25, 1), (44, 1), (63, 1)] }, { coefficient := -2, powers := [(5, 1), (63, 1)] }, { coefficient := -2, powers := [(25, 1), (63, 1)] }],
  [{ coefficient := 2, powers := [(5, 1), (7, 1), (44, 2), (61, 1)] }, { coefficient := 2, powers := [(7, 1), (44, 1), (61, 1)] }],
  [{ coefficient := 2, powers := [(5, 1), (7, 1), (44, 1), (61, 1)] }, { coefficient := 2, powers := [(7, 1), (61, 1)] }],
  [{ coefficient := -2, powers := [(4, 1), (5, 1)] }],
  [{ coefficient := 2, powers := [(5, 1), (44, 1)] }, { coefficient := -2, powers := [(5, 1), (58, 1)] }],
  [{ coefficient := -2, powers := [(1, 1), (4, 1), (5, 1), (54, 1)] }, { coefficient := -2, powers := [(1, 1), (4, 1), (5, 1), (58, 1)] }, { coefficient := -2, powers := [(4, 1), (5, 1), (19, 1), (54, 1)] }, { coefficient := -2, powers := [(4, 1), (5, 1), (19, 1), (58, 1)] }, { coefficient := 2, powers := [(5, 2), (44, 1), (54, 1)] }, { coefficient := 2, powers := [(5, 2), (44, 1), (58, 1)] }, { coefficient := -1, powers := [(5, 1), (10, 1), (54, 1), (61, 1)] }, { coefficient := -1, powers := [(5, 1), (10, 1), (58, 1), (61, 1)] }, { coefficient := 2, powers := [(5, 1), (25, 1), (44, 1), (54, 1)] }, { coefficient := 2, powers := [(5, 1), (25, 1), (44, 1), (58, 1)] }, { coefficient := 2, powers := [(5, 1), (54, 1)] }, { coefficient := 2, powers := [(5, 1), (58, 1)] }, { coefficient := 2, powers := [(25, 1), (54, 1)] }, { coefficient := 2, powers := [(25, 1), (58, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
/-- Lean replays the exact selected-row integer certificate. -/
theorem constantIdentity :
    ∑ index, (multipliers index).toPoly *
      (selectedEquations index).toPoly = C (2 : ℤ) := by
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
  have constantNonzero : ((2 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (2 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (2 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.FrozenCase0NoncollapseType01Chart3B2Z_W15ZeroCertificate.selectedHasNoCommonZero

end Krenn.FrozenCase0NoncollapseType01Chart3B2Z_W15ZeroCertificate
