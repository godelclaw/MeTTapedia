import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.FrozenCase0NoncollapseType01Chart3B6Certificate

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "f8f0e8bf999d82940877a8b39ecf129c8574e89a95f94047b52ac2c39aa62d30"
def certificateSHA256 : String := "ba81ac65707865acea3bc361cb542cff5234935c73e71df2ee868a644ccf3d8e"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 16 → Fin 469 := ![
  0,
  9,
  80,
  328,
  330,
  337,
  338,
  354,
  363,
  370,
  389,
  395,
  461,
  464,
  467,
  468
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 16 → SparsePoly (Fin 63) := ![
  [{ coefficient := 1, powers := [(5, 1), (41, 1), (58, 1)] }, { coefficient := 1, powers := [(8, 1), (29, 1), (58, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (55, 1)] }, { coefficient := 1, powers := [(11, 1), (23, 1), (58, 1)] }, { coefficient := 1, powers := [(17, 1), (35, 1), (41, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(8, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (25, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(16, 1), (35, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (23, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1)] }, { coefficient := 1, powers := [(16, 1), (29, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (23, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (35, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (35, 1), (46, 1)] }, { coefficient := 1, powers := [(13, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (29, 1), (58, 1)] }, { coefficient := 1, powers := [(10, 1), (35, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (36, 1)] }, { coefficient := 1, powers := [(16, 1), (31, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (25, 1)] }, { coefficient := 1, powers := [(10, 1), (39, 1)] }, { coefficient := 1, powers := [(16, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (4, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(3, 1), (23, 1)] }, { coefficient := 1, powers := [(3, 1), (29, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(31, 1), (61, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(25, 1), (62, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 16 → SparsePoly (Fin 63) := ![
  [{ coefficient := -1, powers := [(1, 1), (4, 1)] }, { coefficient := -1, powers := [(4, 1), (13, 1), (36, 1), (61, 1)] }, { coefficient := -1, powers := [(4, 1), (16, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (4, 1), (29, 1)] }, { coefficient := 1, powers := [(4, 1), (13, 1), (29, 1), (36, 1), (61, 1)] }, { coefficient := 1, powers := [(4, 1), (16, 1), (29, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (16, 1), (29, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (17, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (4, 1), (31, 1), (61, 1)] }, { coefficient := -1, powers := [(3, 1), (4, 1)] }, { coefficient := 1, powers := [(4, 1), (11, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (11, 1), (36, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (5, 1), (36, 1), (41, 1), (46, 1), (61, 1)] }, { coefficient := 1, powers := [(4, 1), (8, 1), (36, 1), (55, 1), (61, 1)] }, { coefficient := 1, powers := [(4, 1), (17, 1), (36, 1), (41, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (5, 1), (36, 1), (41, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (8, 1), (39, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (5, 1), (39, 1), (41, 1), (62, 1)] }, { coefficient := 1, powers := [(4, 1), (8, 1), (29, 1), (39, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (5, 1), (41, 1), (58, 1), (62, 1)] }, { coefficient := 1, powers := [(4, 1), (8, 1), (35, 1), (55, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (23, 1), (31, 1), (61, 1)] }, { coefficient := 1, powers := [(3, 1), (23, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(4, 1), (16, 1), (31, 1), (61, 1)] }, { coefficient := 1, powers := [(4, 1), (16, 1)] }, { coefficient := -1, powers := [(31, 1), (61, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(3, 1), (29, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(1, 1), (4, 1), (5, 1), (41, 1), (58, 1)] }, { coefficient := -1, powers := [(1, 1), (4, 1), (8, 1), (35, 1), (55, 1)] }, { coefficient := -1, powers := [(4, 1), (5, 1), (16, 1), (41, 1), (58, 1)] }, { coefficient := -1, powers := [(4, 1), (8, 1), (16, 1), (35, 1), (55, 1)] }, { coefficient := 1, powers := [(4, 1), (11, 1), (16, 1), (29, 1), (58, 1)] }]
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
    ¬ ∀ index : Fin 16,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.FrozenCase0NoncollapseType01Chart3B6Certificate.selectedHasNoCommonZero

end Krenn.FrozenCase0NoncollapseType01Chart3B6Certificate
