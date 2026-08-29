import KrennSparseCertificate

/-!
A concrete strict certificate reflected from frozen sparse data.
The hashes bind this generated theorem to the externally replayed inputs.
-/

namespace Krenn.C6NoncollapseSlot0Strict11

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "25dd0040f699ab024fe5e7a55d9a3bd8cc1c6b54491b3ac69838ad757573d586"
def certificateSHA256 : String := "662fe277d5aee22dd0a62a065ce0de89d2804e735f91cbb7b665ac8136239f75"
def generatedModule : String := "KrennC6NoncollapseSlot0Strict11"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def parentEquations : Fin 11 → SparsePoly (Fin 65) := ![
  [{ coefficient := 1, powers := [(9, 1), (28, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (51, 1)] }, { coefficient := 1, powers := [(18, 1), (28, 1), (40, 1)] }, { coefficient := 1, powers := [(18, 1), (33, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (23, 1), (59, 1)] }, { coefficient := 1, powers := [(10, 1), (28, 1), (43, 1)] }, { coefficient := 1, powers := [(10, 1), (35, 1), (37, 1)] }, { coefficient := 1, powers := [(17, 1), (23, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (28, 1)] }, { coefficient := 1, powers := [(21, 1), (23, 1), (51, 1)] }, { coefficient := 1, powers := [(21, 1), (28, 1), (40, 1)] }, { coefficient := 1, powers := [(21, 1), (33, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (23, 1), (59, 1)] }, { coefficient := 1, powers := [(13, 1), (28, 1), (43, 1)] }, { coefficient := 1, powers := [(13, 1), (35, 1), (37, 1)] }, { coefficient := 1, powers := [(20, 1), (23, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (23, 1), (60, 1)] }, { coefficient := 1, powers := [(12, 1)] }, { coefficient := 1, powers := [(21, 1), (23, 1), (53, 1)] }, { coefficient := 1, powers := [(21, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (23, 1), (60, 1)] }, { coefficient := 1, powers := [(13, 1)] }, { coefficient := 1, powers := [(21, 1), (23, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (28, 1), (45, 1)] }, { coefficient := 1, powers := [(13, 1), (59, 1)] }, { coefficient := 1, powers := [(20, 1), (28, 1), (41, 1)] }, { coefficient := 1, powers := [(20, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (28, 1), (46, 1)] }, { coefficient := 1, powers := [(21, 1), (28, 1), (41, 1)] }, { coefficient := 1, powers := [(21, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (59, 1)] }, { coefficient := 1, powers := [(28, 1), (43, 1)] }, { coefficient := 1, powers := [(35, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (51, 1)] }, { coefficient := 1, powers := [(28, 1), (40, 1)] }, { coefficient := 1, powers := [(33, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (9, 1), (20, 1)] }, { coefficient := -1, powers := [(0, 1), (12, 1), (17, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedIndices : Fin 11 → Fin 11 := ![
  0,
  1,
  2,
  3,
  4,
  5,
  6,
  7,
  8,
  9,
  10
]

def selectedEquations : Fin 11 → SparsePoly (Fin 65) :=
  fun index => parentEquations (selectedIndices index)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 11 → SparsePoly (Fin 65) := ![
  [{ coefficient := -1, powers := [(0, 2), (9, 1), (13, 1), (20, 1), (45, 1)] }, { coefficient := -1, powers := [(0, 2), (9, 1), (20, 2), (41, 1)] }, { coefficient := -1, powers := [(0, 2), (13, 1), (17, 1), (20, 1), (40, 1), (46, 1)] }, { coefficient := -1, powers := [(0, 2), (17, 1), (20, 1), (21, 1), (40, 1), (41, 1)] }],
  [{ coefficient := -1, powers := [(0, 2), (9, 1), (12, 1), (13, 1), (59, 1), (60, 1)] }, { coefficient := -1, powers := [(0, 2), (9, 1), (12, 1), (21, 1), (54, 1), (59, 1)] }, { coefficient := -1, powers := [(0, 2), (12, 2), (17, 1), (60, 1)] }, { coefficient := -1, powers := [(0, 2), (12, 1), (17, 1), (21, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(0, 2), (9, 1), (13, 1), (17, 1), (45, 1)] }, { coefficient := 1, powers := [(0, 2), (9, 1), (17, 1), (20, 1), (41, 1)] }, { coefficient := 1, powers := [(0, 2), (13, 1), (17, 2), (40, 1), (46, 1)] }, { coefficient := 1, powers := [(0, 2), (17, 2), (21, 1), (40, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(0, 2), (9, 2), (13, 1), (59, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 2), (9, 2), (21, 1), (54, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 2), (9, 1), (12, 1), (17, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 2), (9, 1), (17, 1), (21, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (17, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (9, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (9, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (17, 1), (40, 1)] }],
  [{ coefficient := -1, powers := [(0, 2), (9, 2), (13, 2), (59, 1), (60, 1)] }, { coefficient := -1, powers := [(0, 2), (9, 2), (13, 1), (21, 1), (54, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 2), (9, 1), (10, 1), (12, 1), (13, 1), (59, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 2), (9, 1), (10, 1), (12, 1), (21, 1), (54, 1), (59, 1)] }, { coefficient := -1, powers := [(0, 2), (9, 1), (12, 1), (13, 1), (17, 1), (60, 1)] }, { coefficient := -1, powers := [(0, 2), (9, 1), (13, 1), (17, 1), (21, 1), (53, 1)] }, { coefficient := 1, powers := [(0, 2), (10, 1), (12, 2), (17, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 2), (10, 1), (12, 1), (17, 1), (21, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(0, 2), (9, 1), (13, 1), (17, 1), (21, 1), (45, 1)] }, { coefficient := 1, powers := [(0, 2), (9, 1), (13, 1), (18, 1), (20, 1), (45, 1)] }, { coefficient := -1, powers := [(0, 2), (9, 1), (17, 1), (20, 1), (21, 1), (41, 1)] }, { coefficient := 1, powers := [(0, 2), (9, 1), (18, 1), (20, 2), (41, 1)] }, { coefficient := -1, powers := [(0, 2), (13, 1), (17, 2), (21, 1), (40, 1), (46, 1)] }, { coefficient := 1, powers := [(0, 2), (13, 1), (17, 1), (18, 1), (20, 1), (40, 1), (46, 1)] }, { coefficient := -1, powers := [(0, 2), (17, 2), (21, 2), (40, 1), (41, 1)] }, { coefficient := 1, powers := [(0, 2), (17, 1), (18, 1), (20, 1), (21, 1), (40, 1), (41, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (9, 1), (13, 1), (23, 1), (59, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (9, 1), (13, 1), (28, 1), (45, 1)] }, { coefficient := 1, powers := [(0, 1), (9, 1), (20, 1), (28, 1), (41, 1)] }, { coefficient := -1, powers := [(0, 1), (9, 1), (21, 1), (23, 1), (54, 1), (59, 1)] }, { coefficient := -1, powers := [(0, 1), (12, 1), (17, 1), (23, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (13, 1), (17, 1), (28, 1), (40, 1), (46, 1)] }, { coefficient := -1, powers := [(0, 1), (17, 1), (21, 1), (23, 1), (53, 1)] }, { coefficient := 1, powers := [(0, 1), (17, 1), (21, 1), (28, 1), (40, 1), (41, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
/-- Lean replays the externally discovered identity from the frozen
integer term lists. -/
theorem constantIdentity :
    ∑ index, (multipliers index).toPoly *
      (selectedEquations index).toPoly = C (1 : ℤ) := by
  simp (config := { maxSteps := 1000000 })
    [Fin.sum_univ_succ, multipliers, selectedEquations,
    selectedIndices, parentEquations,
    SparsePoly.toPoly, SparseTerm.toPoly]
  ring

/-- The selected generator subfamily already has no common zero. -/
theorem selectedHasNoCommonZero {R : Type*} [CommRing R] [Nontrivial R] [CharZero R]
    (values : Fin 65 → R) :
    ¬ ∀ index : Fin 11,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

/-- The reflected integer certificate rules out a common zero of the
complete frozen family over every characteristic-zero commutative ring. -/
theorem parentHasNoCommonZero {R : Type*} [CommRing R] [Nontrivial R] [CharZero R]
    (values : Fin 65 → R) :
    ¬ ∀ index : Fin 11,
      eval₂Hom (Int.castRingHom R) values
        (parentEquations index).toPoly = 0 := by
  intro parentZero
  have selectedZero : ∀ index,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
    intro index
    exact parentZero (selectedIndices index)
  exact (selectedHasNoCommonZero values) selectedZero

#print axioms Krenn.C6NoncollapseSlot0Strict11.parentHasNoCommonZero

end Krenn.C6NoncollapseSlot0Strict11
