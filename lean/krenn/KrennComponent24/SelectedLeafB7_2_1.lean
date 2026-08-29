import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component24.SelectedLeafB7_2_1

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "2df5983f004b0dbe50906ad6da3965bb6983dd377182be851ac3c81c0709d441"
def certificateSHA256 : String := "dfd0cbd37314251bdc181c94d88c71e049a6e273acc76f135af9de2ba62535d3"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 13 → Fin 673 := ![
  17,
  166,
  449,
  455,
  470,
  472,
  503,
  652,
  656,
  664,
  666,
  671,
  672
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 13 → SparsePoly (Fin 67) := ![
  [{ coefficient := 1, powers := [(18, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1), (58, 1)] }, { coefficient := 1, powers := [(58, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (46, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (42, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (46, 1)] }, { coefficient := 1, powers := [(18, 1), (30, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (53, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (53, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (57, 1)] }, { coefficient := 1, powers := [(18, 1), (30, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (42, 1)] }, { coefficient := 1, powers := [(18, 1), (46, 1)] }, { coefficient := 1, powers := [(18, 1), (53, 1)] }, { coefficient := 1, powers := [(18, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(30, 1), (42, 1)] }, { coefficient := 1, powers := [(30, 1), (46, 1)] }, { coefficient := 1, powers := [(30, 1), (53, 1)] }, { coefficient := 1, powers := [(30, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (39, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (42, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (46, 1), (53, 1)] }, { coefficient := 1, powers := [(42, 1)] }, { coefficient := 1, powers := [(46, 1)] }, { coefficient := 1, powers := [(53, 1)] }, { coefficient := 1, powers := [(57, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (39, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (42, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (46, 1), (53, 1)] }, { coefficient := 1, powers := [(18, 1), (30, 1), (42, 1)] }, { coefficient := 1, powers := [(18, 1), (30, 1), (46, 1)] }, { coefficient := 1, powers := [(18, 1), (30, 1), (53, 1)] }, { coefficient := 1, powers := [(18, 1), (30, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (64, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(57, 1)] }],
  [{ coefficient := 1, powers := [(58, 1), (66, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 13 → SparsePoly (Fin 67) := ![
  [{ coefficient := -1, powers := [(0, 2), (24, 1), (38, 1), (46, 1), (53, 1), (60, 1), (64, 1), (66, 1)] }, { coefficient := -1, powers := [(0, 2), (24, 1), (39, 1), (60, 1), (64, 1), (66, 1)] }, { coefficient := 1, powers := [(0, 2), (24, 1), (42, 1), (53, 1), (64, 1), (66, 1)] }, { coefficient := -1, powers := [(0, 2), (24, 1), (46, 1), (53, 1), (64, 1), (66, 1)] }, { coefficient := -1, powers := [(0, 2), (29, 1), (39, 1), (60, 1), (64, 1), (66, 1)] }, { coefficient := -1, powers := [(0, 2), (29, 1), (42, 1), (53, 1), (64, 1), (66, 1)] }, { coefficient := -1, powers := [(0, 2), (30, 1), (38, 1), (46, 1), (60, 1), (64, 1), (66, 1)] }, { coefficient := 2, powers := [(0, 2), (30, 1), (42, 1), (64, 1), (66, 1)] }, { coefficient := -1, powers := [(0, 2), (30, 1), (46, 1), (64, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(0, 2), (42, 1), (62, 1), (66, 1)] }, { coefficient := 1, powers := [(0, 2), (46, 1), (62, 1), (66, 1)] }, { coefficient := 1, powers := [(0, 2), (53, 1), (62, 1), (66, 1)] }, { coefficient := -1, powers := [(0, 1), (42, 1), (66, 1)] }, { coefficient := 1, powers := [(66, 1)] }],
  [{ coefficient := -1, powers := [(0, 2), (42, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(0, 2), (38, 1), (46, 1), (60, 1), (64, 1)] }, { coefficient := -1, powers := [(0, 2), (42, 1), (64, 1)] }, { coefficient := 1, powers := [(0, 2), (46, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(0, 2), (29, 1), (42, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(0, 2), (18, 1), (38, 1), (60, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(0, 2), (39, 1), (60, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(0, 2), (62, 1)] }],
  [{ coefficient := -1, powers := [(0, 2), (38, 1), (60, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(0, 2), (39, 1), (60, 1)] }, { coefficient := -1, powers := [(0, 2), (42, 2)] }, { coefficient := -1, powers := [(0, 2), (42, 1), (46, 1)] }, { coefficient := -1, powers := [(0, 2), (42, 1), (53, 1)] }, { coefficient := 1, powers := [(0, 2), (46, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(0, 2), (39, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 2), (42, 1), (46, 1)] }, { coefficient := 1, powers := [(0, 2), (42, 1), (53, 1)] }, { coefficient := -1, powers := [(0, 2), (46, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(0, 3), (42, 1), (62, 1)] }, { coefficient := 1, powers := [(0, 2), (2, 1), (38, 1), (42, 1), (60, 1), (64, 1)] }, { coefficient := -1, powers := [(0, 2), (18, 1), (24, 1), (38, 1), (46, 1), (60, 1), (64, 1)] }, { coefficient := 1, powers := [(0, 2), (18, 1), (24, 1), (42, 1), (64, 1)] }, { coefficient := -1, powers := [(0, 2), (18, 1), (24, 1), (46, 1), (64, 1)] }, { coefficient := -1, powers := [(0, 2), (18, 1), (29, 1), (42, 1), (64, 1)] }, { coefficient := 1, powers := [(0, 2), (62, 1)] }],
  [{ coefficient := -1, powers := [(0, 3), (42, 2), (62, 1)] }, { coefficient := -1, powers := [(0, 3), (42, 1), (46, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 3), (42, 1), (53, 1), (62, 1)] }, { coefficient := 1, powers := [(0, 2), (18, 1), (24, 1), (38, 1), (46, 1), (53, 1), (60, 1), (64, 1)] }, { coefficient := 1, powers := [(0, 2), (18, 1), (24, 1), (39, 1), (60, 1), (64, 1)] }, { coefficient := -1, powers := [(0, 2), (18, 1), (24, 1), (42, 1), (53, 1), (64, 1)] }, { coefficient := 1, powers := [(0, 2), (18, 1), (24, 1), (46, 1), (53, 1), (64, 1)] }, { coefficient := 1, powers := [(0, 2), (18, 1), (29, 1), (39, 1), (60, 1), (64, 1)] }, { coefficient := 1, powers := [(0, 2), (18, 1), (29, 1), (42, 1), (53, 1), (64, 1)] }, { coefficient := 1, powers := [(0, 2), (18, 1), (30, 1), (38, 1), (46, 1), (60, 1), (64, 1)] }, { coefficient := -2, powers := [(0, 2), (18, 1), (30, 1), (42, 1), (64, 1)] }, { coefficient := 1, powers := [(0, 2), (18, 1), (30, 1), (46, 1), (64, 1)] }, { coefficient := 1, powers := [(0, 2), (42, 2)] }, { coefficient := -1, powers := [(0, 2), (42, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 2), (46, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 2), (53, 1), (62, 1)] }, { coefficient := -1, powers := [] }]
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
    ¬ ∀ index : Fin 13,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component24.SelectedLeafB7_2_1.selectedHasNoCommonZero

end Krenn.Component24.SelectedLeafB7_2_1
