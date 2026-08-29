import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component18.SelectedLeafB7_2_1_6

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "abf735eed1cc74d78db28424fee50cbec0e15b3520c02d285aa46cb1d5dbfdb0"
def certificateSHA256 : String := "5a2166672dfb8f83cd034bb67b578f34dba1cd940420a2bd9d99b38cccf90e6f"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 24 → Fin 670 := ![
  162,
  323,
  345,
  403,
  426,
  430,
  435,
  449,
  458,
  478,
  482,
  564,
  580,
  581,
  608,
  645,
  649,
  658,
  660,
  662,
  665,
  666,
  667,
  669
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 24 → SparsePoly (Fin 68) := ![
  [{ coefficient := 1, powers := [(17, 1), (19, 1)] }, { coefficient := 1, powers := [(17, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1), (52, 1)] }, { coefficient := 1, powers := [(19, 1), (45, 1), (52, 1)] }, { coefficient := 1, powers := [(45, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (45, 1), (52, 1)] }, { coefficient := 1, powers := [(17, 1), (30, 1), (45, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (19, 1), (52, 1)] }, { coefficient := 1, powers := [(17, 1), (19, 1), (56, 1)] }, { coefficient := 1, powers := [(17, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (53, 1)] }, { coefficient := 1, powers := [(3, 1), (26, 1), (59, 1)] }, { coefficient := 1, powers := [(19, 1), (53, 1)] }, { coefficient := 1, powers := [(26, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (46, 1)] }, { coefficient := 1, powers := [(17, 1), (29, 1), (42, 1)] }, { coefficient := 1, powers := [(17, 1), (29, 1), (46, 1)] }, { coefficient := 1, powers := [(17, 1), (30, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (52, 1)] }, { coefficient := 1, powers := [(17, 1), (23, 1), (52, 1)] }, { coefficient := 1, powers := [(17, 1), (23, 1), (56, 1)] }, { coefficient := 1, powers := [(17, 1), (30, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (42, 1)] }, { coefficient := 1, powers := [(17, 1), (46, 1)] }, { coefficient := 1, powers := [(17, 1), (52, 1)] }, { coefficient := 1, powers := [(17, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1), (53, 1)] }, { coefficient := 1, powers := [(19, 1), (45, 1), (53, 1)] }, { coefficient := 1, powers := [(19, 1), (57, 1)] }, { coefficient := 1, powers := [(26, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1)] }, { coefficient := 1, powers := [(17, 1), (23, 1)] }, { coefficient := 1, powers := [(17, 1), (29, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (45, 1), (53, 1)] }, { coefficient := 1, powers := [(17, 1), (23, 1), (57, 1)] }, { coefficient := 1, powers := [(17, 1), (31, 1), (45, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(30, 1), (45, 1), (53, 1)] }, { coefficient := 1, powers := [(30, 1), (57, 1)] }, { coefficient := 1, powers := [(31, 1), (42, 1), (45, 1)] }, { coefficient := 1, powers := [(31, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1)] }, { coefficient := 1, powers := [(6, 1), (59, 1)] }, { coefficient := 1, powers := [(25, 1), (42, 1)] }, { coefficient := 1, powers := [(25, 1), (46, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (52, 1)] }, { coefficient := 1, powers := [(3, 1), (59, 1)] }, { coefficient := 1, powers := [(19, 1), (52, 1)] }, { coefficient := 1, powers := [(19, 1), (56, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (38, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1)] }, { coefficient := 1, powers := [(3, 1), (25, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (19, 1), (59, 1)] }, { coefficient := 1, powers := [(19, 1)] }, { coefficient := 1, powers := [(25, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (39, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (42, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(42, 1)] }, { coefficient := 1, powers := [(46, 1)] }, { coefficient := 1, powers := [(52, 1)] }, { coefficient := 1, powers := [(56, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (39, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (42, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(17, 1), (30, 1), (42, 1)] }, { coefficient := 1, powers := [(17, 1), (30, 1), (46, 1)] }, { coefficient := 1, powers := [(17, 1), (30, 1), (52, 1)] }, { coefficient := 1, powers := [(17, 1), (30, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (61, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(42, 1), (64, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(56, 1)] }],
  [{ coefficient := 1, powers := [(57, 1), (65, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(25, 1), (66, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(31, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 24 → SparsePoly (Fin 68) := ![
  [{ coefficient := -1, powers := [(23, 1), (52, 1), (63, 1), (64, 1), (66, 1)] }, { coefficient := -1, powers := [(29, 1), (52, 1), (63, 1), (64, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(26, 1), (46, 1), (64, 1), (65, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(53, 1), (63, 1), (64, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (63, 1), (64, 1), (66, 1)] }, { coefficient := 1, powers := [(29, 1), (63, 1), (64, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(45, 1), (46, 1), (64, 1), (65, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(25, 1), (63, 1), (64, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (63, 1), (64, 1), (66, 1)] }, { coefficient := -1, powers := [(57, 1), (63, 1), (64, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (30, 1), (63, 1), (64, 1)] }, { coefficient := 1, powers := [(19, 1), (25, 1), (30, 1), (63, 1), (64, 1), (66, 1)] }, { coefficient := 1, powers := [(25, 1), (29, 1), (63, 1), (64, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(46, 1), (64, 1), (65, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(63, 1), (64, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(52, 1), (63, 1), (64, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (63, 1), (64, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(19, 1), (61, 1), (64, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(25, 1), (61, 1), (64, 1), (66, 1)] }, { coefficient := 1, powers := [(26, 1), (45, 1), (46, 1), (64, 1), (65, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(61, 1), (64, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (25, 1), (61, 1), (64, 1), (66, 1)] }, { coefficient := 1, powers := [(64, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (63, 1), (64, 1)] }, { coefficient := -1, powers := [(19, 1), (25, 1), (63, 1), (64, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(19, 1), (25, 1), (39, 1), (59, 1), (64, 1), (66, 1)] }, { coefficient := -1, powers := [(19, 1), (25, 1), (46, 1), (52, 1), (64, 1), (66, 1)] }, { coefficient := 1, powers := [(19, 1), (46, 1), (64, 1), (66, 1)] }, { coefficient := 1, powers := [(25, 1), (52, 1), (64, 1), (66, 1)] }, { coefficient := -1, powers := [(38, 1), (59, 1), (64, 1), (66, 1)] }, { coefficient := -1, powers := [(64, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (39, 1), (59, 1), (64, 1)] }, { coefficient := 1, powers := [(0, 1), (46, 1), (52, 1), (64, 1)] }, { coefficient := 1, powers := [(19, 1), (25, 1), (39, 1), (59, 1), (64, 1), (66, 1)] }, { coefficient := 1, powers := [(19, 1), (25, 1), (46, 1), (52, 1), (64, 1), (66, 1)] }, { coefficient := 1, powers := [(25, 1), (46, 1), (64, 1), (66, 1)] }, { coefficient := -1, powers := [(25, 1), (52, 1), (64, 1), (66, 1)] }, { coefficient := 1, powers := [(38, 1), (59, 1), (64, 1), (66, 1)] }, { coefficient := 1, powers := [(52, 1), (57, 1), (64, 1), (65, 1)] }, { coefficient := 1, powers := [(64, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (2, 1), (42, 1), (63, 1), (64, 1)] }, { coefficient := -1, powers := [(0, 1), (19, 1), (25, 1), (42, 1), (61, 1), (64, 1), (66, 1)] }, { coefficient := -1, powers := [(0, 1), (42, 1), (64, 1)] }, { coefficient := 1, powers := [(2, 1), (19, 1), (25, 1), (42, 1), (63, 1), (64, 1), (66, 1)] }, { coefficient := -1, powers := [(17, 1), (19, 1), (23, 1), (63, 1), (64, 1), (66, 1)] }, { coefficient := -1, powers := [(17, 1), (19, 1), (29, 1), (63, 1), (64, 1), (66, 1)] }, { coefficient := -1, powers := [(17, 1), (23, 1), (25, 1), (63, 1), (64, 1), (66, 1)] }, { coefficient := 1, powers := [(17, 1), (23, 1), (57, 1), (63, 1), (64, 1), (65, 1)] }, { coefficient := -1, powers := [(17, 1), (25, 1), (29, 1), (63, 1), (64, 1), (66, 1)] }, { coefficient := -1, powers := [(19, 1), (26, 1), (45, 1), (46, 1), (64, 1), (65, 1), (66, 1)] }, { coefficient := -1, powers := [(64, 1)] }],
  [{ coefficient := -1, powers := [(19, 1), (46, 1), (64, 1), (66, 1)] }, { coefficient := 1, powers := [(52, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(46, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(17, 1), (42, 1), (45, 1), (63, 1), (64, 1), (65, 1)] }, { coefficient := -1, powers := [(17, 1), (45, 1), (52, 1), (63, 1), (64, 1), (65, 1)] }, { coefficient := -1, powers := [(17, 1), (47, 1), (63, 1), (64, 1), (65, 1)] }]
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
    (values : Fin 68 → R) :
    ¬ ∀ index : Fin 24,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component18.SelectedLeafB7_2_1_6.selectedHasNoCommonZero

end Krenn.Component18.SelectedLeafB7_2_1_6
