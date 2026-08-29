import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component18.SelectedLeafB0_6_3_3

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "6d181009655f0171b3318ee548625d755f4ef6d8dc7a58bfabe16530d6e25c3b"
def certificateSHA256 : String := "ed6401951fad3dcdbfb07095becbdb63e08a2ee08b15522c0b1919111014b5b5"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 8 → Fin 670 := ![
  294,
  323,
  460,
  463,
  609,
  658,
  666,
  667
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 8 → SparsePoly (Fin 67) := ![
  [{ coefficient := 1, powers := [(0, 1), (45, 1)] }, { coefficient := 1, powers := [(19, 1), (45, 1)] }, { coefficient := 1, powers := [(25, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1), (52, 1)] }, { coefficient := 1, powers := [(19, 1), (45, 1), (52, 1)] }, { coefficient := 1, powers := [(45, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1), (53, 1)] }, { coefficient := 1, powers := [(26, 1), (42, 1)] }, { coefficient := 1, powers := [(26, 1), (46, 1)] }, { coefficient := 1, powers := [(53, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1), (52, 1)] }, { coefficient := 1, powers := [(42, 1), (45, 1)] }, { coefficient := 1, powers := [(45, 1), (52, 1)] }, { coefficient := 1, powers := [(47, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (47, 1), (53, 1)] }, { coefficient := 1, powers := [(26, 1), (42, 1), (45, 1)] }, { coefficient := 1, powers := [(26, 1), (47, 1)] }, { coefficient := 1, powers := [(45, 1), (53, 1)] }, { coefficient := 1, powers := [(57, 1)] }],
  [{ coefficient := 1, powers := [(0, 1)] }],
  [{ coefficient := 1, powers := [(57, 1), (64, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(25, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 8 → SparsePoly (Fin 67) := ![
  [{ coefficient := -1, powers := [(26, 1), (42, 1), (52, 1), (64, 1)] }, { coefficient := -1, powers := [(26, 1), (46, 1), (52, 1), (64, 1)] }, { coefficient := -1, powers := [(26, 1), (52, 2), (64, 1)] }],
  [{ coefficient := 1, powers := [(26, 1), (42, 1), (64, 1)] }, { coefficient := 1, powers := [(26, 1), (46, 1), (64, 1)] }, { coefficient := 1, powers := [(26, 1), (52, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(45, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(26, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(64, 1)] }],
  [{ coefficient := 1, powers := [(26, 1), (47, 1), (52, 1), (64, 1)] }, { coefficient := -1, powers := [(42, 1), (57, 1), (64, 1)] }, { coefficient := 1, powers := [(45, 1), (46, 1), (53, 1), (64, 1)] }, { coefficient := -1, powers := [(47, 1), (53, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(26, 1), (42, 1), (45, 1), (52, 1), (64, 1)] }, { coefficient := 1, powers := [(26, 1), (45, 1), (46, 1), (52, 1), (64, 1)] }, { coefficient := 1, powers := [(26, 1), (45, 1), (52, 2), (64, 1)] }]
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
    ¬ ∀ index : Fin 8,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component18.SelectedLeafB0_6_3_3.selectedHasNoCommonZero

end Krenn.Component18.SelectedLeafB0_6_3_3
