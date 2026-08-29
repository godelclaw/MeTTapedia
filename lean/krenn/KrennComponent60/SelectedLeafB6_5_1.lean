import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component60.SelectedLeafB6_5_1

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "1fce58733ff50ddbe2076781dc197175cd96f788f8f7335df8c01c36037c9f66"
def certificateSHA256 : String := "986bd8cab50429e91f9204b1ddc52764e77f8c5ebd47f2a2bfe1bbdcefc2ddae"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 8 → Fin 665 := ![
  70,
  153,
  211,
  304,
  582,
  659,
  663,
  664
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 8 → SparsePoly (Fin 66) := ![
  [{ coefficient := 1, powers := [(9, 1), (26, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (46, 1)] }, { coefficient := 1, powers := [(30, 1), (37, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (26, 1), (46, 1)] }, { coefficient := 1, powers := [(9, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (45, 1)] }, { coefficient := 1, powers := [(9, 1), (56, 1)] }, { coefficient := 1, powers := [(30, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(3, 1), (30, 1), (56, 1)] }, { coefficient := 1, powers := [(9, 1), (20, 1), (56, 1)] }, { coefficient := 1, powers := [(9, 1)] }, { coefficient := 1, powers := [(39, 1)] }],
  [{ coefficient := 1, powers := [(39, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(56, 1)] }],
  [{ coefficient := 1, powers := [(57, 1), (65, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 8 → SparsePoly (Fin 66) := ![
  [{ coefficient := 1, powers := [(43, 1), (63, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(26, 1), (63, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(63, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(26, 1), (43, 1), (63, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(63, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(0, 1), (39, 1), (63, 1)] }, { coefficient := -1, powers := [(3, 1), (30, 1), (63, 1)] }, { coefficient := -1, powers := [(9, 1), (20, 1), (63, 1)] }, { coefficient := 1, powers := [(9, 1), (26, 1), (43, 1), (63, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (63, 1)] }]
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
    (values : Fin 66 → R) :
    ¬ ∀ index : Fin 8,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component60.SelectedLeafB6_5_1.selectedHasNoCommonZero

end Krenn.Component60.SelectedLeafB6_5_1
