import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component60.SelectedLeafB2_6_3

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "e7562abe6e1223f13b4db6336dc639c1cef39bce372bf29ff36573b2851e08a6"
def certificateSHA256 : String := "6432d1d129d93dd69d9776dbbb40de5b0f61a610a35057add85c104a246a65b1"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 11 → Fin 665 := ![
  70,
  107,
  150,
  305,
  427,
  460,
  608,
  656,
  657,
  659,
  664
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 11 → SparsePoly (Fin 66) := ![
  [{ coefficient := 1, powers := [(9, 1), (26, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (26, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (26, 1)] }, { coefficient := 1, powers := [(26, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (46, 1)] }, { coefficient := 1, powers := [(16, 1), (40, 1)] }, { coefficient := 1, powers := [(16, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (46, 1)] }, { coefficient := 1, powers := [(10, 1), (27, 1), (46, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1), (53, 1)] }, { coefficient := 1, powers := [(26, 1), (40, 1)] }, { coefficient := 1, powers := [(26, 1), (45, 1)] }, { coefficient := 1, powers := [(53, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (46, 1), (53, 1)] }, { coefficient := 1, powers := [(26, 1), (40, 1), (43, 1)] }, { coefficient := 1, powers := [(26, 1), (46, 1)] }, { coefficient := 1, powers := [(43, 1), (53, 1)] }, { coefficient := 1, powers := [(57, 1)] }],
  [{ coefficient := 1, powers := [(0, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (61, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(39, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(57, 1), (65, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 11 → SparsePoly (Fin 66) := ![
  [{ coefficient := -1, powers := [(43, 1), (62, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (61, 1), (62, 1), (65, 1)] }, { coefficient := -1, powers := [(27, 1), (51, 1), (61, 1), (62, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(43, 1), (45, 1), (62, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(26, 1), (27, 1), (61, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(26, 1), (61, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(39, 1), (43, 1), (62, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(65, 1)] }],
  [{ coefficient := 1, powers := [(39, 1), (43, 1), (45, 1), (53, 1), (62, 1), (65, 1)] }, { coefficient := -1, powers := [(40, 1), (57, 1), (65, 1)] }, { coefficient := -1, powers := [(46, 1), (53, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(26, 1), (46, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(16, 1), (23, 1), (26, 1), (61, 1), (65, 1)] }, { coefficient := 1, powers := [(16, 1), (26, 1), (27, 1), (51, 1), (61, 1), (65, 1)] }, { coefficient := 1, powers := [(26, 1), (40, 1), (43, 1), (65, 1)] }, { coefficient := 1, powers := [(43, 1), (53, 1), (65, 1)] }],
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
    (values : Fin 66 → R) :
    ¬ ∀ index : Fin 11,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component60.SelectedLeafB2_6_3.selectedHasNoCommonZero

end Krenn.Component60.SelectedLeafB2_6_3
