import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component39.SelectedLeafB4_1_0

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "58223406601517f043dbcb1a4f5df30cf463ac0ea40439523d324e72aac7130a"
def certificateSHA256 : String := "e955d98508c5949240ffd042b40b2a014e8d3671533f1567118d81d3f0bf03de"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 9 → Fin 670 := ![
  321,
  411,
  457,
  465,
  580,
  608,
  665,
  666,
  668
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 9 → SparsePoly (Fin 63) := ![
  [{ coefficient := 1, powers := [(0, 1), (44, 1), (49, 1)] }, { coefficient := 1, powers := [(23, 1), (44, 1), (49, 1)] }, { coefficient := 1, powers := [(49, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1)] }, { coefficient := 1, powers := [(6, 1), (19, 1), (59, 1)] }, { coefficient := 1, powers := [(19, 1)] }, { coefficient := 1, powers := [(23, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(44, 1), (49, 1)] }, { coefficient := 1, powers := [(49, 1), (56, 1)] }, { coefficient := 1, powers := [(52, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1), (49, 1)] }, { coefficient := 1, powers := [(19, 1), (49, 1)] }, { coefficient := 1, powers := [(23, 1), (40, 1)] }, { coefficient := 1, powers := [(23, 1), (46, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1)] }, { coefficient := 1, powers := [(6, 1), (59, 1)] }, { coefficient := 1, powers := [(23, 1), (39, 1)] }, { coefficient := 1, powers := [(23, 1), (44, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (40, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(19, 1), (49, 1), (56, 1)] }, { coefficient := 1, powers := [(19, 1), (52, 1)] }, { coefficient := 1, powers := [(40, 1)] }, { coefficient := 1, powers := [(46, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(39, 1)] }],
  [{ coefficient := 1, powers := [(40, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(56, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 9 → SparsePoly (Fin 63) := ![
  [{ coefficient := -1, powers := [(46, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(52, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(19, 1), (62, 1)] }, { coefficient := 1, powers := [(23, 1), (46, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(44, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (52, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(23, 1), (44, 1), (62, 1)] }, { coefficient := 1, powers := [(62, 1)] }],
  [{ coefficient := -1, powers := [(19, 1), (23, 1), (52, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (23, 1), (40, 1), (44, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 1), (40, 1), (62, 1)] }, { coefficient := 1, powers := [(19, 1), (23, 1), (44, 1), (49, 1), (62, 1)] }, { coefficient := -1, powers := [(23, 1), (46, 1), (49, 1), (62, 1)] }]
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
    ¬ ∀ index : Fin 9,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component39.SelectedLeafB4_1_0.selectedHasNoCommonZero

end Krenn.Component39.SelectedLeafB4_1_0
