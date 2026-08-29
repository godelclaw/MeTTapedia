import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component16.SelectedLeafB1_6_0

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "99405de37ffe9e41bfd621a9f74fe5a2640691540173d678aaae12e6c43a36d1"
def certificateSHA256 : String := "587ffaf8d0316e0b1a370f6a79028461c31b5750cf293679ded3d6fe11607a16"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 15 → Fin 671 := ![
  166,
  407,
  433,
  438,
  454,
  455,
  501,
  527,
  584,
  585,
  649,
  662,
  664,
  666,
  669
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 15 → SparsePoly (Fin 65) := ![
  [{ coefficient := 1, powers := [(19, 1), (21, 1)] }, { coefficient := 1, powers := [(19, 1), (26, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (26, 1), (42, 1)] }, { coefficient := 1, powers := [(19, 1), (26, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (29, 1), (42, 1)] }, { coefficient := 1, powers := [(19, 1), (29, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (30, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (53, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (53, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (57, 1)] }, { coefficient := 1, powers := [(19, 1), (30, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (42, 1)] }, { coefficient := 1, powers := [(19, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (53, 1)] }, { coefficient := 1, powers := [(19, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(30, 1), (42, 1)] }, { coefficient := 1, powers := [(30, 1), (47, 1)] }, { coefficient := 1, powers := [(30, 1), (53, 1)] }, { coefficient := 1, powers := [(30, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (30, 1), (60, 1)] }, { coefficient := 1, powers := [(24, 1), (53, 1)] }, { coefficient := 1, powers := [(24, 1), (57, 1)] }, { coefficient := 1, powers := [(30, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (30, 1), (60, 1)] }, { coefficient := 1, powers := [(29, 1), (42, 1)] }, { coefficient := 1, powers := [(29, 1), (47, 1)] }, { coefficient := 1, powers := [(30, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1)] }, { coefficient := 1, powers := [(6, 1), (60, 1)] }, { coefficient := 1, powers := [(26, 1), (42, 1)] }, { coefficient := 1, powers := [(26, 1), (47, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (53, 1)] }, { coefficient := 1, powers := [(3, 1), (60, 1)] }, { coefficient := 1, powers := [(21, 1), (53, 1)] }, { coefficient := 1, powers := [(21, 1), (57, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (39, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (42, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (47, 1), (53, 1)] }, { coefficient := 1, powers := [(42, 1)] }, { coefficient := 1, powers := [(47, 1)] }, { coefficient := 1, powers := [(53, 1)] }, { coefficient := 1, powers := [(57, 1)] }],
  [{ coefficient := 1, powers := [(0, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(42, 1), (64, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(57, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 15 → SparsePoly (Fin 65) := ![
  [{ coefficient := 1, powers := [(30, 1), (53, 1), (62, 1), (64, 1)] }],
  [{ coefficient := 2, powers := [(30, 1), (62, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(62, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(62, 1), (64, 1)] }],
  [{ coefficient := -2, powers := [(26, 1), (30, 1), (62, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (26, 1), (62, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (62, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (62, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(19, 1), (30, 1), (62, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(19, 1), (30, 1), (62, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (62, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (39, 1), (60, 1), (62, 1), (64, 1)] }, { coefficient := -1, powers := [(2, 1), (42, 1), (57, 1), (62, 1), (64, 1)] }, { coefficient := -1, powers := [(2, 1), (47, 1), (53, 1), (62, 1), (64, 1)] }, { coefficient := 1, powers := [(19, 1), (30, 1), (47, 1), (62, 1), (64, 1)] }, { coefficient := 1, powers := [(19, 1), (30, 1), (53, 1), (62, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(2, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (62, 1), (64, 1)] }, { coefficient := 1, powers := [(19, 1), (21, 1), (30, 1), (62, 1), (64, 1)] }, { coefficient := 1, powers := [(19, 1), (26, 1), (30, 1), (62, 1), (64, 1)] }]
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
    (values : Fin 65 → R) :
    ¬ ∀ index : Fin 15,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component16.SelectedLeafB1_6_0.selectedHasNoCommonZero

end Krenn.Component16.SelectedLeafB1_6_0
