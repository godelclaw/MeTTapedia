import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component16.SelectedLeafB1_6_3

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "ef01d9fbb79578d347a6177cf1d8f36b62ae8fb0d1150d0a2a902aeb1bb7d555"
def certificateSHA256 : String := "6decf3defcce17f85fe074e63f8959f9514b59861340823c9b16030d2e70a250"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 15 → Fin 671 := ![
  166,
  321,
  404,
  438,
  454,
  462,
  468,
  498,
  527,
  584,
  585,
  612,
  662,
  664,
  670
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 15 → SparsePoly (Fin 67) := ![
  [{ coefficient := 1, powers := [(19, 1), (21, 1)] }, { coefficient := 1, powers := [(19, 1), (26, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1), (53, 1)] }, { coefficient := 1, powers := [(21, 1), (45, 1), (53, 1)] }, { coefficient := 1, powers := [(45, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (21, 1), (53, 1)] }, { coefficient := 1, powers := [(19, 1), (21, 1), (57, 1)] }, { coefficient := 1, powers := [(19, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (53, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (53, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (57, 1)] }, { coefficient := 1, powers := [(19, 1), (30, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (42, 1)] }, { coefficient := 1, powers := [(19, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (53, 1)] }, { coefficient := 1, powers := [(19, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1), (54, 1)] }, { coefficient := 1, powers := [(21, 1), (45, 1), (54, 1)] }, { coefficient := 1, powers := [(21, 1), (58, 1)] }, { coefficient := 1, powers := [(27, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (48, 1), (53, 1)] }, { coefficient := 1, powers := [(42, 1), (45, 1)] }, { coefficient := 1, powers := [(45, 1), (53, 1)] }, { coefficient := 1, powers := [(48, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (29, 1), (60, 1)] }, { coefficient := 1, powers := [(6, 1), (24, 1), (60, 1)] }, { coefficient := 1, powers := [(24, 1)] }, { coefficient := 1, powers := [(29, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (30, 1), (60, 1)] }, { coefficient := 1, powers := [(29, 1), (42, 1)] }, { coefficient := 1, powers := [(29, 1), (47, 1)] }, { coefficient := 1, powers := [(30, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1)] }, { coefficient := 1, powers := [(6, 1), (60, 1)] }, { coefficient := 1, powers := [(26, 1), (42, 1)] }, { coefficient := 1, powers := [(26, 1), (47, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (53, 1)] }, { coefficient := 1, powers := [(3, 1), (60, 1)] }, { coefficient := 1, powers := [(21, 1), (53, 1)] }, { coefficient := 1, powers := [(21, 1), (57, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1), (58, 1)] }, { coefficient := 1, powers := [(0, 1), (48, 1), (54, 1)] }, { coefficient := 1, powers := [(27, 1), (42, 1), (45, 1)] }, { coefficient := 1, powers := [(27, 1), (48, 1)] }, { coefficient := 1, powers := [(45, 1), (54, 1)] }, { coefficient := 1, powers := [(58, 1)] }],
  [{ coefficient := 1, powers := [(0, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(58, 1), (66, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 15 → SparsePoly (Fin 67) := ![
  [{ coefficient := 1, powers := [(21, 1), (30, 1), (42, 1), (62, 1)] }, { coefficient := 1, powers := [(21, 1), (30, 1), (47, 1), (62, 1)] }, { coefficient := -1, powers := [(24, 1), (42, 1), (62, 1)] }, { coefficient := -1, powers := [(24, 1), (47, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(54, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (30, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(21, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(21, 2), (30, 1), (62, 1)] }, { coefficient := 1, powers := [(21, 1), (24, 1), (62, 1)] }, { coefficient := -1, powers := [(21, 1), (29, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(53, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(27, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(19, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (21, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(19, 1), (21, 1), (30, 1), (62, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (62, 1)] }, { coefficient := 1, powers := [(19, 1), (29, 1), (62, 1)] }, { coefficient := -1, powers := [(58, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(66, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (53, 1), (62, 1)] }, { coefficient := 1, powers := [(19, 1), (21, 1), (30, 1), (47, 1), (62, 1)] }, { coefficient := -1, powers := [(19, 1), (24, 1), (47, 1), (62, 1)] }, { coefficient := -1, powers := [(19, 1), (29, 1), (53, 1), (62, 1)] }, { coefficient := 1, powers := [(27, 1), (48, 1), (53, 1), (66, 1)] }, { coefficient := -1, powers := [(42, 1), (58, 1), (66, 1)] }, { coefficient := -1, powers := [(48, 1), (54, 1), (66, 1)] }, { coefficient := 1, powers := [(53, 1), (58, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (60, 1)] }, { coefficient := -1, powers := [(21, 1), (57, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(3, 1), (60, 1)] }, { coefficient := 1, powers := [(21, 1), (57, 1)] }]
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
    ¬ ∀ index : Fin 15,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component16.SelectedLeafB1_6_3.selectedHasNoCommonZero

end Krenn.Component16.SelectedLeafB1_6_3
