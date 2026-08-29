import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component16.SelectedLeafB5_6_5_3

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "34be9da3df22a48690cfb45788450e1c0b2494c3d09ebbc30e1f6330bdc498e8"
def certificateSHA256 : String := "6b5dde5a223a026a0d052e90b5ea51f6cc68b5262aba6c4cd1c82fa9a49dc28e"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 23 → Fin 674 := ![
  18,
  26,
  27,
  260,
  298,
  312,
  317,
  428,
  430,
  433,
  454,
  462,
  468,
  501,
  612,
  662,
  664,
  668,
  669,
  670,
  671,
  672,
  673
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 23 → SparsePoly (Fin 70) := ![
  [{ coefficient := 1, powers := [(19, 1), (28, 1)] }],
  [{ coefficient := 1, powers := [(28, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(28, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (24, 1), (53, 1)] }, { coefficient := 1, powers := [(30, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1)] }, { coefficient := 1, powers := [(21, 1), (45, 1)] }, { coefficient := 1, powers := [(26, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (24, 1)] }, { coefficient := 1, powers := [(24, 1), (56, 1)] }, { coefficient := 1, powers := [(29, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(30, 1), (54, 1)] }, { coefficient := 1, powers := [(31, 1), (42, 1)] }, { coefficient := 1, powers := [(31, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (48, 1)] }, { coefficient := 1, powers := [(26, 1), (42, 1), (45, 1)] }, { coefficient := 1, powers := [(26, 1), (48, 1)] }, { coefficient := 1, powers := [(45, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (54, 1)] }, { coefficient := 1, powers := [(3, 1), (27, 1), (60, 1)] }, { coefficient := 1, powers := [(21, 1), (54, 1)] }, { coefficient := 1, powers := [(27, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (29, 1), (42, 1)] }, { coefficient := 1, powers := [(19, 1), (29, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (30, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (42, 1)] }, { coefficient := 1, powers := [(19, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (53, 1)] }, { coefficient := 1, powers := [(19, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1), (54, 1)] }, { coefficient := 1, powers := [(21, 1), (45, 1), (54, 1)] }, { coefficient := 1, powers := [(21, 1), (58, 1)] }, { coefficient := 1, powers := [(27, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (48, 1), (53, 1)] }, { coefficient := 1, powers := [(42, 1), (45, 1)] }, { coefficient := 1, powers := [(45, 1), (53, 1)] }, { coefficient := 1, powers := [(48, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (30, 1), (60, 1)] }, { coefficient := 1, powers := [(24, 1), (53, 1)] }, { coefficient := 1, powers := [(24, 1), (57, 1)] }, { coefficient := 1, powers := [(30, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1), (58, 1)] }, { coefficient := 1, powers := [(0, 1), (48, 1), (54, 1)] }, { coefficient := 1, powers := [(27, 1), (42, 1), (45, 1)] }, { coefficient := 1, powers := [(27, 1), (48, 1)] }, { coefficient := 1, powers := [(45, 1), (54, 1)] }, { coefficient := 1, powers := [(58, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(56, 1), (66, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(57, 1)] }],
  [{ coefficient := 1, powers := [(58, 1), (67, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(26, 1)] }],
  [{ coefficient := 1, powers := [(28, 1), (68, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(31, 1), (69, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 23 → SparsePoly (Fin 70) := ![
  [{ coefficient := 1, powers := [(0, 1), (29, 1), (53, 1), (63, 1), (68, 1)] }, { coefficient := -1, powers := [(0, 1), (30, 1), (63, 1), (68, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (27, 1), (29, 1), (53, 1), (62, 1), (66, 1), (68, 1), (69, 1)] }, { coefficient := 1, powers := [(0, 1), (27, 1), (30, 1), (62, 1), (66, 1), (68, 1), (69, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (27, 1), (30, 1), (54, 1), (62, 1), (67, 1), (68, 1), (69, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (27, 1), (62, 1), (66, 1), (69, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (30, 1), (54, 2), (62, 1), (67, 1), (69, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (27, 1), (53, 1), (62, 1), (66, 1), (69, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (69, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (53, 1), (67, 1)] }, { coefficient := -1, powers := [(54, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (30, 1), (62, 1), (69, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (29, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (30, 1), (54, 1), (62, 1), (67, 1), (69, 1)] }],
  [{ coefficient := -1, powers := [(27, 1), (67, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (27, 1), (62, 1), (69, 1)] }],
  [{ coefficient := 1, powers := [(67, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (30, 1), (54, 1), (69, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (47, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (24, 1), (27, 1), (53, 1), (62, 1), (69, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (19, 1), (29, 1), (63, 1)] }, { coefficient := 1, powers := [(0, 1), (24, 1), (27, 1), (62, 1), (69, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (21, 1), (30, 1), (54, 1), (62, 1), (69, 1)] }, { coefficient := -1, powers := [(0, 1), (42, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(0, 1), (30, 1), (45, 1), (54, 2), (62, 1), (67, 1), (69, 1)] }, { coefficient := -1, powers := [(27, 1), (42, 1), (45, 1), (53, 1), (67, 1)] }, { coefficient := -1, powers := [(27, 1), (48, 1), (53, 1), (67, 1)] }, { coefficient := 1, powers := [(42, 1), (45, 1), (54, 1), (67, 1)] }, { coefficient := 1, powers := [(48, 1), (54, 1), (67, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (19, 1), (29, 1), (53, 1), (63, 1)] }, { coefficient := 1, powers := [(0, 1), (19, 1), (30, 1), (63, 1)] }, { coefficient := 1, powers := [(0, 1), (27, 1), (29, 1), (44, 1), (53, 1), (62, 1), (66, 1), (69, 1)] }, { coefficient := -1, powers := [(0, 1), (27, 1), (30, 1), (44, 1), (62, 1), (66, 1), (69, 1)] }, { coefficient := -1, powers := [(0, 1), (27, 1), (30, 1), (45, 1), (54, 1), (62, 1), (67, 1), (69, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1)] }, { coefficient := 1, powers := [(0, 1), (47, 1)] }]
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
    (values : Fin 70 → R) :
    ¬ ∀ index : Fin 23,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component16.SelectedLeafB5_6_5_3.selectedHasNoCommonZero

end Krenn.Component16.SelectedLeafB5_6_5_3
