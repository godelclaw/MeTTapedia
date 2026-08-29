import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component16.SelectedLeafB5_2_3_0

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "803bcc3d91b231ad2e316c2d0a00617cde1a8b39727b156f2b4ae96e28506226"
def certificateSHA256 : String := "107ab7f6e66e40a8e4fd0e8be79f09778dbc5e21d2da485743f735ac1f67f060"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 18 → Fin 674 := ![
  21,
  49,
  273,
  300,
  407,
  433,
  441,
  506,
  523,
  584,
  593,
  609,
  660,
  663,
  664,
  670,
  671,
  672
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 18 → SparsePoly (Fin 67) := ![
  [{ coefficient := 1, powers := [(23, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (33, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (45, 1), (54, 1)] }, { coefficient := 1, powers := [(23, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (47, 1)] }, { coefficient := 1, powers := [(4, 1), (36, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (26, 1), (42, 1)] }, { coefficient := 1, powers := [(19, 1), (26, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (29, 1), (42, 1)] }, { coefficient := 1, powers := [(19, 1), (29, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (30, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (36, 1)] }, { coefficient := 1, powers := [(6, 1), (33, 1)] }, { coefficient := 1, powers := [(33, 1), (38, 1)] }, { coefficient := 1, powers := [(36, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (26, 1), (60, 1)] }, { coefficient := 1, powers := [(11, 1), (26, 1), (47, 1)] }, { coefficient := 1, powers := [(16, 1), (26, 1), (42, 1)] }, { coefficient := 1, powers := [(16, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (23, 1), (60, 1)] }, { coefficient := 1, powers := [(6, 1), (33, 1), (47, 1)] }, { coefficient := 1, powers := [(6, 1), (36, 1), (42, 1)] }, { coefficient := 1, powers := [(23, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1)] }, { coefficient := 1, powers := [(6, 1), (60, 1)] }, { coefficient := 1, powers := [(26, 1), (42, 1)] }, { coefficient := 1, powers := [(26, 1), (47, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1), (42, 1), (58, 1)] }, { coefficient := 1, powers := [(1, 1), (48, 1), (54, 1)] }, { coefficient := 1, powers := [(4, 1), (33, 1), (58, 1)] }, { coefficient := 1, powers := [(11, 1), (23, 1), (58, 1)] }, { coefficient := 1, powers := [(17, 1), (23, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (53, 1)] }, { coefficient := 1, powers := [(23, 1), (57, 1)] }, { coefficient := 1, powers := [(28, 1), (42, 1)] }, { coefficient := 1, powers := [(28, 1), (47, 1)] }, { coefficient := 1, powers := [(33, 1), (39, 1)] }, { coefficient := 1, powers := [(36, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (39, 1), (60, 1)] }, { coefficient := 1, powers := [(1, 1), (42, 1), (57, 1)] }, { coefficient := 1, powers := [(1, 1), (47, 1), (53, 1)] }, { coefficient := 1, powers := [(4, 1), (28, 1), (60, 1)] }, { coefficient := 1, powers := [(4, 1), (33, 1), (57, 1)] }, { coefficient := 1, powers := [(4, 1), (36, 1), (53, 1)] }, { coefficient := 1, powers := [(7, 1), (23, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (33, 1), (47, 1)] }, { coefficient := 1, powers := [(7, 1), (36, 1), (42, 1)] }, { coefficient := 1, powers := [(11, 1), (23, 1), (57, 1)] }, { coefficient := 1, powers := [(11, 1), (28, 1), (47, 1)] }, { coefficient := 1, powers := [(11, 1), (36, 1), (39, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1), (53, 1)] }, { coefficient := 1, powers := [(16, 1), (28, 1), (42, 1)] }, { coefficient := 1, powers := [(16, 1), (33, 1), (39, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(58, 1), (66, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(26, 1)] }],
  [{ coefficient := 1, powers := [(28, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 18 → SparsePoly (Fin 67) := ![
  [{ coefficient := 1, powers := [(0, 1), (7, 1), (45, 1), (47, 1), (60, 1), (66, 1)] }, { coefficient := -1, powers := [(3, 1), (11, 1), (45, 1), (53, 1), (60, 1), (66, 1)] }, { coefficient := -1, powers := [(3, 1), (11, 1), (45, 1), (57, 1), (60, 1), (66, 1)] }, { coefficient := 1, powers := [(6, 1), (7, 1), (45, 1), (60, 2), (66, 1)] }, { coefficient := -1, powers := [(6, 1), (11, 1), (45, 1), (53, 1), (60, 1), (66, 1)] }, { coefficient := -1, powers := [(6, 1), (11, 1), (45, 1), (57, 1), (60, 1), (66, 1)] }, { coefficient := 1, powers := [(6, 1), (17, 1), (57, 1), (60, 1), (66, 1)] }, { coefficient := -1, powers := [(11, 1), (38, 1), (45, 1), (53, 1), (60, 1), (66, 1)] }, { coefficient := -1, powers := [(11, 1), (38, 1), (45, 1), (57, 1), (60, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (39, 1), (60, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (7, 1), (47, 1), (60, 1), (66, 1)] }, { coefficient := 1, powers := [(3, 1), (11, 1), (53, 1), (60, 1), (66, 1)] }, { coefficient := 1, powers := [(3, 1), (11, 1), (57, 1), (60, 1), (66, 1)] }, { coefficient := -1, powers := [(6, 1), (7, 1), (60, 2), (66, 1)] }, { coefficient := 1, powers := [(6, 1), (11, 1), (53, 1), (60, 1), (66, 1)] }, { coefficient := 1, powers := [(6, 1), (11, 1), (57, 1), (60, 1), (66, 1)] }, { coefficient := 1, powers := [(11, 1), (38, 1), (53, 1), (60, 1), (66, 1)] }, { coefficient := 1, powers := [(11, 1), (38, 1), (57, 1), (60, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (53, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (29, 1), (42, 1), (63, 1)] }, { coefficient := 1, powers := [(0, 1), (29, 1), (47, 1), (63, 1)] }, { coefficient := 1, powers := [(0, 1), (30, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (39, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (33, 1), (39, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (23, 1), (60, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := -1, powers := [(6, 1), (57, 1), (60, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (11, 1), (60, 1)] }, { coefficient := -1, powers := [(6, 1), (11, 1), (60, 1)] }, { coefficient := -1, powers := [(11, 1), (38, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (39, 1), (60, 2)] }, { coefficient := 1, powers := [(6, 1), (42, 1), (57, 1), (58, 1), (60, 1), (66, 1)] }, { coefficient := -1, powers := [(6, 1), (42, 1), (57, 1), (60, 1)] }, { coefficient := 1, powers := [(6, 1), (48, 1), (54, 1), (57, 1), (60, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (7, 1), (23, 1), (47, 1), (60, 1)] }, { coefficient := -1, powers := [(3, 1), (11, 1), (23, 1), (53, 1), (60, 1)] }, { coefficient := -1, powers := [(3, 1), (11, 1), (23, 1), (57, 1), (60, 1)] }, { coefficient := -1, powers := [(3, 1), (11, 1), (33, 1), (39, 1), (60, 1)] }, { coefficient := 1, powers := [(4, 1), (6, 1), (33, 1), (57, 1), (60, 1)] }, { coefficient := 1, powers := [(6, 1), (7, 1), (23, 1), (60, 2)] }, { coefficient := -1, powers := [(6, 1), (11, 1), (23, 1), (53, 1), (60, 1)] }, { coefficient := -1, powers := [(11, 1), (23, 1), (38, 1), (53, 1), (60, 1)] }, { coefficient := -1, powers := [(11, 1), (23, 1), (38, 1), (57, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (19, 1), (29, 1), (42, 2), (63, 1)] }, { coefficient := -2, powers := [(0, 1), (19, 1), (29, 1), (42, 1), (47, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (19, 1), (29, 1), (47, 2), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (19, 1), (30, 1), (42, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (19, 1), (30, 1), (47, 1), (63, 1)] }, { coefficient := 1, powers := [(4, 1), (6, 1), (33, 1), (39, 1), (60, 2)] }, { coefficient := 1, powers := [(6, 1), (11, 1), (33, 1), (39, 1), (47, 1), (60, 1)] }, { coefficient := 1, powers := [(6, 1), (16, 1), (33, 1), (39, 1), (42, 1), (60, 1)] }, { coefficient := -1, powers := [(7, 1), (23, 1), (42, 1), (60, 1)] }, { coefficient := -1, powers := [(7, 1), (23, 1), (47, 1), (60, 1)] }, { coefficient := -1, powers := [(42, 1)] }, { coefficient := -1, powers := [(47, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (11, 1), (42, 1), (60, 1)] }, { coefficient := 1, powers := [(3, 1), (11, 1), (47, 1), (60, 1)] }, { coefficient := -1, powers := [(4, 1), (6, 1), (60, 2)] }, { coefficient := 1, powers := [(6, 1), (11, 1), (42, 1), (60, 1)] }, { coefficient := -1, powers := [(6, 1), (16, 1), (42, 1), (60, 1)] }, { coefficient := 1, powers := [(11, 1), (38, 1), (42, 1), (60, 1)] }, { coefficient := 1, powers := [(11, 1), (38, 1), (47, 1), (60, 1)] }]
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
    ¬ ∀ index : Fin 18,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component16.SelectedLeafB5_2_3_0.selectedHasNoCommonZero

end Krenn.Component16.SelectedLeafB5_2_3_0
