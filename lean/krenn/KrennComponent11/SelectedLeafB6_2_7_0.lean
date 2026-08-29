import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component11.SelectedLeafB6_2_7_0

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "8a105b5dfc7fe3ae90a4318605b7ff367a7cf091d406978ea6be3caa5e69e61b"
def certificateSHA256 : String := "4419ded4ef4a90ac9fef845e95b30cbe17fa41a3ce5ba65da54d2cfb4cfb42df"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 20 → Fin 675 := ![
  16,
  183,
  269,
  286,
  328,
  329,
  341,
  342,
  453,
  489,
  557,
  559,
  662,
  665,
  668,
  669,
  670,
  671,
  672,
  674
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 20 → SparsePoly (Fin 67) := ![
  [{ coefficient := 1, powers := [(12, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (53, 1)] }, { coefficient := 1, powers := [(30, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (24, 1), (45, 1)] }, { coefficient := 1, powers := [(12, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (24, 1), (41, 1)] }, { coefficient := 1, powers := [(17, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (49, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1)] }, { coefficient := 1, powers := [(17, 1), (23, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1)] }, { coefficient := 1, powers := [(12, 1), (30, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (54, 1)] }, { coefficient := 1, powers := [(30, 1), (42, 1)] }, { coefficient := 1, powers := [(33, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (53, 1)] }, { coefficient := 1, powers := [(30, 1), (41, 1)] }, { coefficient := 1, powers := [(30, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (60, 1)] }, { coefficient := 1, powers := [(12, 1), (25, 1), (47, 1)] }, { coefficient := 1, powers := [(12, 1), (57, 1)] }, { coefficient := 1, powers := [(17, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (42, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (56, 1)] }, { coefficient := 1, powers := [(12, 1), (23, 1), (56, 1)] }, { coefficient := 1, powers := [(12, 1), (29, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (44, 1), (53, 1)] }, { coefficient := 1, powers := [(23, 1), (57, 1)] }, { coefficient := 1, powers := [(30, 1), (49, 1)] }, { coefficient := 1, powers := [(36, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (44, 1), (53, 1)] }, { coefficient := 1, powers := [(29, 1), (57, 1)] }, { coefficient := 1, powers := [(30, 1), (41, 1), (44, 1)] }, { coefficient := 1, powers := [(30, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (39, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (42, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (49, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (23, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (49, 1)] }, { coefficient := 1, powers := [(8, 1), (36, 1), (42, 1)] }, { coefficient := 1, powers := [(12, 1), (23, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1), (30, 1), (49, 1)] }, { coefficient := 1, powers := [(12, 1), (36, 1), (39, 1)] }, { coefficient := 1, powers := [(17, 1), (23, 1), (54, 1)] }, { coefficient := 1, powers := [(17, 1), (30, 1), (42, 1)] }, { coefficient := 1, powers := [(17, 1), (33, 1), (39, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(42, 1)] }],
  [{ coefficient := 1, powers := [(55, 1), (64, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(56, 1), (65, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(57, 1), (66, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(24, 1)] }],
  [{ coefficient := 1, powers := [(30, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 20 → SparsePoly (Fin 67) := ![
  [{ coefficient := -1, powers := [(23, 1), (25, 1), (57, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (44, 1), (57, 1), (66, 1)] }],
  [{ coefficient := -2, powers := [(23, 1), (57, 1), (64, 1)] }],
  [{ coefficient := -2, powers := [(23, 1), (54, 1), (57, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(54, 1), (57, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(49, 1), (57, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (57, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (44, 1), (48, 1), (57, 1), (65, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (57, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(57, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (57, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (48, 1), (57, 1), (65, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(57, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(39, 1), (57, 1), (60, 1), (66, 1)] }, { coefficient := -1, powers := [(49, 1), (54, 1), (57, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (56, 1), (57, 1), (65, 1)] }, { coefficient := 1, powers := [(2, 1), (57, 2), (66, 1)] }, { coefficient := 1, powers := [(8, 1), (36, 1), (57, 1), (66, 1)] }],
  [{ coefficient := 2, powers := [(12, 1), (23, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (33, 1), (57, 1)] }, { coefficient := -1, powers := [(12, 1), (23, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (33, 1), (57, 1)] }, { coefficient := -1, powers := [(12, 1), (23, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1), (29, 1), (48, 1), (57, 1), (65, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 2, powers := [(12, 1), (23, 1), (45, 1), (57, 1), (64, 1)] }, { coefficient := 2, powers := [(17, 1), (23, 1), (41, 1), (54, 1), (57, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (57, 1), (60, 1), (66, 1)] }, { coefficient := -1, powers := [(12, 1), (44, 1), (46, 1), (48, 1), (57, 1), (65, 1), (66, 1)] }, { coefficient := 1, powers := [(12, 1), (44, 1), (48, 1), (57, 1), (66, 1)] }, { coefficient := 1, powers := [(12, 1), (47, 1), (48, 1), (57, 1), (65, 1), (66, 1)] }, { coefficient := -1, powers := [(12, 1), (49, 1), (57, 1), (66, 1)] }]
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
    ¬ ∀ index : Fin 20,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component11.SelectedLeafB6_2_7_0.selectedHasNoCommonZero

end Krenn.Component11.SelectedLeafB6_2_7_0
