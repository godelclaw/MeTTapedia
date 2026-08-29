import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component11.SelectedLeafB6_6_5_6

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "ce7f6d285c7bfffdbc7ac18dc47417c7812a6c765b245d9a406dbc7e7c61940e"
def certificateSHA256 : String := "96d758aeaded333879326088559602741e5c4a2318b7a8f476a7330028eaf6a7"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 20 → Fin 675 := ![
  11,
  12,
  13,
  19,
  161,
  183,
  328,
  329,
  341,
  453,
  488,
  557,
  662,
  664,
  665,
  668,
  669,
  671,
  672,
  674
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 20 → SparsePoly (Fin 69) := ![
  [{ coefficient := 1, powers := [(12, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (28, 1)] }],
  [{ coefficient := 1, powers := [(15, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (54, 1)] }, { coefficient := 1, powers := [(15, 1), (20, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (53, 1)] }, { coefficient := 1, powers := [(30, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (49, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1)] }, { coefficient := 1, powers := [(17, 1), (23, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1)] }, { coefficient := 1, powers := [(12, 1), (30, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (54, 1)] }, { coefficient := 1, powers := [(30, 1), (42, 1)] }, { coefficient := 1, powers := [(33, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (60, 1)] }, { coefficient := 1, powers := [(12, 1), (25, 1), (47, 1)] }, { coefficient := 1, powers := [(12, 1), (57, 1)] }, { coefficient := 1, powers := [(17, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (42, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (55, 1)] }, { coefficient := 1, powers := [(12, 1), (19, 1), (28, 1), (45, 1)] }, { coefficient := 1, powers := [(12, 1), (23, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (44, 1), (53, 1)] }, { coefficient := 1, powers := [(23, 1), (57, 1)] }, { coefficient := 1, powers := [(30, 1), (49, 1)] }, { coefficient := 1, powers := [(36, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (39, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (42, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (49, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (23, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (49, 1)] }, { coefficient := 1, powers := [(8, 1), (36, 1), (42, 1)] }, { coefficient := 1, powers := [(12, 1), (23, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1), (30, 1), (49, 1)] }, { coefficient := 1, powers := [(12, 1), (36, 1), (39, 1)] }, { coefficient := 1, powers := [(17, 1), (23, 1), (54, 1)] }, { coefficient := 1, powers := [(17, 1), (30, 1), (42, 1)] }, { coefficient := 1, powers := [(17, 1), (33, 1), (39, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(42, 1)] }],
  [{ coefficient := 1, powers := [(55, 1), (65, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(57, 1), (66, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(24, 1), (67, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(30, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 20 → SparsePoly (Fin 69) := ![
  [{ coefficient := -1, powers := [(23, 1), (55, 1), (57, 1), (65, 1), (67, 1)] }, { coefficient := -1, powers := [(23, 1), (57, 2), (66, 1), (67, 1)] }],
  [{ coefficient := -1, powers := [(23, 1), (47, 1), (57, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(19, 1), (45, 1), (57, 1), (65, 1)] }],
  [{ coefficient := 2, powers := [(17, 1), (20, 1), (23, 1), (57, 1), (62, 1), (66, 1)] }],
  [{ coefficient := -2, powers := [(17, 1), (23, 1), (57, 1), (62, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (44, 1), (57, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(54, 1), (57, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(49, 1), (57, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (57, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (57, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(57, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (57, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(57, 1), (66, 1)] }],
  [{ coefficient := 2, powers := [(17, 1), (23, 1), (54, 1), (57, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(39, 1), (57, 1), (60, 1), (66, 1)] }, { coefficient := -1, powers := [(49, 1), (54, 1), (57, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (55, 1), (57, 1), (65, 1)] }, { coefficient := 1, powers := [(2, 1), (57, 2), (66, 1)] }, { coefficient := 1, powers := [(8, 1), (36, 1), (57, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (33, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (33, 1), (57, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(12, 1), (23, 1), (55, 1), (57, 1), (65, 1)] }, { coefficient := 1, powers := [(12, 1), (23, 1), (57, 2), (66, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (57, 1), (60, 1), (66, 1)] }, { coefficient := 1, powers := [(12, 1), (44, 1), (48, 1), (57, 1), (66, 1)] }, { coefficient := -1, powers := [(12, 1), (49, 1), (57, 1), (66, 1)] }]
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
    (values : Fin 69 → R) :
    ¬ ∀ index : Fin 20,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component11.SelectedLeafB6_6_5_6.selectedHasNoCommonZero

end Krenn.Component11.SelectedLeafB6_6_5_6
