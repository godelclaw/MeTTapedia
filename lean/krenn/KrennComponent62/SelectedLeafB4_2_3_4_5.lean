import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component62.SelectedLeafB4_2_3_4_5

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "1ada53beeec542c8ec8e5bc70c0551440e5635a8b610b570de493ceac26c8c4b"
def certificateSHA256 : String := "db2102a45e48e1c54f6bc7cb69911f7baf604e020fbb08600f94cd05ce39569b"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 15 → Fin 673 := ![
  18,
  135,
  158,
  191,
  301,
  302,
  454,
  557,
  589,
  657,
  660,
  663,
  665,
  669,
  671
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 15 → SparsePoly (Fin 67) := ![
  [{ coefficient := 1, powers := [(22, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (45, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (50, 1)] }, { coefficient := 1, powers := [(22, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (22, 1), (58, 1)] }, { coefficient := 1, powers := [(22, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (46, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (53, 1)] }, { coefficient := 1, powers := [(8, 1), (30, 1)] }, { coefficient := 1, powers := [(12, 1), (27, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (53, 1)] }, { coefficient := 1, powers := [(27, 1), (39, 1)] }, { coefficient := 1, powers := [(27, 1), (45, 1), (48, 1)] }, { coefficient := 1, powers := [(30, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (41, 1), (52, 1)] }, { coefficient := 1, powers := [(22, 1), (56, 1)] }, { coefficient := 1, powers := [(27, 1), (46, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (39, 1), (55, 1)] }, { coefficient := 1, powers := [(2, 1), (45, 1), (51, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (55, 1)] }, { coefficient := 1, powers := [(12, 1), (22, 1), (55, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (36, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (46, 1), (53, 1)] }, { coefficient := 1, powers := [(5, 1), (27, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (53, 1)] }, { coefficient := 1, powers := [(8, 1), (22, 1), (59, 1)] }, { coefficient := 1, powers := [(8, 1), (30, 1), (46, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (39, 1)] }, { coefficient := 1, powers := [(12, 1), (22, 1), (56, 1)] }, { coefficient := 1, powers := [(12, 1), (27, 1), (46, 1)] }, { coefficient := 1, powers := [(12, 1), (33, 1), (36, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (53, 1)] }, { coefficient := 1, powers := [(17, 1), (27, 1), (39, 1)] }, { coefficient := 1, powers := [(17, 1), (30, 1), (36, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(39, 1)] }],
  [{ coefficient := 1, powers := [(55, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(27, 1)] }],
  [{ coefficient := 1, powers := [(58, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 15 → SparsePoly (Fin 67) := ![
  [{ coefficient := -1, powers := [(12, 1), (52, 1), (55, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(51, 1), (56, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (56, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (55, 1), (59, 1), (62, 1)] }, { coefficient := 1, powers := [(12, 1), (50, 1), (56, 1), (62, 1)] }, { coefficient := -1, powers := [(17, 1), (53, 1), (55, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(53, 1), (55, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(46, 1), (55, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (55, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (55, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(56, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(55, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(36, 1), (55, 1), (59, 1), (62, 1)] }, { coefficient := -1, powers := [(46, 1), (53, 1), (55, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (33, 1), (55, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(5, 1), (55, 1), (59, 1), (62, 1)] }, { coefficient := -1, powers := [(12, 1), (46, 1), (55, 1), (62, 1)] }, { coefficient := -1, powers := [(17, 1), (45, 1), (48, 1), (55, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (8, 1), (22, 1), (55, 1), (59, 1), (62, 1)] }, { coefficient := -1, powers := [(6, 1), (12, 1), (22, 1), (50, 1), (56, 1), (62, 1)] }, { coefficient := 1, powers := [(6, 1), (17, 1), (22, 1), (53, 1), (55, 1), (62, 1)] }]
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

#print axioms Krenn.Component62.SelectedLeafB4_2_3_4_5.selectedHasNoCommonZero

end Krenn.Component62.SelectedLeafB4_2_3_4_5
