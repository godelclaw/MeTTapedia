import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component11.SelectedLeafB4_2_3

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "ee2b6a1c9080660a3f1d6d61ce4d7af9ba82133cadb350484e2bb2b15bf568a7"
def certificateSHA256 : String := "cb86849a7d198d9b8ef31bfa92ed52239838f0659e937503256dc88b51583154"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 26 → Fin 672 := ![
  11,
  13,
  15,
  16,
  20,
  28,
  160,
  182,
  262,
  322,
  323,
  328,
  329,
  330,
  340,
  341,
  453,
  462,
  489,
  557,
  629,
  662,
  663,
  665,
  668,
  670
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 26 → SparsePoly (Fin 65) := ![
  [{ coefficient := 1, powers := [(12, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (28, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (18, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (54, 1)] }, { coefficient := 1, powers := [(18, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (44, 1)] }, { coefficient := 1, powers := [(28, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (18, 1), (56, 1)] }, { coefficient := 1, powers := [(12, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1)] }, { coefficient := 1, powers := [(18, 1), (44, 1)] }, { coefficient := 1, powers := [(24, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (49, 1)] }, { coefficient := 1, powers := [(19, 1), (44, 1)] }, { coefficient := 1, powers := [(24, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (49, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1)] }, { coefficient := 1, powers := [(17, 1), (23, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1)] }, { coefficient := 1, powers := [(12, 1), (30, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (60, 1)] }, { coefficient := 1, powers := [(12, 1), (49, 1)] }, { coefficient := 1, powers := [(17, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (52, 1)] }, { coefficient := 1, powers := [(23, 1), (56, 1)] }, { coefficient := 1, powers := [(29, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (54, 1)] }, { coefficient := 1, powers := [(30, 1), (42, 1)] }, { coefficient := 1, powers := [(33, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (60, 1)] }, { coefficient := 1, powers := [(12, 1), (25, 1), (47, 1)] }, { coefficient := 1, powers := [(12, 1), (57, 1)] }, { coefficient := 1, powers := [(17, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1), (53, 1)] }, { coefficient := 1, powers := [(18, 1), (44, 1), (53, 1)] }, { coefficient := 1, powers := [(18, 1), (57, 1)] }, { coefficient := 1, powers := [(25, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (42, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (56, 1)] }, { coefficient := 1, powers := [(12, 1), (23, 1), (56, 1)] }, { coefficient := 1, powers := [(12, 1), (29, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (44, 1), (53, 1)] }, { coefficient := 1, powers := [(23, 1), (57, 1)] }, { coefficient := 1, powers := [(30, 1), (49, 1)] }, { coefficient := 1, powers := [(36, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (47, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (29, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (47, 1)] }, { coefficient := 1, powers := [(12, 1), (29, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1), (30, 1), (47, 1)] }, { coefficient := 1, powers := [(17, 1), (29, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (39, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (42, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (49, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (23, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (49, 1)] }, { coefficient := 1, powers := [(8, 1), (36, 1), (42, 1)] }, { coefficient := 1, powers := [(12, 1), (23, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1), (30, 1), (49, 1)] }, { coefficient := 1, powers := [(12, 1), (36, 1), (39, 1)] }, { coefficient := 1, powers := [(17, 1), (23, 1), (54, 1)] }, { coefficient := 1, powers := [(17, 1), (30, 1), (42, 1)] }, { coefficient := 1, powers := [(17, 1), (33, 1), (39, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (61, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(42, 1)] }],
  [{ coefficient := 1, powers := [(56, 1), (63, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 26 → SparsePoly (Fin 65) := ![
  [{ coefficient := 2, powers := [(30, 1), (49, 1), (56, 1), (61, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(49, 1), (53, 1), (56, 1), (63, 1)] }],
  [{ coefficient := 2, powers := [(19, 1), (30, 1), (56, 1), (61, 1), (63, 1)] }, { coefficient := -1, powers := [(23, 1), (24, 1), (52, 1), (53, 1), (56, 1), (63, 1)] }, { coefficient := 1, powers := [(23, 1), (24, 1), (53, 1), (56, 2), (63, 1)] }, { coefficient := 1, powers := [(23, 1), (25, 1), (52, 1), (56, 1), (63, 1)] }, { coefficient := -1, powers := [(23, 1), (25, 1), (56, 2), (63, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (25, 1), (52, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(23, 1), (52, 1), (54, 1), (61, 1), (63, 1)] }, { coefficient := 1, powers := [(23, 1), (54, 1), (56, 1), (61, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (48, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (23, 1), (52, 1), (61, 1), (63, 1)] }, { coefficient := -1, powers := [(17, 1), (23, 1), (56, 1), (61, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (53, 1), (56, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (52, 1), (57, 1), (63, 1)] }, { coefficient := -1, powers := [(23, 1), (56, 1), (57, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (23, 1), (52, 1), (53, 1), (56, 1), (63, 1)] }, { coefficient := -1, powers := [(12, 1), (23, 1), (53, 1), (56, 2), (63, 1)] }],
  [{ coefficient := -2, powers := [(12, 1), (30, 1), (56, 1), (61, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(54, 1), (56, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(47, 1), (48, 1), (63, 1)] }, { coefficient := 1, powers := [(49, 1), (56, 1), (63, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (30, 1), (56, 1), (61, 1), (63, 1)] }, { coefficient := -1, powers := [(30, 1), (56, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (60, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (56, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(23, 1), (52, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (23, 1), (52, 1), (56, 1), (63, 1)] }, { coefficient := 1, powers := [(12, 1), (23, 1), (56, 2), (63, 1)] }],
  [{ coefficient := 1, powers := [(57, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (56, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(48, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(56, 1), (63, 1)] }],
  [{ coefficient := -2, powers := [(5, 1), (30, 1), (56, 1), (60, 1), (63, 1)] }, { coefficient := -1, powers := [(17, 1), (23, 1), (52, 1), (54, 1), (63, 1)] }, { coefficient := 1, powers := [(17, 1), (23, 1), (54, 1), (56, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(39, 1), (56, 1), (60, 1), (63, 1)] }, { coefficient := -1, powers := [(49, 1), (54, 1), (56, 1), (63, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (17, 1), (30, 1), (56, 1), (61, 1), (63, 1)] }, { coefficient := 1, powers := [(8, 1), (36, 1), (56, 1), (63, 1)] }, { coefficient := 1, powers := [(17, 1), (30, 1), (56, 1), (63, 1)] }],
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
    (values : Fin 65 → R) :
    ¬ ∀ index : Fin 26,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component11.SelectedLeafB4_2_3.selectedHasNoCommonZero

end Krenn.Component11.SelectedLeafB4_2_3
