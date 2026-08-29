import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component11.SelectedLeafB6_6_3_2

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "b1bac3102c0986911276df21e702494cde9b53dfb92c973556ce1a06f93d0f02"
def certificateSHA256 : String := "28cd4e02df553297d322f11b82773fd6a0056b5a96eff8ac3029f4cb6f5f2369"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 25 → Fin 675 := ![
  10,
  16,
  183,
  262,
  286,
  322,
  328,
  329,
  340,
  341,
  346,
  453,
  462,
  489,
  557,
  588,
  614,
  662,
  663,
  665,
  668,
  670,
  671,
  672,
  674
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 25 → SparsePoly (Fin 68) := ![
  [{ coefficient := 1, powers := [(8, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (53, 1)] }, { coefficient := 1, powers := [(30, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (18, 1), (56, 1)] }, { coefficient := 1, powers := [(12, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (24, 1), (41, 1)] }, { coefficient := 1, powers := [(17, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1)] }, { coefficient := 1, powers := [(18, 1), (44, 1)] }, { coefficient := 1, powers := [(24, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (49, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1)] }, { coefficient := 1, powers := [(17, 1), (23, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1)] }, { coefficient := 1, powers := [(12, 1), (30, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (52, 1)] }, { coefficient := 1, powers := [(23, 1), (56, 1)] }, { coefficient := 1, powers := [(29, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (54, 1)] }, { coefficient := 1, powers := [(30, 1), (42, 1)] }, { coefficient := 1, powers := [(33, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(18, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(44, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (60, 1)] }, { coefficient := 1, powers := [(12, 1), (25, 1), (47, 1)] }, { coefficient := 1, powers := [(12, 1), (57, 1)] }, { coefficient := 1, powers := [(17, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1), (53, 1)] }, { coefficient := 1, powers := [(18, 1), (44, 1), (53, 1)] }, { coefficient := 1, powers := [(18, 1), (57, 1)] }, { coefficient := 1, powers := [(25, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (42, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (56, 1)] }, { coefficient := 1, powers := [(12, 1), (23, 1), (56, 1)] }, { coefficient := 1, powers := [(12, 1), (29, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (44, 1), (53, 1)] }, { coefficient := 1, powers := [(23, 1), (57, 1)] }, { coefficient := 1, powers := [(30, 1), (49, 1)] }, { coefficient := 1, powers := [(36, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1)] }, { coefficient := 1, powers := [(6, 1), (59, 1)] }, { coefficient := 1, powers := [(24, 1), (41, 1)] }, { coefficient := 1, powers := [(24, 1), (46, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (37, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1)] }, { coefficient := 1, powers := [(3, 1), (24, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (18, 1), (59, 1)] }, { coefficient := 1, powers := [(18, 1)] }, { coefficient := 1, powers := [(24, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (39, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (42, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (49, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (23, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (49, 1)] }, { coefficient := 1, powers := [(8, 1), (36, 1), (42, 1)] }, { coefficient := 1, powers := [(12, 1), (23, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1), (30, 1), (49, 1)] }, { coefficient := 1, powers := [(12, 1), (36, 1), (39, 1)] }, { coefficient := 1, powers := [(17, 1), (23, 1), (54, 1)] }, { coefficient := 1, powers := [(17, 1), (30, 1), (42, 1)] }, { coefficient := 1, powers := [(17, 1), (33, 1), (39, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (61, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(42, 1)] }],
  [{ coefficient := 1, powers := [(56, 1), (65, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(57, 1), (66, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(24, 1)] }],
  [{ coefficient := 1, powers := [(30, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 25 → SparsePoly (Fin 68) := ![
  [{ coefficient := -1, powers := [(23, 1), (37, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(23, 1), (25, 1), (37, 1), (59, 1)] }, { coefficient := -1, powers := [(23, 1), (25, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (44, 1)] }],
  [{ coefficient := -1, powers := [(23, 1), (57, 1)] }, { coefficient := -1, powers := [(29, 1), (48, 1), (57, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(23, 1), (37, 1), (54, 1), (59, 1)] }, { coefficient := -2, powers := [(23, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (23, 1), (25, 1), (46, 1), (52, 1), (57, 1), (66, 1)] }, { coefficient := -1, powers := [(12, 1), (23, 1), (25, 1), (52, 2), (57, 1), (66, 1)] }, { coefficient := 1, powers := [(12, 1), (23, 1), (46, 1), (53, 1), (57, 1), (66, 1)] }, { coefficient := 1, powers := [(12, 1), (23, 1), (52, 1), (53, 1), (57, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(54, 1)] }],
  [{ coefficient := 1, powers := [(49, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (18, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(17, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (23, 1), (25, 1), (46, 1), (57, 1), (66, 1)] }, { coefficient := 1, powers := [(12, 1), (23, 1), (25, 1), (52, 1), (57, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (37, 1), (59, 1)] }, { coefficient := 1, powers := [(23, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (23, 1), (46, 1), (57, 1), (66, 1)] }, { coefficient := -1, powers := [(12, 1), (23, 1), (52, 1), (57, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(57, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(12, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (18, 1), (23, 1), (57, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (23, 1), (57, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(12, 1), (18, 1), (23, 1), (46, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1), (23, 1), (37, 1), (57, 1), (59, 1)] }, { coefficient := 1, powers := [(12, 1), (23, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(39, 1), (60, 1)] }, { coefficient := -1, powers := [(49, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (56, 1), (57, 1), (65, 1)] }, { coefficient := 1, powers := [(2, 1), (57, 1)] }, { coefficient := 1, powers := [(8, 1), (36, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (33, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1), (18, 1), (29, 1), (48, 1), (57, 1)] }, { coefficient := -1, powers := [(12, 1), (23, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (18, 1), (23, 1), (46, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1), (18, 1), (23, 1), (52, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (12, 1), (23, 1), (57, 1), (59, 1), (61, 1)] }, { coefficient := -1, powers := [(12, 1), (18, 1), (23, 1), (41, 1), (57, 1), (61, 1)] }, { coefficient := -1, powers := [(12, 1), (18, 1), (23, 1), (46, 1), (57, 1), (61, 1)] }, { coefficient := 1, powers := [(12, 1), (23, 1), (25, 1), (44, 1), (46, 1), (52, 1), (57, 1), (66, 1)] }, { coefficient := 1, powers := [(12, 1), (23, 1), (25, 1), (44, 1), (52, 2), (57, 1), (66, 1)] }, { coefficient := -1, powers := [(12, 1), (23, 1), (44, 1), (46, 1), (53, 1), (57, 1), (66, 1)] }, { coefficient := -1, powers := [(12, 1), (23, 1), (44, 1), (52, 1), (53, 1), (57, 1), (66, 1)] }, { coefficient := 1, powers := [(12, 1), (23, 1), (57, 1), (61, 1)] }, { coefficient := 1, powers := [(17, 1), (23, 1), (37, 1), (41, 1), (54, 1), (59, 1)] }, { coefficient := 2, powers := [(17, 1), (23, 1), (41, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (60, 1)] }, { coefficient := 1, powers := [(12, 1), (44, 1), (48, 1)] }, { coefficient := -1, powers := [(12, 1), (49, 1)] }]
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
    (values : Fin 68 → R) :
    ¬ ∀ index : Fin 25,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component11.SelectedLeafB6_6_3_2.selectedHasNoCommonZero

end Krenn.Component11.SelectedLeafB6_6_3_2
