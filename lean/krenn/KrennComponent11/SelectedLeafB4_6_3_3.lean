import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component11.SelectedLeafB4_6_3_3

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "d7548ce1e755c466c2dc3227854e8b5b4ce56ed8229d76e93ea010dd9277e9f5"
def certificateSHA256 : String := "ea1c649f592ced9a30e81dc9c5c275f13dc0fe36a8d081130ec230350cddeec8"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 25 → Fin 675 := ![
  4,
  15,
  16,
  24,
  166,
  286,
  322,
  323,
  329,
  330,
  341,
  346,
  350,
  451,
  453,
  485,
  496,
  497,
  631,
  662,
  665,
  668,
  671,
  672,
  673
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 25 → SparsePoly (Fin 68) := ![
  [{ coefficient := 1, powers := [(3, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (33, 1)] }, { coefficient := 1, powers := [(33, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (24, 1), (41, 1)] }, { coefficient := 1, powers := [(17, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1)] }, { coefficient := 1, powers := [(18, 1), (44, 1)] }, { coefficient := 1, powers := [(24, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (49, 1)] }, { coefficient := 1, powers := [(19, 1), (44, 1)] }, { coefficient := 1, powers := [(24, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1)] }, { coefficient := 1, powers := [(12, 1), (30, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (60, 1)] }, { coefficient := 1, powers := [(12, 1), (49, 1)] }, { coefficient := 1, powers := [(17, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (54, 1)] }, { coefficient := 1, powers := [(30, 1), (42, 1)] }, { coefficient := 1, powers := [(33, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(18, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(44, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (49, 1), (52, 1)] }, { coefficient := 1, powers := [(19, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(49, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (36, 1)] }, { coefficient := 1, powers := [(22, 1), (44, 1)] }, { coefficient := 1, powers := [(28, 1), (44, 1)] }, { coefficient := 1, powers := [(36, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (60, 1)] }, { coefficient := 1, powers := [(12, 1), (25, 1), (47, 1)] }, { coefficient := 1, powers := [(12, 1), (57, 1)] }, { coefficient := 1, powers := [(17, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (37, 1), (60, 1)] }, { coefficient := 1, powers := [(12, 1), (28, 1), (44, 1)] }, { coefficient := 1, powers := [(12, 1), (36, 1), (37, 1)] }, { coefficient := 1, powers := [(17, 1), (33, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (30, 1), (60, 1)] }, { coefficient := 1, powers := [(3, 1), (33, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (36, 1), (54, 1)] }, { coefficient := 1, powers := [(22, 1), (44, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (32, 1), (57, 1)] }, { coefficient := 1, powers := [(20, 1), (44, 1), (53, 1)] }, { coefficient := 1, powers := [(20, 1), (57, 1)] }, { coefficient := 1, powers := [(26, 1), (44, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (27, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (32, 1), (56, 1)] }, { coefficient := 1, powers := [(3, 1), (35, 1), (52, 1)] }, { coefficient := 1, powers := [(20, 1), (52, 1)] }, { coefficient := 1, powers := [(20, 1), (56, 1)] }, { coefficient := 1, powers := [(27, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (39, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (42, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (49, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (23, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (49, 1)] }, { coefficient := 1, powers := [(8, 1), (36, 1), (42, 1)] }, { coefficient := 1, powers := [(12, 1), (23, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1), (30, 1), (49, 1)] }, { coefficient := 1, powers := [(12, 1), (36, 1), (39, 1)] }, { coefficient := 1, powers := [(17, 1), (23, 1), (54, 1)] }, { coefficient := 1, powers := [(17, 1), (30, 1), (42, 1)] }, { coefficient := 1, powers := [(17, 1), (33, 1), (39, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(42, 1)] }],
  [{ coefficient := 1, powers := [(57, 1), (65, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(24, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (66, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 25 → SparsePoly (Fin 68) := ![
  [{ coefficient := 1, powers := [(5, 1), (27, 1), (30, 1), (59, 1), (66, 1)] }, { coefficient := -1, powers := [(5, 1), (30, 1), (32, 1), (52, 1), (66, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (35, 1), (52, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (27, 1), (39, 1), (59, 1), (66, 1)] }, { coefficient := -1, powers := [(22, 1), (32, 1), (39, 1), (52, 1), (66, 1)] }, { coefficient := 1, powers := [(22, 1), (35, 1), (39, 1), (52, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (23, 1), (25, 1), (27, 1), (59, 1), (66, 1)] }, { coefficient := -1, powers := [(3, 1), (23, 1), (25, 1), (32, 1), (52, 1), (66, 1)] }, { coefficient := 1, powers := [(3, 1), (23, 1), (25, 1), (35, 1), (52, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (27, 1), (44, 1), (59, 1), (66, 1)] }, { coefficient := -1, powers := [(5, 1), (32, 1), (44, 1), (52, 1), (66, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (44, 1), (52, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(17, 1), (27, 1), (39, 1), (59, 1), (66, 1)] }, { coefficient := 1, powers := [(17, 1), (32, 1), (39, 1), (52, 1), (66, 1)] }, { coefficient := -1, powers := [(17, 1), (35, 1), (39, 1), (52, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (23, 1), (27, 1), (54, 1), (59, 1), (66, 1)] }, { coefficient := -1, powers := [(3, 1), (23, 1), (32, 1), (52, 1), (54, 1), (66, 1)] }, { coefficient := 1, powers := [(3, 1), (23, 1), (35, 1), (52, 1), (54, 1), (66, 1)] }, { coefficient := 1, powers := [(6, 1), (27, 1), (33, 1), (39, 1), (59, 1), (66, 1)] }, { coefficient := -1, powers := [(6, 1), (32, 1), (33, 1), (39, 1), (52, 1), (66, 1)] }, { coefficient := 1, powers := [(6, 1), (33, 1), (35, 1), (39, 1), (52, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(20, 1), (52, 2), (53, 1), (65, 1), (66, 1)] }, { coefficient := -1, powers := [(20, 1), (52, 1), (53, 1), (56, 1), (65, 1), (66, 1)] }, { coefficient := -1, powers := [(26, 1), (52, 2), (53, 1), (65, 1), (66, 1)] }, { coefficient := -1, powers := [(26, 1), (52, 1), (53, 1), (56, 1), (65, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (12, 1), (27, 1), (30, 1), (52, 1), (59, 1), (66, 1)] }, { coefficient := 1, powers := [(3, 1), (12, 1), (30, 1), (32, 1), (52, 2), (66, 1)] }, { coefficient := -1, powers := [(3, 1), (12, 1), (30, 1), (35, 1), (52, 2), (66, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (27, 1), (49, 1), (59, 1), (66, 1)] }, { coefficient := 1, powers := [(3, 1), (32, 1), (49, 1), (52, 1), (66, 1)] }, { coefficient := -1, powers := [(3, 1), (35, 1), (49, 1), (52, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (27, 1), (30, 1), (59, 1), (66, 1)] }, { coefficient := 1, powers := [(3, 1), (30, 1), (32, 1), (52, 1), (66, 1)] }, { coefficient := -1, powers := [(3, 1), (30, 1), (35, 1), (52, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (17, 1), (27, 1), (59, 1), (66, 1)] }, { coefficient := 1, powers := [(3, 1), (17, 1), (32, 1), (52, 1), (66, 1)] }, { coefficient := -1, powers := [(3, 1), (17, 1), (35, 1), (52, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (52, 1), (53, 1), (65, 1), (66, 1)] }, { coefficient := 1, powers := [(20, 1), (53, 1), (56, 1), (65, 1), (66, 1)] }, { coefficient := 1, powers := [(26, 1), (52, 1), (53, 1), (65, 1), (66, 1)] }, { coefficient := 1, powers := [(26, 1), (53, 1), (56, 1), (65, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (12, 1), (27, 1), (30, 1), (59, 1), (66, 1)] }, { coefficient := -1, powers := [(3, 1), (12, 1), (30, 1), (32, 1), (52, 1), (66, 1)] }, { coefficient := 1, powers := [(3, 1), (12, 1), (30, 1), (35, 1), (52, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (27, 1), (39, 1), (59, 1), (66, 1)] }, { coefficient := 1, powers := [(12, 1), (32, 1), (39, 1), (52, 1), (66, 1)] }, { coefficient := -1, powers := [(12, 1), (35, 1), (39, 1), (52, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (23, 1), (27, 1), (59, 1), (66, 1)] }, { coefficient := 1, powers := [(3, 1), (23, 1), (32, 1), (52, 1), (66, 1)] }, { coefficient := -1, powers := [(3, 1), (23, 1), (35, 1), (52, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (39, 1), (59, 1), (66, 1)] }, { coefficient := -1, powers := [(32, 1), (39, 1), (52, 1), (66, 1)] }, { coefficient := 1, powers := [(35, 1), (39, 1), (52, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (27, 1), (59, 1), (66, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (52, 1), (66, 1)] }, { coefficient := -1, powers := [(5, 1), (35, 1), (52, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(52, 1), (65, 1), (66, 1)] }, { coefficient := -1, powers := [(56, 1), (65, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(66, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (27, 1), (59, 1), (66, 1)] }, { coefficient := -1, powers := [(3, 1), (32, 1), (52, 1), (66, 1)] }, { coefficient := 1, powers := [(3, 1), (35, 1), (52, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (27, 1), (39, 1), (59, 1), (60, 1), (66, 1)] }, { coefficient := 1, powers := [(3, 1), (32, 1), (39, 1), (52, 1), (60, 1), (66, 1)] }, { coefficient := -1, powers := [(3, 1), (35, 1), (39, 1), (52, 1), (60, 1), (66, 1)] }, { coefficient := -1, powers := [(27, 1), (37, 1), (39, 1), (59, 1), (60, 1), (66, 1)] }, { coefficient := 1, powers := [(32, 1), (37, 1), (39, 1), (52, 1), (60, 1), (66, 1)] }, { coefficient := -1, powers := [(35, 1), (37, 1), (39, 1), (52, 1), (60, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (3, 1), (27, 1), (57, 1), (59, 1), (66, 1)] }, { coefficient := 1, powers := [(2, 1), (3, 1), (32, 1), (52, 1), (57, 1), (66, 1)] }, { coefficient := -1, powers := [(2, 1), (3, 1), (35, 1), (52, 1), (57, 1), (66, 1)] }, { coefficient := -1, powers := [(3, 1), (8, 1), (27, 1), (36, 1), (59, 1), (66, 1)] }, { coefficient := 1, powers := [(3, 1), (8, 1), (32, 1), (36, 1), (52, 1), (66, 1)] }, { coefficient := -1, powers := [(3, 1), (8, 1), (35, 1), (36, 1), (52, 1), (66, 1)] }, { coefficient := 1, powers := [(3, 1), (17, 1), (27, 1), (30, 1), (59, 1), (66, 1)] }, { coefficient := -1, powers := [(3, 1), (17, 1), (30, 1), (32, 1), (52, 1), (66, 1)] }, { coefficient := 1, powers := [(3, 1), (17, 1), (30, 1), (35, 1), (52, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (32, 1), (52, 1), (66, 1)] }, { coefficient := 1, powers := [(3, 1), (32, 1), (56, 1), (66, 1)] }, { coefficient := 1, powers := [(20, 1), (52, 1), (66, 1)] }, { coefficient := 1, powers := [(20, 1), (56, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (12, 1), (27, 1), (30, 1), (49, 1), (52, 1), (59, 1), (66, 1)] }, { coefficient := -1, powers := [(3, 1), (12, 1), (30, 1), (32, 1), (49, 1), (52, 2), (66, 1)] }, { coefficient := 1, powers := [(3, 1), (12, 1), (30, 1), (35, 1), (49, 1), (52, 2), (66, 1)] }, { coefficient := -1, powers := [(3, 1), (17, 1), (23, 1), (27, 1), (41, 1), (54, 1), (59, 1), (66, 1)] }, { coefficient := 1, powers := [(3, 1), (17, 1), (23, 1), (32, 1), (41, 1), (52, 1), (54, 1), (66, 1)] }, { coefficient := -1, powers := [(3, 1), (17, 1), (23, 1), (35, 1), (41, 1), (52, 1), (54, 1), (66, 1)] }, { coefficient := -1, powers := [(6, 1), (17, 1), (27, 1), (33, 1), (39, 1), (41, 1), (59, 1), (66, 1)] }, { coefficient := 1, powers := [(6, 1), (17, 1), (32, 1), (33, 1), (39, 1), (41, 1), (52, 1), (66, 1)] }, { coefficient := -1, powers := [(6, 1), (17, 1), (33, 1), (35, 1), (39, 1), (41, 1), (52, 1), (66, 1)] }, { coefficient := 1, powers := [(20, 1), (44, 1), (52, 2), (53, 1), (65, 1), (66, 1)] }, { coefficient := 1, powers := [(20, 1), (44, 1), (52, 1), (53, 1), (56, 1), (65, 1), (66, 1)] }, { coefficient := 1, powers := [(26, 1), (44, 1), (52, 2), (53, 1), (65, 1), (66, 1)] }, { coefficient := 1, powers := [(26, 1), (44, 1), (52, 1), (53, 1), (56, 1), (65, 1), (66, 1)] }],
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
    (values : Fin 68 → R) :
    ¬ ∀ index : Fin 25,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component11.SelectedLeafB4_6_3_3.selectedHasNoCommonZero

end Krenn.Component11.SelectedLeafB4_6_3_3
