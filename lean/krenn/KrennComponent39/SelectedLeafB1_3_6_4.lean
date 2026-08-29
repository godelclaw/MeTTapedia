import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component39.SelectedLeafB1_3_6_4

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "b8e3a075d27fbd12ce08cdad14028b6105614451f67b0e216223131ba87acf9d"
def certificateSHA256 : String := "90a831e47ef2e0bf9ea06628c003cff361b505dd1ffe7fe788017c5f14d456f3"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 23 → Fin 673 := ![
  18,
  19,
  173,
  268,
  302,
  304,
  305,
  321,
  465,
  477,
  479,
  511,
  537,
  602,
  603,
  644,
  659,
  661,
  662,
  666,
  667,
  670,
  671
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 23 → SparsePoly (Fin 67) := ![
  [{ coefficient := 1, powers := [(14, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (23, 1)] }, { coefficient := 1, powers := [(14, 1), (18, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (19, 1), (52, 1)] }, { coefficient := 1, powers := [(14, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (49, 1)] }, { coefficient := 1, powers := [(18, 1), (49, 1)] }, { coefficient := 1, powers := [(23, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (44, 1)] }, { coefficient := 1, powers := [(4, 1), (33, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (51, 1)] }, { coefficient := 1, powers := [(7, 1), (30, 1)] }, { coefficient := 1, powers := [(10, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1), (49, 1)] }, { coefficient := 1, powers := [(23, 1), (44, 1), (49, 1)] }, { coefficient := 1, powers := [(49, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1), (49, 1)] }, { coefficient := 1, powers := [(19, 1), (49, 1)] }, { coefficient := 1, powers := [(23, 1), (40, 1)] }, { coefficient := 1, powers := [(23, 1), (46, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (39, 1), (55, 1)] }, { coefficient := 1, powers := [(1, 1), (43, 1)] }, { coefficient := 1, powers := [(4, 1), (30, 1), (55, 1)] }, { coefficient := 1, powers := [(10, 1), (20, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (40, 1), (56, 1)] }, { coefficient := 1, powers := [(1, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(7, 1), (33, 1), (40, 1)] }, { coefficient := 1, powers := [(14, 1), (25, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (23, 1), (59, 1)] }, { coefficient := 1, powers := [(10, 1), (23, 1), (44, 1)] }, { coefficient := 1, powers := [(14, 1), (23, 1), (39, 1)] }, { coefficient := 1, powers := [(14, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (18, 1), (59, 1)] }, { coefficient := 1, powers := [(10, 1), (18, 1), (56, 1)] }, { coefficient := 1, powers := [(10, 1)] }, { coefficient := 1, powers := [(14, 1), (18, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (59, 1)] }, { coefficient := 1, powers := [(10, 1), (44, 1)] }, { coefficient := 1, powers := [(10, 1), (56, 1)] }, { coefficient := 1, powers := [(14, 1), (39, 1)] }, { coefficient := 1, powers := [(14, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (51, 1)] }, { coefficient := 1, powers := [(20, 1), (56, 1)] }, { coefficient := 1, powers := [(25, 1), (39, 1)] }, { coefficient := 1, powers := [(25, 1), (44, 1)] }, { coefficient := 1, powers := [(30, 1), (36, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (36, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (44, 1), (51, 1)] }, { coefficient := 1, powers := [(39, 1)] }, { coefficient := 1, powers := [(44, 1)] }, { coefficient := 1, powers := [(51, 1)] }, { coefficient := 1, powers := [(56, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (36, 1), (59, 1)] }, { coefficient := 1, powers := [(1, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(1, 1), (44, 1), (51, 1)] }, { coefficient := 1, powers := [(4, 1), (25, 1), (59, 1)] }, { coefficient := 1, powers := [(4, 1), (30, 1), (56, 1)] }, { coefficient := 1, powers := [(4, 1), (33, 1), (51, 1)] }, { coefficient := 1, powers := [(7, 1), (20, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (30, 1), (44, 1)] }, { coefficient := 1, powers := [(7, 1), (33, 1), (39, 1)] }, { coefficient := 1, powers := [(10, 1), (20, 1), (56, 1)] }, { coefficient := 1, powers := [(10, 1), (25, 1), (44, 1)] }, { coefficient := 1, powers := [(10, 1), (33, 1), (36, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1), (51, 1)] }, { coefficient := 1, powers := [(14, 1), (25, 1), (39, 1)] }, { coefficient := 1, powers := [(14, 1), (30, 1), (36, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1)] }],
  [{ coefficient := 1, powers := [(1, 1)] }],
  [{ coefficient := 1, powers := [(40, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(55, 1), (64, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(23, 1), (66, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(25, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 23 → SparsePoly (Fin 67) := ![
  [{ coefficient := -1, powers := [(19, 1), (20, 1), (23, 1), (44, 1), (51, 1), (56, 1), (63, 1)] }, { coefficient := 1, powers := [(19, 1), (23, 1), (33, 1), (36, 1), (44, 1), (51, 1), (63, 1)] }, { coefficient := 1, powers := [(20, 1), (23, 1), (46, 1), (51, 1), (56, 1), (63, 1)] }, { coefficient := -1, powers := [(23, 1), (33, 1), (36, 1), (46, 1), (51, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (19, 1), (20, 1), (51, 1), (56, 1), (63, 1)] }, { coefficient := -1, powers := [(18, 1), (19, 1), (20, 1), (56, 1), (63, 1), (66, 1)] }, { coefficient := -1, powers := [(18, 1), (19, 1), (33, 1), (36, 1), (51, 1), (63, 1)] }, { coefficient := 1, powers := [(18, 1), (19, 1), (33, 1), (36, 1), (63, 1), (66, 1)] }, { coefficient := 2, powers := [(19, 1), (20, 1), (51, 1), (63, 1)] }, { coefficient := 1, powers := [(19, 1), (20, 1), (56, 1), (63, 1)] }, { coefficient := -1, powers := [(19, 1), (20, 1), (63, 1), (66, 1)] }, { coefficient := 1, powers := [(19, 1), (33, 1), (36, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(19, 1), (20, 1), (44, 1), (49, 1), (51, 1), (56, 1), (63, 1)] }, { coefficient := 1, powers := [(19, 1), (33, 1), (36, 1), (44, 1), (49, 1), (51, 1), (63, 1)] }, { coefficient := 1, powers := [(20, 1), (46, 1), (49, 1), (51, 1), (56, 1), (63, 1)] }, { coefficient := 1, powers := [(20, 1), (51, 1), (56, 1)] }, { coefficient := -1, powers := [(33, 1), (36, 1), (46, 1), (49, 1), (51, 1), (63, 1)] }, { coefficient := -1, powers := [(33, 1), (36, 1), (51, 1)] }],
  [{ coefficient := -1, powers := [(18, 1), (20, 1), (51, 1), (56, 1), (63, 1)] }, { coefficient := 1, powers := [(18, 1), (20, 1), (56, 1), (63, 1), (66, 1)] }, { coefficient := 1, powers := [(18, 1), (33, 1), (36, 1), (51, 1), (63, 1)] }, { coefficient := -1, powers := [(18, 1), (33, 1), (36, 1), (63, 1), (66, 1)] }, { coefficient := -2, powers := [(20, 1), (51, 1), (63, 1)] }, { coefficient := -1, powers := [(20, 1), (56, 1), (63, 1)] }, { coefficient := 1, powers := [(20, 1), (63, 1), (66, 1)] }, { coefficient := -1, powers := [(33, 1), (36, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (19, 1), (20, 1), (44, 1), (51, 1), (56, 1), (63, 1)] }, { coefficient := -1, powers := [(14, 1), (19, 1), (33, 1), (36, 1), (44, 1), (51, 1), (63, 1)] }, { coefficient := -1, powers := [(14, 1), (20, 1), (46, 1), (51, 1), (56, 1), (63, 1)] }, { coefficient := 1, powers := [(14, 1), (33, 1), (36, 1), (46, 1), (51, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(51, 1)] }],
  [{ coefficient := 1, powers := [(44, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (19, 1), (20, 1), (51, 1), (56, 1), (63, 1)] }, { coefficient := -1, powers := [(10, 1), (19, 1), (33, 1), (36, 1), (51, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(10, 1), (20, 1), (51, 1), (56, 1), (63, 1)] }, { coefficient := 1, powers := [(10, 1), (33, 1), (36, 1), (51, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(56, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(44, 1), (63, 1)] }, { coefficient := -1, powers := [(51, 1), (63, 1)] }, { coefficient := -1, powers := [(56, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(18, 1), (20, 1), (56, 1), (66, 1)] }, { coefficient := 1, powers := [(18, 1), (33, 1), (36, 1), (66, 1)] }, { coefficient := -1, powers := [(20, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(20, 1), (56, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (20, 1), (23, 1), (56, 1), (66, 1)] }, { coefficient := -1, powers := [(18, 1), (23, 1), (33, 1), (36, 1), (66, 1)] }, { coefficient := 1, powers := [(20, 1), (23, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(14, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (33, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(7, 1), (33, 1), (36, 1), (59, 1)] }, { coefficient := -1, powers := [(7, 1), (33, 1), (39, 1), (56, 1)] }, { coefficient := -1, powers := [(7, 1), (33, 1), (44, 1), (51, 1)] }, { coefficient := -1, powers := [(10, 1), (19, 1), (20, 1), (44, 1), (49, 1), (51, 1), (56, 1), (63, 1)] }, { coefficient := 1, powers := [(10, 1), (19, 1), (33, 1), (36, 1), (44, 1), (49, 1), (51, 1), (63, 1)] }, { coefficient := 1, powers := [(10, 1), (20, 1), (46, 1), (49, 1), (51, 1), (56, 1), (63, 1)] }, { coefficient := -1, powers := [(10, 1), (33, 1), (36, 1), (46, 1), (49, 1), (51, 1), (63, 1)] }, { coefficient := -1, powers := [(14, 1), (19, 1), (20, 1), (44, 1), (49, 1), (51, 1), (56, 1), (63, 1)] }, { coefficient := 1, powers := [(14, 1), (19, 1), (33, 1), (36, 1), (44, 1), (49, 1), (51, 1), (63, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1), (46, 1), (49, 1), (51, 1), (56, 1), (63, 1)] }, { coefficient := -1, powers := [(14, 1), (33, 1), (36, 1), (46, 1), (49, 1), (51, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(36, 1), (59, 1)] }, { coefficient := -1, powers := [(39, 1), (55, 1), (56, 1), (64, 1)] }, { coefficient := 1, powers := [(39, 1), (56, 1)] }, { coefficient := 1, powers := [(40, 1), (44, 1), (56, 1), (63, 1)] }, { coefficient := 1, powers := [(40, 1), (51, 1), (56, 1), (63, 1)] }, { coefficient := 1, powers := [(40, 1), (56, 2), (63, 1)] }, { coefficient := -1, powers := [(43, 1), (56, 1), (64, 1)] }, { coefficient := 1, powers := [(44, 1), (46, 1), (52, 1), (63, 1)] }, { coefficient := -1, powers := [(44, 1), (51, 1)] }, { coefficient := 1, powers := [(46, 1), (51, 1), (52, 1), (63, 1)] }, { coefficient := 1, powers := [(46, 1), (52, 1), (56, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (33, 1), (44, 1)] }, { coefficient := 1, powers := [(7, 1), (33, 1), (51, 1)] }, { coefficient := 1, powers := [(7, 1), (33, 1), (56, 1)] }, { coefficient := 1, powers := [(10, 1), (20, 1), (23, 1), (51, 1), (56, 1)] }, { coefficient := -1, powers := [(10, 1), (23, 1), (33, 1), (36, 1), (51, 1)] }, { coefficient := 1, powers := [(14, 1), (18, 1), (20, 1), (51, 1), (56, 1)] }, { coefficient := -1, powers := [(14, 1), (18, 1), (20, 1), (56, 1), (66, 1)] }, { coefficient := -1, powers := [(14, 1), (18, 1), (33, 1), (36, 1), (51, 1)] }, { coefficient := 1, powers := [(14, 1), (18, 1), (33, 1), (36, 1), (66, 1)] }, { coefficient := 2, powers := [(14, 1), (20, 1), (51, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1), (56, 1)] }, { coefficient := -1, powers := [(14, 1), (20, 1), (66, 1)] }, { coefficient := 1, powers := [(14, 1), (33, 1), (36, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (30, 1), (56, 1)] }, { coefficient := -1, powers := [(10, 1), (20, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (18, 1), (20, 1), (56, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (18, 1), (33, 1), (36, 1), (59, 1)] }, { coefficient := -1, powers := [(7, 1), (20, 1), (59, 1)] }, { coefficient := -1, powers := [(10, 1), (18, 1), (20, 1), (56, 2)] }, { coefficient := 1, powers := [(10, 1), (18, 1), (33, 1), (36, 1), (56, 1)] }, { coefficient := -1, powers := [(10, 1), (20, 1), (56, 1)] }, { coefficient := -1, powers := [(14, 1), (18, 1), (20, 1), (51, 1), (56, 1)] }, { coefficient := 1, powers := [(14, 1), (18, 1), (33, 1), (36, 1), (51, 1)] }, { coefficient := -1, powers := [(14, 1), (20, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (59, 1)] }, { coefficient := 1, powers := [(14, 1), (40, 1), (44, 1), (63, 1)] }, { coefficient := 1, powers := [(14, 1), (40, 1), (51, 1), (63, 1)] }, { coefficient := 1, powers := [(14, 1), (40, 1), (56, 1), (63, 1)] }, { coefficient := -1, powers := [(14, 1), (44, 1)] }]
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
    ¬ ∀ index : Fin 23,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component39.SelectedLeafB1_3_6_4.selectedHasNoCommonZero

end Krenn.Component39.SelectedLeafB1_3_6_4
