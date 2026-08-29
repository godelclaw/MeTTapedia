import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component39.SelectedLeafB1_2_6_1

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "f2fe7e8c667107082653a953822361dfc9160b4cb49f0721e461b6103ddfcbaa"
def certificateSHA256 : String := "23edb4361a1e53dc370bb7dfcb6e4cb46747c7e939fecadc658b08eac9b9334e"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 25 → Fin 673 := ![
  26,
  173,
  304,
  305,
  318,
  396,
  422,
  441,
  477,
  511,
  515,
  537,
  602,
  603,
  644,
  649,
  659,
  661,
  662,
  663,
  667,
  668,
  670,
  671,
  672
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 25 → SparsePoly (Fin 66) := ![
  [{ coefficient := 1, powers := [(20, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (23, 1)] }, { coefficient := 1, powers := [(14, 1), (18, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (44, 1)] }, { coefficient := 1, powers := [(4, 1), (33, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (51, 1)] }, { coefficient := 1, powers := [(7, 1), (30, 1)] }, { coefficient := 1, powers := [(10, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (53, 1)] }, { coefficient := 1, powers := [(28, 1), (39, 1)] }, { coefficient := 1, powers := [(28, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (23, 1), (39, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1), (44, 1)] }, { coefficient := 1, powers := [(16, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (51, 1)] }, { coefficient := 1, powers := [(16, 1), (21, 1), (51, 1)] }, { coefficient := 1, powers := [(16, 1), (21, 1), (56, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (39, 1)] }, { coefficient := 1, powers := [(27, 1), (44, 1)] }, { coefficient := 1, powers := [(27, 1), (51, 1)] }, { coefficient := 1, powers := [(27, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (39, 1), (55, 1)] }, { coefficient := 1, powers := [(1, 1), (43, 1)] }, { coefficient := 1, powers := [(4, 1), (30, 1), (55, 1)] }, { coefficient := 1, powers := [(10, 1), (20, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (23, 1), (59, 1)] }, { coefficient := 1, powers := [(10, 1), (23, 1), (44, 1)] }, { coefficient := 1, powers := [(14, 1), (23, 1), (39, 1)] }, { coefficient := 1, powers := [(14, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (28, 1), (59, 1)] }, { coefficient := 1, powers := [(10, 1), (28, 1), (44, 1)] }, { coefficient := 1, powers := [(14, 1), (27, 1), (53, 1)] }, { coefficient := 1, powers := [(14, 1), (28, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (18, 1), (59, 1)] }, { coefficient := 1, powers := [(10, 1), (18, 1), (56, 1)] }, { coefficient := 1, powers := [(10, 1)] }, { coefficient := 1, powers := [(14, 1), (18, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (59, 1)] }, { coefficient := 1, powers := [(10, 1), (44, 1)] }, { coefficient := 1, powers := [(10, 1), (56, 1)] }, { coefficient := 1, powers := [(14, 1), (39, 1)] }, { coefficient := 1, powers := [(14, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (51, 1)] }, { coefficient := 1, powers := [(20, 1), (56, 1)] }, { coefficient := 1, powers := [(25, 1), (39, 1)] }, { coefficient := 1, powers := [(25, 1), (44, 1)] }, { coefficient := 1, powers := [(30, 1), (36, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (36, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (44, 1), (51, 1)] }, { coefficient := 1, powers := [(39, 1)] }, { coefficient := 1, powers := [(44, 1)] }, { coefficient := 1, powers := [(51, 1)] }, { coefficient := 1, powers := [(56, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (36, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (44, 1), (51, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1), (39, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1), (44, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1), (51, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (36, 1), (59, 1)] }, { coefficient := 1, powers := [(1, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(1, 1), (44, 1), (51, 1)] }, { coefficient := 1, powers := [(4, 1), (25, 1), (59, 1)] }, { coefficient := 1, powers := [(4, 1), (30, 1), (56, 1)] }, { coefficient := 1, powers := [(4, 1), (33, 1), (51, 1)] }, { coefficient := 1, powers := [(7, 1), (20, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (30, 1), (44, 1)] }, { coefficient := 1, powers := [(7, 1), (33, 1), (39, 1)] }, { coefficient := 1, powers := [(10, 1), (20, 1), (56, 1)] }, { coefficient := 1, powers := [(10, 1), (25, 1), (44, 1)] }, { coefficient := 1, powers := [(10, 1), (33, 1), (36, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1), (51, 1)] }, { coefficient := 1, powers := [(14, 1), (25, 1), (39, 1)] }, { coefficient := 1, powers := [(14, 1), (30, 1), (36, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1)] }],
  [{ coefficient := 1, powers := [(1, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (61, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(55, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(56, 1), (64, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(23, 1)] }],
  [{ coefficient := 1, powers := [(25, 1)] }],
  [{ coefficient := 1, powers := [(28, 1), (65, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 25 → SparsePoly (Fin 66) := ![
  [{ coefficient := -1, powers := [(10, 1), (27, 1), (56, 1), (64, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(20, 1), (51, 2), (56, 1), (64, 1)] }, { coefficient := -2, powers := [(33, 1), (36, 1), (51, 1), (56, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(51, 1), (56, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(44, 1), (56, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (20, 1), (56, 1), (64, 1), (65, 1)] }, { coefficient := -1, powers := [(14, 1), (18, 1), (20, 1), (51, 1), (56, 1), (64, 1), (65, 1)] }, { coefficient := -2, powers := [(14, 1), (18, 1), (33, 1), (36, 1), (56, 1), (64, 1), (65, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1), (56, 1), (64, 1), (65, 1)] }, { coefficient := -1, powers := [(14, 1), (33, 1), (36, 1), (64, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (21, 1), (33, 1), (44, 1), (51, 1), (61, 1), (64, 1)] }, { coefficient := 1, powers := [(7, 1), (21, 1), (33, 1), (44, 1), (56, 1), (61, 1), (64, 1)] }, { coefficient := 1, powers := [(7, 1), (27, 1), (33, 1), (44, 1), (61, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (33, 1), (44, 1), (61, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (16, 1), (33, 1), (61, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(56, 2), (63, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(18, 1), (20, 1), (51, 1), (56, 2), (64, 1)] }, { coefficient := -2, powers := [(18, 1), (33, 1), (36, 1), (56, 2), (64, 1)] }, { coefficient := -1, powers := [(20, 1), (51, 1), (56, 1), (64, 1)] }, { coefficient := -2, powers := [(33, 1), (36, 1), (56, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (20, 1), (51, 1), (56, 1), (64, 1), (65, 1)] }, { coefficient := 2, powers := [(18, 1), (33, 1), (36, 1), (56, 1), (64, 1), (65, 1)] }, { coefficient := -1, powers := [(20, 1), (56, 1), (64, 1), (65, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1), (64, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (51, 1), (56, 1), (64, 1)] }, { coefficient := 2, powers := [(33, 1), (36, 1), (56, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(18, 1), (20, 1), (28, 1), (51, 1), (56, 1), (64, 1), (65, 1)] }, { coefficient := -2, powers := [(18, 1), (28, 1), (33, 1), (36, 1), (56, 1), (64, 1), (65, 1)] }, { coefficient := 1, powers := [(20, 1), (28, 1), (56, 1), (64, 1), (65, 1)] }, { coefficient := -1, powers := [(28, 1), (33, 1), (36, 1), (64, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (56, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(10, 1), (20, 1), (56, 1), (64, 1)] }, { coefficient := 1, powers := [(14, 1), (18, 1), (20, 1), (51, 1), (56, 1), (64, 1)] }, { coefficient := 2, powers := [(14, 1), (18, 1), (33, 1), (36, 1), (56, 1), (64, 1)] }, { coefficient := -1, powers := [(14, 1), (20, 1), (56, 1), (64, 1)] }, { coefficient := 1, powers := [(14, 1), (33, 1), (36, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (33, 1), (61, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(56, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (20, 1), (36, 1), (56, 1), (59, 1), (64, 1)] }, { coefficient := 1, powers := [(10, 1), (20, 1), (39, 1), (56, 2), (64, 1)] }, { coefficient := 1, powers := [(10, 1), (20, 1), (44, 1), (51, 1), (56, 1), (64, 1)] }, { coefficient := -1, powers := [(14, 1), (18, 1), (20, 1), (36, 1), (51, 1), (56, 1), (59, 1), (64, 1)] }, { coefficient := -1, powers := [(14, 1), (18, 1), (20, 1), (39, 1), (51, 1), (56, 2), (64, 1)] }, { coefficient := -1, powers := [(14, 1), (18, 1), (20, 1), (44, 1), (51, 2), (56, 1), (64, 1)] }, { coefficient := -2, powers := [(14, 1), (18, 1), (33, 1), (36, 2), (56, 1), (59, 1), (64, 1)] }, { coefficient := -2, powers := [(14, 1), (18, 1), (33, 1), (36, 1), (39, 1), (56, 2), (64, 1)] }, { coefficient := -2, powers := [(14, 1), (18, 1), (33, 1), (36, 1), (44, 1), (51, 1), (56, 1), (64, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1), (36, 1), (56, 1), (59, 1), (64, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1), (39, 1), (56, 2), (64, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1), (44, 1), (51, 1), (56, 1), (64, 1)] }, { coefficient := -1, powers := [(14, 1), (33, 1), (36, 2), (59, 1), (64, 1)] }, { coefficient := -1, powers := [(14, 1), (33, 1), (36, 1), (39, 1), (56, 1), (64, 1)] }, { coefficient := -1, powers := [(14, 1), (33, 1), (36, 1), (44, 1), (51, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(36, 1), (56, 1), (59, 1), (64, 1)] }, { coefficient := -1, powers := [(39, 1), (55, 1), (56, 2), (63, 1), (64, 1)] }, { coefficient := 1, powers := [(39, 1), (56, 2), (64, 1)] }, { coefficient := -1, powers := [(43, 1), (56, 2), (63, 1), (64, 1)] }, { coefficient := -1, powers := [(44, 1), (51, 1), (56, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (33, 1), (36, 1), (59, 1), (64, 1)] }, { coefficient := -1, powers := [(7, 1), (33, 1), (39, 1), (56, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (30, 1), (56, 2), (64, 1)] }, { coefficient := -1, powers := [(10, 1), (20, 1), (56, 2), (64, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(4, 1), (18, 1), (20, 1), (51, 1), (56, 2), (59, 1), (64, 1)] }, { coefficient := 2, powers := [(4, 1), (18, 1), (33, 1), (36, 1), (56, 2), (59, 1), (64, 1)] }, { coefficient := 1, powers := [(4, 1), (20, 1), (51, 1), (56, 1), (59, 1), (64, 1)] }, { coefficient := 2, powers := [(4, 1), (33, 1), (36, 1), (56, 1), (59, 1), (64, 1)] }, { coefficient := -1, powers := [(7, 1), (16, 1), (21, 1), (33, 1), (39, 1), (44, 1), (51, 1), (61, 1), (64, 1)] }, { coefficient := -1, powers := [(7, 1), (16, 1), (21, 1), (33, 1), (39, 1), (44, 1), (56, 1), (61, 1), (64, 1)] }, { coefficient := -1, powers := [(7, 1), (16, 1), (21, 1), (33, 1), (44, 2), (51, 1), (61, 1), (64, 1)] }, { coefficient := -1, powers := [(7, 1), (16, 1), (21, 1), (33, 1), (44, 2), (56, 1), (61, 1), (64, 1)] }, { coefficient := -1, powers := [(7, 1), (16, 1), (27, 1), (33, 1), (39, 1), (44, 1), (61, 1), (64, 1)] }, { coefficient := -1, powers := [(7, 1), (16, 1), (27, 1), (33, 1), (44, 2), (61, 1), (64, 1)] }, { coefficient := 1, powers := [(10, 1), (18, 1), (20, 1), (44, 1), (51, 1), (56, 2), (64, 1)] }, { coefficient := 2, powers := [(10, 1), (18, 1), (33, 1), (36, 1), (44, 1), (56, 2), (64, 1)] }, { coefficient := 1, powers := [(10, 1), (20, 1), (44, 1), (51, 1), (56, 1), (64, 1)] }, { coefficient := 1, powers := [(10, 1), (20, 1), (51, 2), (56, 1), (64, 1)] }, { coefficient := 2, powers := [(10, 1), (33, 1), (36, 1), (44, 1), (56, 1), (64, 1)] }, { coefficient := 2, powers := [(10, 1), (33, 1), (36, 1), (51, 1), (56, 1), (64, 1)] }, { coefficient := 1, powers := [(14, 1), (18, 1), (20, 1), (39, 1), (51, 1), (56, 2), (64, 1)] }, { coefficient := 2, powers := [(14, 1), (18, 1), (33, 1), (36, 1), (39, 1), (56, 2), (64, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1), (39, 1), (51, 1), (56, 1), (64, 1)] }, { coefficient := 2, powers := [(14, 1), (33, 1), (36, 1), (39, 1), (56, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (56, 1), (59, 1), (64, 1)] }, { coefficient := -1, powers := [(14, 1), (44, 1), (56, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (18, 1), (20, 1), (51, 1), (56, 1), (59, 1), (64, 1)] }, { coefficient := 2, powers := [(7, 1), (18, 1), (33, 1), (36, 1), (56, 1), (59, 1), (64, 1)] }, { coefficient := -1, powers := [(7, 1), (20, 1), (56, 1), (59, 1), (64, 1)] }, { coefficient := 1, powers := [(7, 1), (33, 1), (36, 1), (59, 1), (64, 1)] }, { coefficient := 1, powers := [(10, 1), (18, 1), (20, 1), (51, 1), (56, 2), (64, 1)] }, { coefficient := 2, powers := [(10, 1), (18, 1), (33, 1), (36, 1), (56, 2), (64, 1)] }, { coefficient := -1, powers := [(10, 1), (20, 1), (39, 1), (56, 1), (64, 1)] }, { coefficient := -1, powers := [(10, 1), (20, 1), (44, 1), (56, 1), (64, 1)] }, { coefficient := -1, powers := [(10, 1), (20, 1), (56, 2), (64, 1)] }, { coefficient := 1, powers := [(10, 1), (33, 1), (36, 1), (56, 1), (64, 1)] }, { coefficient := 1, powers := [(14, 1), (18, 1), (20, 1), (39, 1), (51, 1), (56, 1), (64, 1)] }, { coefficient := 1, powers := [(14, 1), (18, 1), (20, 1), (44, 1), (51, 1), (56, 1), (64, 1)] }, { coefficient := 1, powers := [(14, 1), (18, 1), (20, 1), (51, 2), (56, 1), (64, 1)] }, { coefficient := 2, powers := [(14, 1), (18, 1), (33, 1), (36, 1), (39, 1), (56, 1), (64, 1)] }, { coefficient := 2, powers := [(14, 1), (18, 1), (33, 1), (36, 1), (44, 1), (56, 1), (64, 1)] }, { coefficient := 2, powers := [(14, 1), (18, 1), (33, 1), (36, 1), (51, 1), (56, 1), (64, 1)] }, { coefficient := -1, powers := [(14, 1), (20, 1), (39, 1), (56, 1), (64, 1)] }, { coefficient := -1, powers := [(14, 1), (20, 1), (44, 1), (56, 1), (64, 1)] }, { coefficient := -1, powers := [(14, 1), (20, 1), (51, 1), (56, 1), (64, 1)] }, { coefficient := 1, powers := [(14, 1), (33, 1), (36, 1), (39, 1), (64, 1)] }, { coefficient := 1, powers := [(14, 1), (33, 1), (36, 1), (44, 1), (64, 1)] }, { coefficient := 1, powers := [(14, 1), (33, 1), (36, 1), (51, 1), (64, 1)] }]
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
    (values : Fin 66 → R) :
    ¬ ∀ index : Fin 25,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component39.SelectedLeafB1_2_6_1.selectedHasNoCommonZero

end Krenn.Component39.SelectedLeafB1_2_6_1
