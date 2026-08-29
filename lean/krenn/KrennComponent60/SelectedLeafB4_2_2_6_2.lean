import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component60.SelectedLeafB4_2_2_6_2

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "7b9f9b3f6a3e4d420c731855b6a33b2dd2c06942f9e3dccc3b2993e40a9a750c"
def certificateSHA256 : String := "e477ebb1bfeaeddb1672e3c2bf547fe67aab127c2850f5eda809aaca06c4a728"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 18 → Fin 671 := ![
  22,
  168,
  177,
  178,
  301,
  302,
  310,
  436,
  443,
  549,
  556,
  655,
  658,
  661,
  663,
  664,
  667,
  670
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 18 → SparsePoly (Fin 67) := ![
  [{ coefficient := 1, powers := [(24, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (46, 1)] }, { coefficient := 1, powers := [(19, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (51, 1)] }, { coefficient := 1, powers := [(24, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (53, 1)] }, { coefficient := 1, powers := [(29, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (48, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1)] }, { coefficient := 1, powers := [(12, 1), (29, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (46, 1)] }, { coefficient := 1, powers := [(19, 1), (40, 1)] }, { coefficient := 1, powers := [(19, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (60, 1)] }, { coefficient := 1, powers := [(12, 1), (26, 1), (46, 1)] }, { coefficient := 1, powers := [(12, 1), (57, 1)] }, { coefficient := 1, powers := [(19, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (54, 1)] }, { coefficient := 1, powers := [(29, 1), (41, 1)] }, { coefficient := 1, powers := [(29, 1), (47, 1), (50, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (26, 1), (46, 1)] }, { coefficient := 1, powers := [(18, 1), (57, 1)] }, { coefficient := 1, powers := [(19, 1), (26, 1), (40, 1)] }, { coefficient := 1, powers := [(19, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (43, 1), (53, 1)] }, { coefficient := 1, powers := [(24, 1), (57, 1)] }, { coefficient := 1, powers := [(29, 1), (48, 1)] }, { coefficient := 1, powers := [(35, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (41, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (48, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (48, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1), (29, 1), (48, 1)] }, { coefficient := 1, powers := [(12, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (54, 1)] }, { coefficient := 1, powers := [(19, 1), (29, 1), (41, 1)] }, { coefficient := 1, powers := [(19, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(41, 1)] }],
  [{ coefficient := 1, powers := [(56, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(57, 1)] }],
  [{ coefficient := 1, powers := [(29, 1)] }],
  [{ coefficient := 1, powers := [(60, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 18 → SparsePoly (Fin 67) := ![
  [{ coefficient := -1, powers := [(12, 1), (53, 1), (56, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(24, 1), (26, 1), (51, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(19, 1), (54, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (52, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(54, 1), (56, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(48, 1), (56, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (26, 1), (52, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (51, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (56, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(24, 1), (52, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (56, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(56, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(38, 1), (56, 1), (60, 1), (63, 1)] }, { coefficient := -1, powers := [(48, 1), (54, 1), (56, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (56, 1), (57, 1), (63, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (56, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(5, 1), (32, 1), (56, 1), (63, 1)] }, { coefficient := -1, powers := [(12, 1), (24, 1), (51, 1), (63, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (52, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (56, 1), (60, 1), (63, 1)] }, { coefficient := -1, powers := [(12, 1), (48, 1), (56, 1), (63, 1)] }, { coefficient := -1, powers := [(19, 1), (47, 1), (50, 1), (56, 1), (63, 1)] }, { coefficient := -1, powers := [(19, 1), (47, 1), (52, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (24, 1), (51, 1), (63, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (56, 1), (63, 1)] }]
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

#print axioms Krenn.Component60.SelectedLeafB4_2_2_6_2.selectedHasNoCommonZero

end Krenn.Component60.SelectedLeafB4_2_2_6_2
