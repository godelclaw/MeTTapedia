import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component62.SelectedLeafB4_6_3_6_3

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "6a1052af139ad0c021fe688cce9c34e91eb5cdcef158550b78aa4912126eaf00"
def certificateSHA256 : String := "8b9bc6dfe4669bd4383dbb402c1d06c1a54d9bb8b254ab7bda8290cccc3e3aa7"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 28 → Fin 673 := ![
  18,
  146,
  147,
  153,
  155,
  159,
  252,
  293,
  294,
  296,
  301,
  302,
  318,
  441,
  444,
  454,
  476,
  483,
  557,
  619,
  657,
  658,
  660,
  663,
  667,
  669,
  671,
  672
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 28 → SparsePoly (Fin 69) := ![
  [{ coefficient := 1, powers := [(22, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (23, 1)] }, { coefficient := 1, powers := [(16, 1), (18, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (24, 1)] }, { coefficient := 1, powers := [(16, 1), (18, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (18, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (46, 1)] }, { coefficient := 1, powers := [(17, 1), (19, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (52, 1)] }, { coefficient := 1, powers := [(27, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (23, 1), (46, 1)] }, { coefficient := 1, powers := [(17, 1), (19, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (41, 1)] }, { coefficient := 1, powers := [(18, 1), (41, 1)] }, { coefficient := 1, powers := [(23, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1)] }, { coefficient := 1, powers := [(19, 1), (41, 1)] }, { coefficient := 1, powers := [(23, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (53, 1)] }, { coefficient := 1, powers := [(18, 1), (53, 1)] }, { coefficient := 1, powers := [(24, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (46, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (53, 1)] }, { coefficient := 1, powers := [(8, 1), (30, 1)] }, { coefficient := 1, powers := [(12, 1), (27, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1), (50, 1)] }, { coefficient := 1, powers := [(19, 1), (41, 1), (50, 1)] }, { coefficient := 1, powers := [(46, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (59, 1)] }, { coefficient := 1, powers := [(12, 1), (46, 1)] }, { coefficient := 1, powers := [(17, 1), (19, 1), (51, 1)] }, { coefficient := 1, powers := [(17, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (59, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (44, 1)] }, { coefficient := 1, powers := [(12, 1), (56, 1)] }, { coefficient := 1, powers := [(17, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (53, 1)] }, { coefficient := 1, powers := [(27, 1), (39, 1)] }, { coefficient := 1, powers := [(27, 1), (45, 1), (48, 1)] }, { coefficient := 1, powers := [(30, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1), (53, 1)] }, { coefficient := 1, powers := [(24, 1), (44, 1), (48, 1)] }, { coefficient := 1, powers := [(41, 1), (53, 1)] }, { coefficient := 1, powers := [(48, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1), (51, 1)] }, { coefficient := 1, powers := [(19, 1), (41, 1), (51, 1)] }, { coefficient := 1, powers := [(39, 1), (41, 1)] }, { coefficient := 1, powers := [(46, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (41, 1), (52, 1)] }, { coefficient := 1, powers := [(22, 1), (56, 1)] }, { coefficient := 1, powers := [(27, 1), (46, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (36, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (45, 1), (52, 1)] }, { coefficient := 1, powers := [(5, 1), (27, 1), (58, 1)] }, { coefficient := 1, powers := [(8, 1), (22, 1), (58, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1), (52, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (36, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (46, 1), (53, 1)] }, { coefficient := 1, powers := [(5, 1), (27, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (53, 1)] }, { coefficient := 1, powers := [(8, 1), (22, 1), (59, 1)] }, { coefficient := 1, powers := [(8, 1), (30, 1), (46, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (39, 1)] }, { coefficient := 1, powers := [(12, 1), (22, 1), (56, 1)] }, { coefficient := 1, powers := [(12, 1), (27, 1), (46, 1)] }, { coefficient := 1, powers := [(12, 1), (33, 1), (36, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (53, 1)] }, { coefficient := 1, powers := [(17, 1), (27, 1), (39, 1)] }, { coefficient := 1, powers := [(17, 1), (30, 1), (36, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (60, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(39, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (65, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(27, 1)] }],
  [{ coefficient := 1, powers := [(58, 1), (67, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(59, 1), (68, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 28 → SparsePoly (Fin 69) := ![
  [{ coefficient := -1, powers := [(12, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (56, 1), (65, 1)] }, { coefficient := -1, powers := [(30, 1), (46, 1), (50, 1), (56, 1), (68, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (41, 1), (53, 1), (60, 1)] }, { coefficient := -1, powers := [(22, 1), (48, 1), (56, 1), (65, 1)] }, { coefficient := 1, powers := [(30, 1), (46, 1), (48, 1), (50, 1), (56, 1), (68, 1)] }],
  [{ coefficient := 1, powers := [(30, 1), (48, 1), (56, 1), (68, 1)] }],
  [{ coefficient := -2, powers := [(16, 1), (59, 1), (67, 1)] }],
  [{ coefficient := -1, powers := [(30, 1), (48, 1), (50, 1), (56, 1), (68, 1)] }, { coefficient := -1, powers := [(30, 1), (51, 1), (56, 1), (68, 1)] }],
  [{ coefficient := -1, powers := [(16, 1), (22, 1), (53, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (30, 1), (50, 1), (56, 1), (68, 1)] }, { coefficient := 1, powers := [(16, 1), (30, 1), (51, 1), (56, 1), (68, 1)] }],
  [{ coefficient := -1, powers := [(16, 1), (22, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(53, 1)] }],
  [{ coefficient := 1, powers := [(46, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (30, 1), (56, 1), (68, 1)] }],
  [{ coefficient := 1, powers := [(30, 1), (56, 1), (68, 1)] }],
  [{ coefficient := -1, powers := [(22, 1)] }],
  [{ coefficient := 1, powers := [(17, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (22, 1)] }],
  [{ coefficient := -1, powers := [(16, 1), (30, 1), (56, 1), (68, 1)] }],
  [{ coefficient := 1, powers := [(12, 1)] }],
  [{ coefficient := 2, powers := [(59, 1), (67, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(16, 1), (22, 1), (41, 1), (53, 1)] }],
  [{ coefficient := -2, powers := [(36, 1), (58, 1), (59, 1), (67, 1)] }, { coefficient := 1, powers := [(36, 1), (59, 1)] }, { coefficient := -2, powers := [(45, 1), (52, 1), (59, 1), (67, 1)] }, { coefficient := -1, powers := [(46, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (56, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1)] }, { coefficient := 1, powers := [(16, 1), (30, 1), (41, 1), (56, 1), (68, 1)] }, { coefficient := -1, powers := [(17, 1), (30, 1), (56, 1), (68, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (22, 1), (56, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1), (48, 1), (56, 1)] }],
  [{ coefficient := -2, powers := [(5, 1), (58, 1), (59, 1), (67, 1)] }, { coefficient := 1, powers := [(5, 1), (59, 1)] }, { coefficient := -1, powers := [(12, 1), (46, 1)] }, { coefficient := -1, powers := [(17, 1), (45, 1), (48, 1)] }],
  [{ coefficient := -2, powers := [(8, 1), (22, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (30, 1), (56, 1)] }]
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
    ¬ ∀ index : Fin 28,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component62.SelectedLeafB4_6_3_6_3.selectedHasNoCommonZero

end Krenn.Component62.SelectedLeafB4_6_3_6_3
