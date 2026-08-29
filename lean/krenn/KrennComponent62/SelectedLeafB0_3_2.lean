import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component62.SelectedLeafB0_3_2

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "8584a5cc66b126e63ec650767ff18bab3f1f977be0d42ff841f2942a04e59daa"
def certificateSHA256 : String := "d03a55ec7eb9cf8b3642e36661d5e5d5016789e154d4a3446b11b3457968b8b1"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 37 → Fin 667 := ![
  18,
  21,
  54,
  68,
  137,
  147,
  149,
  150,
  154,
  187,
  192,
  223,
  224,
  252,
  294,
  296,
  301,
  302,
  311,
  315,
  316,
  318,
  408,
  441,
  444,
  454,
  470,
  480,
  557,
  588,
  610,
  657,
  658,
  660,
  662,
  663,
  666
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 37 → SparsePoly (Fin 63) := ![
  [{ coefficient := 1, powers := [(22, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (33, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (30, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (52, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (24, 1)] }, { coefficient := 1, powers := [(16, 1), (18, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (41, 1)] }, { coefficient := 1, powers := [(17, 1), (18, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (44, 1)] }, { coefficient := 1, powers := [(17, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (41, 1)] }, { coefficient := 1, powers := [(17, 1), (18, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (33, 1), (52, 1)] }, { coefficient := 1, powers := [(27, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (30, 1), (45, 1)] }, { coefficient := 1, powers := [(22, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (23, 1), (43, 1)] }, { coefficient := 1, powers := [(16, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (23, 1), (44, 1)] }, { coefficient := 1, powers := [(17, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (23, 1), (46, 1)] }, { coefficient := 1, powers := [(17, 1), (19, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1)] }, { coefficient := 1, powers := [(19, 1), (41, 1)] }, { coefficient := 1, powers := [(23, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (53, 1)] }, { coefficient := 1, powers := [(18, 1), (53, 1)] }, { coefficient := 1, powers := [(24, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (46, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (53, 1)] }, { coefficient := 1, powers := [(8, 1), (30, 1)] }, { coefficient := 1, powers := [(12, 1), (27, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (44, 1)] }, { coefficient := 1, powers := [(17, 1), (38, 1)] }, { coefficient := 1, powers := [(17, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1), (48, 1)] }, { coefficient := 1, powers := [(23, 1), (43, 1), (48, 1)] }, { coefficient := 1, powers := [(48, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1), (53, 1)] }, { coefficient := 1, powers := [(24, 1), (43, 1), (48, 1)] }, { coefficient := 1, powers := [(53, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1), (50, 1)] }, { coefficient := 1, powers := [(19, 1), (41, 1), (50, 1)] }, { coefficient := 1, powers := [(46, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (23, 1), (44, 1)] }, { coefficient := 1, powers := [(17, 1), (23, 1), (38, 1)] }, { coefficient := 1, powers := [(17, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (59, 1)] }, { coefficient := 1, powers := [(12, 1), (46, 1)] }, { coefficient := 1, powers := [(17, 1), (19, 1), (51, 1)] }, { coefficient := 1, powers := [(17, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (59, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (44, 1)] }, { coefficient := 1, powers := [(12, 1), (56, 1)] }, { coefficient := 1, powers := [(17, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (53, 1)] }, { coefficient := 1, powers := [(27, 1), (39, 1)] }, { coefficient := 1, powers := [(27, 1), (45, 1), (48, 1)] }, { coefficient := 1, powers := [(30, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1), (51, 1)] }, { coefficient := 1, powers := [(43, 1), (48, 1)] }, { coefficient := 1, powers := [(48, 1), (55, 1)] }, { coefficient := 1, powers := [(51, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1), (50, 1)] }, { coefficient := 1, powers := [(19, 1), (50, 1)] }, { coefficient := 1, powers := [(19, 1), (55, 1)] }, { coefficient := 1, powers := [(45, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (41, 1), (52, 1)] }, { coefficient := 1, powers := [(22, 1), (56, 1)] }, { coefficient := 1, powers := [(27, 1), (46, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (38, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1), (44, 1)] }, { coefficient := 1, powers := [(17, 1), (27, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (39, 1), (55, 1)] }, { coefficient := 1, powers := [(0, 1), (45, 1), (51, 1)] }, { coefficient := 1, powers := [(19, 1), (48, 1), (55, 1)] }, { coefficient := 1, powers := [(19, 1), (51, 1)] }, { coefficient := 1, powers := [(39, 1)] }, { coefficient := 1, powers := [(45, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (36, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (46, 1), (53, 1)] }, { coefficient := 1, powers := [(5, 1), (27, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (53, 1)] }, { coefficient := 1, powers := [(8, 1), (22, 1), (59, 1)] }, { coefficient := 1, powers := [(8, 1), (30, 1), (46, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (39, 1)] }, { coefficient := 1, powers := [(12, 1), (22, 1), (56, 1)] }, { coefficient := 1, powers := [(12, 1), (27, 1), (46, 1)] }, { coefficient := 1, powers := [(12, 1), (33, 1), (36, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (53, 1)] }, { coefficient := 1, powers := [(17, 1), (27, 1), (39, 1)] }, { coefficient := 1, powers := [(17, 1), (30, 1), (36, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1)] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(38, 1), (60, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(39, 1), (61, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(56, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 37 → SparsePoly (Fin 63) := ![
  [{ coefficient := -1, powers := [(12, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(17, 1), (19, 1), (39, 1), (43, 1), (61, 1)] }, { coefficient := -1, powers := [(17, 1), (23, 1), (39, 1), (43, 1), (45, 1), (61, 1)] }, { coefficient := -1, powers := [(17, 1), (45, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (19, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(17, 1), (24, 1), (45, 1)] }],
  [{ coefficient := -1, powers := [(39, 1), (44, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(22, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (27, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (23, 1), (27, 1), (50, 1)] }],
  [{ coefficient := -1, powers := [(19, 1), (27, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (19, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (24, 1), (43, 1)] }],
  [{ coefficient := -1, powers := [(22, 1), (24, 1), (44, 1)] }],
  [{ coefficient := -1, powers := [(19, 1), (27, 1), (50, 1)] }, { coefficient := 1, powers := [(22, 1), (24, 1), (43, 1)] }],
  [{ coefficient := -1, powers := [(27, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (27, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (22, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(53, 1)] }],
  [{ coefficient := 1, powers := [(46, 1)] }],
  [{ coefficient := -1, powers := [(19, 1), (23, 1), (27, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (27, 1), (39, 1), (45, 1), (61, 1)] }],
  [{ coefficient := -2, powers := [(17, 1), (22, 1)] }],
  [{ coefficient := -2, powers := [(12, 1), (27, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (27, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(27, 1)] }],
  [{ coefficient := 1, powers := [(22, 1)] }],
  [{ coefficient := 1, powers := [(17, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (19, 1), (27, 1), (39, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (27, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(12, 1)] }],
  [{ coefficient := 1, powers := [(39, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(17, 1), (27, 1), (39, 1), (61, 1)] }, { coefficient := -1, powers := [(17, 1), (27, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := 2, powers := [(12, 1), (27, 1), (46, 1), (50, 1)] }, { coefficient := -1, powers := [(16, 1), (22, 1), (44, 1), (53, 1)] }, { coefficient := -1, powers := [(16, 1), (27, 1), (46, 1), (51, 1)] }, { coefficient := -1, powers := [(17, 1), (19, 1), (27, 1), (39, 1), (43, 1), (51, 1), (61, 1)] }, { coefficient := 2, powers := [(17, 1), (22, 1), (43, 1), (53, 1)] }, { coefficient := 1, powers := [(17, 1), (27, 1), (39, 2), (55, 1), (61, 1)] }, { coefficient := -1, powers := [(17, 1), (27, 1), (39, 1), (43, 1), (45, 1), (48, 1), (61, 1)] }, { coefficient := 1, powers := [(17, 1), (27, 1), (39, 1), (45, 1), (51, 1), (61, 1)] }, { coefficient := 1, powers := [(17, 1), (27, 1), (39, 1), (55, 1)] }, { coefficient := -1, powers := [(17, 1), (27, 1), (45, 1), (48, 1), (50, 1)] }, { coefficient := 1, powers := [(17, 1), (27, 1), (45, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(36, 1), (59, 1)] }, { coefficient := -1, powers := [(38, 1), (39, 1), (56, 1), (60, 1)] }, { coefficient := 1, powers := [(39, 1), (56, 1)] }, { coefficient := -1, powers := [(46, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (33, 1), (39, 1)] }, { coefficient := -1, powers := [(17, 1), (27, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (27, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (30, 1)] }, { coefficient := -1, powers := [(12, 1), (22, 1)] }]
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
    (values : Fin 63 → R) :
    ¬ ∀ index : Fin 37,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component62.SelectedLeafB0_3_2.selectedHasNoCommonZero

end Krenn.Component62.SelectedLeafB0_3_2
