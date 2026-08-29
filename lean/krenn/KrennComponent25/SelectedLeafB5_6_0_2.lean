import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component25.SelectedLeafB5_6_0_2

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "cb184b4768b6a9ea5a323a7537b3c5c67d184b22a418a4d655d3fdfaa2fefd86"
def certificateSHA256 : String := "b0b5551d44308751329b570a9160dc9b58ac20f31d96385575b7dc514466b93f"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 24 → Fin 668 := ![
  14,
  142,
  162,
  239,
  292,
  300,
  312,
  317,
  388,
  405,
  406,
  435,
  440,
  450,
  475,
  579,
  616,
  628,
  655,
  661,
  663,
  664,
  665,
  667
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 24 → SparsePoly (Fin 66) := ![
  [{ coefficient := 1, powers := [(16, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (54, 1)] }, { coefficient := 1, powers := [(18, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (18, 1)] }, { coefficient := 1, powers := [(16, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (24, 1), (46, 1)] }, { coefficient := 1, powers := [(17, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1)] }, { coefficient := 1, powers := [(18, 1), (43, 1)] }, { coefficient := 1, powers := [(24, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (60, 1)] }, { coefficient := 1, powers := [(12, 1), (57, 1)] }, { coefficient := 1, powers := [(17, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (57, 1)] }, { coefficient := 1, powers := [(29, 1), (48, 1)] }, { coefficient := 1, powers := [(35, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1), (52, 1)] }, { coefficient := 1, powers := [(18, 1), (43, 1), (52, 1)] }, { coefficient := 1, powers := [(43, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (18, 1), (56, 1)] }, { coefficient := 1, powers := [(12, 1)] }, { coefficient := 1, powers := [(16, 1), (18, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (24, 1), (40, 1)] }, { coefficient := 1, powers := [(16, 1), (24, 1), (45, 1)] }, { coefficient := 1, powers := [(16, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (24, 1), (46, 1)] }, { coefficient := 1, powers := [(17, 1), (24, 1), (40, 1)] }, { coefficient := 1, powers := [(17, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1)] }, { coefficient := 1, powers := [(12, 1), (29, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (32, 1)] }, { coefficient := 1, powers := [(22, 1), (50, 1)] }, { coefficient := 1, powers := [(27, 1), (50, 1)] }, { coefficient := 1, powers := [(32, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (54, 1)] }, { coefficient := 1, powers := [(29, 1), (41, 1)] }, { coefficient := 1, powers := [(29, 1), (47, 1), (50, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (36, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (52, 1)] }, { coefficient := 1, powers := [(3, 1), (59, 1)] }, { coefficient := 1, powers := [(18, 1), (52, 1)] }, { coefficient := 1, powers := [(18, 1), (56, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (36, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (43, 1), (50, 1)] }, { coefficient := 1, powers := [(12, 1), (27, 1), (43, 1)] }, { coefficient := 1, powers := [(12, 1), (35, 1), (36, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (50, 1)] }, { coefficient := 1, powers := [(17, 1), (32, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (29, 1), (60, 1)] }, { coefficient := 1, powers := [(3, 1), (32, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (35, 1), (54, 1)] }, { coefficient := 1, powers := [(22, 1), (43, 1), (54, 1)] }, { coefficient := 1, powers := [(22, 1), (50, 1), (57, 1)] }, { coefficient := 1, powers := [(29, 1), (43, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (41, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (48, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (23, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (48, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(12, 1), (23, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1), (29, 1), (48, 1)] }, { coefficient := 1, powers := [(12, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(17, 1), (23, 1), (54, 1)] }, { coefficient := 1, powers := [(17, 1), (29, 1), (41, 1)] }, { coefficient := 1, powers := [(17, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(41, 1)] }],
  [{ coefficient := 1, powers := [(56, 1)] }],
  [{ coefficient := 1, powers := [(57, 1)] }],
  [{ coefficient := 1, powers := [(24, 1)] }],
  [{ coefficient := 1, powers := [(29, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 24 → SparsePoly (Fin 66) := ![
  [{ coefficient := -1, powers := [(22, 1), (48, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (35, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(35, 1), (36, 1), (38, 1), (53, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(27, 1), (38, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (38, 1), (50, 1), (52, 1), (59, 1)] }, { coefficient := -1, powers := [(5, 1), (22, 1), (52, 1), (54, 1), (59, 1)] }, { coefficient := -1, powers := [(12, 1), (27, 1), (38, 1), (52, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(23, 1)] }],
  [{ coefficient := 1, powers := [(12, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (50, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (22, 1), (54, 1), (59, 1)] }, { coefficient := 1, powers := [(12, 1), (27, 1), (38, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(35, 1), (36, 1), (38, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(22, 1), (38, 1), (60, 1)] }, { coefficient := -1, powers := [(27, 1), (38, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (32, 1), (38, 1), (59, 1)] }, { coefficient := -1, powers := [(23, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(48, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (38, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(17, 1)] }],
  [{ coefficient := 1, powers := [(38, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (35, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(38, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(8, 1), (35, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (18, 1), (35, 1), (54, 1)] }, { coefficient := -1, powers := [(12, 1), (18, 1), (35, 1), (36, 1), (38, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (41, 1)] }, { coefficient := 1, powers := [(3, 1), (5, 1), (32, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (22, 1), (50, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1)] }, { coefficient := -1, powers := [(12, 1), (23, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (43, 1), (50, 1), (52, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (22, 1), (43, 1), (52, 1), (54, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (16, 1), (32, 1), (38, 1), (46, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (17, 1), (32, 1), (38, 1), (40, 1), (59, 1)] }, { coefficient := 1, powers := [(12, 1), (27, 1), (38, 1), (43, 1), (52, 1), (59, 1)] }, { coefficient := 1, powers := [(12, 1), (27, 1), (38, 1), (46, 1), (59, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1), (38, 1), (40, 1), (60, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1), (38, 1), (45, 1), (60, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1), (46, 1), (54, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1), (38, 1), (40, 1), (60, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1), (38, 1), (45, 1), (60, 1)] }, { coefficient := 1, powers := [(16, 1), (35, 1), (36, 1), (38, 1), (53, 1), (59, 1)] }, { coefficient := 1, powers := [(17, 1), (23, 1), (40, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (5, 1), (59, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (43, 1), (50, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (60, 1)] }, { coefficient := -1, powers := [(12, 1), (48, 1)] }, { coefficient := -1, powers := [(17, 1), (47, 1), (50, 1)] }]
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
    ¬ ∀ index : Fin 24,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component25.SelectedLeafB5_6_0_2.selectedHasNoCommonZero

end Krenn.Component25.SelectedLeafB5_6_0_2
