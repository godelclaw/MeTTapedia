import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component13.SelectedLeafB6_5

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "309ce8c81ebdafb2ab06f2526b37bf8a7f8a56ad9cf44802547ab9db939ce5f1"
def certificateSHA256 : String := "4d4ea521c2f9eccefda599d9f69e240df24b224d91cbaf058c2e84f2478c166b"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 28 → Fin 611 := ![
  0,
  12,
  17,
  19,
  25,
  55,
  170,
  188,
  189,
  284,
  325,
  360,
  361,
  371,
  376,
  389,
  405,
  451,
  480,
  483,
  548,
  549,
  603,
  604,
  607,
  608,
  609,
  610
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 28 → SparsePoly (Fin 62) := ![
  [{ coefficient := 1, powers := [(4, 1), (33, 1)] }],
  [{ coefficient := 1, powers := [(15, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(33, 1), (35, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (33, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (43, 1)] }, { coefficient := 1, powers := [(12, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (38, 1)] }, { coefficient := 1, powers := [(27, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(38, 1), (41, 1)] }, { coefficient := 1, powers := [(41, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (18, 1), (53, 1)] }, { coefficient := 1, powers := [(12, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (23, 1), (38, 1)] }, { coefficient := 1, powers := [(17, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1), (45, 1)] }, { coefficient := 1, powers := [(17, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1), (54, 1)] }, { coefficient := 1, powers := [(17, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (38, 1), (54, 1)] }, { coefficient := 1, powers := [(41, 1), (50, 1)] }, { coefficient := 1, powers := [(54, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (41, 1), (49, 1)] }, { coefficient := 1, powers := [(18, 1), (41, 1), (49, 1)] }, { coefficient := 1, powers := [(41, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (39, 1), (53, 1)] }, { coefficient := 1, powers := [(7, 1), (32, 1), (39, 1)] }, { coefficient := 1, powers := [(15, 1), (25, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (37, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (37, 1)] }, { coefficient := 1, powers := [(17, 1), (27, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (20, 1), (53, 1)] }, { coefficient := 1, powers := [(12, 1), (25, 1), (43, 1)] }, { coefficient := 1, powers := [(12, 1), (32, 1), (35, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (45, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1)] }, { coefficient := 1, powers := [(16, 1), (26, 1), (45, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (51, 1)] }, { coefficient := 1, powers := [(8, 1), (30, 1)] }, { coefficient := 1, powers := [(12, 1), (27, 1)] }, { coefficient := 1, powers := [(16, 1), (21, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (56, 1)] }, { coefficient := 1, powers := [(7, 1), (56, 1)] }, { coefficient := 1, powers := [(11, 1), (43, 1)] }, { coefficient := 1, powers := [(11, 1), (53, 1)] }, { coefficient := 1, powers := [(15, 1), (38, 1)] }, { coefficient := 1, powers := [(15, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (49, 1)] }, { coefficient := 1, powers := [(20, 1), (53, 1)] }, { coefficient := 1, powers := [(25, 1), (38, 1)] }, { coefficient := 1, powers := [(25, 1), (43, 1)] }, { coefficient := 1, powers := [(29, 1), (35, 1)] }, { coefficient := 1, powers := [(32, 1), (35, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (35, 1), (56, 1)] }, { coefficient := 1, powers := [(1, 1), (38, 1), (53, 1)] }, { coefficient := 1, powers := [(1, 1), (43, 1), (49, 1)] }, { coefficient := 1, powers := [(4, 1), (25, 1), (56, 1)] }, { coefficient := 1, powers := [(4, 1), (29, 1), (53, 1)] }, { coefficient := 1, powers := [(4, 1), (32, 1), (49, 1)] }, { coefficient := 1, powers := [(7, 1), (20, 1), (56, 1)] }, { coefficient := 1, powers := [(7, 1), (29, 1), (43, 1)] }, { coefficient := 1, powers := [(7, 1), (32, 1), (38, 1)] }, { coefficient := 1, powers := [(11, 1), (20, 1), (53, 1)] }, { coefficient := 1, powers := [(11, 1), (25, 1), (43, 1)] }, { coefficient := 1, powers := [(11, 1), (32, 1), (35, 1)] }, { coefficient := 1, powers := [(15, 1), (20, 1), (49, 1)] }, { coefficient := 1, powers := [(15, 1), (25, 1), (38, 1)] }, { coefficient := 1, powers := [(15, 1), (29, 1), (35, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (36, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (39, 1), (54, 1)] }, { coefficient := 1, powers := [(2, 1), (45, 1), (51, 1)] }, { coefficient := 1, powers := [(5, 1), (27, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (51, 1)] }, { coefficient := 1, powers := [(8, 1), (22, 1), (57, 1)] }, { coefficient := 1, powers := [(8, 1), (30, 1), (45, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (39, 1)] }, { coefficient := 1, powers := [(12, 1), (22, 1), (54, 1)] }, { coefficient := 1, powers := [(12, 1), (27, 1), (45, 1)] }, { coefficient := 1, powers := [(12, 1), (33, 1), (36, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (51, 1)] }, { coefficient := 1, powers := [(17, 1), (27, 1), (39, 1)] }, { coefficient := 1, powers := [(17, 1), (30, 1), (36, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(37, 1), (60, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(38, 1)] }],
  [{ coefficient := 1, powers := [(39, 1), (61, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 28 → SparsePoly (Fin 62) := ![
  [{ coefficient := 1, powers := [(12, 1), (29, 1), (36, 1), (53, 1)] }, { coefficient := 1, powers := [(12, 1), (32, 1), (36, 1), (49, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (20, 1), (33, 1), (36, 1), (53, 1), (61, 1)] }, { coefficient := -1, powers := [(12, 1), (25, 1), (33, 1), (36, 1), (43, 1), (61, 1)] }, { coefficient := -1, powers := [(12, 1), (32, 1), (33, 1), (35, 1), (36, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(26, 1), (51, 1)] }],
  [{ coefficient := -1, powers := [(21, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (12, 1), (36, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (20, 1), (36, 1), (56, 1), (60, 1)] }, { coefficient := -1, powers := [(12, 1), (25, 1), (36, 1), (56, 1), (60, 1)] }, { coefficient := -1, powers := [(12, 1), (29, 1), (36, 1), (53, 1), (60, 1)] }, { coefficient := 1, powers := [(12, 1), (32, 1), (36, 1), (49, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (33, 1), (36, 1), (49, 1)] }, { coefficient := 1, powers := [(7, 1), (29, 1), (33, 1), (36, 1)] }, { coefficient := -1, powers := [(11, 1), (25, 1), (33, 1), (36, 1)] }, { coefficient := 1, powers := [(18, 1), (27, 1), (45, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (18, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (5, 1), (30, 1), (50, 1)] }, { coefficient := 1, powers := [(5, 1), (18, 1), (30, 1), (50, 1)] }],
  [{ coefficient := -1, powers := [(27, 1), (45, 1)] }],
  [{ coefficient := -1, powers := [(22, 1), (51, 1)] }, { coefficient := -1, powers := [(27, 1), (37, 1), (39, 1), (60, 1)] }, { coefficient := 1, powers := [(30, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(27, 1)] }],
  [{ coefficient := 1, powers := [(22, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (30, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (30, 1), (50, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (33, 1), (36, 1), (49, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(39, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (33, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(51, 1)] }],
  [{ coefficient := 1, powers := [(45, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (25, 1), (33, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (15, 1), (33, 1), (36, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (33, 1), (36, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(36, 1), (57, 1)] }, { coefficient := -1, powers := [(37, 1), (39, 1), (54, 1), (60, 1)] }, { coefficient := 1, powers := [(39, 1), (54, 1)] }, { coefficient := -1, powers := [(45, 1), (51, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (12, 1), (20, 1), (33, 1), (36, 1), (56, 1)] }, { coefficient := 1, powers := [(7, 1), (12, 1), (25, 1), (33, 1), (36, 1), (56, 1)] }, { coefficient := 1, powers := [(7, 1), (12, 1), (29, 1), (33, 1), (36, 1), (53, 1)] }, { coefficient := -1, powers := [(7, 1), (12, 1), (32, 1), (33, 1), (36, 1), (49, 1)] }, { coefficient := -1, powers := [(8, 1), (33, 1), (39, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (5, 1), (30, 1), (41, 1), (50, 1)] }, { coefficient := -1, powers := [(0, 1), (5, 1), (30, 1), (54, 1)] }, { coefficient := 1, powers := [(1, 1), (12, 1), (33, 1), (36, 1), (53, 1)] }, { coefficient := -1, powers := [(5, 1), (18, 1), (30, 1), (41, 1), (50, 1)] }, { coefficient := 1, powers := [(7, 1), (12, 1), (32, 1), (33, 1), (36, 1)] }, { coefficient := -1, powers := [(12, 1), (15, 1), (25, 1), (33, 1), (36, 1)] }, { coefficient := 1, powers := [(12, 1), (18, 1), (27, 1), (45, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (23, 1), (51, 1)] }, { coefficient := 1, powers := [(17, 1), (23, 1), (27, 1), (37, 1), (39, 1), (60, 1)] }, { coefficient := -1, powers := [(17, 1), (23, 1), (30, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (12, 1), (33, 1), (36, 1), (49, 1), (53, 1)] }, { coefficient := 1, powers := [(7, 1), (12, 1), (32, 1), (33, 1), (36, 1), (49, 1)] }, { coefficient := 1, powers := [(12, 1), (15, 1), (20, 1), (33, 1), (36, 1), (53, 1)] }, { coefficient := 1, powers := [(12, 1), (15, 1), (25, 1), (33, 1), (36, 1), (43, 1)] }, { coefficient := 1, powers := [(12, 1), (15, 1), (25, 1), (33, 1), (36, 1), (49, 1)] }, { coefficient := 1, powers := [(12, 1), (15, 1), (32, 1), (33, 1), (35, 1), (36, 1)] }]
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
    (values : Fin 62 → R) :
    ¬ ∀ index : Fin 28,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component13.SelectedLeafB6_5.selectedHasNoCommonZero

end Krenn.Component13.SelectedLeafB6_5
