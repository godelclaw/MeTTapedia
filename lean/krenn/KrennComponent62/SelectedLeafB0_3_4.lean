import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component62.SelectedLeafB0_3_4

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "b50926845a5aed11c0f366d061b7687f6e48e72e2a3df620d95b690822dcbbb0"
def certificateSHA256 : String := "6e229627c4882116a56d20c41d6c212b89c810a457c2b0217443b9a2e7e77f46"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 26 → Fin 667 := ![
  18,
  21,
  158,
  295,
  301,
  311,
  315,
  408,
  437,
  454,
  457,
  470,
  473,
  478,
  515,
  557,
  578,
  610,
  646,
  657,
  658,
  660,
  662,
  663,
  665,
  666
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 26 → SparsePoly (Fin 63) := ![
  [{ coefficient := 1, powers := [(22, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (50, 1)] }, { coefficient := 1, powers := [(22, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (48, 1)] }, { coefficient := 1, powers := [(18, 1), (48, 1)] }, { coefficient := 1, powers := [(23, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (46, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (44, 1)] }, { coefficient := 1, powers := [(17, 1), (38, 1)] }, { coefficient := 1, powers := [(17, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1), (48, 1)] }, { coefficient := 1, powers := [(23, 1), (43, 1), (48, 1)] }, { coefficient := 1, powers := [(48, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (23, 1), (44, 1)] }, { coefficient := 1, powers := [(17, 1), (23, 1), (38, 1)] }, { coefficient := 1, powers := [(17, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (51, 1)] }, { coefficient := 1, powers := [(18, 1), (48, 1), (55, 1)] }, { coefficient := 1, powers := [(18, 1), (51, 1)] }, { coefficient := 1, powers := [(48, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (53, 1)] }, { coefficient := 1, powers := [(27, 1), (39, 1)] }, { coefficient := 1, powers := [(27, 1), (45, 1), (48, 1)] }, { coefficient := 1, powers := [(30, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (35, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (44, 1), (51, 1)] }, { coefficient := 1, powers := [(41, 1), (51, 1)] }, { coefficient := 1, powers := [(44, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1), (51, 1)] }, { coefficient := 1, powers := [(43, 1), (48, 1)] }, { coefficient := 1, powers := [(48, 1), (55, 1)] }, { coefficient := 1, powers := [(51, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1), (48, 1)] }, { coefficient := 1, powers := [(6, 1), (59, 1)] }, { coefficient := 1, powers := [(23, 1), (44, 1), (48, 1)] }, { coefficient := 1, powers := [(41, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1), (48, 1)] }, { coefficient := 1, powers := [(19, 1), (48, 1)] }, { coefficient := 1, powers := [(23, 1), (39, 1)] }, { coefficient := 1, powers := [(23, 1), (45, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (22, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (30, 1), (46, 1)] }, { coefficient := 1, powers := [(6, 1), (33, 1), (39, 1)] }, { coefficient := 1, powers := [(22, 1), (41, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (41, 1), (52, 1)] }, { coefficient := 1, powers := [(22, 1), (56, 1)] }, { coefficient := 1, powers := [(27, 1), (46, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1)] }, { coefficient := 1, powers := [(6, 1), (58, 1)] }, { coefficient := 1, powers := [(23, 1), (38, 1)] }, { coefficient := 1, powers := [(23, 1), (43, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (39, 1), (55, 1)] }, { coefficient := 1, powers := [(0, 1), (45, 1), (51, 1)] }, { coefficient := 1, powers := [(19, 1), (48, 1), (55, 1)] }, { coefficient := 1, powers := [(19, 1), (51, 1)] }, { coefficient := 1, powers := [(39, 1)] }, { coefficient := 1, powers := [(45, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (35, 1), (58, 1)] }, { coefficient := 1, powers := [(0, 1), (38, 1), (55, 1)] }, { coefficient := 1, powers := [(0, 1), (43, 1), (50, 1)] }, { coefficient := 1, powers := [(38, 1)] }, { coefficient := 1, powers := [(43, 1)] }, { coefficient := 1, powers := [(50, 1)] }, { coefficient := 1, powers := [(55, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (36, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (46, 1), (53, 1)] }, { coefficient := 1, powers := [(5, 1), (27, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (53, 1)] }, { coefficient := 1, powers := [(8, 1), (22, 1), (59, 1)] }, { coefficient := 1, powers := [(8, 1), (30, 1), (46, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (39, 1)] }, { coefficient := 1, powers := [(12, 1), (22, 1), (56, 1)] }, { coefficient := 1, powers := [(12, 1), (27, 1), (46, 1)] }, { coefficient := 1, powers := [(12, 1), (33, 1), (36, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (53, 1)] }, { coefficient := 1, powers := [(17, 1), (27, 1), (39, 1)] }, { coefficient := 1, powers := [(17, 1), (30, 1), (36, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1)] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(38, 1), (60, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(39, 1), (61, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(55, 1)] }],
  [{ coefficient := 1, powers := [(56, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 26 → SparsePoly (Fin 63) := ![
  [{ coefficient := 1, powers := [(6, 1), (12, 1), (50, 1), (52, 1), (58, 1), (60, 1)] }, { coefficient := 1, powers := [(6, 1), (12, 1), (52, 1), (58, 1)] }, { coefficient := 1, powers := [(8, 1), (48, 1), (50, 1), (58, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (48, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (17, 1), (45, 1), (50, 1), (58, 1), (60, 1)] }, { coefficient := 1, powers := [(6, 1), (17, 1), (45, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (17, 1), (23, 1), (50, 1), (53, 1), (58, 1), (60, 1)] }, { coefficient := 1, powers := [(6, 1), (17, 1), (23, 1), (53, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (27, 1), (44, 1), (50, 1), (58, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (27, 1), (44, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (50, 1), (53, 1), (58, 1), (60, 1)] }, { coefficient := -1, powers := [(6, 1), (53, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (22, 1), (23, 1), (50, 1), (53, 1), (58, 1), (60, 1)] }, { coefficient := -1, powers := [(6, 1), (22, 1), (23, 1), (53, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(45, 1), (50, 1), (60, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (22, 1), (50, 1), (53, 1), (58, 1), (60, 1)] }, { coefficient := 1, powers := [(6, 1), (22, 1), (53, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (27, 1), (41, 1), (50, 1), (58, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (27, 1), (41, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (17, 1), (50, 1), (58, 1), (60, 1)] }, { coefficient := -1, powers := [(6, 1), (17, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (18, 1), (27, 1), (50, 1), (58, 1), (60, 1)] }, { coefficient := -1, powers := [(5, 1), (18, 1), (27, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (50, 1), (60, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (27, 1), (50, 1), (58, 1), (60, 1)] }, { coefficient := -1, powers := [(5, 1), (27, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(43, 1), (50, 1), (60, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (50, 1), (58, 1), (60, 1)] }, { coefficient := -1, powers := [(8, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (12, 1), (50, 1), (58, 1), (60, 1)] }, { coefficient := -1, powers := [(6, 1), (12, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(50, 1), (60, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := -1, powers := [(50, 1), (60, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(23, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (50, 1), (58, 1), (60, 1)] }, { coefficient := 1, powers := [(6, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (18, 1), (27, 1), (35, 1), (50, 1), (58, 1), (59, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (18, 1), (27, 1), (35, 1), (58, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (18, 1), (27, 1), (44, 1), (50, 1), (51, 1), (58, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (18, 1), (27, 1), (44, 1), (51, 1), (58, 1)] }, { coefficient := -1, powers := [(5, 1), (27, 1), (41, 1), (50, 1), (51, 1), (58, 1), (60, 1)] }, { coefficient := -1, powers := [(5, 1), (27, 1), (41, 1), (51, 1), (58, 1)] }, { coefficient := -1, powers := [(19, 1), (43, 1), (50, 1), (51, 1), (60, 1), (61, 1)] }, { coefficient := 1, powers := [(23, 1), (35, 1), (58, 1)] }, { coefficient := 1, powers := [(23, 1), (38, 1), (55, 1)] }, { coefficient := 1, powers := [(23, 1), (43, 1), (50, 1)] }, { coefficient := 1, powers := [(39, 1), (50, 1), (55, 1), (60, 1), (61, 1)] }, { coefficient := -1, powers := [(43, 1), (50, 1), (60, 1)] }, { coefficient := -1, powers := [(43, 1)] }, { coefficient := 1, powers := [(45, 1), (50, 1), (51, 1), (60, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (36, 1), (50, 1), (58, 1), (59, 1), (60, 1)] }, { coefficient := -1, powers := [(6, 1), (36, 1), (58, 1), (59, 1)] }, { coefficient := -1, powers := [(6, 1), (39, 1), (50, 1), (56, 1), (58, 1), (60, 1)] }, { coefficient := -1, powers := [(6, 1), (39, 1), (56, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(23, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (43, 1), (50, 1), (60, 1)] }, { coefficient := 1, powers := [(50, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (18, 1), (27, 1), (41, 1), (48, 1), (50, 1), (58, 1), (60, 1)] }, { coefficient := -1, powers := [(5, 1), (18, 1), (27, 1), (41, 1), (48, 1), (58, 1)] }, { coefficient := -1, powers := [(6, 1), (17, 1), (22, 1), (23, 1), (50, 1), (53, 1), (58, 1), (60, 1)] }, { coefficient := -1, powers := [(6, 1), (17, 1), (22, 1), (23, 1), (53, 1), (58, 1)] }, { coefficient := 1, powers := [(23, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (6, 1), (30, 1), (50, 1), (58, 1), (60, 1)] }, { coefficient := -1, powers := [(5, 1), (6, 1), (30, 1), (58, 1)] }]
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
    ¬ ∀ index : Fin 26,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component62.SelectedLeafB0_3_4.selectedHasNoCommonZero

end Krenn.Component62.SelectedLeafB0_3_4
