import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component10.SelectedLeafB5_6_6

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "138d584e056e518ba3b07d2b88389af9424c756c8f6c08546efcc7efaecf4089"
def certificateSHA256 : String := "6f0c0474af35c583c09c040169208c4bc202168f64b0300cb38a513ba5a74aff"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 48 → Fin 644 := ![
  0,
  2,
  8,
  10,
  19,
  21,
  34,
  97,
  135,
  162,
  167,
  168,
  182,
  184,
  185,
  202,
  284,
  290,
  343,
  349,
  350,
  356,
  358,
  359,
  368,
  409,
  445,
  446,
  456,
  462,
  463,
  464,
  466,
  467,
  471,
  479,
  490,
  491,
  499,
  556,
  557,
  634,
  635,
  637,
  640,
  641,
  642,
  643
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 48 → SparsePoly (Fin 66) := ![
  [{ coefficient := 1, powers := [(3, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (23, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (23, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (48, 1)] }, { coefficient := 1, powers := [(24, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (58, 1)] }, { coefficient := 1, powers := [(17, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (32, 1)] }, { coefficient := 1, powers := [(32, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (23, 1)] }, { coefficient := 1, powers := [(23, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (19, 1)] }, { coefficient := 1, powers := [(17, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (43, 1)] }, { coefficient := 1, powers := [(18, 1), (19, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (48, 1), (51, 1)] }, { coefficient := 1, powers := [(48, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (19, 1), (55, 1)] }, { coefficient := 1, powers := [(12, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (24, 1), (44, 1)] }, { coefficient := 1, powers := [(12, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1)] }, { coefficient := 1, powers := [(19, 1), (43, 1)] }, { coefficient := 1, powers := [(24, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (59, 1)] }, { coefficient := 1, powers := [(12, 1), (48, 1)] }, { coefficient := 1, powers := [(18, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (59, 1)] }, { coefficient := 1, powers := [(12, 1), (56, 1)] }, { coefficient := 1, powers := [(18, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (46, 1)] }, { coefficient := 1, powers := [(18, 1), (40, 1)] }, { coefficient := 1, powers := [(18, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (51, 1)] }, { coefficient := 1, powers := [(23, 1), (55, 1)] }, { coefficient := 1, powers := [(28, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (53, 1)] }, { coefficient := 1, powers := [(29, 1), (41, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1), (51, 1)] }, { coefficient := 1, powers := [(19, 1), (43, 1), (51, 1)] }, { coefficient := 1, powers := [(43, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (23, 1), (58, 1)] }, { coefficient := 1, powers := [(23, 1)] }, { coefficient := 1, powers := [(27, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (24, 1), (40, 1)] }, { coefficient := 1, powers := [(17, 1), (24, 1), (45, 1)] }, { coefficient := 1, powers := [(17, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (24, 1), (46, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (40, 1)] }, { coefficient := 1, powers := [(18, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1)] }, { coefficient := 1, powers := [(24, 1), (40, 1), (43, 1)] }, { coefficient := 1, powers := [(24, 1), (46, 1)] }, { coefficient := 1, powers := [(43, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (47, 1)] }, { coefficient := 1, powers := [(5, 1), (27, 1), (58, 1)] }, { coefficient := 1, powers := [(17, 1), (23, 1)] }, { coefficient := 1, powers := [(17, 1), (27, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (48, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1)] }, { coefficient := 1, powers := [(17, 1), (27, 1), (48, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (51, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (51, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (55, 1)] }, { coefficient := 1, powers := [(17, 1), (28, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (53, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1)] }, { coefficient := 1, powers := [(12, 1), (29, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (35, 1)] }, { coefficient := 1, powers := [(22, 1), (43, 1)] }, { coefficient := 1, powers := [(27, 1), (43, 1)] }, { coefficient := 1, powers := [(35, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (40, 1)] }, { coefficient := 1, powers := [(17, 1), (45, 1)] }, { coefficient := 1, powers := [(17, 1), (51, 1)] }, { coefficient := 1, powers := [(17, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1), (51, 1)] }, { coefficient := 1, powers := [(40, 1), (43, 1)] }, { coefficient := 1, powers := [(43, 1), (51, 1)] }, { coefficient := 1, powers := [(46, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (36, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1)] }, { coefficient := 1, powers := [(17, 1), (27, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (36, 1), (59, 1)] }, { coefficient := 1, powers := [(12, 1), (27, 1), (43, 1)] }, { coefficient := 1, powers := [(12, 1), (35, 1), (36, 1)] }, { coefficient := 1, powers := [(18, 1), (32, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (27, 1), (58, 1)] }, { coefficient := 1, powers := [(6, 1), (22, 1), (58, 1)] }, { coefficient := 1, powers := [(22, 1)] }, { coefficient := 1, powers := [(27, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1)] }, { coefficient := 1, powers := [(6, 1), (58, 1)] }, { coefficient := 1, powers := [(24, 1), (40, 1)] }, { coefficient := 1, powers := [(24, 1), (45, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (51, 1)] }, { coefficient := 1, powers := [(3, 1), (58, 1)] }, { coefficient := 1, powers := [(19, 1), (51, 1)] }, { coefficient := 1, powers := [(19, 1), (55, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (41, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (48, 1), (53, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (53, 1)] }, { coefficient := 1, powers := [(8, 1), (23, 1), (59, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (48, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(12, 1), (23, 1), (56, 1)] }, { coefficient := 1, powers := [(12, 1), (29, 1), (48, 1)] }, { coefficient := 1, powers := [(12, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (53, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (41, 1)] }, { coefficient := 1, powers := [(18, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (60, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (61, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(41, 1)] }],
  [{ coefficient := 1, powers := [(54, 1), (64, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(55, 1), (65, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(56, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 48 → SparsePoly (Fin 66) := ![
  [{ coefficient := 1, powers := [(17, 1), (27, 1), (38, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (22, 1), (38, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (35, 1), (38, 1), (44, 1), (51, 1), (64, 1)] }, { coefficient := -1, powers := [(19, 1), (35, 1), (38, 1), (44, 1), (51, 1), (64, 1)] }, { coefficient := 1, powers := [(29, 1), (44, 1), (48, 1), (64, 1)] }, { coefficient := -1, powers := [(35, 1), (38, 1), (44, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(22, 1), (38, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (53, 1)] }, { coefficient := 1, powers := [(24, 1), (28, 1), (53, 1)] }, { coefficient := -1, powers := [(27, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(22, 1), (48, 1)] }, { coefficient := -1, powers := [(23, 1), (24, 1), (46, 1)] }],
  [{ coefficient := -1, powers := [(18, 1), (27, 1), (60, 1)] }],
  [{ coefficient := -3, powers := [(18, 1), (53, 1), (64, 1), (65, 1)] }],
  [{ coefficient := -3, powers := [(18, 1), (28, 1), (53, 1), (61, 1), (64, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (51, 1), (53, 1)] }],
  [{ coefficient := -3, powers := [(18, 1), (27, 1), (28, 1), (53, 1), (61, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (38, 1), (58, 1)] }],
  [{ coefficient := 3, powers := [(18, 1), (51, 1), (53, 1), (64, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(24, 1), (32, 1), (38, 1), (40, 1), (43, 1), (60, 1)] }, { coefficient := -1, powers := [(24, 1), (32, 1), (38, 1), (43, 1), (51, 1), (60, 1)] }, { coefficient := -1, powers := [(24, 1), (32, 1), (38, 1), (46, 1), (51, 1)] }],
  [{ coefficient := -1, powers := [(24, 1), (32, 1), (38, 1), (40, 1)] }, { coefficient := -1, powers := [(24, 1), (32, 1), (38, 1), (51, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(35, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (35, 1), (38, 1), (51, 1), (64, 1)] }, { coefficient := 1, powers := [(19, 1), (35, 1), (38, 1), (51, 1), (64, 1)] }, { coefficient := -1, powers := [(29, 1), (48, 1), (64, 1)] }, { coefficient := 1, powers := [(35, 1), (38, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(17, 1), (24, 1), (32, 1), (38, 1), (40, 1), (51, 1)] }, { coefficient := 1, powers := [(17, 1), (24, 1), (32, 1), (38, 1), (40, 1), (60, 1)] }, { coefficient := 1, powers := [(17, 1), (24, 1), (32, 1), (38, 1), (51, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(29, 1)] }],
  [{ coefficient := 1, powers := [(23, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (24, 1), (32, 1), (38, 1), (51, 1)] }],
  [{ coefficient := -3, powers := [(18, 1), (53, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (18, 1), (45, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (45, 1)] }, { coefficient := 1, powers := [(18, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (24, 1), (32, 1), (38, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(22, 1), (48, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (53, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (24, 1), (32, 1), (38, 1), (51, 1)] }],
  [{ coefficient := 3, powers := [(18, 1), (28, 1), (53, 1), (61, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(53, 1)] }],
  [{ coefficient := -1, powers := [(24, 1), (48, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(48, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (38, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (24, 1), (48, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(17, 1), (24, 1), (32, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(38, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(38, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(17, 1), (38, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(18, 1), (23, 1), (53, 1)] }, { coefficient := -1, powers := [(18, 1), (32, 1), (38, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (35, 1), (38, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(17, 1), (24, 1), (32, 1), (38, 1), (40, 1), (43, 1)] }, { coefficient := -1, powers := [(17, 1), (24, 1), (32, 1), (38, 1), (43, 1), (51, 1)] }, { coefficient := 1, powers := [(18, 1), (27, 1), (47, 1), (53, 1)] }],
  [{ coefficient := -3, powers := [(18, 1), (28, 1), (47, 1), (53, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (18, 1), (29, 1), (45, 1)] }, { coefficient := 1, powers := [(2, 1), (56, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1)] }, { coefficient := -1, powers := [(18, 1), (24, 1), (29, 1), (45, 1)] }, { coefficient := -1, powers := [(18, 1), (29, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (12, 1), (35, 1), (38, 1), (51, 1)] }, { coefficient := -1, powers := [(12, 1), (19, 1), (35, 1), (38, 1), (51, 1)] }, { coefficient := 1, powers := [(12, 1), (29, 1), (48, 1)] }, { coefficient := -1, powers := [(12, 1), (35, 1), (38, 1)] }, { coefficient := 3, powers := [(17, 1), (18, 1), (23, 1), (28, 1), (53, 1), (61, 1), (65, 1)] }, { coefficient := -3, powers := [(18, 1), (23, 1), (51, 1), (53, 1), (65, 1)] }],
  [{ coefficient := 3, powers := [(18, 1), (23, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (32, 1)] }]
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
    ¬ ∀ index : Fin 48,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component10.SelectedLeafB5_6_6.selectedHasNoCommonZero

end Krenn.Component10.SelectedLeafB5_6_6
