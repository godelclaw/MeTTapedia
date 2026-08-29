import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component25.SelectedLeafB5_2_4_1

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "eedcdf8b92f84b7b5d7c929476dec8c4f490137914e894402e37ce2c60608bbe"
def certificateSHA256 : String := "9858244fe25ded1a02e9024e089b64fcd9b0819fccdd79df475b4759228eb0e1"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 27 → Fin 668 := ![
  14,
  21,
  162,
  169,
  170,
  239,
  267,
  293,
  300,
  312,
  388,
  405,
  406,
  430,
  435,
  439,
  440,
  450,
  475,
  616,
  655,
  656,
  661,
  663,
  664,
  665,
  667
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 27 → SparsePoly (Fin 66) := ![
  [{ coefficient := 1, powers := [(16, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (18, 1)] }, { coefficient := 1, powers := [(16, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (57, 1)] }, { coefficient := 1, powers := [(29, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (43, 1)] }, { coefficient := 1, powers := [(27, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (24, 1), (46, 1)] }, { coefficient := 1, powers := [(17, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (24, 1), (48, 1)] }, { coefficient := 1, powers := [(17, 1), (19, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (48, 1)] }, { coefficient := 1, powers := [(19, 1), (43, 1)] }, { coefficient := 1, powers := [(24, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (60, 1)] }, { coefficient := 1, powers := [(12, 1), (57, 1)] }, { coefficient := 1, powers := [(17, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (57, 1)] }, { coefficient := 1, powers := [(29, 1), (48, 1)] }, { coefficient := 1, powers := [(35, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (18, 1), (56, 1)] }, { coefficient := 1, powers := [(12, 1)] }, { coefficient := 1, powers := [(16, 1), (18, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (24, 1), (40, 1)] }, { coefficient := 1, powers := [(16, 1), (24, 1), (45, 1)] }, { coefficient := 1, powers := [(16, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (24, 1), (46, 1)] }, { coefficient := 1, powers := [(17, 1), (24, 1), (40, 1)] }, { coefficient := 1, powers := [(17, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (48, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1), (48, 1)] }, { coefficient := 1, powers := [(17, 1), (23, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1)] }, { coefficient := 1, powers := [(12, 1), (29, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (60, 1)] }, { coefficient := 1, powers := [(12, 1), (48, 1)] }, { coefficient := 1, powers := [(17, 1), (19, 1), (53, 1)] }, { coefficient := 1, powers := [(17, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (32, 1)] }, { coefficient := 1, powers := [(22, 1), (50, 1)] }, { coefficient := 1, powers := [(27, 1), (50, 1)] }, { coefficient := 1, powers := [(32, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (54, 1)] }, { coefficient := 1, powers := [(29, 1), (41, 1)] }, { coefficient := 1, powers := [(29, 1), (47, 1), (50, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (36, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (36, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (43, 1), (50, 1)] }, { coefficient := 1, powers := [(12, 1), (27, 1), (43, 1)] }, { coefficient := 1, powers := [(12, 1), (35, 1), (36, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (50, 1)] }, { coefficient := 1, powers := [(17, 1), (32, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (41, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (48, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (23, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (48, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(12, 1), (23, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1), (29, 1), (48, 1)] }, { coefficient := 1, powers := [(12, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(17, 1), (23, 1), (54, 1)] }, { coefficient := 1, powers := [(17, 1), (29, 1), (41, 1)] }, { coefficient := 1, powers := [(17, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (61, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(41, 1)] }],
  [{ coefficient := 1, powers := [(56, 1)] }],
  [{ coefficient := 1, powers := [(57, 1)] }],
  [{ coefficient := 1, powers := [(24, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (65, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 27 → SparsePoly (Fin 66) := ![
  [{ coefficient := -1, powers := [(22, 1), (48, 1)] }],
  [{ coefficient := -1, powers := [(17, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (48, 1), (53, 1)] }, { coefficient := -1, powers := [(35, 1), (36, 1), (38, 1), (53, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (19, 1), (54, 1), (61, 1), (65, 1)] }, { coefficient := 1, powers := [(2, 1), (38, 1), (50, 1), (59, 1), (65, 1)] }, { coefficient := 1, powers := [(12, 1), (19, 1), (29, 1), (61, 1), (65, 1)] }, { coefficient := 1, powers := [(12, 1), (27, 1), (38, 1), (59, 1), (65, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1), (54, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(16, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(27, 1), (38, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(29, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (54, 1), (61, 1)] }, { coefficient := -1, powers := [(12, 1), (29, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(23, 1)] }],
  [{ coefficient := 1, powers := [(12, 1)] }],
  [{ coefficient := -1, powers := [(29, 1), (48, 1)] }, { coefficient := 1, powers := [(35, 1), (36, 1), (38, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(22, 1), (38, 1), (60, 1)] }, { coefficient := -1, powers := [(27, 1), (38, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (32, 1), (38, 1), (59, 1)] }, { coefficient := -2, powers := [(23, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(54, 1)] }],
  [{ coefficient := 1, powers := [(48, 1)] }],
  [{ coefficient := 1, powers := [(29, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (38, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(17, 1)] }],
  [{ coefficient := 1, powers := [(38, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(38, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (48, 1), (54, 1)] }, { coefficient := 1, powers := [(12, 1), (29, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (35, 1)] }, { coefficient := -1, powers := [(17, 1), (29, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (18, 1), (29, 1), (48, 1)] }, { coefficient := -1, powers := [(12, 1), (18, 1), (35, 1), (36, 1), (38, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (19, 1), (22, 1), (54, 1), (61, 1), (65, 1)] }, { coefficient := -1, powers := [(2, 1), (22, 1), (38, 1), (50, 1), (59, 1), (65, 1)] }, { coefficient := 1, powers := [(2, 1), (41, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1)] }, { coefficient := -1, powers := [(12, 1), (19, 1), (22, 1), (29, 1), (61, 1), (65, 1)] }, { coefficient := -1, powers := [(12, 1), (22, 1), (27, 1), (38, 1), (59, 1), (65, 1)] }, { coefficient := -1, powers := [(12, 1), (23, 1)] }, { coefficient := -1, powers := [(16, 1), (22, 1), (23, 1), (54, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (48, 1), (54, 1), (61, 1)] }, { coefficient := 1, powers := [(6, 1), (16, 1), (32, 1), (38, 1), (46, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (17, 1), (32, 1), (38, 1), (40, 1), (59, 1)] }, { coefficient := 1, powers := [(12, 1), (27, 1), (38, 1), (46, 1), (59, 1)] }, { coefficient := 1, powers := [(12, 1), (29, 1), (48, 1), (61, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1), (38, 1), (40, 1), (60, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1), (38, 1), (45, 1), (60, 1)] }, { coefficient := 2, powers := [(16, 1), (23, 1), (46, 1), (54, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1), (38, 1), (40, 1), (60, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1), (38, 1), (45, 1), (60, 1)] }, { coefficient := 1, powers := [(16, 1), (35, 1), (36, 1), (38, 1), (53, 1), (59, 1)] }, { coefficient := 2, powers := [(17, 1), (23, 1), (40, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (19, 1), (43, 1), (54, 1), (61, 1)] }, { coefficient := -1, powers := [(2, 1), (38, 1), (43, 1), (50, 1), (59, 1)] }, { coefficient := -1, powers := [(12, 1), (19, 1), (29, 1), (43, 1), (61, 1)] }, { coefficient := -1, powers := [(12, 1), (27, 1), (38, 1), (43, 1), (59, 1)] }, { coefficient := -1, powers := [(16, 1), (23, 1), (43, 1), (54, 1)] }]
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
    ¬ ∀ index : Fin 27,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component25.SelectedLeafB5_2_4_1.selectedHasNoCommonZero

end Krenn.Component25.SelectedLeafB5_2_4_1
