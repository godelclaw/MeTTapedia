import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component36.SelectedLeafB0_3_6

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "30c4b277ac9a650e324751538e9ce6bffdf337de163be261ae8c3902ba75fd9d"
def certificateSHA256 : String := "0fed907333b9e9371d748dada92e475ce216b39749ae2a5f9454eb9bac0cc045"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 40 → Fin 672 := ![
  13,
  14,
  15,
  18,
  19,
  134,
  154,
  158,
  162,
  256,
  278,
  298,
  299,
  300,
  301,
  305,
  307,
  320,
  322,
  323,
  325,
  379,
  448,
  451,
  453,
  470,
  475,
  478,
  480,
  483,
  583,
  584,
  613,
  642,
  651,
  662,
  663,
  665,
  669,
  671
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 40 → SparsePoly (Fin 66) := ![
  [{ coefficient := 1, powers := [(8, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (19, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (20, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (43, 1)] }, { coefficient := 1, powers := [(18, 1), (22, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (46, 1)] }, { coefficient := 1, powers := [(18, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (55, 1)] }, { coefficient := 1, powers := [(29, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (53, 1)] }, { coefficient := -1, powers := [(28, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (24, 1), (44, 1)] }, { coefficient := 1, powers := [(13, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (43, 1), (52, 1)] }, { coefficient := 1, powers := [(28, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1)] }, { coefficient := 1, powers := [(19, 1), (43, 1)] }, { coefficient := 1, powers := [(24, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (48, 1)] }, { coefficient := 1, powers := [(20, 1), (43, 1)] }, { coefficient := 1, powers := [(24, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (50, 1)] }, { coefficient := 1, powers := [(19, 1), (50, 1)] }, { coefficient := 1, powers := [(24, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (55, 1)] }, { coefficient := 1, powers := [(19, 1), (55, 1)] }, { coefficient := 1, powers := [(25, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (48, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1)] }, { coefficient := 1, powers := [(13, 1), (29, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1), (52, 1)] }, { coefficient := 1, powers := [(19, 1), (43, 1), (52, 1)] }, { coefficient := 1, powers := [(43, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1), (50, 1)] }, { coefficient := 1, powers := [(24, 1), (45, 1), (50, 1)] }, { coefficient := 1, powers := [(50, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1), (55, 1)] }, { coefficient := 1, powers := [(25, 1), (45, 1), (50, 1)] }, { coefficient := 1, powers := [(55, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (48, 1), (52, 1)] }, { coefficient := 1, powers := [(20, 1), (43, 1), (52, 1)] }, { coefficient := 1, powers := [(48, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (23, 1), (60, 1)] }, { coefficient := 1, powers := [(23, 1)] }, { coefficient := 1, powers := [(27, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (61, 1)] }, { coefficient := 1, powers := [(13, 1), (48, 1)] }, { coefficient := 1, powers := [(18, 1), (20, 1), (53, 1)] }, { coefficient := 1, powers := [(18, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (61, 1)] }, { coefficient := 1, powers := [(13, 1), (25, 1), (46, 1)] }, { coefficient := 1, powers := [(13, 1), (58, 1)] }, { coefficient := 1, powers := [(18, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (55, 1)] }, { coefficient := 1, powers := [(29, 1), (41, 1)] }, { coefficient := 1, powers := [(29, 1), (47, 1), (50, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1), (53, 1)] }, { coefficient := 1, powers := [(45, 1), (50, 1)] }, { coefficient := 1, powers := [(50, 1), (57, 1)] }, { coefficient := 1, powers := [(53, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(40, 1), (43, 1)] }, { coefficient := 1, powers := [(43, 1), (52, 1)] }, { coefficient := 1, powers := [(46, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1), (50, 1)] }, { coefficient := 1, powers := [(20, 1), (50, 1)] }, { coefficient := 1, powers := [(24, 1), (41, 1)] }, { coefficient := 1, powers := [(24, 1), (47, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1), (52, 1)] }, { coefficient := 1, powers := [(20, 1), (52, 1)] }, { coefficient := 1, powers := [(20, 1), (57, 1)] }, { coefficient := 1, powers := [(47, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (48, 1), (53, 1)] }, { coefficient := 1, powers := [(20, 1), (43, 1), (53, 1)] }, { coefficient := 1, powers := [(41, 1), (43, 1)] }, { coefficient := 1, powers := [(48, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1)] }, { coefficient := 1, powers := [(6, 1), (60, 1)] }, { coefficient := 1, powers := [(24, 1), (40, 1)] }, { coefficient := 1, powers := [(24, 1), (45, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (52, 1)] }, { coefficient := 1, powers := [(3, 1), (60, 1)] }, { coefficient := 1, powers := [(19, 1), (52, 1)] }, { coefficient := 1, powers := [(19, 1), (57, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (41, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (47, 1), (53, 1)] }, { coefficient := 1, powers := [(20, 1), (50, 1), (57, 1)] }, { coefficient := 1, powers := [(20, 1), (53, 1)] }, { coefficient := 1, powers := [(41, 1)] }, { coefficient := 1, powers := [(47, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (23, 1), (61, 1)] }, { coefficient := 1, powers := [(6, 1), (32, 1), (48, 1)] }, { coefficient := 1, powers := [(6, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(23, 1), (43, 1), (50, 1)] }, { coefficient := 1, powers := [(27, 1), (41, 1), (43, 1)] }, { coefficient := 1, powers := [(27, 1), (48, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (37, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (45, 1), (52, 1)] }, { coefficient := 1, powers := [(40, 1)] }, { coefficient := 1, powers := [(45, 1)] }, { coefficient := 1, powers := [(52, 1)] }, { coefficient := 1, powers := [(57, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (41, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (48, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (23, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (48, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(13, 1), (23, 1), (58, 1)] }, { coefficient := 1, powers := [(13, 1), (29, 1), (48, 1)] }, { coefficient := 1, powers := [(13, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (55, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (41, 1)] }, { coefficient := 1, powers := [(18, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1)] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(56, 1), (64, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(58, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 40 → SparsePoly (Fin 66) := ![
  [{ coefficient := -1, powers := [(3, 1), (35, 1), (47, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (44, 1), (48, 1), (64, 1)] }, { coefficient := 1, powers := [(29, 1), (45, 1), (48, 1)] }, { coefficient := -1, powers := [(35, 1), (38, 1), (44, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (46, 1), (47, 1)] }],
  [{ coefficient := -1, powers := [(23, 1), (45, 1), (55, 1)] }, { coefficient := 1, powers := [(27, 1), (45, 1), (47, 1), (55, 1)] }, { coefficient := 1, powers := [(29, 1), (45, 1), (47, 1), (50, 1)] }],
  [{ coefficient := -1, powers := [(29, 1), (45, 1), (50, 1)] }, { coefficient := -2, powers := [(29, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(47, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (29, 1)] }],
  [{ coefficient := -1, powers := [(18, 1), (47, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (20, 1), (43, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(29, 1), (48, 1), (64, 1)] }, { coefficient := 1, powers := [(35, 1), (38, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (24, 1), (50, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (23, 1), (50, 1), (52, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (28, 1), (50, 1), (60, 1)] }, { coefficient := -1, powers := [(8, 1), (32, 1), (40, 1)] }, { coefficient := -1, powers := [(8, 1), (32, 1), (45, 1)] }, { coefficient := -1, powers := [(13, 1), (29, 1), (45, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (35, 1), (47, 1), (52, 1)] }, { coefficient := -1, powers := [(8, 1), (35, 1), (47, 1), (57, 1)] }, { coefficient := -1, powers := [(18, 1), (29, 1), (45, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (23, 1), (45, 1)] }, { coefficient := -1, powers := [(18, 1), (27, 1), (45, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(55, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (43, 1), (45, 1)] }, { coefficient := -1, powers := [(20, 1), (46, 1)] }, { coefficient := 1, powers := [(48, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (23, 1), (50, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (29, 1), (47, 1)] }],
  [{ coefficient := -1, powers := [(18, 1), (23, 1)] }, { coefficient := 1, powers := [(18, 1), (27, 1), (47, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (32, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(29, 1)] }],
  [{ coefficient := -1, powers := [(27, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(18, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (20, 1), (29, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (20, 1), (32, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (35, 1), (52, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (35, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (27, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (32, 1), (48, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (35, 1), (47, 1), (50, 1)] }],
  [{ coefficient := -1, powers := [(18, 1), (29, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (24, 1), (35, 1), (41, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(8, 1), (20, 1), (32, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (35, 1), (37, 1), (41, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (35, 1), (40, 1), (41, 1), (57, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (35, 1), (41, 1), (45, 1), (52, 1)] }, { coefficient := -1, powers := [(8, 1), (27, 1), (48, 1), (53, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (28, 1), (48, 1), (50, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (40, 1), (48, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (48, 1), (52, 1)] }, { coefficient := -1, powers := [(8, 1), (35, 1), (41, 1), (45, 1)] }, { coefficient := 1, powers := [(13, 1), (29, 1), (45, 1), (48, 1)] }, { coefficient := -1, powers := [(18, 1), (20, 1), (29, 1), (45, 1), (53, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (41, 1), (57, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (47, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(20, 1), (43, 1), (45, 1), (55, 1)] }, { coefficient := 1, powers := [(20, 1), (46, 1), (55, 1)] }, { coefficient := 1, powers := [(38, 1), (61, 1)] }, { coefficient := 1, powers := [(41, 1), (58, 1)] }, { coefficient := -1, powers := [(43, 1), (47, 1), (55, 1)] }, { coefficient := -1, powers := [(48, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (29, 1), (48, 1)] }, { coefficient := -1, powers := [(13, 1), (35, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (32, 1)] }, { coefficient := 1, powers := [(13, 1), (23, 1)] }, { coefficient := 1, powers := [(13, 1), (27, 1), (47, 1)] }]
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
    ¬ ∀ index : Fin 40,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component36.SelectedLeafB0_3_6.selectedHasNoCommonZero

end Krenn.Component36.SelectedLeafB0_3_6
