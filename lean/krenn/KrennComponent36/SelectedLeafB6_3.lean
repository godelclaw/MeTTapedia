import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component36.SelectedLeafB6_3

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "5b529ab055bf0b74597d8fa8337e80b2cd4edaa2bd071a7b9d3144aa410b15f6"
def certificateSHA256 : String := "fa05db40f4ce78f5eac98a0962223823e0599685389de658b97fc0e587e6cb22"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 24 → Fin 669 := ![
  0,
  2,
  3,
  10,
  13,
  19,
  158,
  159,
  305,
  307,
  327,
  363,
  379,
  448,
  453,
  485,
  486,
  562,
  595,
  662,
  664,
  665,
  667,
  668
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 24 → SparsePoly (Fin 66) := ![
  [{ coefficient := 1, powers := [(1, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (20, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (55, 1)] }, { coefficient := 1, powers := [(29, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (43, 1)] }, { coefficient := 1, powers := [(27, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (48, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1)] }, { coefficient := 1, powers := [(13, 1), (29, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (38, 1), (61, 1)] }, { coefficient := 1, powers := [(1, 1), (41, 1), (58, 1)] }, { coefficient := 1, powers := [(1, 1), (48, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (29, 1), (60, 1)] }, { coefficient := 1, powers := [(22, 1), (54, 1)] }, { coefficient := 1, powers := [(29, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (23, 1), (60, 1)] }, { coefficient := 1, powers := [(23, 1)] }, { coefficient := 1, powers := [(27, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (61, 1)] }, { coefficient := 1, powers := [(13, 1), (48, 1)] }, { coefficient := 1, powers := [(18, 1), (20, 1), (53, 1)] }, { coefficient := 1, powers := [(18, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (55, 1)] }, { coefficient := 1, powers := [(29, 1), (41, 1)] }, { coefficient := 1, powers := [(29, 1), (47, 1), (50, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (36, 1), (60, 1)] }, { coefficient := 1, powers := [(1, 1)] }, { coefficient := 1, powers := [(11, 1), (34, 1), (36, 1)] }, { coefficient := 1, powers := [(16, 1), (31, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (38, 1), (60, 1)] }, { coefficient := 1, powers := [(1, 1), (47, 1), (54, 1)] }, { coefficient := 1, powers := [(11, 1), (34, 1), (38, 1)] }, { coefficient := 1, powers := [(16, 1), (31, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (43, 1), (54, 1)] }, { coefficient := 1, powers := [(23, 1), (58, 1)] }, { coefficient := 1, powers := [(29, 1), (48, 1)] }, { coefficient := 1, powers := [(35, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (40, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (46, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (40, 1)] }, { coefficient := 1, powers := [(18, 1), (28, 1), (54, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (41, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (48, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (23, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (48, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(13, 1), (23, 1), (58, 1)] }, { coefficient := 1, powers := [(13, 1), (29, 1), (48, 1)] }, { coefficient := 1, powers := [(13, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (55, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (41, 1)] }, { coefficient := 1, powers := [(18, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(40, 1), (64, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(41, 1), (65, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 24 → SparsePoly (Fin 66) := ![
  [{ coefficient := -1, powers := [(8, 1), (27, 1), (61, 1), (63, 1)] }],
  [{ coefficient := -2, powers := [(5, 1), (22, 1), (61, 1), (63, 1)] }, { coefficient := -1, powers := [(5, 1), (32, 1), (36, 1), (47, 1), (61, 1), (63, 1), (65, 1)] }, { coefficient := 1, powers := [(13, 1), (27, 1), (48, 1), (63, 1)] }, { coefficient := -1, powers := [(18, 1), (28, 1), (41, 1), (63, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (32, 1), (48, 1), (63, 1), (65, 1)] }, { coefficient := 1, powers := [(18, 1), (22, 1), (47, 1), (63, 1)] }, { coefficient := -1, powers := [(18, 1), (23, 1), (63, 1)] }],
  [{ coefficient := -2, powers := [(3, 1), (29, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (23, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(18, 1), (47, 1)] }],
  [{ coefficient := -1, powers := [(13, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(55, 1)] }],
  [{ coefficient := 1, powers := [(48, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (32, 1), (63, 1), (65, 1)] }],
  [{ coefficient := 2, powers := [(5, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(29, 1)] }],
  [{ coefficient := 1, powers := [(18, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (32, 1), (38, 1), (61, 1), (63, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (32, 1), (36, 1), (61, 1), (63, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(13, 1)] }],
  [{ coefficient := 1, powers := [(41, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := 2, powers := [(5, 1), (22, 1), (54, 1), (61, 1)] }, { coefficient := -1, powers := [(5, 1), (32, 1), (41, 1), (58, 1), (65, 1)] }, { coefficient := 1, powers := [(8, 1), (27, 1), (47, 1), (61, 1)] }, { coefficient := -1, powers := [(13, 1), (27, 1), (48, 1), (54, 1)] }, { coefficient := -1, powers := [(18, 1), (22, 1), (47, 1), (55, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (55, 1)] }, { coefficient := 1, powers := [(18, 1), (28, 1), (41, 1), (54, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(38, 1), (61, 1)] }, { coefficient := -1, powers := [(40, 1), (41, 1), (58, 1), (64, 1)] }, { coefficient := -1, powers := [(41, 1), (46, 1), (54, 1), (64, 1)] }, { coefficient := 1, powers := [(41, 1), (58, 1)] }, { coefficient := -1, powers := [(48, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (35, 1), (41, 1)] }, { coefficient := -1, powers := [(18, 1), (29, 1), (41, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (32, 1), (58, 1)] }]
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

#print axioms Krenn.Component36.SelectedLeafB6_3.selectedHasNoCommonZero

end Krenn.Component36.SelectedLeafB6_3
