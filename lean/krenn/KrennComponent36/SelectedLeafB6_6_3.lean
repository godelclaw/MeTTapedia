import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component36.SelectedLeafB6_6_3

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "38c9dd37b2a5d869f8d9947fee01581a48aab27697cb74c0a864fc0b101fb714"
def certificateSHA256 : String := "0f7c8efe9325da8b5661254f96cf85b0e1a7388459859472a42fa4c89e127b41"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 21 → Fin 672 := ![
  0,
  1,
  3,
  13,
  15,
  19,
  160,
  305,
  307,
  379,
  448,
  451,
  453,
  562,
  596,
  662,
  664,
  665,
  668,
  670,
  671
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 21 → SparsePoly (Fin 68) := ![
  [{ coefficient := 1, powers := [(1, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (20, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (54, 1)] }, { coefficient := 1, powers := [(29, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (48, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1)] }, { coefficient := 1, powers := [(13, 1), (29, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (23, 1), (60, 1)] }, { coefficient := 1, powers := [(23, 1)] }, { coefficient := 1, powers := [(27, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (61, 1)] }, { coefficient := 1, powers := [(13, 1), (48, 1)] }, { coefficient := 1, powers := [(18, 1), (20, 1), (53, 1)] }, { coefficient := 1, powers := [(18, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (61, 1)] }, { coefficient := 1, powers := [(13, 1), (25, 1), (46, 1)] }, { coefficient := 1, powers := [(13, 1), (58, 1)] }, { coefficient := 1, powers := [(18, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (55, 1)] }, { coefficient := 1, powers := [(29, 1), (41, 1)] }, { coefficient := 1, powers := [(29, 1), (47, 1), (50, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (43, 1), (54, 1)] }, { coefficient := 1, powers := [(23, 1), (58, 1)] }, { coefficient := 1, powers := [(29, 1), (48, 1)] }, { coefficient := 1, powers := [(35, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (41, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (47, 1), (53, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (57, 1)] }, { coefficient := 1, powers := [(13, 1), (23, 1), (57, 1)] }, { coefficient := 1, powers := [(13, 1), (28, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (41, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (48, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (23, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (48, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(13, 1), (23, 1), (58, 1)] }, { coefficient := 1, powers := [(13, 1), (29, 1), (48, 1)] }, { coefficient := 1, powers := [(13, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (55, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (41, 1)] }, { coefficient := 1, powers := [(18, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(41, 1)] }],
  [{ coefficient := 1, powers := [(57, 1), (66, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(58, 1), (67, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 21 → SparsePoly (Fin 68) := ![
  [{ coefficient := -2, powers := [(8, 1), (27, 1), (61, 1), (63, 1)] }, { coefficient := -1, powers := [(13, 1), (28, 1), (58, 1), (63, 1), (66, 1)] }, { coefficient := 1, powers := [(13, 1), (29, 1), (43, 1), (58, 1), (63, 1), (67, 1)] }, { coefficient := -1, powers := [(18, 1), (29, 1), (50, 1), (58, 1), (63, 1), (67, 1)] }],
  [{ coefficient := -2, powers := [(13, 1), (29, 1), (58, 1), (63, 1), (67, 1)] }],
  [{ coefficient := -2, powers := [(18, 1), (23, 1), (58, 1), (63, 1), (67, 1)] }, { coefficient := 2, powers := [(18, 1), (23, 1), (63, 1)] }],
  [{ coefficient := -2, powers := [(6, 1), (23, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(23, 1), (46, 1), (58, 1), (67, 1)] }, { coefficient := 2, powers := [(23, 1), (46, 1)] }],
  [{ coefficient := -1, powers := [(29, 1), (53, 1), (58, 1), (67, 1)] }],
  [{ coefficient := -1, powers := [(13, 1), (43, 1), (58, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(55, 1), (58, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(48, 1), (58, 1), (67, 1)] }],
  [{ coefficient := 2, powers := [(8, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (58, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (58, 1), (67, 1)] }, { coefficient := -2, powers := [(23, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (58, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (58, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(58, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(58, 1), (67, 1)] }],
  [{ coefficient := 2, powers := [(8, 1), (27, 1), (47, 1), (61, 1)] }, { coefficient := 1, powers := [(13, 1), (28, 1), (47, 1), (58, 1), (66, 1)] }, { coefficient := -1, powers := [(13, 1), (29, 1), (43, 1), (47, 1), (58, 1), (67, 1)] }, { coefficient := 2, powers := [(13, 1), (29, 1), (48, 1), (58, 1), (67, 1)] }, { coefficient := 2, powers := [(18, 1), (23, 1), (55, 1), (58, 1), (67, 1)] }, { coefficient := -2, powers := [(18, 1), (23, 1), (55, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (47, 1), (50, 1), (58, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(38, 1), (58, 1), (61, 1), (67, 1)] }, { coefficient := -1, powers := [(41, 1), (57, 1), (58, 1), (66, 1)] }, { coefficient := 1, powers := [(41, 1), (58, 2), (67, 1)] }, { coefficient := -1, powers := [(47, 1), (53, 1), (58, 1), (66, 1)] }, { coefficient := -1, powers := [(48, 1), (55, 1), (58, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (35, 1), (58, 1), (67, 1)] }, { coefficient := -1, powers := [(18, 1), (29, 1), (58, 1), (67, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (32, 1), (58, 1)] }, { coefficient := -1, powers := [(13, 1), (23, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (32, 1), (58, 1)] }, { coefficient := -1, powers := [(13, 1), (23, 1), (58, 1)] }, { coefficient := -1, powers := [] }]
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
    (values : Fin 68 → R) :
    ¬ ∀ index : Fin 21,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component36.SelectedLeafB6_6_3.selectedHasNoCommonZero

end Krenn.Component36.SelectedLeafB6_6_3
