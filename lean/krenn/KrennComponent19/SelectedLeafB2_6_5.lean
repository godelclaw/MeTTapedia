import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component19.SelectedLeafB2_6_5

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "e2a0ddeddebc327d3bf28c40f92205f9f15638653b4d4ad62b1d65ccf0f8070f"
def certificateSHA256 : String := "804428cae19c1eec89a78c6ed5948a8ca7d8aa40038c6311b11f6e7305043f67"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 21 → Fin 672 := ![
  10,
  18,
  20,
  22,
  188,
  200,
  203,
  267,
  304,
  318,
  420,
  424,
  429,
  469,
  565,
  662,
  663,
  665,
  668,
  669,
  670
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 21 → SparsePoly (Fin 67) := ![
  [{ coefficient := 1, powers := [(13, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (25, 1)] }, { coefficient := 1, powers := [(25, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (48, 1), (55, 1)] }, { coefficient := 1, powers := [(55, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (50, 1), (53, 1)] }, { coefficient := 1, powers := [(50, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (21, 1), (57, 1)] }, { coefficient := 1, powers := [(13, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (61, 1)] }, { coefficient := 1, powers := [(13, 1), (50, 1)] }, { coefficient := 1, powers := [(20, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (55, 1)] }, { coefficient := 1, powers := [(32, 1), (44, 1)] }, { coefficient := 1, powers := [(35, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (50, 1)] }, { coefficient := 1, powers := [(5, 1), (38, 1)] }, { coefficient := 1, powers := [(19, 1), (30, 1), (50, 1)] }, { coefficient := 1, powers := [(20, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1)] }, { coefficient := 1, powers := [(13, 1), (32, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (61, 1)] }, { coefficient := 1, powers := [(13, 1), (27, 1), (49, 1)] }, { coefficient := 1, powers := [(13, 1), (58, 1)] }, { coefficient := 1, powers := [(20, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (44, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (56, 1)] }, { coefficient := 1, powers := [(13, 1), (25, 1), (56, 1)] }, { coefficient := 1, powers := [(18, 1), (30, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (46, 1), (54, 1)] }, { coefficient := 1, powers := [(25, 1), (58, 1)] }, { coefficient := 1, powers := [(32, 1), (50, 1)] }, { coefficient := 1, powers := [(38, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (41, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (44, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (50, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (38, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (25, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (50, 1)] }, { coefficient := 1, powers := [(8, 1), (38, 1), (44, 1)] }, { coefficient := 1, powers := [(13, 1), (25, 1), (58, 1)] }, { coefficient := 1, powers := [(13, 1), (32, 1), (50, 1)] }, { coefficient := 1, powers := [(13, 1), (38, 1), (41, 1)] }, { coefficient := 1, powers := [(20, 1), (25, 1), (55, 1)] }, { coefficient := 1, powers := [(20, 1), (32, 1), (44, 1)] }, { coefficient := 1, powers := [(20, 1), (35, 1), (41, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1)] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(44, 1)] }],
  [{ coefficient := 1, powers := [(56, 1), (65, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(57, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 21 → SparsePoly (Fin 67) := ![
  [{ coefficient := -1, powers := [(25, 1), (27, 1), (56, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(30, 1), (55, 1), (56, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(19, 1), (50, 1), (56, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(13, 1), (46, 1), (56, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(13, 1), (58, 1), (65, 1)] }],
  [{ coefficient := -2, powers := [(20, 1), (25, 1), (56, 1), (65, 1)] }],
  [{ coefficient := -2, powers := [(13, 1), (32, 1), (56, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (25, 1), (58, 1), (65, 1)] }, { coefficient := -1, powers := [(25, 1), (56, 1), (58, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(32, 1), (56, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (56, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(55, 1), (56, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(50, 1), (56, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (56, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(58, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (56, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(56, 1), (65, 1)] }],
  [{ coefficient := 2, powers := [(13, 1), (32, 1), (50, 1), (53, 1), (56, 1), (65, 1)] }, { coefficient := 2, powers := [(20, 1), (25, 1), (48, 1), (55, 1), (56, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(41, 1), (56, 1), (61, 1), (65, 1)] }, { coefficient := -1, powers := [(50, 1), (55, 1), (56, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (38, 1), (56, 1), (65, 1)] }, { coefficient := -1, powers := [(18, 1), (30, 1), (58, 1), (65, 1)] }, { coefficient := -1, powers := [(20, 1), (32, 1), (56, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(13, 1), (14, 1), (21, 1), (25, 1), (58, 1), (65, 1)] }, { coefficient := 1, powers := [(13, 1), (21, 1), (25, 1), (56, 1), (58, 1), (65, 1)] }]
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
    (values : Fin 67 → R) :
    ¬ ∀ index : Fin 21,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component19.SelectedLeafB2_6_5.selectedHasNoCommonZero

end Krenn.Component19.SelectedLeafB2_6_5
