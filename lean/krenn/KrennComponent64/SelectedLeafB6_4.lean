import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component64.SelectedLeafB6_4

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "cae8e244e6a527b3ee8456ff1cf116e303ce82e2dc8f2f56f8bba32bfaebae6b"
def certificateSHA256 : String := "1cbb05bba32930b8700a28c7b0cd77544332fd8e8c403761b7d3d8f17bda9805"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 26 → Fin 641 := ![
  14,
  19,
  26,
  29,
  163,
  188,
  189,
  199,
  200,
  348,
  349,
  350,
  351,
  352,
  356,
  367,
  433,
  466,
  468,
  548,
  634,
  635,
  636,
  637,
  639,
  640
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 26 → SparsePoly (Fin 63) := ![
  [{ coefficient := 1, powers := [(12, 1), (27, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (52, 1)] }, { coefficient := 1, powers := [(20, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (41, 1)] }, { coefficient := 1, powers := [(19, 1), (20, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (44, 1)] }, { coefficient := 1, powers := [(19, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (52, 1)] }, { coefficient := 1, powers := [(27, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (38, 1)] }, { coefficient := 1, powers := [(27, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (53, 1)] }, { coefficient := 1, powers := [(12, 1), (25, 1), (52, 1)] }, { coefficient := 1, powers := [(16, 1), (21, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (46, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1)] }, { coefficient := 1, powers := [(19, 1), (23, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (53, 1)] }, { coefficient := 1, powers := [(8, 1), (30, 1)] }, { coefficient := 1, powers := [(13, 1), (27, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (59, 1)] }, { coefficient := 1, powers := [(13, 1), (46, 1)] }, { coefficient := 1, powers := [(19, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (59, 1)] }, { coefficient := 1, powers := [(13, 1), (56, 1)] }, { coefficient := 1, powers := [(19, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (43, 1)] }, { coefficient := 1, powers := [(13, 1), (55, 1)] }, { coefficient := 1, powers := [(18, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (41, 1), (52, 1)] }, { coefficient := 1, powers := [(20, 1), (41, 1), (52, 1)] }, { coefficient := 1, powers := [(20, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (20, 1), (55, 1)] }, { coefficient := 1, powers := [(13, 1)] }, { coefficient := 1, powers := [(18, 1), (20, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (53, 1)] }, { coefficient := 1, powers := [(27, 1), (39, 1)] }, { coefficient := 1, powers := [(27, 1), (45, 1), (48, 1)] }, { coefficient := 1, powers := [(30, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (38, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(41, 1), (52, 1)] }, { coefficient := 1, powers := [(56, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (41, 1), (52, 1)] }, { coefficient := 1, powers := [(23, 1), (56, 1)] }, { coefficient := 1, powers := [(27, 1), (46, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (36, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (46, 1), (53, 1)] }, { coefficient := 1, powers := [(5, 1), (27, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (53, 1)] }, { coefficient := 1, powers := [(8, 1), (23, 1), (59, 1)] }, { coefficient := 1, powers := [(8, 1), (30, 1), (46, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (39, 1)] }, { coefficient := 1, powers := [(13, 1), (23, 1), (56, 1)] }, { coefficient := 1, powers := [(13, 1), (27, 1), (46, 1)] }, { coefficient := 1, powers := [(13, 1), (33, 1), (36, 1)] }, { coefficient := 1, powers := [(19, 1), (23, 1), (53, 1)] }, { coefficient := 1, powers := [(19, 1), (27, 1), (39, 1)] }, { coefficient := 1, powers := [(19, 1), (30, 1), (36, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (60, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1), (61, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(38, 1)] }],
  [{ coefficient := 1, powers := [(39, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 26 → SparsePoly (Fin 63) := ![
  [{ coefficient := -2, powers := [(19, 1), (25, 1), (45, 1), (61, 1)] }],
  [{ coefficient := 2, powers := [(19, 1), (21, 1), (23, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(13, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(19, 1), (45, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (5, 1), (30, 1), (44, 1), (60, 1)] }, { coefficient := 1, powers := [(13, 1), (23, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(20, 1), (23, 1), (52, 1)] }],
  [{ coefficient := 2, powers := [(12, 1), (19, 1), (25, 1), (61, 1)] }],
  [{ coefficient := -2, powers := [(13, 1), (20, 1), (46, 1)] }],
  [{ coefficient := -2, powers := [(19, 1), (23, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(53, 1)] }],
  [{ coefficient := 1, powers := [(46, 1)] }],
  [{ coefficient := 1, powers := [(27, 1)] }],
  [{ coefficient := 1, powers := [(23, 1)] }],
  [{ coefficient := 2, powers := [(20, 1), (27, 1), (46, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (30, 1), (60, 1)] }],
  [{ coefficient := -2, powers := [(27, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(19, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (5, 1), (30, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (20, 1), (30, 1), (60, 1)] }, { coefficient := -1, powers := [(13, 1), (23, 1)] }],
  [{ coefficient := 1, powers := [(13, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(5, 1), (30, 1), (56, 1)] }],
  [{ coefficient := 2, powers := [(19, 1), (23, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(36, 1), (59, 1)] }, { coefficient := 1, powers := [(39, 1), (56, 1)] }, { coefficient := -1, powers := [(46, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(0, 2), (5, 1), (30, 1), (56, 1), (60, 1)] }, { coefficient := -1, powers := [(0, 1), (5, 1), (20, 1), (30, 1), (56, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (13, 1), (23, 1), (56, 1)] }, { coefficient := 2, powers := [(13, 1), (20, 1), (27, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (33, 1)] }, { coefficient := -1, powers := [(19, 1), (27, 1)] }]
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

#print axioms Krenn.Component64.SelectedLeafB6_4.selectedHasNoCommonZero

end Krenn.Component64.SelectedLeafB6_4
