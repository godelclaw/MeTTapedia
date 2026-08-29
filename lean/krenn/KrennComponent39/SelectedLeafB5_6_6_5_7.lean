import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component39.SelectedLeafB5_6_6_5_7

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "4a29851d48bea20d14bf22f091ba5ecbd3c93155974c9bb76d787ff09aabf141"
def certificateSHA256 : String := "0ea1eb2ae0e4ecc692ba82de5c6f732b3af9b2698e67def736ec91d13f3fb4cc"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 22 → Fin 676 := ![
  18,
  19,
  68,
  82,
  110,
  171,
  173,
  304,
  305,
  306,
  444,
  474,
  603,
  659,
  661,
  662,
  667,
  670,
  671,
  672,
  673,
  675
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 22 → SparsePoly (Fin 72) := ![
  [{ coefficient := 1, powers := [(14, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (28, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (18, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (28, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (23, 1)] }, { coefficient := 1, powers := [(14, 1), (18, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (44, 1)] }, { coefficient := 1, powers := [(4, 1), (33, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (51, 1)] }, { coefficient := 1, powers := [(7, 1), (30, 1)] }, { coefficient := 1, powers := [(10, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (32, 1)] }, { coefficient := 1, powers := [(10, 1), (23, 1), (43, 1)] }, { coefficient := 1, powers := [(10, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (36, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (45, 1), (52, 1)] }, { coefficient := 1, powers := [(42, 1), (52, 1)] }, { coefficient := 1, powers := [(45, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (36, 1), (60, 1)] }, { coefficient := 1, powers := [(1, 1), (45, 1), (52, 1)] }, { coefficient := 1, powers := [(4, 1), (25, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (20, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (51, 1)] }, { coefficient := 1, powers := [(20, 1), (56, 1)] }, { coefficient := 1, powers := [(25, 1), (39, 1)] }, { coefficient := 1, powers := [(25, 1), (44, 1)] }, { coefficient := 1, powers := [(30, 1), (36, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (36, 1), (59, 1)] }, { coefficient := 1, powers := [(1, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(1, 1), (44, 1), (51, 1)] }, { coefficient := 1, powers := [(4, 1), (25, 1), (59, 1)] }, { coefficient := 1, powers := [(4, 1), (30, 1), (56, 1)] }, { coefficient := 1, powers := [(4, 1), (33, 1), (51, 1)] }, { coefficient := 1, powers := [(7, 1), (20, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (30, 1), (44, 1)] }, { coefficient := 1, powers := [(7, 1), (33, 1), (39, 1)] }, { coefficient := 1, powers := [(10, 1), (20, 1), (56, 1)] }, { coefficient := 1, powers := [(10, 1), (25, 1), (44, 1)] }, { coefficient := 1, powers := [(10, 1), (33, 1), (36, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1), (51, 1)] }, { coefficient := 1, powers := [(14, 1), (25, 1), (39, 1)] }, { coefficient := 1, powers := [(14, 1), (30, 1), (36, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (61, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1)] }],
  [{ coefficient := 1, powers := [(55, 1), (65, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(23, 1), (67, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(25, 1)] }],
  [{ coefficient := 1, powers := [(28, 1), (68, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(58, 1), (69, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(60, 1), (71, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 22 → SparsePoly (Fin 72) := ![
  [{ coefficient := -1, powers := [(30, 1), (45, 1), (61, 1), (71, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (30, 1), (45, 1), (61, 1), (71, 1)] }, { coefficient := -1, powers := [(30, 1), (42, 1), (61, 1), (71, 1)] }],
  [{ coefficient := 1, powers := [(30, 1), (32, 1), (36, 1), (65, 1), (68, 1), (69, 1)] }, { coefficient := -1, powers := [(33, 1), (39, 1), (68, 1), (69, 1)] }],
  [{ coefficient := 1, powers := [(33, 1), (51, 1), (67, 1), (71, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (30, 1), (36, 1), (65, 1), (68, 1)] }],
  [{ coefficient := -1, powers := [(18, 1), (33, 1), (51, 1), (67, 1), (71, 1)] }, { coefficient := 1, powers := [(30, 1), (56, 1), (71, 1)] }, { coefficient := 1, powers := [(33, 1), (39, 1), (71, 1)] }],
  [{ coefficient := -1, powers := [(20, 1), (51, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (51, 1), (67, 1)] }, { coefficient := 1, powers := [(51, 1)] }],
  [{ coefficient := 1, powers := [(44, 1)] }, { coefficient := -1, powers := [(56, 1)] }],
  [{ coefficient := -1, powers := [(30, 1), (36, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (30, 1), (61, 1), (71, 1)] }],
  [{ coefficient := 1, powers := [(59, 1), (71, 1)] }],
  [{ coefficient := 1, powers := [(10, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(14, 1), (30, 1), (36, 1)] }],
  [{ coefficient := -1, powers := [(18, 1), (44, 1), (51, 1), (67, 1)] }, { coefficient := -1, powers := [(36, 1), (59, 1), (60, 1), (71, 1)] }, { coefficient := 1, powers := [(36, 1), (59, 1)] }, { coefficient := 1, powers := [(39, 1), (56, 1)] }, { coefficient := -1, powers := [(44, 1), (51, 1)] }, { coefficient := -1, powers := [(45, 1), (52, 1), (59, 1), (71, 1)] }, { coefficient := 1, powers := [(51, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (30, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (20, 1), (51, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (59, 1), (60, 1), (71, 1)] }, { coefficient := 1, powers := [(4, 1), (59, 1)] }, { coefficient := -1, powers := [(10, 1), (39, 1)] }, { coefficient := -1, powers := [(10, 1), (44, 1)] }, { coefficient := 1, powers := [(10, 1), (56, 1)] }, { coefficient := 1, powers := [(14, 1), (39, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (30, 1), (32, 1), (36, 1), (65, 1)] }, { coefficient := 1, powers := [(4, 1), (33, 1), (39, 1)] }, { coefficient := -1, powers := [(10, 1), (23, 1), (30, 1), (36, 1), (43, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (28, 1), (30, 1), (32, 1), (36, 1), (65, 1), (68, 1)] }, { coefficient := 1, powers := [(4, 1), (28, 1), (33, 1), (39, 1), (68, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (14, 1), (30, 1), (36, 1), (61, 1)] }, { coefficient := 1, powers := [(4, 1), (18, 1), (33, 1), (51, 1), (67, 1)] }, { coefficient := -1, powers := [(4, 1), (30, 1), (56, 1)] }, { coefficient := -1, powers := [(4, 1), (33, 1), (39, 1)] }, { coefficient := -1, powers := [(7, 1), (20, 1), (59, 1)] }, { coefficient := -1, powers := [(7, 1), (30, 1), (56, 1)] }, { coefficient := -1, powers := [(7, 1), (33, 1), (39, 1)] }]
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
    (values : Fin 72 → R) :
    ¬ ∀ index : Fin 22,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component39.SelectedLeafB5_6_6_5_7.selectedHasNoCommonZero

end Krenn.Component39.SelectedLeafB5_6_6_5_7
