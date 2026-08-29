import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component39.SelectedLeafB5_7_6_4

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "514a6a2c937a829b961a76965d1f413e428b0369e4a958d7cf704a10f635e319"
def certificateSHA256 : String := "72dc6131000b746fc1c4e279e78a0e90a34171e6f8b659a41a8be05513e372d5"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 17 → Fin 673 := ![
  19,
  268,
  304,
  305,
  476,
  477,
  511,
  537,
  602,
  603,
  659,
  662,
  664,
  666,
  667,
  670,
  671
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 17 → SparsePoly (Fin 69) := ![
  [{ coefficient := 1, powers := [(14, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (19, 1), (52, 1)] }, { coefficient := 1, powers := [(14, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (44, 1)] }, { coefficient := 1, powers := [(4, 1), (33, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (51, 1)] }, { coefficient := 1, powers := [(7, 1), (30, 1)] }, { coefficient := 1, powers := [(10, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (38, 1), (56, 1)] }, { coefficient := 1, powers := [(1, 1), (50, 1)] }, { coefficient := 1, powers := [(7, 1), (33, 1), (38, 1)] }, { coefficient := 1, powers := [(14, 1), (25, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (39, 1), (55, 1)] }, { coefficient := 1, powers := [(1, 1), (43, 1)] }, { coefficient := 1, powers := [(4, 1), (30, 1), (55, 1)] }, { coefficient := 1, powers := [(10, 1), (20, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (23, 1), (59, 1)] }, { coefficient := 1, powers := [(10, 1), (23, 1), (44, 1)] }, { coefficient := 1, powers := [(14, 1), (23, 1), (39, 1)] }, { coefficient := 1, powers := [(14, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (18, 1), (59, 1)] }, { coefficient := 1, powers := [(10, 1), (18, 1), (56, 1)] }, { coefficient := 1, powers := [(10, 1)] }, { coefficient := 1, powers := [(14, 1), (18, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (59, 1)] }, { coefficient := 1, powers := [(10, 1), (44, 1)] }, { coefficient := 1, powers := [(10, 1), (56, 1)] }, { coefficient := 1, powers := [(14, 1), (39, 1)] }, { coefficient := 1, powers := [(14, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (51, 1)] }, { coefficient := 1, powers := [(20, 1), (56, 1)] }, { coefficient := 1, powers := [(25, 1), (39, 1)] }, { coefficient := 1, powers := [(25, 1), (44, 1)] }, { coefficient := 1, powers := [(30, 1), (36, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (36, 1), (59, 1)] }, { coefficient := 1, powers := [(1, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(1, 1), (44, 1), (51, 1)] }, { coefficient := 1, powers := [(4, 1), (25, 1), (59, 1)] }, { coefficient := 1, powers := [(4, 1), (30, 1), (56, 1)] }, { coefficient := 1, powers := [(4, 1), (33, 1), (51, 1)] }, { coefficient := 1, powers := [(7, 1), (20, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (30, 1), (44, 1)] }, { coefficient := 1, powers := [(7, 1), (33, 1), (39, 1)] }, { coefficient := 1, powers := [(10, 1), (20, 1), (56, 1)] }, { coefficient := 1, powers := [(10, 1), (25, 1), (44, 1)] }, { coefficient := 1, powers := [(10, 1), (33, 1), (36, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1), (51, 1)] }, { coefficient := 1, powers := [(14, 1), (25, 1), (39, 1)] }, { coefficient := 1, powers := [(14, 1), (30, 1), (36, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1)] }],
  [{ coefficient := 1, powers := [(38, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(40, 1), (65, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(55, 1), (66, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(23, 1), (68, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(25, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 17 → SparsePoly (Fin 69) := ![
  [{ coefficient := -1, powers := [(18, 1), (19, 1), (20, 1), (56, 1), (65, 1), (68, 1)] }, { coefficient := 1, powers := [(18, 1), (19, 1), (33, 1), (36, 1), (65, 1), (68, 1)] }, { coefficient := 2, powers := [(19, 1), (20, 1), (51, 1), (65, 1)] }, { coefficient := 1, powers := [(19, 1), (20, 1), (56, 1), (65, 1)] }, { coefficient := -1, powers := [(19, 1), (20, 1), (65, 1), (68, 1)] }, { coefficient := 1, powers := [(19, 1), (33, 1), (36, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (20, 1), (56, 1), (65, 1), (68, 1)] }, { coefficient := -1, powers := [(18, 1), (33, 1), (36, 1), (65, 1), (68, 1)] }, { coefficient := -2, powers := [(20, 1), (51, 1), (65, 1)] }, { coefficient := -1, powers := [(20, 1), (56, 1), (65, 1)] }, { coefficient := 1, powers := [(20, 1), (65, 1), (68, 1)] }, { coefficient := -1, powers := [(33, 1), (36, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(51, 1)] }],
  [{ coefficient := 1, powers := [(44, 1)] }],
  [{ coefficient := 1, powers := [(39, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(56, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(18, 1), (20, 1), (56, 1), (68, 1)] }, { coefficient := 1, powers := [(18, 1), (33, 1), (36, 1), (68, 1)] }, { coefficient := -1, powers := [(20, 1), (68, 1)] }],
  [{ coefficient := -1, powers := [(20, 1), (56, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (20, 1), (23, 1), (56, 1), (68, 1)] }, { coefficient := -1, powers := [(18, 1), (23, 1), (33, 1), (36, 1), (68, 1)] }, { coefficient := 1, powers := [(20, 1), (23, 1), (68, 1)] }],
  [{ coefficient := 1, powers := [(14, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(36, 1), (59, 1)] }, { coefficient := -1, powers := [(38, 1), (39, 1), (56, 1), (63, 1)] }, { coefficient := -1, powers := [(39, 1), (50, 1), (63, 1)] }, { coefficient := -1, powers := [(39, 1), (55, 1), (56, 1), (66, 1)] }, { coefficient := 1, powers := [(39, 1), (56, 1)] }, { coefficient := -1, powers := [(43, 1), (56, 1), (66, 1)] }, { coefficient := -1, powers := [(44, 1), (51, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (33, 1), (39, 1)] }],
  [{ coefficient := -1, powers := [(14, 1), (18, 1), (20, 1), (56, 1), (68, 1)] }, { coefficient := 1, powers := [(14, 1), (18, 1), (33, 1), (36, 1), (68, 1)] }, { coefficient := 2, powers := [(14, 1), (20, 1), (51, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1), (56, 1)] }, { coefficient := -1, powers := [(14, 1), (20, 1), (68, 1)] }, { coefficient := 1, powers := [(14, 1), (33, 1), (36, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (30, 1), (56, 1)] }, { coefficient := -1, powers := [(10, 1), (20, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (18, 1), (20, 1), (56, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (18, 1), (33, 1), (36, 1), (59, 1)] }, { coefficient := -1, powers := [(7, 1), (20, 1), (59, 1)] }, { coefficient := -1, powers := [(10, 1), (18, 1), (20, 1), (56, 2)] }, { coefficient := 1, powers := [(10, 1), (18, 1), (33, 1), (36, 1), (56, 1)] }, { coefficient := -1, powers := [(10, 1), (20, 1), (56, 1)] }, { coefficient := -1, powers := [(14, 1), (18, 1), (20, 1), (51, 1), (56, 1)] }, { coefficient := 1, powers := [(14, 1), (18, 1), (33, 1), (36, 1), (51, 1)] }, { coefficient := -1, powers := [(14, 1), (20, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (59, 1)] }, { coefficient := -1, powers := [(14, 1), (38, 1), (39, 1), (63, 1)] }, { coefficient := -1, powers := [(14, 1), (44, 1)] }]
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
    (values : Fin 69 → R) :
    ¬ ∀ index : Fin 17,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component39.SelectedLeafB5_7_6_4.selectedHasNoCommonZero

end Krenn.Component39.SelectedLeafB5_7_6_4
