import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component62.SelectedLeafB4_2_3_5

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "55b17df0defb2a4881497a6134625838dae409e2116014b52d6cb059e037922c"
def certificateSHA256 : String := "7d8544c5744e1cb39dd97929fe92b683b2c2ba4b04ff15df9b0c7589f302eaea"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 18 → Fin 670 := ![
  8,
  11,
  160,
  186,
  361,
  496,
  579,
  586,
  602,
  603,
  604,
  605,
  656,
  659,
  666,
  667,
  668,
  669
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 18 → SparsePoly (Fin 66) := ![
  [{ coefficient := 1, powers := [(10, 1), (27, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (38, 1)] }, { coefficient := 1, powers := [(27, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (27, 1), (58, 1)] }, { coefficient := 1, powers := [(27, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (27, 1), (58, 1)] }, { coefficient := 1, powers := [(10, 1), (27, 1), (43, 1)] }, { coefficient := 1, powers := [(14, 1), (27, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (23, 1), (58, 1)] }, { coefficient := 1, powers := [(10, 1), (23, 1), (43, 1)] }, { coefficient := 1, powers := [(14, 1), (23, 1), (38, 1)] }, { coefficient := 1, powers := [(14, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (50, 1)] }, { coefficient := 1, powers := [(3, 1), (58, 1)] }, { coefficient := 1, powers := [(18, 1), (50, 1)] }, { coefficient := 1, powers := [(18, 1), (55, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1), (38, 1), (56, 1)] }, { coefficient := 1, powers := [(1, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(4, 1), (29, 1), (56, 1)] }, { coefficient := 1, powers := [(10, 1), (21, 1), (56, 1)] }, { coefficient := 1, powers := [(10, 1), (25, 1), (44, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (43, 1)] }, { coefficient := 1, powers := [(4, 1), (25, 1), (58, 1)] }, { coefficient := 1, powers := [(4, 1), (32, 1)] }, { coefficient := 1, powers := [(10, 1), (25, 1), (43, 1)] }, { coefficient := 1, powers := [(14, 1), (21, 1)] }, { coefficient := 1, powers := [(14, 1), (25, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (50, 1)] }, { coefficient := 1, powers := [(7, 1), (20, 1), (58, 1)] }, { coefficient := 1, powers := [(7, 1), (29, 1)] }, { coefficient := 1, powers := [(10, 1), (20, 1), (55, 1)] }, { coefficient := 1, powers := [(10, 1), (26, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (58, 1)] }, { coefficient := 1, powers := [(7, 1), (58, 1)] }, { coefficient := 1, powers := [(10, 1), (43, 1)] }, { coefficient := 1, powers := [(10, 1), (55, 1)] }, { coefficient := 1, powers := [(14, 1), (38, 1)] }, { coefficient := 1, powers := [(14, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (50, 1)] }, { coefficient := 1, powers := [(21, 1), (55, 1)] }, { coefficient := 1, powers := [(26, 1), (38, 1)] }, { coefficient := 1, powers := [(26, 1), (43, 1)] }, { coefficient := 1, powers := [(29, 1), (35, 1)] }, { coefficient := 1, powers := [(32, 1), (35, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (35, 1), (58, 1)] }, { coefficient := 1, powers := [(1, 1), (38, 1), (55, 1)] }, { coefficient := 1, powers := [(1, 1), (43, 1), (50, 1)] }, { coefficient := 1, powers := [(4, 1), (26, 1), (58, 1)] }, { coefficient := 1, powers := [(4, 1), (29, 1), (55, 1)] }, { coefficient := 1, powers := [(4, 1), (32, 1), (50, 1)] }, { coefficient := 1, powers := [(7, 1), (21, 1), (58, 1)] }, { coefficient := 1, powers := [(7, 1), (29, 1), (43, 1)] }, { coefficient := 1, powers := [(7, 1), (32, 1), (38, 1)] }, { coefficient := 1, powers := [(10, 1), (21, 1), (55, 1)] }, { coefficient := 1, powers := [(10, 1), (26, 1), (43, 1)] }, { coefficient := 1, powers := [(10, 1), (32, 1), (35, 1)] }, { coefficient := 1, powers := [(14, 1), (21, 1), (50, 1)] }, { coefficient := 1, powers := [(14, 1), (26, 1), (38, 1)] }, { coefficient := 1, powers := [(14, 1), (29, 1), (35, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1)] }],
  [{ coefficient := 1, powers := [(56, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(23, 1), (64, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(26, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (65, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 18 → SparsePoly (Fin 66) := ![
  [{ coefficient := -1, powers := [(3, 1), (23, 1), (27, 1), (32, 1), (43, 1), (50, 1), (55, 1), (65, 2)] }, { coefficient := 1, powers := [(3, 1), (23, 1), (27, 1), (32, 1), (43, 1), (55, 1), (64, 1), (65, 2)] }, { coefficient := 1, powers := [(3, 1), (23, 1), (32, 1), (43, 1), (50, 1), (55, 1), (65, 1)] }, { coefficient := -2, powers := [(3, 1), (23, 1), (32, 1), (43, 1), (55, 1), (64, 1), (65, 1)] }, { coefficient := -1, powers := [(20, 1), (23, 1), (27, 1), (43, 1), (55, 1), (64, 1), (65, 2)] }, { coefficient := 2, powers := [(20, 1), (23, 1), (43, 1), (55, 1), (64, 1), (65, 1)] }, { coefficient := -1, powers := [(20, 1), (43, 1), (55, 1), (65, 1)] }, { coefficient := -2, powers := [(21, 1), (23, 1), (27, 1), (50, 1), (55, 1), (65, 2)] }, { coefficient := -1, powers := [(21, 1), (23, 1), (27, 1), (55, 2), (65, 2)] }, { coefficient := 1, powers := [(21, 1), (23, 1), (27, 1), (55, 1), (64, 1), (65, 2)] }, { coefficient := 2, powers := [(21, 1), (23, 1), (50, 1), (55, 1), (65, 1)] }, { coefficient := 1, powers := [(21, 1), (23, 1), (55, 2), (65, 1)] }, { coefficient := -2, powers := [(21, 1), (23, 1), (55, 1), (64, 1), (65, 1)] }, { coefficient := -1, powers := [(21, 1), (55, 1), (56, 1), (63, 1), (65, 1)] }, { coefficient := 1, powers := [(21, 1), (55, 1), (65, 1)] }, { coefficient := -1, powers := [(23, 1), (27, 1), (32, 1), (35, 1), (55, 1), (65, 2)] }, { coefficient := 1, powers := [(23, 1), (32, 1), (35, 1), (55, 1), (65, 1)] }, { coefficient := 1, powers := [(25, 1), (27, 1), (50, 1), (55, 1), (65, 2)] }, { coefficient := -1, powers := [(25, 1), (50, 1), (55, 1), (65, 1)] }, { coefficient := 1, powers := [(32, 1), (35, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(25, 1), (52, 1), (55, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (32, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (32, 1), (43, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (23, 1), (32, 1), (43, 1), (50, 1), (65, 1)] }, { coefficient := -1, powers := [(3, 1), (23, 1), (32, 1), (43, 1), (64, 1), (65, 1)] }, { coefficient := 1, powers := [(20, 1), (23, 1), (43, 1), (64, 1), (65, 1)] }, { coefficient := 2, powers := [(21, 1), (23, 1), (50, 1), (65, 1)] }, { coefficient := 1, powers := [(21, 1), (23, 1), (55, 1), (65, 1)] }, { coefficient := -1, powers := [(21, 1), (23, 1), (64, 1), (65, 1)] }, { coefficient := 1, powers := [(23, 1), (32, 1), (35, 1), (65, 1)] }, { coefficient := -1, powers := [(25, 1), (50, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (27, 1), (32, 1), (43, 1), (50, 1), (65, 1)] }, { coefficient := 1, powers := [(3, 1), (27, 1), (32, 1), (43, 1), (64, 1), (65, 1)] }, { coefficient := -1, powers := [(3, 1), (32, 1), (43, 1), (64, 1)] }, { coefficient := -1, powers := [(20, 1), (27, 1), (43, 1), (64, 1), (65, 1)] }, { coefficient := 1, powers := [(20, 1), (43, 1), (64, 1)] }, { coefficient := -2, powers := [(21, 1), (27, 1), (50, 1), (65, 1)] }, { coefficient := -1, powers := [(21, 1), (27, 1), (55, 1), (65, 1)] }, { coefficient := 1, powers := [(21, 1), (27, 1), (64, 1), (65, 1)] }, { coefficient := -1, powers := [(21, 1), (64, 1)] }, { coefficient := -1, powers := [(27, 1), (32, 1), (35, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (27, 1), (32, 1), (43, 1), (65, 1)] }, { coefficient := -1, powers := [(7, 1), (32, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(55, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (50, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(43, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (23, 1), (32, 1), (43, 1), (64, 1)] }, { coefficient := -1, powers := [(20, 1), (23, 1), (43, 1), (64, 1)] }, { coefficient := 1, powers := [(21, 1), (23, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(14, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(27, 1), (43, 1), (50, 1), (65, 1)] }, { coefficient := 1, powers := [(35, 1), (58, 1)] }, { coefficient := -1, powers := [(38, 1), (55, 1), (56, 1), (63, 1)] }, { coefficient := 1, powers := [(38, 1), (55, 1)] }, { coefficient := -1, powers := [(44, 1), (52, 1), (55, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (29, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (7, 1), (32, 1), (43, 1), (58, 1)] }, { coefficient := -1, powers := [(3, 1), (14, 1), (32, 1), (43, 1), (50, 1)] }, { coefficient := 1, powers := [(7, 1), (20, 1), (43, 1), (58, 1)] }, { coefficient := -1, powers := [(7, 1), (21, 1), (58, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1), (43, 1), (50, 1)] }, { coefficient := -1, powers := [(14, 1), (21, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (58, 1)] }, { coefficient := -1, powers := [(14, 1), (43, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (7, 1), (32, 1), (43, 1), (50, 1)] }, { coefficient := 1, powers := [(3, 1), (10, 1), (23, 1), (27, 1), (32, 1), (43, 1), (50, 1), (55, 1), (65, 1)] }, { coefficient := -1, powers := [(3, 1), (10, 1), (23, 1), (27, 1), (32, 1), (43, 1), (55, 1), (64, 1), (65, 1)] }, { coefficient := 1, powers := [(3, 1), (10, 1), (23, 1), (32, 1), (43, 1), (55, 1), (64, 1)] }, { coefficient := 1, powers := [(3, 1), (14, 1), (32, 1), (43, 1), (50, 1)] }, { coefficient := -1, powers := [(3, 1), (14, 1), (32, 1), (43, 1), (64, 1)] }, { coefficient := -1, powers := [(4, 1), (32, 1), (50, 1)] }, { coefficient := -1, powers := [(7, 1), (18, 1), (32, 1), (43, 1), (50, 1)] }, { coefficient := -1, powers := [(7, 1), (18, 1), (32, 1), (43, 1), (55, 1)] }, { coefficient := -1, powers := [(7, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [(7, 1), (32, 1), (43, 1)] }, { coefficient := 1, powers := [(10, 1), (20, 1), (23, 1), (27, 1), (43, 1), (55, 1), (64, 1), (65, 1)] }, { coefficient := -1, powers := [(10, 1), (20, 1), (23, 1), (43, 1), (55, 1), (64, 1)] }, { coefficient := 1, powers := [(10, 1), (20, 1), (43, 1), (55, 1)] }, { coefficient := 2, powers := [(10, 1), (21, 1), (23, 1), (27, 1), (50, 1), (55, 1), (65, 1)] }, { coefficient := 1, powers := [(10, 1), (21, 1), (23, 1), (27, 1), (55, 2), (65, 1)] }, { coefficient := -1, powers := [(10, 1), (21, 1), (23, 1), (27, 1), (55, 1), (64, 1), (65, 1)] }, { coefficient := 1, powers := [(10, 1), (21, 1), (23, 1), (55, 1), (64, 1)] }, { coefficient := 1, powers := [(10, 1), (21, 1), (55, 1), (56, 1), (63, 1)] }, { coefficient := -1, powers := [(10, 1), (21, 1), (55, 1)] }, { coefficient := 1, powers := [(10, 1), (23, 1), (27, 1), (32, 1), (35, 1), (55, 1), (65, 1)] }, { coefficient := -1, powers := [(10, 1), (25, 1), (27, 1), (50, 1), (55, 1), (65, 1)] }, { coefficient := -1, powers := [(10, 1), (32, 1), (35, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1), (43, 1), (64, 1)] }, { coefficient := 1, powers := [(14, 1), (21, 1), (50, 1)] }, { coefficient := 1, powers := [(14, 1), (21, 1), (55, 1)] }, { coefficient := -1, powers := [(14, 1), (21, 1), (64, 1)] }, { coefficient := 1, powers := [(14, 1), (32, 1), (35, 1)] }]
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
    ¬ ∀ index : Fin 18,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component62.SelectedLeafB4_2_3_5.selectedHasNoCommonZero

end Krenn.Component62.SelectedLeafB4_2_3_5
