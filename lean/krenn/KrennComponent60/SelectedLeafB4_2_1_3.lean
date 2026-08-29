import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component60.SelectedLeafB4_2_1_3

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "eda256129e6be0c2f1fddc587d1e9d0a75fa25a7dcda9b1a20e8444c39c056b1"
def certificateSHA256 : String := "fdac211c423c2eb7f022ee08377f0e82491000c9d9f8e8652e29b5e50f6fcfc5"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 31 → Fin 668 := ![
  22,
  25,
  179,
  194,
  264,
  292,
  293,
  294,
  295,
  302,
  312,
  316,
  434,
  443,
  453,
  454,
  462,
  491,
  556,
  578,
  579,
  606,
  607,
  655,
  656,
  658,
  661,
  663,
  664,
  665,
  667
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 31 → SparsePoly (Fin 66) := ![
  [{ coefficient := 1, powers := [(24, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (40, 1)] }, { coefficient := 1, powers := [(29, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (29, 1), (59, 1)] }, { coefficient := 1, powers := [(29, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (25, 1), (48, 1)] }, { coefficient := 1, powers := [(19, 1), (21, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1)] }, { coefficient := 1, powers := [(20, 1), (43, 1)] }, { coefficient := 1, powers := [(25, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (48, 1)] }, { coefficient := 1, powers := [(21, 1), (43, 1)] }, { coefficient := 1, powers := [(25, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (50, 1)] }, { coefficient := 1, powers := [(20, 1), (50, 1)] }, { coefficient := 1, powers := [(25, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (54, 1)] }, { coefficient := 1, powers := [(20, 1), (54, 1)] }, { coefficient := 1, powers := [(26, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1)] }, { coefficient := 1, powers := [(12, 1), (29, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1), (51, 1)] }, { coefficient := 1, powers := [(20, 1), (43, 1), (51, 1)] }, { coefficient := 1, powers := [(43, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (48, 1), (51, 1)] }, { coefficient := 1, powers := [(21, 1), (43, 1), (51, 1)] }, { coefficient := 1, powers := [(48, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (60, 1)] }, { coefficient := 1, powers := [(12, 1), (48, 1)] }, { coefficient := 1, powers := [(19, 1), (21, 1), (52, 1)] }, { coefficient := 1, powers := [(19, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (54, 1)] }, { coefficient := 1, powers := [(29, 1), (41, 1)] }, { coefficient := 1, powers := [(29, 1), (47, 1), (50, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1), (52, 1)] }, { coefficient := 1, powers := [(3, 1), (60, 1)] }, { coefficient := 1, powers := [(20, 1), (43, 1), (52, 1)] }, { coefficient := 1, powers := [(43, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1), (53, 1)] }, { coefficient := 1, powers := [(20, 1), (43, 1), (53, 1)] }, { coefficient := 1, powers := [(20, 1), (57, 1)] }, { coefficient := 1, powers := [(26, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1), (50, 1)] }, { coefficient := 1, powers := [(6, 1), (60, 1)] }, { coefficient := 1, powers := [(25, 1), (46, 1), (50, 1)] }, { coefficient := 1, powers := [(43, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (29, 1), (60, 1)] }, { coefficient := 1, powers := [(3, 1), (32, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (35, 1), (54, 1)] }, { coefficient := 1, powers := [(29, 1), (43, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (43, 1), (53, 1)] }, { coefficient := 1, powers := [(24, 1), (57, 1)] }, { coefficient := 1, powers := [(29, 1), (48, 1)] }, { coefficient := 1, powers := [(35, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1)] }, { coefficient := 1, powers := [(6, 1), (59, 1)] }, { coefficient := 1, powers := [(25, 1), (40, 1)] }, { coefficient := 1, powers := [(25, 1), (45, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (51, 1)] }, { coefficient := 1, powers := [(3, 1), (59, 1)] }, { coefficient := 1, powers := [(20, 1), (51, 1)] }, { coefficient := 1, powers := [(20, 1), (56, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (36, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1)] }, { coefficient := 1, powers := [(3, 1), (25, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1), (59, 1)] }, { coefficient := 1, powers := [(20, 1)] }, { coefficient := 1, powers := [(25, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (36, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (43, 1), (50, 1)] }, { coefficient := 1, powers := [(3, 1), (25, 1), (60, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1), (60, 1)] }, { coefficient := 1, powers := [(20, 1), (43, 1), (50, 1)] }, { coefficient := 1, powers := [(25, 1), (43, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (41, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (48, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (48, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1), (29, 1), (48, 1)] }, { coefficient := 1, powers := [(12, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (54, 1)] }, { coefficient := 1, powers := [(19, 1), (29, 1), (41, 1)] }, { coefficient := 1, powers := [(19, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (61, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(41, 1)] }],
  [{ coefficient := 1, powers := [(56, 1)] }],
  [{ coefficient := 1, powers := [(57, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(25, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (65, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 31 → SparsePoly (Fin 66) := ![
  [{ coefficient := -1, powers := [(12, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (26, 1), (35, 1), (51, 1), (65, 1)] }, { coefficient := -1, powers := [(5, 1), (29, 1), (43, 1), (59, 1), (65, 1)] }, { coefficient := 1, powers := [(5, 1), (43, 1), (59, 1)] }, { coefficient := 1, powers := [(8, 1), (20, 2), (24, 1), (46, 1), (59, 1), (61, 1), (65, 1)] }, { coefficient := -1, powers := [(8, 1), (20, 1), (24, 1), (43, 1), (59, 1), (61, 1), (65, 1)] }, { coefficient := -1, powers := [(19, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (8, 1), (20, 1), (24, 1), (60, 1), (61, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (32, 1), (57, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(29, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (26, 1), (32, 1), (51, 2), (57, 1), (63, 1)] }, { coefficient := -1, powers := [(5, 1), (26, 1), (32, 1), (51, 2)] }, { coefficient := -1, powers := [(5, 1), (29, 1), (52, 1), (59, 1)] }, { coefficient := -1, powers := [(5, 1), (32, 1), (51, 1), (53, 1), (57, 1), (63, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (51, 1), (53, 1)] }, { coefficient := -1, powers := [(8, 1), (24, 1), (26, 1), (40, 1), (51, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (40, 1), (53, 1), (60, 1), (63, 1)] }],
  [{ coefficient := 2, powers := [(12, 1), (29, 1), (51, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (20, 1), (24, 1), (46, 1), (59, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (43, 1), (59, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (35, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(48, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (26, 1), (32, 1), (51, 1), (57, 1), (63, 1)] }, { coefficient := 1, powers := [(5, 1), (26, 1), (32, 1), (51, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (26, 1), (40, 1), (60, 1), (63, 1)] }],
  [{ coefficient := -2, powers := [(12, 1), (29, 1)] }],
  [{ coefficient := 1, powers := [(29, 1)] }],
  [{ coefficient := 1, powers := [(19, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (29, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (32, 1), (51, 1), (57, 1), (63, 1)] }, { coefficient := -1, powers := [(5, 1), (32, 1), (51, 1)] }, { coefficient := -1, powers := [(8, 1), (24, 1), (40, 1), (60, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (20, 1), (24, 1), (59, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(12, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (20, 1), (24, 1), (60, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (29, 1), (32, 1), (57, 1), (65, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (24, 1), (60, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (24, 1), (59, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(8, 1), (20, 1), (24, 1), (40, 1), (60, 1)] }, { coefficient := -1, powers := [(8, 1), (24, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(38, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (57, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1)] }, { coefficient := -1, powers := [(19, 1), (29, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (20, 1), (29, 1), (32, 1), (57, 1), (65, 1)] }, { coefficient := -1, powers := [(5, 1), (20, 1), (32, 1), (57, 1)] }, { coefficient := -1, powers := [(5, 1), (20, 1), (35, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (20, 1), (32, 1), (51, 1), (57, 1)] }, { coefficient := 1, powers := [(8, 1), (20, 1), (24, 1), (40, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (26, 1), (32, 1), (43, 1), (51, 2), (57, 1), (63, 1)] }, { coefficient := 1, powers := [(5, 1), (26, 1), (32, 1), (43, 1), (51, 2)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (43, 1), (52, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (43, 1), (51, 1), (53, 1), (57, 1), (63, 1)] }, { coefficient := -1, powers := [(5, 1), (32, 1), (43, 1), (51, 1), (53, 1)] }, { coefficient := 1, powers := [(8, 1), (20, 1), (24, 1), (40, 1), (60, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (20, 1), (24, 1), (45, 1), (60, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (26, 1), (40, 1), (43, 1), (51, 1), (60, 1), (63, 1)] }, { coefficient := -1, powers := [(8, 1), (24, 1), (40, 1), (43, 1), (53, 1), (60, 1), (63, 1)] }, { coefficient := -1, powers := [(8, 1), (24, 1), (60, 1), (61, 1)] }, { coefficient := -2, powers := [(12, 1), (29, 1), (48, 1), (51, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (48, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (5, 1), (32, 1), (51, 1), (57, 1)] }, { coefficient := -1, powers := [(0, 1), (8, 1), (20, 1), (24, 1), (40, 1), (60, 1), (61, 1)] }, { coefficient := -1, powers := [(0, 1), (8, 1), (20, 1), (24, 1), (45, 1), (60, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (20, 1), (32, 1), (51, 1), (57, 1)] }, { coefficient := -1, powers := [(5, 1), (26, 1), (35, 1), (50, 1), (51, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (43, 1), (50, 1), (59, 1)] }, { coefficient := -1, powers := [(8, 1), (20, 2), (24, 1), (46, 1), (50, 1), (59, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (20, 1), (24, 1), (43, 1), (50, 1), (59, 1), (61, 1)] }]
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
    ¬ ∀ index : Fin 31,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component60.SelectedLeafB4_2_1_3.selectedHasNoCommonZero

end Krenn.Component60.SelectedLeafB4_2_1_3
