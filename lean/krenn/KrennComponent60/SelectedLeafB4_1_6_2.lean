import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component60.SelectedLeafB4_1_6_2

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "b7221e09f57164e56b7af65a7b689bc85c02eaad19a50b0c696bb36f56d00527"
def certificateSHA256 : String := "23ff47cc49da697737d642f72bdeae6ed74be632524bcb8ae971d05c0c02dfa9"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 20 → Fin 668 := ![
  22,
  147,
  293,
  301,
  302,
  316,
  404,
  443,
  455,
  517,
  556,
  578,
  650,
  655,
  658,
  661,
  662,
  664,
  665,
  667
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 20 → SparsePoly (Fin 66) := ![
  [{ coefficient := 1, powers := [(24, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (32, 1)] }, { coefficient := 1, powers := [(32, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (48, 1)] }, { coefficient := 1, powers := [(21, 1), (43, 1)] }, { coefficient := 1, powers := [(25, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (48, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1)] }, { coefficient := 1, powers := [(12, 1), (29, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (48, 1), (51, 1)] }, { coefficient := 1, powers := [(21, 1), (43, 1), (51, 1)] }, { coefficient := 1, powers := [(48, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (25, 1), (46, 1)] }, { coefficient := 1, powers := [(19, 1), (25, 1), (40, 1)] }, { coefficient := 1, powers := [(19, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (54, 1)] }, { coefficient := 1, powers := [(29, 1), (41, 1)] }, { coefficient := 1, powers := [(29, 1), (47, 1), (50, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1), (50, 1)] }, { coefficient := 1, powers := [(13, 1), (50, 1)] }, { coefficient := 1, powers := [(25, 1), (44, 1), (50, 1)] }, { coefficient := 1, powers := [(50, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (24, 1), (60, 1)] }, { coefficient := 1, powers := [(6, 1), (32, 1), (48, 1)] }, { coefficient := 1, powers := [(6, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(24, 1), (43, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (43, 1), (53, 1)] }, { coefficient := 1, powers := [(24, 1), (57, 1)] }, { coefficient := 1, powers := [(29, 1), (48, 1)] }, { coefficient := 1, powers := [(35, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1)] }, { coefficient := 1, powers := [(6, 1), (59, 1)] }, { coefficient := 1, powers := [(25, 1), (40, 1)] }, { coefficient := 1, powers := [(25, 1), (45, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (21, 1), (44, 1), (50, 1)] }, { coefficient := 1, powers := [(0, 1), (41, 1), (55, 1)] }, { coefficient := 1, powers := [(6, 1), (33, 1), (41, 1)] }, { coefficient := 1, powers := [(13, 1), (21, 1), (50, 1)] }, { coefficient := 1, powers := [(13, 1), (25, 1), (41, 1)] }, { coefficient := 1, powers := [(21, 1), (25, 1), (44, 1), (50, 1)] }, { coefficient := 1, powers := [(21, 1), (50, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (41, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (48, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (48, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1), (29, 1), (48, 1)] }, { coefficient := 1, powers := [(12, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (54, 1)] }, { coefficient := 1, powers := [(19, 1), (29, 1), (41, 1)] }, { coefficient := 1, powers := [(19, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(41, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(55, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(57, 1)] }],
  [{ coefficient := 1, powers := [(25, 1)] }],
  [{ coefficient := 1, powers := [(29, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 20 → SparsePoly (Fin 66) := ![
  [{ coefficient := -1, powers := [(6, 1), (12, 1), (33, 1), (45, 1), (53, 1), (63, 1)] }, { coefficient := 1, powers := [(6, 1), (12, 1), (53, 1), (59, 1)] }, { coefficient := -1, powers := [(8, 1), (33, 1), (45, 1), (50, 1), (63, 1)] }, { coefficient := 1, powers := [(8, 1), (50, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (33, 1), (45, 1), (48, 1), (63, 1)] }, { coefficient := 1, powers := [(8, 1), (48, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (32, 1), (33, 1), (36, 1), (45, 1), (51, 1), (63, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (36, 1), (51, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (33, 1), (45, 1), (54, 1), (63, 1)] }, { coefficient := -1, powers := [(6, 1), (54, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (33, 1), (45, 1), (48, 1), (63, 1)] }, { coefficient := -1, powers := [(6, 1), (48, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (32, 1), (33, 1), (36, 1), (45, 1), (63, 1)] }, { coefficient := -1, powers := [(8, 1), (32, 1), (36, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (24, 1), (33, 1), (45, 1), (54, 1), (63, 1)] }, { coefficient := 1, powers := [(6, 1), (24, 1), (54, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (19, 1), (33, 1), (45, 1), (63, 1)] }, { coefficient := -1, powers := [(6, 1), (19, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (45, 1), (62, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (33, 1), (45, 1), (63, 1)] }, { coefficient := -1, powers := [(8, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (12, 1), (33, 1), (45, 1), (63, 1)] }, { coefficient := -1, powers := [(6, 1), (12, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [] }],
  [{ coefficient := -1, powers := [(45, 1), (62, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (33, 1), (45, 1), (63, 1)] }, { coefficient := 1, powers := [(6, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (33, 1), (38, 1), (45, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(6, 1), (33, 1), (41, 1), (45, 1), (57, 1), (63, 1)] }, { coefficient := -1, powers := [(6, 1), (33, 1), (45, 1), (48, 1), (54, 1), (63, 1)] }, { coefficient := -1, powers := [(6, 1), (38, 1), (59, 1), (60, 1)] }, { coefficient := -1, powers := [(6, 1), (41, 1), (57, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (48, 1), (54, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1), (55, 1), (63, 1)] }, { coefficient := 1, powers := [(6, 1), (33, 1), (45, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (6, 1), (32, 1), (33, 1), (45, 1), (63, 1)] }, { coefficient := -1, powers := [(5, 1), (6, 1), (32, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (18, 1), (24, 1), (33, 1), (45, 1), (46, 1), (54, 1), (63, 1)] }, { coefficient := -1, powers := [(6, 1), (18, 1), (24, 1), (46, 1), (54, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (19, 1), (24, 1), (33, 1), (40, 1), (45, 1), (54, 1), (63, 1)] }, { coefficient := -1, powers := [(6, 1), (19, 1), (24, 1), (40, 1), (54, 1), (59, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (33, 1), (36, 1), (45, 1), (48, 1), (51, 1), (63, 1)] }, { coefficient := -1, powers := [(8, 1), (32, 1), (36, 1), (48, 1), (51, 1), (59, 1)] }, { coefficient := 1, powers := [(13, 1), (41, 1), (45, 1), (62, 1), (63, 1)] }, { coefficient := -1, powers := [(40, 1)] }, { coefficient := -1, powers := [(45, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (6, 1), (33, 1), (45, 1), (60, 1), (63, 1)] }, { coefficient := -1, powers := [(5, 1), (6, 1), (59, 1), (60, 1)] }, { coefficient := -1, powers := [(6, 1), (12, 1), (33, 1), (45, 1), (48, 1), (63, 1)] }, { coefficient := 1, powers := [(6, 1), (12, 1), (48, 1), (59, 1)] }, { coefficient := -1, powers := [(6, 1), (19, 1), (33, 1), (45, 1), (47, 1), (50, 1), (63, 1)] }, { coefficient := 1, powers := [(6, 1), (19, 1), (47, 1), (50, 1), (59, 1)] }]
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
    ¬ ∀ index : Fin 20,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component60.SelectedLeafB4_1_6_2.selectedHasNoCommonZero

end Krenn.Component60.SelectedLeafB4_1_6_2
