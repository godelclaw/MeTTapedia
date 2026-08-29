import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component55.SelectedLeafB4_7

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "dc81fdc18578620232b87687a1ade62ca9503dba32a01031a7359cf357d910ff"
def certificateSHA256 : String := "ccd4cb5d854936560a7490ff078e9ae65fa0cf9a0a569a7517d44679cf3cd437"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 27 → Fin 590 := ![
  29,
  93,
  97,
  196,
  197,
  198,
  209,
  228,
  233,
  234,
  244,
  257,
  268,
  341,
  342,
  345,
  348,
  361,
  362,
  390,
  510,
  544,
  545,
  583,
  586,
  587,
  588
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 27 → SparsePoly (Fin 62) := ![
  [{ coefficient := 1, powers := [(24, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (26, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (29, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (26, 1)] }, { coefficient := 1, powers := [(26, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (29, 1)] }, { coefficient := 1, powers := [(29, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (43, 1)] }, { coefficient := 1, powers := [(39, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (43, 1)] }, { coefficient := 1, powers := [(19, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (49, 1)] }, { coefficient := 1, powers := [(21, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(26, 1), (40, 1)] }, { coefficient := 1, powers := [(26, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (40, 1)] }, { coefficient := 1, powers := [(29, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (29, 1), (56, 1)] }, { coefficient := 1, powers := [(29, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (24, 1), (56, 1)] }, { coefficient := 1, powers := [(24, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (26, 1), (45, 1)] }, { coefficient := 1, powers := [(9, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (46, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (51, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1)] }, { coefficient := 1, powers := [(13, 1), (29, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (56, 1)] }, { coefficient := 1, powers := [(18, 1), (21, 1), (49, 1)] }, { coefficient := 1, powers := [(18, 1), (21, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (56, 1)] }, { coefficient := 1, powers := [(18, 1), (26, 1), (40, 1)] }, { coefficient := 1, powers := [(18, 1), (26, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (51, 1)] }, { coefficient := 1, powers := [(29, 1), (41, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (54, 1)] }, { coefficient := 1, powers := [(29, 1), (46, 1)] }, { coefficient := 1, powers := [(35, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (56, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (39, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (39, 1)] }, { coefficient := 1, powers := [(12, 1), (29, 1), (43, 1)] }, { coefficient := 1, powers := [(19, 1), (29, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (39, 1), (53, 1)] }, { coefficient := 1, powers := [(3, 1), (30, 1), (53, 1)] }, { coefficient := 1, powers := [(9, 1), (20, 1), (53, 1)] }, { coefficient := 1, powers := [(9, 1)] }, { coefficient := 1, powers := [(39, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (39, 1), (54, 1)] }, { coefficient := 1, powers := [(3, 1), (30, 1), (54, 1)] }, { coefficient := 1, powers := [(9, 1), (20, 1), (54, 1)] }, { coefficient := 1, powers := [(9, 1), (26, 1), (43, 1)] }, { coefficient := 1, powers := [(26, 1), (39, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (41, 1), (54, 1)] }, { coefficient := 1, powers := [(2, 1), (46, 1), (51, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (51, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (57, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (46, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(13, 1), (24, 1), (54, 1)] }, { coefficient := 1, powers := [(13, 1), (29, 1), (46, 1)] }, { coefficient := 1, powers := [(13, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (51, 1)] }, { coefficient := 1, powers := [(19, 1), (29, 1), (41, 1)] }, { coefficient := 1, powers := [(19, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(39, 1), (59, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(40, 1), (60, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 27 → SparsePoly (Fin 62) := ![
  [{ coefficient := 1, powers := [(12, 1), (51, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (32, 1), (45, 1), (59, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (57, 1), (59, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (32, 1), (44, 1), (45, 1), (59, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (45, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (44, 1), (57, 1), (59, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (26, 1), (32, 1), (53, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(24, 1), (51, 1), (59, 1)] }, { coefficient := -1, powers := [(29, 1), (41, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (18, 1), (29, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (18, 1), (32, 1), (46, 1)] }, { coefficient := -1, powers := [(5, 1), (32, 1), (45, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (57, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(13, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (32, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(39, 1), (51, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (46, 1), (56, 1)] }, { coefficient := 1, powers := [(46, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (29, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (32, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(19, 1)] }],
  [{ coefficient := 1, powers := [(13, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(41, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (32, 1), (54, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (32, 1), (53, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(3, 1), (46, 1), (51, 1), (56, 1)] }, { coefficient := 1, powers := [(6, 1), (38, 1), (56, 1), (57, 1)] }, { coefficient := 1, powers := [(38, 1), (57, 1)] }, { coefficient := -1, powers := [(39, 1), (41, 1), (54, 1), (59, 1)] }, { coefficient := -1, powers := [(39, 1), (46, 1), (51, 1), (59, 1)] }, { coefficient := 1, powers := [(41, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (26, 1), (32, 1), (44, 1), (45, 1), (60, 1)] }, { coefficient := -1, powers := [(5, 1), (26, 1), (32, 1), (45, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (44, 1), (57, 1), (60, 1)] }, { coefficient := -1, powers := [(5, 1), (32, 1), (54, 1)] }, { coefficient := -1, powers := [(5, 1), (35, 1), (51, 1)] }, { coefficient := -1, powers := [(8, 1), (35, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (26, 1), (32, 1), (45, 1)] }, { coefficient := -1, powers := [(5, 1), (29, 1), (57, 1)] }]
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
    (values : Fin 62 → R) :
    ¬ ∀ index : Fin 27,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component55.SelectedLeafB4_7.selectedHasNoCommonZero

end Krenn.Component55.SelectedLeafB4_7
