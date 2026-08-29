import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component18.SelectedLeafB6_0_5

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "bc08fa0210c52dcfec067a15fabceab65efb63b4b10e754eb922d64cbe99daba"
def certificateSHA256 : String := "02298b0c80b2bb2940eff6605d1258bd718bc9bcc55c8049308f50a95eb9f5ed"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 19 → Fin 667 := ![
  10,
  11,
  17,
  19,
  167,
  301,
  318,
  343,
  409,
  433,
  437,
  443,
  585,
  657,
  660,
  662,
  663,
  664,
  666
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 19 → SparsePoly (Fin 65) := ![
  [{ coefficient := 1, powers := [(13, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (45, 1)] }, { coefficient := 1, powers := [(29, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (60, 1)] }, { coefficient := 1, powers := [(13, 1), (49, 1)] }, { coefficient := 1, powers := [(18, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (54, 1)] }, { coefficient := 1, powers := [(31, 1), (43, 1)] }, { coefficient := 1, powers := [(34, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (43, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (55, 1)] }, { coefficient := 1, powers := [(13, 1), (24, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (25, 1), (47, 1)] }, { coefficient := 1, powers := [(18, 1), (25, 1), (42, 1)] }, { coefficient := 1, powers := [(18, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (49, 1)] }, { coefficient := 1, powers := [(5, 1), (37, 1)] }, { coefficient := 1, powers := [(17, 1), (29, 1), (49, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1)] }, { coefficient := 1, powers := [(13, 1), (31, 1)] }, { coefficient := 1, powers := [(17, 1), (23, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (60, 1)] }, { coefficient := 1, powers := [(13, 1), (26, 1), (47, 1)] }, { coefficient := 1, powers := [(13, 1), (57, 1)] }, { coefficient := 1, powers := [(18, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1), (55, 1)] }, { coefficient := 1, powers := [(6, 1), (35, 1), (42, 1)] }, { coefficient := 1, powers := [(14, 1), (25, 1), (42, 1)] }, { coefficient := 1, powers := [(14, 1)] }, { coefficient := 1, powers := [(55, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (40, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (43, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (49, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (37, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (49, 1)] }, { coefficient := 1, powers := [(8, 1), (37, 1), (43, 1)] }, { coefficient := 1, powers := [(13, 1), (24, 1), (57, 1)] }, { coefficient := 1, powers := [(13, 1), (31, 1), (49, 1)] }, { coefficient := 1, powers := [(13, 1), (37, 1), (40, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (54, 1)] }, { coefficient := 1, powers := [(18, 1), (31, 1), (43, 1)] }, { coefficient := 1, powers := [(18, 1), (34, 1), (40, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(42, 1)] }],
  [{ coefficient := 1, powers := [(43, 1)] }],
  [{ coefficient := 1, powers := [(55, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(57, 1), (64, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 19 → SparsePoly (Fin 65) := ![
  [{ coefficient := 1, powers := [(14, 1), (24, 1), (26, 1), (57, 1), (63, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (31, 1), (49, 1), (57, 1), (63, 2), (64, 1)] }, { coefficient := -1, powers := [(14, 1), (37, 1), (40, 1), (57, 1), (63, 2), (64, 1)] }, { coefficient := -1, powers := [(24, 1), (57, 1), (63, 1)] }],
  [{ coefficient := -2, powers := [(14, 1), (24, 1), (25, 1), (47, 1), (54, 1), (57, 1), (63, 2), (64, 1)] }, { coefficient := -1, powers := [(14, 1), (24, 1), (45, 1), (54, 1), (57, 1), (63, 2), (64, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (17, 1), (49, 1), (57, 1), (63, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (17, 1), (54, 1), (57, 1), (63, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(14, 1), (31, 1), (57, 1), (63, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(14, 1), (18, 1), (57, 1), (63, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(57, 1), (63, 1)] }],
  [{ coefficient := 2, powers := [(14, 1), (24, 1), (54, 1), (57, 1), (63, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(14, 1), (54, 1), (57, 1), (63, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(14, 1), (49, 1), (57, 1), (63, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(14, 1), (24, 1), (57, 1), (63, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (34, 1), (57, 1), (63, 1)] }, { coefficient := 1, powers := [(63, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (57, 1), (63, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(14, 1), (40, 1), (57, 1), (60, 1), (63, 1), (64, 1)] }, { coefficient := 1, powers := [(14, 1), (49, 1), (54, 1), (57, 1), (63, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (5, 1), (34, 1), (55, 1), (57, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (55, 1), (63, 1)] }, { coefficient := 1, powers := [(5, 1), (6, 1), (34, 1), (35, 1), (57, 1), (63, 1)] }, { coefficient := 1, powers := [(5, 1), (14, 1), (25, 1), (34, 1), (57, 1), (63, 1)] }, { coefficient := -1, powers := [(6, 1), (35, 1), (63, 1)] }, { coefficient := -2, powers := [(14, 1), (18, 1), (24, 1), (25, 1), (54, 1), (57, 1), (63, 1), (64, 1)] }, { coefficient := -1, powers := [(14, 1), (25, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (14, 1), (57, 2), (63, 1), (64, 1)] }, { coefficient := -1, powers := [(2, 1), (55, 1), (57, 1), (63, 1)] }, { coefficient := -1, powers := [(8, 1), (14, 1), (37, 1), (57, 1), (63, 1), (64, 1)] }, { coefficient := 1, powers := [(14, 1), (18, 1), (31, 1), (57, 1), (63, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(13, 1), (14, 1), (31, 1), (49, 1), (57, 1), (63, 1), (64, 1)] }, { coefficient := 1, powers := [(13, 1), (14, 1), (37, 1), (40, 1), (57, 1), (63, 1), (64, 1)] }, { coefficient := 2, powers := [(14, 1), (17, 1), (24, 1), (25, 1), (47, 1), (54, 1), (57, 1), (63, 1), (64, 1)] }, { coefficient := 1, powers := [(14, 1), (17, 1), (24, 1), (45, 1), (54, 1), (57, 1), (63, 1), (64, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(5, 1), (14, 1), (34, 1), (57, 1), (63, 1)] }, { coefficient := 1, powers := [(14, 1), (63, 1)] }]
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
    (values : Fin 65 → R) :
    ¬ ∀ index : Fin 19,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component18.SelectedLeafB6_0_5.selectedHasNoCommonZero

end Krenn.Component18.SelectedLeafB6_0_5
