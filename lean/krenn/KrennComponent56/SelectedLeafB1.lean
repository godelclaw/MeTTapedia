import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component56.SelectedLeafB1

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "8b1670d64fb339f5e17130a7340b670d8718ef2befe5f093a1af8dcb0e24bcee"
def certificateSHA256 : String := "e6ed17e220c9f0e8fad895e911be40c805669fe1809ded72d00c996d68d6adb0"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 26 → Fin 589 := ![
  2,
  3,
  5,
  6,
  7,
  9,
  11,
  20,
  235,
  242,
  254,
  263,
  302,
  360,
  362,
  372,
  373,
  377,
  379,
  397,
  468,
  472,
  473,
  585,
  586,
  588
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 26 → SparsePoly (Fin 58) := ![
  [{ coefficient := 1, powers := [(2, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (23, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (53, 1)] }, { coefficient := 1, powers := [(23, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (37, 1)] }, { coefficient := 1, powers := [(23, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (33, 1), (55, 1)] }, { coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (26, 1), (55, 1)] }, { coefficient := 1, powers := [(26, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (17, 1), (52, 1)] }, { coefficient := 1, powers := [(12, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1)] }, { coefficient := 1, powers := [(18, 1), (40, 1)] }, { coefficient := 1, powers := [(22, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (50, 1)] }, { coefficient := 1, powers := [(17, 1), (50, 1)] }, { coefficient := 1, powers := [(23, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (50, 1)] }, { coefficient := 1, powers := [(26, 1), (38, 1)] }, { coefficient := 1, powers := [(29, 1), (35, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (53, 1)] }, { coefficient := 1, powers := [(26, 1), (44, 1)] }, { coefficient := 1, powers := [(32, 1), (35, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1), (50, 1)] }, { coefficient := 1, powers := [(23, 1), (42, 1), (46, 1)] }, { coefficient := 1, powers := [(50, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1), (48, 1)] }, { coefficient := 1, powers := [(18, 1), (40, 1), (48, 1)] }, { coefficient := 1, powers := [(44, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (35, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (26, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (21, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (56, 1)] }, { coefficient := 1, powers := [(12, 1), (23, 1), (43, 1)] }, { coefficient := 1, powers := [(12, 1), (53, 1)] }, { coefficient := 1, powers := [(16, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (37, 1), (53, 1)] }, { coefficient := 1, powers := [(23, 1), (37, 1), (40, 1)] }, { coefficient := 1, powers := [(23, 1), (43, 1)] }, { coefficient := 1, powers := [(53, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (38, 1), (52, 1)] }, { coefficient := 1, powers := [(18, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(18, 1), (49, 1)] }, { coefficient := 1, powers := [(38, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (35, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (38, 1), (53, 1)] }, { coefficient := 1, powers := [(2, 1), (44, 1), (50, 1)] }, { coefficient := 1, powers := [(5, 1), (26, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (53, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (50, 1)] }, { coefficient := 1, powers := [(8, 1), (21, 1), (56, 1)] }, { coefficient := 1, powers := [(8, 1), (29, 1), (44, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (38, 1)] }, { coefficient := 1, powers := [(12, 1), (21, 1), (53, 1)] }, { coefficient := 1, powers := [(12, 1), (26, 1), (44, 1)] }, { coefficient := 1, powers := [(12, 1), (32, 1), (35, 1)] }, { coefficient := 1, powers := [(16, 1), (21, 1), (50, 1)] }, { coefficient := 1, powers := [(16, 1), (26, 1), (38, 1)] }, { coefficient := 1, powers := [(16, 1), (29, 1), (35, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (57, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 26 → SparsePoly (Fin 58) := ![
  [{ coefficient := -1, powers := [(5, 1), (17, 1), (29, 1), (53, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (17, 1), (32, 1), (50, 1), (57, 1)] }, { coefficient := -1, powers := [(16, 1), (17, 1), (21, 1), (50, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (23, 1), (29, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (18, 1), (52, 1), (53, 1), (57, 1)] }, { coefficient := -1, powers := [(8, 1), (18, 1), (32, 1), (52, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (22, 1), (44, 1), (50, 1), (57, 1)] }, { coefficient := 1, powers := [(8, 1), (22, 1), (29, 1), (44, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (18, 1), (53, 1), (57, 1)] }, { coefficient := -1, powers := [(8, 1), (18, 1), (32, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (26, 1), (56, 1)] }, { coefficient := 1, powers := [(26, 1), (33, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (33, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [(21, 1), (40, 1), (52, 1)] }, { coefficient := -1, powers := [(21, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (29, 1), (42, 1)] }, { coefficient := 1, powers := [(12, 1), (21, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (29, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(35, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [(21, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (48, 1), (50, 1)] }, { coefficient := -1, powers := [(8, 1), (29, 1), (48, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (32, 1), (42, 1)] }, { coefficient := 1, powers := [(16, 1), (21, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(16, 1)] }],
  [{ coefficient := 1, powers := [(12, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (32, 1)] }, { coefficient := -1, powers := [(16, 1), (21, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (50, 1)] }, { coefficient := 1, powers := [(8, 1), (29, 1)] }],
  [{ coefficient := -1, powers := [(33, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(21, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (29, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (53, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(2, 1), (38, 1), (52, 1), (53, 1)] }, { coefficient := -1, powers := [(5, 1), (29, 1), (37, 1), (53, 1)] }, { coefficient := -1, powers := [(8, 1), (32, 1), (38, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (18, 1), (46, 1), (52, 1), (53, 1)] }, { coefficient := 1, powers := [(2, 1), (18, 1), (49, 1), (53, 1)] }, { coefficient := -1, powers := [(2, 1), (22, 1), (44, 1), (48, 1), (50, 1)] }, { coefficient := 1, powers := [(5, 1), (17, 1), (29, 1), (42, 1), (53, 1)] }, { coefficient := -1, powers := [(5, 1), (17, 1), (32, 1), (42, 1), (50, 1)] }, { coefficient := 1, powers := [(5, 1), (23, 1), (29, 1), (43, 1)] }, { coefficient := 1, powers := [(8, 1), (18, 1), (32, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(8, 1), (18, 1), (32, 1), (49, 1)] }, { coefficient := -1, powers := [(8, 1), (22, 1), (29, 1), (44, 1), (48, 1)] }, { coefficient := 1, powers := [(16, 1), (17, 1), (21, 1), (42, 1), (50, 1)] }]
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
    (values : Fin 58 → R) :
    ¬ ∀ index : Fin 26,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component56.SelectedLeafB1.selectedHasNoCommonZero

end Krenn.Component56.SelectedLeafB1
