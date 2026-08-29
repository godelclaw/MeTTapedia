import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component65.SelectedLeafB4_7

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "6720a19977060b4b186fa8d67bbfc578131d888cd2b5a2c1aa02ca3df99d5ecb"
def certificateSHA256 : String := "cbbc046b66ea78f866ae36f682aea4b43c749a4c5d8dbdafb1f009bc32aa3a52"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 32 → Fin 668 := ![
  12,
  18,
  19,
  23,
  24,
  26,
  29,
  187,
  254,
  275,
  301,
  302,
  309,
  310,
  320,
  412,
  414,
  420,
  421,
  423,
  434,
  440,
  447,
  478,
  540,
  581,
  607,
  661,
  664,
  665,
  666,
  667
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 32 → SparsePoly (Fin 65) := ![
  [{ coefficient := 1, powers := [(5, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (19, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (20, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(28, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (44, 1)] }, { coefficient := 1, powers := [(13, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (19, 1), (56, 1)] }, { coefficient := 1, powers := [(13, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (19, 1), (50, 1)] }, { coefficient := 1, powers := [(18, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1)] }, { coefficient := 1, powers := [(19, 1), (42, 1)] }, { coefficient := 1, powers := [(24, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1)] }, { coefficient := 1, powers := [(20, 1), (42, 1)] }, { coefficient := 1, powers := [(24, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (47, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1)] }, { coefficient := 1, powers := [(13, 1), (28, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1), (51, 1)] }, { coefficient := 1, powers := [(20, 1), (42, 1), (51, 1)] }, { coefficient := 1, powers := [(47, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1), (59, 1)] }, { coefficient := 1, powers := [(20, 1)] }, { coefficient := 1, powers := [(24, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (53, 1)] }, { coefficient := 1, powers := [(3, 1), (25, 1), (59, 1)] }, { coefficient := 1, powers := [(19, 1), (53, 1)] }, { coefficient := 1, powers := [(25, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (60, 1)] }, { coefficient := 1, powers := [(13, 1), (47, 1)] }, { coefficient := 1, powers := [(18, 1), (20, 1), (52, 1)] }, { coefficient := 1, powers := [(18, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (60, 1)] }, { coefficient := 1, powers := [(13, 1), (25, 1), (45, 1)] }, { coefficient := 1, powers := [(13, 1), (57, 1)] }, { coefficient := 1, powers := [(18, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (54, 1)] }, { coefficient := 1, powers := [(28, 1), (40, 1)] }, { coefficient := 1, powers := [(28, 1), (46, 1), (49, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1), (53, 1)] }, { coefficient := 1, powers := [(19, 1), (42, 1), (53, 1)] }, { coefficient := 1, powers := [(19, 1), (57, 1)] }, { coefficient := 1, powers := [(25, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1), (53, 1)] }, { coefficient := 1, powers := [(25, 1), (39, 1)] }, { coefficient := 1, powers := [(25, 1), (44, 1)] }, { coefficient := 1, powers := [(53, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1), (49, 1)] }, { coefficient := 1, powers := [(20, 1), (49, 1)] }, { coefficient := 1, powers := [(24, 1), (40, 1)] }, { coefficient := 1, powers := [(24, 1), (46, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (39, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (45, 1), (53, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (39, 1)] }, { coefficient := 1, powers := [(18, 1), (28, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (42, 1), (53, 1)] }, { coefficient := 1, powers := [(23, 1), (57, 1)] }, { coefficient := 1, powers := [(28, 1), (47, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1)] }, { coefficient := 1, powers := [(6, 1), (59, 1)] }, { coefficient := 1, powers := [(24, 1), (39, 1)] }, { coefficient := 1, powers := [(24, 1), (44, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (35, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1)] }, { coefficient := 1, powers := [(3, 1), (24, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (19, 1), (59, 1)] }, { coefficient := 1, powers := [(19, 1)] }, { coefficient := 1, powers := [(24, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (37, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (47, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (28, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (23, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1), (47, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (40, 1)] }, { coefficient := 1, powers := [(13, 1), (23, 1), (57, 1)] }, { coefficient := 1, powers := [(13, 1), (28, 1), (47, 1)] }, { coefficient := 1, powers := [(13, 1), (34, 1), (37, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (54, 1)] }, { coefficient := 1, powers := [(18, 1), (28, 1), (40, 1)] }, { coefficient := 1, powers := [(18, 1), (31, 1), (37, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(38, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(39, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(40, 1), (64, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 32 → SparsePoly (Fin 65) := ![
  [{ coefficient := 1, powers := [(0, 1), (31, 1), (35, 1), (39, 2), (57, 1), (63, 1)] }, { coefficient := 1, powers := [(0, 1), (31, 1), (35, 1), (39, 1), (42, 1), (53, 1)] }, { coefficient := 1, powers := [(0, 1), (31, 1), (35, 1), (39, 1), (44, 1), (57, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (31, 1), (35, 1), (39, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (24, 1), (31, 1), (39, 2), (57, 1), (63, 1)] }, { coefficient := 1, powers := [(3, 1), (24, 1), (31, 1), (39, 1), (42, 1), (53, 1)] }, { coefficient := 1, powers := [(3, 1), (24, 1), (31, 1), (39, 1), (44, 1), (57, 1), (63, 1)] }, { coefficient := -1, powers := [(3, 1), (24, 1), (31, 1), (39, 1), (57, 1)] }, { coefficient := -1, powers := [(3, 1), (25, 1), (31, 1), (39, 1), (42, 1)] }, { coefficient := 1, powers := [(6, 1), (19, 1), (31, 1), (39, 2), (57, 1), (63, 1)] }, { coefficient := 1, powers := [(6, 1), (19, 1), (31, 1), (39, 1), (42, 1), (53, 1)] }, { coefficient := 1, powers := [(6, 1), (19, 1), (31, 1), (39, 1), (44, 1), (57, 1), (63, 1)] }, { coefficient := -1, powers := [(6, 1), (19, 1), (31, 1), (39, 1), (57, 1)] }, { coefficient := -1, powers := [(6, 1), (20, 1), (31, 1), (39, 1), (49, 1), (57, 1), (64, 1)] }, { coefficient := -1, powers := [(6, 1), (31, 1), (39, 1), (42, 1), (53, 1), (63, 1)] }, { coefficient := -1, powers := [(6, 1), (31, 1), (39, 1), (57, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(23, 1), (42, 1), (44, 1), (53, 1)] }, { coefficient := -2, powers := [(28, 1), (47, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (42, 1), (44, 1)] }, { coefficient := -1, powers := [(23, 1), (45, 1)] }],
  [{ coefficient := 2, powers := [(23, 1), (50, 1), (54, 1), (62, 1)] }, { coefficient := 2, powers := [(28, 1), (40, 1), (50, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(28, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(13, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(18, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (23, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [(23, 1), (57, 1)] }],
  [{ coefficient := -2, powers := [(23, 1), (54, 1), (62, 1)] }, { coefficient := -2, powers := [(28, 1), (40, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (31, 1), (39, 2), (53, 1), (63, 1)] }, { coefficient := -1, powers := [(5, 1), (31, 1), (39, 1), (44, 1), (53, 1), (63, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (39, 1), (53, 1)] }, { coefficient := 1, powers := [(13, 1), (23, 1), (44, 1), (53, 1)] }],
  [{ coefficient := 2, powers := [(13, 1), (28, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(54, 1)] }],
  [{ coefficient := 1, powers := [(47, 1)] }],
  [{ coefficient := -2, powers := [(13, 1), (28, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (31, 1), (39, 1), (49, 1), (57, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (31, 1), (39, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(28, 1)] }],
  [{ coefficient := 1, powers := [(23, 1)] }],
  [{ coefficient := 1, powers := [(18, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (31, 1), (39, 2), (63, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (39, 1), (44, 1), (63, 1)] }, { coefficient := -1, powers := [(5, 1), (31, 1), (39, 1)] }, { coefficient := -1, powers := [(13, 1), (23, 1), (44, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (31, 1), (39, 1), (42, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (31, 1), (39, 1), (57, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(40, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(13, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (31, 1), (39, 1), (42, 1), (53, 1), (63, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (39, 1), (57, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (31, 1), (39, 2), (57, 1), (63, 1)] }, { coefficient := -1, powers := [(5, 1), (31, 1), (39, 1), (42, 1), (53, 1)] }, { coefficient := -1, powers := [(5, 1), (31, 1), (39, 1), (44, 1), (57, 1), (63, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (39, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(37, 1), (60, 1)] }, { coefficient := -1, powers := [(39, 1), (40, 1), (57, 1), (63, 1)] }, { coefficient := -1, powers := [(40, 1), (45, 1), (53, 1), (63, 1)] }, { coefficient := 1, powers := [(40, 1), (57, 1)] }, { coefficient := -1, powers := [(47, 1), (54, 1)] }],
  [{ coefficient := 2, powers := [(18, 1), (23, 1), (54, 1)] }, { coefficient := 2, powers := [(18, 1), (28, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (5, 1), (31, 1), (39, 1), (57, 1)] }, { coefficient := -1, powers := [(5, 1), (31, 1), (57, 1)] }, { coefficient := -1, powers := [(8, 1), (34, 1), (40, 1)] }, { coefficient := -1, powers := [(18, 1), (28, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (24, 1), (31, 1), (39, 1), (57, 1)] }]
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
    ¬ ∀ index : Fin 32,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component65.SelectedLeafB4_7.selectedHasNoCommonZero

end Krenn.Component65.SelectedLeafB4_7
