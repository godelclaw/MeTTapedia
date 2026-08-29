import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component65.SelectedLeafB6_5_6_0

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "1e6edacd157c47761b104266ae1bcb1752d5fd29cd9ebfdb589fc8c24039d161"
def certificateSHA256 : String := "baab23d62150560e9fe3edf991f4006fbb896ba8765ef30dcff69fe6406fe240"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 23 → Fin 674 := ![
  15,
  19,
  26,
  278,
  309,
  310,
  317,
  412,
  421,
  423,
  439,
  447,
  540,
  581,
  611,
  645,
  661,
  664,
  666,
  667,
  670,
  671,
  673
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 23 → SparsePoly (Fin 67) := ![
  [{ coefficient := 1, powers := [(8, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (24, 1), (39, 1)] }, { coefficient := 1, powers := [(18, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (47, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1)] }, { coefficient := 1, powers := [(13, 1), (28, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1), (49, 1)] }, { coefficient := 1, powers := [(24, 1), (44, 1), (49, 1)] }, { coefficient := 1, powers := [(49, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1), (59, 1)] }, { coefficient := 1, powers := [(20, 1)] }, { coefficient := 1, powers := [(24, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (60, 1)] }, { coefficient := 1, powers := [(13, 1), (25, 1), (45, 1)] }, { coefficient := 1, powers := [(13, 1), (57, 1)] }, { coefficient := 1, powers := [(18, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (54, 1)] }, { coefficient := 1, powers := [(28, 1), (40, 1)] }, { coefficient := 1, powers := [(28, 1), (46, 1), (49, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(44, 1), (49, 1)] }, { coefficient := 1, powers := [(49, 1), (56, 1)] }, { coefficient := 1, powers := [(52, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1), (49, 1)] }, { coefficient := 1, powers := [(20, 1), (49, 1)] }, { coefficient := 1, powers := [(24, 1), (40, 1)] }, { coefficient := 1, powers := [(24, 1), (46, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (42, 1), (53, 1)] }, { coefficient := 1, powers := [(23, 1), (57, 1)] }, { coefficient := 1, powers := [(28, 1), (47, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1)] }, { coefficient := 1, powers := [(6, 1), (59, 1)] }, { coefficient := 1, powers := [(24, 1), (39, 1)] }, { coefficient := 1, powers := [(24, 1), (44, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (40, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(20, 1), (49, 1), (56, 1)] }, { coefficient := 1, powers := [(20, 1), (52, 1)] }, { coefficient := 1, powers := [(40, 1)] }, { coefficient := 1, powers := [(46, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (36, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (44, 1), (51, 1)] }, { coefficient := 1, powers := [(39, 1)] }, { coefficient := 1, powers := [(44, 1)] }, { coefficient := 1, powers := [(51, 1)] }, { coefficient := 1, powers := [(56, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (37, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (47, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (28, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (23, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1), (47, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (40, 1)] }, { coefficient := 1, powers := [(13, 1), (23, 1), (57, 1)] }, { coefficient := 1, powers := [(13, 1), (28, 1), (47, 1)] }, { coefficient := 1, powers := [(13, 1), (34, 1), (37, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (54, 1)] }, { coefficient := 1, powers := [(18, 1), (28, 1), (40, 1)] }, { coefficient := 1, powers := [(18, 1), (31, 1), (37, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(39, 1)] }],
  [{ coefficient := 1, powers := [(40, 1), (64, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(57, 1)] }],
  [{ coefficient := 1, powers := [(24, 1)] }],
  [{ coefficient := 1, powers := [(28, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 23 → SparsePoly (Fin 67) := ![
  [{ coefficient := 1, powers := [(0, 2), (34, 1), (36, 1), (40, 1)] }, { coefficient := -1, powers := [(0, 1), (6, 1), (34, 1), (40, 1), (51, 1)] }, { coefficient := -1, powers := [(0, 1), (6, 1), (34, 1), (40, 1), (56, 1)] }, { coefficient := -2, powers := [(6, 1), (34, 1), (40, 1)] }],
  [{ coefficient := -1, powers := [(0, 2), (23, 1), (36, 1), (45, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (6, 1), (23, 1), (45, 1), (51, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (6, 1), (23, 1), (45, 1), (56, 1), (59, 1)] }, { coefficient := 2, powers := [(6, 1), (23, 1), (45, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(0, 2), (13, 1), (36, 1), (53, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (6, 1), (13, 1), (51, 1), (53, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (6, 1), (13, 1), (53, 1), (56, 1), (59, 1)] }, { coefficient := 2, powers := [(6, 1), (13, 1), (53, 1), (59, 1)] }],
  [{ coefficient := -2, powers := [(0, 2), (23, 1), (36, 1), (54, 1), (59, 1)] }, { coefficient := 2, powers := [(0, 1), (6, 1), (23, 1), (51, 1), (54, 1), (59, 1)] }, { coefficient := 2, powers := [(0, 1), (6, 1), (23, 1), (54, 1), (56, 1), (59, 1)] }, { coefficient := 4, powers := [(6, 1), (23, 1), (54, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(0, 2), (36, 1), (54, 1), (59, 1)] }, { coefficient := -1, powers := [(0, 1), (6, 1), (51, 1), (54, 1), (59, 1)] }, { coefficient := -1, powers := [(0, 1), (6, 1), (54, 1), (56, 1), (59, 1)] }, { coefficient := -2, powers := [(6, 1), (54, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(0, 2), (36, 1), (47, 1), (59, 1)] }, { coefficient := -1, powers := [(0, 1), (6, 1), (47, 1), (51, 1), (59, 1)] }, { coefficient := -1, powers := [(0, 1), (6, 1), (47, 1), (56, 1), (59, 1)] }, { coefficient := -2, powers := [(6, 1), (47, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1), (46, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1), (52, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(0, 2), (23, 1), (36, 1), (59, 1)] }, { coefficient := -1, powers := [(0, 1), (6, 1), (23, 1), (51, 1), (59, 1)] }, { coefficient := -1, powers := [(0, 1), (6, 1), (23, 1), (56, 1), (59, 1)] }, { coefficient := -2, powers := [(6, 1), (23, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(0, 2), (18, 1), (36, 1), (59, 1)] }, { coefficient := -1, powers := [(0, 1), (6, 1), (18, 1), (51, 1), (59, 1)] }, { coefficient := -1, powers := [(0, 1), (6, 1), (18, 1), (56, 1), (59, 1)] }, { coefficient := -2, powers := [(6, 1), (18, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (20, 1), (44, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (44, 2), (64, 1)] }],
  [{ coefficient := 1, powers := [(0, 2), (13, 1), (36, 1), (59, 1)] }, { coefficient := -1, powers := [(0, 1), (6, 1), (13, 1), (51, 1), (59, 1)] }, { coefficient := -1, powers := [(0, 1), (6, 1), (13, 1), (56, 1), (59, 1)] }, { coefficient := -2, powers := [(6, 1), (13, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (20, 1), (44, 1), (52, 1), (64, 1)] }, { coefficient := 1, powers := [(0, 1), (51, 1)] }, { coefficient := 1, powers := [(0, 1), (56, 1)] }, { coefficient := 2, powers := [] }],
  [{ coefficient := -1, powers := [(0, 1), (44, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(0, 1)] }],
  [{ coefficient := -1, powers := [(0, 2), (36, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (6, 1), (51, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (6, 1), (56, 1), (59, 1)] }, { coefficient := 2, powers := [(6, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(0, 2), (36, 1), (37, 1), (59, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 2), (36, 1), (40, 1), (57, 1), (59, 1)] }, { coefficient := -1, powers := [(0, 2), (36, 1), (47, 1), (54, 1), (59, 1)] }, { coefficient := -1, powers := [(0, 1), (6, 1), (37, 1), (51, 1), (59, 1), (60, 1)] }, { coefficient := -1, powers := [(0, 1), (6, 1), (37, 1), (56, 1), (59, 1), (60, 1)] }, { coefficient := -1, powers := [(0, 1), (6, 1), (40, 1), (51, 1), (57, 1), (59, 1)] }, { coefficient := -1, powers := [(0, 1), (6, 1), (40, 1), (56, 1), (57, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (6, 1), (47, 1), (51, 1), (54, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (6, 1), (47, 1), (54, 1), (56, 1), (59, 1)] }, { coefficient := -2, powers := [(6, 1), (37, 1), (59, 1), (60, 1)] }, { coefficient := -2, powers := [(6, 1), (40, 1), (57, 1), (59, 1)] }, { coefficient := 2, powers := [(6, 1), (47, 1), (54, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(0, 2), (56, 1)] }, { coefficient := 1, powers := [(0, 1)] }],
  [{ coefficient := 1, powers := [(0, 2), (44, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(0, 2), (5, 1), (31, 1), (36, 1), (59, 1)] }, { coefficient := -1, powers := [(0, 2), (13, 1), (23, 1), (36, 1), (59, 1)] }, { coefficient := -1, powers := [(0, 1), (5, 1), (6, 1), (31, 1), (51, 1), (59, 1)] }, { coefficient := -1, powers := [(0, 1), (5, 1), (6, 1), (31, 1), (56, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (6, 1), (13, 1), (23, 1), (51, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (6, 1), (13, 1), (23, 1), (56, 1), (59, 1)] }, { coefficient := -2, powers := [(5, 1), (6, 1), (31, 1), (59, 1)] }, { coefficient := 2, powers := [(6, 1), (13, 1), (23, 1), (59, 1)] }],
  [{ coefficient := 2, powers := [(0, 2), (18, 1), (23, 1), (36, 1), (39, 1), (54, 1), (59, 1)] }, { coefficient := -2, powers := [(0, 1), (6, 1), (18, 1), (23, 1), (39, 1), (51, 1), (54, 1), (59, 1)] }, { coefficient := -2, powers := [(0, 1), (6, 1), (18, 1), (23, 1), (39, 1), (54, 1), (56, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (20, 1), (39, 1), (44, 1), (52, 1), (64, 1)] }, { coefficient := 1, powers := [(0, 1), (20, 1), (44, 2), (52, 1), (64, 1)] }, { coefficient := -1, powers := [(0, 1), (39, 1), (51, 1)] }, { coefficient := -1, powers := [(0, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (40, 1), (44, 2), (64, 1)] }, { coefficient := -1, powers := [(0, 1), (44, 1), (46, 1), (52, 1), (64, 1)] }, { coefficient := -1, powers := [(0, 1), (44, 1), (51, 1)] }, { coefficient := -1, powers := [(0, 1), (44, 1), (56, 1)] }, { coefficient := -4, powers := [(6, 1), (18, 1), (23, 1), (39, 1), (54, 1), (59, 1)] }, { coefficient := -2, powers := [(39, 1)] }, { coefficient := -2, powers := [(44, 1)] }],
  [{ coefficient := 1, powers := [(0, 2), (5, 1), (36, 1), (59, 1), (60, 1)] }, { coefficient := -1, powers := [(0, 2), (13, 1), (36, 1), (47, 1), (59, 1)] }, { coefficient := -1, powers := [(0, 2), (18, 1), (36, 1), (46, 1), (49, 1), (59, 1)] }, { coefficient := -1, powers := [(0, 1), (5, 1), (6, 1), (51, 1), (59, 1), (60, 1)] }, { coefficient := -1, powers := [(0, 1), (5, 1), (6, 1), (56, 1), (59, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (6, 1), (13, 1), (47, 1), (51, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (6, 1), (13, 1), (47, 1), (56, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (6, 1), (18, 1), (46, 1), (49, 1), (51, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (6, 1), (18, 1), (46, 1), (49, 1), (56, 1), (59, 1)] }, { coefficient := -2, powers := [(5, 1), (6, 1), (59, 1), (60, 1)] }, { coefficient := 2, powers := [(6, 1), (13, 1), (47, 1), (59, 1)] }, { coefficient := 2, powers := [(6, 1), (18, 1), (46, 1), (49, 1), (59, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
/-- Lean replays the exact selected-row integer certificate. -/
theorem constantIdentity :
    ∑ index, (multipliers index).toPoly *
      (selectedEquations index).toPoly = C (2 : ℤ) := by
  simp (config := { maxSteps := 1000000 })
    [Fin.sum_univ_succ, multipliers, selectedEquations,
    SparsePoly.toPoly, SparseTerm.toPoly]
  ring

/-- The selected rows have no common zero in a characteristic-zero ring. -/
theorem selectedHasNoCommonZero {R : Type*} [CommRing R] [Nontrivial R] [CharZero R]
    (values : Fin 67 → R) :
    ¬ ∀ index : Fin 23,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((2 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (2 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (2 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component65.SelectedLeafB6_5_6_0.selectedHasNoCommonZero

end Krenn.Component65.SelectedLeafB6_5_6_0
