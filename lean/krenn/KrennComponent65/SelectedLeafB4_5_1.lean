import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component65.SelectedLeafB4_5_1

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "d8d99ec7953e3e1457c035757640aec95b507d5cbf29e95a1a88982ad6a8a1fd"
def certificateSHA256 : String := "0ca82f9c6357b96712e22024b5bc39a549947c3664d6a9fbd8c240e8bbae0596"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 27 → Fin 671 := ![
  12,
  19,
  24,
  26,
  29,
  172,
  254,
  278,
  309,
  310,
  317,
  412,
  420,
  421,
  423,
  447,
  540,
  558,
  581,
  582,
  607,
  661,
  664,
  665,
  666,
  667,
  669
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 27 → SparsePoly (Fin 65) := ![
  [{ coefficient := 1, powers := [(5, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (20, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(28, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (28, 1)] }, { coefficient := 1, powers := [(28, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (19, 1), (56, 1)] }, { coefficient := 1, powers := [(13, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (24, 1), (39, 1)] }, { coefficient := 1, powers := [(18, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (47, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1)] }, { coefficient := 1, powers := [(13, 1), (28, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1), (49, 1)] }, { coefficient := 1, powers := [(24, 1), (44, 1), (49, 1)] }, { coefficient := 1, powers := [(49, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1), (59, 1)] }, { coefficient := 1, powers := [(20, 1)] }, { coefficient := 1, powers := [(24, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (60, 1)] }, { coefficient := 1, powers := [(13, 1), (47, 1)] }, { coefficient := 1, powers := [(18, 1), (20, 1), (52, 1)] }, { coefficient := 1, powers := [(18, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (60, 1)] }, { coefficient := 1, powers := [(13, 1), (25, 1), (45, 1)] }, { coefficient := 1, powers := [(13, 1), (57, 1)] }, { coefficient := 1, powers := [(18, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (54, 1)] }, { coefficient := 1, powers := [(28, 1), (40, 1)] }, { coefficient := 1, powers := [(28, 1), (46, 1), (49, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1), (49, 1)] }, { coefficient := 1, powers := [(20, 1), (49, 1)] }, { coefficient := 1, powers := [(24, 1), (40, 1)] }, { coefficient := 1, powers := [(24, 1), (46, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (42, 1), (53, 1)] }, { coefficient := 1, powers := [(23, 1), (57, 1)] }, { coefficient := 1, powers := [(28, 1), (47, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (25, 1), (42, 1), (50, 1)] }, { coefficient := 1, powers := [(2, 1), (38, 1), (57, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (38, 1)] }, { coefficient := 1, powers := [(18, 1), (28, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1)] }, { coefficient := 1, powers := [(6, 1), (59, 1)] }, { coefficient := 1, powers := [(24, 1), (39, 1)] }, { coefficient := 1, powers := [(24, 1), (44, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (51, 1)] }, { coefficient := 1, powers := [(3, 1), (59, 1)] }, { coefficient := 1, powers := [(19, 1), (51, 1)] }, { coefficient := 1, powers := [(19, 1), (56, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (35, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1)] }, { coefficient := 1, powers := [(3, 1), (24, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (19, 1), (59, 1)] }, { coefficient := 1, powers := [(19, 1)] }, { coefficient := 1, powers := [(24, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (37, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (47, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (28, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (23, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1), (47, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (40, 1)] }, { coefficient := 1, powers := [(13, 1), (23, 1), (57, 1)] }, { coefficient := 1, powers := [(13, 1), (28, 1), (47, 1)] }, { coefficient := 1, powers := [(13, 1), (34, 1), (37, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (54, 1)] }, { coefficient := 1, powers := [(18, 1), (28, 1), (40, 1)] }, { coefficient := 1, powers := [(18, 1), (31, 1), (37, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(38, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(39, 1)] }],
  [{ coefficient := 1, powers := [(40, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(56, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 27 → SparsePoly (Fin 65) := ![
  [{ coefficient := 1, powers := [(0, 1), (31, 1), (35, 1), (51, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (24, 1), (31, 1), (51, 1), (57, 1)] }, { coefficient := -1, powers := [(3, 1), (31, 1), (57, 1)] }, { coefficient := 1, powers := [(6, 1), (19, 1), (31, 1), (51, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [(23, 1), (45, 1)] }],
  [{ coefficient := -1, powers := [(28, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(13, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(18, 1), (46, 1)] }],
  [{ coefficient := -1, powers := [(18, 1), (40, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(23, 1), (57, 1)] }, { coefficient := -2, powers := [(28, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (28, 1), (40, 1), (62, 1)] }, { coefficient := -2, powers := [(23, 1), (54, 1)] }, { coefficient := -1, powers := [(28, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(54, 1)] }],
  [{ coefficient := 1, powers := [(47, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (20, 1), (31, 1), (51, 1), (57, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (31, 1), (49, 1), (51, 1), (57, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(28, 1)] }],
  [{ coefficient := 1, powers := [(23, 1)] }],
  [{ coefficient := 1, powers := [(18, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (31, 1), (51, 1), (57, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(13, 1)] }],
  [{ coefficient := 1, powers := [(40, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (20, 1), (31, 1), (49, 1), (51, 1), (57, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (31, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (31, 1), (51, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(25, 1), (40, 1), (42, 1), (50, 1), (62, 1)] }, { coefficient := 1, powers := [(37, 1), (60, 1)] }, { coefficient := -1, powers := [(38, 1), (40, 1), (57, 1), (62, 1)] }, { coefficient := 1, powers := [(40, 1), (57, 1)] }, { coefficient := -1, powers := [(47, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (34, 1), (40, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (20, 1), (24, 1), (31, 1), (49, 1), (51, 1), (57, 1), (63, 1)] }, { coefficient := -1, powers := [(9, 1), (18, 1), (24, 1), (28, 1), (40, 1), (62, 1)] }, { coefficient := 2, powers := [(18, 1), (23, 1), (24, 1), (54, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (28, 1), (40, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (24, 1), (31, 1), (51, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (19, 1), (31, 1), (57, 1)] }, { coefficient := 1, powers := [(13, 1), (19, 1), (23, 1), (57, 1)] }, { coefficient := 2, powers := [(13, 1), (19, 1), (28, 1), (47, 1)] }]
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
    ¬ ∀ index : Fin 27,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component65.SelectedLeafB4_5_1.selectedHasNoCommonZero

end Krenn.Component65.SelectedLeafB4_5_1
