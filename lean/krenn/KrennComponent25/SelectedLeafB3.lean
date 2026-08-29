import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component25.SelectedLeafB3

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "d9de5bd3bf4fd0b6b614e017b3621ced68113c2d7f9956ccbabc05322c05fc19"
def certificateSHA256 : String := "dbd58daa3062c9ddfacde9acdb0924d1369848dd059f9e8dfbbd95df569400ac"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 18 → Fin 659 := ![
  1,
  21,
  162,
  175,
  177,
  300,
  312,
  402,
  449,
  450,
  475,
  478,
  497,
  578,
  579,
  655,
  656,
  658
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 18 → SparsePoly (Fin 63) := ![
  [{ coefficient := 1, powers := [(8, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (18, 1)] }, { coefficient := 1, powers := [(16, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(57, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1), (54, 1)] }, { coefficient := 1, powers := [(54, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (60, 1)] }, { coefficient := 1, powers := [(12, 1), (57, 1)] }, { coefficient := 1, powers := [(17, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (57, 1)] }, { coefficient := 1, powers := [(29, 1), (48, 1)] }, { coefficient := 1, powers := [(35, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (18, 1), (52, 1)] }, { coefficient := 1, powers := [(16, 1), (18, 1), (56, 1)] }, { coefficient := 1, powers := [(16, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (40, 1)] }, { coefficient := 1, powers := [(16, 1), (45, 1)] }, { coefficient := 1, powers := [(16, 1), (52, 1)] }, { coefficient := 1, powers := [(16, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (54, 1)] }, { coefficient := 1, powers := [(29, 1), (41, 1)] }, { coefficient := 1, powers := [(29, 1), (47, 1), (50, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (36, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (59, 1)] }, { coefficient := 1, powers := [(8, 1), (23, 1), (59, 1)] }, { coefficient := 1, powers := [(16, 1), (29, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (27, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (22, 1), (59, 1)] }, { coefficient := 1, powers := [(22, 1)] }, { coefficient := 1, powers := [(27, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1)] }, { coefficient := 1, powers := [(6, 1), (59, 1)] }, { coefficient := 1, powers := [(24, 1), (40, 1)] }, { coefficient := 1, powers := [(24, 1), (45, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (52, 1)] }, { coefficient := 1, powers := [(3, 1), (59, 1)] }, { coefficient := 1, powers := [(18, 1), (52, 1)] }, { coefficient := 1, powers := [(18, 1), (56, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (41, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (48, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (23, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (48, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(12, 1), (23, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1), (29, 1), (48, 1)] }, { coefficient := 1, powers := [(12, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(17, 1), (23, 1), (54, 1)] }, { coefficient := 1, powers := [(17, 1), (29, 1), (41, 1)] }, { coefficient := 1, powers := [(17, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (62, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 18 → SparsePoly (Fin 63) := ![
  [{ coefficient := 1, powers := [(23, 1), (36, 1), (60, 1)] }, { coefficient := -1, powers := [(32, 1), (36, 1), (48, 1)] }, { coefficient := -1, powers := [(35, 1), (36, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (36, 1), (60, 1)] }, { coefficient := 1, powers := [(17, 1), (36, 1), (50, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(22, 1), (40, 1), (62, 1)] }, { coefficient := -1, powers := [(22, 1), (45, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (36, 1), (41, 1), (59, 1)] }, { coefficient := -1, powers := [(5, 1), (32, 1), (36, 1), (59, 1)] }, { coefficient := 1, powers := [(12, 1), (23, 1), (36, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (36, 1), (48, 1), (59, 1)] }, { coefficient := -1, powers := [(5, 1), (35, 1), (36, 1), (59, 1)] }, { coefficient := 1, powers := [(17, 1), (23, 1), (36, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(23, 1), (36, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (36, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(22, 1), (62, 1)] }, { coefficient := -1, powers := [(27, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (22, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(17, 1), (36, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(62, 1)] }],
  [{ coefficient := -1, powers := [(36, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(16, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (22, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (27, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(36, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (36, 1), (40, 1), (41, 1), (57, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (36, 1), (45, 1), (48, 1), (54, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (36, 1), (40, 1), (57, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (36, 1), (45, 1), (54, 1), (59, 1)] }, { coefficient := -1, powers := [(12, 1), (23, 1), (36, 1), (40, 1), (57, 1), (59, 1)] }, { coefficient := -1, powers := [(16, 1), (22, 1), (45, 1), (62, 1)] }, { coefficient := -1, powers := [(16, 1), (27, 1), (52, 1), (62, 1)] }, { coefficient := -1, powers := [(17, 1), (23, 1), (36, 1), (45, 1), (54, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(36, 1), (59, 1)] }, { coefficient := -1, powers := [] }]
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
    (values : Fin 63 → R) :
    ¬ ∀ index : Fin 18,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component25.SelectedLeafB3.selectedHasNoCommonZero

end Krenn.Component25.SelectedLeafB3
