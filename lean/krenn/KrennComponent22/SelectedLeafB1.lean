import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component22.SelectedLeafB1

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "b937af4a55ace5c5400526e504ad184eab68947f04c74cd45520d4ffcbfc3f5d"
def certificateSHA256 : String := "0cc2be21c85e05349df12b85feb9ad2415f908be646453dee90bdf3ac5929ff9"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 19 → Fin 639 := ![
  0,
  1,
  2,
  3,
  219,
  225,
  237,
  345,
  347,
  363,
  364,
  369,
  371,
  388,
  468,
  477,
  635,
  636,
  638
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 19 → SparsePoly (Fin 61) := ![
  [{ coefficient := 1, powers := [(2, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (36, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (29, 1), (58, 1)] }, { coefficient := 1, powers := [(29, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (22, 1), (58, 1)] }, { coefficient := 1, powers := [(22, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1)] }, { coefficient := 1, powers := [(18, 1), (43, 1)] }, { coefficient := 1, powers := [(23, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (53, 1)] }, { coefficient := 1, powers := [(17, 1), (53, 1)] }, { coefficient := 1, powers := [(24, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (53, 1)] }, { coefficient := 1, powers := [(29, 1), (41, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (56, 1)] }, { coefficient := 1, powers := [(29, 1), (47, 1)] }, { coefficient := 1, powers := [(35, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1), (53, 1)] }, { coefficient := 1, powers := [(24, 1), (45, 1), (49, 1)] }, { coefficient := 1, powers := [(53, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1), (51, 1)] }, { coefficient := 1, powers := [(18, 1), (43, 1), (51, 1)] }, { coefficient := 1, powers := [(47, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (58, 1)] }, { coefficient := 1, powers := [(8, 1), (22, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (41, 1), (55, 1)] }, { coefficient := 1, powers := [(18, 1), (49, 1), (55, 1)] }, { coefficient := 1, powers := [(18, 1), (52, 1)] }, { coefficient := 1, powers := [(41, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1), (52, 1)] }, { coefficient := 1, powers := [(45, 1), (49, 1)] }, { coefficient := 1, powers := [(49, 1), (55, 1)] }, { coefficient := 1, powers := [(52, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (41, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (47, 1), (53, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (53, 1)] }, { coefficient := 1, powers := [(8, 1), (22, 1), (59, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (47, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(12, 1), (22, 1), (56, 1)] }, { coefficient := 1, powers := [(12, 1), (29, 1), (47, 1)] }, { coefficient := 1, powers := [(12, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1), (53, 1)] }, { coefficient := 1, powers := [(16, 1), (29, 1), (41, 1)] }, { coefficient := 1, powers := [(16, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (60, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 19 → SparsePoly (Fin 61) := ![
  [{ coefficient := 1, powers := [(2, 1), (18, 1), (49, 1), (56, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (17, 1), (35, 1), (53, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (18, 1), (35, 1), (49, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (23, 1), (47, 1), (53, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (23, 1), (32, 1), (47, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (29, 1), (59, 1)] }, { coefficient := 1, powers := [(29, 1), (36, 1), (59, 1)] }, { coefficient := -1, powers := [(32, 1), (36, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (22, 1), (59, 1)] }, { coefficient := 1, powers := [(22, 1), (36, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (32, 1), (56, 1), (60, 1)] }, { coefficient := 1, powers := [(38, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (51, 1), (53, 1)] }, { coefficient := -1, powers := [(8, 1), (32, 1), (51, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (35, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(16, 1)] }],
  [{ coefficient := 1, powers := [(12, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (35, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (53, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1)] }],
  [{ coefficient := -1, powers := [(36, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (56, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (18, 1), (56, 1)] }, { coefficient := -1, powers := [(8, 1), (18, 1), (35, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (18, 1), (45, 1), (52, 1), (56, 1)] }, { coefficient := -1, powers := [(2, 1), (41, 1), (55, 1), (56, 1)] }, { coefficient := 1, powers := [(8, 1), (18, 1), (35, 1), (45, 1), (52, 1)] }, { coefficient := -1, powers := [(8, 1), (35, 1), (41, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (18, 1), (45, 1), (49, 1), (56, 1)] }, { coefficient := -1, powers := [(2, 1), (23, 1), (47, 1), (51, 1), (53, 1)] }, { coefficient := -1, powers := [(5, 1), (17, 1), (35, 1), (45, 1), (53, 1)] }, { coefficient := -1, powers := [(5, 1), (32, 1), (36, 1), (56, 1), (58, 1)] }, { coefficient := -1, powers := [(5, 1), (32, 1), (56, 1)] }, { coefficient := -1, powers := [(8, 1), (18, 1), (35, 1), (45, 1), (49, 1)] }, { coefficient := -1, powers := [(8, 1), (23, 1), (32, 1), (47, 1), (51, 1)] }]
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
    (values : Fin 61 → R) :
    ¬ ∀ index : Fin 19,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component22.SelectedLeafB1.selectedHasNoCommonZero

end Krenn.Component22.SelectedLeafB1
