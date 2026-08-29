import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component16.SelectedLeafB5_6_3_0

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "30224b4a36332ac9430e7537529cd07eee94c749a20175e6ed551d9b176e607a"
def certificateSHA256 : String := "a53d7a7bc7fbdc88d098c1b88817515317d42d9ee9ebac86fae3c03bd7c5c3f6"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 24 → Fin 674 := ![
  21,
  49,
  273,
  298,
  301,
  321,
  407,
  438,
  441,
  454,
  462,
  497,
  506,
  585,
  591,
  608,
  609,
  660,
  663,
  664,
  665,
  670,
  671,
  672
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 24 → SparsePoly (Fin 68) := ![
  [{ coefficient := 1, powers := [(23, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (33, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (45, 1), (54, 1)] }, { coefficient := 1, powers := [(23, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1)] }, { coefficient := 1, powers := [(21, 1), (45, 1)] }, { coefficient := 1, powers := [(26, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (53, 1)] }, { coefficient := 1, powers := [(7, 1), (33, 1)] }, { coefficient := 1, powers := [(11, 1), (28, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1), (53, 1)] }, { coefficient := 1, powers := [(21, 1), (45, 1), (53, 1)] }, { coefficient := 1, powers := [(45, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (26, 1), (42, 1)] }, { coefficient := 1, powers := [(19, 1), (26, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (53, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (53, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (57, 1)] }, { coefficient := 1, powers := [(19, 1), (30, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (36, 1)] }, { coefficient := 1, powers := [(6, 1), (33, 1)] }, { coefficient := 1, powers := [(33, 1), (38, 1)] }, { coefficient := 1, powers := [(36, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (42, 1)] }, { coefficient := 1, powers := [(19, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (53, 1)] }, { coefficient := 1, powers := [(19, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1), (54, 1)] }, { coefficient := 1, powers := [(21, 1), (45, 1), (54, 1)] }, { coefficient := 1, powers := [(21, 1), (58, 1)] }, { coefficient := 1, powers := [(27, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (28, 1), (60, 1)] }, { coefficient := 1, powers := [(3, 1), (33, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (36, 1), (53, 1)] }, { coefficient := 1, powers := [(28, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (26, 1), (60, 1)] }, { coefficient := 1, powers := [(11, 1), (26, 1), (47, 1)] }, { coefficient := 1, powers := [(16, 1), (26, 1), (42, 1)] }, { coefficient := 1, powers := [(16, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (53, 1)] }, { coefficient := 1, powers := [(3, 1), (60, 1)] }, { coefficient := 1, powers := [(21, 1), (53, 1)] }, { coefficient := 1, powers := [(21, 1), (57, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1), (41, 1), (57, 1)] }, { coefficient := 1, powers := [(1, 1), (52, 1)] }, { coefficient := 1, powers := [(7, 1), (36, 1), (41, 1)] }, { coefficient := 1, powers := [(10, 1), (28, 1)] }, { coefficient := 1, powers := [(16, 1), (28, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (60, 1)] }, { coefficient := 1, powers := [(11, 1), (47, 1)] }, { coefficient := 1, powers := [(11, 1), (57, 1)] }, { coefficient := 1, powers := [(16, 1), (42, 1)] }, { coefficient := 1, powers := [(16, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (53, 1)] }, { coefficient := 1, powers := [(23, 1), (57, 1)] }, { coefficient := 1, powers := [(28, 1), (42, 1)] }, { coefficient := 1, powers := [(28, 1), (47, 1)] }, { coefficient := 1, powers := [(33, 1), (39, 1)] }, { coefficient := 1, powers := [(36, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (39, 1), (60, 1)] }, { coefficient := 1, powers := [(1, 1), (42, 1), (57, 1)] }, { coefficient := 1, powers := [(1, 1), (47, 1), (53, 1)] }, { coefficient := 1, powers := [(4, 1), (28, 1), (60, 1)] }, { coefficient := 1, powers := [(4, 1), (33, 1), (57, 1)] }, { coefficient := 1, powers := [(4, 1), (36, 1), (53, 1)] }, { coefficient := 1, powers := [(7, 1), (23, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (33, 1), (47, 1)] }, { coefficient := 1, powers := [(7, 1), (36, 1), (42, 1)] }, { coefficient := 1, powers := [(11, 1), (23, 1), (57, 1)] }, { coefficient := 1, powers := [(11, 1), (28, 1), (47, 1)] }, { coefficient := 1, powers := [(11, 1), (36, 1), (39, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1), (53, 1)] }, { coefficient := 1, powers := [(16, 1), (28, 1), (42, 1)] }, { coefficient := 1, powers := [(16, 1), (33, 1), (39, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(41, 1), (64, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(58, 1), (67, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(26, 1)] }],
  [{ coefficient := 1, powers := [(28, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 24 → SparsePoly (Fin 68) := ![
  [{ coefficient := 1, powers := [(0, 1), (4, 1), (45, 1), (53, 1), (60, 1), (67, 1)] }, { coefficient := -1, powers := [(3, 1), (11, 1), (45, 1), (47, 1), (60, 1), (67, 1)] }, { coefficient := -1, powers := [(3, 1), (11, 1), (45, 1), (53, 1), (60, 1), (67, 1)] }, { coefficient := -1, powers := [(3, 1), (11, 1), (45, 1), (57, 1), (60, 1), (67, 1)] }, { coefficient := 1, powers := [(4, 1), (21, 1), (45, 1), (53, 1), (60, 1), (67, 1)] }, { coefficient := 1, powers := [(4, 1), (21, 1), (45, 1), (57, 1), (60, 1), (67, 1)] }, { coefficient := 1, powers := [(4, 1), (45, 1), (60, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (39, 1), (60, 1), (67, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (4, 1), (53, 1), (60, 1), (67, 1)] }, { coefficient := 1, powers := [(3, 1), (11, 1), (47, 1), (60, 1), (67, 1)] }, { coefficient := 1, powers := [(3, 1), (11, 1), (53, 1), (60, 1), (67, 1)] }, { coefficient := 1, powers := [(3, 1), (11, 1), (57, 1), (60, 1), (67, 1)] }, { coefficient := -1, powers := [(4, 1), (21, 1), (53, 1), (60, 1), (67, 1)] }, { coefficient := -1, powers := [(4, 1), (21, 1), (57, 1), (60, 1), (67, 1)] }, { coefficient := -1, powers := [(4, 1), (60, 1), (67, 1)] }],
  [{ coefficient := -1, powers := [(27, 1), (53, 2), (67, 1)] }, { coefficient := -1, powers := [(27, 1), (53, 1), (57, 1), (67, 1)] }, { coefficient := 1, powers := [(53, 1), (54, 1), (67, 1)] }, { coefficient := 1, powers := [(54, 1), (57, 1), (67, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (47, 1), (60, 1)] }, { coefficient := 1, powers := [(6, 1), (42, 1), (60, 1)] }, { coefficient := 1, powers := [(38, 1), (42, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (53, 1), (67, 1)] }, { coefficient := 1, powers := [(27, 1), (57, 1), (67, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (24, 1), (42, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (24, 1), (47, 1), (63, 1)] }, { coefficient := 1, powers := [(0, 1), (30, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (42, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (24, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(53, 1), (67, 1)] }, { coefficient := -1, powers := [(57, 1), (67, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (23, 1), (42, 1), (60, 1)] }, { coefficient := -1, powers := [(3, 1), (33, 1), (39, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (23, 1), (60, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(38, 1), (42, 1), (60, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (23, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (11, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (39, 1), (60, 2)] }, { coefficient := -1, powers := [(3, 1), (42, 1), (57, 1), (60, 1)] }, { coefficient := -1, powers := [(6, 1), (42, 1), (53, 1), (60, 1)] }, { coefficient := -1, powers := [(38, 1), (41, 1), (42, 1), (57, 1), (60, 1), (64, 1)] }, { coefficient := -1, powers := [(38, 1), (42, 1), (52, 1), (60, 1), (64, 1)] }, { coefficient := -1, powers := [(38, 1), (42, 1), (53, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (36, 1), (38, 1), (42, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (4, 1), (23, 1), (53, 1), (60, 1)] }, { coefficient := -1, powers := [(3, 1), (11, 1), (23, 1), (47, 1), (60, 1)] }, { coefficient := -1, powers := [(3, 1), (11, 1), (23, 1), (53, 1), (60, 1)] }, { coefficient := -1, powers := [(3, 1), (11, 1), (23, 1), (57, 1), (60, 1)] }, { coefficient := -1, powers := [(3, 1), (11, 1), (33, 1), (39, 1), (60, 1)] }, { coefficient := 1, powers := [(4, 1), (21, 1), (23, 1), (53, 1), (60, 1)] }, { coefficient := 1, powers := [(4, 1), (21, 1), (23, 1), (57, 1), (60, 1)] }, { coefficient := 1, powers := [(4, 1), (23, 1), (60, 1)] }, { coefficient := 1, powers := [(21, 1), (53, 1)] }, { coefficient := 1, powers := [(21, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (19, 1), (24, 1), (42, 2), (63, 1)] }, { coefficient := 2, powers := [(0, 1), (19, 1), (24, 1), (42, 1), (47, 1), (63, 1)] }, { coefficient := 1, powers := [(0, 1), (19, 1), (24, 1), (47, 2), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (19, 1), (30, 1), (42, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (19, 1), (30, 1), (47, 1), (63, 1)] }, { coefficient := -1, powers := [(3, 1), (4, 1), (23, 1), (42, 1), (60, 2)] }, { coefficient := 1, powers := [(3, 1), (4, 1), (33, 1), (39, 1), (60, 2)] }, { coefficient := -1, powers := [(3, 1), (11, 1), (23, 1), (42, 1), (47, 1), (60, 1)] }, { coefficient := 1, powers := [(3, 1), (11, 1), (33, 1), (39, 1), (47, 1), (60, 1)] }, { coefficient := -1, powers := [(3, 1), (16, 1), (23, 1), (42, 2), (60, 1)] }, { coefficient := 1, powers := [(3, 1), (16, 1), (33, 1), (39, 1), (42, 1), (60, 1)] }, { coefficient := 1, powers := [(27, 1), (45, 1), (53, 2), (67, 1)] }, { coefficient := 1, powers := [(27, 1), (45, 1), (53, 1), (57, 1), (67, 1)] }, { coefficient := -1, powers := [(45, 1), (53, 1), (54, 1), (67, 1)] }, { coefficient := -1, powers := [(45, 1), (54, 1), (57, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (11, 1), (42, 1), (60, 1)] }, { coefficient := 1, powers := [(3, 1), (11, 1), (47, 1), (60, 1)] }, { coefficient := -1, powers := [(3, 1), (16, 1), (42, 1), (60, 1)] }, { coefficient := 1, powers := [(4, 1), (60, 1)] }, { coefficient := -1, powers := [(6, 1), (11, 1), (42, 1), (60, 1)] }, { coefficient := -1, powers := [(10, 1), (38, 1), (42, 1), (60, 1), (64, 1)] }, { coefficient := -1, powers := [(11, 1), (38, 1), (42, 1), (60, 1)] }, { coefficient := -1, powers := [(16, 1), (38, 1), (41, 1), (42, 1), (60, 1), (64, 1)] }]
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
    (values : Fin 68 → R) :
    ¬ ∀ index : Fin 24,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component16.SelectedLeafB5_6_3_0.selectedHasNoCommonZero

end Krenn.Component16.SelectedLeafB5_6_3_0
