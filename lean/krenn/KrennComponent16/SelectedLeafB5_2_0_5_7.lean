import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component16.SelectedLeafB5_2_0_5_7

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "518ac02300d9aa286cadc282e2ea38461090073e19e70c14fab73b5b04a95616"
def certificateSHA256 : String := "d1ec83b700afd0185ab3d58ac05271b90dd88b3f29b1e1184a09694b3c275bcb"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 25 → Fin 677 := ![
  4,
  6,
  166,
  300,
  301,
  318,
  327,
  433,
  441,
  454,
  455,
  474,
  478,
  498,
  584,
  585,
  610,
  649,
  653,
  660,
  663,
  664,
  669,
  672,
  676
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 25 → SparsePoly (Fin 70) := ![
  [{ coefficient := 1, powers := [(3, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (21, 1)] }, { coefficient := 1, powers := [(19, 1), (26, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (47, 1)] }, { coefficient := 1, powers := [(4, 1), (36, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (53, 1)] }, { coefficient := 1, powers := [(7, 1), (33, 1)] }, { coefficient := 1, powers := [(11, 1), (28, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (38, 1), (61, 1)] }, { coefficient := 1, powers := [(3, 1), (26, 1), (61, 1)] }, { coefficient := 1, powers := [(6, 1), (21, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (39, 1), (61, 1)] }, { coefficient := 1, powers := [(4, 1), (28, 1), (61, 1)] }, { coefficient := 1, powers := [(7, 1), (23, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (29, 1), (42, 1)] }, { coefficient := 1, powers := [(19, 1), (29, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (30, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (36, 1)] }, { coefficient := 1, powers := [(6, 1), (33, 1)] }, { coefficient := 1, powers := [(33, 1), (38, 1)] }, { coefficient := 1, powers := [(36, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (42, 1)] }, { coefficient := 1, powers := [(19, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (53, 1)] }, { coefficient := 1, powers := [(19, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(30, 1), (42, 1)] }, { coefficient := 1, powers := [(30, 1), (47, 1)] }, { coefficient := 1, powers := [(30, 1), (53, 1)] }, { coefficient := 1, powers := [(30, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (38, 1), (60, 1)] }, { coefficient := 1, powers := [(1, 1)] }, { coefficient := 1, powers := [(11, 1), (36, 1), (38, 1)] }, { coefficient := 1, powers := [(16, 1), (33, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1)] }, { coefficient := 1, powers := [(19, 1), (29, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (29, 1), (60, 1)] }, { coefficient := 1, powers := [(6, 1), (24, 1), (60, 1)] }, { coefficient := 1, powers := [(24, 1)] }, { coefficient := 1, powers := [(29, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1)] }, { coefficient := 1, powers := [(6, 1), (60, 1)] }, { coefficient := 1, powers := [(26, 1), (42, 1)] }, { coefficient := 1, powers := [(26, 1), (47, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (53, 1)] }, { coefficient := 1, powers := [(3, 1), (60, 1)] }, { coefficient := 1, powers := [(21, 1), (53, 1)] }, { coefficient := 1, powers := [(21, 1), (57, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (38, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1)] }, { coefficient := 1, powers := [(3, 1), (26, 1), (60, 1)] }, { coefficient := 1, powers := [(6, 1), (21, 1), (60, 1)] }, { coefficient := 1, powers := [(21, 1)] }, { coefficient := 1, powers := [(26, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (39, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (42, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (47, 1), (53, 1)] }, { coefficient := 1, powers := [(42, 1)] }, { coefficient := 1, powers := [(47, 1)] }, { coefficient := 1, powers := [(53, 1)] }, { coefficient := 1, powers := [(57, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (39, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (42, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (47, 1), (53, 1)] }, { coefficient := 1, powers := [(19, 1), (30, 1), (42, 1)] }, { coefficient := 1, powers := [(19, 1), (30, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (30, 1), (53, 1)] }, { coefficient := 1, powers := [(19, 1), (30, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (39, 1), (60, 1)] }, { coefficient := 1, powers := [(1, 1), (42, 1), (57, 1)] }, { coefficient := 1, powers := [(1, 1), (47, 1), (53, 1)] }, { coefficient := 1, powers := [(4, 1), (28, 1), (60, 1)] }, { coefficient := 1, powers := [(4, 1), (33, 1), (57, 1)] }, { coefficient := 1, powers := [(4, 1), (36, 1), (53, 1)] }, { coefficient := 1, powers := [(7, 1), (23, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (33, 1), (47, 1)] }, { coefficient := 1, powers := [(7, 1), (36, 1), (42, 1)] }, { coefficient := 1, powers := [(11, 1), (23, 1), (57, 1)] }, { coefficient := 1, powers := [(11, 1), (28, 1), (47, 1)] }, { coefficient := 1, powers := [(11, 1), (36, 1), (39, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1), (53, 1)] }, { coefficient := 1, powers := [(16, 1), (28, 1), (42, 1)] }, { coefficient := 1, powers := [(16, 1), (33, 1), (39, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(57, 1)] }],
  [{ coefficient := 1, powers := [(28, 1)] }],
  [{ coefficient := 1, powers := [(61, 1), (69, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 25 → SparsePoly (Fin 70) := ![
  [{ coefficient := -1, powers := [(2, 1), (60, 1), (63, 1), (69, 1)] }, { coefficient := 2, powers := [(7, 1), (36, 1), (42, 1), (60, 1), (69, 1)] }, { coefficient := 2, powers := [(19, 1), (29, 1), (60, 1), (63, 1), (69, 1)] }, { coefficient := 2, powers := [(60, 1), (69, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (60, 1), (63, 1), (69, 1)] }, { coefficient := 2, powers := [(7, 1), (33, 1), (42, 1), (60, 1), (69, 1)] }, { coefficient := 2, powers := [(19, 1), (24, 1), (60, 1), (63, 1), (69, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (53, 1), (63, 1)] }, { coefficient := -1, powers := [(30, 1), (63, 1)] }],
  [{ coefficient := -2, powers := [(38, 1), (53, 1), (60, 1)] }],
  [{ coefficient := 2, powers := [(38, 1), (42, 1), (60, 1)] }, { coefficient := -2, powers := [(38, 1), (47, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (42, 1), (60, 1), (63, 1), (69, 1)] }, { coefficient := -2, powers := [(53, 1), (60, 1), (69, 1)] }],
  [{ coefficient := -2, powers := [(38, 1), (60, 2), (69, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (63, 1)] }, { coefficient := 1, powers := [(26, 1), (63, 1)] }],
  [{ coefficient := -2, powers := [(7, 1), (42, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(21, 1), (29, 1), (63, 1)] }, { coefficient := -1, powers := [(26, 1), (29, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(0, 2), (19, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (19, 1), (21, 1), (63, 1)] }, { coefficient := -2, powers := [(0, 1), (19, 1), (26, 1), (63, 1)] }],
  [{ coefficient := -2, powers := [(39, 1), (60, 1)] }],
  [{ coefficient := 2, powers := [(63, 1)] }],
  [{ coefficient := -2, powers := [(19, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (63, 1)] }, { coefficient := -2, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (42, 1), (63, 1)] }, { coefficient := 2, powers := [(53, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (2, 1), (63, 1)] }, { coefficient := -1, powers := [(2, 1), (21, 1), (63, 1)] }, { coefficient := -2, powers := [(2, 1), (26, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(0, 2), (63, 1)] }, { coefficient := 1, powers := [(0, 1), (21, 1), (63, 1)] }, { coefficient := 2, powers := [(0, 1), (26, 1), (63, 1)] }],
  [{ coefficient := 2, powers := [(38, 1), (60, 1)] }],
  [{ coefficient := 2, powers := [(38, 1), (39, 1), (60, 2), (61, 1), (69, 1)] }, { coefficient := -2, powers := [(38, 1), (42, 1), (53, 1), (60, 1)] }, { coefficient := -2, powers := [(38, 1), (42, 1), (57, 1), (60, 1)] }, { coefficient := 2, powers := [(38, 1), (47, 1), (53, 1), (60, 1)] }, { coefficient := 2, powers := [(39, 1), (60, 1)] }],
  [{ coefficient := 2, powers := [(26, 1), (53, 1)] }, { coefficient := -2, powers := [(38, 1), (60, 1)] }, { coefficient := -4, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (2, 1), (63, 1)] }, { coefficient := 2, powers := [(2, 1), (26, 1), (63, 1)] }, { coefficient := -2, powers := [(4, 1), (33, 1), (38, 1), (60, 1)] }, { coefficient := -2, powers := [(11, 1), (23, 1), (38, 1), (60, 1)] }, { coefficient := 1, powers := [(19, 1), (21, 1), (29, 1), (63, 1)] }, { coefficient := 1, powers := [(19, 1), (26, 1), (29, 1), (63, 1)] }, { coefficient := 2, powers := [(21, 1)] }],
  [{ coefficient := 2, powers := [(4, 1), (38, 1), (60, 2), (61, 1), (69, 1)] }, { coefficient := -2, powers := [(4, 1), (38, 1), (60, 2)] }, { coefficient := -2, powers := [(11, 1), (38, 1), (42, 1), (60, 1)] }, { coefficient := -2, powers := [(16, 1), (38, 1), (42, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (2, 1), (38, 1), (42, 1), (60, 1), (63, 1)] }, { coefficient := 2, powers := [(0, 1), (38, 1), (53, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (3, 1), (26, 1), (42, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(2, 1), (3, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(2, 1), (6, 1), (21, 1), (42, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(2, 1), (6, 1), (60, 1), (63, 1)] }, { coefficient := -2, powers := [(3, 1), (7, 1), (36, 1), (42, 1), (60, 1)] }, { coefficient := -2, powers := [(3, 1), (19, 1), (29, 1), (60, 1), (63, 1)] }, { coefficient := 2, powers := [(3, 1), (26, 1), (53, 1), (60, 1)] }, { coefficient := -2, powers := [(3, 1), (60, 1)] }, { coefficient := -2, powers := [(6, 1), (7, 1), (33, 1), (42, 1), (60, 1)] }, { coefficient := -2, powers := [(6, 1), (19, 1), (24, 1), (60, 1), (63, 1)] }, { coefficient := 2, powers := [(6, 1), (21, 1), (53, 1), (60, 1)] }, { coefficient := 2, powers := [(7, 1), (23, 1), (38, 1), (60, 2)] }]
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
    (values : Fin 70 → R) :
    ¬ ∀ index : Fin 25,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((2 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (2 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (2 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component16.SelectedLeafB5_2_0_5_7.selectedHasNoCommonZero

end Krenn.Component16.SelectedLeafB5_2_0_5_7
