import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component16.SelectedLeafB5_2_7_1

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "a914fd05a7868ab135ec30d98b882d93c06a41a7924905f6669515c4c43eabf0"
def certificateSHA256 : String := "468f9ce604253d67c172a1f0fec29a065d2f4c2215c1e361e67e17c2d10664f7"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 24 → Fin 674 := ![
  21,
  150,
  151,
  153,
  273,
  300,
  301,
  317,
  407,
  478,
  506,
  507,
  512,
  532,
  593,
  608,
  609,
  660,
  663,
  664,
  670,
  671,
  672,
  673
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 24 → SparsePoly (Fin 69) := ![
  [{ coefficient := 1, powers := [(23, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (26, 1)] }, { coefficient := 1, powers := [(16, 1), (21, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (27, 1)] }, { coefficient := 1, powers := [(16, 1), (21, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (31, 1)] }, { coefficient := 1, powers := [(16, 1), (24, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (45, 1), (54, 1)] }, { coefficient := 1, powers := [(23, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (47, 1)] }, { coefficient := 1, powers := [(4, 1), (36, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (53, 1)] }, { coefficient := 1, powers := [(7, 1), (33, 1)] }, { coefficient := 1, powers := [(11, 1), (28, 1)] }],
  [{ coefficient := 1, powers := [(30, 1), (54, 1)] }, { coefficient := 1, powers := [(31, 1), (42, 1)] }, { coefficient := 1, powers := [(31, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (26, 1), (42, 1)] }, { coefficient := 1, powers := [(19, 1), (26, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1)] }, { coefficient := 1, powers := [(19, 1), (29, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (26, 1), (60, 1)] }, { coefficient := 1, powers := [(11, 1), (26, 1), (47, 1)] }, { coefficient := 1, powers := [(16, 1), (26, 1), (42, 1)] }, { coefficient := 1, powers := [(16, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (27, 1), (60, 1)] }, { coefficient := 1, powers := [(11, 1), (27, 1), (47, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1), (42, 1)] }, { coefficient := 1, powers := [(16, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (31, 1), (60, 1)] }, { coefficient := 1, powers := [(11, 1), (31, 1), (47, 1)] }, { coefficient := 1, powers := [(16, 1), (30, 1), (54, 1)] }, { coefficient := 1, powers := [(16, 1), (31, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (24, 1), (60, 1)] }, { coefficient := 1, powers := [(11, 1), (24, 1), (57, 1)] }, { coefficient := 1, powers := [(11, 1), (30, 1)] }, { coefficient := 1, powers := [(16, 1), (24, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (42, 1), (58, 1)] }, { coefficient := 1, powers := [(1, 1), (48, 1), (54, 1)] }, { coefficient := 1, powers := [(4, 1), (33, 1), (58, 1)] }, { coefficient := 1, powers := [(11, 1), (23, 1), (58, 1)] }, { coefficient := 1, powers := [(17, 1), (23, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (60, 1)] }, { coefficient := 1, powers := [(11, 1), (47, 1)] }, { coefficient := 1, powers := [(11, 1), (57, 1)] }, { coefficient := 1, powers := [(16, 1), (42, 1)] }, { coefficient := 1, powers := [(16, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (53, 1)] }, { coefficient := 1, powers := [(23, 1), (57, 1)] }, { coefficient := 1, powers := [(28, 1), (42, 1)] }, { coefficient := 1, powers := [(28, 1), (47, 1)] }, { coefficient := 1, powers := [(33, 1), (39, 1)] }, { coefficient := 1, powers := [(36, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (39, 1), (60, 1)] }, { coefficient := 1, powers := [(1, 1), (42, 1), (57, 1)] }, { coefficient := 1, powers := [(1, 1), (47, 1), (53, 1)] }, { coefficient := 1, powers := [(4, 1), (28, 1), (60, 1)] }, { coefficient := 1, powers := [(4, 1), (33, 1), (57, 1)] }, { coefficient := 1, powers := [(4, 1), (36, 1), (53, 1)] }, { coefficient := 1, powers := [(7, 1), (23, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (33, 1), (47, 1)] }, { coefficient := 1, powers := [(7, 1), (36, 1), (42, 1)] }, { coefficient := 1, powers := [(11, 1), (23, 1), (57, 1)] }, { coefficient := 1, powers := [(11, 1), (28, 1), (47, 1)] }, { coefficient := 1, powers := [(11, 1), (36, 1), (39, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1), (53, 1)] }, { coefficient := 1, powers := [(16, 1), (28, 1), (42, 1)] }, { coefficient := 1, powers := [(16, 1), (33, 1), (39, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(58, 1), (67, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(26, 1)] }],
  [{ coefficient := 1, powers := [(28, 1)] }],
  [{ coefficient := 1, powers := [(31, 1), (68, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 24 → SparsePoly (Fin 69) := ![
  [{ coefficient := 1, powers := [(11, 1), (45, 1), (53, 1), (67, 1)] }, { coefficient := 2, powers := [(11, 1), (45, 1), (57, 1), (67, 1)] }, { coefficient := -1, powers := [(17, 1), (57, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(30, 1), (33, 1), (39, 1), (54, 1), (68, 1)] }, { coefficient := -1, powers := [(30, 1), (36, 1), (38, 1), (42, 1), (54, 1), (57, 1), (68, 1)] }],
  [{ coefficient := -1, powers := [(30, 1), (33, 1), (39, 1), (68, 1)] }, { coefficient := 1, powers := [(30, 1), (36, 1), (38, 1), (42, 1), (57, 1), (68, 1)] }],
  [{ coefficient := -1, powers := [(33, 1), (39, 1), (68, 1)] }, { coefficient := 1, powers := [(36, 1), (38, 1), (42, 1), (57, 1), (68, 1)] }],
  [{ coefficient := -1, powers := [(11, 1), (53, 1), (67, 1)] }, { coefficient := -2, powers := [(11, 1), (57, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(53, 1)] }],
  [{ coefficient := 1, powers := [(47, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (23, 1), (68, 1)] }, { coefficient := -1, powers := [(16, 1), (36, 1), (38, 1), (42, 1), (68, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (24, 1), (36, 1), (42, 1), (63, 1)] }, { coefficient := -1, powers := [(7, 1), (29, 1), (36, 1), (42, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (36, 1), (42, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(23, 1), (42, 1)] }, { coefficient := -1, powers := [(23, 1), (47, 1)] }, { coefficient := -1, powers := [(23, 1), (53, 1)] }, { coefficient := 1, powers := [(33, 1), (39, 1)] }, { coefficient := 1, powers := [(36, 1), (38, 1), (42, 2)] }, { coefficient := 1, powers := [(36, 1), (38, 1), (42, 1), (47, 1)] }, { coefficient := 1, powers := [(36, 1), (38, 1), (42, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (33, 1), (39, 1), (68, 1)] }, { coefficient := -1, powers := [(24, 1), (36, 1), (38, 1), (42, 1), (57, 1), (68, 1)] }],
  [{ coefficient := -1, powers := [(23, 1), (68, 1)] }, { coefficient := 1, powers := [(36, 1), (38, 1), (42, 1), (68, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (33, 1), (39, 1), (68, 1)] }, { coefficient := -1, powers := [(27, 1), (36, 1), (38, 1), (42, 1), (57, 1), (68, 1)] }],
  [{ coefficient := 1, powers := [(57, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (31, 1), (68, 1)] }, { coefficient := -1, powers := [(24, 1), (27, 1), (33, 1), (39, 1), (68, 1)] }, { coefficient := 1, powers := [(24, 1), (27, 1), (36, 1), (38, 1), (42, 1), (57, 1), (68, 1)] }, { coefficient := -1, powers := [(31, 1), (36, 1), (38, 1), (42, 1), (68, 1)] }],
  [{ coefficient := 1, powers := [(11, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(39, 1), (60, 1)] }, { coefficient := -1, powers := [(42, 1), (57, 1), (58, 1), (67, 1)] }, { coefficient := 1, powers := [(42, 1), (57, 1)] }, { coefficient := -1, powers := [(47, 1), (53, 1)] }, { coefficient := -1, powers := [(48, 1), (54, 1), (57, 1), (67, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (36, 1), (38, 1), (42, 1), (60, 1)] }, { coefficient := -1, powers := [(7, 1), (36, 1), (42, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (33, 1), (57, 1)] }, { coefficient := 1, powers := [(11, 1), (23, 1), (53, 1)] }, { coefficient := 1, powers := [(11, 1), (23, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (23, 1), (42, 1), (60, 1)] }, { coefficient := 1, powers := [(4, 1), (23, 1), (47, 1), (60, 1)] }, { coefficient := 1, powers := [(4, 1), (23, 1), (53, 1), (60, 1)] }, { coefficient := -1, powers := [(4, 1), (33, 1), (39, 1), (60, 1)] }, { coefficient := -1, powers := [(4, 1), (36, 1), (38, 1), (42, 2), (60, 1)] }, { coefficient := -1, powers := [(4, 1), (36, 1), (38, 1), (42, 1), (47, 1), (60, 1)] }, { coefficient := -1, powers := [(4, 1), (36, 1), (38, 1), (42, 1), (53, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (19, 1), (24, 1), (36, 1), (42, 2), (63, 1)] }, { coefficient := 1, powers := [(7, 1), (19, 1), (24, 1), (36, 1), (42, 1), (47, 1), (63, 1)] }, { coefficient := 1, powers := [(7, 1), (19, 1), (29, 1), (36, 1), (42, 2), (63, 1)] }, { coefficient := 1, powers := [(7, 1), (19, 1), (29, 1), (36, 1), (42, 1), (47, 1), (63, 1)] }, { coefficient := 1, powers := [(11, 1), (23, 1), (42, 1), (47, 1)] }, { coefficient := 1, powers := [(11, 1), (23, 1), (47, 2)] }, { coefficient := 1, powers := [(11, 1), (23, 1), (47, 1), (53, 1)] }, { coefficient := -1, powers := [(11, 1), (30, 1), (33, 1), (39, 1), (54, 1), (68, 1)] }, { coefficient := 1, powers := [(11, 1), (30, 1), (36, 1), (38, 1), (42, 1), (54, 1), (57, 1), (68, 1)] }, { coefficient := -1, powers := [(11, 1), (33, 1), (39, 1), (47, 1)] }, { coefficient := -1, powers := [(11, 1), (36, 1), (38, 1), (42, 2), (47, 1)] }, { coefficient := -1, powers := [(11, 1), (36, 1), (38, 1), (42, 1), (47, 2)] }, { coefficient := -1, powers := [(11, 1), (36, 1), (38, 1), (42, 1), (47, 1), (53, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1), (42, 2)] }, { coefficient := 1, powers := [(16, 1), (23, 1), (42, 1), (47, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1), (42, 1), (53, 1)] }, { coefficient := -1, powers := [(16, 1), (33, 1), (39, 1), (42, 1)] }, { coefficient := -1, powers := [(16, 1), (36, 1), (38, 1), (42, 3)] }, { coefficient := -1, powers := [(16, 1), (36, 1), (38, 1), (42, 2), (47, 1)] }, { coefficient := -1, powers := [(16, 1), (36, 1), (38, 1), (42, 2), (53, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (60, 1)] }, { coefficient := -1, powers := [(11, 1), (42, 1)] }, { coefficient := -1, powers := [(11, 1), (47, 1)] }, { coefficient := 1, powers := [(16, 1), (42, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (23, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (36, 1), (38, 1), (42, 1), (60, 1)] }, { coefficient := -1, powers := [(11, 1), (23, 1), (57, 1)] }, { coefficient := 1, powers := [(11, 1), (33, 1), (39, 1)] }, { coefficient := -1, powers := [(16, 1), (23, 1), (42, 1)] }, { coefficient := -1, powers := [(16, 1), (23, 1), (47, 1)] }, { coefficient := -1, powers := [(16, 1), (23, 1), (53, 1)] }, { coefficient := 1, powers := [(16, 1), (36, 1), (38, 1), (42, 2)] }, { coefficient := 1, powers := [(16, 1), (36, 1), (38, 1), (42, 1), (47, 1)] }, { coefficient := 1, powers := [(16, 1), (36, 1), (38, 1), (42, 1), (53, 1)] }]
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
    (values : Fin 69 → R) :
    ¬ ∀ index : Fin 24,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component16.SelectedLeafB5_2_7_1.selectedHasNoCommonZero

end Krenn.Component16.SelectedLeafB5_2_7_1
