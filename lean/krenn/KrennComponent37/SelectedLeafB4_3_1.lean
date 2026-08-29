import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component37.SelectedLeafB4_3_1

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "fb53a8fa158ac07fb32ae29043a33c09cd0a0a2bd8655d1a1474b3e1489142df"
def certificateSHA256 : String := "20ef0b8587fc96cb290713896515fe2f1e7184b57fced7bd8d9bf360b7804390"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 26 → Fin 667 := ![
  23,
  27,
  154,
  155,
  159,
  182,
  233,
  234,
  283,
  298,
  299,
  304,
  385,
  427,
  546,
  549,
  581,
  590,
  604,
  605,
  656,
  658,
  659,
  663,
  665,
  666
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 26 → SparsePoly (Fin 66) := ![
  [{ coefficient := 1, powers := [(22, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (25, 1)] }, { coefficient := 1, powers := [(15, 1), (20, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (26, 1)] }, { coefficient := 1, powers := [(15, 1), (20, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (44, 1)] }, { coefficient := 1, powers := [(16, 1), (20, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (42, 1)] }, { coefficient := 1, powers := [(27, 1), (48, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (25, 1), (44, 1)] }, { coefficient := 1, powers := [(16, 1), (20, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (25, 1), (48, 1)] }, { coefficient := 1, powers := [(15, 1), (21, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (44, 1), (54, 1)] }, { coefficient := 1, powers := [(22, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (46, 1)] }, { coefficient := 1, powers := [(4, 1), (35, 1)] }, { coefficient := 1, powers := [(15, 1), (22, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (52, 1)] }, { coefficient := 1, powers := [(7, 1), (32, 1)] }, { coefficient := 1, powers := [(10, 1), (27, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (47, 1)] }, { coefficient := 1, powers := [(16, 1), (41, 1)] }, { coefficient := 1, powers := [(16, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (20, 1), (57, 1)] }, { coefficient := 1, powers := [(11, 1)] }, { coefficient := 1, powers := [(15, 1), (20, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (54, 1)] }, { coefficient := 1, powers := [(3, 1), (26, 1), (60, 1)] }, { coefficient := 1, powers := [(20, 1), (54, 1)] }, { coefficient := 1, powers := [(26, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (26, 1), (47, 1)] }, { coefficient := 1, powers := [(10, 1), (58, 1)] }, { coefficient := 1, powers := [(16, 1), (26, 1), (41, 1)] }, { coefficient := 1, powers := [(16, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (21, 1), (57, 1)] }, { coefficient := 1, powers := [(11, 1), (48, 1)] }, { coefficient := 1, powers := [(15, 1), (21, 1), (53, 1)] }, { coefficient := 1, powers := [(15, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (52, 1)] }, { coefficient := 1, powers := [(3, 1), (60, 1)] }, { coefficient := 1, powers := [(20, 1), (52, 1)] }, { coefficient := 1, powers := [(20, 1), (57, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1), (42, 1), (57, 1)] }, { coefficient := 1, powers := [(1, 1), (48, 1), (53, 1)] }, { coefficient := 1, powers := [(7, 1), (35, 1), (42, 1)] }, { coefficient := 1, powers := [(11, 1), (27, 1), (48, 1)] }, { coefficient := 1, powers := [(15, 1), (27, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (60, 1)] }, { coefficient := 1, powers := [(10, 1), (46, 1)] }, { coefficient := 1, powers := [(10, 1), (57, 1)] }, { coefficient := 1, powers := [(15, 1), (41, 1)] }, { coefficient := 1, powers := [(15, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (52, 1)] }, { coefficient := 1, powers := [(22, 1), (57, 1)] }, { coefficient := 1, powers := [(27, 1), (41, 1)] }, { coefficient := 1, powers := [(27, 1), (46, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1)] }, { coefficient := 1, powers := [(35, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (38, 1), (60, 1)] }, { coefficient := 1, powers := [(1, 1), (41, 1), (57, 1)] }, { coefficient := 1, powers := [(1, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(4, 1), (27, 1), (60, 1)] }, { coefficient := 1, powers := [(4, 1), (32, 1), (57, 1)] }, { coefficient := 1, powers := [(4, 1), (35, 1), (52, 1)] }, { coefficient := 1, powers := [(7, 1), (22, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (32, 1), (46, 1)] }, { coefficient := 1, powers := [(7, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(10, 1), (22, 1), (57, 1)] }, { coefficient := 1, powers := [(10, 1), (27, 1), (46, 1)] }, { coefficient := 1, powers := [(10, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(15, 1), (22, 1), (52, 1)] }, { coefficient := 1, powers := [(15, 1), (27, 1), (41, 1)] }, { coefficient := 1, powers := [(15, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1)] }],
  [{ coefficient := 1, powers := [(42, 1), (64, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(57, 1)] }],
  [{ coefficient := 1, powers := [(58, 1), (65, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 26 → SparsePoly (Fin 66) := ![
  [{ coefficient := -1, powers := [(7, 1), (44, 1), (60, 1), (65, 1)] }, { coefficient := 1, powers := [(10, 1), (44, 1), (52, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (51, 1), (60, 1), (64, 1)] }, { coefficient := 1, powers := [(10, 1), (41, 1), (51, 1), (64, 1)] }, { coefficient := 2, powers := [(10, 1), (46, 1), (51, 1), (64, 1)] }, { coefficient := -1, powers := [(11, 1), (41, 1), (64, 1)] }, { coefficient := 1, powers := [(15, 1), (41, 1), (51, 1), (64, 1)] }, { coefficient := 1, powers := [(15, 1), (51, 1), (52, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(32, 1), (38, 1), (44, 1), (54, 1), (62, 1), (65, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1), (48, 1), (53, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(32, 1), (38, 1), (44, 1), (62, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(26, 1), (32, 1), (38, 1), (62, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (60, 1), (64, 1)] }, { coefficient := -1, powers := [(10, 1), (41, 1), (64, 1)] }, { coefficient := -2, powers := [(10, 1), (46, 1), (64, 1)] }, { coefficient := -1, powers := [(15, 1), (41, 1), (64, 1)] }, { coefficient := -1, powers := [(15, 1), (52, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(32, 1), (38, 1), (54, 1), (62, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(32, 1), (38, 1), (53, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (60, 1), (65, 1)] }, { coefficient := -1, powers := [(10, 1), (52, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(52, 1)] }],
  [{ coefficient := 1, powers := [(46, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (26, 1), (32, 1), (38, 1), (62, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(32, 1), (38, 1), (48, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (32, 1), (38, 1), (62, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (32, 1), (38, 1), (62, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(32, 1), (38, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(16, 1), (26, 1), (32, 1), (38, 1), (62, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(41, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(27, 1)] }],
  [{ coefficient := 1, powers := [(10, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(10, 1), (32, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(38, 1), (60, 1)] }, { coefficient := -1, powers := [(41, 1), (42, 1), (57, 1), (64, 1)] }, { coefficient := -1, powers := [(41, 1), (48, 1), (53, 1), (64, 1)] }, { coefficient := 1, powers := [(41, 1), (57, 1)] }, { coefficient := -1, powers := [(46, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (27, 1), (60, 1)] }, { coefficient := -1, powers := [(7, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(10, 1), (27, 1), (41, 1)] }, { coefficient := 2, powers := [(10, 1), (27, 1), (46, 1)] }, { coefficient := 1, powers := [(15, 1), (27, 1), (52, 1)] }, { coefficient := -1, powers := [(15, 1), (32, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (32, 1)] }, { coefficient := -1, powers := [(10, 1), (27, 1)] }, { coefficient := 1, powers := [(11, 1), (20, 1), (32, 1), (38, 1), (48, 1), (64, 1)] }, { coefficient := -1, powers := [(11, 1), (21, 1), (32, 1), (38, 1), (64, 1)] }, { coefficient := 1, powers := [(16, 1), (20, 1), (26, 1), (32, 1), (38, 1), (62, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (10, 1), (32, 1), (38, 1), (62, 1)] }, { coefficient := -1, powers := [(7, 1), (22, 1), (60, 1)] }, { coefficient := 1, powers := [(10, 1), (22, 1), (52, 1)] }]
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
    (values : Fin 66 → R) :
    ¬ ∀ index : Fin 26,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component37.SelectedLeafB4_3_1.selectedHasNoCommonZero

end Krenn.Component37.SelectedLeafB4_3_1
