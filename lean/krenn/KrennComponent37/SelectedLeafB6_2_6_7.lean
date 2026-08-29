import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component37.SelectedLeafB6_2_6_7

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "ec3caf76b438ae05c3b664b23ed71cf8f0299661eb05885892950a6cd9936f97"
def certificateSHA256 : String := "f727b194669e28731c79bafb2d80a34488a83198b04ef943609d3dd68b77ce08"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 17 → Fin 670 := ![
  2,
  3,
  25,
  150,
  301,
  318,
  349,
  581,
  583,
  602,
  603,
  655,
  659,
  661,
  665,
  668,
  669
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 17 → SparsePoly (Fin 70) := ![
  [{ coefficient := 1, powers := [(1, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (27, 1)] }, { coefficient := 1, powers := [(27, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (59, 1)] }, { coefficient := 1, powers := [(9, 1), (43, 1)] }, { coefficient := 1, powers := [(13, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (37, 1), (59, 1)] }, { coefficient := 1, powers := [(1, 1), (40, 1), (56, 1)] }, { coefficient := 1, powers := [(1, 1), (43, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (30, 1), (60, 1)] }, { coefficient := 1, powers := [(23, 1), (54, 1)] }, { coefficient := 1, powers := [(30, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (52, 1)] }, { coefficient := 1, powers := [(3, 1), (60, 1)] }, { coefficient := 1, powers := [(20, 1), (52, 1)] }, { coefficient := 1, powers := [(20, 1), (57, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (31, 1), (57, 1)] }, { coefficient := 1, powers := [(9, 1), (20, 1), (57, 1)] }, { coefficient := 1, powers := [(9, 1)] }, { coefficient := 1, powers := [(40, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1)] }, { coefficient := 1, powers := [(3, 1), (34, 1)] }, { coefficient := 1, powers := [(13, 1), (20, 1)] }, { coefficient := 1, powers := [(20, 1), (56, 1)] }, { coefficient := 1, powers := [(25, 1), (43, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (50, 1)] }, { coefficient := 1, powers := [(6, 1), (31, 1)] }, { coefficient := 1, powers := [(9, 1), (25, 1)] }, { coefficient := 1, powers := [(20, 1), (50, 1)] }, { coefficient := 1, powers := [(25, 1), (40, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (37, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (40, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (43, 1), (50, 1)] }, { coefficient := 1, powers := [(3, 1), (25, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (31, 1), (56, 1)] }, { coefficient := 1, powers := [(3, 1), (34, 1), (50, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (31, 1), (43, 1)] }, { coefficient := 1, powers := [(6, 1), (34, 1), (40, 1)] }, { coefficient := 1, powers := [(9, 1), (20, 1), (56, 1)] }, { coefficient := 1, powers := [(9, 1), (25, 1), (43, 1)] }, { coefficient := 1, powers := [(9, 1), (34, 1), (37, 1)] }, { coefficient := 1, powers := [(13, 1), (20, 1), (50, 1)] }, { coefficient := 1, powers := [(13, 1), (25, 1), (40, 1)] }, { coefficient := 1, powers := [(13, 1), (31, 1), (37, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(40, 1)] }],
  [{ coefficient := 1, powers := [(57, 1), (66, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(27, 1), (68, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(30, 1), (69, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 17 → SparsePoly (Fin 70) := ![
  [{ coefficient := -2, powers := [(0, 1), (43, 1), (63, 1)] }, { coefficient := -1, powers := [(20, 1), (43, 1), (63, 1)] }, { coefficient := -1, powers := [(20, 1), (56, 1), (63, 1)] }, { coefficient := -1, powers := [(25, 1), (43, 1), (63, 1)] }, { coefficient := -1, powers := [(34, 1), (37, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (20, 1), (23, 1), (59, 1), (63, 1), (69, 1)] }, { coefficient := -1, powers := [(13, 1), (23, 1), (31, 1), (37, 1), (63, 1), (69, 1)] }],
  [{ coefficient := -1, powers := [(31, 1), (37, 1), (68, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (20, 1), (43, 1), (60, 1), (68, 1)] }, { coefficient := 1, powers := [(13, 1), (20, 1), (37, 1), (57, 1), (60, 1), (66, 1), (68, 1)] }, { coefficient := 1, powers := [(13, 1), (37, 1), (60, 1), (66, 1), (68, 1)] }, { coefficient := -1, powers := [(20, 1), (56, 1), (57, 1), (66, 1), (68, 1)] }, { coefficient := 1, powers := [(20, 1), (56, 1), (68, 1)] }, { coefficient := -1, powers := [(25, 1), (43, 1), (68, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1), (68, 1)] }, { coefficient := -1, powers := [(56, 1), (66, 1), (68, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (20, 1), (60, 1)] }, { coefficient := 1, powers := [(25, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (20, 1), (59, 1), (69, 1)] }, { coefficient := 1, powers := [(13, 1), (31, 1), (37, 1), (69, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (20, 1), (30, 1), (59, 1), (69, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1), (59, 1)] }, { coefficient := -1, powers := [(13, 1), (30, 1), (31, 1), (37, 1), (69, 1)] }, { coefficient := 1, powers := [(13, 1), (31, 1), (37, 1)] }],
  [{ coefficient := -1, powers := [(13, 1), (37, 1), (60, 1), (66, 1)] }, { coefficient := 1, powers := [(56, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(50, 1)] }],
  [{ coefficient := 1, powers := [(43, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(0, 1), (37, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (43, 1), (50, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1), (23, 1), (54, 1), (59, 1), (69, 1)] }, { coefficient := 1, powers := [(13, 1), (23, 1), (31, 1), (37, 1), (54, 1), (69, 1)] }, { coefficient := 1, powers := [(20, 1), (43, 1), (50, 1)] }, { coefficient := 1, powers := [(20, 1), (50, 1), (56, 1)] }, { coefficient := 1, powers := [(25, 1), (43, 1), (50, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1), (50, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (1, 1), (56, 1), (63, 1)] }, { coefficient := 1, powers := [(0, 1), (13, 1), (37, 1), (57, 1), (60, 1), (66, 1)] }, { coefficient := -1, powers := [(0, 1), (56, 1), (57, 1), (66, 1)] }, { coefficient := 1, powers := [(0, 1), (56, 1)] }, { coefficient := 1, powers := [(6, 1), (13, 1), (20, 1), (60, 1)] }, { coefficient := -1, powers := [(6, 1), (20, 1), (27, 1), (43, 1), (60, 1), (68, 1)] }, { coefficient := 1, powers := [(6, 1), (34, 1)] }, { coefficient := -1, powers := [(13, 1), (20, 1), (27, 1), (37, 1), (57, 1), (60, 1), (66, 1), (68, 1)] }, { coefficient := -1, powers := [(13, 1), (27, 1), (37, 1), (60, 1), (66, 1), (68, 1)] }, { coefficient := 1, powers := [(13, 1), (37, 1), (60, 1), (66, 1)] }, { coefficient := 1, powers := [(20, 1), (27, 1), (56, 1), (57, 1), (66, 1), (68, 1)] }, { coefficient := -1, powers := [(20, 1), (27, 1), (56, 1), (68, 1)] }, { coefficient := 1, powers := [(25, 1), (27, 1), (43, 1), (68, 1)] }, { coefficient := -1, powers := [(25, 1), (43, 1)] }, { coefficient := -1, powers := [(27, 1), (34, 1), (37, 1), (68, 1)] }, { coefficient := 1, powers := [(27, 1), (56, 1), (66, 1), (68, 1)] }, { coefficient := -1, powers := [(56, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (13, 1), (31, 1), (37, 1), (60, 1)] }, { coefficient := -1, powers := [(3, 1), (31, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (9, 1), (20, 1), (43, 1), (60, 1)] }, { coefficient := -1, powers := [(9, 1), (13, 1), (20, 1), (37, 1), (57, 1), (60, 1), (66, 1)] }, { coefficient := -1, powers := [(9, 1), (13, 1), (37, 1), (60, 1), (66, 1)] }, { coefficient := 1, powers := [(9, 1), (20, 1), (56, 1), (57, 1), (66, 1)] }, { coefficient := -1, powers := [(9, 1), (20, 1), (56, 1)] }, { coefficient := 1, powers := [(9, 1), (25, 1), (43, 1)] }, { coefficient := -1, powers := [(9, 1), (34, 1), (37, 1)] }, { coefficient := 1, powers := [(9, 1), (56, 1), (66, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (6, 1), (20, 1), (52, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (13, 1), (31, 1), (37, 1), (52, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 2), (52, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 2), (57, 1), (59, 1)] }, { coefficient := 1, powers := [(13, 1), (20, 1), (31, 1), (37, 1), (52, 1)] }, { coefficient := 1, powers := [(13, 1), (20, 1), (31, 1), (37, 1), (57, 1)] }]
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
    (values : Fin 70 → R) :
    ¬ ∀ index : Fin 17,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component37.SelectedLeafB6_2_6_7.selectedHasNoCommonZero

end Krenn.Component37.SelectedLeafB6_2_6_7
