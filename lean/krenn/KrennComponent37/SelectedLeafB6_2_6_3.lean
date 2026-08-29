import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component37.SelectedLeafB6_2_6_3

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "7be68f6cc943c2dd5dbe6ea81eb3bf90e23dfd214b2d93bcc3ddc9a5f497b123"
def certificateSHA256 : String := "0ec86b45205baf574edda81c3a96c491991e3e7bdef9c8e9657794c02b227483"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 18 → Fin 670 := ![
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
  667,
  668,
  669
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 18 → SparsePoly (Fin 69) := ![
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
  [{ coefficient := 1, powers := [(25, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (67, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(30, 1), (68, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 18 → SparsePoly (Fin 69) := ![
  [{ coefficient := -2, powers := [(0, 1), (43, 1), (63, 1)] }, { coefficient := -1, powers := [(20, 1), (43, 1), (63, 1)] }, { coefficient := -1, powers := [(20, 1), (56, 1), (63, 1)] }, { coefficient := -1, powers := [(34, 1), (37, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (20, 1), (23, 1), (59, 1), (63, 1), (68, 1)] }, { coefficient := -1, powers := [(13, 1), (23, 1), (31, 1), (37, 1), (63, 1), (68, 1)] }],
  [{ coefficient := -1, powers := [(31, 1), (37, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (20, 1), (43, 1), (60, 1), (67, 1)] }, { coefficient := 1, powers := [(13, 1), (20, 1), (37, 1), (57, 1), (60, 1), (66, 1), (67, 1)] }, { coefficient := 1, powers := [(13, 1), (37, 1), (60, 1), (66, 1), (67, 1)] }, { coefficient := -1, powers := [(20, 1), (56, 1), (57, 1), (66, 1), (67, 1)] }, { coefficient := 1, powers := [(20, 1), (56, 1), (67, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1), (67, 1)] }, { coefficient := -1, powers := [(56, 1), (66, 1), (67, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (20, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (20, 1), (59, 1), (68, 1)] }, { coefficient := 1, powers := [(13, 1), (31, 1), (37, 1), (68, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (20, 1), (30, 1), (59, 1), (68, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1), (59, 1)] }, { coefficient := -1, powers := [(13, 1), (30, 1), (31, 1), (37, 1), (68, 1)] }, { coefficient := 1, powers := [(13, 1), (31, 1), (37, 1)] }],
  [{ coefficient := -1, powers := [(13, 1), (37, 1), (60, 1), (66, 1)] }, { coefficient := 1, powers := [(56, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(50, 1)] }],
  [{ coefficient := 1, powers := [(43, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(0, 1), (37, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (43, 1), (50, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1), (23, 1), (54, 1), (59, 1), (68, 1)] }, { coefficient := 1, powers := [(13, 1), (23, 1), (31, 1), (37, 1), (54, 1), (68, 1)] }, { coefficient := 1, powers := [(20, 1), (43, 1), (50, 1)] }, { coefficient := 1, powers := [(20, 1), (50, 1), (56, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1), (50, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (1, 1), (56, 1), (63, 1)] }, { coefficient := 1, powers := [(0, 1), (13, 1), (37, 1), (57, 1), (60, 1), (66, 1)] }, { coefficient := -1, powers := [(0, 1), (56, 1), (57, 1), (66, 1)] }, { coefficient := 1, powers := [(0, 1), (56, 1)] }, { coefficient := 1, powers := [(6, 1), (13, 1), (20, 1), (60, 1)] }, { coefficient := -1, powers := [(6, 1), (20, 1), (27, 1), (43, 1), (60, 1), (67, 1)] }, { coefficient := 1, powers := [(6, 1), (34, 1)] }, { coefficient := -1, powers := [(13, 1), (20, 1), (27, 1), (37, 1), (57, 1), (60, 1), (66, 1), (67, 1)] }, { coefficient := -1, powers := [(13, 1), (27, 1), (37, 1), (60, 1), (66, 1), (67, 1)] }, { coefficient := 1, powers := [(13, 1), (37, 1), (60, 1), (66, 1)] }, { coefficient := 1, powers := [(20, 1), (27, 1), (56, 1), (57, 1), (66, 1), (67, 1)] }, { coefficient := -1, powers := [(20, 1), (27, 1), (56, 1), (67, 1)] }, { coefficient := -1, powers := [(27, 1), (34, 1), (37, 1), (67, 1)] }, { coefficient := 1, powers := [(27, 1), (56, 1), (66, 1), (67, 1)] }, { coefficient := -1, powers := [(56, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (13, 1), (31, 1), (37, 1), (60, 1)] }, { coefficient := -1, powers := [(3, 1), (31, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (59, 1)] }, { coefficient := 1, powers := [(13, 1), (40, 1)] }, { coefficient := -1, powers := [(40, 1), (43, 1)] }, { coefficient := -1, powers := [(43, 1), (50, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (9, 1), (20, 1), (43, 1), (60, 1)] }, { coefficient := -1, powers := [(9, 1), (13, 1), (20, 1), (37, 1), (57, 1), (60, 1), (66, 1)] }, { coefficient := -1, powers := [(9, 1), (13, 1), (37, 1), (60, 1), (66, 1)] }, { coefficient := 1, powers := [(9, 1), (20, 1), (56, 1), (57, 1), (66, 1)] }, { coefficient := -1, powers := [(9, 1), (20, 1), (56, 1)] }, { coefficient := -1, powers := [(9, 1), (34, 1), (37, 1)] }, { coefficient := 1, powers := [(9, 1), (56, 1), (66, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1), (43, 1)] }],
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
    (values : Fin 69 → R) :
    ¬ ∀ index : Fin 18,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component37.SelectedLeafB6_2_6_3.selectedHasNoCommonZero

end Krenn.Component37.SelectedLeafB6_2_6_3
