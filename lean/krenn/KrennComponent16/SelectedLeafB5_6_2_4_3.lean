import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component16.SelectedLeafB5_6_2_4_3

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "bc626d556f65905386df86ce459806510f463982bf5446ff4c338e5a71f59897"
def certificateSHA256 : String := "4249d9c77067723f43215589e8fd306f1bd2815eaad43e24aecceb1b04ea8b28"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 16 → Fin 677 := ![
  6,
  34,
  147,
  300,
  301,
  327,
  523,
  591,
  608,
  609,
  660,
  662,
  663,
  665,
  672,
  676
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 16 → SparsePoly (Fin 70) := ![
  [{ coefficient := 1, powers := [(6, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (39, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (61, 1)] }, { coefficient := 1, powers := [(7, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (47, 1)] }, { coefficient := 1, powers := [(4, 1), (36, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (53, 1)] }, { coefficient := 1, powers := [(7, 1), (33, 1)] }, { coefficient := 1, powers := [(11, 1), (28, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (39, 1), (61, 1)] }, { coefficient := 1, powers := [(4, 1), (28, 1), (61, 1)] }, { coefficient := 1, powers := [(7, 1), (23, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (23, 1), (60, 1)] }, { coefficient := 1, powers := [(6, 1), (33, 1), (47, 1)] }, { coefficient := 1, powers := [(6, 1), (36, 1), (42, 1)] }, { coefficient := 1, powers := [(23, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (41, 1), (57, 1)] }, { coefficient := 1, powers := [(1, 1), (52, 1)] }, { coefficient := 1, powers := [(7, 1), (36, 1), (41, 1)] }, { coefficient := 1, powers := [(10, 1), (28, 1)] }, { coefficient := 1, powers := [(16, 1), (28, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (60, 1)] }, { coefficient := 1, powers := [(11, 1), (47, 1)] }, { coefficient := 1, powers := [(11, 1), (57, 1)] }, { coefficient := 1, powers := [(16, 1), (42, 1)] }, { coefficient := 1, powers := [(16, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (53, 1)] }, { coefficient := 1, powers := [(23, 1), (57, 1)] }, { coefficient := 1, powers := [(28, 1), (42, 1)] }, { coefficient := 1, powers := [(28, 1), (47, 1)] }, { coefficient := 1, powers := [(33, 1), (39, 1)] }, { coefficient := 1, powers := [(36, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (39, 1), (60, 1)] }, { coefficient := 1, powers := [(1, 1), (42, 1), (57, 1)] }, { coefficient := 1, powers := [(1, 1), (47, 1), (53, 1)] }, { coefficient := 1, powers := [(4, 1), (28, 1), (60, 1)] }, { coefficient := 1, powers := [(4, 1), (33, 1), (57, 1)] }, { coefficient := 1, powers := [(4, 1), (36, 1), (53, 1)] }, { coefficient := 1, powers := [(7, 1), (23, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (33, 1), (47, 1)] }, { coefficient := 1, powers := [(7, 1), (36, 1), (42, 1)] }, { coefficient := 1, powers := [(11, 1), (23, 1), (57, 1)] }, { coefficient := 1, powers := [(11, 1), (28, 1), (47, 1)] }, { coefficient := 1, powers := [(11, 1), (36, 1), (39, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1), (53, 1)] }, { coefficient := 1, powers := [(16, 1), (28, 1), (42, 1)] }, { coefficient := 1, powers := [(16, 1), (33, 1), (39, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1)] }],
  [{ coefficient := 1, powers := [(41, 1), (64, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(28, 1)] }],
  [{ coefficient := 1, powers := [(61, 1), (69, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 16 → SparsePoly (Fin 70) := ![
  [{ coefficient := 1, powers := [(11, 1), (23, 1), (47, 1), (60, 1), (69, 1)] }, { coefficient := 1, powers := [(11, 1), (23, 1), (53, 1), (60, 1), (69, 1)] }, { coefficient := 1, powers := [(11, 1), (23, 1), (57, 1), (60, 1), (69, 1)] }, { coefficient := 1, powers := [(11, 1), (33, 1), (47, 2), (69, 1)] }, { coefficient := 1, powers := [(11, 1), (33, 1), (47, 1), (53, 1), (69, 1)] }, { coefficient := 1, powers := [(11, 1), (33, 1), (47, 1), (57, 1), (69, 1)] }, { coefficient := 1, powers := [(11, 1), (36, 1), (42, 1), (47, 1), (69, 1)] }, { coefficient := 1, powers := [(11, 1), (36, 1), (42, 1), (53, 1), (69, 1)] }, { coefficient := 1, powers := [(11, 1), (36, 1), (42, 1), (57, 1), (69, 1)] }],
  [{ coefficient := -1, powers := [(11, 1), (33, 1), (62, 1), (69, 1)] }, { coefficient := 1, powers := [(16, 1), (33, 1), (62, 1), (69, 1)] }],
  [{ coefficient := -1, powers := [(23, 1), (60, 1), (69, 1)] }, { coefficient := 1, powers := [(33, 1), (57, 1), (69, 1)] }, { coefficient := 1, powers := [(36, 1), (42, 1), (69, 1)] }, { coefficient := 1, powers := [(36, 1), (53, 1), (69, 1)] }],
  [{ coefficient := -1, powers := [(42, 1)] }],
  [{ coefficient := 1, powers := [(47, 1)] }, { coefficient := -1, powers := [(57, 1)] }],
  [{ coefficient := 1, powers := [(60, 1), (69, 1)] }],
  [{ coefficient := -1, powers := [(11, 1), (47, 1)] }, { coefficient := -1, powers := [(11, 1), (53, 1)] }, { coefficient := -1, powers := [(11, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [(53, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(23, 1)] }],
  [{ coefficient := 1, powers := [(11, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(11, 1), (33, 1), (39, 1)] }, { coefficient := -1, powers := [(16, 1), (33, 1), (39, 1)] }],
  [{ coefficient := -1, powers := [(39, 1), (60, 1), (61, 1), (69, 1)] }, { coefficient := 1, powers := [(39, 1), (60, 1)] }, { coefficient := 1, powers := [(41, 1), (53, 1), (57, 1), (64, 1)] }, { coefficient := 1, powers := [(42, 1), (47, 1)] }, { coefficient := 1, powers := [(42, 1), (57, 1)] }, { coefficient := 1, powers := [(52, 1), (53, 1), (64, 1)] }, { coefficient := 1, powers := [(53, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (36, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (60, 1), (61, 1), (69, 1)] }, { coefficient := 1, powers := [(4, 1), (60, 1)] }, { coefficient := 1, powers := [(10, 1), (53, 1), (64, 1)] }, { coefficient := -1, powers := [(11, 1), (42, 1)] }, { coefficient := -1, powers := [(11, 1), (47, 1)] }, { coefficient := 1, powers := [(11, 1), (57, 1)] }, { coefficient := 1, powers := [(16, 1), (41, 1), (53, 1), (64, 1)] }, { coefficient := 1, powers := [(16, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (11, 1), (33, 1), (39, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 1), (16, 1), (33, 1), (39, 1), (62, 1)] }, { coefficient := 1, powers := [(4, 1), (23, 1), (60, 1)] }, { coefficient := -1, powers := [(4, 1), (33, 1), (57, 1)] }, { coefficient := -1, powers := [(4, 1), (36, 1), (42, 1)] }, { coefficient := -1, powers := [(4, 1), (36, 1), (53, 1)] }, { coefficient := -1, powers := [(6, 1), (11, 1), (23, 1), (47, 1), (60, 1)] }, { coefficient := -1, powers := [(6, 1), (11, 1), (23, 1), (53, 1), (60, 1)] }, { coefficient := -1, powers := [(6, 1), (11, 1), (23, 1), (57, 1), (60, 1)] }, { coefficient := -1, powers := [(6, 1), (11, 1), (33, 1), (47, 2)] }, { coefficient := -1, powers := [(6, 1), (11, 1), (33, 1), (47, 1), (53, 1)] }, { coefficient := -1, powers := [(6, 1), (11, 1), (33, 1), (47, 1), (57, 1)] }, { coefficient := -1, powers := [(6, 1), (11, 1), (36, 1), (42, 1), (47, 1)] }, { coefficient := -1, powers := [(6, 1), (11, 1), (36, 1), (42, 1), (53, 1)] }, { coefficient := -1, powers := [(6, 1), (11, 1), (36, 1), (42, 1), (57, 1)] }, { coefficient := -1, powers := [(7, 1), (33, 1), (57, 1)] }, { coefficient := -1, powers := [(7, 1), (36, 1), (42, 1)] }, { coefficient := -1, powers := [(7, 1), (36, 1), (53, 1)] }]
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
    ¬ ∀ index : Fin 16,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component16.SelectedLeafB5_6_2_4_3.selectedHasNoCommonZero

end Krenn.Component16.SelectedLeafB5_6_2_4_3
