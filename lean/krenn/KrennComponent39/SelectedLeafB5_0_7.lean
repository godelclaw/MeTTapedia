import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component39.SelectedLeafB5_0_7

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "39ac2991c6908c547fdf5ae803bbaf0336975e4ecb7149836ee2091dd8285733"
def certificateSHA256 : String := "3a298f717661d0713e439b244857b21605be3fef5326f729b3ee3558cc23f3f9"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 14 → Fin 670 := ![
  187,
  188,
  190,
  300,
  316,
  319,
  342,
  397,
  417,
  536,
  607,
  663,
  665,
  669
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 14 → SparsePoly (Fin 66) := ![
  [{ coefficient := 1, powers := [(16, 1), (18, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (42, 1)] }, { coefficient := 1, powers := [(17, 1), (18, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (45, 1)] }, { coefficient := -1, powers := [(27, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1)] }, { coefficient := 1, powers := [(18, 1), (42, 1)] }, { coefficient := 1, powers := [(23, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (45, 1)] }, { coefficient := 1, powers := [(17, 1), (39, 1)] }, { coefficient := 1, powers := [(17, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1), (51, 1)] }, { coefficient := 1, powers := [(18, 1), (42, 1), (51, 1)] }, { coefficient := 1, powers := [(42, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (42, 1), (51, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1), (42, 1)] }, { coefficient := 1, powers := [(17, 1), (21, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (23, 1), (45, 1)] }, { coefficient := 1, powers := [(17, 1), (23, 1), (39, 1)] }, { coefficient := 1, powers := [(17, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (45, 1)] }, { coefficient := 1, powers := [(16, 1), (26, 1), (45, 1)] }, { coefficient := 1, powers := [(17, 1), (26, 1), (39, 1)] }, { coefficient := 1, powers := [(17, 1), (27, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (34, 1), (39, 1)] }, { coefficient := 1, powers := [(26, 1), (39, 1), (42, 1)] }, { coefficient := 1, powers := [(26, 1), (45, 1)] }, { coefficient := 1, powers := [(27, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (39, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (45, 1), (53, 1)] }, { coefficient := 1, powers := [(24, 1), (39, 1), (42, 1)] }, { coefficient := 1, powers := [(24, 1), (45, 1)] }, { coefficient := 1, powers := [(42, 1), (53, 1)] }, { coefficient := 1, powers := [(57, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(39, 1)] }],
  [{ coefficient := 1, powers := [(57, 1), (65, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 14 → SparsePoly (Fin 66) := ![
  [{ coefficient := -1, powers := [(0, 1), (27, 1), (45, 1), (53, 1), (62, 1), (65, 1)] }, { coefficient := -1, powers := [(24, 1), (27, 1), (45, 1), (62, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (27, 1), (53, 1), (62, 1), (65, 1)] }, { coefficient := -1, powers := [(24, 1), (27, 1), (62, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(16, 1), (23, 1), (53, 1), (62, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (51, 1), (53, 1), (62, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (18, 1), (27, 1), (53, 1), (62, 1), (65, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (27, 1), (62, 1), (65, 1)] }, { coefficient := 1, powers := [(21, 1), (23, 1), (53, 1), (62, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (53, 1), (62, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(23, 1), (53, 1), (62, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (27, 1), (53, 1), (62, 1), (65, 1)] }, { coefficient := 1, powers := [(24, 1), (27, 1), (62, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (53, 1), (62, 1), (65, 1)] }, { coefficient := -1, powers := [(24, 1), (62, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (16, 1), (53, 1), (62, 1), (65, 1)] }, { coefficient := 1, powers := [(16, 1), (24, 1), (62, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(65, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1), (53, 1), (65, 1)] }, { coefficient := 1, powers := [(24, 1), (45, 1), (65, 1)] }, { coefficient := 1, powers := [(42, 1), (53, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (6, 1), (16, 1), (34, 1), (53, 1), (62, 1), (65, 1)] }, { coefficient := -1, powers := [(0, 1), (16, 1), (26, 1), (42, 1), (53, 1), (62, 1), (65, 1)] }, { coefficient := -1, powers := [(0, 1), (17, 1), (18, 1), (27, 1), (53, 1), (62, 1), (65, 1)] }, { coefficient := -1, powers := [(0, 1), (17, 1), (23, 1), (27, 1), (53, 1), (62, 1), (65, 1)] }, { coefficient := 1, powers := [(0, 1), (17, 1), (26, 1), (53, 1), (62, 1), (65, 1)] }, { coefficient := -1, powers := [(0, 1), (57, 1), (65, 1)] }, { coefficient := -1, powers := [(6, 1), (16, 1), (24, 1), (34, 1), (62, 1), (65, 1)] }, { coefficient := -1, powers := [(16, 1), (24, 1), (26, 1), (42, 1), (62, 1), (65, 1)] }, { coefficient := -1, powers := [(17, 1), (18, 1), (24, 1), (27, 1), (62, 1), (65, 1)] }, { coefficient := -1, powers := [(17, 1), (21, 1), (23, 1), (53, 1), (62, 1), (65, 1)] }, { coefficient := -1, powers := [(17, 1), (23, 1), (24, 1), (27, 1), (62, 1), (65, 1)] }, { coefficient := 1, powers := [(17, 1), (24, 1), (26, 1), (62, 1), (65, 1)] }, { coefficient := -1, powers := [(24, 1), (42, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [] }]
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
    ¬ ∀ index : Fin 14,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component39.SelectedLeafB5_0_7.selectedHasNoCommonZero

end Krenn.Component39.SelectedLeafB5_0_7
