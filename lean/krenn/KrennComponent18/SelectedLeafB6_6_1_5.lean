import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component18.SelectedLeafB6_6_1_5

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "825e432482d6020c606a7087c66d8ea3b921dd0543b63b3964f791e7e0b0cda0"
def certificateSHA256 : String := "6aef12b082b18a3f2414d29da84dd2a277fc4f0bfb8cc0c8ba1781236b7e6ebc"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 23 → Fin 670 := ![
  0,
  7,
  10,
  15,
  19,
  143,
  150,
  165,
  299,
  301,
  318,
  349,
  437,
  443,
  496,
  581,
  657,
  659,
  660,
  663,
  665,
  667,
  669
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 23 → SparsePoly (Fin 68) := ![
  [{ coefficient := 1, powers := [(3, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(15, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (54, 1)] }, { coefficient := 1, powers := [(15, 1), (21, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (29, 1)] }, { coefficient := 1, powers := [(15, 1), (23, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (29, 1)] }, { coefficient := -1, powers := [(23, 1), (27, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (53, 1)] }, { coefficient := 1, powers := [(11, 1), (27, 1), (53, 1)] }, { coefficient := 1, powers := [(15, 1), (21, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (60, 1)] }, { coefficient := 1, powers := [(13, 1), (49, 1)] }, { coefficient := 1, powers := [(18, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (54, 1)] }, { coefficient := 1, powers := [(31, 1), (43, 1)] }, { coefficient := 1, powers := [(34, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (31, 1), (59, 1)] }, { coefficient := 1, powers := [(23, 1), (53, 1)] }, { coefficient := 1, powers := [(31, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1)] }, { coefficient := 1, powers := [(13, 1), (31, 1)] }, { coefficient := 1, powers := [(17, 1), (23, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (60, 1)] }, { coefficient := 1, powers := [(13, 1), (26, 1), (47, 1)] }, { coefficient := 1, powers := [(13, 1), (57, 1)] }, { coefficient := 1, powers := [(18, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (31, 1), (60, 1)] }, { coefficient := 1, powers := [(3, 1), (34, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (37, 1), (54, 1)] }, { coefficient := 1, powers := [(23, 1), (45, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (52, 1)] }, { coefficient := 1, powers := [(3, 1), (59, 1)] }, { coefficient := 1, powers := [(19, 1), (52, 1)] }, { coefficient := 1, powers := [(19, 1), (56, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (40, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (43, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (49, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (37, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (49, 1)] }, { coefficient := 1, powers := [(8, 1), (37, 1), (43, 1)] }, { coefficient := 1, powers := [(13, 1), (24, 1), (57, 1)] }, { coefficient := 1, powers := [(13, 1), (31, 1), (49, 1)] }, { coefficient := 1, powers := [(13, 1), (37, 1), (40, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (54, 1)] }, { coefficient := 1, powers := [(18, 1), (31, 1), (43, 1)] }, { coefficient := 1, powers := [(18, 1), (34, 1), (40, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(43, 1)] }],
  [{ coefficient := 1, powers := [(56, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (66, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(31, 1), (67, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 23 → SparsePoly (Fin 68) := ![
  [{ coefficient := 1, powers := [(5, 1), (31, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (31, 1), (49, 1), (59, 1), (66, 1)] }, { coefficient := -1, powers := [(3, 1), (37, 1), (40, 1), (59, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (24, 1), (26, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (18, 1), (21, 1), (24, 1), (59, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (17, 1), (49, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (45, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (18, 1), (24, 1), (59, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (53, 1), (62, 1), (67, 1)] }],
  [{ coefficient := -1, powers := [(11, 1), (53, 1), (62, 1), (67, 1)] }],
  [{ coefficient := -1, powers := [(23, 1), (62, 1), (67, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (31, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (18, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(67, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (49, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (24, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(31, 1), (67, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(3, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (18, 1), (24, 1), (54, 1), (59, 1)] }, { coefficient := 1, powers := [(23, 1), (53, 1), (67, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (40, 1), (59, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (3, 1), (57, 1), (59, 1)] }, { coefficient := -1, powers := [(3, 1), (8, 1), (37, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (18, 1), (31, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (31, 1), (67, 1)] }, { coefficient := -1, powers := [(19, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (13, 1), (31, 1), (49, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (13, 1), (37, 1), (40, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (52, 1)] }, { coefficient := 1, powers := [(19, 1), (52, 1)] }]
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
    ¬ ∀ index : Fin 23,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component18.SelectedLeafB6_6_1_5.selectedHasNoCommonZero

end Krenn.Component18.SelectedLeafB6_6_1_5
