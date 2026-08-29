import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component16.SelectedLeafB7_2_3

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "6f2886ea5965ffdc2cdabb4c04d1a92a6caf2b001760af0f664945e7db5722a2"
def certificateSHA256 : String := "641cc167cb55907305e75ff885b7980e184ff4693c9de24668ff2f1d01ac7388"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 22 → Fin 671 := ![
  0,
  1,
  2,
  3,
  6,
  13,
  23,
  142,
  302,
  316,
  366,
  440,
  448,
  571,
  588,
  595,
  661,
  662,
  663,
  667,
  669,
  670
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 22 → SparsePoly (Fin 68) := ![
  [{ coefficient := 1, powers := [(1, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (55, 1)] }, { coefficient := 1, powers := [(21, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (61, 1)] }, { coefficient := 1, powers := [(13, 1), (50, 1)] }, { coefficient := 1, powers := [(20, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (55, 1)] }, { coefficient := 1, powers := [(31, 1), (43, 1)] }, { coefficient := 1, powers := [(34, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (25, 1), (60, 1)] }, { coefficient := 1, powers := [(25, 1)] }, { coefficient := 1, powers := [(29, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1)] }, { coefficient := 1, powers := [(13, 1), (31, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (61, 1)] }, { coefficient := 1, powers := [(13, 1), (27, 1), (48, 1)] }, { coefficient := 1, powers := [(13, 1), (58, 1)] }, { coefficient := 1, powers := [(20, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (45, 1), (54, 1)] }, { coefficient := 1, powers := [(25, 1), (58, 1)] }, { coefficient := 1, powers := [(31, 1), (50, 1)] }, { coefficient := 1, powers := [(37, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (40, 1), (61, 1)] }, { coefficient := 1, powers := [(0, 1), (43, 1), (58, 1)] }, { coefficient := 1, powers := [(0, 1), (50, 1), (55, 1)] }, { coefficient := 1, powers := [(22, 1), (45, 1), (55, 1)] }, { coefficient := 1, powers := [(27, 1), (43, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (43, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (57, 1)] }, { coefficient := 1, powers := [(13, 1), (25, 1), (57, 1)] }, { coefficient := 1, powers := [(13, 1), (30, 1), (49, 1)] }, { coefficient := 1, powers := [(19, 1), (30, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (40, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (43, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (50, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (37, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (25, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (50, 1)] }, { coefficient := 1, powers := [(8, 1), (37, 1), (43, 1)] }, { coefficient := 1, powers := [(13, 1), (25, 1), (58, 1)] }, { coefficient := 1, powers := [(13, 1), (31, 1), (50, 1)] }, { coefficient := 1, powers := [(13, 1), (37, 1), (40, 1)] }, { coefficient := 1, powers := [(20, 1), (25, 1), (55, 1)] }, { coefficient := 1, powers := [(20, 1), (31, 1), (43, 1)] }, { coefficient := 1, powers := [(20, 1), (34, 1), (40, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(43, 1)] }],
  [{ coefficient := 1, powers := [(57, 1), (66, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(58, 1), (67, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 22 → SparsePoly (Fin 68) := ![
  [{ coefficient := -2, powers := [(8, 1), (29, 1), (61, 1), (63, 1)] }, { coefficient := -1, powers := [(13, 1), (30, 1), (58, 1), (63, 1), (66, 1)] }],
  [{ coefficient := -2, powers := [(13, 1), (31, 1), (58, 1), (63, 1), (67, 1)] }],
  [{ coefficient := -1, powers := [(13, 1), (25, 1), (45, 1), (58, 1), (63, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (21, 1), (50, 1), (58, 1), (62, 1), (63, 1), (67, 1)] }, { coefficient := -1, powers := [(2, 1), (22, 1), (45, 1), (58, 1), (62, 1), (63, 1), (67, 1)] }, { coefficient := 1, powers := [(5, 1), (37, 1), (58, 1), (63, 1), (67, 1)] }, { coefficient := -1, powers := [(20, 1), (25, 1), (58, 1), (63, 1), (67, 1)] }, { coefficient := 2, powers := [(20, 1), (25, 1), (63, 1)] }],
  [{ coefficient := -2, powers := [(8, 1), (25, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(25, 1), (27, 1), (58, 1), (67, 1)] }, { coefficient := 2, powers := [(25, 1), (27, 1)] }],
  [{ coefficient := -1, powers := [(19, 1), (50, 1), (58, 1), (67, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (50, 1), (58, 1), (62, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(31, 1), (58, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (58, 1), (67, 1)] }],
  [{ coefficient := 2, powers := [(8, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(50, 1), (58, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (58, 1), (67, 1)] }, { coefficient := -2, powers := [(25, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (58, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (58, 1), (62, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(58, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(58, 1), (67, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (40, 1), (58, 1), (61, 1), (67, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (21, 1), (50, 1), (55, 1), (58, 1), (62, 1), (67, 1)] }, { coefficient := 1, powers := [(2, 1), (22, 1), (45, 1), (55, 1), (58, 1), (62, 1), (67, 1)] }, { coefficient := -1, powers := [(5, 1), (37, 1), (55, 1), (58, 1), (67, 1)] }, { coefficient := 2, powers := [(8, 1), (29, 1), (49, 1), (61, 1)] }, { coefficient := 1, powers := [(13, 1), (25, 1), (45, 1), (54, 1), (58, 1), (67, 1)] }, { coefficient := 1, powers := [(13, 1), (30, 1), (49, 1), (58, 1), (66, 1)] }, { coefficient := 2, powers := [(13, 1), (31, 1), (50, 1), (58, 1), (67, 1)] }, { coefficient := 1, powers := [(20, 1), (25, 1), (55, 1), (58, 1), (67, 1)] }, { coefficient := -2, powers := [(20, 1), (25, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (2, 1), (58, 2), (62, 1), (67, 1)] }, { coefficient := -1, powers := [(2, 1), (27, 1), (45, 1), (58, 1), (62, 1), (67, 1)] }, { coefficient := -1, powers := [(2, 1), (57, 1), (58, 1), (66, 1)] }, { coefficient := 1, powers := [(2, 1), (58, 2), (67, 1)] }, { coefficient := 1, powers := [(8, 1), (37, 1), (58, 1), (67, 1)] }, { coefficient := -1, powers := [(19, 1), (30, 1), (58, 1), (66, 1)] }, { coefficient := -1, powers := [(20, 1), (31, 1), (58, 1), (67, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (34, 1), (58, 1)] }, { coefficient := -1, powers := [(13, 1), (25, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (34, 1), (58, 1)] }, { coefficient := -1, powers := [(13, 1), (25, 1), (58, 1)] }, { coefficient := -1, powers := [] }]
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
    ¬ ∀ index : Fin 22,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component16.SelectedLeafB7_2_3.selectedHasNoCommonZero

end Krenn.Component16.SelectedLeafB7_2_3
