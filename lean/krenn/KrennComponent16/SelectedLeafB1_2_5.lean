import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component16.SelectedLeafB1_2_5

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "fbf7ba74eab5a7c789d484cecbb1d8ac525c97e79ebff4b27eae00deb946264c"
def certificateSHA256 : String := "3a3fe9a21e4bb9f5165945e4a6657165cf990898b7882c12377fe15aa94c5087"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 21 → Fin 671 := ![
  4,
  13,
  23,
  175,
  176,
  247,
  302,
  316,
  321,
  430,
  440,
  442,
  448,
  462,
  503,
  585,
  661,
  662,
  667,
  669,
  670
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 21 → SparsePoly (Fin 66) := ![
  [{ coefficient := 1, powers := [(3, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1), (55, 1)] }, { coefficient := 1, powers := [(55, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (48, 1), (55, 1)] }, { coefficient := 1, powers := [(45, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (21, 1), (57, 1)] }, { coefficient := 1, powers := [(13, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (61, 1)] }, { coefficient := 1, powers := [(13, 1), (50, 1)] }, { coefficient := 1, powers := [(20, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (55, 1)] }, { coefficient := 1, powers := [(31, 1), (43, 1)] }, { coefficient := 1, powers := [(34, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1), (53, 1)] }, { coefficient := 1, powers := [(21, 1), (45, 1), (53, 1)] }, { coefficient := 1, powers := [(45, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (54, 1)] }, { coefficient := 1, powers := [(3, 1), (27, 1), (60, 1)] }, { coefficient := 1, powers := [(21, 1), (54, 1)] }, { coefficient := 1, powers := [(27, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1)] }, { coefficient := 1, powers := [(13, 1), (31, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (37, 1)] }, { coefficient := 1, powers := [(24, 1), (45, 1)] }, { coefficient := 1, powers := [(29, 1), (45, 1)] }, { coefficient := 1, powers := [(37, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (61, 1)] }, { coefficient := 1, powers := [(13, 1), (27, 1), (48, 1)] }, { coefficient := 1, powers := [(13, 1), (58, 1)] }, { coefficient := 1, powers := [(20, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1), (54, 1)] }, { coefficient := 1, powers := [(21, 1), (45, 1), (54, 1)] }, { coefficient := 1, powers := [(21, 1), (58, 1)] }, { coefficient := 1, powers := [(27, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (31, 1), (61, 1)] }, { coefficient := 1, powers := [(3, 1), (34, 1), (58, 1)] }, { coefficient := 1, powers := [(3, 1), (37, 1), (55, 1)] }, { coefficient := 1, powers := [(24, 1), (45, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (53, 1)] }, { coefficient := 1, powers := [(3, 1), (60, 1)] }, { coefficient := 1, powers := [(21, 1), (53, 1)] }, { coefficient := 1, powers := [(21, 1), (57, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (40, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (43, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (50, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (37, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (25, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (50, 1)] }, { coefficient := 1, powers := [(8, 1), (37, 1), (43, 1)] }, { coefficient := 1, powers := [(13, 1), (25, 1), (58, 1)] }, { coefficient := 1, powers := [(13, 1), (31, 1), (50, 1)] }, { coefficient := 1, powers := [(13, 1), (37, 1), (40, 1)] }, { coefficient := 1, powers := [(20, 1), (25, 1), (55, 1)] }, { coefficient := 1, powers := [(20, 1), (31, 1), (43, 1)] }, { coefficient := 1, powers := [(20, 1), (34, 1), (40, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1)] }],
  [{ coefficient := 1, powers := [(43, 1)] }],
  [{ coefficient := 1, powers := [(57, 1)] }],
  [{ coefficient := 1, powers := [(58, 1), (65, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 21 → SparsePoly (Fin 66) := ![
  [{ coefficient := -1, powers := [(2, 1), (40, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (25, 1), (27, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (19, 1), (50, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (5, 1), (37, 1), (60, 1)] }, { coefficient := 1, powers := [(3, 1), (20, 1), (25, 1), (60, 1)] }, { coefficient := -1, powers := [(5, 1), (37, 1), (38, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (29, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (31, 1), (50, 1), (60, 1)] }, { coefficient := -1, powers := [(3, 1), (37, 1), (40, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (31, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (20, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (53, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(45, 1), (53, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (50, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (55, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (25, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(53, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(27, 1), (45, 1), (53, 1), (65, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(3, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (5, 1), (37, 1), (47, 1), (55, 1), (60, 1)] }, { coefficient := -1, powers := [(3, 1), (20, 1), (25, 1), (47, 1), (55, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (48, 1), (55, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (37, 1), (38, 1), (47, 1), (55, 1), (60, 1)] }, { coefficient := -1, powers := [(53, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (3, 1), (58, 1), (60, 1)] }, { coefficient := -1, powers := [(3, 1), (8, 1), (37, 1), (60, 1)] }, { coefficient := 1, powers := [(3, 1), (20, 1), (31, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (13, 1), (21, 1), (31, 1), (50, 1), (60, 1)] }, { coefficient := 1, powers := [(3, 1), (13, 1), (21, 1), (37, 1), (40, 1), (60, 1)] }, { coefficient := 1, powers := [(21, 1), (27, 1), (45, 1), (53, 1), (65, 1)] }, { coefficient := -1, powers := [(21, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (53, 1)] }]
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
    ¬ ∀ index : Fin 21,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component16.SelectedLeafB1_2_5.selectedHasNoCommonZero

end Krenn.Component16.SelectedLeafB1_2_5
