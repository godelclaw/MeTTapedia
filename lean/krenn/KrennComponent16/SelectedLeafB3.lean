import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component16.SelectedLeafB3

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "477f8f911041c9aa6b0700cd3a847935386c3e0d330e95b5abda1890a8a7c51c"
def certificateSHA256 : String := "9937764e7ed7237395407ec930154a7f03f124675d0c52e05dda56066e692207"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 26 → Fin 665 := ![
  0,
  1,
  2,
  3,
  4,
  5,
  6,
  23,
  107,
  148,
  173,
  316,
  348,
  366,
  440,
  441,
  445,
  454,
  471,
  474,
  475,
  571,
  649,
  661,
  662,
  663
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 26 → SparsePoly (Fin 64) := ![
  [{ coefficient := 1, powers := [(1, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (34, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (34, 1)] }, { coefficient := 1, powers := [(34, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1), (57, 1)] }, { coefficient := 1, powers := [(43, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (55, 1)] }, { coefficient := 1, powers := [(31, 1), (43, 1)] }, { coefficient := 1, powers := [(34, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (31, 1), (60, 1)] }, { coefficient := 1, powers := [(24, 1), (54, 1)] }, { coefficient := 1, powers := [(31, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (25, 1), (60, 1)] }, { coefficient := 1, powers := [(25, 1)] }, { coefficient := 1, powers := [(29, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1)] }, { coefficient := 1, powers := [(13, 1), (31, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (36, 1)] }, { coefficient := 1, powers := [(6, 1), (33, 1)] }, { coefficient := 1, powers := [(33, 1), (38, 1)] }, { coefficient := 1, powers := [(36, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (60, 1)] }, { coefficient := 1, powers := [(19, 1), (22, 1), (53, 1)] }, { coefficient := 1, powers := [(19, 1), (22, 1), (57, 1)] }, { coefficient := 1, powers := [(19, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (42, 1)] }, { coefficient := 1, powers := [(19, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (53, 1)] }, { coefficient := 1, powers := [(19, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (49, 1), (53, 1)] }, { coefficient := 1, powers := [(22, 1), (53, 1)] }, { coefficient := 1, powers := [(22, 1), (57, 1)] }, { coefficient := 1, powers := [(49, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (38, 1), (60, 1)] }, { coefficient := 1, powers := [(1, 1)] }, { coefficient := 1, powers := [(11, 1), (36, 1), (38, 1)] }, { coefficient := 1, powers := [(16, 1), (33, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (40, 1), (60, 1)] }, { coefficient := 1, powers := [(1, 1), (49, 1), (54, 1)] }, { coefficient := 1, powers := [(11, 1), (36, 1), (40, 1)] }, { coefficient := 1, powers := [(16, 1), (33, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (45, 1), (54, 1)] }, { coefficient := 1, powers := [(25, 1), (58, 1)] }, { coefficient := 1, powers := [(31, 1), (50, 1)] }, { coefficient := 1, powers := [(37, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (39, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (42, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (47, 1), (53, 1)] }, { coefficient := 1, powers := [(42, 1)] }, { coefficient := 1, powers := [(47, 1)] }, { coefficient := 1, powers := [(53, 1)] }, { coefficient := 1, powers := [(57, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (40, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (43, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (50, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (37, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (25, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (50, 1)] }, { coefficient := 1, powers := [(8, 1), (37, 1), (43, 1)] }, { coefficient := 1, powers := [(13, 1), (25, 1), (58, 1)] }, { coefficient := 1, powers := [(13, 1), (31, 1), (50, 1)] }, { coefficient := 1, powers := [(13, 1), (37, 1), (40, 1)] }, { coefficient := 1, powers := [(20, 1), (25, 1), (55, 1)] }, { coefficient := 1, powers := [(20, 1), (31, 1), (43, 1)] }, { coefficient := 1, powers := [(20, 1), (34, 1), (40, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (62, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 26 → SparsePoly (Fin 64) := ![
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (54, 1), (61, 1), (62, 1)] }, { coefficient := -1, powers := [(8, 1), (29, 1), (61, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (55, 1), (62, 1)] }, { coefficient := -1, powers := [(13, 1), (31, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (24, 1), (61, 1), (62, 1)] }, { coefficient := -1, powers := [(13, 1), (25, 1), (45, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (50, 1), (62, 1)] }, { coefficient := 1, powers := [(5, 1), (37, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (31, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (16, 1), (34, 1), (58, 1), (62, 1)] }, { coefficient := -1, powers := [(11, 1), (34, 1), (38, 1), (58, 1), (62, 1)] }, { coefficient := 1, powers := [(16, 1), (34, 1), (38, 1), (58, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (25, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(19, 1), (50, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (33, 1), (58, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (16, 1), (33, 1), (58, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (58, 1)] }, { coefficient := 1, powers := [(8, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(20, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(50, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (16, 1), (34, 1), (58, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(1, 1), (34, 1), (38, 1), (58, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (22, 1), (34, 1), (38, 1), (58, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (19, 1), (34, 1), (38, 1), (58, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (40, 1), (61, 1), (62, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (58, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (38, 1), (61, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(13, 1)] }],
  [{ coefficient := -1, powers := [(1, 1), (19, 1), (22, 1), (34, 1), (38, 1), (58, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1), (19, 1), (22, 1), (34, 1), (38, 1), (39, 1), (58, 1), (60, 1), (62, 1)] }, { coefficient := 1, powers := [(1, 1), (19, 1), (22, 1), (34, 1), (38, 1), (42, 1), (57, 1), (58, 1), (62, 1)] }, { coefficient := 1, powers := [(1, 1), (19, 1), (22, 1), (34, 1), (38, 1), (47, 1), (53, 1), (58, 1), (62, 1)] }, { coefficient := -1, powers := [(1, 1), (19, 1), (34, 1), (38, 1), (49, 1), (53, 1), (58, 1), (62, 1)] }, { coefficient := -1, powers := [(2, 1), (43, 1), (57, 1), (58, 1)] }, { coefficient := -1, powers := [(8, 1), (37, 1), (43, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (40, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (24, 1), (54, 1), (61, 1)] }, { coefficient := -1, powers := [(5, 1), (34, 1), (58, 1)] }, { coefficient := -1, powers := [(5, 1), (37, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (29, 1), (49, 1), (61, 1)] }, { coefficient := 1, powers := [(13, 1), (25, 1), (45, 1), (54, 1)] }, { coefficient := 1, powers := [(13, 1), (31, 1), (50, 1)] }]
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
    (values : Fin 64 → R) :
    ¬ ∀ index : Fin 26,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component16.SelectedLeafB3.selectedHasNoCommonZero

end Krenn.Component16.SelectedLeafB3
