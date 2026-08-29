import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component54.SelectedLeafB4_1

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "eb61996511a7ad33a9eba737457231291fa4bf41be9bc03c37407ccbe9c0dd2d"
def certificateSHA256 : String := "7ea0bc4076199fad915da48f774882eb3164eaa3a0e5cbb2395d0b57fb4e3821"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 16 → Fin 645 := ![
  9,
  11,
  197,
  234,
  359,
  360,
  363,
  474,
  560,
  586,
  624,
  638,
  639,
  641,
  643,
  644
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 16 → SparsePoly (Fin 63) := ![
  [{ coefficient := 1, powers := [(5, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (50, 1)] }, { coefficient := 1, powers := [(26, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (22, 1), (59, 1)] }, { coefficient := 1, powers := [(22, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (54, 1)] }, { coefficient := 1, powers := [(30, 1), (42, 1)] }, { coefficient := 1, powers := [(33, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (57, 1)] }, { coefficient := 1, powers := [(30, 1), (48, 1)] }, { coefficient := 1, powers := [(36, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1), (50, 1)] }, { coefficient := 1, powers := [(26, 1), (46, 1), (50, 1)] }, { coefficient := 1, powers := [(50, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1), (56, 1)] }, { coefficient := 1, powers := [(22, 1), (50, 1), (56, 1)] }, { coefficient := 1, powers := [(22, 1), (53, 1)] }, { coefficient := 1, powers := [(42, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1)] }, { coefficient := 1, powers := [(6, 1), (59, 1)] }, { coefficient := 1, powers := [(26, 1), (41, 1)] }, { coefficient := 1, powers := [(26, 1), (46, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (37, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1)] }, { coefficient := 1, powers := [(3, 1), (26, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (21, 1), (59, 1)] }, { coefficient := 1, powers := [(21, 1)] }, { coefficient := 1, powers := [(26, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (38, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (41, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(41, 1)] }, { coefficient := 1, powers := [(46, 1)] }, { coefficient := 1, powers := [(52, 1)] }, { coefficient := 1, powers := [(56, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (39, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (42, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (48, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (25, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (48, 1)] }, { coefficient := 1, powers := [(8, 1), (36, 1), (42, 1)] }, { coefficient := 1, powers := [(14, 1), (25, 1), (57, 1)] }, { coefficient := 1, powers := [(14, 1), (30, 1), (48, 1)] }, { coefficient := 1, powers := [(14, 1), (36, 1), (39, 1)] }, { coefficient := 1, powers := [(20, 1), (25, 1), (54, 1)] }, { coefficient := 1, powers := [(20, 1), (30, 1), (42, 1)] }, { coefficient := 1, powers := [(20, 1), (33, 1), (39, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (61, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(41, 1)] }],
  [{ coefficient := 1, powers := [(42, 1), (62, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 16 → SparsePoly (Fin 63) := ![
  [{ coefficient := -1, powers := [(0, 1), (21, 1), (30, 1), (38, 1), (60, 1)] }, { coefficient := -1, powers := [(0, 1), (21, 1), (33, 1), (38, 1), (57, 1)] }, { coefficient := -1, powers := [(0, 1), (21, 1), (36, 1), (38, 1), (54, 1)] }, { coefficient := 1, powers := [(0, 1), (30, 1), (37, 1), (56, 1), (60, 1)] }, { coefficient := -1, powers := [(0, 1), (30, 1), (37, 1), (60, 1), (61, 1)] }, { coefficient := 1, powers := [(0, 1), (33, 1), (37, 1), (56, 1), (57, 1)] }, { coefficient := -1, powers := [(0, 1), (33, 1), (37, 1), (57, 1), (61, 1)] }, { coefficient := 1, powers := [(0, 1), (36, 1), (37, 1), (54, 1), (56, 1)] }, { coefficient := -1, powers := [(0, 1), (36, 1), (37, 1), (54, 1), (61, 1)] }, { coefficient := 1, powers := [(3, 1), (26, 1), (30, 1), (56, 1), (60, 1)] }, { coefficient := -1, powers := [(3, 1), (26, 1), (30, 1), (60, 1), (61, 1)] }, { coefficient := 1, powers := [(3, 1), (26, 1), (33, 1), (56, 1), (57, 1)] }, { coefficient := -1, powers := [(3, 1), (26, 1), (33, 1), (57, 1), (61, 1)] }, { coefficient := 1, powers := [(3, 1), (26, 1), (36, 1), (54, 1), (56, 1)] }, { coefficient := -1, powers := [(3, 1), (26, 1), (36, 1), (54, 1), (61, 1)] }, { coefficient := 1, powers := [(6, 1), (21, 1), (30, 1), (52, 1), (60, 1)] }, { coefficient := 1, powers := [(6, 1), (21, 1), (30, 1), (56, 1), (60, 1)] }, { coefficient := 1, powers := [(6, 1), (21, 1), (33, 1), (52, 1), (57, 1)] }, { coefficient := 1, powers := [(6, 1), (21, 1), (33, 1), (56, 1), (57, 1)] }, { coefficient := 1, powers := [(6, 1), (21, 1), (36, 1), (52, 1), (54, 1)] }, { coefficient := 1, powers := [(6, 1), (21, 1), (36, 1), (54, 1), (56, 1)] }, { coefficient := 1, powers := [(6, 1), (22, 1), (30, 1), (53, 1), (60, 1), (62, 1)] }, { coefficient := 1, powers := [(6, 1), (22, 1), (33, 1), (53, 1), (57, 1), (62, 1)] }, { coefficient := 1, powers := [(6, 1), (22, 1), (36, 1), (53, 1), (54, 1), (62, 1)] }, { coefficient := -1, powers := [(21, 1), (26, 1), (30, 1), (38, 1), (60, 1)] }, { coefficient := -1, powers := [(21, 1), (26, 1), (33, 1), (38, 1), (57, 1)] }, { coefficient := -1, powers := [(21, 1), (26, 1), (36, 1), (38, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (21, 1), (25, 1), (38, 1), (60, 1)] }, { coefficient := -1, powers := [(0, 1), (21, 1), (33, 1), (38, 1), (48, 1)] }, { coefficient := -1, powers := [(0, 1), (21, 1), (36, 1), (38, 1), (42, 1)] }, { coefficient := 1, powers := [(0, 1), (25, 1), (37, 1), (56, 1), (60, 1)] }, { coefficient := -1, powers := [(0, 1), (25, 1), (37, 1), (60, 1), (61, 1)] }, { coefficient := 1, powers := [(0, 1), (33, 1), (37, 1), (48, 1), (56, 1)] }, { coefficient := -1, powers := [(0, 1), (33, 1), (37, 1), (48, 1), (61, 1)] }, { coefficient := 1, powers := [(0, 1), (36, 1), (37, 1), (42, 1), (56, 1)] }, { coefficient := -1, powers := [(0, 1), (36, 1), (37, 1), (42, 1), (61, 1)] }, { coefficient := 1, powers := [(3, 1), (25, 1), (26, 1), (56, 1), (60, 1)] }, { coefficient := -1, powers := [(3, 1), (25, 1), (26, 1), (60, 1), (61, 1)] }, { coefficient := 1, powers := [(3, 1), (26, 1), (33, 1), (48, 1), (56, 1)] }, { coefficient := -1, powers := [(3, 1), (26, 1), (33, 1), (48, 1), (61, 1)] }, { coefficient := 1, powers := [(3, 1), (26, 1), (36, 1), (42, 1), (56, 1)] }, { coefficient := -1, powers := [(3, 1), (26, 1), (36, 1), (42, 1), (61, 1)] }, { coefficient := 1, powers := [(6, 1), (21, 1), (25, 1), (52, 1), (60, 1)] }, { coefficient := 1, powers := [(6, 1), (21, 1), (25, 1), (56, 1), (60, 1)] }, { coefficient := 1, powers := [(6, 1), (21, 1), (33, 1), (48, 1), (52, 1)] }, { coefficient := 1, powers := [(6, 1), (21, 1), (33, 1), (48, 1), (56, 1)] }, { coefficient := 1, powers := [(6, 1), (21, 1), (36, 1), (42, 1), (52, 1)] }, { coefficient := 1, powers := [(6, 1), (21, 1), (36, 1), (42, 1), (56, 1)] }, { coefficient := 1, powers := [(6, 1), (22, 1), (25, 1), (53, 1), (60, 1), (62, 1)] }, { coefficient := 1, powers := [(6, 1), (22, 1), (33, 1), (48, 1), (53, 1), (62, 1)] }, { coefficient := 1, powers := [(6, 1), (22, 1), (36, 1), (42, 1), (53, 1), (62, 1)] }, { coefficient := -1, powers := [(21, 1), (25, 1), (26, 1), (38, 1), (60, 1)] }, { coefficient := -1, powers := [(21, 1), (26, 1), (33, 1), (38, 1), (48, 1)] }, { coefficient := -1, powers := [(21, 1), (26, 1), (36, 1), (38, 1), (42, 1)] }],
  [{ coefficient := -1, powers := [(21, 1), (52, 1), (61, 1), (62, 1)] }, { coefficient := -1, powers := [(21, 1), (56, 1), (61, 1), (62, 1)] }, { coefficient := 1, powers := [(56, 1), (62, 1)] }, { coefficient := -1, powers := [(61, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (50, 1), (52, 1), (61, 1), (62, 1)] }, { coefficient := 1, powers := [(21, 1), (50, 1), (56, 1), (61, 1), (62, 1)] }, { coefficient := -2, powers := [(50, 1), (56, 1), (62, 1)] }, { coefficient := 1, powers := [(50, 1), (61, 1), (62, 1)] }, { coefficient := -1, powers := [(53, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (20, 1), (21, 1), (38, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (20, 1), (37, 1), (56, 1), (59, 1)] }, { coefficient := -1, powers := [(0, 1), (20, 1), (37, 1), (59, 1), (61, 1)] }, { coefficient := 1, powers := [(3, 1), (20, 1), (26, 1), (56, 1), (59, 1)] }, { coefficient := -1, powers := [(3, 1), (20, 1), (26, 1), (59, 1), (61, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1), (21, 1), (52, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1), (21, 1), (56, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1), (22, 1), (53, 1), (59, 1), (62, 1)] }, { coefficient := -1, powers := [(20, 1), (21, 1), (26, 1), (38, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (14, 1), (21, 1), (38, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (14, 1), (37, 1), (56, 1), (59, 1)] }, { coefficient := -1, powers := [(0, 1), (14, 1), (37, 1), (59, 1), (61, 1)] }, { coefficient := 1, powers := [(3, 1), (14, 1), (26, 1), (56, 1), (59, 1)] }, { coefficient := -1, powers := [(3, 1), (14, 1), (26, 1), (59, 1), (61, 1)] }, { coefficient := 1, powers := [(6, 1), (14, 1), (21, 1), (52, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (14, 1), (21, 1), (56, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (14, 1), (22, 1), (53, 1), (59, 1), (62, 1)] }, { coefficient := -1, powers := [(14, 1), (21, 1), (26, 1), (38, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (22, 1), (52, 1), (61, 1), (62, 1)] }, { coefficient := 1, powers := [(21, 1), (22, 1), (56, 1), (61, 1), (62, 1)] }, { coefficient := -2, powers := [(22, 1), (56, 1), (62, 1)] }, { coefficient := 1, powers := [(22, 1), (61, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(62, 1)] }],
  [{ coefficient := -1, powers := [(21, 1), (22, 1), (50, 1), (52, 1), (61, 1), (62, 1)] }, { coefficient := -1, powers := [(21, 1), (22, 1), (50, 1), (56, 1), (61, 1), (62, 1)] }, { coefficient := -1, powers := [(21, 1), (52, 1)] }, { coefficient := -1, powers := [(21, 1), (61, 1)] }, { coefficient := 2, powers := [(22, 1), (50, 1), (56, 1), (62, 1)] }, { coefficient := -1, powers := [(22, 1), (50, 1), (61, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(56, 1)] }, { coefficient := 1, powers := [(61, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (26, 1), (61, 1)] }, { coefficient := 1, powers := [(21, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (21, 1), (38, 1), (59, 1)] }, { coefficient := -1, powers := [(0, 1), (37, 1), (56, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (37, 1), (59, 1), (61, 1)] }, { coefficient := -1, powers := [(3, 1), (26, 1), (56, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (26, 1), (59, 1), (61, 1)] }, { coefficient := -1, powers := [(6, 1), (21, 1), (52, 1), (59, 1)] }, { coefficient := -1, powers := [(6, 1), (21, 1), (56, 1), (59, 1)] }, { coefficient := -1, powers := [(6, 1), (22, 1), (53, 1), (59, 1), (62, 1)] }, { coefficient := 1, powers := [(21, 1), (26, 1), (38, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(21, 1), (26, 1), (38, 1), (59, 1)] }, { coefficient := -1, powers := [(21, 1), (26, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(21, 1), (46, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(0, 1), (21, 1), (38, 1), (39, 1), (59, 1), (60, 1)] }, { coefficient := -1, powers := [(0, 1), (21, 1), (38, 1), (42, 1), (57, 1), (59, 1)] }, { coefficient := -1, powers := [(0, 1), (21, 1), (38, 1), (48, 1), (54, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (37, 1), (39, 1), (56, 1), (59, 1), (60, 1)] }, { coefficient := -1, powers := [(0, 1), (37, 1), (39, 1), (59, 1), (60, 1), (61, 1)] }, { coefficient := 1, powers := [(0, 1), (37, 1), (42, 1), (56, 1), (57, 1), (59, 1)] }, { coefficient := -1, powers := [(0, 1), (37, 1), (42, 1), (57, 1), (59, 1), (61, 1)] }, { coefficient := 1, powers := [(0, 1), (37, 1), (48, 1), (54, 1), (56, 1), (59, 1)] }, { coefficient := -1, powers := [(0, 1), (37, 1), (48, 1), (54, 1), (59, 1), (61, 1)] }, { coefficient := 1, powers := [(3, 1), (26, 1), (39, 1), (56, 1), (59, 1), (60, 1)] }, { coefficient := -1, powers := [(3, 1), (26, 1), (39, 1), (59, 1), (60, 1), (61, 1)] }, { coefficient := 1, powers := [(3, 1), (26, 1), (42, 1), (56, 1), (57, 1), (59, 1)] }, { coefficient := -1, powers := [(3, 1), (26, 1), (42, 1), (57, 1), (59, 1), (61, 1)] }, { coefficient := 1, powers := [(3, 1), (26, 1), (48, 1), (54, 1), (56, 1), (59, 1)] }, { coefficient := -1, powers := [(3, 1), (26, 1), (48, 1), (54, 1), (59, 1), (61, 1)] }, { coefficient := 1, powers := [(6, 1), (21, 1), (39, 1), (52, 1), (59, 1), (60, 1)] }, { coefficient := 1, powers := [(6, 1), (21, 1), (39, 1), (56, 1), (59, 1), (60, 1)] }, { coefficient := 1, powers := [(6, 1), (21, 1), (42, 1), (52, 1), (57, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (21, 1), (42, 1), (56, 1), (57, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (21, 1), (48, 1), (52, 1), (54, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (21, 1), (48, 1), (54, 1), (56, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (22, 1), (39, 1), (53, 1), (59, 1), (60, 1), (62, 1)] }, { coefficient := 1, powers := [(6, 1), (22, 1), (42, 1), (53, 1), (57, 1), (59, 1), (62, 1)] }, { coefficient := 1, powers := [(6, 1), (22, 1), (48, 1), (53, 1), (54, 1), (59, 1), (62, 1)] }, { coefficient := -1, powers := [(21, 1), (26, 1), (38, 1), (39, 1), (59, 1), (60, 1)] }, { coefficient := -1, powers := [(21, 1), (26, 1), (38, 1), (42, 1), (57, 1), (59, 1)] }, { coefficient := -1, powers := [(21, 1), (26, 1), (38, 1), (48, 1), (54, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (21, 1), (26, 1), (56, 1), (61, 1)] }, { coefficient := -1, powers := [(0, 1), (21, 1), (56, 1)] }, { coefficient := 1, powers := [(21, 1), (22, 1), (26, 1), (50, 1), (52, 1), (61, 1), (62, 1)] }, { coefficient := 1, powers := [(21, 1), (22, 1), (26, 1), (50, 1), (56, 1), (61, 1), (62, 1)] }, { coefficient := 1, powers := [(21, 1), (26, 1), (52, 1)] }, { coefficient := -1, powers := [(21, 1)] }, { coefficient := -2, powers := [(22, 1), (26, 1), (50, 1), (56, 1), (62, 1)] }, { coefficient := 1, powers := [(22, 1), (26, 1), (50, 1), (61, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (56, 1)] }, { coefficient := 1, powers := [(21, 1), (26, 1), (52, 1), (61, 1)] }, { coefficient := 1, powers := [(21, 1), (26, 1), (56, 1), (61, 1)] }, { coefficient := -1, powers := [(26, 1), (56, 1)] }, { coefficient := 1, powers := [(26, 1), (61, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
/-- Lean replays the exact selected-row integer certificate. -/
theorem constantIdentity :
    ∑ index, (multipliers index).toPoly *
      (selectedEquations index).toPoly = C (2 : ℤ) := by
  simp (config := { maxSteps := 1000000 })
    [Fin.sum_univ_succ, multipliers, selectedEquations,
    SparsePoly.toPoly, SparseTerm.toPoly]
  ring

/-- The selected rows have no common zero in a characteristic-zero ring. -/
theorem selectedHasNoCommonZero {R : Type*} [CommRing R] [Nontrivial R] [CharZero R]
    (values : Fin 63 → R) :
    ¬ ∀ index : Fin 16,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((2 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (2 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (2 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component54.SelectedLeafB4_1.selectedHasNoCommonZero

end Krenn.Component54.SelectedLeafB4_1
