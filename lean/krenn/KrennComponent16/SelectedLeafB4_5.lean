import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component16.SelectedLeafB4_5

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "6e6dd66ef3cb3c4387d2531afddde8d90307abfeae99ba36c3d583a22325bc53"
def certificateSHA256 : String := "11a59eabb5147716798c3bcbbc75ec914df9fe9df9a934dd6954f879e95b318c"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 34 → Fin 668 := ![
  4,
  8,
  15,
  21,
  24,
  25,
  30,
  33,
  162,
  166,
  167,
  170,
  173,
  299,
  300,
  302,
  314,
  315,
  316,
  408,
  428,
  436,
  523,
  540,
  571,
  585,
  609,
  612,
  660,
  661,
  663,
  664,
  666,
  667
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 34 → SparsePoly (Fin 65) := ![
  [{ coefficient := 1, powers := [(3, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (33, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(26, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(28, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(30, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(43, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (47, 1)] }, { coefficient := 1, powers := [(13, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (21, 1)] }, { coefficient := 1, powers := [(19, 1), (26, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (45, 1)] }, { coefficient := 1, powers := [(20, 1), (21, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (45, 1)] }, { coefficient := 1, powers := [(29, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1), (57, 1)] }, { coefficient := 1, powers := [(43, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (50, 1)] }, { coefficient := 1, powers := [(22, 1), (45, 1)] }, { coefficient := 1, powers := [(26, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (47, 1)] }, { coefficient := 1, powers := [(4, 1), (36, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (61, 1)] }, { coefficient := 1, powers := [(13, 1), (50, 1)] }, { coefficient := 1, powers := [(20, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (48, 1)] }, { coefficient := 1, powers := [(20, 1), (42, 1)] }, { coefficient := 1, powers := [(20, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (53, 1)] }, { coefficient := 1, powers := [(25, 1), (57, 1)] }, { coefficient := 1, powers := [(30, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (55, 1)] }, { coefficient := 1, powers := [(31, 1), (43, 1)] }, { coefficient := 1, powers := [(34, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (26, 1), (48, 1)] }, { coefficient := 1, powers := [(20, 1), (26, 1), (42, 1)] }, { coefficient := 1, powers := [(20, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (48, 1)] }, { coefficient := 1, powers := [(26, 1), (42, 1), (45, 1)] }, { coefficient := 1, powers := [(26, 1), (48, 1)] }, { coefficient := 1, powers := [(45, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (50, 1)] }, { coefficient := 1, powers := [(5, 1), (37, 1)] }, { coefficient := 1, powers := [(19, 1), (29, 1), (50, 1)] }, { coefficient := 1, powers := [(20, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (23, 1), (60, 1)] }, { coefficient := 1, powers := [(6, 1), (33, 1), (47, 1)] }, { coefficient := 1, powers := [(6, 1), (36, 1), (42, 1)] }, { coefficient := 1, powers := [(23, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (23, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (47, 1)] }, { coefficient := 1, powers := [(8, 1), (36, 1), (42, 1)] }, { coefficient := 1, powers := [(19, 1), (23, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (45, 1), (54, 1)] }, { coefficient := 1, powers := [(25, 1), (58, 1)] }, { coefficient := 1, powers := [(31, 1), (50, 1)] }, { coefficient := 1, powers := [(37, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (53, 1)] }, { coefficient := 1, powers := [(3, 1), (60, 1)] }, { coefficient := 1, powers := [(21, 1), (53, 1)] }, { coefficient := 1, powers := [(21, 1), (57, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(23, 1), (53, 1)] }, { coefficient := 1, powers := [(23, 1), (57, 1)] }, { coefficient := 1, powers := [(28, 1), (42, 1)] }, { coefficient := 1, powers := [(28, 1), (47, 1)] }, { coefficient := 1, powers := [(33, 1), (39, 1)] }, { coefficient := 1, powers := [(36, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1), (58, 1)] }, { coefficient := 1, powers := [(0, 1), (48, 1), (54, 1)] }, { coefficient := 1, powers := [(27, 1), (42, 1), (45, 1)] }, { coefficient := 1, powers := [(27, 1), (48, 1)] }, { coefficient := 1, powers := [(45, 1), (54, 1)] }, { coefficient := 1, powers := [(58, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (39, 1), (60, 1)] }, { coefficient := 1, powers := [(1, 1), (42, 1), (57, 1)] }, { coefficient := 1, powers := [(1, 1), (47, 1), (53, 1)] }, { coefficient := 1, powers := [(4, 1), (28, 1), (60, 1)] }, { coefficient := 1, powers := [(4, 1), (33, 1), (57, 1)] }, { coefficient := 1, powers := [(4, 1), (36, 1), (53, 1)] }, { coefficient := 1, powers := [(7, 1), (23, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (33, 1), (47, 1)] }, { coefficient := 1, powers := [(7, 1), (36, 1), (42, 1)] }, { coefficient := 1, powers := [(11, 1), (23, 1), (57, 1)] }, { coefficient := 1, powers := [(11, 1), (28, 1), (47, 1)] }, { coefficient := 1, powers := [(11, 1), (36, 1), (39, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1), (53, 1)] }, { coefficient := 1, powers := [(16, 1), (28, 1), (42, 1)] }, { coefficient := 1, powers := [(16, 1), (33, 1), (39, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (40, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (43, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (50, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (37, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (25, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (50, 1)] }, { coefficient := 1, powers := [(8, 1), (37, 1), (43, 1)] }, { coefficient := 1, powers := [(13, 1), (25, 1), (58, 1)] }, { coefficient := 1, powers := [(13, 1), (31, 1), (50, 1)] }, { coefficient := 1, powers := [(13, 1), (37, 1), (40, 1)] }, { coefficient := 1, powers := [(20, 1), (25, 1), (55, 1)] }, { coefficient := 1, powers := [(20, 1), (31, 1), (43, 1)] }, { coefficient := 1, powers := [(20, 1), (34, 1), (40, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1)] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(42, 1)] }],
  [{ coefficient := 1, powers := [(43, 1), (64, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 34 → SparsePoly (Fin 65) := ![
  [{ coefficient := -1, powers := [(8, 1), (25, 1), (60, 1)] }],
  [{ coefficient := 2, powers := [(4, 1), (37, 1), (43, 1), (57, 1)] }, { coefficient := -2, powers := [(11, 1), (37, 1), (39, 1), (43, 1)] }],
  [{ coefficient := 2, powers := [(8, 1), (33, 1), (37, 1), (39, 1), (43, 1), (64, 1)] }],
  [{ coefficient := -2, powers := [(6, 1), (11, 1), (19, 1), (37, 1), (43, 1), (53, 1)] }, { coefficient := -2, powers := [(7, 1), (19, 1), (37, 1), (43, 1)] }],
  [{ coefficient := -2, powers := [(5, 1), (27, 1), (34, 1), (48, 1), (57, 1), (64, 1)] }, { coefficient := 2, powers := [(5, 1), (34, 1), (48, 1), (54, 1), (64, 1)] }, { coefficient := 2, powers := [(8, 1), (34, 1), (50, 1), (57, 1), (64, 1)] }, { coefficient := 2, powers := [(13, 1), (31, 1), (47, 1), (50, 1), (64, 1)] }],
  [{ coefficient := 2, powers := [(4, 1), (8, 1), (37, 1), (43, 1), (60, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (8, 1), (49, 1), (61, 1), (64, 1)] }, { coefficient := 1, powers := [(8, 1), (21, 1), (49, 1), (61, 1), (64, 1)] }],
  [{ coefficient := -2, powers := [(5, 1), (27, 1), (34, 1), (57, 1), (64, 1)] }, { coefficient := 2, powers := [(8, 1), (22, 1), (34, 1), (57, 1), (64, 1)] }, { coefficient := 2, powers := [(13, 1), (22, 1), (31, 1), (47, 1), (64, 1)] }, { coefficient := -2, powers := [(13, 1), (25, 1), (54, 1), (64, 1)] }, { coefficient := -2, powers := [(19, 1), (31, 1), (43, 1), (64, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (31, 1), (50, 1)] }],
  [{ coefficient := 2, powers := [(25, 1), (48, 1), (55, 1)] }, { coefficient := 2, powers := [(31, 1), (43, 1), (48, 1)] }],
  [{ coefficient := 2, powers := [(25, 1), (55, 1)] }, { coefficient := 2, powers := [(31, 1), (43, 1)] }],
  [{ coefficient := -2, powers := [(19, 1), (55, 1)] }],
  [{ coefficient := -2, powers := [(5, 1), (27, 1), (34, 1), (48, 1), (64, 1)] }, { coefficient := 2, powers := [(5, 1), (31, 1), (61, 1), (64, 1)] }, { coefficient := 1, powers := [(8, 1), (25, 1), (61, 1), (64, 1)] }, { coefficient := 2, powers := [(8, 1), (34, 1), (50, 1), (64, 1)] }, { coefficient := 2, powers := [(20, 1), (31, 1)] }],
  [{ coefficient := -2, powers := [(8, 1), (34, 1), (57, 1)] }, { coefficient := -2, powers := [(13, 1), (31, 1), (47, 1)] }],
  [{ coefficient := 2, powers := [(8, 1), (37, 1), (43, 1), (53, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (31, 1), (57, 1)] }],
  [{ coefficient := -2, powers := [(21, 1), (25, 1), (55, 1)] }, { coefficient := -2, powers := [(21, 1), (31, 1), (43, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (8, 1), (61, 1)] }, { coefficient := -1, powers := [(8, 1), (21, 1), (61, 1)] }],
  [{ coefficient := 2, powers := [(20, 1)] }],
  [{ coefficient := -2, powers := [(25, 1), (55, 1)] }, { coefficient := -2, powers := [(31, 1), (43, 1)] }],
  [{ coefficient := 2, powers := [(5, 1), (27, 1), (34, 1), (57, 1)] }, { coefficient := -2, powers := [(5, 1), (34, 1), (54, 1)] }],
  [{ coefficient := 2, powers := [(55, 1)] }],
  [{ coefficient := -2, powers := [(8, 1), (11, 1), (37, 1), (43, 1), (53, 1)] }],
  [{ coefficient := 2, powers := [(6, 1), (11, 1), (37, 1), (43, 1), (53, 1)] }, { coefficient := 2, powers := [(7, 1), (37, 1), (43, 1)] }],
  [{ coefficient := 2, powers := [(13, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (25, 1), (61, 1)] }],
  [{ coefficient := 2, powers := [(8, 1), (11, 1), (37, 1), (43, 1)] }],
  [{ coefficient := 2, powers := [(5, 1), (34, 1)] }],
  [{ coefficient := -2, powers := [(8, 1), (37, 1), (43, 1)] }],
  [{ coefficient := -2, powers := [] }],
  [{ coefficient := 2, powers := [(8, 1), (37, 1), (39, 1), (43, 1), (60, 1)] }, { coefficient := 2, powers := [(8, 1), (37, 1), (42, 1), (43, 1), (57, 1)] }],
  [{ coefficient := 2, powers := [(40, 1), (61, 1)] }, { coefficient := 2, powers := [(43, 1), (58, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (5, 1), (34, 1), (58, 1)] }, { coefficient := -2, powers := [(5, 1), (26, 1), (27, 1), (34, 1), (45, 1), (57, 1)] }, { coefficient := 2, powers := [(5, 1), (26, 1), (34, 1), (45, 1), (54, 1)] }, { coefficient := -2, powers := [(5, 1), (27, 1), (34, 1), (45, 1)] }, { coefficient := -2, powers := [(8, 1), (11, 1), (28, 1), (37, 1), (43, 1)] }, { coefficient := 2, powers := [(8, 1), (16, 1), (28, 1), (37, 1), (43, 1)] }, { coefficient := 2, powers := [(20, 1), (21, 1), (25, 1), (55, 1)] }, { coefficient := 2, powers := [(20, 1), (21, 1), (31, 1), (43, 1)] }, { coefficient := 2, powers := [(20, 1), (25, 1), (26, 1), (55, 1)] }, { coefficient := 2, powers := [(20, 1), (26, 1), (31, 1), (43, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (5, 1), (27, 1), (34, 1), (48, 1), (57, 1)] }, { coefficient := -2, powers := [(0, 1), (5, 1), (31, 1), (57, 1), (61, 1)] }, { coefficient := -1, powers := [(0, 1), (8, 1), (25, 1), (57, 1), (61, 1)] }, { coefficient := -1, powers := [(0, 1), (8, 1), (30, 1), (49, 1), (61, 1)] }, { coefficient := -2, powers := [(0, 1), (8, 1), (34, 1), (50, 1), (57, 1)] }, { coefficient := -2, powers := [(4, 1), (8, 1), (28, 1), (37, 1), (43, 1), (60, 1)] }, { coefficient := 2, powers := [(5, 1), (26, 1), (27, 1), (34, 1), (48, 1), (57, 1)] }, { coefficient := -2, powers := [(5, 1), (26, 1), (34, 1), (48, 1), (54, 1)] }, { coefficient := 2, powers := [(5, 1), (27, 1), (34, 1), (45, 1), (57, 1)] }, { coefficient := 2, powers := [(5, 1), (27, 1), (34, 1), (48, 1)] }, { coefficient := -2, powers := [(5, 1), (31, 1), (61, 1)] }, { coefficient := -2, powers := [(8, 1), (16, 1), (33, 1), (37, 1), (39, 1), (43, 1)] }, { coefficient := -1, powers := [(8, 1), (21, 1), (30, 1), (49, 1), (61, 1)] }, { coefficient := -2, powers := [(8, 1), (22, 1), (34, 1), (45, 1), (57, 1)] }, { coefficient := -1, powers := [(8, 1), (25, 1), (61, 1)] }, { coefficient := -2, powers := [(8, 1), (26, 1), (34, 1), (50, 1), (57, 1)] }, { coefficient := -2, powers := [(8, 1), (34, 1), (50, 1)] }, { coefficient := -2, powers := [(13, 1), (22, 1), (31, 1), (45, 1), (47, 1)] }, { coefficient := 2, powers := [(13, 1), (25, 1), (45, 1), (54, 1)] }, { coefficient := -2, powers := [(13, 1), (26, 1), (31, 1), (47, 1), (50, 1)] }, { coefficient := 2, powers := [(19, 1), (31, 1), (43, 1), (45, 1)] }]
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
    (values : Fin 65 → R) :
    ¬ ∀ index : Fin 34,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((2 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (2 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (2 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component16.SelectedLeafB4_5.selectedHasNoCommonZero

end Krenn.Component16.SelectedLeafB4_5
