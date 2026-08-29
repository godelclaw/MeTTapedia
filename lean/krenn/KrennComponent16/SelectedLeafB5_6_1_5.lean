import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component16.SelectedLeafB5_6_1_5

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "c7757a932901115e8cc56bb20a5e27c1420cc9dbb25467d2160b55e6a7547ad6"
def certificateSHA256 : String := "3213c27048d29f77f51b0939b6ec2e4e11dcec88ff534fc83414990be153a9a2"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 36 → Fin 674 := ![
  7,
  9,
  13,
  16,
  22,
  23,
  31,
  32,
  142,
  150,
  175,
  300,
  301,
  302,
  316,
  317,
  321,
  323,
  366,
  440,
  448,
  471,
  584,
  588,
  591,
  609,
  660,
  661,
  662,
  663,
  665,
  667,
  669,
  671,
  672,
  673
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 36 → SparsePoly (Fin 69) := ![
  [{ coefficient := 1, powers := [(7, 1), (34, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (26, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(30, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(34, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (55, 1)] }, { coefficient := 1, powers := [(21, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (26, 1)] }, { coefficient := 1, powers := [(16, 1), (21, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1), (55, 1)] }, { coefficient := 1, powers := [(55, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (47, 1)] }, { coefficient := 1, powers := [(4, 1), (36, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (53, 1)] }, { coefficient := 1, powers := [(7, 1), (33, 1)] }, { coefficient := 1, powers := [(11, 1), (28, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (61, 1)] }, { coefficient := 1, powers := [(13, 1), (50, 1)] }, { coefficient := 1, powers := [(20, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (55, 1)] }, { coefficient := 1, powers := [(31, 1), (43, 1)] }, { coefficient := 1, powers := [(34, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(30, 1), (54, 1)] }, { coefficient := 1, powers := [(31, 1), (42, 1)] }, { coefficient := 1, powers := [(31, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1), (53, 1)] }, { coefficient := 1, powers := [(21, 1), (45, 1), (53, 1)] }, { coefficient := 1, powers := [(45, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (49, 1), (55, 1)] }, { coefficient := 1, powers := [(22, 1), (55, 1)] }, { coefficient := 1, powers := [(27, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (25, 1), (60, 1)] }, { coefficient := 1, powers := [(25, 1)] }, { coefficient := 1, powers := [(29, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1)] }, { coefficient := 1, powers := [(13, 1), (31, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (61, 1)] }, { coefficient := 1, powers := [(13, 1), (27, 1), (48, 1)] }, { coefficient := 1, powers := [(13, 1), (58, 1)] }, { coefficient := 1, powers := [(20, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (49, 1), (53, 1)] }, { coefficient := 1, powers := [(22, 1), (53, 1)] }, { coefficient := 1, powers := [(22, 1), (57, 1)] }, { coefficient := 1, powers := [(49, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1)] }, { coefficient := 1, powers := [(6, 1), (60, 1)] }, { coefficient := 1, powers := [(26, 1), (42, 1)] }, { coefficient := 1, powers := [(26, 1), (47, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (40, 1), (61, 1)] }, { coefficient := 1, powers := [(0, 1), (43, 1), (58, 1)] }, { coefficient := 1, powers := [(0, 1), (50, 1), (55, 1)] }, { coefficient := 1, powers := [(22, 1), (45, 1), (55, 1)] }, { coefficient := 1, powers := [(27, 1), (43, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (41, 1), (57, 1)] }, { coefficient := 1, powers := [(1, 1), (52, 1)] }, { coefficient := 1, powers := [(7, 1), (36, 1), (41, 1)] }, { coefficient := 1, powers := [(10, 1), (28, 1)] }, { coefficient := 1, powers := [(16, 1), (28, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (53, 1)] }, { coefficient := 1, powers := [(23, 1), (57, 1)] }, { coefficient := 1, powers := [(28, 1), (42, 1)] }, { coefficient := 1, powers := [(28, 1), (47, 1)] }, { coefficient := 1, powers := [(33, 1), (39, 1)] }, { coefficient := 1, powers := [(36, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (39, 1), (60, 1)] }, { coefficient := 1, powers := [(1, 1), (42, 1), (57, 1)] }, { coefficient := 1, powers := [(1, 1), (47, 1), (53, 1)] }, { coefficient := 1, powers := [(4, 1), (28, 1), (60, 1)] }, { coefficient := 1, powers := [(4, 1), (33, 1), (57, 1)] }, { coefficient := 1, powers := [(4, 1), (36, 1), (53, 1)] }, { coefficient := 1, powers := [(7, 1), (23, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (33, 1), (47, 1)] }, { coefficient := 1, powers := [(7, 1), (36, 1), (42, 1)] }, { coefficient := 1, powers := [(11, 1), (23, 1), (57, 1)] }, { coefficient := 1, powers := [(11, 1), (28, 1), (47, 1)] }, { coefficient := 1, powers := [(11, 1), (36, 1), (39, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1), (53, 1)] }, { coefficient := 1, powers := [(16, 1), (28, 1), (42, 1)] }, { coefficient := 1, powers := [(16, 1), (33, 1), (39, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (40, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (43, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (50, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (37, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (25, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (50, 1)] }, { coefficient := 1, powers := [(8, 1), (37, 1), (43, 1)] }, { coefficient := 1, powers := [(13, 1), (25, 1), (58, 1)] }, { coefficient := 1, powers := [(13, 1), (31, 1), (50, 1)] }, { coefficient := 1, powers := [(13, 1), (37, 1), (40, 1)] }, { coefficient := 1, powers := [(20, 1), (25, 1), (55, 1)] }, { coefficient := 1, powers := [(20, 1), (31, 1), (43, 1)] }, { coefficient := 1, powers := [(20, 1), (34, 1), (40, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1)] }],
  [{ coefficient := 1, powers := [(41, 1), (64, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(43, 1)] }],
  [{ coefficient := 1, powers := [(57, 1)] }],
  [{ coefficient := 1, powers := [(26, 1), (67, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(28, 1)] }],
  [{ coefficient := 1, powers := [(31, 1), (68, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 36 → SparsePoly (Fin 69) := ![
  [{ coefficient := 1, powers := [(5, 1), (23, 1), (58, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1), (42, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(31, 1), (50, 1), (67, 1)] }, { coefficient := 1, powers := [(37, 1), (40, 1), (67, 1)] }],
  [{ coefficient := -1, powers := [(25, 1), (27, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (21, 1), (33, 1), (39, 1), (50, 1), (67, 1)] }, { coefficient := -1, powers := [(2, 1), (33, 1), (39, 1), (50, 1)] }, { coefficient := 1, powers := [(5, 1), (21, 1), (33, 1), (37, 1), (39, 1), (67, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (37, 1), (39, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (7, 1), (50, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (11, 1), (50, 1), (53, 1)] }, { coefficient := 1, powers := [(5, 1), (7, 1), (37, 1), (60, 1)] }, { coefficient := -1, powers := [(5, 1), (11, 1), (37, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(19, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (25, 1), (26, 1), (54, 1), (68, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (11, 1), (36, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (16, 1), (33, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (22, 1), (45, 1), (53, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (33, 1), (39, 1), (50, 1), (55, 1), (67, 1)] }, { coefficient := -1, powers := [(5, 1), (33, 1), (37, 1), (39, 1), (55, 1), (67, 1)] }],
  [{ coefficient := -1, powers := [(20, 1), (25, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (50, 1), (53, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (53, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (37, 1), (53, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (47, 1), (50, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (47, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (37, 1), (47, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(31, 1)] }],
  [{ coefficient := 1, powers := [(20, 1)] }],
  [{ coefficient := -1, powers := [(20, 1), (25, 1), (26, 1), (55, 1), (68, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (22, 1), (55, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(20, 1), (29, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(20, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(50, 1)] }],
  [{ coefficient := 1, powers := [(25, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (29, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (25, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (42, 1), (50, 1), (55, 1), (64, 1)] }, { coefficient := 1, powers := [(5, 1), (37, 1), (42, 1), (55, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (11, 1), (50, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (11, 1), (37, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (50, 1), (55, 1)] }, { coefficient := -1, powers := [(5, 1), (34, 1), (58, 1)] }, { coefficient := -1, powers := [(5, 1), (37, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(2, 1), (40, 1), (61, 1)] }, { coefficient := -1, powers := [(2, 1), (50, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (39, 1), (50, 1), (55, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (41, 1), (42, 1), (50, 1), (55, 1), (57, 1), (64, 1)] }, { coefficient := 1, powers := [(2, 1), (42, 1), (50, 1), (52, 1), (55, 1), (64, 1)] }, { coefficient := -1, powers := [(2, 1), (42, 1), (50, 1), (55, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (47, 1), (50, 1), (53, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (39, 1), (58, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (42, 1), (57, 1), (58, 1)] }, { coefficient := -1, powers := [(5, 1), (34, 1), (47, 1), (53, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (37, 1), (39, 1), (55, 1), (60, 1)] }, { coefficient := -1, powers := [(5, 1), (37, 1), (41, 1), (42, 1), (55, 1), (57, 1), (64, 1)] }, { coefficient := -1, powers := [(5, 1), (37, 1), (42, 1), (52, 1), (55, 1), (64, 1)] }, { coefficient := 1, powers := [(5, 1), (37, 1), (42, 1), (55, 1), (57, 1)] }, { coefficient := -1, powers := [(5, 1), (37, 1), (47, 1), (53, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (7, 1), (36, 1), (42, 1), (50, 1), (55, 1)] }, { coefficient := -1, powers := [(5, 1), (7, 1), (36, 1), (37, 1), (42, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (2, 1), (58, 1), (62, 1)] }, { coefficient := -1, powers := [(2, 1), (27, 1), (45, 1), (62, 1)] }, { coefficient := 1, powers := [(2, 1), (58, 1)] }, { coefficient := 1, powers := [(8, 1), (37, 1)] }, { coefficient := 1, powers := [(20, 1), (27, 1), (29, 1), (53, 1)] }, { coefficient := -1, powers := [(20, 1), (31, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (4, 1), (33, 1), (50, 1), (55, 1)] }, { coefficient := 1, powers := [(4, 1), (5, 1), (33, 1), (34, 1), (58, 1)] }, { coefficient := 1, powers := [(4, 1), (5, 1), (33, 1), (37, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (11, 1), (23, 1), (34, 1), (58, 1)] }, { coefficient := -1, powers := [(20, 1), (22, 1), (29, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (11, 1), (33, 1), (39, 1), (50, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (11, 1), (33, 1), (37, 1), (39, 1), (55, 1)] }, { coefficient := 1, powers := [(13, 1), (31, 1), (50, 1)] }, { coefficient := -1, powers := [(13, 1), (37, 1), (40, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (4, 1), (50, 1), (55, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (10, 1), (42, 1), (50, 1), (55, 1), (64, 1)] }, { coefficient := 1, powers := [(2, 1), (11, 1), (42, 1), (50, 1), (55, 1)] }, { coefficient := 1, powers := [(2, 1), (11, 1), (47, 1), (50, 1), (55, 1)] }, { coefficient := 1, powers := [(2, 1), (16, 1), (41, 1), (42, 1), (50, 1), (55, 1), (64, 1)] }, { coefficient := -1, powers := [(2, 1), (16, 1), (42, 1), (50, 1), (55, 1)] }, { coefficient := 1, powers := [(4, 1), (5, 1), (34, 1), (58, 1), (60, 1)] }, { coefficient := 1, powers := [(4, 1), (5, 1), (37, 1), (55, 1), (60, 1)] }, { coefficient := -1, powers := [(5, 1), (10, 1), (37, 1), (42, 1), (55, 1), (64, 1)] }, { coefficient := -1, powers := [(5, 1), (11, 1), (37, 1), (42, 1), (55, 1)] }, { coefficient := -1, powers := [(5, 1), (11, 1), (37, 1), (47, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (16, 1), (34, 1), (42, 1), (58, 1)] }, { coefficient := -1, powers := [(5, 1), (16, 1), (37, 1), (41, 1), (42, 1), (55, 1), (64, 1)] }, { coefficient := 1, powers := [(5, 1), (16, 1), (37, 1), (42, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (25, 1), (26, 1), (42, 1), (55, 1)] }, { coefficient := 1, powers := [(20, 1), (25, 1), (26, 1), (47, 1), (55, 1)] }]
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
    ¬ ∀ index : Fin 36,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component16.SelectedLeafB5_6_1_5.selectedHasNoCommonZero

end Krenn.Component16.SelectedLeafB5_6_1_5
