import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component16.SelectedLeafB0_2_3

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "a01b8eb64932260a59f668d3f0e52337020089d520480ebdd87c3a5f65d8c3c1"
def certificateSHA256 : String := "840d7b77c4f6ab68b22019314b58d0d3c1f9717c6f899d7fc3cfd8dead664406"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 34 → Fin 671 := ![
  5,
  6,
  9,
  12,
  18,
  21,
  23,
  49,
  175,
  273,
  300,
  301,
  302,
  316,
  440,
  445,
  448,
  454,
  471,
  497,
  518,
  571,
  584,
  608,
  609,
  612,
  649,
  660,
  661,
  662,
  663,
  664,
  667,
  670
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 34 → SparsePoly (Fin 65) := ![
  [{ coefficient := 1, powers := [(5, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (26, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (28, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (33, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1), (55, 1)] }, { coefficient := 1, powers := [(55, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (45, 1), (54, 1)] }, { coefficient := 1, powers := [(23, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (47, 1)] }, { coefficient := 1, powers := [(4, 1), (36, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (53, 1)] }, { coefficient := 1, powers := [(7, 1), (33, 1)] }, { coefficient := 1, powers := [(11, 1), (28, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (61, 1)] }, { coefficient := 1, powers := [(13, 1), (50, 1)] }, { coefficient := 1, powers := [(20, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (55, 1)] }, { coefficient := 1, powers := [(31, 1), (43, 1)] }, { coefficient := 1, powers := [(34, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1)] }, { coefficient := 1, powers := [(13, 1), (31, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (60, 1)] }, { coefficient := 1, powers := [(19, 1), (22, 1), (53, 1)] }, { coefficient := 1, powers := [(19, 1), (22, 1), (57, 1)] }, { coefficient := 1, powers := [(19, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (61, 1)] }, { coefficient := 1, powers := [(13, 1), (27, 1), (48, 1)] }, { coefficient := 1, powers := [(13, 1), (58, 1)] }, { coefficient := 1, powers := [(20, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (42, 1)] }, { coefficient := 1, powers := [(19, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (53, 1)] }, { coefficient := 1, powers := [(19, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (49, 1), (53, 1)] }, { coefficient := 1, powers := [(22, 1), (53, 1)] }, { coefficient := 1, powers := [(22, 1), (57, 1)] }, { coefficient := 1, powers := [(49, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (28, 1), (60, 1)] }, { coefficient := 1, powers := [(3, 1), (33, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (36, 1), (53, 1)] }, { coefficient := 1, powers := [(28, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (28, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1), (53, 1)] }, { coefficient := 1, powers := [(19, 1), (28, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (45, 1), (54, 1)] }, { coefficient := 1, powers := [(25, 1), (58, 1)] }, { coefficient := 1, powers := [(31, 1), (50, 1)] }, { coefficient := 1, powers := [(37, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1)] }, { coefficient := 1, powers := [(6, 1), (60, 1)] }, { coefficient := 1, powers := [(26, 1), (42, 1)] }, { coefficient := 1, powers := [(26, 1), (47, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(4, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (60, 1)] }, { coefficient := 1, powers := [(11, 1), (47, 1)] }, { coefficient := 1, powers := [(11, 1), (57, 1)] }, { coefficient := 1, powers := [(16, 1), (42, 1)] }, { coefficient := 1, powers := [(16, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (53, 1)] }, { coefficient := 1, powers := [(23, 1), (57, 1)] }, { coefficient := 1, powers := [(28, 1), (42, 1)] }, { coefficient := 1, powers := [(28, 1), (47, 1)] }, { coefficient := 1, powers := [(33, 1), (39, 1)] }, { coefficient := 1, powers := [(36, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1), (58, 1)] }, { coefficient := 1, powers := [(0, 1), (48, 1), (54, 1)] }, { coefficient := 1, powers := [(27, 1), (42, 1), (45, 1)] }, { coefficient := 1, powers := [(27, 1), (48, 1)] }, { coefficient := 1, powers := [(45, 1), (54, 1)] }, { coefficient := 1, powers := [(58, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (39, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (42, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (47, 1), (53, 1)] }, { coefficient := 1, powers := [(42, 1)] }, { coefficient := 1, powers := [(47, 1)] }, { coefficient := 1, powers := [(53, 1)] }, { coefficient := 1, powers := [(57, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (39, 1), (60, 1)] }, { coefficient := 1, powers := [(1, 1), (42, 1), (57, 1)] }, { coefficient := 1, powers := [(1, 1), (47, 1), (53, 1)] }, { coefficient := 1, powers := [(4, 1), (28, 1), (60, 1)] }, { coefficient := 1, powers := [(4, 1), (33, 1), (57, 1)] }, { coefficient := 1, powers := [(4, 1), (36, 1), (53, 1)] }, { coefficient := 1, powers := [(7, 1), (23, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (33, 1), (47, 1)] }, { coefficient := 1, powers := [(7, 1), (36, 1), (42, 1)] }, { coefficient := 1, powers := [(11, 1), (23, 1), (57, 1)] }, { coefficient := 1, powers := [(11, 1), (28, 1), (47, 1)] }, { coefficient := 1, powers := [(11, 1), (36, 1), (39, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1), (53, 1)] }, { coefficient := 1, powers := [(16, 1), (28, 1), (42, 1)] }, { coefficient := 1, powers := [(16, 1), (33, 1), (39, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (40, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (43, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (50, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (37, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (25, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (50, 1)] }, { coefficient := 1, powers := [(8, 1), (37, 1), (43, 1)] }, { coefficient := 1, powers := [(13, 1), (25, 1), (58, 1)] }, { coefficient := 1, powers := [(13, 1), (31, 1), (50, 1)] }, { coefficient := 1, powers := [(13, 1), (37, 1), (40, 1)] }, { coefficient := 1, powers := [(20, 1), (25, 1), (55, 1)] }, { coefficient := 1, powers := [(20, 1), (31, 1), (43, 1)] }, { coefficient := 1, powers := [(20, 1), (34, 1), (40, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1)] }],
  [{ coefficient := 1, powers := [(1, 1)] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(43, 1)] }],
  [{ coefficient := 1, powers := [(58, 1), (64, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 34 → SparsePoly (Fin 65) := ![
  [{ coefficient := 1, powers := [(3, 1), (16, 1), (34, 1), (47, 1), (53, 1), (58, 1)] }, { coefficient := -1, powers := [(4, 1), (34, 1), (47, 1), (58, 1)] }, { coefficient := 1, powers := [(7, 1), (34, 1), (42, 1), (58, 1)] }, { coefficient := 1, powers := [(11, 1), (34, 1), (39, 1), (58, 1)] }, { coefficient := -1, powers := [(16, 1), (34, 1), (39, 1), (58, 1)] }],
  [{ coefficient := -2, powers := [(5, 1), (31, 1), (60, 1)] }],
  [{ coefficient := 2, powers := [(31, 1), (42, 1), (50, 1)] }, { coefficient := 2, powers := [(31, 1), (47, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (27, 1), (42, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (34, 1), (49, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (5, 1), (34, 1), (45, 1), (58, 1), (60, 1), (64, 1)] }, { coefficient := 1, powers := [(5, 1), (11, 1), (34, 1), (45, 1), (47, 1), (58, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(19, 1), (50, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (16, 1), (34, 1), (42, 1), (47, 1), (58, 1), (64, 1)] }, { coefficient := -1, powers := [(5, 1), (16, 1), (34, 1), (47, 2), (58, 1), (64, 1)] }, { coefficient := -1, powers := [(5, 1), (16, 1), (34, 1), (47, 1), (53, 1), (58, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (37, 1)] }, { coefficient := -1, powers := [(20, 1), (25, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (5, 1), (34, 1), (58, 1), (60, 1), (64, 1)] }, { coefficient := -1, powers := [(5, 1), (11, 1), (34, 1), (47, 1), (58, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (34, 1), (47, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (34, 1), (47, 1), (58, 1)] }],
  [{ coefficient := 2, powers := [(6, 1), (31, 1), (60, 1)] }, { coefficient := 1, powers := [(31, 1)] }],
  [{ coefficient := 1, powers := [(20, 1)] }],
  [{ coefficient := 1, powers := [(50, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (16, 1), (28, 1), (34, 1), (47, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(25, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (16, 1), (22, 1), (28, 1), (34, 1), (47, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (16, 1), (19, 1), (28, 1), (34, 1), (47, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (16, 1), (34, 1), (47, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (34, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(13, 1)] }],
  [{ coefficient := -2, powers := [(13, 1), (31, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (23, 1), (34, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (16, 1), (34, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(13, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (5, 1), (16, 1), (33, 1), (34, 1), (47, 1), (58, 1)] }, { coefficient := 1, powers := [(3, 1), (16, 1), (19, 1), (22, 1), (28, 1), (34, 1), (47, 1), (58, 1)] }, { coefficient := -1, powers := [(5, 1), (16, 1), (23, 1), (34, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (34, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(3, 1), (5, 1), (16, 1), (33, 1), (34, 1), (39, 1), (47, 1), (58, 1), (60, 1)] }, { coefficient := -1, powers := [(3, 1), (5, 1), (16, 1), (33, 1), (34, 1), (42, 1), (47, 1), (57, 1), (58, 1)] }, { coefficient := -1, powers := [(3, 1), (5, 1), (16, 1), (33, 1), (34, 1), (47, 2), (53, 1), (58, 1)] }, { coefficient := -1, powers := [(3, 1), (16, 1), (19, 1), (22, 1), (28, 1), (34, 1), (39, 1), (47, 1), (58, 1), (60, 1)] }, { coefficient := -1, powers := [(3, 1), (16, 1), (19, 1), (22, 1), (28, 1), (34, 1), (42, 1), (47, 1), (57, 1), (58, 1)] }, { coefficient := -1, powers := [(3, 1), (16, 1), (19, 1), (22, 1), (28, 1), (34, 1), (47, 2), (53, 1), (58, 1)] }, { coefficient := 1, powers := [(3, 1), (16, 1), (19, 1), (28, 1), (34, 1), (47, 1), (49, 1), (53, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (16, 1), (23, 1), (34, 1), (39, 1), (58, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (16, 1), (23, 1), (34, 1), (42, 1), (57, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (16, 1), (23, 1), (34, 1), (47, 1), (53, 1), (58, 1)] }, { coefficient := -1, powers := [(5, 1), (37, 1), (47, 1), (55, 1)] }, { coefficient := 1, powers := [(13, 1), (25, 1), (42, 1), (58, 1)] }, { coefficient := 1, powers := [(13, 1), (25, 1), (48, 1), (54, 1)] }, { coefficient := 2, powers := [(13, 1), (31, 1), (47, 1), (50, 1)] }, { coefficient := 1, powers := [(20, 1), (25, 1), (47, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (34, 1), (39, 1), (58, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (42, 1), (57, 1), (58, 1)] }, { coefficient := -1, powers := [(5, 1), (34, 1), (47, 2), (58, 1)] }],
  [{ coefficient := 1, powers := [(40, 1), (61, 1)] }, { coefficient := 1, powers := [(43, 1), (58, 1)] }],
  [{ coefficient := -2, powers := [(6, 1), (20, 1), (31, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (37, 1)] }, { coefficient := -1, powers := [(20, 1), (31, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (5, 1), (16, 1), (33, 1), (34, 1), (42, 1), (47, 1), (58, 1)] }, { coefficient := 1, powers := [(3, 1), (5, 1), (16, 1), (33, 1), (34, 1), (47, 2), (58, 1)] }, { coefficient := 1, powers := [(3, 1), (5, 1), (16, 1), (33, 1), (34, 1), (47, 1), (53, 1), (58, 1)] }, { coefficient := 1, powers := [(4, 1), (5, 1), (23, 1), (34, 1), (58, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (11, 1), (23, 1), (34, 1), (47, 1), (58, 1)] }]
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
    (values : Fin 65 → R) :
    ¬ ∀ index : Fin 34,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component16.SelectedLeafB0_2_3.selectedHasNoCommonZero

end Krenn.Component16.SelectedLeafB0_2_3
