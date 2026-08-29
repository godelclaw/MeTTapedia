import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component13.SelectedLeafB3

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "80548a09b70d89a5ee8546c8a862a15b8a781a5977daac9fbb5c4c4c4be37bae"
def certificateSHA256 : String := "091b1556f31e8640d8cd2f5f69c9b07ccba9f32489723a17fbe0816f98d26d92"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 30 → Fin 608 := ![
  13,
  156,
  161,
  162,
  173,
  175,
  182,
  183,
  184,
  187,
  196,
  197,
  199,
  201,
  202,
  360,
  361,
  371,
  373,
  460,
  482,
  488,
  489,
  498,
  499,
  525,
  604,
  605,
  606,
  607
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 30 → SparsePoly (Fin 60) := ![
  [{ coefficient := 1, powers := [(15, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (47, 1)] }, { coefficient := 1, powers := [(15, 1), (19, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (57, 1)] }, { coefficient := 1, powers := [(41, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (56, 1)] }, { coefficient := 1, powers := [(16, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (18, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (54, 1)] }, { coefficient := 1, powers := [(17, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (49, 1)] }, { coefficient := 1, powers := [(21, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (51, 1)] }, { coefficient := 1, powers := [(27, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (41, 1)] }, { coefficient := 1, powers := [(26, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(26, 1), (38, 1)] }, { coefficient := 1, powers := [(26, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1), (50, 1)] }, { coefficient := 1, powers := [(50, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1), (51, 1)] }, { coefficient := 1, powers := [(51, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1), (49, 1)] }, { coefficient := 1, powers := [(44, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1), (49, 1)] }, { coefficient := 1, powers := [(45, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (34, 1), (57, 1)] }, { coefficient := 1, powers := [(1, 1), (41, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1), (45, 1)] }, { coefficient := 1, powers := [(17, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1), (54, 1)] }, { coefficient := 1, powers := [(17, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (38, 1), (54, 1)] }, { coefficient := 1, powers := [(41, 1), (50, 1)] }, { coefficient := 1, powers := [(54, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (39, 1), (53, 1)] }, { coefficient := 1, powers := [(39, 1)] }, { coefficient := 1, powers := [(44, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (18, 1), (49, 1)] }, { coefficient := 1, powers := [(16, 1), (18, 1), (53, 1)] }, { coefficient := 1, powers := [(16, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (50, 1)] }, { coefficient := 1, powers := [(8, 1), (21, 1), (56, 1)] }, { coefficient := 1, powers := [(16, 1), (21, 1), (50, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (38, 1)] }, { coefficient := 1, powers := [(16, 1), (43, 1)] }, { coefficient := 1, powers := [(16, 1), (49, 1)] }, { coefficient := 1, powers := [(16, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (51, 1)] }, { coefficient := 1, powers := [(27, 1), (39, 1)] }, { coefficient := 1, powers := [(27, 1), (44, 1), (47, 1)] }, { coefficient := 1, powers := [(30, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (34, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1)] }, { coefficient := 1, powers := [(16, 1), (21, 1)] }, { coefficient := 1, powers := [(16, 1), (26, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (41, 1), (50, 1)] }, { coefficient := 1, powers := [(16, 1), (21, 1), (54, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1), (41, 1)] }, { coefficient := 1, powers := [(17, 1), (21, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (41, 1), (50, 1)] }, { coefficient := 1, powers := [(22, 1), (54, 1)] }, { coefficient := 1, powers := [(27, 1), (45, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (36, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (39, 1), (54, 1)] }, { coefficient := 1, powers := [(2, 1), (45, 1), (51, 1)] }, { coefficient := 1, powers := [(5, 1), (27, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (51, 1)] }, { coefficient := 1, powers := [(8, 1), (22, 1), (57, 1)] }, { coefficient := 1, powers := [(8, 1), (30, 1), (45, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (39, 1)] }, { coefficient := 1, powers := [(12, 1), (22, 1), (54, 1)] }, { coefficient := 1, powers := [(12, 1), (27, 1), (45, 1)] }, { coefficient := 1, powers := [(12, 1), (33, 1), (36, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (51, 1)] }, { coefficient := 1, powers := [(17, 1), (27, 1), (39, 1)] }, { coefficient := 1, powers := [(17, 1), (30, 1), (36, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (58, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (59, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 30 → SparsePoly (Fin 60) := ![
  [{ coefficient := -1, powers := [(2, 1), (19, 1), (36, 1), (41, 1), (56, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (36, 1), (41, 1), (56, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (2, 1), (36, 1), (56, 1), (58, 1)] }, { coefficient := -1, powers := [(2, 1), (36, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [(21, 1), (39, 1), (41, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (26, 1), (36, 1), (38, 1), (57, 1), (59, 1)] }, { coefficient := -1, powers := [(2, 1), (26, 1), (36, 1), (43, 1), (57, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (16, 1), (18, 1), (36, 1), (57, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(17, 1), (44, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (16, 1), (23, 1), (36, 1), (57, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (39, 1), (41, 1)] }, { coefficient := -1, powers := [(5, 1), (30, 1), (41, 1)] }, { coefficient := 1, powers := [(12, 1), (22, 1), (41, 1)] }, { coefficient := 1, powers := [(12, 1), (26, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (45, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1)] }, { coefficient := 1, powers := [(17, 1), (21, 1), (44, 1)] }, { coefficient := -1, powers := [(17, 1), (22, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (33, 1), (47, 1)] }, { coefficient := 1, powers := [(17, 1), (27, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (30, 1)] }, { coefficient := -1, powers := [(12, 1), (27, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (36, 1), (56, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(27, 1)] }],
  [{ coefficient := 1, powers := [(22, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (39, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1)] }, { coefficient := -1, powers := [(12, 1), (22, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (33, 1)] }, { coefficient := -1, powers := [(17, 1), (27, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (21, 1), (36, 1), (57, 1), (59, 1)] }, { coefficient := -1, powers := [(2, 1), (26, 1), (36, 1), (57, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(39, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (18, 1), (26, 1), (36, 1), (57, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(17, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (36, 1), (57, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(39, 1)] }],
  [{ coefficient := 1, powers := [(12, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(2, 1), (38, 1), (39, 1), (54, 1)] }, { coefficient := 1, powers := [(2, 1), (39, 1), (41, 1), (43, 1), (50, 1)] }, { coefficient := -1, powers := [(2, 1), (43, 1), (45, 1), (51, 1)] }, { coefficient := -1, powers := [(5, 1), (30, 1), (38, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (41, 1), (43, 1), (50, 1)] }, { coefficient := -1, powers := [(5, 1), (33, 1), (43, 1), (51, 1)] }, { coefficient := -1, powers := [(8, 1), (30, 1), (45, 1), (49, 1)] }, { coefficient := -1, powers := [(8, 1), (33, 1), (39, 1), (53, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (44, 1), (47, 1), (49, 1)] }, { coefficient := 1, powers := [(12, 1), (22, 1), (38, 1), (54, 1)] }, { coefficient := -1, powers := [(12, 1), (22, 1), (41, 1), (43, 1), (50, 1)] }, { coefficient := -1, powers := [(12, 1), (26, 1), (43, 1), (45, 1), (50, 1)] }, { coefficient := 1, powers := [(12, 1), (27, 1), (45, 1), (49, 1)] }, { coefficient := -1, powers := [(17, 1), (21, 1), (43, 1), (44, 1), (51, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (43, 1), (51, 1)] }, { coefficient := 1, powers := [(17, 1), (27, 1), (39, 1), (53, 1)] }, { coefficient := -1, powers := [(17, 1), (27, 1), (44, 1), (47, 1), (49, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (6, 1), (36, 1), (56, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (34, 1), (36, 1), (56, 1), (57, 1)] }, { coefficient := -1, powers := [(2, 1), (36, 1), (41, 1), (47, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (34, 1), (36, 1), (56, 1), (57, 1)] }, { coefficient := -1, powers := [(2, 1), (36, 1), (57, 1)] }]
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
    (values : Fin 60 → R) :
    ¬ ∀ index : Fin 30,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component13.SelectedLeafB3.selectedHasNoCommonZero

end Krenn.Component13.SelectedLeafB3
