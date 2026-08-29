import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component17.SelectedLeafB6_1

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "bfeab28fb53944fa0c88615929c75086f4f52e45ad53fb1f6fc494abb9d91eec"
def certificateSHA256 : String := "4a8277c63a9263d5f0d731a86cc6dfe29672233ef93f15552d9d0c7baa49952d"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 32 → Fin 608 := ![
  0,
  2,
  4,
  18,
  20,
  32,
  33,
  42,
  311,
  312,
  313,
  325,
  335,
  415,
  423,
  434,
  436,
  441,
  459,
  541,
  553,
  567,
  568,
  572,
  584,
  599,
  601,
  603,
  604,
  605,
  606,
  607
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 32 → SparsePoly (Fin 62) := ![
  [{ coefficient := 1, powers := [(1, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(41, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (58, 1)] }, { coefficient := 1, powers := [(13, 1), (47, 1)] }, { coefficient := 1, powers := [(18, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (56, 1)] }, { coefficient := 1, powers := [(9, 1), (53, 1)] }, { coefficient := 1, powers := [(14, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (27, 1)] }, { coefficient := 1, powers := [(22, 1), (48, 1)] }, { coefficient := 1, powers := [(27, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (52, 1)] }, { coefficient := 1, powers := [(29, 1), (41, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (36, 1), (56, 1)] }, { coefficient := 1, powers := [(1, 1), (39, 1), (53, 1)] }, { coefficient := 1, powers := [(1, 1), (42, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (24, 1), (45, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (40, 1)] }, { coefficient := 1, powers := [(18, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1)] }, { coefficient := 1, powers := [(24, 1), (40, 1), (43, 1)] }, { coefficient := 1, powers := [(24, 1), (45, 1)] }, { coefficient := 1, powers := [(43, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (52, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1)] }, { coefficient := 1, powers := [(13, 1), (29, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (35, 1)] }, { coefficient := 1, powers := [(22, 1), (43, 1)] }, { coefficient := 1, powers := [(27, 1), (43, 1)] }, { coefficient := 1, powers := [(35, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (58, 1)] }, { coefficient := 1, powers := [(13, 1), (25, 1), (45, 1)] }, { coefficient := 1, powers := [(13, 1), (55, 1)] }, { coefficient := 1, powers := [(18, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1), (50, 1)] }, { coefficient := 1, powers := [(40, 1), (43, 1)] }, { coefficient := 1, powers := [(43, 1), (50, 1)] }, { coefficient := 1, powers := [(45, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (43, 1), (51, 1)] }, { coefficient := 1, powers := [(23, 1), (55, 1)] }, { coefficient := 1, powers := [(29, 1), (47, 1)] }, { coefficient := 1, powers := [(35, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (40, 1), (53, 1)] }, { coefficient := 1, powers := [(6, 1), (33, 1), (40, 1)] }, { coefficient := 1, powers := [(14, 1), (24, 1), (40, 1)] }, { coefficient := 1, powers := [(14, 1)] }, { coefficient := 1, powers := [(53, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1)] }, { coefficient := 1, powers := [(3, 1), (33, 1)] }, { coefficient := 1, powers := [(14, 1), (19, 1)] }, { coefficient := 1, powers := [(19, 1), (53, 1)] }, { coefficient := 1, powers := [(24, 1), (42, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (48, 1)] }, { coefficient := 1, powers := [(6, 1), (30, 1)] }, { coefficient := 1, powers := [(9, 1), (24, 1)] }, { coefficient := 1, powers := [(19, 1), (48, 1)] }, { coefficient := 1, powers := [(24, 1), (39, 1)] }, { coefficient := 1, powers := [(30, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (40, 1), (55, 1)] }, { coefficient := 1, powers := [(0, 1), (45, 1), (51, 1)] }, { coefficient := 1, powers := [(25, 1), (40, 1), (43, 1)] }, { coefficient := 1, powers := [(25, 1), (45, 1)] }, { coefficient := 1, powers := [(43, 1), (51, 1)] }, { coefficient := 1, powers := [(55, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (35, 1), (48, 1)] }, { coefficient := 1, powers := [(6, 1), (35, 1), (39, 1)] }, { coefficient := 1, powers := [(9, 1), (27, 1), (43, 1)] }, { coefficient := 1, powers := [(9, 1), (35, 1), (36, 1)] }, { coefficient := 1, powers := [(22, 1), (43, 1), (48, 1)] }, { coefficient := 1, powers := [(27, 1), (39, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (36, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (39, 1), (53, 1)] }, { coefficient := 1, powers := [(0, 1), (42, 1), (48, 1)] }, { coefficient := 1, powers := [(3, 1), (24, 1), (56, 1)] }, { coefficient := 1, powers := [(3, 1), (30, 1), (53, 1)] }, { coefficient := 1, powers := [(3, 1), (33, 1), (48, 1)] }, { coefficient := 1, powers := [(6, 1), (19, 1), (56, 1)] }, { coefficient := 1, powers := [(6, 1), (30, 1), (42, 1)] }, { coefficient := 1, powers := [(6, 1), (33, 1), (39, 1)] }, { coefficient := 1, powers := [(9, 1), (19, 1), (53, 1)] }, { coefficient := 1, powers := [(9, 1), (24, 1), (42, 1)] }, { coefficient := 1, powers := [(9, 1), (33, 1), (36, 1)] }, { coefficient := 1, powers := [(14, 1), (19, 1), (48, 1)] }, { coefficient := 1, powers := [(14, 1), (24, 1), (39, 1)] }, { coefficient := 1, powers := [(14, 1), (30, 1), (36, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (41, 1), (55, 1)] }, { coefficient := 1, powers := [(2, 1), (47, 1), (52, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (52, 1)] }, { coefficient := 1, powers := [(8, 1), (23, 1), (58, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (47, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(13, 1), (23, 1), (55, 1)] }, { coefficient := 1, powers := [(13, 1), (29, 1), (47, 1)] }, { coefficient := 1, powers := [(13, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (52, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (41, 1)] }, { coefficient := 1, powers := [(18, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1), (60, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(39, 1)] }],
  [{ coefficient := 1, powers := [(40, 1)] }],
  [{ coefficient := 1, powers := [(41, 1), (61, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 32 → SparsePoly (Fin 62) := ![
  [{ coefficient := -2, powers := [(0, 1), (8, 1), (35, 1), (41, 1), (48, 1), (60, 1)] }, { coefficient := -1, powers := [(8, 1), (19, 1), (35, 1), (41, 1), (48, 1), (60, 1)] }, { coefficient := -1, powers := [(8, 1), (24, 1), (35, 1), (41, 1), (48, 1), (60, 1)] }, { coefficient := -1, powers := [(8, 1), (30, 1), (35, 1), (36, 1), (41, 1), (60, 1)] }],
  [{ coefficient := -2, powers := [(13, 1), (29, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (35, 1), (60, 1)] }, { coefficient := -1, powers := [(18, 1), (23, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(23, 1), (25, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (8, 1), (30, 1), (35, 1), (41, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (30, 1), (35, 1), (36, 1), (41, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(17, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (8, 1), (35, 1), (41, 1), (56, 1), (61, 1)] }, { coefficient := -1, powers := [(5, 1), (25, 1), (32, 1), (45, 1), (50, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (45, 1), (51, 1), (61, 1)] }, { coefficient := 1, powers := [(13, 1), (23, 1), (25, 1), (45, 1), (50, 1), (61, 1)] }, { coefficient := -1, powers := [(13, 1), (23, 1), (45, 1), (51, 1), (61, 1)] }, { coefficient := 1, powers := [(17, 1), (29, 1), (41, 1), (45, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (22, 1), (33, 1), (41, 1), (48, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (27, 1), (33, 1), (41, 1), (48, 1), (61, 1)] }, { coefficient := -1, powers := [(13, 1), (23, 1), (51, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(29, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (19, 1), (35, 1), (41, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (33, 1), (41, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(18, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (8, 1), (35, 1), (41, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(29, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (25, 1), (32, 1), (50, 1)] }, { coefficient := -1, powers := [(5, 1), (32, 1), (51, 1)] }, { coefficient := -1, powers := [(13, 1), (23, 1), (25, 1), (50, 1)] }, { coefficient := 1, powers := [(13, 1), (23, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(47, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (33, 1), (41, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(23, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (25, 1), (32, 1)] }, { coefficient := 1, powers := [(13, 1), (23, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(13, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (8, 1), (30, 1), (35, 1), (41, 1)] }, { coefficient := -1, powers := [(8, 1), (19, 1), (35, 1), (41, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (35, 1), (41, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (35, 1), (41, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (32, 1)] }, { coefficient := -1, powers := [(13, 1), (23, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (33, 1), (41, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (35, 1), (41, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(0, 1), (8, 1), (35, 1), (36, 1), (41, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (8, 1), (35, 1), (41, 1), (42, 1), (48, 1)] }, { coefficient := -1, powers := [(5, 1), (35, 1), (52, 1)] }, { coefficient := 1, powers := [(8, 1), (19, 1), (35, 1), (41, 1), (42, 1), (48, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (35, 1), (41, 1), (42, 1), (48, 1)] }, { coefficient := 1, powers := [(8, 1), (30, 1), (35, 1), (36, 1), (41, 1), (42, 1)] }, { coefficient := 2, powers := [(13, 1), (29, 1), (47, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(38, 1), (58, 1)] }, { coefficient := 1, powers := [(41, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (1, 1), (8, 1), (35, 1), (41, 1), (53, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (8, 1), (35, 1), (41, 1), (53, 1)] }, { coefficient := 1, powers := [(8, 1), (14, 1), (24, 1), (35, 1), (41, 1)] }, { coefficient := -1, powers := [(8, 1), (24, 1), (35, 1), (41, 1), (42, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (3, 1), (8, 1), (30, 1), (35, 1), (41, 1), (53, 1)] }, { coefficient := -1, powers := [(0, 1), (5, 1), (32, 1), (55, 1)] }, { coefficient := 1, powers := [(0, 1), (8, 1), (19, 1), (35, 1), (41, 1), (48, 1), (53, 1)] }, { coefficient := 1, powers := [(0, 1), (13, 1), (23, 1), (55, 1)] }, { coefficient := -1, powers := [(3, 1), (6, 1), (8, 1), (30, 1), (33, 1), (35, 1), (41, 1)] }, { coefficient := -1, powers := [(3, 1), (8, 1), (14, 1), (24, 1), (30, 1), (35, 1), (41, 1)] }, { coefficient := -1, powers := [(5, 1), (24, 1), (25, 1), (32, 1), (43, 1), (50, 1)] }, { coefficient := 1, powers := [(5, 1), (24, 1), (32, 1), (43, 1), (51, 1)] }, { coefficient := 1, powers := [(6, 1), (8, 1), (19, 1), (33, 1), (35, 1), (41, 1), (48, 1)] }, { coefficient := 1, powers := [(8, 1), (14, 1), (19, 1), (24, 1), (35, 1), (41, 1), (48, 1)] }, { coefficient := 1, powers := [(13, 1), (23, 1), (24, 1), (25, 1), (43, 1), (50, 1)] }, { coefficient := -1, powers := [(13, 1), (23, 1), (24, 1), (43, 1), (51, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (29, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (8, 1), (14, 1), (30, 1), (35, 1), (41, 1)] }, { coefficient := -1, powers := [(3, 1), (8, 1), (24, 1), (35, 1), (41, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (24, 1), (25, 1), (32, 1), (45, 1), (50, 1)] }, { coefficient := -1, powers := [(5, 1), (24, 1), (32, 1), (45, 1), (51, 1)] }, { coefficient := -1, powers := [(8, 1), (14, 1), (30, 1), (35, 1), (36, 1), (41, 1)] }, { coefficient := -1, powers := [(8, 1), (22, 1), (33, 1), (41, 1), (43, 1), (48, 1)] }, { coefficient := -1, powers := [(8, 1), (27, 1), (33, 1), (41, 1), (43, 1), (48, 1)] }, { coefficient := -1, powers := [(13, 1), (23, 1), (24, 1), (25, 1), (45, 1), (50, 1)] }, { coefficient := 1, powers := [(13, 1), (23, 1), (24, 1), (45, 1), (51, 1)] }, { coefficient := 1, powers := [(13, 1), (23, 1), (43, 1), (51, 1)] }, { coefficient := -1, powers := [(17, 1), (24, 1), (29, 1), (41, 1), (45, 1)] }]
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
    (values : Fin 62 → R) :
    ¬ ∀ index : Fin 32,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component17.SelectedLeafB6_1.selectedHasNoCommonZero

end Krenn.Component17.SelectedLeafB6_1
