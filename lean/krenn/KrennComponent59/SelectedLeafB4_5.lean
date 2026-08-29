import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component59.SelectedLeafB4_5

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "b133c97879f36db74f4b38a6cd50cf8bb08f39420405a417f8e412c4f8f40a6c"
def certificateSHA256 : String := "5b897bd826c2f12f1c048f6b94264e74dffb88198121ec5d0522a1429cb249b8"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 26 → Fin 617 := ![
  9,
  23,
  33,
  35,
  215,
  216,
  220,
  222,
  331,
  337,
  338,
  341,
  346,
  348,
  349,
  426,
  441,
  471,
  497,
  498,
  559,
  610,
  611,
  613,
  614,
  615
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 26 → SparsePoly (Fin 61) := ![
  [{ coefficient := 1, powers := [(8, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (26, 1)] }],
  [{ coefficient := 1, powers := [(26, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(26, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (18, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (40, 1)] }, { coefficient := 1, powers := [(17, 1), (18, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(26, 1), (37, 1)] }, { coefficient := 1, powers := [(26, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (37, 1), (54, 1)] }, { coefficient := 1, powers := [(54, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (40, 1)] }, { coefficient := 1, powers := [(18, 1), (40, 1)] }, { coefficient := 1, powers := [(23, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (45, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (51, 1)] }, { coefficient := 1, powers := [(8, 1), (29, 1)] }, { coefficient := 1, powers := [(12, 1), (26, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1), (54, 1)] }, { coefficient := 1, powers := [(17, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (42, 1)] }, { coefficient := 1, powers := [(12, 1), (53, 1)] }, { coefficient := 1, powers := [(16, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (43, 1)] }, { coefficient := 1, powers := [(17, 1), (37, 1)] }, { coefficient := 1, powers := [(17, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (54, 1)] }, { coefficient := 1, powers := [(26, 1), (45, 1)] }, { coefficient := 1, powers := [(32, 1), (35, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (18, 1), (53, 1)] }, { coefficient := 1, powers := [(12, 1)] }, { coefficient := 1, powers := [(16, 1), (18, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (23, 1), (43, 1)] }, { coefficient := 1, powers := [(17, 1), (23, 1), (37, 1)] }, { coefficient := 1, powers := [(17, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (51, 1)] }, { coefficient := 1, powers := [(26, 1), (38, 1)] }, { coefficient := 1, powers := [(26, 1), (44, 1), (47, 1)] }, { coefficient := 1, powers := [(29, 1), (35, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (35, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (26, 1), (56, 1)] }, { coefficient := 1, powers := [(8, 1), (22, 1), (56, 1)] }, { coefficient := 1, powers := [(16, 1), (26, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (36, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (36, 1)] }, { coefficient := 1, powers := [(11, 1), (26, 1), (40, 1)] }, { coefficient := 1, powers := [(17, 1), (26, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1)] }, { coefficient := 1, powers := [(6, 1), (56, 1)] }, { coefficient := 1, powers := [(23, 1), (37, 1)] }, { coefficient := 1, powers := [(23, 1), (42, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (35, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (38, 1), (54, 1)] }, { coefficient := 1, powers := [(2, 1), (45, 1), (51, 1)] }, { coefficient := 1, powers := [(5, 1), (26, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (51, 1)] }, { coefficient := 1, powers := [(8, 1), (22, 1), (57, 1)] }, { coefficient := 1, powers := [(8, 1), (29, 1), (45, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (38, 1)] }, { coefficient := 1, powers := [(12, 1), (22, 1), (54, 1)] }, { coefficient := 1, powers := [(12, 1), (26, 1), (45, 1)] }, { coefficient := 1, powers := [(12, 1), (32, 1), (35, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (51, 1)] }, { coefficient := 1, powers := [(17, 1), (26, 1), (38, 1)] }, { coefficient := 1, powers := [(17, 1), (29, 1), (35, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (58, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(36, 1), (59, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(37, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 26 → SparsePoly (Fin 61) := ![
  [{ coefficient := 1, powers := [(6, 1), (22, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (44, 1), (57, 1)] }, { coefficient := -1, powers := [(18, 1), (45, 1), (50, 1)] }, { coefficient := -1, powers := [(23, 1), (45, 1), (50, 1)] }],
  [{ coefficient := -1, powers := [(11, 1), (38, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(17, 1), (44, 1)] }],
  [{ coefficient := 2, powers := [(22, 1), (40, 1), (51, 1), (58, 1)] }, { coefficient := 2, powers := [(22, 1), (43, 1), (51, 1)] }, { coefficient := 1, powers := [(26, 1), (38, 1), (40, 1), (58, 1)] }, { coefficient := 1, powers := [(26, 1), (38, 1), (43, 1)] }, { coefficient := 1, powers := [(26, 1), (45, 1), (50, 1)] }],
  [{ coefficient := 2, powers := [(22, 1), (51, 1)] }, { coefficient := 1, powers := [(26, 1), (38, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (5, 1), (57, 1)] }, { coefficient := -1, powers := [(5, 1), (23, 1), (57, 1)] }, { coefficient := -1, powers := [(12, 1), (18, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (29, 1)] }, { coefficient := -1, powers := [(12, 1), (22, 1)] }],
  [{ coefficient := -2, powers := [(16, 1), (22, 1), (51, 1), (58, 1)] }, { coefficient := -1, powers := [(16, 1), (26, 1), (38, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(51, 1)] }],
  [{ coefficient := 1, powers := [(45, 1)] }],
  [{ coefficient := 1, powers := [(22, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (26, 1), (45, 1)] }],
  [{ coefficient := -2, powers := [(18, 1), (22, 1), (51, 1)] }, { coefficient := -1, powers := [(18, 1), (26, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(12, 1)] }],
  [{ coefficient := -1, powers := [(26, 1), (45, 1)] }],
  [{ coefficient := -2, powers := [(22, 1), (51, 1)] }, { coefficient := -1, powers := [(26, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(17, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(38, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (26, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := 2, powers := [(16, 1), (22, 1), (40, 1), (51, 1)] }, { coefficient := 1, powers := [(16, 1), (26, 1), (38, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (35, 1), (56, 1), (57, 1)] }, { coefficient := 1, powers := [(35, 1), (57, 1)] }, { coefficient := -1, powers := [(36, 1), (38, 1), (54, 1), (59, 1)] }, { coefficient := 1, powers := [(38, 1), (54, 1)] }, { coefficient := -1, powers := [(45, 1), (51, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [(17, 1), (26, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (5, 1), (26, 1), (57, 1)] }, { coefficient := -1, powers := [(0, 1), (5, 1), (29, 1), (54, 1)] }, { coefficient := 1, powers := [(0, 1), (12, 1), (22, 1), (54, 1)] }, { coefficient := 1, powers := [(12, 1), (18, 1), (26, 1), (45, 1)] }, { coefficient := 2, powers := [(17, 1), (18, 1), (22, 1), (51, 1)] }, { coefficient := 1, powers := [(17, 1), (18, 1), (26, 1), (38, 1)] }, { coefficient := 2, powers := [(17, 1), (22, 1), (23, 1), (51, 1)] }, { coefficient := 1, powers := [(17, 1), (23, 1), (26, 1), (38, 1)] }]
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
    (values : Fin 61 → R) :
    ¬ ∀ index : Fin 26,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component59.SelectedLeafB4_5.selectedHasNoCommonZero

end Krenn.Component59.SelectedLeafB4_5
