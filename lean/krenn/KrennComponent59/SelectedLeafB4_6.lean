import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component59.SelectedLeafB4_6

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "5440151b5a6834bd3a181e5c82d11ae2bbea313e621b4be5b106d8fc19d7a8b1"
def certificateSHA256 : String := "e3f1a81b3ba1a517803e74cc1aeaad8e0c82e6e9f80f1197592ca40eaca7058b"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 26 → Fin 617 := ![
  8,
  9,
  23,
  25,
  26,
  27,
  35,
  36,
  192,
  215,
  222,
  247,
  337,
  338,
  341,
  349,
  351,
  426,
  471,
  497,
  516,
  610,
  611,
  613,
  614,
  616
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 26 → SparsePoly (Fin 61) := ![
  [{ coefficient := 1, powers := [(8, 1), (27, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (26, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(26, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (35, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (51, 1)] }, { coefficient := 1, powers := [(18, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (18, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (37, 1), (54, 1)] }, { coefficient := 1, powers := [(54, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (26, 1), (56, 1)] }, { coefficient := 1, powers := [(26, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (45, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (51, 1)] }, { coefficient := 1, powers := [(8, 1), (29, 1)] }, { coefficient := 1, powers := [(12, 1), (26, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1), (54, 1)] }, { coefficient := 1, powers := [(17, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (54, 1)] }, { coefficient := 1, powers := [(26, 1), (45, 1)] }, { coefficient := 1, powers := [(32, 1), (35, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (36, 1), (54, 1)] }, { coefficient := 1, powers := [(3, 1), (27, 1), (54, 1)] }, { coefficient := 1, powers := [(9, 1), (18, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (18, 1), (53, 1)] }, { coefficient := 1, powers := [(12, 1)] }, { coefficient := 1, powers := [(16, 1), (18, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (51, 1)] }, { coefficient := 1, powers := [(26, 1), (38, 1)] }, { coefficient := 1, powers := [(26, 1), (44, 1), (47, 1)] }, { coefficient := 1, powers := [(29, 1), (35, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (35, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (26, 1), (56, 1)] }, { coefficient := 1, powers := [(8, 1), (22, 1), (56, 1)] }, { coefficient := 1, powers := [(16, 1), (26, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (27, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (27, 1), (45, 1)] }, { coefficient := 1, powers := [(11, 1), (19, 1), (54, 1)] }, { coefficient := 1, powers := [(17, 1), (27, 1), (35, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (35, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (38, 1), (54, 1)] }, { coefficient := 1, powers := [(2, 1), (45, 1), (51, 1)] }, { coefficient := 1, powers := [(5, 1), (26, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (51, 1)] }, { coefficient := 1, powers := [(8, 1), (22, 1), (57, 1)] }, { coefficient := 1, powers := [(8, 1), (29, 1), (45, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (38, 1)] }, { coefficient := 1, powers := [(12, 1), (22, 1), (54, 1)] }, { coefficient := 1, powers := [(12, 1), (26, 1), (45, 1)] }, { coefficient := 1, powers := [(12, 1), (32, 1), (35, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (51, 1)] }, { coefficient := 1, powers := [(17, 1), (26, 1), (38, 1)] }, { coefficient := 1, powers := [(17, 1), (29, 1), (35, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (58, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(36, 1), (59, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(38, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 26 → SparsePoly (Fin 61) := ![
  [{ coefficient := 1, powers := [(3, 1), (29, 1), (45, 1), (58, 1), (59, 1)] }],
  [{ coefficient := 2, powers := [(3, 1), (17, 1), (18, 1), (22, 2), (51, 1), (57, 1), (58, 1)] }, { coefficient := -2, powers := [(3, 1), (17, 1), (18, 1), (22, 1), (29, 1), (45, 1), (51, 1), (58, 1)] }, { coefficient := -4, powers := [(3, 1), (17, 1), (22, 1), (29, 1), (35, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (22, 1), (57, 1)] }, { coefficient := -1, powers := [(3, 1), (29, 1), (45, 1)] }],
  [{ coefficient := 2, powers := [(3, 1), (17, 1), (18, 1), (22, 1), (44, 1), (51, 1), (57, 1), (58, 1)] }, { coefficient := 1, powers := [(3, 1), (44, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [(22, 1), (23, 1), (50, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (9, 1), (29, 1), (58, 1), (59, 1)] }, { coefficient := 2, powers := [(5, 1), (17, 1), (22, 1), (29, 1), (51, 1), (58, 1)] }, { coefficient := -4, powers := [(12, 1), (17, 1), (22, 2), (37, 1), (51, 1)] }, { coefficient := -2, powers := [(12, 1), (17, 1), (22, 2), (51, 1), (58, 1)] }, { coefficient := 1, powers := [(12, 1), (22, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (11, 1), (29, 1), (58, 1), (59, 1)] }],
  [{ coefficient := -4, powers := [(12, 1), (17, 1), (22, 1), (44, 1), (54, 1)] }, { coefficient := -2, powers := [(17, 2), (18, 1), (22, 1), (44, 1), (51, 1), (58, 1)] }, { coefficient := -4, powers := [(17, 2), (22, 1), (44, 1), (51, 1)] }, { coefficient := -1, powers := [(17, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (17, 1), (29, 1), (58, 1), (59, 1)] }],
  [{ coefficient := 4, powers := [(12, 1), (17, 1), (22, 2), (37, 1), (54, 1)] }, { coefficient := -4, powers := [(17, 2), (22, 2), (51, 1), (58, 1)] }, { coefficient := -2, powers := [(17, 1), (22, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (50, 1), (54, 1)] }],
  [{ coefficient := -4, powers := [(12, 1), (17, 1), (22, 2), (51, 1)] }],
  [{ coefficient := 2, powers := [(5, 1), (17, 1), (18, 1), (22, 1), (51, 1), (57, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (57, 1)] }, { coefficient := -2, powers := [(12, 1), (17, 1), (18, 1), (22, 1), (45, 1), (51, 1), (58, 1)] }, { coefficient := -4, powers := [(12, 1), (17, 1), (22, 1), (35, 1), (57, 1)] }, { coefficient := -1, powers := [(12, 1), (45, 1)] }],
  [{ coefficient := 2, powers := [(17, 1), (18, 1), (22, 1), (51, 2), (58, 1)] }, { coefficient := 1, powers := [(51, 1)] }],
  [{ coefficient := 2, powers := [(3, 1), (17, 1), (18, 1), (22, 1), (45, 1), (51, 1), (56, 1), (58, 1)] }, { coefficient := 4, powers := [(3, 1), (17, 1), (22, 1), (35, 1), (56, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (45, 1), (56, 1)] }, { coefficient := 2, powers := [(17, 1), (18, 1), (22, 1), (45, 1), (51, 1), (58, 1)] }, { coefficient := 4, powers := [(17, 1), (22, 1), (35, 1), (57, 1)] }, { coefficient := 1, powers := [(45, 1)] }],
  [{ coefficient := 2, powers := [(17, 1), (18, 1), (22, 2), (51, 1), (58, 1)] }, { coefficient := -4, powers := [(17, 1), (22, 1), (29, 1), (35, 1)] }, { coefficient := 1, powers := [(22, 1)] }],
  [{ coefficient := 2, powers := [(12, 1), (17, 1), (18, 1), (22, 1), (51, 1), (58, 1)] }, { coefficient := 1, powers := [(12, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (29, 1), (58, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(22, 1), (54, 1)] }],
  [{ coefficient := 4, powers := [(12, 1), (17, 1), (22, 1), (54, 1)] }, { coefficient := 2, powers := [(17, 2), (18, 1), (22, 1), (51, 1), (58, 1)] }, { coefficient := 4, powers := [(17, 2), (22, 1), (51, 1)] }, { coefficient := 1, powers := [(17, 1)] }],
  [{ coefficient := -2, powers := [(3, 1), (17, 1), (18, 1), (22, 1), (51, 1), (57, 1), (58, 1)] }, { coefficient := -1, powers := [(3, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (29, 1), (58, 1), (59, 1)] }],
  [{ coefficient := -2, powers := [(17, 1), (18, 1), (22, 1), (51, 1), (58, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(5, 1), (29, 1), (54, 1)] }, { coefficient := 4, powers := [(17, 2), (22, 2), (51, 2)] }, { coefficient := 2, powers := [(17, 1), (22, 1), (51, 1)] }],
  [{ coefficient := 2, powers := [(3, 1), (17, 1), (18, 1), (22, 1), (35, 1), (51, 1), (56, 1), (57, 1), (58, 1)] }, { coefficient := -2, powers := [(3, 1), (17, 1), (18, 1), (22, 1), (45, 1), (51, 2), (56, 1), (58, 1)] }, { coefficient := -4, powers := [(3, 1), (17, 1), (22, 1), (35, 1), (51, 1), (56, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (35, 1), (56, 1), (57, 1)] }, { coefficient := -1, powers := [(3, 1), (45, 1), (51, 1), (56, 1)] }, { coefficient := 2, powers := [(17, 1), (18, 1), (22, 1), (35, 1), (51, 1), (57, 1), (58, 1)] }, { coefficient := 2, powers := [(17, 1), (18, 1), (22, 1), (38, 1), (51, 1), (54, 1), (58, 1)] }, { coefficient := -2, powers := [(17, 1), (18, 1), (22, 1), (45, 1), (51, 2), (58, 1)] }, { coefficient := -4, powers := [(17, 1), (22, 1), (35, 1), (51, 1), (57, 1)] }, { coefficient := 1, powers := [(35, 1), (57, 1)] }, { coefficient := 1, powers := [(38, 1), (54, 1)] }, { coefficient := -1, powers := [(45, 1), (51, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (5, 1), (29, 1), (54, 1), (58, 1)] }],
  [{ coefficient := 2, powers := [(8, 1), (17, 1), (18, 1), (22, 1), (32, 1), (51, 1), (58, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1)] }, { coefficient := -4, powers := [(12, 1), (17, 1), (22, 1), (26, 1), (54, 1)] }, { coefficient := -4, powers := [(17, 2), (22, 1), (26, 1), (51, 1)] }]
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

#print axioms Krenn.Component59.SelectedLeafB4_6.selectedHasNoCommonZero

end Krenn.Component59.SelectedLeafB4_6
