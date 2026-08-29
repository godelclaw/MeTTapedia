import KrennSparseCertificate

/-! Selected core of a strict exact certificate over a frozen system. -/

namespace Krenn.X5Case1075Selected

open Krenn.SparseCertificate
open MvPolynomial

def sourceSystemFileSHA256 : String := "2d0e211520ecf0f162dde372ed70e27cbd637c7cd335d0cf72f8f36bb30db164"
def sourceSystemSemanticSHA256 : String := "e1a26c8d17982cd556971e9d6b9ea3f31c48d3ed4c0beea9f322a96ce5a84a5f"
def certificateSHA256 : String := "058ea739b196ad9c40d744a7540bff8d47b84e66bae00c44dda0aa9c3e68a996"
def sourceEquationCount : Nat := 675

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedIndices : Fin 27 → Fin 675 := ![
  0,
  1,
  2,
  3,
  24,
  25,
  26,
  27,
  30,
  34,
  43,
  386,
  414,
  415,
  421,
  423,
  424,
  425,
  427,
  616,
  641,
  642,
  659,
  661,
  662,
  672,
  674
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 27 → SparsePoly (Fin 70) := ![
  [{ coefficient := 1, powers := [(52, 1)] }],
  [{ coefficient := 1, powers := [(54, 1)] }],
  [{ coefficient := 1, powers := [(55, 1)] }],
  [{ coefficient := 1, powers := [(57, 1)] }],
  [{ coefficient := 1, powers := [(35, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(35, 1), (69, 1)] }],
  [{ coefficient := 1, powers := [(37, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(37, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(40, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(43, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(48, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (46, 1), (63, 1)] }, { coefficient := 1, powers := [(58, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (61, 1)] }, { coefficient := 1, powers := [(16, 1), (55, 1)] }, { coefficient := 1, powers := [(24, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (63, 1)] }, { coefficient := 1, powers := [(18, 1), (35, 1), (69, 1)] }, { coefficient := 1, powers := [(26, 1), (35, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(35, 1), (64, 1)] }, { coefficient := 1, powers := [(38, 1), (58, 1)] }, { coefficient := 1, powers := [(44, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(35, 1), (67, 1)] }, { coefficient := 1, powers := [(41, 1), (58, 1)] }, { coefficient := 1, powers := [(44, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(37, 1), (66, 1)] }, { coefficient := 1, powers := [(40, 1), (60, 1)] }, { coefficient := 1, powers := [(51, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(37, 1), (69, 1)] }, { coefficient := 1, powers := [(43, 1), (60, 1)] }, { coefficient := 1, powers := [(51, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(40, 1), (69, 1)] }, { coefficient := 1, powers := [(43, 1), (66, 1)] }, { coefficient := 1, powers := [(51, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (58, 1), (63, 1)] }, { coefficient := 1, powers := [(23, 1), (43, 1), (58, 1)] }, { coefficient := 1, powers := [(31, 1), (40, 1), (58, 1)] }, { coefficient := 1, powers := [(49, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (35, 1), (69, 1)] }, { coefficient := 1, powers := [(31, 1), (35, 1), (66, 1)] }, { coefficient := 1, powers := [(34, 1), (35, 1), (63, 1)] }, { coefficient := 1, powers := [(63, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (55, 1)] }, { coefficient := 1, powers := [(30, 1), (52, 1)] }, { coefficient := 1, powers := [(34, 1), (35, 1), (61, 1)] }, { coefficient := 1, powers := [(34, 1), (38, 1), (55, 1)] }, { coefficient := 1, powers := [(34, 1), (41, 1), (52, 1)] }, { coefficient := 1, powers := [(61, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (46, 1), (61, 1)] }, { coefficient := 1, powers := [(16, 1), (46, 1), (55, 1)] }, { coefficient := 1, powers := [(24, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(52, 1), (67, 1)] }, { coefficient := 1, powers := [(55, 1), (64, 1)] }, { coefficient := 1, powers := [(58, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (48, 1), (63, 1)] }, { coefficient := 1, powers := [(18, 1), (48, 1), (57, 1)] }, { coefficient := 1, powers := [(26, 1), (48, 1), (54, 1)] }, { coefficient := 1, powers := [(54, 1), (69, 1)] }, { coefficient := 1, powers := [(57, 1), (66, 1)] }, { coefficient := 1, powers := [(60, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (49, 1), (63, 1)] }, { coefficient := 1, powers := [(18, 1), (49, 1), (57, 1)] }, { coefficient := 1, powers := [(26, 1), (49, 1), (54, 1)] }, { coefficient := 1, powers := [(32, 1), (37, 1), (63, 1)] }, { coefficient := 1, powers := [(32, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(32, 1), (43, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (52, 1), (67, 1)] }, { coefficient := 1, powers := [(0, 1), (55, 1), (64, 1)] }, { coefficient := 1, powers := [(0, 1), (58, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (38, 1), (67, 1)] }, { coefficient := 1, powers := [(8, 1), (41, 1), (64, 1)] }, { coefficient := 1, powers := [(8, 1), (44, 1), (61, 1)] }, { coefficient := 1, powers := [(16, 1), (35, 1), (67, 1)] }, { coefficient := 1, powers := [(16, 1), (41, 1), (58, 1)] }, { coefficient := 1, powers := [(16, 1), (44, 1), (55, 1)] }, { coefficient := 1, powers := [(24, 1), (35, 1), (64, 1)] }, { coefficient := 1, powers := [(24, 1), (38, 1), (58, 1)] }, { coefficient := 1, powers := [(24, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(32, 1), (35, 1), (61, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1), (55, 1)] }, { coefficient := 1, powers := [(32, 1), (41, 1), (52, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(7, 1), (54, 1), (69, 1)] }, { coefficient := 1, powers := [(7, 1), (57, 1), (66, 1)] }, { coefficient := 1, powers := [(7, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(15, 1), (40, 1), (69, 1)] }, { coefficient := 1, powers := [(15, 1), (43, 1), (66, 1)] }, { coefficient := 1, powers := [(15, 1), (51, 1), (63, 1)] }, { coefficient := 1, powers := [(23, 1), (37, 1), (69, 1)] }, { coefficient := 1, powers := [(23, 1), (43, 1), (60, 1)] }, { coefficient := 1, powers := [(23, 1), (51, 1), (57, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1), (66, 1)] }, { coefficient := 1, powers := [(31, 1), (40, 1), (60, 1)] }, { coefficient := 1, powers := [(31, 1), (51, 1), (54, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1), (63, 1)] }, { coefficient := 1, powers := [(34, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(34, 1), (43, 1), (54, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 27 → SparsePoly (Fin 70) := ![
  [{ coefficient := 1, powers := [(24, 1), (34, 1), (35, 1), (44, 1)] }, { coefficient := 1, powers := [(30, 1), (32, 1), (35, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (8, 1), (26, 1), (34, 1), (35, 1), (38, 1), (48, 1), (67, 1)] }, { coefficient := 1, powers := [(7, 1), (8, 1), (26, 1), (34, 1), (35, 1), (41, 1), (48, 1), (64, 1)] }, { coefficient := -1, powers := [(7, 1), (26, 1), (32, 1), (35, 1), (48, 1), (61, 1)] }, { coefficient := -1, powers := [(7, 1), (26, 1), (34, 1), (35, 1), (48, 1)] }, { coefficient := -1, powers := [(7, 1), (26, 1), (48, 1)] }, { coefficient := -1, powers := [(8, 1), (34, 2), (35, 1), (38, 1), (43, 1), (67, 1)] }, { coefficient := -1, powers := [(8, 1), (34, 2), (35, 1), (41, 1), (43, 1), (64, 1)] }, { coefficient := -1, powers := [(26, 1), (34, 1), (35, 1), (49, 1), (61, 1)] }, { coefficient := 1, powers := [(34, 2), (35, 1), (43, 1)] }, { coefficient := 1, powers := [(34, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (34, 1), (35, 1), (44, 1)] }, { coefficient := 1, powers := [(22, 1), (32, 1), (35, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (8, 1), (18, 1), (34, 1), (35, 1), (38, 1), (48, 1), (67, 1)] }, { coefficient := 1, powers := [(7, 1), (8, 1), (18, 1), (34, 1), (35, 1), (41, 1), (48, 1), (64, 1)] }, { coefficient := -1, powers := [(7, 1), (18, 1), (32, 1), (35, 1), (48, 1), (61, 1)] }, { coefficient := -1, powers := [(7, 1), (18, 1), (34, 1), (35, 1), (48, 1)] }, { coefficient := -1, powers := [(7, 1), (18, 1), (48, 1)] }, { coefficient := -1, powers := [(8, 1), (34, 2), (35, 1), (38, 1), (40, 1), (67, 1)] }, { coefficient := -1, powers := [(8, 1), (34, 2), (35, 1), (40, 1), (41, 1), (64, 1)] }, { coefficient := -1, powers := [(18, 1), (34, 1), (35, 1), (49, 1), (61, 1)] }, { coefficient := 1, powers := [(34, 2), (35, 1), (40, 1)] }, { coefficient := 1, powers := [(34, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (10, 1), (26, 1), (34, 1), (35, 1), (46, 1), (61, 1)] }, { coefficient := -1, powers := [(31, 1), (34, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (10, 1), (18, 1), (34, 1), (35, 1), (46, 1), (61, 1)] }, { coefficient := -1, powers := [(23, 1), (34, 1), (37, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (34, 2), (35, 1), (41, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (34, 2), (35, 1), (38, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (31, 1), (34, 1), (35, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (23, 1), (34, 1), (35, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (8, 1), (10, 1), (34, 1), (35, 1), (38, 1), (67, 1)] }, { coefficient := 1, powers := [(7, 1), (8, 1), (10, 1), (34, 1), (35, 1), (41, 1), (64, 1)] }, { coefficient := -1, powers := [(7, 1), (10, 1), (32, 1), (35, 1), (61, 1)] }, { coefficient := -1, powers := [(7, 1), (10, 1), (34, 1), (35, 1)] }, { coefficient := -1, powers := [(7, 1), (10, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (10, 1), (34, 1), (35, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (34, 1), (35, 1), (46, 1)] }, { coefficient := -1, powers := [(34, 1), (35, 1), (44, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (10, 1), (34, 1), (35, 1), (46, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(24, 1), (34, 1), (35, 1)] }],
  [{ coefficient := -1, powers := [(16, 1), (34, 1), (35, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (31, 1), (34, 1), (35, 1), (38, 1), (67, 1)] }, { coefficient := -1, powers := [(8, 1), (31, 1), (34, 1), (35, 1), (41, 1), (64, 1)] }, { coefficient := 1, powers := [(31, 1), (32, 1), (35, 1), (61, 1)] }, { coefficient := 1, powers := [(31, 1), (34, 1), (35, 1)] }, { coefficient := 1, powers := [(31, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (23, 1), (34, 1), (35, 1), (38, 1), (67, 1)] }, { coefficient := -1, powers := [(8, 1), (23, 1), (34, 1), (35, 1), (41, 1), (64, 1)] }, { coefficient := 1, powers := [(23, 1), (32, 1), (35, 1), (61, 1)] }, { coefficient := 1, powers := [(23, 1), (34, 1), (35, 1)] }, { coefficient := 1, powers := [(23, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (15, 1), (34, 1), (35, 1), (38, 1), (67, 1)] }, { coefficient := -1, powers := [(8, 1), (15, 1), (34, 1), (35, 1), (41, 1), (64, 1)] }, { coefficient := 1, powers := [(15, 1), (32, 1), (35, 1), (61, 1)] }, { coefficient := 1, powers := [(15, 1), (34, 1), (35, 1)] }, { coefficient := 1, powers := [(15, 1)] }],
  [{ coefficient := -1, powers := [(10, 1), (34, 1), (35, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(34, 1), (37, 1)] }],
  [{ coefficient := -1, powers := [(32, 1), (35, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (34, 1), (35, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (8, 1), (34, 1), (35, 1), (38, 1), (67, 1)] }, { coefficient := -1, powers := [(7, 1), (8, 1), (34, 1), (35, 1), (41, 1), (64, 1)] }, { coefficient := 1, powers := [(7, 1), (32, 1), (35, 1), (61, 1)] }, { coefficient := 1, powers := [(7, 1), (34, 1), (35, 1)] }, { coefficient := 1, powers := [(7, 1)] }],
  [{ coefficient := 1, powers := [(34, 1), (35, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(34, 1), (35, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (34, 1), (35, 1), (38, 1), (67, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (35, 1), (41, 1), (64, 1)] }, { coefficient := -1, powers := [(32, 1), (35, 1), (61, 1)] }, { coefficient := -1, powers := [(34, 1), (35, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
theorem constantIdentity :
    ∑ index, (multipliers index).toPoly *
      (selectedEquations index).toPoly = C (1 : ℤ) := by
  simp (config := { maxSteps := 1000000 })
    [Fin.sum_univ_succ, multipliers, selectedEquations,
      SparsePoly.toPoly, SparseTerm.toPoly]
  ring

theorem selectedHasNoCommonZero {R : Type*}
    [CommRing R] [Nontrivial R] [CharZero R]
    (values : Fin 70 → R) :
    ¬ ∀ index : Fin 27,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.X5Case1075Selected.selectedHasNoCommonZero

end Krenn.X5Case1075Selected
