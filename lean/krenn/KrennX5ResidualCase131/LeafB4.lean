import KrennSparseCertificate

/-! Selected core of a strict exact certificate over a frozen system. -/

namespace Krenn.X5ResidualCase131.LeafB4

open Krenn.SparseCertificate
open MvPolynomial

def sourceSystemFileSHA256 : String := "af5df90db555bb1c2e521d656e63a29a35033371e45000fae247958e69f9e809"
def sourceSystemSemanticSHA256 : String := "9fdde2ac898b81f91b8cc9f0c165a79b74e24aa0603b51d111deaf3031c8751f"
def certificateSHA256 : String := "0ded2c09183eeb426a2bf5dafb84b96b0d6c37feffd83207603e3af89a78e2a8"
def sourceEquationCount : Nat := 678

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedIndices : Fin 24 → Fin 678 := ![
  17,
  18,
  20,
  23,
  33,
  45,
  402,
  406,
  416,
  418,
  420,
  422,
  423,
  426,
  429,
  490,
  659,
  660,
  663,
  672,
  674,
  675,
  676,
  677
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 24 → SparsePoly (Fin 71) := ![
  [{ coefficient := 1, powers := [(24, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(26, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(31, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(41, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(47, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (47, 1), (54, 1)] }, { coefficient := 1, powers := [(54, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(26, 1), (49, 1), (52, 1)] }, { coefficient := 1, powers := [(52, 1), (69, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (63, 1)] }, { coefficient := 1, powers := [(18, 1), (57, 1)] }, { coefficient := 1, powers := [(26, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (61, 1)] }, { coefficient := 1, powers := [(21, 1), (55, 1)] }, { coefficient := 1, powers := [(29, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(15, 1), (63, 1)] }, { coefficient := 1, powers := [(23, 1), (57, 1)] }, { coefficient := 1, powers := [(31, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(35, 1), (64, 1)] }, { coefficient := 1, powers := [(38, 1), (58, 1)] }, { coefficient := 1, powers := [(44, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(35, 1), (67, 1)] }, { coefficient := 1, powers := [(41, 1), (58, 1)] }, { coefficient := 1, powers := [(44, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(38, 1), (67, 1)] }, { coefficient := 1, powers := [(41, 1), (64, 1)] }, { coefficient := 1, powers := [(44, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (54, 1), (67, 1)] }, { coefficient := 1, powers := [(24, 1), (44, 1), (54, 1)] }, { coefficient := 1, powers := [(32, 1), (41, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (41, 1), (66, 1)] }, { coefficient := 1, powers := [(27, 1), (46, 1), (54, 1)] }, { coefficient := 1, powers := [(41, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (47, 1), (61, 1)] }, { coefficient := 1, powers := [(16, 1), (47, 1), (55, 1)] }, { coefficient := 1, powers := [(24, 1), (47, 1), (52, 1)] }, { coefficient := 1, powers := [(52, 1), (67, 1)] }, { coefficient := 1, powers := [(55, 1), (64, 1)] }, { coefficient := 1, powers := [(58, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (49, 1), (63, 1)] }, { coefficient := 1, powers := [(18, 1), (49, 1), (57, 1)] }, { coefficient := 1, powers := [(26, 1), (49, 1), (54, 1)] }, { coefficient := 1, powers := [(54, 1), (69, 1)] }, { coefficient := 1, powers := [(57, 1), (66, 1)] }, { coefficient := 1, powers := [(60, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (46, 1), (61, 1)] }, { coefficient := 1, powers := [(21, 1), (46, 1), (55, 1)] }, { coefficient := 1, powers := [(29, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(34, 1), (35, 1), (61, 1)] }, { coefficient := 1, powers := [(34, 1), (38, 1), (55, 1)] }, { coefficient := 1, powers := [(34, 1), (41, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (52, 1), (67, 1)] }, { coefficient := 1, powers := [(0, 1), (55, 1), (64, 1)] }, { coefficient := 1, powers := [(0, 1), (58, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (38, 1), (67, 1)] }, { coefficient := 1, powers := [(8, 1), (41, 1), (64, 1)] }, { coefficient := 1, powers := [(8, 1), (44, 1), (61, 1)] }, { coefficient := 1, powers := [(16, 1), (35, 1), (67, 1)] }, { coefficient := 1, powers := [(16, 1), (41, 1), (58, 1)] }, { coefficient := 1, powers := [(16, 1), (44, 1), (55, 1)] }, { coefficient := 1, powers := [(24, 1), (35, 1), (64, 1)] }, { coefficient := 1, powers := [(24, 1), (38, 1), (58, 1)] }, { coefficient := 1, powers := [(24, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(32, 1), (35, 1), (61, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1), (55, 1)] }, { coefficient := 1, powers := [(32, 1), (41, 1), (52, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(7, 1), (54, 1), (69, 1)] }, { coefficient := 1, powers := [(7, 1), (57, 1), (66, 1)] }, { coefficient := 1, powers := [(7, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(15, 1), (40, 1), (69, 1)] }, { coefficient := 1, powers := [(15, 1), (43, 1), (66, 1)] }, { coefficient := 1, powers := [(15, 1), (51, 1), (63, 1)] }, { coefficient := 1, powers := [(23, 1), (37, 1), (69, 1)] }, { coefficient := 1, powers := [(23, 1), (43, 1), (60, 1)] }, { coefficient := 1, powers := [(23, 1), (51, 1), (57, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1), (66, 1)] }, { coefficient := 1, powers := [(31, 1), (40, 1), (60, 1)] }, { coefficient := 1, powers := [(31, 1), (51, 1), (54, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1), (63, 1)] }, { coefficient := 1, powers := [(34, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(34, 1), (43, 1), (54, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(52, 1), (70, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(55, 1)] }],
  [{ coefficient := 1, powers := [(61, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 24 → SparsePoly (Fin 71) := ![
  [{ coefficient := 1, powers := [(0, 1), (34, 1), (43, 1), (47, 1), (52, 1)] }, { coefficient := -1, powers := [(34, 1), (43, 1), (44, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(15, 1), (40, 1), (49, 1), (70, 1)] }, { coefficient := -1, powers := [(23, 1), (37, 1), (49, 1), (70, 1)] }],
  [{ coefficient := -1, powers := [(23, 1), (32, 1), (43, 1), (46, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(37, 1), (66, 1), (70, 1)] }, { coefficient := 1, powers := [(40, 1), (60, 1), (70, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (23, 1), (32, 1), (43, 1), (52, 1)] }, { coefficient := 1, powers := [(15, 1), (32, 1), (43, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (15, 1), (24, 1), (43, 1), (66, 1)] }, { coefficient := -1, powers := [(0, 1), (23, 1), (24, 1), (43, 1), (52, 1), (60, 1), (70, 1)] }, { coefficient := -1, powers := [(0, 1), (24, 1), (34, 1), (37, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (24, 1), (34, 1), (40, 1), (57, 1)] }, { coefficient := -1, powers := [(0, 1), (24, 1), (34, 1), (43, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (34, 1), (43, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(15, 1), (40, 1), (70, 1)] }, { coefficient := 1, powers := [(23, 1), (37, 1), (70, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (49, 1)] }],
  [{ coefficient := -1, powers := [(32, 1), (37, 1), (46, 1), (63, 1)] }, { coefficient := -1, powers := [(32, 1), (40, 1), (46, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(51, 1)] }],
  [{ coefficient := 1, powers := [(15, 1), (24, 1), (43, 1), (66, 1)] }, { coefficient := 1, powers := [(23, 1), (24, 1), (43, 1), (52, 1), (60, 1), (70, 1)] }, { coefficient := 1, powers := [(24, 1), (34, 1), (37, 1), (63, 1)] }, { coefficient := 1, powers := [(24, 1), (34, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(24, 1), (34, 1), (43, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(15, 1), (16, 1), (43, 1), (66, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1), (43, 1), (52, 1), (60, 1), (70, 1)] }, { coefficient := 1, powers := [(16, 1), (34, 1), (37, 1), (63, 1)] }, { coefficient := 1, powers := [(16, 1), (34, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(16, 1), (34, 1), (43, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (15, 1), (43, 1), (66, 1)] }, { coefficient := 1, powers := [(8, 1), (23, 1), (43, 1), (52, 1), (60, 1), (70, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (37, 1), (63, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (43, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(34, 1), (43, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (32, 1), (43, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (15, 1), (43, 1), (66, 1)] }, { coefficient := 1, powers := [(0, 1), (23, 1), (43, 1), (52, 1), (60, 1), (70, 1)] }, { coefficient := 1, powers := [(0, 1), (34, 1), (37, 1), (63, 1)] }, { coefficient := 1, powers := [(0, 1), (34, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (34, 1), (43, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(7, 1)] }],
  [{ coefficient := 1, powers := [(32, 1), (37, 1), (63, 1)] }, { coefficient := 1, powers := [(32, 1), (40, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [(15, 1), (43, 1), (66, 1)] }, { coefficient := -1, powers := [(23, 1), (43, 1), (52, 1), (60, 1), (70, 1)] }, { coefficient := -1, powers := [(34, 1), (37, 1), (63, 1)] }, { coefficient := -1, powers := [(34, 1), (40, 1), (57, 1)] }, { coefficient := -1, powers := [(34, 1), (43, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(15, 1), (40, 1), (69, 1)] }, { coefficient := 1, powers := [(23, 1), (32, 1), (41, 1), (43, 1), (52, 1), (60, 1)] }, { coefficient := -1, powers := [(23, 1), (37, 1), (69, 1)] }, { coefficient := -1, powers := [(23, 1), (43, 1), (60, 1)] }, { coefficient := -1, powers := [(31, 1), (37, 1), (66, 1)] }, { coefficient := -1, powers := [(31, 1), (40, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (15, 1), (16, 1), (43, 1), (47, 1), (66, 1)] }, { coefficient := -1, powers := [(0, 1), (16, 1), (23, 1), (43, 1), (47, 1), (52, 1), (60, 1), (70, 1)] }, { coefficient := -1, powers := [(0, 1), (16, 1), (34, 1), (37, 1), (47, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (16, 1), (34, 1), (40, 1), (47, 1), (57, 1)] }, { coefficient := -1, powers := [(0, 1), (16, 1), (34, 1), (43, 1), (47, 1), (54, 1)] }, { coefficient := 1, powers := [(15, 1), (32, 1), (38, 1), (43, 1), (66, 1)] }, { coefficient := 1, powers := [(23, 1), (32, 1), (38, 1), (43, 1), (52, 1), (60, 1), (70, 1)] }, { coefficient := 1, powers := [(32, 1), (34, 1), (38, 1), (43, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (8, 1), (15, 1), (43, 1), (47, 1), (66, 1)] }, { coefficient := -1, powers := [(0, 1), (8, 1), (23, 1), (43, 1), (47, 1), (52, 1), (60, 1), (70, 1)] }, { coefficient := -1, powers := [(0, 1), (8, 1), (34, 1), (37, 1), (47, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (8, 1), (34, 1), (40, 1), (47, 1), (57, 1)] }, { coefficient := -1, powers := [(0, 1), (8, 1), (34, 1), (43, 1), (47, 1), (54, 1)] }, { coefficient := 1, powers := [(15, 1), (32, 1), (35, 1), (43, 1), (66, 1)] }, { coefficient := 1, powers := [(23, 1), (32, 1), (35, 1), (43, 1), (52, 1), (60, 1), (70, 1)] }, { coefficient := 1, powers := [(32, 1), (34, 1), (35, 1), (43, 1), (54, 1)] }]
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
    (values : Fin 71 → R) :
    ¬ ∀ index : Fin 24,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.X5ResidualCase131.LeafB4.selectedHasNoCommonZero

end Krenn.X5ResidualCase131.LeafB4
