import KrennSparseCertificate

/-! Selected core of a strict exact certificate over a frozen system. -/

namespace Krenn.X5ResidualCase86.LeafB2

open Krenn.SparseCertificate
open MvPolynomial

def sourceSystemFileSHA256 : String := "f893b6e641df702e77e1f58f753dfb69edca93a1a1906c97fe596981602f12c1"
def sourceSystemSemanticSHA256 : String := "0b9db3572febe92601f98e595cc4530f13fa87fe9172778c1a02e4a3d03638c5"
def certificateSHA256 : String := "09696ae4e1cabd49f61f3b714fc8774e95b4a7a89635863016343c84e0eed087"
def sourceEquationCount : Nat := 678

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedIndices : Fin 23 → Fin 678 := ![
  5,
  8,
  14,
  24,
  25,
  35,
  44,
  46,
  399,
  411,
  423,
  424,
  426,
  441,
  495,
  542,
  633,
  650,
  660,
  674,
  675,
  676,
  677
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 23 → SparsePoly (Fin 71) := ![
  [{ coefficient := 1, powers := [(14, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(36, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(36, 1), (69, 1)] }],
  [{ coefficient := 1, powers := [(43, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(48, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(48, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (48, 1), (55, 1)] }, { coefficient := 1, powers := [(55, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(32, 1), (36, 1), (63, 1)] }, { coefficient := 1, powers := [(63, 1)] }],
  [{ coefficient := 1, powers := [(37, 1), (66, 1)] }, { coefficient := 1, powers := [(40, 1), (60, 1)] }, { coefficient := 1, powers := [(51, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(37, 1), (69, 1)] }, { coefficient := 1, powers := [(43, 1), (60, 1)] }, { coefficient := 1, powers := [(51, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(40, 1), (69, 1)] }, { coefficient := 1, powers := [(43, 1), (66, 1)] }, { coefficient := 1, powers := [(51, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (55, 1), (66, 1)] }, { coefficient := 1, powers := [(23, 1), (51, 1), (55, 1)] }, { coefficient := 1, powers := [(34, 1), (40, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (49, 1), (61, 1)] }, { coefficient := 1, powers := [(37, 1), (64, 1)] }, { coefficient := 1, powers := [(37, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (36, 1), (69, 1)] }, { coefficient := 1, powers := [(26, 1), (36, 1), (66, 1)] }, { coefficient := 1, powers := [(48, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (48, 1), (63, 1)] }, { coefficient := 1, powers := [(23, 1), (36, 1), (69, 1)] }, { coefficient := 1, powers := [(31, 1), (36, 1), (66, 1)] }, { coefficient := 1, powers := [(34, 1), (36, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (52, 1), (67, 1)] }, { coefficient := 1, powers := [(3, 1), (55, 1), (64, 1)] }, { coefficient := 1, powers := [(3, 1), (58, 1), (61, 1)] }, { coefficient := 1, powers := [(10, 1), (61, 1)] }, { coefficient := 1, powers := [(52, 1)] }, { coefficient := 1, powers := [(55, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (48, 1), (63, 1)] }, { coefficient := 1, powers := [(18, 1), (48, 1), (57, 1)] }, { coefficient := 1, powers := [(26, 1), (48, 1), (54, 1)] }, { coefficient := 1, powers := [(54, 1), (69, 1)] }, { coefficient := 1, powers := [(57, 1), (66, 1)] }, { coefficient := 1, powers := [(60, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (54, 1), (69, 1)] }, { coefficient := 1, powers := [(7, 1), (57, 1), (66, 1)] }, { coefficient := 1, powers := [(7, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(15, 1), (40, 1), (69, 1)] }, { coefficient := 1, powers := [(15, 1), (43, 1), (66, 1)] }, { coefficient := 1, powers := [(15, 1), (51, 1), (63, 1)] }, { coefficient := 1, powers := [(23, 1), (37, 1), (69, 1)] }, { coefficient := 1, powers := [(23, 1), (43, 1), (60, 1)] }, { coefficient := 1, powers := [(23, 1), (51, 1), (57, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1), (66, 1)] }, { coefficient := 1, powers := [(31, 1), (40, 1), (60, 1)] }, { coefficient := 1, powers := [(31, 1), (51, 1), (54, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1), (63, 1)] }, { coefficient := 1, powers := [(34, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(34, 1), (43, 1), (54, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(52, 1)] }],
  [{ coefficient := 1, powers := [(55, 1), (70, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(61, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 23 → SparsePoly (Fin 71) := ![
  [{ coefficient := 1, powers := [(3, 1), (32, 1), (37, 1), (48, 1), (67, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (7, 1), (48, 1), (57, 1), (64, 1), (70, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (51, 1), (57, 1), (64, 1), (70, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (7, 1), (9, 1), (26, 1), (64, 1)] }, { coefficient := 1, powers := [(3, 1), (31, 1), (32, 1), (37, 1), (67, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (7, 1), (9, 1), (18, 1), (64, 1)] }, { coefficient := 1, powers := [(3, 1), (23, 1), (32, 1), (37, 1), (67, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (34, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (7, 1), (26, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (7, 1), (18, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (7, 1), (57, 1), (64, 1), (70, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (34, 1), (37, 1), (67, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (31, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (23, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (15, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (57, 1), (64, 1), (70, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (34, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (7, 1), (9, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (32, 1), (37, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(70, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (7, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (67, 1), (70, 1)] }, { coefficient := -1, powers := [(70, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (34, 1), (40, 1), (57, 1), (64, 1)] }, { coefficient := -1, powers := [(3, 1), (64, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(3, 1), (12, 1), (34, 1), (49, 1), (63, 1)] }, { coefficient := -1, powers := [(3, 1), (58, 1), (70, 1)] }, { coefficient := -1, powers := [(10, 1), (70, 1)] }]
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
    ¬ ∀ index : Fin 23,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.X5ResidualCase86.LeafB2.selectedHasNoCommonZero

end Krenn.X5ResidualCase86.LeafB2
