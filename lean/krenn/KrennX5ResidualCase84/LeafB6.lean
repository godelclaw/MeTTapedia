import KrennSparseCertificate

/-! Selected core of a strict exact certificate over a frozen system. -/

namespace Krenn.X5ResidualCase84.LeafB6

open Krenn.SparseCertificate
open MvPolynomial

def sourceSystemFileSHA256 : String := "933cbdeb893e4bcbb9889ff6be5e0565bbfa8259be8b186150a21fa3a1d762b0"
def sourceSystemSemanticSHA256 : String := "7a7827ddad17ba94c7c4ad7f541b1d2d2af2a8a5558b78de8bdda64cdbaf58a2"
def certificateSHA256 : String := "5b3a933b986c82aefbd84fd143f08b3c6b0dcf961bf7f32c7a147d623ac3d519"
def sourceEquationCount : Nat := 678

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedIndices : Fin 21 → Fin 678 := ![
  41,
  42,
  44,
  46,
  51,
  53,
  396,
  405,
  422,
  423,
  424,
  425,
  427,
  660,
  662,
  671,
  673,
  674,
  675,
  676,
  677
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 21 → SparsePoly (Fin 72) := ![
  [{ coefficient := 1, powers := [(47, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(47, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(48, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(48, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(50, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(50, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (47, 1), (57, 1)] }, { coefficient := 1, powers := [(57, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (47, 1), (54, 1)] }, { coefficient := 1, powers := [(54, 1), (68, 1)] }],
  [{ coefficient := 1, powers := [(36, 1), (65, 1)] }, { coefficient := 1, powers := [(39, 1), (59, 1)] }, { coefficient := 1, powers := [(47, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(36, 1), (68, 1)] }, { coefficient := 1, powers := [(42, 1), (59, 1)] }, { coefficient := 1, powers := [(47, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(37, 1), (66, 1)] }, { coefficient := 1, powers := [(40, 1), (60, 1)] }, { coefficient := 1, powers := [(51, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(37, 1), (69, 1)] }, { coefficient := 1, powers := [(43, 1), (60, 1)] }, { coefficient := 1, powers := [(51, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(40, 1), (69, 1)] }, { coefficient := 1, powers := [(43, 1), (66, 1)] }, { coefficient := 1, powers := [(51, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (48, 1), (63, 1)] }, { coefficient := 1, powers := [(18, 1), (48, 1), (57, 1)] }, { coefficient := 1, powers := [(26, 1), (48, 1), (54, 1)] }, { coefficient := 1, powers := [(54, 1), (69, 1)] }, { coefficient := 1, powers := [(57, 1), (66, 1)] }, { coefficient := 1, powers := [(60, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (50, 1), (63, 1)] }, { coefficient := 1, powers := [(20, 1), (50, 1), (57, 1)] }, { coefficient := 1, powers := [(28, 1), (50, 1), (54, 1)] }, { coefficient := 1, powers := [(33, 1), (37, 1), (63, 1)] }, { coefficient := 1, powers := [(33, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(33, 1), (43, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (36, 1), (68, 1)] }, { coefficient := 1, powers := [(17, 1), (42, 1), (59, 1)] }, { coefficient := 1, powers := [(17, 1), (47, 1), (56, 1)] }, { coefficient := 1, powers := [(25, 1), (36, 1), (65, 1)] }, { coefficient := 1, powers := [(25, 1), (39, 1), (59, 1)] }, { coefficient := 1, powers := [(25, 1), (47, 1), (53, 1)] }, { coefficient := 1, powers := [(39, 1), (68, 1)] }, { coefficient := 1, powers := [(42, 1), (65, 1)] }, { coefficient := 1, powers := [(47, 1), (62, 1)] }, { coefficient := 1, powers := [(53, 1), (68, 1)] }, { coefficient := 1, powers := [(56, 1), (65, 1)] }, { coefficient := 1, powers := [(59, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (53, 1), (68, 1)] }, { coefficient := 1, powers := [(3, 1), (56, 1), (65, 1)] }, { coefficient := 1, powers := [(3, 1), (59, 1), (62, 1)] }, { coefficient := 1, powers := [(11, 1), (39, 1), (68, 1)] }, { coefficient := 1, powers := [(11, 1), (42, 1), (65, 1)] }, { coefficient := 1, powers := [(11, 1), (47, 1), (62, 1)] }, { coefficient := 1, powers := [(19, 1), (36, 1), (68, 1)] }, { coefficient := 1, powers := [(19, 1), (42, 1), (59, 1)] }, { coefficient := 1, powers := [(19, 1), (47, 1), (56, 1)] }, { coefficient := 1, powers := [(27, 1), (36, 1), (65, 1)] }, { coefficient := 1, powers := [(27, 1), (39, 1), (59, 1)] }, { coefficient := 1, powers := [(27, 1), (47, 1), (53, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1), (62, 1)] }, { coefficient := 1, powers := [(33, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(33, 1), (42, 1), (53, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(7, 1), (54, 1), (69, 1)] }, { coefficient := 1, powers := [(7, 1), (57, 1), (66, 1)] }, { coefficient := 1, powers := [(7, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(15, 1), (40, 1), (69, 1)] }, { coefficient := 1, powers := [(15, 1), (43, 1), (66, 1)] }, { coefficient := 1, powers := [(15, 1), (51, 1), (63, 1)] }, { coefficient := 1, powers := [(23, 1), (37, 1), (69, 1)] }, { coefficient := 1, powers := [(23, 1), (43, 1), (60, 1)] }, { coefficient := 1, powers := [(23, 1), (51, 1), (57, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1), (66, 1)] }, { coefficient := 1, powers := [(31, 1), (40, 1), (60, 1)] }, { coefficient := 1, powers := [(31, 1), (51, 1), (54, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1), (63, 1)] }, { coefficient := 1, powers := [(34, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(34, 1), (43, 1), (54, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(54, 1), (70, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(57, 1), (71, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(63, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 21 → SparsePoly (Fin 72) := ![
  [{ coefficient := 1, powers := [(3, 1), (25, 1), (39, 1), (70, 1)] }, { coefficient := -1, powers := [(3, 1), (62, 1), (70, 1)] }, { coefficient := -1, powers := [(11, 1), (25, 1), (39, 1), (70, 1)] }, { coefficient := 1, powers := [(11, 1), (62, 1), (70, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (17, 1), (42, 1), (71, 1)] }, { coefficient := -1, powers := [(11, 1), (17, 1), (42, 1), (71, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (26, 1), (33, 1), (36, 1), (62, 1)] }, { coefficient := -1, powers := [(7, 1), (26, 1), (33, 1), (39, 1), (56, 1)] }, { coefficient := -1, powers := [(7, 1), (26, 1), (33, 1), (42, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (18, 1), (33, 1), (36, 1), (62, 1)] }, { coefficient := -1, powers := [(7, 1), (18, 1), (33, 1), (39, 1), (56, 1)] }, { coefficient := -1, powers := [(7, 1), (18, 1), (33, 1), (42, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(28, 1), (34, 1), (36, 1), (62, 1)] }, { coefficient := -1, powers := [(28, 1), (34, 1), (39, 1), (56, 1)] }, { coefficient := -1, powers := [(28, 1), (34, 1), (42, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(20, 1), (34, 1), (36, 1), (62, 1)] }, { coefficient := -1, powers := [(20, 1), (34, 1), (39, 1), (56, 1)] }, { coefficient := -1, powers := [(20, 1), (34, 1), (42, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (42, 1), (71, 1)] }, { coefficient := 1, powers := [(11, 1), (42, 1), (71, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (39, 1), (70, 1)] }, { coefficient := 1, powers := [(11, 1), (39, 1), (70, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (25, 1)] }, { coefficient := 1, powers := [(27, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (17, 1)] }, { coefficient := 1, powers := [(19, 1)] }],
  [{ coefficient := 1, powers := [(31, 1), (33, 1), (36, 1), (62, 1)] }, { coefficient := 1, powers := [(31, 1), (33, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(31, 1), (33, 1), (42, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (33, 1), (36, 1), (62, 1)] }, { coefficient := 1, powers := [(23, 1), (33, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(23, 1), (33, 1), (42, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(15, 1), (33, 1), (36, 1), (62, 1)] }, { coefficient := 1, powers := [(15, 1), (33, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(15, 1), (33, 1), (42, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (33, 1), (36, 1), (62, 1)] }, { coefficient := 1, powers := [(7, 1), (33, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(7, 1), (33, 1), (42, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(34, 1), (36, 1), (62, 1)] }, { coefficient := 1, powers := [(34, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(34, 1), (42, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(3, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(33, 1), (36, 1), (62, 1)] }, { coefficient := -1, powers := [(33, 1), (39, 1), (56, 1)] }, { coefficient := -1, powers := [(33, 1), (42, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (39, 1), (68, 1)] }, { coefficient := 1, powers := [(3, 1), (47, 1), (62, 1)] }, { coefficient := -1, powers := [(11, 1), (39, 1), (68, 1)] }, { coefficient := -1, powers := [(11, 1), (47, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (42, 1), (65, 1)] }, { coefficient := -1, powers := [(11, 1), (42, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (9, 1), (33, 1), (36, 1), (48, 1), (62, 1)] }, { coefficient := -1, powers := [(7, 1), (9, 1), (33, 1), (39, 1), (48, 1), (56, 1)] }, { coefficient := -1, powers := [(7, 1), (9, 1), (33, 1), (42, 1), (48, 1), (53, 1)] }, { coefficient := -1, powers := [(12, 1), (34, 1), (36, 1), (50, 1), (62, 1)] }, { coefficient := -1, powers := [(12, 1), (34, 1), (39, 1), (50, 1), (56, 1)] }, { coefficient := -1, powers := [(12, 1), (34, 1), (42, 1), (50, 1), (53, 1)] }]
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
    (values : Fin 72 → R) :
    ¬ ∀ index : Fin 21,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.X5ResidualCase84.LeafB6.selectedHasNoCommonZero

end Krenn.X5ResidualCase84.LeafB6
