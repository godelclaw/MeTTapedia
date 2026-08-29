import KrennSparseCertificate

/-! Selected core of a strict exact certificate over a frozen system. -/

namespace Krenn.X5ResidualCase385.LeafB1

open Krenn.SparseCertificate
open MvPolynomial

def sourceSystemFileSHA256 : String := "12f91a972f53596d5c7dd862f7e616512319ed7f5b568fb7600e642352e0d427"
def sourceSystemSemanticSHA256 : String := "8c33d6e2fa10a74117c474d85c5f72e47f802ac40c9e1ea907f74e41001e13b0"
def certificateSHA256 : String := "77403f54480b24e4731006be42789fd190ded681ec00491257f9839957fa9588"
def sourceEquationCount : Nat := 678

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedIndices : Fin 20 → Fin 678 := ![
  6,
  46,
  47,
  48,
  49,
  307,
  324,
  422,
  423,
  424,
  425,
  427,
  444,
  663,
  664,
  666,
  671,
  673,
  674,
  677
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 20 → SparsePoly (Fin 71) := ![
  [{ coefficient := 1, powers := [(14, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(48, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(48, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(48, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(48, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(48, 1), (61, 1)] }, { coefficient := 1, powers := [(60, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (60, 1), (61, 1)] }, { coefficient := 1, powers := [(51, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(36, 1), (65, 1)] }, { coefficient := 1, powers := [(39, 1), (59, 1)] }, { coefficient := 1, powers := [(47, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(36, 1), (68, 1)] }, { coefficient := 1, powers := [(42, 1), (59, 1)] }, { coefficient := 1, powers := [(47, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(37, 1), (66, 1)] }, { coefficient := 1, powers := [(40, 1), (60, 1)] }, { coefficient := 1, powers := [(51, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(37, 1), (69, 1)] }, { coefficient := 1, powers := [(43, 1), (60, 1)] }, { coefficient := 1, powers := [(51, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(39, 1), (68, 1)] }, { coefficient := 1, powers := [(42, 1), (65, 1)] }, { coefficient := 1, powers := [(47, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (60, 1), (61, 1)] }, { coefficient := 1, powers := [(15, 1), (51, 1), (61, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (48, 1), (62, 1)] }, { coefficient := 1, powers := [(22, 1), (48, 1), (56, 1)] }, { coefficient := 1, powers := [(30, 1), (48, 1), (53, 1)] }, { coefficient := 1, powers := [(34, 1), (36, 1), (62, 1)] }, { coefficient := 1, powers := [(34, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(34, 1), (42, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (48, 1), (57, 1)] }, { coefficient := 1, powers := [(26, 1), (48, 1), (54, 1)] }, { coefficient := 1, powers := [(48, 1), (63, 1)] }, { coefficient := 1, powers := [(54, 1), (69, 1)] }, { coefficient := 1, powers := [(57, 1), (66, 1)] }, { coefficient := 1, powers := [(60, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (54, 1), (69, 1)] }, { coefficient := 1, powers := [(1, 1), (57, 1), (66, 1)] }, { coefficient := 1, powers := [(1, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(18, 1), (37, 1), (69, 1)] }, { coefficient := 1, powers := [(18, 1), (43, 1), (60, 1)] }, { coefficient := 1, powers := [(18, 1), (51, 1), (57, 1)] }, { coefficient := 1, powers := [(26, 1), (37, 1), (66, 1)] }, { coefficient := 1, powers := [(26, 1), (40, 1), (60, 1)] }, { coefficient := 1, powers := [(26, 1), (51, 1), (54, 1)] }, { coefficient := 1, powers := [(40, 1), (69, 1)] }, { coefficient := 1, powers := [(43, 1), (66, 1)] }, { coefficient := 1, powers := [(51, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (39, 1), (68, 1)] }, { coefficient := 1, powers := [(9, 1), (42, 1), (65, 1)] }, { coefficient := 1, powers := [(9, 1), (47, 1), (62, 1)] }, { coefficient := 1, powers := [(17, 1), (36, 1), (68, 1)] }, { coefficient := 1, powers := [(17, 1), (42, 1), (59, 1)] }, { coefficient := 1, powers := [(17, 1), (47, 1), (56, 1)] }, { coefficient := 1, powers := [(25, 1), (36, 1), (65, 1)] }, { coefficient := 1, powers := [(25, 1), (39, 1), (59, 1)] }, { coefficient := 1, powers := [(25, 1), (47, 1), (53, 1)] }, { coefficient := 1, powers := [(53, 1), (68, 1)] }, { coefficient := 1, powers := [(56, 1), (65, 1)] }, { coefficient := 1, powers := [(59, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (53, 1), (68, 1)] }, { coefficient := 1, powers := [(3, 1), (56, 1), (65, 1)] }, { coefficient := 1, powers := [(3, 1), (59, 1), (62, 1)] }, { coefficient := 1, powers := [(11, 1), (39, 1), (68, 1)] }, { coefficient := 1, powers := [(11, 1), (42, 1), (65, 1)] }, { coefficient := 1, powers := [(11, 1), (47, 1), (62, 1)] }, { coefficient := 1, powers := [(20, 1), (36, 1), (68, 1)] }, { coefficient := 1, powers := [(20, 1), (42, 1), (59, 1)] }, { coefficient := 1, powers := [(20, 1), (47, 1), (56, 1)] }, { coefficient := 1, powers := [(28, 1), (36, 1), (65, 1)] }, { coefficient := 1, powers := [(28, 1), (39, 1), (59, 1)] }, { coefficient := 1, powers := [(28, 1), (47, 1), (53, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1), (62, 1)] }, { coefficient := 1, powers := [(33, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(33, 1), (42, 1), (53, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(7, 1), (54, 1), (69, 1)] }, { coefficient := 1, powers := [(7, 1), (57, 1), (66, 1)] }, { coefficient := 1, powers := [(7, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(15, 1), (40, 1), (69, 1)] }, { coefficient := 1, powers := [(15, 1), (43, 1), (66, 1)] }, { coefficient := 1, powers := [(15, 1), (51, 1), (63, 1)] }, { coefficient := 1, powers := [(23, 1), (37, 1), (69, 1)] }, { coefficient := 1, powers := [(23, 1), (43, 1), (60, 1)] }, { coefficient := 1, powers := [(23, 1), (51, 1), (57, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1), (66, 1)] }, { coefficient := 1, powers := [(31, 1), (40, 1), (60, 1)] }, { coefficient := 1, powers := [(31, 1), (51, 1), (54, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1), (63, 1)] }, { coefficient := 1, powers := [(34, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(34, 1), (43, 1), (54, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(61, 1), (70, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 20 → SparsePoly (Fin 71) := ![
  [{ coefficient := -1, powers := [(33, 1), (40, 1), (48, 1), (57, 1), (61, 1), (62, 1), (70, 2)] }, { coefficient := -1, powers := [(33, 1), (43, 1), (48, 1), (54, 1), (61, 1), (62, 1), (70, 2)] }],
  [{ coefficient := -1, powers := [(30, 1), (33, 1), (40, 1), (57, 1), (61, 1), (70, 1)] }, { coefficient := -1, powers := [(30, 1), (33, 1), (43, 1), (54, 1), (61, 1), (70, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (15, 1), (26, 1), (61, 1), (70, 1)] }, { coefficient := -1, powers := [(7, 1), (26, 1), (61, 1), (70, 1)] }],
  [{ coefficient := -1, powers := [(22, 1), (33, 1), (40, 1), (57, 1), (61, 1), (70, 1)] }, { coefficient := -1, powers := [(22, 1), (33, 1), (43, 1), (54, 1), (61, 1), (70, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (15, 1), (18, 1), (61, 1), (70, 1)] }, { coefficient := -1, powers := [(7, 1), (18, 1), (61, 1), (70, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (15, 1), (61, 1), (63, 1), (70, 2)] }, { coefficient := -1, powers := [(7, 1), (61, 1), (63, 1), (70, 2)] }],
  [{ coefficient := -1, powers := [(15, 1), (61, 1), (63, 1), (70, 2)] }],
  [{ coefficient := -1, powers := [(3, 1), (25, 1), (34, 1), (40, 1), (57, 1), (61, 1), (70, 1)] }, { coefficient := -1, powers := [(3, 1), (25, 1), (34, 1), (43, 1), (54, 1), (61, 1), (70, 1)] }, { coefficient := 1, powers := [(28, 1), (34, 1), (40, 1), (57, 1), (61, 1), (70, 1)] }, { coefficient := 1, powers := [(28, 1), (34, 1), (43, 1), (54, 1), (61, 1), (70, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (17, 1), (34, 1), (40, 1), (57, 1), (61, 1), (70, 1)] }, { coefficient := -1, powers := [(3, 1), (17, 1), (34, 1), (43, 1), (54, 1), (61, 1), (70, 1)] }, { coefficient := 1, powers := [(20, 1), (34, 1), (40, 1), (57, 1), (61, 1), (70, 1)] }, { coefficient := 1, powers := [(20, 1), (34, 1), (43, 1), (54, 1), (61, 1), (70, 1)] }],
  [{ coefficient := -1, powers := [(15, 1), (26, 1), (61, 1), (70, 1)] }, { coefficient := 1, powers := [(31, 1), (61, 1), (70, 1)] }],
  [{ coefficient := -1, powers := [(15, 1), (18, 1), (61, 1), (70, 1)] }, { coefficient := 1, powers := [(23, 1), (61, 1), (70, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (9, 1), (34, 1), (40, 1), (57, 1), (61, 1), (70, 1)] }, { coefficient := -1, powers := [(3, 1), (9, 1), (34, 1), (43, 1), (54, 1), (61, 1), (70, 1)] }, { coefficient := 1, powers := [(11, 1), (34, 1), (40, 1), (57, 1), (61, 1), (70, 1)] }, { coefficient := 1, powers := [(11, 1), (34, 1), (43, 1), (54, 1), (61, 1), (70, 1)] }],
  [{ coefficient := 1, powers := [(63, 1), (70, 1)] }],
  [{ coefficient := 1, powers := [(33, 1), (40, 1), (57, 1), (61, 1), (70, 1)] }, { coefficient := 1, powers := [(33, 1), (43, 1), (54, 1), (61, 1), (70, 1)] }],
  [{ coefficient := -1, powers := [(1, 1), (15, 1), (61, 1), (70, 1)] }, { coefficient := 1, powers := [(7, 1), (61, 1), (70, 1)] }],
  [{ coefficient := 1, powers := [(15, 1), (61, 1), (70, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (34, 1), (40, 1), (57, 1), (61, 1), (70, 1)] }, { coefficient := 1, powers := [(3, 1), (34, 1), (43, 1), (54, 1), (61, 1), (70, 1)] }],
  [{ coefficient := -1, powers := [(34, 1), (40, 1), (57, 1), (61, 1), (70, 1)] }, { coefficient := -1, powers := [(34, 1), (43, 1), (54, 1), (61, 1), (70, 1)] }],
  [{ coefficient := -1, powers := [(61, 1), (70, 1)] }],
  [{ coefficient := -1, powers := [(1, 1), (15, 1), (48, 1), (61, 1), (63, 1), (70, 1)] }, { coefficient := 1, powers := [(7, 1), (48, 1), (61, 1), (63, 1), (70, 1)] }, { coefficient := 1, powers := [(7, 1), (60, 1), (61, 1), (63, 1), (70, 1)] }, { coefficient := 1, powers := [(14, 1), (33, 1), (40, 1), (48, 1), (57, 1), (61, 1), (62, 1), (70, 1)] }, { coefficient := 1, powers := [(14, 1), (33, 1), (43, 1), (48, 1), (54, 1), (61, 1), (62, 1), (70, 1)] }, { coefficient := 1, powers := [(15, 1), (51, 1), (61, 1), (63, 1), (70, 1)] }, { coefficient := -1, powers := [] }]
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
    ¬ ∀ index : Fin 20,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.X5ResidualCase385.LeafB1.selectedHasNoCommonZero

end Krenn.X5ResidualCase385.LeafB1
