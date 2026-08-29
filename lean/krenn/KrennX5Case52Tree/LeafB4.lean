import KrennSparseCertificate

/-! Selected core of a strict exact certificate over a frozen system. -/

namespace Krenn.X5Case52Tree.LeafB4

open Krenn.SparseCertificate
open MvPolynomial

def sourceSystemFileSHA256 : String := "0888e9cdd1c338b5785b543a45208a2bb23f835998089e45b13333dc6bc6e9be"
def sourceSystemSemanticSHA256 : String := "7305a2ac502faceb8422bbb86c7b48e16a9abda432246946c08d325b2d301fcf"
def certificateSHA256 : String := "81c1d25d86d190b7c31f20d6aba9e02980253355dd88da1bf5d61477537f1893"
def sourceEquationCount : Nat := 678

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedIndices : Fin 19 → Fin 678 := ![
  1,
  48,
  417,
  419,
  420,
  422,
  423,
  424,
  426,
  643,
  660,
  664,
  666,
  671,
  673,
  674,
  675,
  676,
  677
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 19 → SparsePoly (Fin 71) := ![
  [{ coefficient := 1, powers := [(63, 1)] }],
  [{ coefficient := 1, powers := [(49, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (62, 1)] }, { coefficient := 1, powers := [(22, 1), (56, 1)] }, { coefficient := 1, powers := [(30, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(15, 1), (63, 1)] }, { coefficient := 1, powers := [(23, 1), (57, 1)] }, { coefficient := 1, powers := [(31, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (56, 1)] }, { coefficient := 1, powers := [(25, 1), (53, 1)] }, { coefficient := 1, powers := [(62, 1)] }],
  [{ coefficient := 1, powers := [(36, 1), (65, 1)] }, { coefficient := 1, powers := [(39, 1), (59, 1)] }, { coefficient := 1, powers := [(48, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(36, 1), (68, 1)] }, { coefficient := 1, powers := [(42, 1), (59, 1)] }, { coefficient := 1, powers := [(48, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(37, 1), (66, 1)] }, { coefficient := 1, powers := [(40, 1), (60, 1)] }, { coefficient := 1, powers := [(51, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(40, 1), (69, 1)] }, { coefficient := 1, powers := [(43, 1), (66, 1)] }, { coefficient := 1, powers := [(51, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (53, 1), (68, 1)] }, { coefficient := 1, powers := [(0, 1), (56, 1), (65, 1)] }, { coefficient := 1, powers := [(0, 1), (59, 1), (62, 1)] }, { coefficient := 1, powers := [(17, 1), (45, 1), (56, 1)] }, { coefficient := 1, powers := [(25, 1), (45, 1), (53, 1)] }, { coefficient := 1, powers := [(45, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (49, 1), (63, 1)] }, { coefficient := 1, powers := [(26, 1), (49, 1), (54, 1)] }, { coefficient := 1, powers := [(49, 1), (57, 1)] }, { coefficient := 1, powers := [(54, 1), (69, 1)] }, { coefficient := 1, powers := [(57, 1), (66, 1)] }, { coefficient := 1, powers := [(60, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (49, 1), (62, 1)] }, { coefficient := 1, powers := [(22, 1), (49, 1), (56, 1)] }, { coefficient := 1, powers := [(30, 1), (49, 1), (53, 1)] }, { coefficient := 1, powers := [(34, 1), (36, 1), (62, 1)] }, { coefficient := 1, powers := [(34, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(34, 1), (42, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (54, 1), (69, 1)] }, { coefficient := 1, powers := [(1, 1), (57, 1), (66, 1)] }, { coefficient := 1, powers := [(1, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(9, 1), (40, 1), (69, 1)] }, { coefficient := 1, powers := [(9, 1), (43, 1), (66, 1)] }, { coefficient := 1, powers := [(9, 1), (51, 1), (63, 1)] }, { coefficient := 1, powers := [(26, 1), (37, 1), (66, 1)] }, { coefficient := 1, powers := [(26, 1), (40, 1), (60, 1)] }, { coefficient := 1, powers := [(26, 1), (51, 1), (54, 1)] }, { coefficient := 1, powers := [(37, 1), (69, 1)] }, { coefficient := 1, powers := [(43, 1), (60, 1)] }, { coefficient := 1, powers := [(51, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (36, 1), (68, 1)] }, { coefficient := 1, powers := [(17, 1), (42, 1), (59, 1)] }, { coefficient := 1, powers := [(17, 1), (48, 1), (56, 1)] }, { coefficient := 1, powers := [(25, 1), (36, 1), (65, 1)] }, { coefficient := 1, powers := [(25, 1), (39, 1), (59, 1)] }, { coefficient := 1, powers := [(25, 1), (48, 1), (53, 1)] }, { coefficient := 1, powers := [(39, 1), (68, 1)] }, { coefficient := 1, powers := [(42, 1), (65, 1)] }, { coefficient := 1, powers := [(48, 1), (62, 1)] }, { coefficient := 1, powers := [(53, 1), (68, 1)] }, { coefficient := 1, powers := [(56, 1), (65, 1)] }, { coefficient := 1, powers := [(59, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (53, 1), (68, 1)] }, { coefficient := 1, powers := [(3, 1), (56, 1), (65, 1)] }, { coefficient := 1, powers := [(3, 1), (59, 1), (62, 1)] }, { coefficient := 1, powers := [(11, 1), (39, 1), (68, 1)] }, { coefficient := 1, powers := [(11, 1), (42, 1), (65, 1)] }, { coefficient := 1, powers := [(11, 1), (48, 1), (62, 1)] }, { coefficient := 1, powers := [(19, 1), (36, 1), (68, 1)] }, { coefficient := 1, powers := [(19, 1), (42, 1), (59, 1)] }, { coefficient := 1, powers := [(19, 1), (48, 1), (56, 1)] }, { coefficient := 1, powers := [(27, 1), (36, 1), (65, 1)] }, { coefficient := 1, powers := [(27, 1), (39, 1), (59, 1)] }, { coefficient := 1, powers := [(27, 1), (48, 1), (53, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1), (62, 1)] }, { coefficient := 1, powers := [(33, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(33, 1), (42, 1), (53, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(7, 1), (54, 1), (69, 1)] }, { coefficient := 1, powers := [(7, 1), (57, 1), (66, 1)] }, { coefficient := 1, powers := [(7, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(15, 1), (40, 1), (69, 1)] }, { coefficient := 1, powers := [(15, 1), (43, 1), (66, 1)] }, { coefficient := 1, powers := [(15, 1), (51, 1), (63, 1)] }, { coefficient := 1, powers := [(23, 1), (37, 1), (69, 1)] }, { coefficient := 1, powers := [(23, 1), (43, 1), (60, 1)] }, { coefficient := 1, powers := [(23, 1), (51, 1), (57, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1), (66, 1)] }, { coefficient := 1, powers := [(31, 1), (40, 1), (60, 1)] }, { coefficient := 1, powers := [(31, 1), (51, 1), (54, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1), (63, 1)] }, { coefficient := 1, powers := [(34, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(34, 1), (43, 1), (54, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (70, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(3, 1)] }],
  [{ coefficient := 1, powers := [(7, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 19 → SparsePoly (Fin 71) := ![
  [{ coefficient := 1, powers := [(1, 1), (9, 1), (23, 1), (49, 1)] }, { coefficient := -1, powers := [(1, 1), (15, 1), (49, 1)] }, { coefficient := 1, powers := [(7, 1), (60, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (23, 1), (26, 1)] }, { coefficient := -1, powers := [(1, 1), (31, 1)] }],
  [{ coefficient := -1, powers := [(33, 1), (40, 1), (49, 1), (57, 1)] }, { coefficient := -1, powers := [(33, 1), (43, 1), (49, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (34, 1), (40, 1), (45, 1), (57, 1), (70, 1)] }, { coefficient := 1, powers := [(11, 1), (34, 1), (43, 1), (45, 1), (54, 1), (70, 1)] }],
  [{ coefficient := -1, powers := [(11, 1), (25, 1), (34, 1), (40, 1), (57, 1)] }, { coefficient := -1, powers := [(11, 1), (25, 1), (34, 1), (43, 1), (54, 1)] }, { coefficient := 1, powers := [(27, 1), (34, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(27, 1), (34, 1), (43, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(11, 1), (17, 1), (34, 1), (40, 1), (57, 1)] }, { coefficient := -1, powers := [(11, 1), (17, 1), (34, 1), (43, 1), (54, 1)] }, { coefficient := 1, powers := [(19, 1), (34, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(19, 1), (34, 1), (43, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(23, 1), (26, 1)] }, { coefficient := 1, powers := [(31, 1)] }],
  [{ coefficient := -1, powers := [(9, 1), (23, 1)] }, { coefficient := 1, powers := [(15, 1)] }],
  [{ coefficient := -1, powers := [(11, 1), (34, 1), (40, 1), (57, 1), (70, 1)] }, { coefficient := -1, powers := [(11, 1), (34, 1), (43, 1), (54, 1), (70, 1)] }],
  [{ coefficient := -1, powers := [(1, 1), (23, 1)] }],
  [{ coefficient := 1, powers := [(33, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(33, 1), (43, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(23, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (34, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(11, 1), (34, 1), (43, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(34, 1), (40, 1), (57, 1)] }, { coefficient := -1, powers := [(34, 1), (43, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(11, 1), (34, 1), (40, 1), (53, 1), (57, 1), (68, 1)] }, { coefficient := 1, powers := [(11, 1), (34, 1), (40, 1), (56, 1), (57, 1), (65, 1)] }, { coefficient := 1, powers := [(11, 1), (34, 1), (40, 1), (57, 1), (59, 1), (62, 1)] }, { coefficient := 1, powers := [(11, 1), (34, 1), (43, 1), (53, 1), (54, 1), (68, 1)] }, { coefficient := 1, powers := [(11, 1), (34, 1), (43, 1), (54, 1), (56, 1), (65, 1)] }, { coefficient := 1, powers := [(11, 1), (34, 1), (43, 1), (54, 1), (59, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(34, 1), (40, 1), (53, 1), (57, 1), (68, 1)] }, { coefficient := 1, powers := [(34, 1), (40, 1), (56, 1), (57, 1), (65, 1)] }, { coefficient := 1, powers := [(34, 1), (40, 1), (57, 1), (59, 1), (62, 1)] }, { coefficient := 1, powers := [(34, 1), (43, 1), (53, 1), (54, 1), (68, 1)] }, { coefficient := 1, powers := [(34, 1), (43, 1), (54, 1), (56, 1), (65, 1)] }, { coefficient := 1, powers := [(34, 1), (43, 1), (54, 1), (59, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(54, 1), (69, 1)] }, { coefficient := 1, powers := [(57, 1), (66, 1)] }]
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
    ¬ ∀ index : Fin 19,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.X5Case52Tree.LeafB4.selectedHasNoCommonZero

end Krenn.X5Case52Tree.LeafB4
