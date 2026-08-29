import KrennSparseCertificate

/-! Selected core of a strict exact certificate over a frozen system. -/

namespace Krenn.X5Case611Selected

open Krenn.SparseCertificate
open MvPolynomial

def sourceSystemFileSHA256 : String := "ff074992f870887a90162a8632d2c089f35f275b81162c5ab1b2ada5b8a2a2bc"
def sourceSystemSemanticSHA256 : String := "b9f869df10faf84de16ee02fc34850a70b6bd1df8b1f673b99b159283bd7c8b6"
def certificateSHA256 : String := "6e10943badabcfe56c9dd90a1cf31f0bc440b02d3fce109e974b9d4589b3ce2c"
def sourceEquationCount : Nat := 675

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedIndices : Fin 21 → Fin 675 := ![
  0,
  1,
  2,
  3,
  25,
  29,
  34,
  35,
  416,
  422,
  423,
  424,
  425,
  426,
  440,
  459,
  514,
  625,
  661,
  673,
  674
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 21 → SparsePoly (Fin 70) := ![
  [{ coefficient := 1, powers := [(56, 1)] }],
  [{ coefficient := 1, powers := [(57, 1)] }],
  [{ coefficient := 1, powers := [(62, 1)] }],
  [{ coefficient := 1, powers := [(63, 1)] }],
  [{ coefficient := 1, powers := [(36, 1), (69, 1)] }],
  [{ coefficient := 1, powers := [(39, 1), (69, 1)] }],
  [{ coefficient := 1, powers := [(43, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(43, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (63, 1)] }, { coefficient := 1, powers := [(18, 1), (57, 1)] }, { coefficient := 1, powers := [(26, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(36, 1), (68, 1)] }, { coefficient := 1, powers := [(42, 1), (59, 1)] }, { coefficient := 1, powers := [(48, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(37, 1), (66, 1)] }, { coefficient := 1, powers := [(40, 1), (60, 1)] }, { coefficient := 1, powers := [(51, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(37, 1), (69, 1)] }, { coefficient := 1, powers := [(43, 1), (60, 1)] }, { coefficient := 1, powers := [(51, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(39, 1), (68, 1)] }, { coefficient := 1, powers := [(42, 1), (65, 1)] }, { coefficient := 1, powers := [(48, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(40, 1), (69, 1)] }, { coefficient := 1, powers := [(43, 1), (66, 1)] }, { coefficient := 1, powers := [(51, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (53, 1), (69, 1)] }, { coefficient := 1, powers := [(31, 1), (51, 1), (53, 1)] }, { coefficient := 1, powers := [(34, 1), (43, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (43, 1), (65, 1)] }, { coefficient := 1, powers := [(17, 1), (43, 1), (59, 1)] }, { coefficient := 1, powers := [(26, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (43, 1), (65, 1)] }, { coefficient := 1, powers := [(22, 1), (43, 1), (59, 1)] }, { coefficient := 1, powers := [(31, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (39, 1), (69, 1)] }, { coefficient := 1, powers := [(17, 1), (36, 1), (69, 1)] }, { coefficient := 1, powers := [(26, 1), (49, 1), (53, 1)] }, { coefficient := 1, powers := [(53, 1), (69, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (49, 1), (63, 1)] }, { coefficient := 1, powers := [(18, 1), (49, 1), (57, 1)] }, { coefficient := 1, powers := [(26, 1), (49, 1), (54, 1)] }, { coefficient := 1, powers := [(54, 1), (69, 1)] }, { coefficient := 1, powers := [(57, 1), (66, 1)] }, { coefficient := 1, powers := [(60, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (53, 1), (68, 1)] }, { coefficient := 1, powers := [(3, 1), (56, 1), (65, 1)] }, { coefficient := 1, powers := [(3, 1), (59, 1), (62, 1)] }, { coefficient := 1, powers := [(11, 1), (39, 1), (68, 1)] }, { coefficient := 1, powers := [(11, 1), (42, 1), (65, 1)] }, { coefficient := 1, powers := [(11, 1), (48, 1), (62, 1)] }, { coefficient := 1, powers := [(20, 1), (36, 1), (68, 1)] }, { coefficient := 1, powers := [(20, 1), (42, 1), (59, 1)] }, { coefficient := 1, powers := [(20, 1), (48, 1), (56, 1)] }, { coefficient := 1, powers := [(28, 1), (36, 1), (65, 1)] }, { coefficient := 1, powers := [(28, 1), (39, 1), (59, 1)] }, { coefficient := 1, powers := [(28, 1), (48, 1), (53, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1), (62, 1)] }, { coefficient := 1, powers := [(33, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(33, 1), (42, 1), (53, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(7, 1), (54, 1), (69, 1)] }, { coefficient := 1, powers := [(7, 1), (57, 1), (66, 1)] }, { coefficient := 1, powers := [(7, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(15, 1), (40, 1), (69, 1)] }, { coefficient := 1, powers := [(15, 1), (43, 1), (66, 1)] }, { coefficient := 1, powers := [(15, 1), (51, 1), (63, 1)] }, { coefficient := 1, powers := [(23, 1), (37, 1), (69, 1)] }, { coefficient := 1, powers := [(23, 1), (43, 1), (60, 1)] }, { coefficient := 1, powers := [(23, 1), (51, 1), (57, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1), (66, 1)] }, { coefficient := 1, powers := [(31, 1), (40, 1), (60, 1)] }, { coefficient := 1, powers := [(31, 1), (51, 1), (54, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1), (63, 1)] }, { coefficient := 1, powers := [(34, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(34, 1), (43, 1), (54, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 21 → SparsePoly (Fin 70) := ![
  [{ coefficient := 1, powers := [(3, 1), (65, 1)] }, { coefficient := 1, powers := [(33, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (34, 1), (40, 1), (53, 1), (68, 1)] }, { coefficient := 1, powers := [(28, 1), (34, 1), (36, 1), (40, 1), (65, 1)] }, { coefficient := 1, powers := [(28, 1), (34, 1), (39, 1), (40, 1), (59, 1)] }, { coefficient := 1, powers := [(28, 1), (34, 1), (40, 1), (48, 1), (53, 1)] }, { coefficient := 1, powers := [(33, 1), (34, 1), (40, 1), (42, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (59, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (34, 1), (37, 1), (53, 1), (68, 1)] }, { coefficient := 1, powers := [(28, 1), (34, 1), (36, 1), (37, 1), (65, 1)] }, { coefficient := 1, powers := [(28, 1), (34, 1), (37, 1), (39, 1), (59, 1)] }, { coefficient := 1, powers := [(28, 1), (34, 1), (37, 1), (48, 1), (53, 1)] }, { coefficient := 1, powers := [(33, 1), (34, 1), (37, 1), (42, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (7, 1), (17, 1), (54, 1), (68, 1)] }, { coefficient := 1, powers := [(7, 1), (17, 1), (28, 1), (48, 1), (54, 1)] }, { coefficient := 1, powers := [(7, 1), (17, 1), (33, 1), (42, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (7, 1), (9, 1), (54, 1), (68, 1)] }, { coefficient := 1, powers := [(7, 1), (9, 1), (28, 1), (48, 1), (54, 1)] }, { coefficient := 1, powers := [(7, 1), (9, 1), (33, 1), (42, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (7, 1), (17, 1), (49, 1), (54, 1), (68, 1)] }, { coefficient := 1, powers := [(3, 1), (22, 1), (51, 1), (54, 1), (68, 1)] }, { coefficient := -1, powers := [(7, 1), (17, 1), (28, 1), (48, 1), (49, 1), (54, 1)] }, { coefficient := -1, powers := [(7, 1), (17, 1), (33, 1), (42, 1), (49, 1), (54, 1)] }, { coefficient := 1, powers := [(22, 1), (28, 1), (48, 1), (51, 1), (54, 1)] }, { coefficient := 1, powers := [(22, 1), (33, 1), (42, 1), (51, 1), (54, 1)] }, { coefficient := 1, powers := [(28, 1), (34, 1), (39, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (7, 1), (9, 1), (49, 1), (54, 1), (68, 1)] }, { coefficient := 1, powers := [(3, 1), (14, 1), (51, 1), (54, 1), (68, 1)] }, { coefficient := -1, powers := [(7, 1), (9, 1), (28, 1), (48, 1), (49, 1), (54, 1)] }, { coefficient := -1, powers := [(7, 1), (9, 1), (33, 1), (42, 1), (49, 1), (54, 1)] }, { coefficient := 1, powers := [(14, 1), (28, 1), (48, 1), (51, 1), (54, 1)] }, { coefficient := 1, powers := [(14, 1), (33, 1), (42, 1), (51, 1), (54, 1)] }, { coefficient := 1, powers := [(28, 1), (34, 1), (36, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (7, 1), (49, 1), (53, 1), (68, 1)] }, { coefficient := -1, powers := [(7, 1), (28, 1), (36, 1), (49, 1), (65, 1)] }, { coefficient := -1, powers := [(7, 1), (28, 1), (39, 1), (49, 1), (59, 1)] }, { coefficient := -1, powers := [(7, 1), (28, 1), (48, 1), (49, 1), (53, 1)] }, { coefficient := -1, powers := [(7, 1), (33, 1), (42, 1), (49, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(20, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (31, 1), (53, 1), (68, 1)] }, { coefficient := 1, powers := [(28, 1), (31, 1), (36, 1), (65, 1)] }, { coefficient := 1, powers := [(28, 1), (31, 1), (39, 1), (59, 1)] }, { coefficient := 1, powers := [(28, 1), (31, 1), (48, 1), (53, 1)] }, { coefficient := 1, powers := [(31, 1), (33, 1), (42, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (23, 1), (53, 1), (68, 1)] }, { coefficient := 1, powers := [(23, 1), (28, 1), (36, 1), (65, 1)] }, { coefficient := 1, powers := [(23, 1), (28, 1), (39, 1), (59, 1)] }, { coefficient := 1, powers := [(23, 1), (28, 1), (48, 1), (53, 1)] }, { coefficient := 1, powers := [(23, 1), (33, 1), (42, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(11, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (15, 1), (53, 1), (68, 1)] }, { coefficient := 1, powers := [(15, 1), (28, 1), (36, 1), (65, 1)] }, { coefficient := 1, powers := [(15, 1), (28, 1), (39, 1), (59, 1)] }, { coefficient := 1, powers := [(15, 1), (28, 1), (48, 1), (53, 1)] }, { coefficient := 1, powers := [(15, 1), (33, 1), (42, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (54, 1), (68, 1)] }, { coefficient := 1, powers := [(28, 1), (48, 1), (54, 1)] }, { coefficient := 1, powers := [(33, 1), (42, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (7, 1), (49, 1), (54, 1), (68, 1)] }, { coefficient := 1, powers := [(7, 1), (28, 1), (48, 1), (49, 1), (54, 1)] }, { coefficient := 1, powers := [(7, 1), (33, 1), (42, 1), (49, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (51, 1), (54, 1), (68, 1)] }, { coefficient := -1, powers := [(28, 1), (48, 1), (51, 1), (54, 1)] }, { coefficient := -1, powers := [(33, 1), (42, 1), (51, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (7, 1), (54, 1), (68, 1)] }, { coefficient := -1, powers := [(7, 1), (28, 1), (48, 1), (54, 1)] }, { coefficient := -1, powers := [(7, 1), (33, 1), (42, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (7, 1), (53, 1), (68, 1)] }, { coefficient := 1, powers := [(7, 1), (28, 1), (36, 1), (65, 1)] }, { coefficient := 1, powers := [(7, 1), (28, 1), (39, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (28, 1), (48, 1), (53, 1)] }, { coefficient := 1, powers := [(7, 1), (33, 1), (42, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(3, 1), (53, 1), (68, 1)] }, { coefficient := -1, powers := [(28, 1), (36, 1), (65, 1)] }, { coefficient := -1, powers := [(28, 1), (39, 1), (59, 1)] }, { coefficient := -1, powers := [(28, 1), (48, 1), (53, 1)] }, { coefficient := -1, powers := [(33, 1), (42, 1), (53, 1)] }]
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
    ¬ ∀ index : Fin 21,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.X5Case611Selected.selectedHasNoCommonZero

end Krenn.X5Case611Selected
