import KrennSparseCertificate

/-! Selected core of a strict exact certificate over a frozen system. -/

namespace Krenn.X5Case609Selected

open Krenn.SparseCertificate
open MvPolynomial

def sourceSystemFileSHA256 : String := "80fe1a7f1d26d3885e4f71860bb1fd76f61419b8fc4c43ae1bb4181c6555b289"
def sourceSystemSemanticSHA256 : String := "f7919304d23bb995e45159e2bbb08ef21d9ea53880c07fcdfedc794020d7791d"
def certificateSHA256 : String := "f6c498874650fc52e0dd4428a78df7c5910831095527ca3999433e5b4d5c59f6"
def sourceEquationCount : Nat := 675

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedIndices : Fin 15 → Fin 675 := ![
  0,
  1,
  2,
  3,
  417,
  422,
  423,
  424,
  425,
  426,
  440,
  518,
  670,
  673,
  674
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 15 → SparsePoly (Fin 70) := ![
  [{ coefficient := 1, powers := [(56, 1)] }],
  [{ coefficient := 1, powers := [(57, 1)] }],
  [{ coefficient := 1, powers := [(62, 1)] }],
  [{ coefficient := 1, powers := [(63, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (62, 1)] }, { coefficient := 1, powers := [(20, 1), (56, 1)] }, { coefficient := 1, powers := [(28, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(36, 1), (68, 1)] }, { coefficient := 1, powers := [(42, 1), (59, 1)] }, { coefficient := 1, powers := [(48, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(37, 1), (66, 1)] }, { coefficient := 1, powers := [(40, 1), (60, 1)] }, { coefficient := 1, powers := [(51, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(37, 1), (69, 1)] }, { coefficient := 1, powers := [(43, 1), (60, 1)] }, { coefficient := 1, powers := [(51, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(39, 1), (68, 1)] }, { coefficient := 1, powers := [(42, 1), (65, 1)] }, { coefficient := 1, powers := [(48, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(40, 1), (69, 1)] }, { coefficient := 1, powers := [(43, 1), (66, 1)] }, { coefficient := 1, powers := [(51, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (53, 1), (69, 1)] }, { coefficient := 1, powers := [(31, 1), (51, 1), (53, 1)] }, { coefficient := 1, powers := [(34, 1), (43, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (51, 1), (62, 1)] }, { coefficient := 1, powers := [(22, 1), (51, 1), (56, 1)] }, { coefficient := 1, powers := [(51, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (53, 1), (68, 1)] }, { coefficient := 1, powers := [(6, 1), (56, 1), (65, 1)] }, { coefficient := 1, powers := [(6, 1), (59, 1), (62, 1)] }, { coefficient := 1, powers := [(14, 1), (39, 1), (68, 1)] }, { coefficient := 1, powers := [(14, 1), (42, 1), (65, 1)] }, { coefficient := 1, powers := [(14, 1), (48, 1), (62, 1)] }, { coefficient := 1, powers := [(22, 1), (36, 1), (68, 1)] }, { coefficient := 1, powers := [(22, 1), (42, 1), (59, 1)] }, { coefficient := 1, powers := [(22, 1), (48, 1), (56, 1)] }, { coefficient := 1, powers := [(36, 1), (65, 1)] }, { coefficient := 1, powers := [(39, 1), (59, 1)] }, { coefficient := 1, powers := [(48, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (53, 1), (68, 1)] }, { coefficient := 1, powers := [(3, 1), (56, 1), (65, 1)] }, { coefficient := 1, powers := [(3, 1), (59, 1), (62, 1)] }, { coefficient := 1, powers := [(11, 1), (39, 1), (68, 1)] }, { coefficient := 1, powers := [(11, 1), (42, 1), (65, 1)] }, { coefficient := 1, powers := [(11, 1), (48, 1), (62, 1)] }, { coefficient := 1, powers := [(20, 1), (36, 1), (68, 1)] }, { coefficient := 1, powers := [(20, 1), (42, 1), (59, 1)] }, { coefficient := 1, powers := [(20, 1), (48, 1), (56, 1)] }, { coefficient := 1, powers := [(28, 1), (36, 1), (65, 1)] }, { coefficient := 1, powers := [(28, 1), (39, 1), (59, 1)] }, { coefficient := 1, powers := [(28, 1), (48, 1), (53, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1), (62, 1)] }, { coefficient := 1, powers := [(33, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(33, 1), (42, 1), (53, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(7, 1), (54, 1), (69, 1)] }, { coefficient := 1, powers := [(7, 1), (57, 1), (66, 1)] }, { coefficient := 1, powers := [(7, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(15, 1), (40, 1), (69, 1)] }, { coefficient := 1, powers := [(15, 1), (43, 1), (66, 1)] }, { coefficient := 1, powers := [(15, 1), (51, 1), (63, 1)] }, { coefficient := 1, powers := [(23, 1), (37, 1), (69, 1)] }, { coefficient := 1, powers := [(23, 1), (43, 1), (60, 1)] }, { coefficient := 1, powers := [(23, 1), (51, 1), (57, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1), (66, 1)] }, { coefficient := 1, powers := [(31, 1), (40, 1), (60, 1)] }, { coefficient := 1, powers := [(31, 1), (51, 1), (54, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1), (63, 1)] }, { coefficient := 1, powers := [(34, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(34, 1), (43, 1), (54, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 15 → SparsePoly (Fin 70) := ![
  [{ coefficient := 1, powers := [(3, 1), (22, 1), (31, 1), (51, 1), (54, 1), (68, 1)] }, { coefficient := 1, powers := [(3, 1), (65, 1)] }, { coefficient := -1, powers := [(6, 1), (22, 1), (28, 1), (31, 1), (51, 1), (54, 1), (68, 1)] }, { coefficient := -1, powers := [(6, 1), (28, 1), (65, 1)] }, { coefficient := -1, powers := [(20, 1), (48, 1)] }, { coefficient := -1, powers := [(22, 1), (28, 1), (31, 1), (48, 1), (51, 1), (54, 1)] }, { coefficient := 1, powers := [(22, 1), (31, 1), (33, 1), (42, 1), (51, 1), (54, 1)] }, { coefficient := 1, powers := [(33, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (7, 1), (53, 1), (66, 1), (68, 1)] }, { coefficient := 1, powers := [(3, 1), (34, 1), (40, 1), (53, 1), (68, 1)] }, { coefficient := -1, powers := [(6, 1), (7, 1), (28, 1), (53, 1), (66, 1), (68, 1)] }, { coefficient := -1, powers := [(6, 1), (28, 1), (34, 1), (40, 1), (53, 1), (68, 1)] }, { coefficient := -1, powers := [(7, 1), (28, 1), (48, 1), (53, 1), (66, 1)] }, { coefficient := 1, powers := [(7, 1), (33, 1), (42, 1), (53, 1), (66, 1)] }, { coefficient := -1, powers := [(28, 1), (34, 1), (40, 1), (48, 1), (53, 1)] }, { coefficient := 1, powers := [(33, 1), (34, 1), (40, 1), (42, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (14, 1), (31, 1), (51, 1), (54, 1), (68, 1)] }, { coefficient := 1, powers := [(3, 1), (59, 1)] }, { coefficient := -1, powers := [(6, 1), (14, 1), (28, 1), (31, 1), (51, 1), (54, 1), (68, 1)] }, { coefficient := -1, powers := [(6, 1), (28, 1), (59, 1)] }, { coefficient := -1, powers := [(11, 1), (48, 1)] }, { coefficient := -1, powers := [(14, 1), (28, 1), (31, 1), (48, 1), (51, 1), (54, 1)] }, { coefficient := 1, powers := [(14, 1), (31, 1), (33, 1), (42, 1), (51, 1), (54, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (7, 1), (53, 1), (60, 1), (68, 1)] }, { coefficient := 1, powers := [(3, 1), (34, 1), (37, 1), (53, 1), (68, 1)] }, { coefficient := -1, powers := [(6, 1), (7, 1), (28, 1), (53, 1), (60, 1), (68, 1)] }, { coefficient := -1, powers := [(6, 1), (28, 1), (34, 1), (37, 1), (53, 1), (68, 1)] }, { coefficient := -1, powers := [(7, 1), (28, 1), (48, 1), (53, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (33, 1), (42, 1), (53, 1), (60, 1)] }, { coefficient := -1, powers := [(28, 1), (34, 1), (37, 1), (48, 1), (53, 1)] }, { coefficient := 1, powers := [(33, 1), (34, 1), (37, 1), (42, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(48, 1)] }],
  [{ coefficient := 1, powers := [(20, 1)] }, { coefficient := -1, powers := [(22, 1), (28, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (31, 1), (53, 1), (68, 1)] }, { coefficient := -1, powers := [(6, 1), (28, 1), (31, 1), (53, 1), (68, 1)] }, { coefficient := -1, powers := [(28, 1), (31, 1), (48, 1), (53, 1)] }, { coefficient := 1, powers := [(31, 1), (33, 1), (42, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (23, 1), (53, 1), (68, 1)] }, { coefficient := -1, powers := [(6, 1), (23, 1), (28, 1), (53, 1), (68, 1)] }, { coefficient := -1, powers := [(23, 1), (28, 1), (48, 1), (53, 1)] }, { coefficient := 1, powers := [(23, 1), (33, 1), (42, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(11, 1)] }, { coefficient := -1, powers := [(14, 1), (28, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (15, 1), (53, 1), (68, 1)] }, { coefficient := -1, powers := [(6, 1), (15, 1), (28, 1), (53, 1), (68, 1)] }, { coefficient := -1, powers := [(15, 1), (28, 1), (48, 1), (53, 1)] }, { coefficient := 1, powers := [(15, 1), (33, 1), (42, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (54, 1), (68, 1)] }, { coefficient := -1, powers := [(6, 1), (28, 1), (54, 1), (68, 1)] }, { coefficient := -1, powers := [(28, 1), (48, 1), (54, 1)] }, { coefficient := 1, powers := [(33, 1), (42, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (31, 1), (54, 1), (68, 1)] }, { coefficient := 1, powers := [(6, 1), (28, 1), (31, 1), (54, 1), (68, 1)] }, { coefficient := 1, powers := [(28, 1), (31, 1), (48, 1), (54, 1)] }, { coefficient := -1, powers := [(31, 1), (33, 1), (42, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(28, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(3, 1), (53, 1), (68, 1)] }, { coefficient := 1, powers := [(6, 1), (28, 1), (53, 1), (68, 1)] }, { coefficient := 1, powers := [(28, 1), (48, 1), (53, 1)] }, { coefficient := -1, powers := [(33, 1), (42, 1), (53, 1)] }]
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
    ¬ ∀ index : Fin 15,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.X5Case609Selected.selectedHasNoCommonZero

end Krenn.X5Case609Selected
