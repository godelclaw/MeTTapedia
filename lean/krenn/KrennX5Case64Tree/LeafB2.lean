import KrennSparseCertificate

/-! Selected core of a strict exact certificate over a frozen system. -/

namespace Krenn.X5Case64Tree.LeafB2

open Krenn.SparseCertificate
open MvPolynomial

def sourceSystemFileSHA256 : String := "1ac5ab5d518692291b4c28ce55e7ae7fdc2aaa16bed0d4f7b3db8cfa1258a0e1"
def sourceSystemSemanticSHA256 : String := "43469b00632245c07b611d5de50cee29f246c4340e6c1919f45911d07c07fc98"
def certificateSHA256 : String := "bd627653502cd81b7388d1c86622265ee1dc51794db146c143803282747edee6"
def sourceEquationCount : Nat := 678

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedIndices : Fin 20 → Fin 678 := ![
  1,
  15,
  30,
  31,
  384,
  412,
  419,
  420,
  422,
  423,
  424,
  426,
  442,
  613,
  642,
  665,
  671,
  673,
  674,
  677
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 20 → SparsePoly (Fin 71) := ![
  [{ coefficient := 1, powers := [(63, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(40, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(40, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (53, 1), (67, 1)] }, { coefficient := 1, powers := [(53, 1)] }],
  [{ coefficient := 1, powers := [(32, 1), (40, 1), (56, 1)] }, { coefficient := 1, powers := [(56, 1)] }],
  [{ coefficient := 1, powers := [(15, 1), (63, 1)] }, { coefficient := 1, powers := [(23, 1), (57, 1)] }, { coefficient := 1, powers := [(31, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (56, 1)] }, { coefficient := 1, powers := [(25, 1), (53, 1)] }, { coefficient := 1, powers := [(62, 1)] }],
  [{ coefficient := 1, powers := [(36, 1), (65, 1)] }, { coefficient := 1, powers := [(39, 1), (59, 1)] }, { coefficient := 1, powers := [(48, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(36, 1), (68, 1)] }, { coefficient := 1, powers := [(42, 1), (59, 1)] }, { coefficient := 1, powers := [(48, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(37, 1), (66, 1)] }, { coefficient := 1, powers := [(40, 1), (60, 1)] }, { coefficient := 1, powers := [(51, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(40, 1), (69, 1)] }, { coefficient := 1, powers := [(43, 1), (66, 1)] }, { coefficient := 1, powers := [(51, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (56, 1), (66, 1)] }, { coefficient := 1, powers := [(23, 1), (51, 1), (56, 1)] }, { coefficient := 1, powers := [(34, 1), (40, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (54, 1), (67, 1)] }, { coefficient := 1, powers := [(15, 1), (40, 1), (67, 1)] }, { coefficient := 1, powers := [(23, 1), (37, 1), (67, 1)] }, { coefficient := 1, powers := [(54, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (63, 1)] }, { coefficient := 1, powers := [(26, 1), (54, 1)] }, { coefficient := 1, powers := [(32, 1), (37, 1), (63, 1)] }, { coefficient := 1, powers := [(32, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(32, 1), (43, 1), (54, 1)] }, { coefficient := 1, powers := [(57, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (47, 1), (56, 1)] }, { coefficient := 1, powers := [(25, 1), (47, 1), (53, 1)] }, { coefficient := 1, powers := [(32, 1), (36, 1), (62, 1)] }, { coefficient := 1, powers := [(32, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(32, 1), (42, 1), (53, 1)] }, { coefficient := 1, powers := [(47, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (36, 1), (68, 1)] }, { coefficient := 1, powers := [(17, 1), (42, 1), (59, 1)] }, { coefficient := 1, powers := [(17, 1), (48, 1), (56, 1)] }, { coefficient := 1, powers := [(25, 1), (36, 1), (65, 1)] }, { coefficient := 1, powers := [(25, 1), (39, 1), (59, 1)] }, { coefficient := 1, powers := [(25, 1), (48, 1), (53, 1)] }, { coefficient := 1, powers := [(39, 1), (68, 1)] }, { coefficient := 1, powers := [(42, 1), (65, 1)] }, { coefficient := 1, powers := [(48, 1), (62, 1)] }, { coefficient := 1, powers := [(53, 1), (68, 1)] }, { coefficient := 1, powers := [(56, 1), (65, 1)] }, { coefficient := 1, powers := [(59, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (53, 1), (68, 1)] }, { coefficient := 1, powers := [(3, 1), (56, 1), (65, 1)] }, { coefficient := 1, powers := [(3, 1), (59, 1), (62, 1)] }, { coefficient := 1, powers := [(11, 1), (39, 1), (68, 1)] }, { coefficient := 1, powers := [(11, 1), (42, 1), (65, 1)] }, { coefficient := 1, powers := [(11, 1), (48, 1), (62, 1)] }, { coefficient := 1, powers := [(19, 1), (36, 1), (68, 1)] }, { coefficient := 1, powers := [(19, 1), (42, 1), (59, 1)] }, { coefficient := 1, powers := [(19, 1), (48, 1), (56, 1)] }, { coefficient := 1, powers := [(28, 1), (36, 1), (65, 1)] }, { coefficient := 1, powers := [(28, 1), (39, 1), (59, 1)] }, { coefficient := 1, powers := [(28, 1), (48, 1), (53, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1), (62, 1)] }, { coefficient := 1, powers := [(33, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(33, 1), (42, 1), (53, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(7, 1), (54, 1), (69, 1)] }, { coefficient := 1, powers := [(7, 1), (57, 1), (66, 1)] }, { coefficient := 1, powers := [(7, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(15, 1), (40, 1), (69, 1)] }, { coefficient := 1, powers := [(15, 1), (43, 1), (66, 1)] }, { coefficient := 1, powers := [(15, 1), (51, 1), (63, 1)] }, { coefficient := 1, powers := [(23, 1), (37, 1), (69, 1)] }, { coefficient := 1, powers := [(23, 1), (43, 1), (60, 1)] }, { coefficient := 1, powers := [(23, 1), (51, 1), (57, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1), (66, 1)] }, { coefficient := 1, powers := [(31, 1), (40, 1), (60, 1)] }, { coefficient := 1, powers := [(31, 1), (51, 1), (54, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1), (63, 1)] }, { coefficient := 1, powers := [(34, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(34, 1), (43, 1), (54, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(7, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 20 → SparsePoly (Fin 71) := ![
  [{ coefficient := -1, powers := [(3, 1), (7, 1), (32, 1), (40, 1), (56, 1), (60, 1), (65, 1)] }, { coefficient := 1, powers := [(3, 1), (9, 1), (34, 1), (40, 1), (56, 1), (65, 1)] }, { coefficient := 1, powers := [(3, 1), (15, 1), (32, 1), (40, 1), (51, 1), (56, 1), (65, 1)] }, { coefficient := 1, powers := [(7, 1), (11, 1), (32, 1), (40, 1), (56, 1), (60, 1), (65, 1)] }, { coefficient := -1, powers := [(9, 1), (11, 1), (34, 1), (40, 1), (56, 1), (65, 1)] }, { coefficient := -1, powers := [(11, 1), (15, 1), (32, 1), (40, 1), (51, 1), (56, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (26, 1), (34, 1), (37, 1), (40, 1), (65, 1), (67, 1)] }, { coefficient := -1, powers := [(3, 1), (31, 1), (32, 1), (37, 1), (40, 1), (51, 1), (65, 1), (67, 1)] }, { coefficient := -1, powers := [(3, 1), (32, 1), (37, 1), (40, 1), (65, 1), (69, 1)] }, { coefficient := -1, powers := [(3, 1), (32, 1), (40, 1), (43, 1), (60, 1), (65, 1)] }, { coefficient := 1, powers := [(3, 1), (32, 1), (40, 1), (51, 1), (57, 1), (65, 1)] }, { coefficient := 1, powers := [(11, 1), (26, 1), (34, 1), (37, 1), (40, 1), (65, 1), (67, 1)] }, { coefficient := 1, powers := [(11, 1), (31, 1), (32, 1), (37, 1), (40, 1), (51, 1), (65, 1), (67, 1)] }, { coefficient := 1, powers := [(11, 1), (32, 1), (37, 1), (40, 1), (65, 1), (69, 1)] }, { coefficient := 1, powers := [(11, 1), (32, 1), (40, 1), (43, 1), (60, 1), (65, 1)] }, { coefficient := -1, powers := [(11, 1), (32, 1), (40, 1), (51, 1), (57, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (17, 1), (32, 1), (56, 1)] }, { coefficient := -1, powers := [(11, 1), (17, 1), (32, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (15, 1), (26, 1), (34, 1), (40, 1), (56, 1), (65, 1)] }, { coefficient := -1, powers := [(3, 1), (15, 1), (31, 1), (32, 1), (40, 1), (51, 1), (56, 1), (65, 1)] }, { coefficient := 1, powers := [(11, 1), (15, 1), (26, 1), (34, 1), (40, 1), (56, 1), (65, 1)] }, { coefficient := 1, powers := [(11, 1), (15, 1), (31, 1), (32, 1), (40, 1), (51, 1), (56, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (25, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (68, 1)] }, { coefficient := 1, powers := [(11, 1), (25, 1), (59, 1)] }, { coefficient := -1, powers := [(11, 1), (68, 1)] }, { coefficient := -1, powers := [(25, 1), (32, 1), (33, 1), (36, 1), (40, 1)] }, { coefficient := -1, powers := [(25, 1), (33, 1), (36, 1)] }, { coefficient := 1, powers := [(32, 1), (33, 1), (40, 1), (42, 1)] }, { coefficient := 1, powers := [(33, 1), (42, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (17, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (34, 1), (40, 1), (57, 1), (65, 1)] }, { coefficient := 1, powers := [(3, 1), (65, 1)] }, { coefficient := 1, powers := [(11, 1), (17, 1), (59, 1)] }, { coefficient := -1, powers := [(11, 1), (34, 1), (40, 1), (57, 1), (65, 1)] }, { coefficient := -1, powers := [(11, 1), (65, 1)] }, { coefficient := -1, powers := [(17, 1), (33, 1), (36, 1)] }, { coefficient := 1, powers := [(33, 1), (39, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (32, 1), (40, 1), (51, 1), (56, 1), (65, 1)] }, { coefficient := 1, powers := [(11, 1), (32, 1), (40, 1), (51, 1), (56, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (59, 1)] }, { coefficient := -1, powers := [(11, 1), (59, 1)] }, { coefficient := 1, powers := [(32, 1), (33, 1), (36, 1), (40, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1)] }, { coefficient := 1, powers := [(33, 1), (40, 1), (47, 1)] }],
  [{ coefficient := -1, powers := [(11, 1), (25, 1)] }, { coefficient := 1, powers := [(28, 1)] }],
  [{ coefficient := -1, powers := [(11, 1), (17, 1)] }, { coefficient := 1, powers := [(19, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (31, 1), (32, 1), (40, 1), (56, 1), (65, 1)] }, { coefficient := 1, powers := [(11, 1), (31, 1), (32, 1), (40, 1), (56, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (15, 1), (32, 1), (40, 1), (56, 1), (65, 1)] }, { coefficient := 1, powers := [(11, 1), (15, 1), (32, 1), (40, 1), (56, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (32, 1), (40, 1), (57, 1), (65, 1)] }, { coefficient := 1, powers := [(11, 1), (32, 1), (40, 1), (57, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (26, 1), (34, 1), (40, 1), (56, 1), (65, 1)] }, { coefficient := 1, powers := [(3, 1), (31, 1), (32, 1), (40, 1), (51, 1), (56, 1), (65, 1)] }, { coefficient := -1, powers := [(11, 1), (26, 1), (34, 1), (40, 1), (56, 1), (65, 1)] }, { coefficient := -1, powers := [(11, 1), (31, 1), (32, 1), (40, 1), (51, 1), (56, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (34, 1), (40, 1), (56, 1), (65, 1)] }, { coefficient := 1, powers := [(11, 1), (34, 1), (40, 1), (56, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(33, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(11, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(3, 1), (32, 1), (40, 1), (56, 1), (65, 1)] }, { coefficient := -1, powers := [(11, 1), (32, 1), (40, 1), (56, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (25, 1), (53, 1), (59, 1), (67, 1)] }, { coefficient := -1, powers := [(3, 1), (26, 1), (34, 1), (40, 1), (54, 1), (56, 1), (65, 1), (67, 1)] }, { coefficient := -1, powers := [(3, 1), (31, 1), (32, 1), (40, 1), (51, 1), (54, 1), (56, 1), (65, 1), (67, 1)] }, { coefficient := -1, powers := [(3, 1), (32, 1), (40, 1), (54, 1), (56, 1), (65, 1), (69, 1)] }, { coefficient := -1, powers := [(3, 1), (53, 1), (67, 1), (68, 1)] }, { coefficient := -1, powers := [(11, 1), (25, 1), (53, 1), (59, 1), (67, 1)] }, { coefficient := 1, powers := [(11, 1), (26, 1), (34, 1), (40, 1), (54, 1), (56, 1), (65, 1), (67, 1)] }, { coefficient := 1, powers := [(11, 1), (31, 1), (32, 1), (40, 1), (51, 1), (54, 1), (56, 1), (65, 1), (67, 1)] }, { coefficient := 1, powers := [(11, 1), (32, 1), (40, 1), (54, 1), (56, 1), (65, 1), (69, 1)] }, { coefficient := 1, powers := [(11, 1), (53, 1), (67, 1), (68, 1)] }, { coefficient := 1, powers := [(25, 1), (32, 1), (33, 1), (36, 1), (40, 1), (53, 1), (67, 1)] }, { coefficient := 1, powers := [(25, 1), (33, 1), (36, 1), (53, 1), (67, 1)] }, { coefficient := -1, powers := [(32, 1), (33, 1), (40, 1), (42, 1), (53, 1), (67, 1)] }, { coefficient := -1, powers := [(33, 1), (42, 1), (53, 1), (67, 1)] }]
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

#print axioms Krenn.X5Case64Tree.LeafB2.selectedHasNoCommonZero

end Krenn.X5Case64Tree.LeafB2
