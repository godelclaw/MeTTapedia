import KrennSparseCertificate

/-! Selected core of a strict exact certificate over a frozen system. -/

namespace Krenn.X5Case68Selected

open Krenn.SparseCertificate
open MvPolynomial

def sourceSystemFileSHA256 : String := "13f0c47dd38487d09301a7eab39a08d58d7b29788ff695cdc13b0bc8e404d830"
def sourceSystemSemanticSHA256 : String := "252db32f8fc52f6aa687acec45c33e8299667a22dd5ace9e360a21ceaf017b39"
def certificateSHA256 : String := "621866633fb53b2ce37b659ae535ef4d59340071ec5237492425c7b1d2a4f404"
def sourceEquationCount : Nat := 675

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedIndices : Fin 17 → Fin 675 := ![
  0,
  1,
  52,
  53,
  411,
  414,
  420,
  421,
  422,
  424,
  425,
  426,
  660,
  661,
  666,
  672,
  674
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 17 → SparsePoly (Fin 70) := ![
  [{ coefficient := 1, powers := [(54, 1)] }],
  [{ coefficient := 1, powers := [(55, 1)] }],
  [{ coefficient := 1, powers := [(51, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(51, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(32, 1), (36, 1), (63, 1)] }, { coefficient := 1, powers := [(63, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (63, 1)] }, { coefficient := 1, powers := [(26, 1), (54, 1)] }, { coefficient := 1, powers := [(57, 1)] }],
  [{ coefficient := 1, powers := [(15, 1), (63, 1)] }, { coefficient := 1, powers := [(23, 1), (57, 1)] }, { coefficient := 1, powers := [(31, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(35, 1), (64, 1)] }, { coefficient := 1, powers := [(38, 1), (58, 1)] }, { coefficient := 1, powers := [(44, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(35, 1), (67, 1)] }, { coefficient := 1, powers := [(41, 1), (58, 1)] }, { coefficient := 1, powers := [(44, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(37, 1), (66, 1)] }, { coefficient := 1, powers := [(40, 1), (60, 1)] }, { coefficient := 1, powers := [(51, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(38, 1), (67, 1)] }, { coefficient := 1, powers := [(41, 1), (64, 1)] }, { coefficient := 1, powers := [(44, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(40, 1), (69, 1)] }, { coefficient := 1, powers := [(43, 1), (66, 1)] }, { coefficient := 1, powers := [(51, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (48, 1), (63, 1)] }, { coefficient := 1, powers := [(26, 1), (48, 1), (54, 1)] }, { coefficient := 1, powers := [(48, 1), (57, 1)] }, { coefficient := 1, powers := [(54, 1), (69, 1)] }, { coefficient := 1, powers := [(57, 1), (66, 1)] }, { coefficient := 1, powers := [(60, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (49, 1), (63, 1)] }, { coefficient := 1, powers := [(26, 1), (49, 1), (54, 1)] }, { coefficient := 1, powers := [(32, 1), (37, 1), (63, 1)] }, { coefficient := 1, powers := [(32, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(32, 1), (43, 1), (54, 1)] }, { coefficient := 1, powers := [(49, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (54, 1), (69, 1)] }, { coefficient := 1, powers := [(1, 1), (57, 1), (66, 1)] }, { coefficient := 1, powers := [(1, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(9, 1), (40, 1), (69, 1)] }, { coefficient := 1, powers := [(9, 1), (43, 1), (66, 1)] }, { coefficient := 1, powers := [(9, 1), (51, 1), (63, 1)] }, { coefficient := 1, powers := [(26, 1), (37, 1), (66, 1)] }, { coefficient := 1, powers := [(26, 1), (40, 1), (60, 1)] }, { coefficient := 1, powers := [(26, 1), (51, 1), (54, 1)] }, { coefficient := 1, powers := [(37, 1), (69, 1)] }, { coefficient := 1, powers := [(43, 1), (60, 1)] }, { coefficient := 1, powers := [(51, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (52, 1), (67, 1)] }, { coefficient := 1, powers := [(0, 1), (55, 1), (64, 1)] }, { coefficient := 1, powers := [(0, 1), (58, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (38, 1), (67, 1)] }, { coefficient := 1, powers := [(8, 1), (41, 1), (64, 1)] }, { coefficient := 1, powers := [(8, 1), (44, 1), (61, 1)] }, { coefficient := 1, powers := [(16, 1), (35, 1), (67, 1)] }, { coefficient := 1, powers := [(16, 1), (41, 1), (58, 1)] }, { coefficient := 1, powers := [(16, 1), (44, 1), (55, 1)] }, { coefficient := 1, powers := [(24, 1), (35, 1), (64, 1)] }, { coefficient := 1, powers := [(24, 1), (38, 1), (58, 1)] }, { coefficient := 1, powers := [(24, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(32, 1), (35, 1), (61, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1), (55, 1)] }, { coefficient := 1, powers := [(32, 1), (41, 1), (52, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(7, 1), (54, 1), (69, 1)] }, { coefficient := 1, powers := [(7, 1), (57, 1), (66, 1)] }, { coefficient := 1, powers := [(7, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(15, 1), (40, 1), (69, 1)] }, { coefficient := 1, powers := [(15, 1), (43, 1), (66, 1)] }, { coefficient := 1, powers := [(15, 1), (51, 1), (63, 1)] }, { coefficient := 1, powers := [(23, 1), (37, 1), (69, 1)] }, { coefficient := 1, powers := [(23, 1), (43, 1), (60, 1)] }, { coefficient := 1, powers := [(23, 1), (51, 1), (57, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1), (66, 1)] }, { coefficient := 1, powers := [(31, 1), (40, 1), (60, 1)] }, { coefficient := 1, powers := [(31, 1), (51, 1), (54, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1), (63, 1)] }, { coefficient := 1, powers := [(34, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(34, 1), (43, 1), (54, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 17 → SparsePoly (Fin 70) := ![
  [{ coefficient := -1, powers := [(26, 1), (32, 1), (34, 1), (36, 1), (40, 1)] }, { coefficient := -1, powers := [(26, 1), (34, 1), (40, 1)] }, { coefficient := -1, powers := [(31, 1), (51, 1)] }, { coefficient := 1, powers := [(32, 1), (34, 1), (36, 1), (43, 1)] }, { coefficient := 1, powers := [(34, 1), (43, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (15, 1), (51, 1), (63, 1), (64, 1)] }, { coefficient := -1, powers := [(0, 1), (23, 1), (51, 1), (57, 1), (64, 1)] }, { coefficient := -1, powers := [(15, 1), (32, 1), (38, 1), (51, 1), (63, 1)] }, { coefficient := -1, powers := [(23, 1), (32, 1), (38, 1), (51, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (15, 1), (63, 1), (67, 1)] }, { coefficient := -1, powers := [(0, 1), (23, 1), (57, 1), (67, 1)] }, { coefficient := -1, powers := [(15, 1), (32, 1), (41, 1), (63, 1)] }, { coefficient := -1, powers := [(23, 1), (32, 1), (41, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (15, 1), (58, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (23, 1), (57, 1), (58, 1)] }, { coefficient := -1, powers := [(15, 1), (32, 1), (35, 1), (63, 1)] }, { coefficient := -1, powers := [(23, 1), (32, 1), (35, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [(9, 1), (34, 1), (40, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (23, 1), (48, 1)] }, { coefficient := -1, powers := [(7, 1), (48, 1)] }, { coefficient := 1, powers := [(32, 1), (34, 1), (36, 1), (40, 1)] }, { coefficient := 1, powers := [(34, 1), (36, 1), (49, 1)] }, { coefficient := 1, powers := [(34, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(51, 1)] }],
  [{ coefficient := -1, powers := [(15, 1), (24, 1), (51, 1), (63, 1)] }, { coefficient := -1, powers := [(23, 1), (24, 1), (51, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [(15, 1), (16, 1), (51, 1), (63, 1)] }, { coefficient := -1, powers := [(16, 1), (23, 1), (51, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [(23, 1), (26, 1)] }, { coefficient := 1, powers := [(31, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (15, 1), (51, 1), (63, 1)] }, { coefficient := -1, powers := [(8, 1), (23, 1), (51, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [(9, 1), (23, 1)] }, { coefficient := 1, powers := [(15, 1)] }],
  [{ coefficient := -1, powers := [(1, 1), (23, 1)] }, { coefficient := 1, powers := [(7, 1)] }],
  [{ coefficient := -1, powers := [(34, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(23, 1)] }],
  [{ coefficient := 1, powers := [(15, 1), (51, 1), (63, 1)] }, { coefficient := 1, powers := [(23, 1), (51, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [] }]
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
    ¬ ∀ index : Fin 17,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.X5Case68Selected.selectedHasNoCommonZero

end Krenn.X5Case68Selected
