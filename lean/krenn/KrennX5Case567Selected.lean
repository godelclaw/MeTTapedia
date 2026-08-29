import KrennSparseCertificate

/-! Selected core of a strict exact certificate over a frozen system. -/

namespace Krenn.X5Case567Selected

open Krenn.SparseCertificate
open MvPolynomial

def sourceSystemFileSHA256 : String := "64730f2c543dfd44613b134405a3d71e9f7334478edc4b9a6459b67036eb7231"
def sourceSystemSemanticSHA256 : String := "b7476cf412072f8535a7ee5dc0ed2dadfbd1264c6e7820f1da1ddb2f06bf4b3a"
def certificateSHA256 : String := "cb3d78ba5ad4e59228c3062572134a1730d3b6ea27fca66bc0f8712678645b51"
def sourceEquationCount : Nat := 675

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedIndices : Fin 18 → Fin 675 := ![
  0,
  1,
  2,
  3,
  28,
  29,
  400,
  422,
  423,
  424,
  425,
  426,
  436,
  467,
  487,
  671,
  673,
  674
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 18 → SparsePoly (Fin 70) := ![
  [{ coefficient := 1, powers := [(53, 1)] }],
  [{ coefficient := 1, powers := [(54, 1)] }],
  [{ coefficient := 1, powers := [(62, 1)] }],
  [{ coefficient := 1, powers := [(63, 1)] }],
  [{ coefficient := 1, powers := [(39, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(39, 1), (69, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (48, 1), (57, 1)] }, { coefficient := 1, powers := [(57, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(36, 1), (65, 1)] }, { coefficient := 1, powers := [(39, 1), (59, 1)] }, { coefficient := 1, powers := [(48, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(36, 1), (68, 1)] }, { coefficient := 1, powers := [(42, 1), (59, 1)] }, { coefficient := 1, powers := [(48, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(37, 1), (66, 1)] }, { coefficient := 1, powers := [(40, 1), (60, 1)] }, { coefficient := 1, powers := [(51, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(39, 1), (68, 1)] }, { coefficient := 1, powers := [(42, 1), (65, 1)] }, { coefficient := 1, powers := [(48, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(40, 1), (69, 1)] }, { coefficient := 1, powers := [(43, 1), (66, 1)] }, { coefficient := 1, powers := [(51, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (57, 1), (65, 1)] }, { coefficient := 1, powers := [(20, 1), (48, 1), (57, 1)] }, { coefficient := 1, powers := [(33, 1), (39, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (39, 1), (69, 1)] }, { coefficient := 1, powers := [(17, 1), (57, 1)] }, { coefficient := 1, powers := [(26, 1), (39, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (39, 1), (69, 1)] }, { coefficient := 1, powers := [(20, 1), (57, 1)] }, { coefficient := 1, powers := [(29, 1), (39, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (39, 1), (68, 1)] }, { coefficient := 1, powers := [(9, 1), (42, 1), (65, 1)] }, { coefficient := 1, powers := [(9, 1), (48, 1), (62, 1)] }, { coefficient := 1, powers := [(17, 1), (36, 1), (68, 1)] }, { coefficient := 1, powers := [(17, 1), (42, 1), (59, 1)] }, { coefficient := 1, powers := [(17, 1), (48, 1), (56, 1)] }, { coefficient := 1, powers := [(25, 1), (36, 1), (65, 1)] }, { coefficient := 1, powers := [(25, 1), (39, 1), (59, 1)] }, { coefficient := 1, powers := [(25, 1), (48, 1), (53, 1)] }, { coefficient := 1, powers := [(53, 1), (68, 1)] }, { coefficient := 1, powers := [(56, 1), (65, 1)] }, { coefficient := 1, powers := [(59, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (53, 1), (68, 1)] }, { coefficient := 1, powers := [(3, 1), (56, 1), (65, 1)] }, { coefficient := 1, powers := [(3, 1), (59, 1), (62, 1)] }, { coefficient := 1, powers := [(11, 1), (39, 1), (68, 1)] }, { coefficient := 1, powers := [(11, 1), (42, 1), (65, 1)] }, { coefficient := 1, powers := [(11, 1), (48, 1), (62, 1)] }, { coefficient := 1, powers := [(20, 1), (36, 1), (68, 1)] }, { coefficient := 1, powers := [(20, 1), (42, 1), (59, 1)] }, { coefficient := 1, powers := [(20, 1), (48, 1), (56, 1)] }, { coefficient := 1, powers := [(28, 1), (36, 1), (65, 1)] }, { coefficient := 1, powers := [(28, 1), (39, 1), (59, 1)] }, { coefficient := 1, powers := [(28, 1), (48, 1), (53, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1), (62, 1)] }, { coefficient := 1, powers := [(33, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(33, 1), (42, 1), (53, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(7, 1), (54, 1), (69, 1)] }, { coefficient := 1, powers := [(7, 1), (57, 1), (66, 1)] }, { coefficient := 1, powers := [(7, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(15, 1), (40, 1), (69, 1)] }, { coefficient := 1, powers := [(15, 1), (43, 1), (66, 1)] }, { coefficient := 1, powers := [(15, 1), (51, 1), (63, 1)] }, { coefficient := 1, powers := [(23, 1), (37, 1), (69, 1)] }, { coefficient := 1, powers := [(23, 1), (43, 1), (60, 1)] }, { coefficient := 1, powers := [(23, 1), (51, 1), (57, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1), (66, 1)] }, { coefficient := 1, powers := [(31, 1), (40, 1), (60, 1)] }, { coefficient := 1, powers := [(31, 1), (51, 1), (54, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1), (63, 1)] }, { coefficient := 1, powers := [(34, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(34, 1), (43, 1), (54, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 18 → SparsePoly (Fin 70) := ![
  [{ coefficient := 1, powers := [(7, 1), (33, 1), (42, 1), (57, 1), (66, 1)] }, { coefficient := 1, powers := [(23, 1), (33, 1), (37, 1), (42, 1), (69, 1)] }, { coefficient := 1, powers := [(23, 1), (33, 1), (42, 1), (43, 1), (60, 1)] }, { coefficient := 1, powers := [(23, 1), (33, 1), (42, 1), (51, 1), (57, 1)] }, { coefficient := 1, powers := [(33, 1), (34, 1), (40, 1), (42, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (69, 1)] }, { coefficient := 1, powers := [(34, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (33, 1), (36, 1), (57, 1), (66, 1)] }, { coefficient := 1, powers := [(23, 1), (33, 1), (36, 1), (37, 1), (69, 1)] }, { coefficient := 1, powers := [(23, 1), (33, 1), (36, 1), (43, 1), (60, 1)] }, { coefficient := 1, powers := [(23, 1), (33, 1), (36, 1), (51, 1), (57, 1)] }, { coefficient := 1, powers := [(33, 1), (34, 1), (36, 1), (40, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (60, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (7, 1), (26, 1), (48, 1), (56, 1), (66, 1)] }, { coefficient := -1, powers := [(3, 1), (23, 1), (26, 1), (48, 1), (51, 1), (56, 1)] }, { coefficient := -1, powers := [(3, 1), (26, 1), (34, 1), (40, 1), (48, 1), (56, 1)] }, { coefficient := 1, powers := [(7, 1), (29, 1), (48, 1), (56, 1), (66, 1)] }, { coefficient := 1, powers := [(23, 1), (29, 1), (48, 1), (51, 1), (56, 1)] }, { coefficient := 1, powers := [(23, 1), (33, 1), (43, 1), (56, 1)] }, { coefficient := 1, powers := [(29, 1), (34, 1), (40, 1), (48, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (7, 1), (10, 1), (48, 1), (56, 1), (66, 1)] }, { coefficient := -1, powers := [(3, 1), (10, 1), (23, 1), (48, 1), (51, 1), (56, 1)] }, { coefficient := -1, powers := [(3, 1), (10, 1), (34, 1), (40, 1), (48, 1), (56, 1)] }, { coefficient := 1, powers := [(7, 1), (12, 1), (48, 1), (56, 1), (66, 1)] }, { coefficient := 1, powers := [(12, 1), (23, 1), (48, 1), (51, 1), (56, 1)] }, { coefficient := 1, powers := [(12, 1), (34, 1), (40, 1), (48, 1), (56, 1)] }, { coefficient := 1, powers := [(23, 1), (33, 1), (37, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (7, 1), (56, 1), (66, 1)] }, { coefficient := -1, powers := [(3, 1), (23, 1), (51, 1), (56, 1)] }, { coefficient := -1, powers := [(3, 1), (34, 1), (40, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (7, 1), (25, 1), (57, 1), (66, 1)] }, { coefficient := -1, powers := [(3, 1), (23, 1), (25, 1), (37, 1), (69, 1)] }, { coefficient := -1, powers := [(3, 1), (23, 1), (25, 1), (43, 1), (60, 1)] }, { coefficient := -1, powers := [(3, 1), (23, 1), (25, 1), (51, 1), (57, 1)] }, { coefficient := -1, powers := [(3, 1), (25, 1), (34, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(7, 1), (28, 1), (57, 1), (66, 1)] }, { coefficient := 1, powers := [(23, 1), (28, 1), (37, 1), (69, 1)] }, { coefficient := 1, powers := [(23, 1), (28, 1), (43, 1), (60, 1)] }, { coefficient := 1, powers := [(23, 1), (28, 1), (51, 1), (57, 1)] }, { coefficient := 1, powers := [(28, 1), (34, 1), (40, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (7, 1), (17, 1), (57, 1), (66, 1)] }, { coefficient := -1, powers := [(3, 1), (17, 1), (23, 1), (37, 1), (69, 1)] }, { coefficient := -1, powers := [(3, 1), (17, 1), (23, 1), (43, 1), (60, 1)] }, { coefficient := -1, powers := [(3, 1), (17, 1), (23, 1), (51, 1), (57, 1)] }, { coefficient := -1, powers := [(3, 1), (17, 1), (34, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(7, 1), (20, 1), (57, 1), (66, 1)] }, { coefficient := 1, powers := [(20, 1), (23, 1), (37, 1), (69, 1)] }, { coefficient := 1, powers := [(20, 1), (23, 1), (43, 1), (60, 1)] }, { coefficient := 1, powers := [(20, 1), (23, 1), (51, 1), (57, 1)] }, { coefficient := 1, powers := [(20, 1), (34, 1), (40, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(31, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (7, 1), (9, 1), (57, 1), (66, 1)] }, { coefficient := -1, powers := [(3, 1), (9, 1), (23, 1), (37, 1), (69, 1)] }, { coefficient := -1, powers := [(3, 1), (9, 1), (23, 1), (43, 1), (60, 1)] }, { coefficient := -1, powers := [(3, 1), (9, 1), (23, 1), (51, 1), (57, 1)] }, { coefficient := -1, powers := [(3, 1), (9, 1), (34, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(7, 1), (11, 1), (57, 1), (66, 1)] }, { coefficient := 1, powers := [(11, 1), (23, 1), (37, 1), (69, 1)] }, { coefficient := 1, powers := [(11, 1), (23, 1), (43, 1), (60, 1)] }, { coefficient := 1, powers := [(11, 1), (23, 1), (51, 1), (57, 1)] }, { coefficient := 1, powers := [(11, 1), (34, 1), (40, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(15, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (56, 1), (66, 1)] }, { coefficient := 1, powers := [(23, 1), (51, 1), (56, 1)] }, { coefficient := 1, powers := [(34, 1), (40, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (7, 1), (48, 1), (56, 1), (66, 1)] }, { coefficient := 1, powers := [(3, 1), (23, 1), (48, 1), (51, 1), (56, 1)] }, { coefficient := 1, powers := [(3, 1), (34, 1), (40, 1), (48, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (48, 1), (56, 1), (66, 1)] }, { coefficient := -1, powers := [(23, 1), (48, 1), (51, 1), (56, 1)] }, { coefficient := -1, powers := [(34, 1), (40, 1), (48, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (7, 1), (57, 1), (66, 1)] }, { coefficient := 1, powers := [(3, 1), (23, 1), (37, 1), (69, 1)] }, { coefficient := 1, powers := [(3, 1), (23, 1), (43, 1), (60, 1)] }, { coefficient := 1, powers := [(3, 1), (23, 1), (51, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (34, 1), (40, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (57, 1), (66, 1)] }, { coefficient := -1, powers := [(23, 1), (37, 1), (69, 1)] }, { coefficient := -1, powers := [(23, 1), (43, 1), (60, 1)] }, { coefficient := -1, powers := [(23, 1), (51, 1), (57, 1)] }, { coefficient := -1, powers := [(34, 1), (40, 1), (57, 1)] }],
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
    ¬ ∀ index : Fin 18,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.X5Case567Selected.selectedHasNoCommonZero

end Krenn.X5Case567Selected
