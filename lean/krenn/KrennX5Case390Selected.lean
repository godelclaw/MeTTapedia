import KrennSparseCertificate

/-! Selected core of a strict exact certificate over a frozen system. -/

namespace Krenn.X5Case390Selected

open Krenn.SparseCertificate
open MvPolynomial

def sourceSystemFileSHA256 : String := "70c8bf0f5e2c58e57bb7be9f1059255521e9da7ad52a38e813be33ed1e41fefc"
def sourceSystemSemanticSHA256 : String := "c261d8f66595e94450e81bbe845f1157fb73a503971f5d9b8b63af01df7c73ba"
def certificateSHA256 : String := "6e36afd115c8c5a2522d9ddc75155e29d1f04274761faaf9cb7119033908b277"
def sourceEquationCount : Nat := 675

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedIndices : Fin 30 → Fin 675 := ![
  0,
  2,
  18,
  23,
  25,
  27,
  29,
  33,
  35,
  45,
  361,
  416,
  420,
  422,
  423,
  424,
  426,
  440,
  509,
  527,
  535,
  580,
  612,
  625,
  661,
  663,
  664,
  666,
  673,
  674
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 30 → SparsePoly (Fin 70) := ![
  [{ coefficient := 1, powers := [(57, 1)] }],
  [{ coefficient := 1, powers := [(62, 1)] }],
  [{ coefficient := 1, powers := [(26, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(31, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(36, 1), (69, 1)] }],
  [{ coefficient := 1, powers := [(37, 1), (68, 1)] }],
  [{ coefficient := 1, powers := [(38, 1), (68, 1)] }],
  [{ coefficient := 1, powers := [(42, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(43, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(48, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (54, 1), (68, 1)] }, { coefficient := 1, powers := [(54, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (63, 1)] }, { coefficient := 1, powers := [(21, 1), (57, 1)] }, { coefficient := 1, powers := [(29, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (57, 1)] }, { coefficient := 1, powers := [(26, 1), (54, 1)] }, { coefficient := 1, powers := [(63, 1)] }],
  [{ coefficient := 1, powers := [(36, 1), (68, 1)] }, { coefficient := 1, powers := [(42, 1), (59, 1)] }, { coefficient := 1, powers := [(47, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(37, 1), (66, 1)] }, { coefficient := 1, powers := [(40, 1), (60, 1)] }, { coefficient := 1, powers := [(51, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(37, 1), (69, 1)] }, { coefficient := 1, powers := [(43, 1), (60, 1)] }, { coefficient := 1, powers := [(51, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(39, 1), (68, 1)] }, { coefficient := 1, powers := [(42, 1), (65, 1)] }, { coefficient := 1, powers := [(47, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (53, 1), (69, 1)] }, { coefficient := 1, powers := [(31, 1), (51, 1), (53, 1)] }, { coefficient := 1, powers := [(34, 1), (43, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (38, 1), (68, 1)] }, { coefficient := 1, powers := [(38, 1), (59, 1)] }, { coefficient := 1, powers := [(56, 1)] }],
  [{ coefficient := 1, powers := [(15, 1), (50, 1), (62, 1)] }, { coefficient := 1, powers := [(22, 1), (37, 1), (68, 1)] }, { coefficient := 1, powers := [(37, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (48, 1), (57, 1)] }, { coefficient := 1, powers := [(26, 1), (39, 1), (60, 1)] }, { coefficient := 1, powers := [(39, 1), (69, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (57, 1), (65, 1)] }, { coefficient := 1, powers := [(17, 1), (50, 1), (57, 1)] }, { coefficient := 1, powers := [(26, 1), (37, 1), (65, 1)] }, { coefficient := 1, powers := [(43, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (60, 1), (62, 1)] }, { coefficient := 1, powers := [(15, 1), (48, 1), (62, 1)] }, { coefficient := 1, powers := [(22, 1), (42, 1), (60, 1)] }, { coefficient := 1, powers := [(39, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (39, 1), (69, 1)] }, { coefficient := 1, powers := [(17, 1), (36, 1), (69, 1)] }, { coefficient := 1, powers := [(26, 1), (48, 1), (53, 1)] }, { coefficient := 1, powers := [(53, 1), (69, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (50, 1), (63, 1)] }, { coefficient := 1, powers := [(21, 1), (50, 1), (57, 1)] }, { coefficient := 1, powers := [(29, 1), (50, 1), (54, 1)] }, { coefficient := 1, powers := [(33, 1), (37, 1), (63, 1)] }, { coefficient := 1, powers := [(33, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(33, 1), (43, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (48, 1), (62, 1)] }, { coefficient := 1, powers := [(22, 1), (48, 1), (56, 1)] }, { coefficient := 1, powers := [(34, 1), (36, 1), (62, 1)] }, { coefficient := 1, powers := [(34, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(34, 1), (42, 1), (53, 1)] }, { coefficient := 1, powers := [(48, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (48, 1), (57, 1)] }, { coefficient := 1, powers := [(26, 1), (48, 1), (54, 1)] }, { coefficient := 1, powers := [(48, 1), (63, 1)] }, { coefficient := 1, powers := [(54, 1), (69, 1)] }, { coefficient := 1, powers := [(57, 1), (66, 1)] }, { coefficient := 1, powers := [(60, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (54, 1), (69, 1)] }, { coefficient := 1, powers := [(1, 1), (57, 1), (66, 1)] }, { coefficient := 1, powers := [(1, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(18, 1), (37, 1), (69, 1)] }, { coefficient := 1, powers := [(18, 1), (43, 1), (60, 1)] }, { coefficient := 1, powers := [(18, 1), (51, 1), (57, 1)] }, { coefficient := 1, powers := [(26, 1), (37, 1), (66, 1)] }, { coefficient := 1, powers := [(26, 1), (40, 1), (60, 1)] }, { coefficient := 1, powers := [(26, 1), (51, 1), (54, 1)] }, { coefficient := 1, powers := [(40, 1), (69, 1)] }, { coefficient := 1, powers := [(43, 1), (66, 1)] }, { coefficient := 1, powers := [(51, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (53, 1), (68, 1)] }, { coefficient := 1, powers := [(3, 1), (56, 1), (65, 1)] }, { coefficient := 1, powers := [(3, 1), (59, 1), (62, 1)] }, { coefficient := 1, powers := [(11, 1), (39, 1), (68, 1)] }, { coefficient := 1, powers := [(11, 1), (42, 1), (65, 1)] }, { coefficient := 1, powers := [(11, 1), (47, 1), (62, 1)] }, { coefficient := 1, powers := [(20, 1), (36, 1), (68, 1)] }, { coefficient := 1, powers := [(20, 1), (42, 1), (59, 1)] }, { coefficient := 1, powers := [(20, 1), (47, 1), (56, 1)] }, { coefficient := 1, powers := [(28, 1), (36, 1), (65, 1)] }, { coefficient := 1, powers := [(28, 1), (39, 1), (59, 1)] }, { coefficient := 1, powers := [(28, 1), (47, 1), (53, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1), (62, 1)] }, { coefficient := 1, powers := [(33, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(33, 1), (42, 1), (53, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(7, 1), (54, 1), (69, 1)] }, { coefficient := 1, powers := [(7, 1), (57, 1), (66, 1)] }, { coefficient := 1, powers := [(7, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(15, 1), (40, 1), (69, 1)] }, { coefficient := 1, powers := [(15, 1), (43, 1), (66, 1)] }, { coefficient := 1, powers := [(15, 1), (51, 1), (63, 1)] }, { coefficient := 1, powers := [(23, 1), (37, 1), (69, 1)] }, { coefficient := 1, powers := [(23, 1), (43, 1), (60, 1)] }, { coefficient := 1, powers := [(23, 1), (51, 1), (57, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1), (66, 1)] }, { coefficient := 1, powers := [(31, 1), (40, 1), (60, 1)] }, { coefficient := 1, powers := [(31, 1), (51, 1), (54, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1), (63, 1)] }, { coefficient := 1, powers := [(34, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(34, 1), (43, 1), (54, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 30 → SparsePoly (Fin 70) := ![
  [{ coefficient := -1, powers := [(1, 1), (28, 1), (34, 1), (36, 1), (54, 1), (65, 1)] }, { coefficient := -1, powers := [(3, 1), (7, 1), (9, 1), (17, 1), (48, 1), (54, 1), (68, 1)] }, { coefficient := -1, powers := [(5, 1), (18, 1), (34, 1), (37, 1), (68, 1)] }, { coefficient := -1, powers := [(7, 1), (9, 1), (17, 1), (28, 1), (47, 1), (48, 1), (54, 1)] }, { coefficient := -1, powers := [(17, 1), (28, 1), (34, 1), (36, 1), (50, 1), (54, 1)] }, { coefficient := -1, powers := [(18, 1), (34, 1), (37, 1)] }, { coefficient := 1, powers := [(34, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (6, 1), (7, 1), (9, 1), (26, 1), (54, 1), (60, 1), (68, 1)] }, { coefficient := 1, powers := [(3, 1), (7, 1), (9, 1), (15, 1), (26, 1), (48, 1), (54, 1), (68, 1)] }, { coefficient := 1, powers := [(3, 1), (34, 1), (43, 1), (54, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (7, 1), (9, 1), (26, 1), (28, 1), (47, 1), (54, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (9, 1), (15, 1), (26, 1), (28, 1), (47, 1), (48, 1), (54, 1)] }, { coefficient := -1, powers := [(14, 1), (33, 1), (43, 1), (48, 1), (54, 1)] }, { coefficient := 1, powers := [(15, 1), (26, 1), (28, 1), (34, 1), (36, 1), (50, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (7, 1), (48, 1), (54, 1), (68, 1)] }, { coefficient := 1, powers := [(7, 1), (28, 1), (47, 1), (48, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (51, 1), (54, 1), (68, 1)] }, { coefficient := -1, powers := [(28, 1), (47, 1), (51, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (7, 1), (17, 1), (54, 1), (68, 1)] }, { coefficient := 1, powers := [(7, 1), (17, 1), (28, 1), (47, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (34, 1), (63, 1)] }, { coefficient := 1, powers := [(22, 1), (26, 1), (28, 1), (34, 1), (36, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (14, 1), (34, 1), (43, 1), (54, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (7, 1), (9, 1), (22, 1), (26, 1), (54, 1), (68, 1)] }, { coefficient := 1, powers := [(7, 1), (9, 1), (22, 1), (26, 1), (28, 1), (47, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (34, 1), (38, 1), (54, 1), (65, 1)] }, { coefficient := 1, powers := [(28, 1), (34, 1), (39, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(22, 1), (33, 1), (43, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(26, 1), (34, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(34, 1), (43, 1), (48, 1), (50, 1), (53, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(1, 1), (15, 1), (33, 1), (43, 1), (48, 2), (53, 1), (54, 1)] }, { coefficient := 1, powers := [(1, 1), (15, 1), (48, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (37, 1), (68, 1)] }, { coefficient := 1, powers := [(7, 1), (33, 1), (43, 1), (48, 2), (53, 1), (54, 1)] }, { coefficient := -1, powers := [(7, 1), (48, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (34, 1), (43, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(15, 1), (26, 1), (33, 1), (43, 1), (48, 1), (53, 1), (54, 1)] }, { coefficient := -1, powers := [(15, 1), (26, 1)] }, { coefficient := -1, powers := [(31, 1), (33, 1), (43, 1), (48, 1), (53, 1), (54, 1)] }, { coefficient := 1, powers := [(31, 1)] }],
  [{ coefficient := 1, powers := [(15, 1), (18, 1), (33, 1), (43, 1), (48, 1), (53, 1), (54, 1)] }, { coefficient := -1, powers := [(15, 1), (18, 1)] }, { coefficient := -1, powers := [(23, 1), (33, 1), (43, 1), (48, 1), (53, 1), (54, 1)] }, { coefficient := 1, powers := [(23, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (34, 1), (43, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (54, 1), (68, 1)] }, { coefficient := 1, powers := [(28, 1), (47, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (34, 1), (43, 1), (54, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(26, 1), (28, 1), (34, 1), (36, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (7, 1), (9, 1), (54, 1), (68, 1)] }, { coefficient := 1, powers := [(7, 1), (9, 1), (28, 1), (47, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(28, 1), (34, 1), (36, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (7, 1), (9, 1), (26, 1), (54, 1), (68, 1)] }, { coefficient := -1, powers := [(7, 1), (9, 1), (26, 1), (28, 1), (47, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (7, 1), (54, 1), (68, 1)] }, { coefficient := -1, powers := [(7, 1), (28, 1), (47, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(34, 1), (43, 1), (48, 1), (53, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(33, 1), (43, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (15, 1), (33, 1), (43, 1), (48, 1), (53, 1), (54, 1)] }, { coefficient := -1, powers := [(1, 1), (15, 1)] }, { coefficient := -1, powers := [(7, 1), (33, 1), (43, 1), (48, 1), (53, 1), (54, 1)] }, { coefficient := 1, powers := [(7, 1)] }],
  [{ coefficient := -1, powers := [(15, 1), (33, 1), (43, 1), (48, 1), (53, 1), (54, 1)] }, { coefficient := 1, powers := [(15, 1)] }],
  [{ coefficient := -1, powers := [(34, 1), (43, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(33, 1), (43, 1), (48, 1), (53, 1), (54, 1)] }, { coefficient := -1, powers := [] }]
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
    ¬ ∀ index : Fin 30,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.X5Case390Selected.selectedHasNoCommonZero

end Krenn.X5Case390Selected
