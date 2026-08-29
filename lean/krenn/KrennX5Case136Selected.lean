import KrennSparseCertificate

/-! Selected core of a strict exact certificate over a frozen system. -/

namespace Krenn.X5Case136Selected

open Krenn.SparseCertificate
open MvPolynomial

def sourceSystemFileSHA256 : String := "744bc60961810047260f8373e7cf9f280c134a2baea5050bd09bd34b1de11669"
def sourceSystemSemanticSHA256 : String := "9838aca3957a68b8f2d76d9b8b2d25cb4d775df65c9617098d0628dcc7e4bd15"
def certificateSHA256 : String := "5de1932bcdb5e2b7bf874ff09c0ca4c21f33a8cd47b83ed45ddb2f530e135dd3"
def sourceEquationCount : Nat := 675

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedIndices : Fin 22 → Fin 675 := ![
  0,
  2,
  17,
  20,
  23,
  45,
  48,
  52,
  406,
  416,
  419,
  420,
  422,
  423,
  424,
  426,
  434,
  660,
  668,
  671,
  673,
  674
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 22 → SparsePoly (Fin 70) := ![
  [{ coefficient := 1, powers := [(56, 1)] }],
  [{ coefficient := 1, powers := [(63, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(31, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(48, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(49, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(51, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (48, 1), (54, 1)] }, { coefficient := 1, powers := [(54, 1), (68, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (63, 1)] }, { coefficient := 1, powers := [(29, 1), (54, 1)] }, { coefficient := 1, powers := [(57, 1)] }],
  [{ coefficient := 1, powers := [(15, 1), (63, 1)] }, { coefficient := 1, powers := [(23, 1), (57, 1)] }, { coefficient := 1, powers := [(31, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (56, 1)] }, { coefficient := 1, powers := [(25, 1), (53, 1)] }, { coefficient := 1, powers := [(62, 1)] }],
  [{ coefficient := 1, powers := [(36, 1), (65, 1)] }, { coefficient := 1, powers := [(39, 1), (59, 1)] }, { coefficient := 1, powers := [(48, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(36, 1), (68, 1)] }, { coefficient := 1, powers := [(42, 1), (59, 1)] }, { coefficient := 1, powers := [(48, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(37, 1), (66, 1)] }, { coefficient := 1, powers := [(40, 1), (60, 1)] }, { coefficient := 1, powers := [(51, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(40, 1), (69, 1)] }, { coefficient := 1, powers := [(43, 1), (66, 1)] }, { coefficient := 1, powers := [(51, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (54, 1), (68, 1)] }, { coefficient := 1, powers := [(28, 1), (48, 1), (54, 1)] }, { coefficient := 1, powers := [(33, 1), (42, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (49, 1), (63, 1)] }, { coefficient := 1, powers := [(18, 1), (49, 1), (57, 1)] }, { coefficient := 1, powers := [(26, 1), (49, 1), (54, 1)] }, { coefficient := 1, powers := [(54, 1), (69, 1)] }, { coefficient := 1, powers := [(57, 1), (66, 1)] }, { coefficient := 1, powers := [(60, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (54, 1), (69, 1)] }, { coefficient := 1, powers := [(4, 1), (57, 1), (66, 1)] }, { coefficient := 1, powers := [(4, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(12, 1), (40, 1), (69, 1)] }, { coefficient := 1, powers := [(12, 1), (43, 1), (66, 1)] }, { coefficient := 1, powers := [(12, 1), (51, 1), (63, 1)] }, { coefficient := 1, powers := [(29, 1), (37, 1), (66, 1)] }, { coefficient := 1, powers := [(29, 1), (40, 1), (60, 1)] }, { coefficient := 1, powers := [(29, 1), (51, 1), (54, 1)] }, { coefficient := 1, powers := [(37, 1), (69, 1)] }, { coefficient := 1, powers := [(43, 1), (60, 1)] }, { coefficient := 1, powers := [(51, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (36, 1), (68, 1)] }, { coefficient := 1, powers := [(17, 1), (42, 1), (59, 1)] }, { coefficient := 1, powers := [(17, 1), (48, 1), (56, 1)] }, { coefficient := 1, powers := [(25, 1), (36, 1), (65, 1)] }, { coefficient := 1, powers := [(25, 1), (39, 1), (59, 1)] }, { coefficient := 1, powers := [(25, 1), (48, 1), (53, 1)] }, { coefficient := 1, powers := [(39, 1), (68, 1)] }, { coefficient := 1, powers := [(42, 1), (65, 1)] }, { coefficient := 1, powers := [(48, 1), (62, 1)] }, { coefficient := 1, powers := [(53, 1), (68, 1)] }, { coefficient := 1, powers := [(56, 1), (65, 1)] }, { coefficient := 1, powers := [(59, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (53, 1), (68, 1)] }, { coefficient := 1, powers := [(3, 1), (56, 1), (65, 1)] }, { coefficient := 1, powers := [(3, 1), (59, 1), (62, 1)] }, { coefficient := 1, powers := [(11, 1), (39, 1), (68, 1)] }, { coefficient := 1, powers := [(11, 1), (42, 1), (65, 1)] }, { coefficient := 1, powers := [(11, 1), (48, 1), (62, 1)] }, { coefficient := 1, powers := [(20, 1), (36, 1), (68, 1)] }, { coefficient := 1, powers := [(20, 1), (42, 1), (59, 1)] }, { coefficient := 1, powers := [(20, 1), (48, 1), (56, 1)] }, { coefficient := 1, powers := [(28, 1), (36, 1), (65, 1)] }, { coefficient := 1, powers := [(28, 1), (39, 1), (59, 1)] }, { coefficient := 1, powers := [(28, 1), (48, 1), (53, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1), (62, 1)] }, { coefficient := 1, powers := [(33, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(33, 1), (42, 1), (53, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(7, 1), (54, 1), (69, 1)] }, { coefficient := 1, powers := [(7, 1), (57, 1), (66, 1)] }, { coefficient := 1, powers := [(7, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(15, 1), (40, 1), (69, 1)] }, { coefficient := 1, powers := [(15, 1), (43, 1), (66, 1)] }, { coefficient := 1, powers := [(15, 1), (51, 1), (63, 1)] }, { coefficient := 1, powers := [(23, 1), (37, 1), (69, 1)] }, { coefficient := 1, powers := [(23, 1), (43, 1), (60, 1)] }, { coefficient := 1, powers := [(23, 1), (51, 1), (57, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1), (66, 1)] }, { coefficient := 1, powers := [(31, 1), (40, 1), (60, 1)] }, { coefficient := 1, powers := [(31, 1), (51, 1), (54, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1), (63, 1)] }, { coefficient := 1, powers := [(34, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(34, 1), (43, 1), (54, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 22 → SparsePoly (Fin 70) := ![
  [{ coefficient := 1, powers := [(3, 1), (17, 1), (23, 1), (51, 1), (57, 1), (59, 1)] }, { coefficient := -1, powers := [(3, 1), (17, 1), (31, 1), (37, 1), (59, 1), (66, 1)] }, { coefficient := -1, powers := [(3, 1), (17, 1), (31, 1), (40, 1), (59, 1), (60, 1)] }, { coefficient := -1, powers := [(3, 1), (17, 1), (34, 1), (40, 1), (57, 1), (59, 1)] }, { coefficient := -1, powers := [(3, 1), (17, 1), (34, 1), (43, 1), (54, 1), (59, 1)] }, { coefficient := -1, powers := [(3, 1), (23, 1), (51, 1), (57, 1), (65, 1)] }, { coefficient := 1, powers := [(3, 1), (31, 1), (37, 1), (65, 1), (66, 1)] }, { coefficient := 1, powers := [(3, 1), (31, 1), (40, 1), (60, 1), (65, 1)] }, { coefficient := 1, powers := [(3, 1), (34, 1), (40, 1), (57, 1), (65, 1)] }, { coefficient := 1, powers := [(3, 1), (34, 1), (43, 1), (54, 1), (65, 1)] }, { coefficient := -1, powers := [(11, 1), (17, 1), (23, 1), (51, 1), (57, 1), (59, 1)] }, { coefficient := 1, powers := [(11, 1), (17, 1), (31, 1), (37, 1), (59, 1), (66, 1)] }, { coefficient := 1, powers := [(11, 1), (17, 1), (31, 1), (40, 1), (59, 1), (60, 1)] }, { coefficient := 1, powers := [(11, 1), (17, 1), (34, 1), (40, 1), (57, 1), (59, 1)] }, { coefficient := 1, powers := [(11, 1), (17, 1), (34, 1), (43, 1), (54, 1), (59, 1)] }, { coefficient := 1, powers := [(11, 1), (23, 1), (51, 1), (57, 1), (65, 1)] }, { coefficient := -1, powers := [(11, 1), (31, 1), (37, 1), (65, 1), (66, 1)] }, { coefficient := -1, powers := [(11, 1), (31, 1), (40, 1), (60, 1), (65, 1)] }, { coefficient := -1, powers := [(11, 1), (34, 1), (40, 1), (57, 1), (65, 1)] }, { coefficient := -1, powers := [(11, 1), (34, 1), (43, 1), (54, 1), (65, 1)] }, { coefficient := 1, powers := [(17, 1), (23, 1), (33, 1), (36, 1), (51, 1), (57, 1)] }, { coefficient := -1, powers := [(17, 1), (31, 1), (33, 1), (36, 1), (37, 1), (66, 1)] }, { coefficient := -1, powers := [(17, 1), (31, 1), (33, 1), (36, 1), (40, 1), (60, 1)] }, { coefficient := -1, powers := [(17, 1), (33, 1), (34, 1), (36, 1), (40, 1), (57, 1)] }, { coefficient := -1, powers := [(17, 1), (33, 1), (34, 1), (36, 1), (43, 1), (54, 1)] }, { coefficient := -1, powers := [(23, 1), (33, 1), (39, 1), (51, 1), (57, 1)] }, { coefficient := 1, powers := [(31, 1), (33, 1), (37, 1), (39, 1), (66, 1)] }, { coefficient := 1, powers := [(31, 1), (33, 1), (39, 1), (40, 1), (60, 1)] }, { coefficient := 1, powers := [(33, 1), (34, 1), (39, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(33, 1), (34, 1), (39, 1), (43, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (12, 1), (25, 1), (34, 1), (40, 1), (53, 1), (59, 1)] }, { coefficient := -1, powers := [(3, 1), (12, 1), (34, 1), (40, 1), (53, 1), (68, 1)] }, { coefficient := 1, powers := [(4, 1), (9, 1), (23, 1), (49, 1)] }, { coefficient := -1, powers := [(4, 1), (12, 1), (18, 1), (23, 1), (49, 1)] }, { coefficient := -1, powers := [(7, 1), (9, 1), (49, 1)] }, { coefficient := 1, powers := [(7, 1), (12, 1), (18, 1), (49, 1)] }, { coefficient := -1, powers := [(11, 1), (12, 1), (25, 1), (34, 1), (40, 1), (53, 1), (59, 1)] }, { coefficient := 1, powers := [(11, 1), (12, 1), (34, 1), (40, 1), (53, 1), (68, 1)] }, { coefficient := 1, powers := [(12, 1), (25, 1), (33, 1), (34, 1), (36, 1), (40, 1), (53, 1)] }, { coefficient := -1, powers := [(12, 1), (33, 1), (34, 1), (40, 1), (42, 1), (53, 1)] }, { coefficient := -1, powers := [(15, 1), (51, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (34, 1), (43, 1), (53, 1), (59, 1)] }, { coefficient := 1, powers := [(11, 1), (34, 1), (43, 1), (53, 1), (59, 1)] }, { coefficient := -1, powers := [(33, 1), (34, 1), (36, 1), (43, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (25, 1), (34, 1), (40, 1), (54, 1), (59, 1)] }, { coefficient := -1, powers := [(3, 1), (34, 1), (40, 1), (54, 1), (68, 1)] }, { coefficient := -1, powers := [(11, 1), (25, 1), (34, 1), (40, 1), (54, 1), (59, 1)] }, { coefficient := 1, powers := [(11, 1), (34, 1), (40, 1), (54, 1), (68, 1)] }, { coefficient := 1, powers := [(25, 1), (33, 1), (34, 1), (36, 1), (40, 1), (54, 1)] }, { coefficient := -1, powers := [(33, 1), (34, 1), (40, 1), (42, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (25, 1), (37, 1), (59, 1), (66, 1)] }, { coefficient := -1, powers := [(3, 1), (25, 1), (40, 1), (59, 1), (60, 1)] }, { coefficient := 1, powers := [(3, 1), (37, 1), (66, 1), (68, 1)] }, { coefficient := 1, powers := [(3, 1), (40, 1), (60, 1), (68, 1)] }, { coefficient := 1, powers := [(11, 1), (25, 1), (37, 1), (59, 1), (66, 1)] }, { coefficient := 1, powers := [(11, 1), (25, 1), (40, 1), (59, 1), (60, 1)] }, { coefficient := -1, powers := [(11, 1), (37, 1), (66, 1), (68, 1)] }, { coefficient := -1, powers := [(11, 1), (40, 1), (60, 1), (68, 1)] }, { coefficient := -1, powers := [(25, 1), (33, 1), (36, 1), (37, 1), (66, 1)] }, { coefficient := -1, powers := [(25, 1), (33, 1), (36, 1), (40, 1), (60, 1)] }, { coefficient := 1, powers := [(33, 1), (37, 1), (42, 1), (66, 1)] }, { coefficient := 1, powers := [(33, 1), (40, 1), (42, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (25, 1), (34, 1), (43, 1), (53, 1)] }, { coefficient := -1, powers := [(28, 1), (34, 1), (43, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (18, 1), (23, 1), (29, 1)] }, { coefficient := 1, powers := [(4, 1), (23, 1), (26, 1)] }, { coefficient := 1, powers := [(7, 1), (18, 1), (29, 1)] }, { coefficient := -1, powers := [(7, 1), (26, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (23, 1), (25, 1), (57, 1), (59, 1)] }, { coefficient := -1, powers := [(3, 1), (23, 1), (57, 1), (68, 1)] }, { coefficient := -1, powers := [(11, 1), (23, 1), (25, 1), (57, 1), (59, 1)] }, { coefficient := 1, powers := [(11, 1), (23, 1), (57, 1), (68, 1)] }, { coefficient := 1, powers := [(23, 1), (25, 1), (33, 1), (36, 1), (57, 1)] }, { coefficient := -1, powers := [(23, 1), (33, 1), (42, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [(11, 1), (34, 1), (43, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (25, 1), (34, 1), (40, 1), (53, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (34, 1), (40, 1), (53, 1), (68, 1)] }, { coefficient := 1, powers := [(4, 1), (18, 1), (23, 1), (49, 1)] }, { coefficient := -1, powers := [(7, 1), (18, 1), (49, 1)] }, { coefficient := 1, powers := [(11, 1), (25, 1), (34, 1), (40, 1), (53, 1), (59, 1)] }, { coefficient := -1, powers := [(11, 1), (34, 1), (40, 1), (53, 1), (68, 1)] }, { coefficient := -1, powers := [(25, 1), (33, 1), (34, 1), (36, 1), (40, 1), (53, 1)] }, { coefficient := 1, powers := [(33, 1), (34, 1), (40, 1), (42, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(51, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (23, 1), (51, 1), (57, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (31, 1), (37, 1), (59, 1), (66, 1)] }, { coefficient := 1, powers := [(3, 1), (31, 1), (40, 1), (59, 1), (60, 1)] }, { coefficient := 1, powers := [(3, 1), (34, 1), (40, 1), (57, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (34, 1), (43, 1), (54, 1), (59, 1)] }, { coefficient := 1, powers := [(11, 1), (23, 1), (51, 1), (57, 1), (59, 1)] }, { coefficient := -1, powers := [(11, 1), (31, 1), (37, 1), (59, 1), (66, 1)] }, { coefficient := -1, powers := [(11, 1), (31, 1), (40, 1), (59, 1), (60, 1)] }, { coefficient := -1, powers := [(11, 1), (34, 1), (40, 1), (57, 1), (59, 1)] }, { coefficient := -1, powers := [(11, 1), (34, 1), (43, 1), (54, 1), (59, 1)] }, { coefficient := -1, powers := [(23, 1), (33, 1), (36, 1), (51, 1), (57, 1)] }, { coefficient := 1, powers := [(31, 1), (33, 1), (36, 1), (37, 1), (66, 1)] }, { coefficient := 1, powers := [(31, 1), (33, 1), (36, 1), (40, 1), (60, 1)] }, { coefficient := 1, powers := [(33, 1), (34, 1), (36, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(33, 1), (34, 1), (36, 1), (43, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (23, 1), (25, 1), (51, 1), (57, 1)] }, { coefficient := -1, powers := [(11, 1), (25, 1), (31, 1), (37, 1), (66, 1)] }, { coefficient := -1, powers := [(11, 1), (25, 1), (31, 1), (40, 1), (60, 1)] }, { coefficient := -1, powers := [(11, 1), (25, 1), (34, 1), (40, 1), (57, 1)] }, { coefficient := -1, powers := [(11, 1), (25, 1), (34, 1), (43, 1), (54, 1)] }, { coefficient := -1, powers := [(23, 1), (28, 1), (51, 1), (57, 1)] }, { coefficient := 1, powers := [(28, 1), (31, 1), (37, 1), (66, 1)] }, { coefficient := 1, powers := [(28, 1), (31, 1), (40, 1), (60, 1)] }, { coefficient := 1, powers := [(28, 1), (34, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(28, 1), (34, 1), (43, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (17, 1), (23, 1), (51, 1), (57, 1)] }, { coefficient := -1, powers := [(11, 1), (17, 1), (31, 1), (37, 1), (66, 1)] }, { coefficient := -1, powers := [(11, 1), (17, 1), (31, 1), (40, 1), (60, 1)] }, { coefficient := -1, powers := [(11, 1), (17, 1), (34, 1), (40, 1), (57, 1)] }, { coefficient := -1, powers := [(11, 1), (17, 1), (34, 1), (43, 1), (54, 1)] }, { coefficient := -1, powers := [(20, 1), (23, 1), (51, 1), (57, 1)] }, { coefficient := 1, powers := [(20, 1), (31, 1), (37, 1), (66, 1)] }, { coefficient := 1, powers := [(20, 1), (31, 1), (40, 1), (60, 1)] }, { coefficient := 1, powers := [(20, 1), (34, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(20, 1), (34, 1), (43, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(23, 1), (29, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (23, 1)] }, { coefficient := 1, powers := [(15, 1)] }],
  [{ coefficient := 1, powers := [(34, 1), (43, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (23, 1)] }, { coefficient := 1, powers := [(7, 1)] }],
  [{ coefficient := 1, powers := [(23, 1)] }],
  [{ coefficient := -1, powers := [(11, 1), (23, 1), (51, 1), (57, 1)] }, { coefficient := 1, powers := [(11, 1), (31, 1), (37, 1), (66, 1)] }, { coefficient := 1, powers := [(11, 1), (31, 1), (40, 1), (60, 1)] }, { coefficient := 1, powers := [(11, 1), (34, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(11, 1), (34, 1), (43, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (51, 1), (57, 1)] }, { coefficient := -1, powers := [(31, 1), (37, 1), (66, 1)] }, { coefficient := -1, powers := [(31, 1), (40, 1), (60, 1)] }, { coefficient := -1, powers := [(34, 1), (40, 1), (57, 1)] }, { coefficient := -1, powers := [(34, 1), (43, 1), (54, 1)] }],
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
    ¬ ∀ index : Fin 22,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.X5Case136Selected.selectedHasNoCommonZero

end Krenn.X5Case136Selected
