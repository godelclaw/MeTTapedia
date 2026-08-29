import KrennSparseCertificate

/-! Selected core of a strict exact certificate over a frozen system. -/

namespace Krenn.X5Case94Selected

open Krenn.SparseCertificate
open MvPolynomial

def sourceSystemFileSHA256 : String := "e178bdb392c38f2a00f38ab25a0243e21df88f8b6fed13b21e8b6c163cc38c29"
def sourceSystemSemanticSHA256 : String := "d74c729d1a4d4252fa387877d0db161e8acc9d1695fd767b329b3a155ce04977"
def certificateSHA256 : String := "e412ed1267ec5af4016a9d16ef9be96025aeba7cb8fe91f61ad47b671c34ca11"
def sourceEquationCount : Nat := 675

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedIndices : Fin 22 → Fin 675 := ![
  0,
  2,
  10,
  13,
  16,
  46,
  48,
  52,
  398,
  416,
  419,
  420,
  422,
  423,
  424,
  426,
  436,
  660,
  668,
  671,
  673,
  674
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 22 → SparsePoly (Fin 70) := ![
  [{ coefficient := 1, powers := [(53, 1)] }],
  [{ coefficient := 1, powers := [(63, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(48, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(49, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(51, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (48, 1), (57, 1)] }, { coefficient := 1, powers := [(57, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (63, 1)] }, { coefficient := 1, powers := [(20, 1), (57, 1)] }, { coefficient := 1, powers := [(54, 1)] }],
  [{ coefficient := 1, powers := [(15, 1), (63, 1)] }, { coefficient := 1, powers := [(23, 1), (57, 1)] }, { coefficient := 1, powers := [(31, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (56, 1)] }, { coefficient := 1, powers := [(25, 1), (53, 1)] }, { coefficient := 1, powers := [(62, 1)] }],
  [{ coefficient := 1, powers := [(36, 1), (65, 1)] }, { coefficient := 1, powers := [(39, 1), (59, 1)] }, { coefficient := 1, powers := [(48, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(36, 1), (68, 1)] }, { coefficient := 1, powers := [(42, 1), (59, 1)] }, { coefficient := 1, powers := [(48, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(37, 1), (69, 1)] }, { coefficient := 1, powers := [(43, 1), (60, 1)] }, { coefficient := 1, powers := [(51, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(40, 1), (69, 1)] }, { coefficient := 1, powers := [(43, 1), (66, 1)] }, { coefficient := 1, powers := [(51, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (57, 1), (65, 1)] }, { coefficient := 1, powers := [(19, 1), (48, 1), (57, 1)] }, { coefficient := 1, powers := [(33, 1), (39, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (49, 1), (63, 1)] }, { coefficient := 1, powers := [(18, 1), (49, 1), (57, 1)] }, { coefficient := 1, powers := [(26, 1), (49, 1), (54, 1)] }, { coefficient := 1, powers := [(54, 1), (69, 1)] }, { coefficient := 1, powers := [(57, 1), (66, 1)] }, { coefficient := 1, powers := [(60, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (54, 1), (69, 1)] }, { coefficient := 1, powers := [(4, 1), (57, 1), (66, 1)] }, { coefficient := 1, powers := [(4, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(12, 1), (40, 1), (69, 1)] }, { coefficient := 1, powers := [(12, 1), (43, 1), (66, 1)] }, { coefficient := 1, powers := [(12, 1), (51, 1), (63, 1)] }, { coefficient := 1, powers := [(20, 1), (37, 1), (69, 1)] }, { coefficient := 1, powers := [(20, 1), (43, 1), (60, 1)] }, { coefficient := 1, powers := [(20, 1), (51, 1), (57, 1)] }, { coefficient := 1, powers := [(37, 1), (66, 1)] }, { coefficient := 1, powers := [(40, 1), (60, 1)] }, { coefficient := 1, powers := [(51, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (36, 1), (68, 1)] }, { coefficient := 1, powers := [(17, 1), (42, 1), (59, 1)] }, { coefficient := 1, powers := [(17, 1), (48, 1), (56, 1)] }, { coefficient := 1, powers := [(25, 1), (36, 1), (65, 1)] }, { coefficient := 1, powers := [(25, 1), (39, 1), (59, 1)] }, { coefficient := 1, powers := [(25, 1), (48, 1), (53, 1)] }, { coefficient := 1, powers := [(39, 1), (68, 1)] }, { coefficient := 1, powers := [(42, 1), (65, 1)] }, { coefficient := 1, powers := [(48, 1), (62, 1)] }, { coefficient := 1, powers := [(53, 1), (68, 1)] }, { coefficient := 1, powers := [(56, 1), (65, 1)] }, { coefficient := 1, powers := [(59, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (53, 1), (68, 1)] }, { coefficient := 1, powers := [(3, 1), (56, 1), (65, 1)] }, { coefficient := 1, powers := [(3, 1), (59, 1), (62, 1)] }, { coefficient := 1, powers := [(11, 1), (39, 1), (68, 1)] }, { coefficient := 1, powers := [(11, 1), (42, 1), (65, 1)] }, { coefficient := 1, powers := [(11, 1), (48, 1), (62, 1)] }, { coefficient := 1, powers := [(19, 1), (36, 1), (68, 1)] }, { coefficient := 1, powers := [(19, 1), (42, 1), (59, 1)] }, { coefficient := 1, powers := [(19, 1), (48, 1), (56, 1)] }, { coefficient := 1, powers := [(28, 1), (36, 1), (65, 1)] }, { coefficient := 1, powers := [(28, 1), (39, 1), (59, 1)] }, { coefficient := 1, powers := [(28, 1), (48, 1), (53, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1), (62, 1)] }, { coefficient := 1, powers := [(33, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(33, 1), (42, 1), (53, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(7, 1), (54, 1), (69, 1)] }, { coefficient := 1, powers := [(7, 1), (57, 1), (66, 1)] }, { coefficient := 1, powers := [(7, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(15, 1), (40, 1), (69, 1)] }, { coefficient := 1, powers := [(15, 1), (43, 1), (66, 1)] }, { coefficient := 1, powers := [(15, 1), (51, 1), (63, 1)] }, { coefficient := 1, powers := [(23, 1), (37, 1), (69, 1)] }, { coefficient := 1, powers := [(23, 1), (43, 1), (60, 1)] }, { coefficient := 1, powers := [(23, 1), (51, 1), (57, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1), (66, 1)] }, { coefficient := 1, powers := [(31, 1), (40, 1), (60, 1)] }, { coefficient := 1, powers := [(31, 1), (51, 1), (54, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1), (63, 1)] }, { coefficient := 1, powers := [(34, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(34, 1), (43, 1), (54, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 22 → SparsePoly (Fin 70) := ![
  [{ coefficient := -1, powers := [(3, 1), (23, 1), (25, 1), (37, 1), (59, 1), (69, 1)] }, { coefficient := -1, powers := [(3, 1), (23, 1), (25, 1), (43, 1), (59, 1), (60, 1)] }, { coefficient := 1, powers := [(3, 1), (23, 1), (37, 1), (68, 1), (69, 1)] }, { coefficient := 1, powers := [(3, 1), (23, 1), (43, 1), (60, 1), (68, 1)] }, { coefficient := 1, powers := [(3, 1), (25, 1), (31, 1), (51, 1), (54, 1), (59, 1)] }, { coefficient := -1, powers := [(3, 1), (25, 1), (34, 1), (40, 1), (57, 1), (59, 1)] }, { coefficient := -1, powers := [(3, 1), (25, 1), (34, 1), (43, 1), (54, 1), (59, 1)] }, { coefficient := -1, powers := [(3, 1), (31, 1), (51, 1), (54, 1), (68, 1)] }, { coefficient := 1, powers := [(3, 1), (34, 1), (40, 1), (57, 1), (68, 1)] }, { coefficient := 1, powers := [(3, 1), (34, 1), (43, 1), (54, 1), (68, 1)] }, { coefficient := 1, powers := [(11, 1), (23, 1), (25, 1), (37, 1), (59, 1), (69, 1)] }, { coefficient := 1, powers := [(11, 1), (23, 1), (25, 1), (43, 1), (59, 1), (60, 1)] }, { coefficient := -1, powers := [(11, 1), (23, 1), (37, 1), (68, 1), (69, 1)] }, { coefficient := -1, powers := [(11, 1), (23, 1), (43, 1), (60, 1), (68, 1)] }, { coefficient := -1, powers := [(11, 1), (25, 1), (31, 1), (51, 1), (54, 1), (59, 1)] }, { coefficient := 1, powers := [(11, 1), (25, 1), (34, 1), (40, 1), (57, 1), (59, 1)] }, { coefficient := 1, powers := [(11, 1), (25, 1), (34, 1), (43, 1), (54, 1), (59, 1)] }, { coefficient := 1, powers := [(11, 1), (31, 1), (51, 1), (54, 1), (68, 1)] }, { coefficient := -1, powers := [(11, 1), (34, 1), (40, 1), (57, 1), (68, 1)] }, { coefficient := -1, powers := [(11, 1), (34, 1), (43, 1), (54, 1), (68, 1)] }, { coefficient := -1, powers := [(23, 1), (25, 1), (33, 1), (36, 1), (37, 1), (69, 1)] }, { coefficient := -1, powers := [(23, 1), (25, 1), (33, 1), (36, 1), (43, 1), (60, 1)] }, { coefficient := 1, powers := [(23, 1), (33, 1), (37, 1), (42, 1), (69, 1)] }, { coefficient := 1, powers := [(23, 1), (33, 1), (42, 1), (43, 1), (60, 1)] }, { coefficient := 1, powers := [(25, 1), (31, 1), (33, 1), (36, 1), (51, 1), (54, 1)] }, { coefficient := -1, powers := [(25, 1), (33, 1), (34, 1), (36, 1), (40, 1), (57, 1)] }, { coefficient := -1, powers := [(25, 1), (33, 1), (34, 1), (36, 1), (43, 1), (54, 1)] }, { coefficient := -1, powers := [(31, 1), (33, 1), (42, 1), (51, 1), (54, 1)] }, { coefficient := 1, powers := [(33, 1), (34, 1), (40, 1), (42, 1), (57, 1)] }, { coefficient := 1, powers := [(33, 1), (34, 1), (42, 1), (43, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (12, 1), (17, 1), (34, 1), (43, 1), (56, 1), (59, 1)] }, { coefficient := -1, powers := [(3, 1), (12, 1), (34, 1), (43, 1), (56, 1), (65, 1)] }, { coefficient := 1, powers := [(4, 1), (9, 1), (31, 1), (49, 1)] }, { coefficient := -1, powers := [(4, 1), (12, 1), (26, 1), (31, 1), (49, 1)] }, { coefficient := -1, powers := [(7, 1), (9, 1), (49, 1)] }, { coefficient := 1, powers := [(7, 1), (12, 1), (26, 1), (49, 1)] }, { coefficient := -1, powers := [(11, 1), (12, 1), (17, 1), (34, 1), (43, 1), (56, 1), (59, 1)] }, { coefficient := 1, powers := [(11, 1), (12, 1), (34, 1), (43, 1), (56, 1), (65, 1)] }, { coefficient := 1, powers := [(12, 1), (17, 1), (33, 1), (34, 1), (36, 1), (43, 1), (56, 1)] }, { coefficient := -1, powers := [(12, 1), (33, 1), (34, 1), (39, 1), (43, 1), (56, 1)] }, { coefficient := -1, powers := [(15, 1), (51, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (34, 1), (40, 1), (56, 1), (59, 1)] }, { coefficient := 1, powers := [(11, 1), (34, 1), (40, 1), (56, 1), (59, 1)] }, { coefficient := -1, powers := [(33, 1), (34, 1), (36, 1), (40, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (17, 1), (34, 1), (43, 1), (57, 1), (59, 1)] }, { coefficient := -1, powers := [(3, 1), (34, 1), (43, 1), (57, 1), (65, 1)] }, { coefficient := -1, powers := [(11, 1), (17, 1), (34, 1), (43, 1), (57, 1), (59, 1)] }, { coefficient := 1, powers := [(11, 1), (34, 1), (43, 1), (57, 1), (65, 1)] }, { coefficient := 1, powers := [(17, 1), (33, 1), (34, 1), (36, 1), (43, 1), (57, 1)] }, { coefficient := -1, powers := [(33, 1), (34, 1), (39, 1), (43, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (17, 1), (37, 1), (59, 1), (69, 1)] }, { coefficient := -1, powers := [(3, 1), (17, 1), (43, 1), (59, 1), (60, 1)] }, { coefficient := 1, powers := [(3, 1), (37, 1), (65, 1), (69, 1)] }, { coefficient := 1, powers := [(3, 1), (43, 1), (60, 1), (65, 1)] }, { coefficient := 1, powers := [(11, 1), (17, 1), (37, 1), (59, 1), (69, 1)] }, { coefficient := 1, powers := [(11, 1), (17, 1), (43, 1), (59, 1), (60, 1)] }, { coefficient := -1, powers := [(11, 1), (37, 1), (65, 1), (69, 1)] }, { coefficient := -1, powers := [(11, 1), (43, 1), (60, 1), (65, 1)] }, { coefficient := -1, powers := [(17, 1), (33, 1), (36, 1), (37, 1), (69, 1)] }, { coefficient := -1, powers := [(17, 1), (33, 1), (36, 1), (43, 1), (60, 1)] }, { coefficient := 1, powers := [(33, 1), (37, 1), (39, 1), (69, 1)] }, { coefficient := 1, powers := [(33, 1), (39, 1), (43, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (17, 1), (34, 1), (40, 1), (56, 1)] }, { coefficient := -1, powers := [(19, 1), (34, 1), (40, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (18, 1), (31, 1)] }, { coefficient := -1, powers := [(4, 1), (20, 1), (26, 1), (31, 1)] }, { coefficient := -1, powers := [(7, 1), (18, 1)] }, { coefficient := 1, powers := [(7, 1), (20, 1), (26, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (17, 1), (31, 1), (54, 1), (59, 1)] }, { coefficient := -1, powers := [(3, 1), (31, 1), (54, 1), (65, 1)] }, { coefficient := -1, powers := [(11, 1), (17, 1), (31, 1), (54, 1), (59, 1)] }, { coefficient := 1, powers := [(11, 1), (31, 1), (54, 1), (65, 1)] }, { coefficient := 1, powers := [(17, 1), (31, 1), (33, 1), (36, 1), (54, 1)] }, { coefficient := -1, powers := [(31, 1), (33, 1), (39, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(11, 1), (34, 1), (40, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (17, 1), (34, 1), (43, 1), (56, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (34, 1), (43, 1), (56, 1), (65, 1)] }, { coefficient := 1, powers := [(4, 1), (26, 1), (31, 1), (49, 1)] }, { coefficient := -1, powers := [(7, 1), (26, 1), (49, 1)] }, { coefficient := 1, powers := [(11, 1), (17, 1), (34, 1), (43, 1), (56, 1), (59, 1)] }, { coefficient := -1, powers := [(11, 1), (34, 1), (43, 1), (56, 1), (65, 1)] }, { coefficient := -1, powers := [(17, 1), (33, 1), (34, 1), (36, 1), (43, 1), (56, 1)] }, { coefficient := 1, powers := [(33, 1), (34, 1), (39, 1), (43, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(51, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (23, 1), (37, 1), (59, 1), (69, 1)] }, { coefficient := 1, powers := [(3, 1), (23, 1), (43, 1), (59, 1), (60, 1)] }, { coefficient := -1, powers := [(3, 1), (31, 1), (51, 1), (54, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (34, 1), (40, 1), (57, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (34, 1), (43, 1), (54, 1), (59, 1)] }, { coefficient := -1, powers := [(11, 1), (23, 1), (37, 1), (59, 1), (69, 1)] }, { coefficient := -1, powers := [(11, 1), (23, 1), (43, 1), (59, 1), (60, 1)] }, { coefficient := 1, powers := [(11, 1), (31, 1), (51, 1), (54, 1), (59, 1)] }, { coefficient := -1, powers := [(11, 1), (34, 1), (40, 1), (57, 1), (59, 1)] }, { coefficient := -1, powers := [(11, 1), (34, 1), (43, 1), (54, 1), (59, 1)] }, { coefficient := 1, powers := [(23, 1), (33, 1), (36, 1), (37, 1), (69, 1)] }, { coefficient := 1, powers := [(23, 1), (33, 1), (36, 1), (43, 1), (60, 1)] }, { coefficient := -1, powers := [(31, 1), (33, 1), (36, 1), (51, 1), (54, 1)] }, { coefficient := 1, powers := [(33, 1), (34, 1), (36, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(33, 1), (34, 1), (36, 1), (43, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(11, 1), (23, 1), (25, 1), (37, 1), (69, 1)] }, { coefficient := -1, powers := [(11, 1), (23, 1), (25, 1), (43, 1), (60, 1)] }, { coefficient := 1, powers := [(11, 1), (25, 1), (31, 1), (51, 1), (54, 1)] }, { coefficient := -1, powers := [(11, 1), (25, 1), (34, 1), (40, 1), (57, 1)] }, { coefficient := -1, powers := [(11, 1), (25, 1), (34, 1), (43, 1), (54, 1)] }, { coefficient := 1, powers := [(23, 1), (28, 1), (37, 1), (69, 1)] }, { coefficient := 1, powers := [(23, 1), (28, 1), (43, 1), (60, 1)] }, { coefficient := -1, powers := [(28, 1), (31, 1), (51, 1), (54, 1)] }, { coefficient := 1, powers := [(28, 1), (34, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(28, 1), (34, 1), (43, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(11, 1), (17, 1), (23, 1), (37, 1), (69, 1)] }, { coefficient := -1, powers := [(11, 1), (17, 1), (23, 1), (43, 1), (60, 1)] }, { coefficient := 1, powers := [(11, 1), (17, 1), (31, 1), (51, 1), (54, 1)] }, { coefficient := -1, powers := [(11, 1), (17, 1), (34, 1), (40, 1), (57, 1)] }, { coefficient := -1, powers := [(11, 1), (17, 1), (34, 1), (43, 1), (54, 1)] }, { coefficient := 1, powers := [(19, 1), (23, 1), (37, 1), (69, 1)] }, { coefficient := 1, powers := [(19, 1), (23, 1), (43, 1), (60, 1)] }, { coefficient := -1, powers := [(19, 1), (31, 1), (51, 1), (54, 1)] }, { coefficient := 1, powers := [(19, 1), (34, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(19, 1), (34, 1), (43, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(20, 1), (31, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (31, 1)] }, { coefficient := 1, powers := [(15, 1)] }],
  [{ coefficient := 1, powers := [(34, 1), (40, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (31, 1)] }, { coefficient := 1, powers := [(7, 1)] }],
  [{ coefficient := 1, powers := [(31, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (23, 1), (37, 1), (69, 1)] }, { coefficient := 1, powers := [(11, 1), (23, 1), (43, 1), (60, 1)] }, { coefficient := -1, powers := [(11, 1), (31, 1), (51, 1), (54, 1)] }, { coefficient := 1, powers := [(11, 1), (34, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(11, 1), (34, 1), (43, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(23, 1), (37, 1), (69, 1)] }, { coefficient := -1, powers := [(23, 1), (43, 1), (60, 1)] }, { coefficient := 1, powers := [(31, 1), (51, 1), (54, 1)] }, { coefficient := -1, powers := [(34, 1), (40, 1), (57, 1)] }, { coefficient := -1, powers := [(34, 1), (43, 1), (54, 1)] }],
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

#print axioms Krenn.X5Case94Selected.selectedHasNoCommonZero

end Krenn.X5Case94Selected
