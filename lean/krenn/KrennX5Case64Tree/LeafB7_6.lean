import KrennSparseCertificate

/-! Selected core of a strict exact certificate over a frozen system. -/

namespace Krenn.X5Case64Tree.LeafB7_6

open Krenn.SparseCertificate
open MvPolynomial

def sourceSystemFileSHA256 : String := "90d3d05b4191e5d3339bff62649218b5537287addcfb6238420eeff986a4f908"
def sourceSystemSemanticSHA256 : String := "3a18f9dba3d5310006dd143c00ce97b4c76ad90ee6e9990d26742c1caad989ad"
def certificateSHA256 : String := "b192eb7a8390b9c08f6f386710f866f6760788eb361ff5ab9c625c97c9312472"
def sourceEquationCount : Nat := 681

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedIndices : Fin 28 → Fin 681 := ![
  1,
  15,
  25,
  30,
  31,
  46,
  48,
  51,
  52,
  310,
  397,
  422,
  423,
  424,
  426,
  500,
  556,
  620,
  636,
  641,
  660,
  662,
  671,
  673,
  674,
  678,
  679,
  680
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 28 → SparsePoly (Fin 75) := ![
  [{ coefficient := 1, powers := [(63, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(36, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(40, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(40, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(48, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(49, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(50, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(50, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(49, 1), (55, 1)] }, { coefficient := 1, powers := [(55, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (48, 1), (55, 1)] }, { coefficient := 1, powers := [(55, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(36, 1), (65, 1)] }, { coefficient := 1, powers := [(39, 1), (59, 1)] }, { coefficient := 1, powers := [(48, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(36, 1), (68, 1)] }, { coefficient := 1, powers := [(42, 1), (59, 1)] }, { coefficient := 1, powers := [(48, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(37, 1), (66, 1)] }, { coefficient := 1, powers := [(40, 1), (60, 1)] }, { coefficient := 1, powers := [(51, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(40, 1), (69, 1)] }, { coefficient := 1, powers := [(43, 1), (66, 1)] }, { coefficient := 1, powers := [(51, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (40, 1), (67, 1)] }, { coefficient := 1, powers := [(23, 1), (55, 1)] }, { coefficient := 1, powers := [(40, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (40, 1), (59, 1)] }, { coefficient := 1, powers := [(40, 1), (68, 1)] }, { coefficient := 1, powers := [(50, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (40, 1), (67, 1)] }, { coefficient := 1, powers := [(24, 1), (40, 1), (58, 1)] }, { coefficient := 1, powers := [(32, 1), (40, 1), (55, 1)] }, { coefficient := 1, powers := [(55, 1)] }],
  [{ coefficient := 1, powers := [(15, 1), (42, 1), (66, 1)] }, { coefficient := 1, powers := [(23, 1), (42, 1), (60, 1)] }, { coefficient := 1, powers := [(30, 1), (49, 1), (54, 1)] }, { coefficient := 1, powers := [(34, 1), (42, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (36, 1), (66, 1)] }, { coefficient := 1, powers := [(42, 1), (66, 1)] }, { coefficient := 1, powers := [(49, 1), (56, 1)] }, { coefficient := 1, powers := [(56, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (49, 1), (63, 1)] }, { coefficient := 1, powers := [(26, 1), (49, 1), (54, 1)] }, { coefficient := 1, powers := [(49, 1), (57, 1)] }, { coefficient := 1, powers := [(54, 1), (69, 1)] }, { coefficient := 1, powers := [(57, 1), (66, 1)] }, { coefficient := 1, powers := [(60, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (50, 1), (63, 1)] }, { coefficient := 1, powers := [(20, 1), (50, 1), (57, 1)] }, { coefficient := 1, powers := [(29, 1), (50, 1), (54, 1)] }, { coefficient := 1, powers := [(33, 1), (37, 1), (63, 1)] }, { coefficient := 1, powers := [(33, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(33, 1), (43, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (36, 1), (68, 1)] }, { coefficient := 1, powers := [(17, 1), (42, 1), (59, 1)] }, { coefficient := 1, powers := [(17, 1), (48, 1), (56, 1)] }, { coefficient := 1, powers := [(25, 1), (36, 1), (65, 1)] }, { coefficient := 1, powers := [(25, 1), (39, 1), (59, 1)] }, { coefficient := 1, powers := [(25, 1), (48, 1), (53, 1)] }, { coefficient := 1, powers := [(39, 1), (68, 1)] }, { coefficient := 1, powers := [(42, 1), (65, 1)] }, { coefficient := 1, powers := [(48, 1), (62, 1)] }, { coefficient := 1, powers := [(53, 1), (68, 1)] }, { coefficient := 1, powers := [(56, 1), (65, 1)] }, { coefficient := 1, powers := [(59, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (53, 1), (68, 1)] }, { coefficient := 1, powers := [(3, 1), (56, 1), (65, 1)] }, { coefficient := 1, powers := [(3, 1), (59, 1), (62, 1)] }, { coefficient := 1, powers := [(11, 1), (39, 1), (68, 1)] }, { coefficient := 1, powers := [(11, 1), (42, 1), (65, 1)] }, { coefficient := 1, powers := [(11, 1), (48, 1), (62, 1)] }, { coefficient := 1, powers := [(19, 1), (36, 1), (68, 1)] }, { coefficient := 1, powers := [(19, 1), (42, 1), (59, 1)] }, { coefficient := 1, powers := [(19, 1), (48, 1), (56, 1)] }, { coefficient := 1, powers := [(28, 1), (36, 1), (65, 1)] }, { coefficient := 1, powers := [(28, 1), (39, 1), (59, 1)] }, { coefficient := 1, powers := [(28, 1), (48, 1), (53, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1), (62, 1)] }, { coefficient := 1, powers := [(33, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(33, 1), (42, 1), (53, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(7, 1), (54, 1), (69, 1)] }, { coefficient := 1, powers := [(7, 1), (57, 1), (66, 1)] }, { coefficient := 1, powers := [(7, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(15, 1), (40, 1), (69, 1)] }, { coefficient := 1, powers := [(15, 1), (43, 1), (66, 1)] }, { coefficient := 1, powers := [(15, 1), (51, 1), (63, 1)] }, { coefficient := 1, powers := [(23, 1), (37, 1), (69, 1)] }, { coefficient := 1, powers := [(23, 1), (43, 1), (60, 1)] }, { coefficient := 1, powers := [(23, 1), (51, 1), (57, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1), (66, 1)] }, { coefficient := 1, powers := [(31, 1), (40, 1), (60, 1)] }, { coefficient := 1, powers := [(31, 1), (51, 1), (54, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1), (63, 1)] }, { coefficient := 1, powers := [(34, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(34, 1), (43, 1), (54, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(55, 1), (73, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(56, 1), (74, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(57, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 28 → SparsePoly (Fin 75) := ![
  [{ coefficient := -1, powers := [(7, 1), (9, 1), (33, 1), (36, 1), (49, 1), (62, 1)] }, { coefficient := -1, powers := [(7, 1), (9, 1), (33, 1), (39, 1), (49, 1), (56, 1)] }, { coefficient := -1, powers := [(7, 1), (9, 1), (33, 1), (42, 1), (49, 1), (53, 1)] }, { coefficient := -1, powers := [(12, 1), (34, 1), (36, 1), (50, 1), (62, 1)] }, { coefficient := -1, powers := [(12, 1), (34, 1), (39, 1), (50, 1), (56, 1)] }, { coefficient := 1, powers := [(33, 1), (34, 1), (37, 1), (42, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (24, 1), (39, 1), (55, 1), (68, 1), (73, 1), (74, 1)] }, { coefficient := 1, powers := [(11, 1), (24, 1), (39, 1), (55, 1), (68, 1), (73, 1), (74, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1), (37, 1), (62, 1), (69, 1), (74, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1), (43, 1), (60, 1), (62, 1), (74, 1)] }, { coefficient := 1, powers := [(33, 1), (37, 1), (39, 1), (56, 1), (69, 1), (74, 1)] }, { coefficient := 1, powers := [(33, 1), (37, 1), (42, 1), (53, 1), (69, 1), (74, 1)] }, { coefficient := 1, powers := [(33, 1), (39, 1), (43, 1), (56, 1), (60, 1), (74, 1)] }],
  [{ coefficient := 1, powers := [(15, 1), (25, 1), (33, 1), (43, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (25, 1), (32, 1), (39, 1)] }, { coefficient := 1, powers := [(11, 1), (25, 1), (32, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (8, 1), (39, 1), (68, 1), (73, 1)] }, { coefficient := -1, powers := [(3, 1), (13, 1), (24, 1), (39, 1), (68, 1), (73, 1)] }, { coefficient := -1, powers := [(8, 1), (11, 1), (39, 1), (68, 1), (73, 1)] }, { coefficient := 1, powers := [(11, 1), (13, 1), (24, 1), (39, 1), (68, 1), (73, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (17, 1), (42, 1), (73, 1)] }, { coefficient := -1, powers := [(3, 1), (62, 1), (73, 1)] }, { coefficient := -1, powers := [(11, 1), (17, 1), (42, 1), (73, 1)] }, { coefficient := 1, powers := [(11, 1), (62, 1), (73, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (26, 1), (33, 1), (36, 1), (62, 1)] }, { coefficient := -1, powers := [(7, 1), (26, 1), (33, 1), (39, 1), (56, 1)] }, { coefficient := -1, powers := [(7, 1), (26, 1), (33, 1), (42, 1), (53, 1)] }, { coefficient := -1, powers := [(30, 1), (33, 1), (43, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(29, 1), (34, 1), (36, 1), (62, 1)] }, { coefficient := -1, powers := [(29, 1), (34, 1), (39, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (32, 1), (39, 1), (56, 1), (73, 1)] }, { coefficient := 1, powers := [(11, 1), (32, 1), (39, 1), (56, 1), (73, 1)] }],
  [{ coefficient := 1, powers := [(15, 1), (33, 1), (43, 1), (53, 1), (56, 1), (73, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (42, 1), (73, 1)] }, { coefficient := 1, powers := [(11, 1), (42, 1), (73, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (25, 1)] }, { coefficient := 1, powers := [(28, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (17, 1)] }, { coefficient := 1, powers := [(19, 1)] }],
  [{ coefficient := 1, powers := [(31, 1), (33, 1), (36, 1), (62, 1)] }, { coefficient := 1, powers := [(31, 1), (33, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(31, 1), (33, 1), (42, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(15, 1), (33, 1), (36, 1), (62, 1)] }, { coefficient := 1, powers := [(15, 1), (33, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(15, 1), (33, 1), (42, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (24, 1), (39, 1), (68, 1), (73, 1)] }, { coefficient := -1, powers := [(11, 1), (24, 1), (39, 1), (68, 1), (73, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (32, 1), (39, 1)] }, { coefficient := -1, powers := [(11, 1), (32, 1), (39, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (39, 1), (68, 1), (73, 1)] }, { coefficient := 1, powers := [(11, 1), (39, 1), (68, 1), (73, 1)] }],
  [{ coefficient := 1, powers := [(33, 1), (43, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(15, 1), (33, 1), (43, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (33, 1), (36, 1), (62, 1)] }, { coefficient := 1, powers := [(7, 1), (33, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(7, 1), (33, 1), (42, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(34, 1), (36, 1), (62, 1)] }, { coefficient := 1, powers := [(34, 1), (39, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(3, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(33, 1), (36, 1), (62, 1)] }, { coefficient := -1, powers := [(33, 1), (39, 1), (56, 1)] }, { coefficient := -1, powers := [(33, 1), (42, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (32, 1), (39, 1), (40, 1), (68, 1)] }, { coefficient := 1, powers := [(3, 1), (32, 1), (39, 1), (50, 1), (56, 1)] }, { coefficient := 1, powers := [(3, 1), (39, 1), (68, 1)] }, { coefficient := 1, powers := [(3, 1), (42, 1), (65, 1)] }, { coefficient := 1, powers := [(3, 1), (48, 1), (62, 1)] }, { coefficient := -1, powers := [(11, 1), (32, 1), (39, 1), (40, 1), (68, 1)] }, { coefficient := -1, powers := [(11, 1), (32, 1), (39, 1), (50, 1), (56, 1)] }, { coefficient := -1, powers := [(11, 1), (39, 1), (68, 1)] }, { coefficient := -1, powers := [(11, 1), (42, 1), (65, 1)] }, { coefficient := -1, powers := [(11, 1), (48, 1), (62, 1)] }, { coefficient := -1, powers := [(15, 1), (33, 1), (43, 1), (49, 1), (53, 1), (56, 1)] }, { coefficient := -1, powers := [(15, 1), (33, 1), (43, 1), (53, 1), (56, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (23, 1), (24, 1), (39, 1), (55, 1), (68, 1), (73, 1)] }, { coefficient := -1, powers := [(11, 1), (23, 1), (24, 1), (39, 1), (55, 1), (68, 1), (73, 1)] }, { coefficient := -1, powers := [(23, 1), (33, 1), (36, 1), (37, 1), (62, 1), (69, 1)] }, { coefficient := -1, powers := [(23, 1), (33, 1), (36, 1), (43, 1), (60, 1), (62, 1)] }, { coefficient := -1, powers := [(23, 1), (33, 1), (37, 1), (39, 1), (56, 1), (69, 1)] }, { coefficient := -1, powers := [(23, 1), (33, 1), (37, 1), (42, 1), (53, 1), (69, 1)] }, { coefficient := -1, powers := [(23, 1), (33, 1), (39, 1), (43, 1), (56, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (33, 1), (36, 1), (49, 1), (62, 1)] }, { coefficient := -1, powers := [(7, 1), (33, 1), (39, 1), (49, 1), (56, 1)] }, { coefficient := -1, powers := [(7, 1), (33, 1), (42, 1), (49, 1), (53, 1)] }, { coefficient := -1, powers := [(20, 1), (34, 1), (36, 1), (50, 1), (62, 1)] }, { coefficient := -1, powers := [(20, 1), (34, 1), (39, 1), (50, 1), (56, 1)] }, { coefficient := 1, powers := [(23, 1), (33, 1), (36, 1), (51, 1), (62, 1)] }, { coefficient := 1, powers := [(23, 1), (33, 1), (39, 1), (51, 1), (56, 1)] }, { coefficient := 1, powers := [(23, 1), (33, 1), (42, 1), (51, 1), (53, 1)] }, { coefficient := 1, powers := [(33, 1), (34, 1), (40, 1), (42, 1), (53, 1)] }]
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
    (values : Fin 75 → R) :
    ¬ ∀ index : Fin 28,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.X5Case64Tree.LeafB7_6.selectedHasNoCommonZero

end Krenn.X5Case64Tree.LeafB7_6
