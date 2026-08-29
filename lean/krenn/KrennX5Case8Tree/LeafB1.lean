import KrennSparseCertificate

/-! Selected core of a strict exact certificate over a frozen system. -/

namespace Krenn.X5Case8Tree.LeafB1

open Krenn.SparseCertificate
open MvPolynomial

def sourceSystemFileSHA256 : String := "fd212bf3f3215c616cd382f9b8dad86f12f31ace10eb29af70bf09e049cc9ad5"
def sourceSystemSemanticSHA256 : String := "8355c37ae4a56af74a525ba343c08957c3dc1c9187e44e59bdead6bb7d0a8793"
def certificateSHA256 : String := "d5ca3b3cc395d247ce893ab29f4a189ae2d1a8b4e0d3af7436ba06b6413b5cc7"
def sourceEquationCount : Nat := 678

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedIndices : Fin 18 → Fin 678 := ![
  0,
  41,
  43,
  53,
  54,
  414,
  420,
  421,
  422,
  424,
  425,
  426,
  660,
  664,
  666,
  672,
  674,
  675
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 18 → SparsePoly (Fin 71) := ![
  [{ coefficient := 1, powers := [(52, 1)] }],
  [{ coefficient := 1, powers := [(46, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(46, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(51, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(51, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (63, 1)] }, { coefficient := 1, powers := [(17, 1), (57, 1)] }, { coefficient := 1, powers := [(54, 1)] }],
  [{ coefficient := 1, powers := [(15, 1), (63, 1)] }, { coefficient := 1, powers := [(23, 1), (57, 1)] }, { coefficient := 1, powers := [(31, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(35, 1), (64, 1)] }, { coefficient := 1, powers := [(38, 1), (58, 1)] }, { coefficient := 1, powers := [(44, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(35, 1), (67, 1)] }, { coefficient := 1, powers := [(41, 1), (58, 1)] }, { coefficient := 1, powers := [(44, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(37, 1), (69, 1)] }, { coefficient := 1, powers := [(43, 1), (60, 1)] }, { coefficient := 1, powers := [(51, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(38, 1), (67, 1)] }, { coefficient := 1, powers := [(41, 1), (64, 1)] }, { coefficient := 1, powers := [(44, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(40, 1), (69, 1)] }, { coefficient := 1, powers := [(43, 1), (66, 1)] }, { coefficient := 1, powers := [(51, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (48, 1), (63, 1)] }, { coefficient := 1, powers := [(17, 1), (48, 1), (57, 1)] }, { coefficient := 1, powers := [(48, 1), (54, 1)] }, { coefficient := 1, powers := [(54, 1), (69, 1)] }, { coefficient := 1, powers := [(57, 1), (66, 1)] }, { coefficient := 1, powers := [(60, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (46, 1), (61, 1)] }, { coefficient := 1, powers := [(21, 1), (46, 1), (55, 1)] }, { coefficient := 1, powers := [(29, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(34, 1), (35, 1), (61, 1)] }, { coefficient := 1, powers := [(34, 1), (38, 1), (55, 1)] }, { coefficient := 1, powers := [(34, 1), (41, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (54, 1), (69, 1)] }, { coefficient := 1, powers := [(1, 1), (57, 1), (66, 1)] }, { coefficient := 1, powers := [(1, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(9, 1), (40, 1), (69, 1)] }, { coefficient := 1, powers := [(9, 1), (43, 1), (66, 1)] }, { coefficient := 1, powers := [(9, 1), (51, 1), (63, 1)] }, { coefficient := 1, powers := [(17, 1), (37, 1), (69, 1)] }, { coefficient := 1, powers := [(17, 1), (43, 1), (60, 1)] }, { coefficient := 1, powers := [(17, 1), (51, 1), (57, 1)] }, { coefficient := 1, powers := [(37, 1), (66, 1)] }, { coefficient := 1, powers := [(40, 1), (60, 1)] }, { coefficient := 1, powers := [(51, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (52, 1), (67, 1)] }, { coefficient := 1, powers := [(0, 1), (55, 1), (64, 1)] }, { coefficient := 1, powers := [(0, 1), (58, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (38, 1), (67, 1)] }, { coefficient := 1, powers := [(8, 1), (41, 1), (64, 1)] }, { coefficient := 1, powers := [(8, 1), (44, 1), (61, 1)] }, { coefficient := 1, powers := [(16, 1), (35, 1), (67, 1)] }, { coefficient := 1, powers := [(16, 1), (41, 1), (58, 1)] }, { coefficient := 1, powers := [(16, 1), (44, 1), (55, 1)] }, { coefficient := 1, powers := [(24, 1), (35, 1), (64, 1)] }, { coefficient := 1, powers := [(24, 1), (38, 1), (58, 1)] }, { coefficient := 1, powers := [(24, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(32, 1), (35, 1), (61, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1), (55, 1)] }, { coefficient := 1, powers := [(32, 1), (41, 1), (52, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(7, 1), (54, 1), (69, 1)] }, { coefficient := 1, powers := [(7, 1), (57, 1), (66, 1)] }, { coefficient := 1, powers := [(7, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(15, 1), (40, 1), (69, 1)] }, { coefficient := 1, powers := [(15, 1), (43, 1), (66, 1)] }, { coefficient := 1, powers := [(15, 1), (51, 1), (63, 1)] }, { coefficient := 1, powers := [(23, 1), (37, 1), (69, 1)] }, { coefficient := 1, powers := [(23, 1), (43, 1), (60, 1)] }, { coefficient := 1, powers := [(23, 1), (51, 1), (57, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1), (66, 1)] }, { coefficient := 1, powers := [(31, 1), (40, 1), (60, 1)] }, { coefficient := 1, powers := [(31, 1), (51, 1), (54, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1), (63, 1)] }, { coefficient := 1, powers := [(34, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(34, 1), (43, 1), (54, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 18 → SparsePoly (Fin 71) := ![
  [{ coefficient := -1, powers := [(0, 1), (15, 1), (51, 1), (63, 1), (67, 1)] }, { coefficient := -1, powers := [(0, 1), (23, 1), (51, 1), (57, 1), (67, 1)] }, { coefficient := -1, powers := [(0, 1), (31, 1), (51, 1), (54, 1), (67, 1)] }, { coefficient := 1, powers := [(0, 1), (34, 1), (37, 1), (63, 1), (67, 1)] }, { coefficient := 1, powers := [(0, 1), (34, 1), (40, 1), (57, 1), (67, 1)] }, { coefficient := 1, powers := [(0, 1), (34, 1), (43, 1), (54, 1), (67, 1)] }, { coefficient := -1, powers := [(15, 1), (32, 1), (41, 1), (51, 1), (63, 1)] }, { coefficient := -1, powers := [(23, 1), (32, 1), (41, 1), (51, 1), (57, 1)] }, { coefficient := -1, powers := [(29, 1), (32, 1), (37, 1), (46, 1), (63, 1)] }, { coefficient := -1, powers := [(29, 1), (32, 1), (40, 1), (46, 1), (57, 1)] }, { coefficient := -1, powers := [(29, 1), (32, 1), (43, 1), (46, 1), (54, 1)] }, { coefficient := -1, powers := [(31, 1), (32, 1), (41, 1), (51, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(21, 1), (32, 1), (37, 1), (63, 1)] }, { coefficient := -1, powers := [(21, 1), (32, 1), (40, 1), (57, 1)] }, { coefficient := -1, powers := [(21, 1), (32, 1), (43, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(13, 1), (32, 1), (37, 1), (63, 1)] }, { coefficient := -1, powers := [(13, 1), (32, 1), (40, 1), (57, 1)] }, { coefficient := -1, powers := [(13, 1), (32, 1), (43, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(15, 1), (32, 1), (38, 1), (63, 1)] }, { coefficient := -1, powers := [(23, 1), (32, 1), (38, 1), (57, 1)] }, { coefficient := -1, powers := [(31, 1), (32, 1), (38, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(15, 1), (32, 1), (35, 1), (63, 1)] }, { coefficient := -1, powers := [(23, 1), (32, 1), (35, 1), (57, 1)] }, { coefficient := -1, powers := [(31, 1), (32, 1), (35, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (31, 1), (48, 1)] }, { coefficient := -1, powers := [(7, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(51, 1)] }],
  [{ coefficient := -1, powers := [(15, 1), (24, 1), (51, 1), (63, 1)] }, { coefficient := -1, powers := [(23, 1), (24, 1), (51, 1), (57, 1)] }, { coefficient := -1, powers := [(24, 1), (31, 1), (51, 1), (54, 1)] }, { coefficient := 1, powers := [(24, 1), (34, 1), (37, 1), (63, 1)] }, { coefficient := 1, powers := [(24, 1), (34, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(24, 1), (34, 1), (43, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(15, 1), (16, 1), (51, 1), (63, 1)] }, { coefficient := -1, powers := [(16, 1), (23, 1), (51, 1), (57, 1)] }, { coefficient := -1, powers := [(16, 1), (31, 1), (51, 1), (54, 1)] }, { coefficient := 1, powers := [(16, 1), (34, 1), (37, 1), (63, 1)] }, { coefficient := 1, powers := [(16, 1), (34, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(16, 1), (34, 1), (43, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(17, 1), (31, 1)] }, { coefficient := 1, powers := [(23, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (15, 1), (51, 1), (63, 1)] }, { coefficient := -1, powers := [(8, 1), (23, 1), (51, 1), (57, 1)] }, { coefficient := -1, powers := [(8, 1), (31, 1), (51, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (37, 1), (63, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (43, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(9, 1), (31, 1)] }, { coefficient := 1, powers := [(15, 1)] }],
  [{ coefficient := -1, powers := [(1, 1), (31, 1)] }, { coefficient := 1, powers := [(7, 1)] }],
  [{ coefficient := 1, powers := [(32, 1), (37, 1), (63, 1)] }, { coefficient := 1, powers := [(32, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(32, 1), (43, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(31, 1)] }],
  [{ coefficient := 1, powers := [(15, 1), (51, 1), (63, 1)] }, { coefficient := 1, powers := [(23, 1), (51, 1), (57, 1)] }, { coefficient := 1, powers := [(31, 1), (51, 1), (54, 1)] }, { coefficient := -1, powers := [(34, 1), (37, 1), (63, 1)] }, { coefficient := -1, powers := [(34, 1), (40, 1), (57, 1)] }, { coefficient := -1, powers := [(34, 1), (43, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(15, 1), (51, 1), (55, 1), (63, 1), (64, 1)] }, { coefficient := -1, powers := [(15, 1), (51, 1), (58, 1), (61, 1), (63, 1)] }, { coefficient := -1, powers := [(23, 1), (51, 1), (55, 1), (57, 1), (64, 1)] }, { coefficient := -1, powers := [(23, 1), (51, 1), (57, 1), (58, 1), (61, 1)] }, { coefficient := -1, powers := [(31, 1), (51, 1), (54, 1), (55, 1), (64, 1)] }, { coefficient := -1, powers := [(31, 1), (51, 1), (54, 1), (58, 1), (61, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1), (55, 1), (63, 1), (64, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1), (58, 1), (61, 1), (63, 1)] }, { coefficient := 1, powers := [(34, 1), (40, 1), (55, 1), (57, 1), (64, 1)] }, { coefficient := 1, powers := [(34, 1), (40, 1), (57, 1), (58, 1), (61, 1)] }, { coefficient := 1, powers := [(34, 1), (43, 1), (54, 1), (55, 1), (64, 1)] }, { coefficient := 1, powers := [(34, 1), (43, 1), (54, 1), (58, 1), (61, 1)] }]
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
    ¬ ∀ index : Fin 18,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.X5Case8Tree.LeafB1.selectedHasNoCommonZero

end Krenn.X5Case8Tree.LeafB1
