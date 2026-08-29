import KrennSparseCertificate

/-! Selected core of a strict exact certificate over a frozen system. -/

namespace Krenn.X5Case8Tree.LeafB4_6

open Krenn.SparseCertificate
open MvPolynomial

def sourceSystemFileSHA256 : String := "61372b4a41ca502d250f5395b2f46ddd1b48aa98beb941af7fa908bb212f230e"
def sourceSystemSemanticSHA256 : String := "07830f21f440a1c8d34e31b81ff7cb5c2a6be7903cdfafe81556873134760a82"
def certificateSHA256 : String := "8ca0bc3f2cae42b7fb6562746a5010ed1140ae4e4bdbf6da7ab183b242d9ea5f"
def sourceEquationCount : Nat := 681

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedIndices : Fin 25 → Fin 681 := ![
  0,
  1,
  11,
  30,
  46,
  48,
  51,
  399,
  400,
  420,
  421,
  422,
  424,
  425,
  430,
  553,
  570,
  622,
  661,
  672,
  674,
  677,
  678,
  679,
  680
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 25 → SparsePoly (Fin 73) := ![
  [{ coefficient := 1, powers := [(52, 1)] }],
  [{ coefficient := 1, powers := [(53, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(39, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(48, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(49, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(49, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (48, 1), (55, 1)] }, { coefficient := 1, powers := [(55, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (49, 1), (56, 1)] }, { coefficient := 1, powers := [(32, 1), (40, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(15, 1), (63, 1)] }, { coefficient := 1, powers := [(23, 1), (57, 1)] }, { coefficient := 1, powers := [(31, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(35, 1), (64, 1)] }, { coefficient := 1, powers := [(38, 1), (58, 1)] }, { coefficient := 1, powers := [(44, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(35, 1), (67, 1)] }, { coefficient := 1, powers := [(41, 1), (58, 1)] }, { coefficient := 1, powers := [(44, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(37, 1), (69, 1)] }, { coefficient := 1, powers := [(43, 1), (60, 1)] }, { coefficient := 1, powers := [(51, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(38, 1), (67, 1)] }, { coefficient := 1, powers := [(41, 1), (64, 1)] }, { coefficient := 1, powers := [(44, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (56, 1), (64, 1)] }, { coefficient := 1, powers := [(16, 1), (44, 1), (56, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (44, 1), (53, 1)] }, { coefficient := 1, powers := [(44, 1), (56, 1)] }, { coefficient := 1, powers := [(44, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (62, 1)] }, { coefficient := 1, powers := [(25, 1), (39, 1), (58, 1)] }, { coefficient := 1, powers := [(42, 1), (58, 1)] }, { coefficient := 1, powers := [(58, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (39, 1), (67, 1)] }, { coefficient := 1, powers := [(24, 1), (39, 1), (58, 1)] }, { coefficient := 1, powers := [(32, 1), (39, 1), (55, 1)] }, { coefficient := 1, powers := [(55, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (49, 1), (63, 1)] }, { coefficient := 1, powers := [(17, 1), (49, 1), (57, 1)] }, { coefficient := 1, powers := [(32, 1), (37, 1), (63, 1)] }, { coefficient := 1, powers := [(32, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(32, 1), (43, 1), (54, 1)] }, { coefficient := 1, powers := [(49, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (52, 1), (67, 1)] }, { coefficient := 1, powers := [(0, 1), (55, 1), (64, 1)] }, { coefficient := 1, powers := [(0, 1), (58, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (38, 1), (67, 1)] }, { coefficient := 1, powers := [(8, 1), (41, 1), (64, 1)] }, { coefficient := 1, powers := [(8, 1), (44, 1), (61, 1)] }, { coefficient := 1, powers := [(16, 1), (35, 1), (67, 1)] }, { coefficient := 1, powers := [(16, 1), (41, 1), (58, 1)] }, { coefficient := 1, powers := [(16, 1), (44, 1), (55, 1)] }, { coefficient := 1, powers := [(24, 1), (35, 1), (64, 1)] }, { coefficient := 1, powers := [(24, 1), (38, 1), (58, 1)] }, { coefficient := 1, powers := [(24, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(32, 1), (35, 1), (61, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1), (55, 1)] }, { coefficient := 1, powers := [(32, 1), (41, 1), (52, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(7, 1), (54, 1), (69, 1)] }, { coefficient := 1, powers := [(7, 1), (57, 1), (66, 1)] }, { coefficient := 1, powers := [(7, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(15, 1), (40, 1), (69, 1)] }, { coefficient := 1, powers := [(15, 1), (43, 1), (66, 1)] }, { coefficient := 1, powers := [(15, 1), (51, 1), (63, 1)] }, { coefficient := 1, powers := [(23, 1), (37, 1), (69, 1)] }, { coefficient := 1, powers := [(23, 1), (43, 1), (60, 1)] }, { coefficient := 1, powers := [(23, 1), (51, 1), (57, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1), (66, 1)] }, { coefficient := 1, powers := [(31, 1), (40, 1), (60, 1)] }, { coefficient := 1, powers := [(31, 1), (51, 1), (54, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1), (63, 1)] }, { coefficient := 1, powers := [(34, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(34, 1), (43, 1), (54, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(7, 1)] }],
  [{ coefficient := 1, powers := [(55, 1), (71, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(56, 1), (72, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(57, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 25 → SparsePoly (Fin 73) := ![
  [{ coefficient := 1, powers := [(0, 1), (67, 1)] }, { coefficient := 1, powers := [(32, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (25, 1), (44, 1), (55, 1), (72, 1)] }],
  [{ coefficient := -1, powers := [(15, 1), (16, 1), (35, 1), (39, 1), (49, 1), (62, 1), (67, 1), (69, 1), (72, 2)] }, { coefficient := -1, powers := [(15, 1), (35, 1), (49, 1), (61, 1), (69, 1), (72, 1)] }, { coefficient := -1, powers := [(16, 1), (31, 1), (35, 1), (39, 1), (49, 1), (60, 1), (62, 1), (67, 1), (72, 2)] }, { coefficient := -1, powers := [(31, 1), (35, 1), (49, 1), (60, 1), (61, 1), (72, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (8, 1), (61, 1), (67, 1), (71, 1)] }, { coefficient := -1, powers := [(0, 1), (24, 1), (58, 1), (61, 1), (71, 1)] }, { coefficient := -1, powers := [(0, 1), (32, 1), (55, 1), (61, 1), (71, 1)] }, { coefficient := 1, powers := [(8, 1), (16, 1), (41, 1), (56, 1), (67, 1), (71, 1), (72, 1)] }, { coefficient := 1, powers := [(8, 1), (16, 1), (41, 1), (62, 1), (67, 1), (71, 1), (72, 1)] }, { coefficient := -1, powers := [(8, 1), (16, 1), (41, 1), (67, 1), (71, 1)] }, { coefficient := 1, powers := [(16, 1), (24, 1), (35, 1), (62, 1), (67, 1), (71, 1), (72, 1)] }, { coefficient := 1, powers := [(16, 1), (24, 1), (41, 1), (56, 1), (58, 1), (71, 1), (72, 1)] }, { coefficient := 1, powers := [(16, 1), (24, 1), (41, 1), (58, 1), (62, 1), (71, 1), (72, 1)] }, { coefficient := -1, powers := [(16, 1), (24, 1), (41, 1), (58, 1), (71, 1)] }, { coefficient := -1, powers := [(16, 1), (25, 1), (35, 1), (39, 1), (67, 2), (71, 1), (72, 1)] }, { coefficient := 1, powers := [(16, 1), (32, 1), (41, 1), (55, 1), (56, 1), (71, 1), (72, 1)] }, { coefficient := 1, powers := [(16, 1), (32, 1), (41, 1), (55, 1), (62, 1), (71, 1), (72, 1)] }, { coefficient := -1, powers := [(16, 1), (32, 1), (41, 1), (55, 1), (71, 1)] }, { coefficient := -1, powers := [(16, 1), (35, 1), (42, 1), (67, 2), (71, 1), (72, 1)] }, { coefficient := -1, powers := [(16, 1), (35, 1), (62, 1), (67, 2), (71, 1), (72, 1)] }],
  [{ coefficient := -1, powers := [(15, 1), (16, 1), (17, 1), (32, 1), (35, 1), (39, 1), (43, 1), (62, 1), (67, 1), (71, 1), (72, 1)] }, { coefficient := -1, powers := [(15, 1), (17, 1), (32, 1), (35, 1), (43, 1), (61, 1), (71, 1)] }, { coefficient := -1, powers := [(16, 1), (17, 1), (31, 1), (32, 1), (35, 1), (37, 1), (39, 1), (62, 1), (67, 1), (71, 1), (72, 1)] }, { coefficient := -1, powers := [(17, 1), (31, 1), (32, 1), (35, 1), (37, 1), (61, 1), (71, 1)] }],
  [{ coefficient := -1, powers := [(16, 1), (34, 1), (35, 1), (39, 1), (54, 1), (62, 1), (67, 1), (71, 1), (72, 1)] }, { coefficient := -1, powers := [(34, 1), (35, 1), (54, 1), (61, 1), (71, 1)] }],
  [{ coefficient := -1, powers := [(9, 1), (16, 1), (34, 1), (35, 1), (39, 1), (62, 1), (67, 1), (72, 1)] }, { coefficient := -1, powers := [(9, 1), (34, 1), (35, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(15, 1), (16, 1), (32, 1), (35, 1), (39, 1), (43, 1), (62, 1), (67, 1), (71, 1), (72, 1)] }, { coefficient := 1, powers := [(15, 1), (32, 1), (35, 1), (43, 1), (61, 1), (71, 1)] }, { coefficient := 1, powers := [(16, 1), (31, 1), (32, 1), (35, 1), (37, 1), (39, 1), (62, 1), (67, 1), (71, 1), (72, 1)] }, { coefficient := 1, powers := [(31, 1), (32, 1), (35, 1), (37, 1), (61, 1), (71, 1)] }],
  [{ coefficient := 1, powers := [(15, 1), (16, 1), (35, 1), (39, 1), (62, 1), (67, 1), (69, 1), (72, 2)] }, { coefficient := 1, powers := [(15, 1), (35, 1), (61, 1), (69, 1), (72, 1)] }, { coefficient := 1, powers := [(16, 1), (31, 1), (35, 1), (39, 1), (60, 1), (62, 1), (67, 1), (72, 2)] }, { coefficient := 1, powers := [(31, 1), (35, 1), (60, 1), (61, 1), (72, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (32, 1), (35, 1), (39, 1), (51, 1), (62, 1), (67, 1), (72, 1)] }, { coefficient := 1, powers := [(32, 1), (35, 1), (51, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(24, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (56, 1), (72, 1)] }, { coefficient := 1, powers := [(16, 1), (62, 1), (72, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (23, 1), (32, 1), (35, 1), (39, 1), (62, 1), (67, 1), (72, 1)] }, { coefficient := 1, powers := [(23, 1), (32, 1), (35, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(8, 1)] }],
  [{ coefficient := 1, powers := [(55, 1), (72, 1)] }],
  [{ coefficient := -1, powers := [(16, 1), (55, 1), (72, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (35, 1), (39, 1), (67, 2), (71, 1), (72, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (58, 1), (61, 1), (71, 1)] }, { coefficient := -1, powers := [(16, 1), (35, 1), (62, 1), (67, 1), (71, 1), (72, 1)] }, { coefficient := -1, powers := [(16, 1), (41, 1), (56, 1), (58, 1), (71, 1), (72, 1)] }, { coefficient := -1, powers := [(16, 1), (41, 1), (58, 1), (62, 1), (71, 1), (72, 1)] }, { coefficient := 1, powers := [(16, 1), (41, 1), (58, 1), (71, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (34, 1), (35, 1), (39, 1), (62, 1), (67, 1), (72, 1)] }, { coefficient := 1, powers := [(34, 1), (35, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(16, 1), (32, 1), (35, 1), (39, 1), (62, 1), (67, 1), (72, 1)] }, { coefficient := -1, powers := [(32, 1), (35, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (32, 1), (35, 1), (39, 1), (54, 1), (62, 1), (67, 1), (69, 1), (72, 1)] }, { coefficient := 1, powers := [(16, 1), (32, 1), (35, 1), (39, 1), (60, 1), (62, 1), (63, 1), (67, 1), (72, 1)] }, { coefficient := 1, powers := [(32, 1), (35, 1), (54, 1), (61, 1), (69, 1)] }, { coefficient := 1, powers := [(32, 1), (35, 1), (60, 1), (61, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (58, 1), (61, 1)] }, { coefficient := -1, powers := [(15, 1), (16, 1), (32, 1), (35, 1), (39, 1), (43, 1), (62, 1), (66, 1), (67, 1), (72, 1)] }, { coefficient := -1, powers := [(15, 1), (32, 1), (35, 1), (43, 1), (61, 1), (66, 1)] }, { coefficient := -1, powers := [(16, 1), (31, 1), (32, 1), (35, 1), (37, 1), (39, 1), (62, 1), (66, 1), (67, 1), (72, 1)] }, { coefficient := 1, powers := [(16, 1), (32, 1), (35, 1), (39, 1), (62, 1), (67, 1), (72, 1)] }, { coefficient := 1, powers := [(16, 1), (34, 1), (35, 1), (39, 1), (49, 1), (54, 1), (62, 1), (67, 1), (72, 1)] }, { coefficient := 1, powers := [(16, 1), (35, 1), (62, 1), (67, 1), (72, 1)] }, { coefficient := 1, powers := [(16, 1), (41, 1), (56, 1), (58, 1), (72, 1)] }, { coefficient := 1, powers := [(16, 1), (41, 1), (58, 1), (62, 1), (72, 1)] }, { coefficient := -1, powers := [(16, 1), (41, 1), (58, 1)] }, { coefficient := -1, powers := [(31, 1), (32, 1), (35, 1), (37, 1), (61, 1), (66, 1)] }, { coefficient := 1, powers := [(34, 1), (35, 1), (49, 1), (54, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (55, 1), (64, 1)] }, { coefficient := -1, powers := [(15, 1), (16, 1), (32, 1), (35, 1), (39, 1), (40, 1), (62, 1), (67, 1), (69, 1), (72, 1)] }, { coefficient := -1, powers := [(15, 1), (32, 1), (35, 1), (40, 1), (61, 1), (69, 1)] }, { coefficient := -1, powers := [(16, 1), (31, 1), (32, 1), (35, 1), (39, 1), (40, 1), (60, 1), (62, 1), (67, 1), (72, 1)] }, { coefficient := -1, powers := [(16, 1), (35, 1), (67, 1)] }, { coefficient := -1, powers := [(16, 1), (44, 1), (55, 1)] }, { coefficient := -1, powers := [(31, 1), (32, 1), (35, 1), (40, 1), (60, 1), (61, 1)] }, { coefficient := -1, powers := [(32, 1), (38, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (16, 1), (32, 1), (35, 1), (39, 1), (62, 1), (66, 1), (67, 1), (72, 1)] }, { coefficient := 1, powers := [(7, 1), (32, 1), (35, 1), (61, 1), (66, 1)] }, { coefficient := -1, powers := [(16, 1), (17, 1), (34, 1), (35, 1), (39, 1), (49, 1), (62, 1), (67, 1), (72, 1)] }, { coefficient := -1, powers := [(16, 1), (23, 1), (32, 1), (35, 1), (39, 1), (51, 1), (62, 1), (67, 1), (72, 1)] }, { coefficient := -1, powers := [(17, 1), (34, 1), (35, 1), (49, 1), (61, 1)] }, { coefficient := -1, powers := [(23, 1), (32, 1), (35, 1), (51, 1), (61, 1)] }]
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
    (values : Fin 73 → R) :
    ¬ ∀ index : Fin 25,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.X5Case8Tree.LeafB4_6.selectedHasNoCommonZero

end Krenn.X5Case8Tree.LeafB4_6
