import KrennSparseCertificate

/-! Selected core of a strict exact certificate over a frozen system. -/

namespace Krenn.X5Case8Tree.LeafB6_3

open Krenn.SparseCertificate
open MvPolynomial

def sourceSystemFileSHA256 : String := "c17d5f819bc3c0eeb92f3692aae75e26dc751ecdae5dca93a161e148b16e40ff"
def sourceSystemSemanticSHA256 : String := "ce2671f9226a25d376c5cd14b89aafc1023daa5765253a01eab33103a307854b"
def certificateSHA256 : String := "7504ed2aa21428ba792dcaeeb3bb6874213885f8b0d7fba7e0953f431a313628"
def sourceEquationCount : Nat := 681

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedIndices : Fin 21 → Fin 681 := ![
  0,
  8,
  11,
  17,
  38,
  317,
  400,
  412,
  414,
  420,
  421,
  422,
  425,
  433,
  672,
  674,
  675,
  677,
  678,
  679,
  680
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 21 → SparsePoly (Fin 74) := ![
  [{ coefficient := 1, powers := [(52, 1)] }],
  [{ coefficient := 1, powers := [(15, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(44, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (56, 1), (66, 1)] }, { coefficient := 1, powers := [(17, 1), (46, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (49, 1), (56, 1)] }, { coefficient := 1, powers := [(32, 1), (40, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(32, 1), (39, 1), (57, 1)] }, { coefficient := 1, powers := [(57, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (63, 1)] }, { coefficient := 1, powers := [(17, 1), (57, 1)] }, { coefficient := 1, powers := [(54, 1)] }],
  [{ coefficient := 1, powers := [(15, 1), (63, 1)] }, { coefficient := 1, powers := [(23, 1), (57, 1)] }, { coefficient := 1, powers := [(31, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(35, 1), (64, 1)] }, { coefficient := 1, powers := [(38, 1), (58, 1)] }, { coefficient := 1, powers := [(44, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(35, 1), (67, 1)] }, { coefficient := 1, powers := [(41, 1), (58, 1)] }, { coefficient := 1, powers := [(44, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(38, 1), (67, 1)] }, { coefficient := 1, powers := [(41, 1), (64, 1)] }, { coefficient := 1, powers := [(44, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (58, 1), (63, 1)] }, { coefficient := 1, powers := [(8, 1), (44, 1), (63, 1)] }, { coefficient := 1, powers := [(32, 1), (35, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (52, 1), (67, 1)] }, { coefficient := 1, powers := [(0, 1), (55, 1), (64, 1)] }, { coefficient := 1, powers := [(0, 1), (58, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (38, 1), (67, 1)] }, { coefficient := 1, powers := [(8, 1), (41, 1), (64, 1)] }, { coefficient := 1, powers := [(8, 1), (44, 1), (61, 1)] }, { coefficient := 1, powers := [(16, 1), (35, 1), (67, 1)] }, { coefficient := 1, powers := [(16, 1), (41, 1), (58, 1)] }, { coefficient := 1, powers := [(16, 1), (44, 1), (55, 1)] }, { coefficient := 1, powers := [(24, 1), (35, 1), (64, 1)] }, { coefficient := 1, powers := [(24, 1), (38, 1), (58, 1)] }, { coefficient := 1, powers := [(24, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(32, 1), (35, 1), (61, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1), (55, 1)] }, { coefficient := 1, powers := [(32, 1), (41, 1), (52, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(7, 1), (54, 1), (69, 1)] }, { coefficient := 1, powers := [(7, 1), (57, 1), (66, 1)] }, { coefficient := 1, powers := [(7, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(15, 1), (40, 1), (69, 1)] }, { coefficient := 1, powers := [(15, 1), (43, 1), (66, 1)] }, { coefficient := 1, powers := [(15, 1), (51, 1), (63, 1)] }, { coefficient := 1, powers := [(23, 1), (37, 1), (69, 1)] }, { coefficient := 1, powers := [(23, 1), (43, 1), (60, 1)] }, { coefficient := 1, powers := [(23, 1), (51, 1), (57, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1), (66, 1)] }, { coefficient := 1, powers := [(31, 1), (40, 1), (60, 1)] }, { coefficient := 1, powers := [(31, 1), (51, 1), (54, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1), (63, 1)] }, { coefficient := 1, powers := [(34, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(34, 1), (43, 1), (54, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (70, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(7, 1)] }],
  [{ coefficient := 1, powers := [(55, 1)] }],
  [{ coefficient := 1, powers := [(56, 1), (72, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(57, 1), (73, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 21 → SparsePoly (Fin 74) := ![
  [{ coefficient := -1, powers := [(0, 1), (9, 1), (34, 1), (43, 1), (63, 1), (67, 1)] }, { coefficient := 1, powers := [(0, 1), (15, 1), (40, 1), (67, 1), (69, 1)] }, { coefficient := 1, powers := [(0, 1), (15, 1), (43, 1), (66, 1), (67, 1)] }, { coefficient := 1, powers := [(0, 1), (34, 1), (37, 1), (63, 1), (67, 1)] }, { coefficient := -1, powers := [(9, 1), (32, 1), (34, 1), (41, 1), (43, 1), (63, 1)] }, { coefficient := 1, powers := [(15, 1), (32, 1), (40, 1), (41, 1), (69, 1)] }, { coefficient := 1, powers := [(15, 1), (32, 1), (41, 1), (43, 1), (66, 1)] }, { coefficient := 1, powers := [(32, 1), (34, 1), (37, 1), (41, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (40, 1), (58, 1), (69, 1)] }, { coefficient := 1, powers := [(0, 1), (43, 1), (58, 1), (66, 1)] }, { coefficient := 1, powers := [(32, 1), (35, 1), (40, 1), (69, 1)] }, { coefficient := 1, powers := [(32, 1), (35, 1), (43, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(31, 1), (37, 1), (46, 1), (70, 1), (72, 1)] }, { coefficient := 1, powers := [(31, 1), (39, 1), (49, 1), (60, 1), (72, 1)] }, { coefficient := 1, powers := [(34, 1), (39, 1), (49, 1), (57, 1), (72, 1)] }, { coefficient := -1, powers := [(34, 1), (43, 1), (57, 1), (72, 1)] }],
  [{ coefficient := 1, powers := [(37, 1), (69, 1), (72, 1)] }, { coefficient := 1, powers := [(43, 1), (60, 1), (72, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (9, 1), (34, 1), (43, 1), (61, 1)] }, { coefficient := -1, powers := [(8, 1), (34, 1), (37, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(31, 1), (37, 1), (70, 1), (72, 1)] }],
  [{ coefficient := -1, powers := [(31, 1), (39, 1), (60, 1), (72, 1)] }, { coefficient := -1, powers := [(34, 1), (39, 1), (57, 1), (72, 1)] }],
  [{ coefficient := 1, powers := [(31, 1), (40, 1), (60, 1), (73, 1)] }, { coefficient := 1, powers := [(34, 1), (40, 1), (57, 1), (73, 1)] }],
  [{ coefficient := 1, powers := [(34, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(51, 1)] }],
  [{ coefficient := -1, powers := [(9, 1), (24, 1), (34, 1), (43, 1), (63, 1)] }, { coefficient := 1, powers := [(15, 1), (24, 1), (40, 1), (69, 1)] }, { coefficient := 1, powers := [(15, 1), (24, 1), (43, 1), (66, 1)] }, { coefficient := 1, powers := [(24, 1), (34, 1), (37, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(9, 1), (16, 1), (34, 1), (43, 1), (63, 1)] }, { coefficient := 1, powers := [(15, 1), (16, 1), (40, 1), (69, 1)] }, { coefficient := 1, powers := [(15, 1), (16, 1), (43, 1), (66, 1)] }, { coefficient := 1, powers := [(16, 1), (34, 1), (37, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (9, 1), (34, 1), (43, 1), (63, 1)] }, { coefficient := 1, powers := [(8, 1), (15, 1), (40, 1), (69, 1)] }, { coefficient := 1, powers := [(8, 1), (15, 1), (43, 1), (66, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (37, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(9, 1), (34, 1), (43, 1), (61, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (34, 1), (43, 1), (63, 1)] }, { coefficient := -1, powers := [(15, 1), (40, 1), (69, 1)] }, { coefficient := -1, powers := [(15, 1), (43, 1), (66, 1)] }, { coefficient := -1, powers := [(34, 1), (37, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(31, 1), (37, 1), (56, 1), (66, 1), (72, 1)] }],
  [{ coefficient := 1, powers := [(54, 1), (69, 1)] }, { coefficient := 1, powers := [(57, 1), (66, 1)] }, { coefficient := 1, powers := [(60, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (9, 1), (34, 1), (43, 1), (63, 1), (64, 1)] }, { coefficient := 1, powers := [(0, 1), (15, 1), (40, 1), (64, 1), (69, 1)] }, { coefficient := 1, powers := [(0, 1), (15, 1), (43, 1), (64, 1), (66, 1)] }, { coefficient := 1, powers := [(0, 1), (34, 1), (37, 1), (63, 1), (64, 1)] }, { coefficient := -1, powers := [(9, 1), (32, 1), (34, 1), (38, 1), (43, 1), (63, 1)] }, { coefficient := 1, powers := [(15, 1), (32, 1), (38, 1), (40, 1), (69, 1)] }, { coefficient := 1, powers := [(15, 1), (32, 1), (38, 1), (43, 1), (66, 1)] }, { coefficient := 1, powers := [(32, 1), (34, 1), (37, 1), (38, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (34, 1), (43, 1), (57, 1)] }, { coefficient := -1, powers := [(23, 1), (37, 1), (69, 1)] }, { coefficient := -1, powers := [(23, 1), (43, 1), (60, 1)] }, { coefficient := 1, powers := [(31, 1), (32, 1), (39, 1), (40, 1), (60, 1)] }, { coefficient := -1, powers := [(31, 1), (37, 1), (66, 1)] }, { coefficient := 1, powers := [(32, 1), (34, 1), (39, 1), (40, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [(31, 1), (32, 1), (39, 1), (40, 1), (60, 1)] }, { coefficient := -1, powers := [(31, 1), (40, 1), (60, 1)] }, { coefficient := -1, powers := [(32, 1), (34, 1), (39, 1), (40, 1), (57, 1)] }, { coefficient := -1, powers := [(34, 1), (40, 1), (57, 1)] }]
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
    (values : Fin 74 → R) :
    ¬ ∀ index : Fin 21,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.X5Case8Tree.LeafB6_3.selectedHasNoCommonZero

end Krenn.X5Case8Tree.LeafB6_3
