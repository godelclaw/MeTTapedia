import KrennSparseCertificate

/-! Selected core of a strict exact certificate over a frozen system. -/

namespace Krenn.X5Case8Tree.LeafB4_7

open Krenn.SparseCertificate
open MvPolynomial

def sourceSystemFileSHA256 : String := "249d4ed7345aeb4e67dd5cc0fa4a15a9c8729d24d91b621a634c2cf3c1d064b3"
def sourceSystemSemanticSHA256 : String := "b72052394acb8b5864102b77904fbf0ea96939a79b8cfe30cf1043323d3614b0"
def certificateSHA256 : String := "aed1e4b856f8fc9150791bdf27b1fd94084fc415311f00c23e043513635500b7"
def sourceEquationCount : Nat := 681

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedIndices : Fin 24 → Fin 681 := ![
  0,
  11,
  16,
  30,
  37,
  46,
  48,
  49,
  51,
  399,
  400,
  412,
  420,
  421,
  422,
  425,
  431,
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
def selectedEquations : Fin 24 → SparsePoly (Fin 74) := ![
  [{ coefficient := 1, powers := [(52, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(39, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(44, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(48, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(49, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(49, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(49, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (48, 1), (55, 1)] }, { coefficient := 1, powers := [(55, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (49, 1), (56, 1)] }, { coefficient := 1, powers := [(32, 1), (40, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(32, 1), (39, 1), (57, 1)] }, { coefficient := 1, powers := [(57, 1)] }],
  [{ coefficient := 1, powers := [(15, 1), (63, 1)] }, { coefficient := 1, powers := [(23, 1), (57, 1)] }, { coefficient := 1, powers := [(31, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(35, 1), (64, 1)] }, { coefficient := 1, powers := [(38, 1), (58, 1)] }, { coefficient := 1, powers := [(44, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(35, 1), (67, 1)] }, { coefficient := 1, powers := [(41, 1), (58, 1)] }, { coefficient := 1, powers := [(44, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(38, 1), (67, 1)] }, { coefficient := 1, powers := [(41, 1), (64, 1)] }, { coefficient := 1, powers := [(44, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (57, 1), (64, 1)] }, { coefficient := 1, powers := [(16, 1), (44, 1), (57, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (49, 1), (63, 1)] }, { coefficient := 1, powers := [(17, 1), (49, 1), (57, 1)] }, { coefficient := 1, powers := [(32, 1), (37, 1), (63, 1)] }, { coefficient := 1, powers := [(32, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(32, 1), (43, 1), (54, 1)] }, { coefficient := 1, powers := [(49, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (52, 1), (67, 1)] }, { coefficient := 1, powers := [(0, 1), (55, 1), (64, 1)] }, { coefficient := 1, powers := [(0, 1), (58, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (38, 1), (67, 1)] }, { coefficient := 1, powers := [(8, 1), (41, 1), (64, 1)] }, { coefficient := 1, powers := [(8, 1), (44, 1), (61, 1)] }, { coefficient := 1, powers := [(16, 1), (35, 1), (67, 1)] }, { coefficient := 1, powers := [(16, 1), (41, 1), (58, 1)] }, { coefficient := 1, powers := [(16, 1), (44, 1), (55, 1)] }, { coefficient := 1, powers := [(24, 1), (35, 1), (64, 1)] }, { coefficient := 1, powers := [(24, 1), (38, 1), (58, 1)] }, { coefficient := 1, powers := [(24, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(32, 1), (35, 1), (61, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1), (55, 1)] }, { coefficient := 1, powers := [(32, 1), (41, 1), (52, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(7, 1), (54, 1), (69, 1)] }, { coefficient := 1, powers := [(7, 1), (57, 1), (66, 1)] }, { coefficient := 1, powers := [(7, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(15, 1), (40, 1), (69, 1)] }, { coefficient := 1, powers := [(15, 1), (43, 1), (66, 1)] }, { coefficient := 1, powers := [(15, 1), (51, 1), (63, 1)] }, { coefficient := 1, powers := [(23, 1), (37, 1), (69, 1)] }, { coefficient := 1, powers := [(23, 1), (43, 1), (60, 1)] }, { coefficient := 1, powers := [(23, 1), (51, 1), (57, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1), (66, 1)] }, { coefficient := 1, powers := [(31, 1), (40, 1), (60, 1)] }, { coefficient := 1, powers := [(31, 1), (51, 1), (54, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1), (63, 1)] }, { coefficient := 1, powers := [(34, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(34, 1), (43, 1), (54, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(7, 1)] }],
  [{ coefficient := 1, powers := [(55, 1), (71, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(56, 1), (72, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(57, 1), (73, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 24 → SparsePoly (Fin 74) := ![
  [{ coefficient := 1, powers := [(0, 1), (67, 1)] }, { coefficient := 1, powers := [(32, 1), (41, 1)] }],
  [{ coefficient := -1, powers := [(15, 1), (35, 1), (49, 1), (61, 1), (69, 1), (72, 1)] }, { coefficient := -1, powers := [(31, 1), (35, 1), (49, 1), (60, 1), (61, 1), (72, 1)] }],
  [{ coefficient := 1, powers := [(32, 1), (35, 1), (37, 1), (61, 1), (69, 1), (71, 1)] }, { coefficient := 1, powers := [(32, 1), (35, 1), (43, 1), (60, 1), (61, 1), (71, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (32, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(16, 1), (55, 1), (73, 1)] }],
  [{ coefficient := -1, powers := [(15, 1), (17, 1), (32, 1), (35, 1), (43, 1), (61, 1), (71, 1)] }, { coefficient := -1, powers := [(17, 1), (31, 1), (32, 1), (35, 1), (37, 1), (61, 1), (71, 1)] }],
  [{ coefficient := -1, powers := [(34, 1), (35, 1), (54, 1), (61, 1), (71, 1)] }],
  [{ coefficient := -1, powers := [(17, 1), (34, 1), (35, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(9, 1), (34, 1), (35, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(15, 1), (32, 1), (35, 1), (43, 1), (61, 1), (71, 1)] }, { coefficient := 1, powers := [(31, 1), (32, 1), (35, 1), (37, 1), (61, 1), (71, 1)] }],
  [{ coefficient := 1, powers := [(15, 1), (35, 1), (61, 1), (69, 1), (72, 1)] }, { coefficient := 1, powers := [(31, 1), (35, 1), (60, 1), (61, 1), (72, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (58, 1), (61, 1), (73, 1)] }],
  [{ coefficient := 1, powers := [(32, 1), (35, 1), (51, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(24, 1)] }],
  [{ coefficient := 1, powers := [(16, 1)] }],
  [{ coefficient := 1, powers := [(8, 1)] }],
  [{ coefficient := 1, powers := [(55, 1), (73, 1)] }],
  [{ coefficient := 1, powers := [(34, 1), (35, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(32, 1), (35, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(32, 1), (35, 1), (54, 1), (61, 1), (69, 1)] }, { coefficient := 1, powers := [(32, 1), (35, 1), (57, 1), (61, 1), (66, 1)] }, { coefficient := 1, powers := [(32, 1), (35, 1), (60, 1), (61, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(15, 1), (32, 1), (35, 1), (43, 1), (61, 1), (66, 1)] }, { coefficient := -1, powers := [(23, 1), (32, 1), (35, 1), (37, 1), (61, 1), (69, 1)] }, { coefficient := -1, powers := [(23, 1), (32, 1), (35, 1), (43, 1), (60, 1), (61, 1)] }, { coefficient := -1, powers := [(31, 1), (32, 1), (35, 1), (37, 1), (61, 1), (66, 1)] }, { coefficient := 1, powers := [(34, 1), (35, 1), (49, 1), (54, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(15, 1), (32, 1), (35, 1), (40, 1), (61, 1), (69, 1)] }, { coefficient := -1, powers := [(31, 1), (32, 1), (35, 1), (40, 1), (60, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (32, 1), (39, 1), (58, 1), (61, 1)] }, { coefficient := -1, powers := [(0, 1), (55, 1), (64, 1)] }, { coefficient := -1, powers := [(0, 1), (58, 1), (61, 1)] }, { coefficient := -1, powers := [(32, 1), (38, 1), (55, 1)] }]
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
    ¬ ∀ index : Fin 24,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.X5Case8Tree.LeafB4_7.selectedHasNoCommonZero

end Krenn.X5Case8Tree.LeafB4_7
