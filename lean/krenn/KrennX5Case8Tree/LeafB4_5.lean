import KrennSparseCertificate

/-! Selected core of a strict exact certificate over a frozen system. -/

namespace Krenn.X5Case8Tree.LeafB4_5

open Krenn.SparseCertificate
open MvPolynomial

def sourceSystemFileSHA256 : String := "743014a8716ad36a1a61fad379a63a3e282d929b74e6c1bead5782ac3cd677b7"
def sourceSystemSemanticSHA256 : String := "448be6ab4d9958c55e356b808745ea953056009449fa89fef9b7a5e422db5545"
def certificateSHA256 : String := "de6a2c46fb5eff8278ba1b2dfab8132d4c38bb7b8f5cb95471de6d09322ffdaf"
def sourceEquationCount : Nat := 681

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedIndices : Fin 25 → Fin 681 := ![
  0,
  16,
  30,
  37,
  48,
  49,
  51,
  53,
  412,
  414,
  420,
  421,
  422,
  424,
  425,
  426,
  431,
  660,
  661,
  666,
  672,
  674,
  677,
  678,
  680
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 25 → SparsePoly (Fin 73) := ![
  [{ coefficient := 1, powers := [(52, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(39, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(44, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(49, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(49, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(49, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(51, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(32, 1), (39, 1), (57, 1)] }, { coefficient := 1, powers := [(57, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (63, 1)] }, { coefficient := 1, powers := [(17, 1), (57, 1)] }, { coefficient := 1, powers := [(54, 1)] }],
  [{ coefficient := 1, powers := [(15, 1), (63, 1)] }, { coefficient := 1, powers := [(23, 1), (57, 1)] }, { coefficient := 1, powers := [(31, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(35, 1), (64, 1)] }, { coefficient := 1, powers := [(38, 1), (58, 1)] }, { coefficient := 1, powers := [(44, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(35, 1), (67, 1)] }, { coefficient := 1, powers := [(41, 1), (58, 1)] }, { coefficient := 1, powers := [(44, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(37, 1), (69, 1)] }, { coefficient := 1, powers := [(43, 1), (60, 1)] }, { coefficient := 1, powers := [(51, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(38, 1), (67, 1)] }, { coefficient := 1, powers := [(41, 1), (64, 1)] }, { coefficient := 1, powers := [(44, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(40, 1), (69, 1)] }, { coefficient := 1, powers := [(43, 1), (66, 1)] }, { coefficient := 1, powers := [(51, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (57, 1), (64, 1)] }, { coefficient := 1, powers := [(16, 1), (44, 1), (57, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (48, 1), (63, 1)] }, { coefficient := 1, powers := [(17, 1), (48, 1), (57, 1)] }, { coefficient := 1, powers := [(48, 1), (54, 1)] }, { coefficient := 1, powers := [(54, 1), (69, 1)] }, { coefficient := 1, powers := [(57, 1), (66, 1)] }, { coefficient := 1, powers := [(60, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (49, 1), (63, 1)] }, { coefficient := 1, powers := [(17, 1), (49, 1), (57, 1)] }, { coefficient := 1, powers := [(32, 1), (37, 1), (63, 1)] }, { coefficient := 1, powers := [(32, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(32, 1), (43, 1), (54, 1)] }, { coefficient := 1, powers := [(49, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (54, 1), (69, 1)] }, { coefficient := 1, powers := [(1, 1), (57, 1), (66, 1)] }, { coefficient := 1, powers := [(1, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(9, 1), (40, 1), (69, 1)] }, { coefficient := 1, powers := [(9, 1), (43, 1), (66, 1)] }, { coefficient := 1, powers := [(9, 1), (51, 1), (63, 1)] }, { coefficient := 1, powers := [(17, 1), (37, 1), (69, 1)] }, { coefficient := 1, powers := [(17, 1), (43, 1), (60, 1)] }, { coefficient := 1, powers := [(17, 1), (51, 1), (57, 1)] }, { coefficient := 1, powers := [(37, 1), (66, 1)] }, { coefficient := 1, powers := [(40, 1), (60, 1)] }, { coefficient := 1, powers := [(51, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (52, 1), (67, 1)] }, { coefficient := 1, powers := [(0, 1), (55, 1), (64, 1)] }, { coefficient := 1, powers := [(0, 1), (58, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (38, 1), (67, 1)] }, { coefficient := 1, powers := [(8, 1), (41, 1), (64, 1)] }, { coefficient := 1, powers := [(8, 1), (44, 1), (61, 1)] }, { coefficient := 1, powers := [(16, 1), (35, 1), (67, 1)] }, { coefficient := 1, powers := [(16, 1), (41, 1), (58, 1)] }, { coefficient := 1, powers := [(16, 1), (44, 1), (55, 1)] }, { coefficient := 1, powers := [(24, 1), (35, 1), (64, 1)] }, { coefficient := 1, powers := [(24, 1), (38, 1), (58, 1)] }, { coefficient := 1, powers := [(24, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(32, 1), (35, 1), (61, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1), (55, 1)] }, { coefficient := 1, powers := [(32, 1), (41, 1), (52, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(7, 1), (54, 1), (69, 1)] }, { coefficient := 1, powers := [(7, 1), (57, 1), (66, 1)] }, { coefficient := 1, powers := [(7, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(15, 1), (40, 1), (69, 1)] }, { coefficient := 1, powers := [(15, 1), (43, 1), (66, 1)] }, { coefficient := 1, powers := [(15, 1), (51, 1), (63, 1)] }, { coefficient := 1, powers := [(23, 1), (37, 1), (69, 1)] }, { coefficient := 1, powers := [(23, 1), (43, 1), (60, 1)] }, { coefficient := 1, powers := [(23, 1), (51, 1), (57, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1), (66, 1)] }, { coefficient := 1, powers := [(31, 1), (40, 1), (60, 1)] }, { coefficient := 1, powers := [(31, 1), (51, 1), (54, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1), (63, 1)] }, { coefficient := 1, powers := [(34, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(34, 1), (43, 1), (54, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(7, 1)] }],
  [{ coefficient := 1, powers := [(55, 1), (71, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(57, 1), (72, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 25 → SparsePoly (Fin 73) := ![
  [{ coefficient := 1, powers := [(0, 1), (67, 1)] }, { coefficient := 1, powers := [(32, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(32, 1), (35, 1), (37, 1), (61, 1), (69, 1), (71, 1)] }, { coefficient := 1, powers := [(32, 1), (35, 1), (43, 1), (60, 1), (61, 1), (71, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (32, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(16, 1), (55, 1), (72, 1)] }],
  [{ coefficient := -1, powers := [(34, 1), (35, 1), (54, 1), (61, 1), (71, 1)] }],
  [{ coefficient := -1, powers := [(17, 1), (34, 1), (35, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(9, 1), (34, 1), (35, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(15, 1), (32, 1), (35, 1), (61, 1), (63, 1), (71, 1)] }, { coefficient := -1, powers := [(31, 1), (32, 1), (35, 1), (54, 1), (61, 1), (71, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (58, 1), (61, 1), (72, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (31, 1), (32, 1), (35, 1), (48, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(32, 1), (35, 1), (51, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(24, 1)] }],
  [{ coefficient := 1, powers := [(16, 1)] }],
  [{ coefficient := -1, powers := [(17, 1), (31, 1), (32, 1), (35, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(8, 1)] }],
  [{ coefficient := -1, powers := [(9, 1), (31, 1), (32, 1), (35, 1), (61, 1)] }, { coefficient := 1, powers := [(15, 1), (32, 1), (35, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(55, 1), (72, 1)] }],
  [{ coefficient := -1, powers := [(1, 1), (31, 1), (32, 1), (35, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(34, 1), (35, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(31, 1), (32, 1), (35, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(32, 1), (35, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(32, 1), (35, 1), (54, 1), (61, 1), (69, 1)] }, { coefficient := 1, powers := [(32, 1), (35, 1), (57, 1), (61, 1), (66, 1)] }, { coefficient := 1, powers := [(32, 1), (35, 1), (60, 1), (61, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(15, 1), (32, 1), (35, 1), (51, 1), (61, 1), (63, 1)] }, { coefficient := -1, powers := [(23, 1), (32, 1), (35, 1), (37, 1), (61, 1), (69, 1)] }, { coefficient := -1, powers := [(23, 1), (32, 1), (35, 1), (43, 1), (60, 1), (61, 1)] }, { coefficient := 1, powers := [(31, 1), (32, 1), (35, 1), (51, 1), (54, 1), (61, 1)] }, { coefficient := 1, powers := [(34, 1), (35, 1), (49, 1), (54, 1), (61, 1)] }],
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
    (values : Fin 73 → R) :
    ¬ ∀ index : Fin 25,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.X5Case8Tree.LeafB4_5.selectedHasNoCommonZero

end Krenn.X5Case8Tree.LeafB4_5
