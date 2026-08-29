import KrennSparseCertificate

/-! Selected core of a strict exact certificate over a frozen system. -/

namespace Krenn.X5ResidualCase863.LeafB5

open Krenn.SparseCertificate
open MvPolynomial

def sourceSystemFileSHA256 : String := "05bda10be78710d0caad3c4aee0af087c14e464a19fcef1fd23ecc796eca4977"
def sourceSystemSemanticSHA256 : String := "a7da73d553ba713334973fd71cf891da5e9f8d829428f53bc1130eeaaea9d9fa"
def certificateSHA256 : String := "5857333a63a7dcc06ab235a407570c256b64fde4ab0dca1129792c2bd44eb706"
def sourceEquationCount : Nat := 678

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedIndices : Fin 20 → Fin 678 := ![
  7,
  50,
  51,
  53,
  55,
  414,
  416,
  421,
  422,
  423,
  424,
  425,
  659,
  661,
  662,
  672,
  674,
  675,
  676,
  677
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 20 → SparsePoly (Fin 72) := ![
  [{ coefficient := 1, powers := [(15, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(50, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(50, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(50, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(51, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (61, 1)] }, { coefficient := 1, powers := [(16, 1), (55, 1)] }, { coefficient := 1, powers := [(24, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (63, 1)] }, { coefficient := 1, powers := [(18, 1), (57, 1)] }, { coefficient := 1, powers := [(26, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(35, 1), (64, 1)] }, { coefficient := 1, powers := [(38, 1), (58, 1)] }, { coefficient := 1, powers := [(44, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(35, 1), (67, 1)] }, { coefficient := 1, powers := [(41, 1), (58, 1)] }, { coefficient := 1, powers := [(44, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(37, 1), (66, 1)] }, { coefficient := 1, powers := [(40, 1), (60, 1)] }, { coefficient := 1, powers := [(51, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(37, 1), (69, 1)] }, { coefficient := 1, powers := [(43, 1), (60, 1)] }, { coefficient := 1, powers := [(51, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(38, 1), (67, 1)] }, { coefficient := 1, powers := [(41, 1), (64, 1)] }, { coefficient := 1, powers := [(44, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (47, 1), (61, 1)] }, { coefficient := 1, powers := [(16, 1), (47, 1), (55, 1)] }, { coefficient := 1, powers := [(24, 1), (47, 1), (52, 1)] }, { coefficient := 1, powers := [(52, 1), (67, 1)] }, { coefficient := 1, powers := [(55, 1), (64, 1)] }, { coefficient := 1, powers := [(58, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (49, 1), (63, 1)] }, { coefficient := 1, powers := [(18, 1), (49, 1), (57, 1)] }, { coefficient := 1, powers := [(26, 1), (49, 1), (54, 1)] }, { coefficient := 1, powers := [(54, 1), (69, 1)] }, { coefficient := 1, powers := [(57, 1), (66, 1)] }, { coefficient := 1, powers := [(60, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (50, 1), (63, 1)] }, { coefficient := 1, powers := [(18, 1), (50, 1), (57, 1)] }, { coefficient := 1, powers := [(26, 1), (50, 1), (54, 1)] }, { coefficient := 1, powers := [(32, 1), (37, 1), (63, 1)] }, { coefficient := 1, powers := [(32, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(32, 1), (43, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (52, 1), (67, 1)] }, { coefficient := 1, powers := [(0, 1), (55, 1), (64, 1)] }, { coefficient := 1, powers := [(0, 1), (58, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (38, 1), (67, 1)] }, { coefficient := 1, powers := [(8, 1), (41, 1), (64, 1)] }, { coefficient := 1, powers := [(8, 1), (44, 1), (61, 1)] }, { coefficient := 1, powers := [(16, 1), (35, 1), (67, 1)] }, { coefficient := 1, powers := [(16, 1), (41, 1), (58, 1)] }, { coefficient := 1, powers := [(16, 1), (44, 1), (55, 1)] }, { coefficient := 1, powers := [(24, 1), (35, 1), (64, 1)] }, { coefficient := 1, powers := [(24, 1), (38, 1), (58, 1)] }, { coefficient := 1, powers := [(24, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(32, 1), (35, 1), (61, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1), (55, 1)] }, { coefficient := 1, powers := [(32, 1), (41, 1), (52, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(7, 1), (54, 1), (69, 1)] }, { coefficient := 1, powers := [(7, 1), (57, 1), (66, 1)] }, { coefficient := 1, powers := [(7, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(15, 1), (40, 1), (69, 1)] }, { coefficient := 1, powers := [(15, 1), (43, 1), (66, 1)] }, { coefficient := 1, powers := [(15, 1), (51, 1), (63, 1)] }, { coefficient := 1, powers := [(23, 1), (37, 1), (69, 1)] }, { coefficient := 1, powers := [(23, 1), (43, 1), (60, 1)] }, { coefficient := 1, powers := [(23, 1), (51, 1), (57, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1), (66, 1)] }, { coefficient := 1, powers := [(31, 1), (40, 1), (60, 1)] }, { coefficient := 1, powers := [(31, 1), (51, 1), (54, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1), (63, 1)] }, { coefficient := 1, powers := [(34, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(34, 1), (43, 1), (54, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(52, 1), (70, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(55, 1)] }],
  [{ coefficient := 1, powers := [(61, 1), (71, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 20 → SparsePoly (Fin 72) := ![
  [{ coefficient := 1, powers := [(32, 1), (35, 1), (40, 1), (61, 1), (69, 1), (71, 1)] }, { coefficient := 1, powers := [(32, 1), (35, 1), (43, 1), (61, 1), (66, 1), (71, 1)] }, { coefficient := 1, powers := [(32, 1), (40, 1), (41, 1), (52, 1), (69, 1), (71, 1)] }, { coefficient := 1, powers := [(32, 1), (41, 1), (43, 1), (52, 1), (66, 1), (71, 1)] }],
  [{ coefficient := -1, powers := [(10, 1), (34, 1), (35, 1), (61, 1), (63, 1), (70, 1)] }, { coefficient := -1, powers := [(10, 1), (34, 1), (41, 1), (52, 1), (63, 1), (70, 1)] }],
  [{ coefficient := -1, powers := [(26, 1), (34, 1), (35, 1), (61, 1)] }, { coefficient := -1, powers := [(26, 1), (34, 1), (41, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(18, 1), (34, 1), (35, 1), (61, 1)] }, { coefficient := -1, powers := [(18, 1), (34, 1), (41, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(15, 1), (32, 1), (35, 1), (61, 1), (63, 1), (70, 1)] }, { coefficient := 1, powers := [(15, 1), (32, 1), (41, 1), (52, 1), (63, 1), (70, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (47, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (32, 1), (35, 1), (49, 1), (61, 1)] }, { coefficient := -1, powers := [(7, 1), (32, 1), (41, 1), (49, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(24, 1)] }],
  [{ coefficient := 1, powers := [(16, 1)] }],
  [{ coefficient := 1, powers := [(31, 1), (32, 1), (35, 1), (61, 1)] }, { coefficient := 1, powers := [(31, 1), (32, 1), (41, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (32, 1), (35, 1), (61, 1)] }, { coefficient := 1, powers := [(23, 1), (32, 1), (41, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(8, 1)] }],
  [{ coefficient := 1, powers := [(0, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (32, 1), (35, 1), (61, 1)] }, { coefficient := 1, powers := [(7, 1), (32, 1), (41, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(34, 1), (35, 1), (61, 1)] }, { coefficient := 1, powers := [(34, 1), (41, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(32, 1), (35, 1), (61, 1)] }, { coefficient := -1, powers := [(32, 1), (41, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (34, 1), (35, 1), (50, 1), (61, 1), (63, 1)] }, { coefficient := 1, powers := [(10, 1), (34, 1), (41, 1), (50, 1), (52, 1), (63, 1)] }, { coefficient := -1, powers := [(15, 1), (32, 1), (35, 1), (51, 1), (61, 1), (63, 1)] }, { coefficient := -1, powers := [(15, 1), (32, 1), (41, 1), (51, 1), (52, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(32, 1), (38, 1)] }],
  [{ coefficient := -1, powers := [(15, 1), (32, 1), (35, 1), (40, 1), (61, 1), (69, 1)] }, { coefficient := -1, powers := [(15, 1), (32, 1), (35, 1), (43, 1), (61, 1), (66, 1)] }, { coefficient := -1, powers := [(15, 1), (32, 1), (40, 1), (41, 1), (52, 1), (69, 1)] }, { coefficient := -1, powers := [(15, 1), (32, 1), (41, 1), (43, 1), (52, 1), (66, 1)] }]
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
    (values : Fin 72 → R) :
    ¬ ∀ index : Fin 20,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.X5ResidualCase863.LeafB5.selectedHasNoCommonZero

end Krenn.X5ResidualCase863.LeafB5
