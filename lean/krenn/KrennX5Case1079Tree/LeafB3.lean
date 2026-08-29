import KrennSparseCertificate

/-! Selected core of a strict exact certificate over a frozen system. -/

namespace Krenn.X5Case1079Tree.LeafB3

open Krenn.SparseCertificate
open MvPolynomial

def sourceSystemFileSHA256 : String := "0607231e71f05fc0a44cfc26986098e210e9d42b85f783177f7747f5fbfd7928"
def sourceSystemSemanticSHA256 : String := "8da3cc0c65f648c75c197e6ee840b3d652fa6bb1da893034f271054b5560eb2f"
def certificateSHA256 : String := "fb6c04ef709bd72fee8183a09eb5cb4a3201edfc89791334e9d2c7caa928c79a"
def sourceEquationCount : Nat := 678

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedIndices : Fin 16 → Fin 678 := ![
  1,
  414,
  416,
  420,
  421,
  423,
  424,
  425,
  427,
  659,
  661,
  665,
  669,
  672,
  674,
  675
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 16 → SparsePoly (Fin 72) := ![
  [{ coefficient := 1, powers := [(63, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (61, 1)] }, { coefficient := 1, powers := [(16, 1), (55, 1)] }, { coefficient := 1, powers := [(24, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (63, 1)] }, { coefficient := 1, powers := [(18, 1), (57, 1)] }, { coefficient := 1, powers := [(26, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (55, 1)] }, { coefficient := 1, powers := [(30, 1), (52, 1)] }, { coefficient := 1, powers := [(61, 1)] }],
  [{ coefficient := 1, powers := [(35, 1), (64, 1)] }, { coefficient := 1, powers := [(38, 1), (58, 1)] }, { coefficient := 1, powers := [(44, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(35, 1), (67, 1)] }, { coefficient := 1, powers := [(41, 1), (58, 1)] }, { coefficient := 1, powers := [(44, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(37, 1), (66, 1)] }, { coefficient := 1, powers := [(40, 1), (60, 1)] }, { coefficient := 1, powers := [(51, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(37, 1), (69, 1)] }, { coefficient := 1, powers := [(43, 1), (60, 1)] }, { coefficient := 1, powers := [(51, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(40, 1), (69, 1)] }, { coefficient := 1, powers := [(43, 1), (66, 1)] }, { coefficient := 1, powers := [(51, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (47, 1), (61, 1)] }, { coefficient := 1, powers := [(16, 1), (47, 1), (55, 1)] }, { coefficient := 1, powers := [(24, 1), (47, 1), (52, 1)] }, { coefficient := 1, powers := [(52, 1), (67, 1)] }, { coefficient := 1, powers := [(55, 1), (64, 1)] }, { coefficient := 1, powers := [(58, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (49, 1), (63, 1)] }, { coefficient := 1, powers := [(18, 1), (49, 1), (57, 1)] }, { coefficient := 1, powers := [(26, 1), (49, 1), (54, 1)] }, { coefficient := 1, powers := [(54, 1), (69, 1)] }, { coefficient := 1, powers := [(57, 1), (66, 1)] }, { coefficient := 1, powers := [(60, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (46, 1), (55, 1)] }, { coefficient := 1, powers := [(30, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(34, 1), (35, 1), (61, 1)] }, { coefficient := 1, powers := [(34, 1), (38, 1), (55, 1)] }, { coefficient := 1, powers := [(34, 1), (41, 1), (52, 1)] }, { coefficient := 1, powers := [(46, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (52, 1), (67, 1)] }, { coefficient := 1, powers := [(5, 1), (55, 1), (64, 1)] }, { coefficient := 1, powers := [(5, 1), (58, 1), (61, 1)] }, { coefficient := 1, powers := [(22, 1), (35, 1), (67, 1)] }, { coefficient := 1, powers := [(22, 1), (41, 1), (58, 1)] }, { coefficient := 1, powers := [(22, 1), (44, 1), (55, 1)] }, { coefficient := 1, powers := [(30, 1), (35, 1), (64, 1)] }, { coefficient := 1, powers := [(30, 1), (38, 1), (58, 1)] }, { coefficient := 1, powers := [(30, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(38, 1), (67, 1)] }, { coefficient := 1, powers := [(41, 1), (64, 1)] }, { coefficient := 1, powers := [(44, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (52, 1), (67, 1)] }, { coefficient := 1, powers := [(0, 1), (55, 1), (64, 1)] }, { coefficient := 1, powers := [(0, 1), (58, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (38, 1), (67, 1)] }, { coefficient := 1, powers := [(8, 1), (41, 1), (64, 1)] }, { coefficient := 1, powers := [(8, 1), (44, 1), (61, 1)] }, { coefficient := 1, powers := [(16, 1), (35, 1), (67, 1)] }, { coefficient := 1, powers := [(16, 1), (41, 1), (58, 1)] }, { coefficient := 1, powers := [(16, 1), (44, 1), (55, 1)] }, { coefficient := 1, powers := [(24, 1), (35, 1), (64, 1)] }, { coefficient := 1, powers := [(24, 1), (38, 1), (58, 1)] }, { coefficient := 1, powers := [(24, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(32, 1), (35, 1), (61, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1), (55, 1)] }, { coefficient := 1, powers := [(32, 1), (41, 1), (52, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(7, 1), (54, 1), (69, 1)] }, { coefficient := 1, powers := [(7, 1), (57, 1), (66, 1)] }, { coefficient := 1, powers := [(7, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(15, 1), (40, 1), (69, 1)] }, { coefficient := 1, powers := [(15, 1), (43, 1), (66, 1)] }, { coefficient := 1, powers := [(15, 1), (51, 1), (63, 1)] }, { coefficient := 1, powers := [(23, 1), (37, 1), (69, 1)] }, { coefficient := 1, powers := [(23, 1), (43, 1), (60, 1)] }, { coefficient := 1, powers := [(23, 1), (51, 1), (57, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1), (66, 1)] }, { coefficient := 1, powers := [(31, 1), (40, 1), (60, 1)] }, { coefficient := 1, powers := [(31, 1), (51, 1), (54, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1), (63, 1)] }, { coefficient := 1, powers := [(34, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(34, 1), (43, 1), (54, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 16 → SparsePoly (Fin 72) := ![
  [{ coefficient := 1, powers := [(34, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (8, 1), (34, 1), (40, 1), (47, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (8, 1), (34, 1), (43, 1), (47, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (49, 1)] }],
  [{ coefficient := -1, powers := [(32, 1), (40, 1), (46, 1), (57, 1)] }, { coefficient := -1, powers := [(32, 1), (43, 1), (46, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (30, 1), (34, 1), (40, 1), (57, 1)] }, { coefficient := -1, powers := [(8, 1), (30, 1), (34, 1), (43, 1), (54, 1)] }, { coefficient := 1, powers := [(24, 1), (34, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(24, 1), (34, 1), (43, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (22, 1), (34, 1), (40, 1), (57, 1)] }, { coefficient := -1, powers := [(8, 1), (22, 1), (34, 1), (43, 1), (54, 1)] }, { coefficient := 1, powers := [(16, 1), (34, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(16, 1), (34, 1), (43, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(31, 1)] }],
  [{ coefficient := 1, powers := [(23, 1)] }],
  [{ coefficient := 1, powers := [(15, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (8, 1), (34, 1), (40, 1), (57, 1)] }, { coefficient := -1, powers := [(5, 1), (8, 1), (34, 1), (43, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(7, 1)] }],
  [{ coefficient := 1, powers := [(32, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(32, 1), (43, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (34, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (43, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(34, 1), (40, 1), (57, 1)] }, { coefficient := -1, powers := [(34, 1), (43, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(34, 1), (40, 1), (52, 1), (57, 1), (67, 1)] }, { coefficient := 1, powers := [(34, 1), (40, 1), (55, 1), (57, 1), (64, 1)] }, { coefficient := 1, powers := [(34, 1), (40, 1), (57, 1), (58, 1), (61, 1)] }, { coefficient := 1, powers := [(34, 1), (43, 1), (52, 1), (54, 1), (67, 1)] }, { coefficient := 1, powers := [(34, 1), (43, 1), (54, 1), (55, 1), (64, 1)] }, { coefficient := 1, powers := [(34, 1), (43, 1), (54, 1), (58, 1), (61, 1)] }]
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
    ¬ ∀ index : Fin 16,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.X5Case1079Tree.LeafB3.selectedHasNoCommonZero

end Krenn.X5Case1079Tree.LeafB3
