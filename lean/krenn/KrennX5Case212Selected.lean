import KrennSparseCertificate

/-! Selected core of a strict exact certificate over a frozen system. -/

namespace Krenn.X5Case212Selected

open Krenn.SparseCertificate
open MvPolynomial

def sourceSystemFileSHA256 : String := "8d43769f3a1f9582c442a333249b1f09d59069a410eb9ba6f3f0fab058bbbb7f"
def sourceSystemSemanticSHA256 : String := "b22ffc24bd520c5a1c841b14d5ed659072c18907a707458c60b84eb1464e2601"
def certificateSHA256 : String := "ffe8553cea8e0b7ef327409c4a3cc756f321b04d3045134676b57f1e542afeca"
def sourceEquationCount : Nat := 675

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedIndices : Fin 20 → Fin 675 := ![
  0,
  1,
  26,
  27,
  45,
  51,
  54,
  391,
  414,
  421,
  422,
  423,
  424,
  425,
  426,
  443,
  660,
  661,
  672,
  674
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 20 → SparsePoly (Fin 70) := ![
  [{ coefficient := 1, powers := [(54, 1)] }],
  [{ coefficient := 1, powers := [(57, 1)] }],
  [{ coefficient := 1, powers := [(37, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(37, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(48, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(49, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(51, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (48, 1), (61, 1)] }, { coefficient := 1, powers := [(60, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (63, 1)] }, { coefficient := 1, powers := [(18, 1), (57, 1)] }, { coefficient := 1, powers := [(26, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(35, 1), (64, 1)] }, { coefficient := 1, powers := [(38, 1), (58, 1)] }, { coefficient := 1, powers := [(44, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(35, 1), (67, 1)] }, { coefficient := 1, powers := [(41, 1), (58, 1)] }, { coefficient := 1, powers := [(44, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(37, 1), (66, 1)] }, { coefficient := 1, powers := [(40, 1), (60, 1)] }, { coefficient := 1, powers := [(51, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(37, 1), (69, 1)] }, { coefficient := 1, powers := [(43, 1), (60, 1)] }, { coefficient := 1, powers := [(51, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(38, 1), (67, 1)] }, { coefficient := 1, powers := [(41, 1), (64, 1)] }, { coefficient := 1, powers := [(44, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(40, 1), (69, 1)] }, { coefficient := 1, powers := [(43, 1), (66, 1)] }, { coefficient := 1, powers := [(51, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (60, 1), (61, 1)] }, { coefficient := 1, powers := [(15, 1), (51, 1), (61, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (48, 1), (63, 1)] }, { coefficient := 1, powers := [(18, 1), (48, 1), (57, 1)] }, { coefficient := 1, powers := [(26, 1), (48, 1), (54, 1)] }, { coefficient := 1, powers := [(54, 1), (69, 1)] }, { coefficient := 1, powers := [(57, 1), (66, 1)] }, { coefficient := 1, powers := [(60, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (49, 1), (63, 1)] }, { coefficient := 1, powers := [(18, 1), (49, 1), (57, 1)] }, { coefficient := 1, powers := [(26, 1), (49, 1), (54, 1)] }, { coefficient := 1, powers := [(32, 1), (37, 1), (63, 1)] }, { coefficient := 1, powers := [(32, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(32, 1), (43, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (52, 1), (67, 1)] }, { coefficient := 1, powers := [(0, 1), (55, 1), (64, 1)] }, { coefficient := 1, powers := [(0, 1), (58, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (38, 1), (67, 1)] }, { coefficient := 1, powers := [(8, 1), (41, 1), (64, 1)] }, { coefficient := 1, powers := [(8, 1), (44, 1), (61, 1)] }, { coefficient := 1, powers := [(16, 1), (35, 1), (67, 1)] }, { coefficient := 1, powers := [(16, 1), (41, 1), (58, 1)] }, { coefficient := 1, powers := [(16, 1), (44, 1), (55, 1)] }, { coefficient := 1, powers := [(24, 1), (35, 1), (64, 1)] }, { coefficient := 1, powers := [(24, 1), (38, 1), (58, 1)] }, { coefficient := 1, powers := [(24, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(32, 1), (35, 1), (61, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1), (55, 1)] }, { coefficient := 1, powers := [(32, 1), (41, 1), (52, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(7, 1), (54, 1), (69, 1)] }, { coefficient := 1, powers := [(7, 1), (57, 1), (66, 1)] }, { coefficient := 1, powers := [(7, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(15, 1), (40, 1), (69, 1)] }, { coefficient := 1, powers := [(15, 1), (43, 1), (66, 1)] }, { coefficient := 1, powers := [(15, 1), (51, 1), (63, 1)] }, { coefficient := 1, powers := [(23, 1), (37, 1), (69, 1)] }, { coefficient := 1, powers := [(23, 1), (43, 1), (60, 1)] }, { coefficient := 1, powers := [(23, 1), (51, 1), (57, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1), (66, 1)] }, { coefficient := 1, powers := [(31, 1), (40, 1), (60, 1)] }, { coefficient := 1, powers := [(31, 1), (51, 1), (54, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1), (63, 1)] }, { coefficient := 1, powers := [(34, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(34, 1), (43, 1), (54, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 20 → SparsePoly (Fin 70) := ![
  [{ coefficient := 1, powers := [(0, 1), (34, 1), (43, 1), (52, 1), (67, 1)] }, { coefficient := 1, powers := [(0, 1), (34, 1), (43, 1), (55, 1), (64, 1)] }, { coefficient := 1, powers := [(0, 1), (34, 1), (43, 1), (58, 1), (61, 1)] }, { coefficient := -1, powers := [(26, 1), (34, 1), (38, 1), (49, 1), (55, 1)] }, { coefficient := -1, powers := [(26, 1), (34, 1), (41, 1), (49, 1), (52, 1)] }, { coefficient := 1, powers := [(32, 1), (34, 1), (35, 1), (43, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (34, 1), (40, 1), (52, 1), (67, 1)] }, { coefficient := 1, powers := [(0, 1), (34, 1), (40, 1), (55, 1), (64, 1)] }, { coefficient := 1, powers := [(0, 1), (34, 1), (40, 1), (58, 1), (61, 1)] }, { coefficient := -1, powers := [(18, 1), (34, 1), (38, 1), (49, 1), (55, 1)] }, { coefficient := -1, powers := [(18, 1), (34, 1), (41, 1), (49, 1), (52, 1)] }, { coefficient := 1, powers := [(32, 1), (34, 1), (35, 1), (40, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (34, 1), (55, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (34, 1), (52, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (7, 1), (9, 1), (58, 1), (63, 1)] }, { coefficient := 1, powers := [(7, 1), (9, 1), (32, 1), (35, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(9, 1), (34, 1), (38, 1), (55, 1)] }, { coefficient := -1, powers := [(9, 1), (34, 1), (41, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (15, 1), (58, 1), (63, 1)] }, { coefficient := -1, powers := [(15, 1), (32, 1), (35, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (7, 1), (58, 1), (63, 1)] }, { coefficient := -1, powers := [(7, 1), (32, 1), (35, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (7, 1), (48, 1), (52, 1), (67, 1)] }, { coefficient := -1, powers := [(0, 1), (7, 1), (48, 1), (55, 1), (64, 1)] }, { coefficient := -1, powers := [(0, 1), (7, 1), (48, 1), (58, 1), (61, 1)] }, { coefficient := -1, powers := [(7, 1), (32, 1), (35, 1), (48, 1), (61, 1)] }, { coefficient := -1, powers := [(7, 1), (32, 1), (38, 1), (48, 1), (55, 1)] }, { coefficient := -1, powers := [(7, 1), (32, 1), (41, 1), (48, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(24, 1)] }],
  [{ coefficient := 1, powers := [(16, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (31, 1), (52, 1), (67, 1)] }, { coefficient := 1, powers := [(0, 1), (31, 1), (55, 1), (64, 1)] }, { coefficient := 1, powers := [(0, 1), (31, 1), (58, 1), (61, 1)] }, { coefficient := 1, powers := [(31, 1), (32, 1), (35, 1), (61, 1)] }, { coefficient := 1, powers := [(31, 1), (32, 1), (38, 1), (55, 1)] }, { coefficient := 1, powers := [(31, 1), (32, 1), (41, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (23, 1), (52, 1), (67, 1)] }, { coefficient := 1, powers := [(0, 1), (23, 1), (55, 1), (64, 1)] }, { coefficient := 1, powers := [(0, 1), (23, 1), (58, 1), (61, 1)] }, { coefficient := 1, powers := [(23, 1), (32, 1), (35, 1), (61, 1)] }, { coefficient := 1, powers := [(23, 1), (32, 1), (38, 1), (55, 1)] }, { coefficient := 1, powers := [(23, 1), (32, 1), (41, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(8, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (15, 1), (52, 1), (67, 1)] }, { coefficient := 1, powers := [(0, 1), (15, 1), (55, 1), (64, 1)] }, { coefficient := 1, powers := [(0, 1), (15, 1), (58, 1), (61, 1)] }, { coefficient := 1, powers := [(15, 1), (32, 1), (35, 1), (61, 1)] }, { coefficient := 1, powers := [(15, 1), (32, 1), (38, 1), (55, 1)] }, { coefficient := 1, powers := [(15, 1), (32, 1), (41, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (58, 1), (63, 1)] }, { coefficient := 1, powers := [(32, 1), (35, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (7, 1), (52, 1), (67, 1)] }, { coefficient := 1, powers := [(0, 1), (7, 1), (55, 1), (64, 1)] }, { coefficient := 1, powers := [(0, 1), (7, 1), (58, 1), (61, 1)] }, { coefficient := 1, powers := [(7, 1), (32, 1), (35, 1), (61, 1)] }, { coefficient := 1, powers := [(7, 1), (32, 1), (38, 1), (55, 1)] }, { coefficient := 1, powers := [(7, 1), (32, 1), (41, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(34, 1), (38, 1), (55, 1)] }, { coefficient := 1, powers := [(34, 1), (41, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(0, 1), (52, 1), (67, 1)] }, { coefficient := -1, powers := [(0, 1), (55, 1), (64, 1)] }, { coefficient := -1, powers := [(0, 1), (58, 1), (61, 1)] }, { coefficient := -1, powers := [(32, 1), (35, 1), (61, 1)] }, { coefficient := -1, powers := [(32, 1), (38, 1), (55, 1)] }, { coefficient := -1, powers := [(32, 1), (41, 1), (52, 1)] }]
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
    ¬ ∀ index : Fin 20,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.X5Case212Selected.selectedHasNoCommonZero

end Krenn.X5Case212Selected
