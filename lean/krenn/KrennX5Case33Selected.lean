import KrennSparseCertificate

/-! Selected core of a strict exact certificate over a frozen system. -/

namespace Krenn.X5Case33Selected

open Krenn.SparseCertificate
open MvPolynomial

def sourceSystemFileSHA256 : String := "a043bffa311868168c6bba94143ab2cc33ef7be2341aaf0f1a27eafa40fe32f6"
def sourceSystemSemanticSHA256 : String := "66907dc57cf2d37e1d56a2b4a746047e28b8eaa90b5e6ef3001149892cc547d0"
def certificateSHA256 : String := "6f9e953f618ba0fb41c290e07598f5aef5e0c88020f9b97be06c1d794bfaf294"
def sourceEquationCount : Nat := 675

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedIndices : Fin 20 → Fin 675 := ![
  0,
  1,
  32,
  33,
  36,
  39,
  45,
  403,
  414,
  420,
  421,
  422,
  423,
  424,
  425,
  427,
  660,
  664,
  672,
  674
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 20 → SparsePoly (Fin 70) := ![
  [{ coefficient := 1, powers := [(55, 1)] }],
  [{ coefficient := 1, powers := [(61, 1)] }],
  [{ coefficient := 1, powers := [(41, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(41, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(44, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(46, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(47, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (47, 1), (54, 1)] }, { coefficient := 1, powers := [(54, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (61, 1)] }, { coefficient := 1, powers := [(16, 1), (55, 1)] }, { coefficient := 1, powers := [(24, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(35, 1), (64, 1)] }, { coefficient := 1, powers := [(38, 1), (58, 1)] }, { coefficient := 1, powers := [(44, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(35, 1), (67, 1)] }, { coefficient := 1, powers := [(41, 1), (58, 1)] }, { coefficient := 1, powers := [(44, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(37, 1), (66, 1)] }, { coefficient := 1, powers := [(40, 1), (60, 1)] }, { coefficient := 1, powers := [(51, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(37, 1), (69, 1)] }, { coefficient := 1, powers := [(43, 1), (60, 1)] }, { coefficient := 1, powers := [(51, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(38, 1), (67, 1)] }, { coefficient := 1, powers := [(41, 1), (64, 1)] }, { coefficient := 1, powers := [(44, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(40, 1), (69, 1)] }, { coefficient := 1, powers := [(43, 1), (66, 1)] }, { coefficient := 1, powers := [(51, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (54, 1), (67, 1)] }, { coefficient := 1, powers := [(24, 1), (44, 1), (54, 1)] }, { coefficient := 1, powers := [(32, 1), (41, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (47, 1), (61, 1)] }, { coefficient := 1, powers := [(16, 1), (47, 1), (55, 1)] }, { coefficient := 1, powers := [(24, 1), (47, 1), (52, 1)] }, { coefficient := 1, powers := [(52, 1), (67, 1)] }, { coefficient := 1, powers := [(55, 1), (64, 1)] }, { coefficient := 1, powers := [(58, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (46, 1), (61, 1)] }, { coefficient := 1, powers := [(21, 1), (46, 1), (55, 1)] }, { coefficient := 1, powers := [(30, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(34, 1), (35, 1), (61, 1)] }, { coefficient := 1, powers := [(34, 1), (38, 1), (55, 1)] }, { coefficient := 1, powers := [(34, 1), (41, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (52, 1), (67, 1)] }, { coefficient := 1, powers := [(0, 1), (55, 1), (64, 1)] }, { coefficient := 1, powers := [(0, 1), (58, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (38, 1), (67, 1)] }, { coefficient := 1, powers := [(8, 1), (41, 1), (64, 1)] }, { coefficient := 1, powers := [(8, 1), (44, 1), (61, 1)] }, { coefficient := 1, powers := [(16, 1), (35, 1), (67, 1)] }, { coefficient := 1, powers := [(16, 1), (41, 1), (58, 1)] }, { coefficient := 1, powers := [(16, 1), (44, 1), (55, 1)] }, { coefficient := 1, powers := [(24, 1), (35, 1), (64, 1)] }, { coefficient := 1, powers := [(24, 1), (38, 1), (58, 1)] }, { coefficient := 1, powers := [(24, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(32, 1), (35, 1), (61, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1), (55, 1)] }, { coefficient := 1, powers := [(32, 1), (41, 1), (52, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(7, 1), (54, 1), (69, 1)] }, { coefficient := 1, powers := [(7, 1), (57, 1), (66, 1)] }, { coefficient := 1, powers := [(7, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(15, 1), (40, 1), (69, 1)] }, { coefficient := 1, powers := [(15, 1), (43, 1), (66, 1)] }, { coefficient := 1, powers := [(15, 1), (51, 1), (63, 1)] }, { coefficient := 1, powers := [(23, 1), (37, 1), (69, 1)] }, { coefficient := 1, powers := [(23, 1), (43, 1), (60, 1)] }, { coefficient := 1, powers := [(23, 1), (51, 1), (57, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1), (66, 1)] }, { coefficient := 1, powers := [(31, 1), (40, 1), (60, 1)] }, { coefficient := 1, powers := [(31, 1), (51, 1), (54, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1), (63, 1)] }, { coefficient := 1, powers := [(34, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(34, 1), (43, 1), (54, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 20 → SparsePoly (Fin 70) := ![
  [{ coefficient := 1, powers := [(7, 1), (32, 1), (38, 1), (54, 1), (69, 1)] }, { coefficient := 1, powers := [(7, 1), (32, 1), (38, 1), (57, 1), (66, 1)] }, { coefficient := 1, powers := [(7, 1), (32, 1), (38, 1), (60, 1), (63, 1)] }, { coefficient := -1, powers := [(21, 1), (32, 1), (37, 1), (46, 1), (63, 1)] }, { coefficient := -1, powers := [(21, 1), (32, 1), (40, 1), (46, 1), (57, 1)] }, { coefficient := 1, powers := [(32, 1), (34, 1), (38, 1), (43, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (32, 1), (35, 1), (54, 1), (69, 1)] }, { coefficient := 1, powers := [(7, 1), (32, 1), (35, 1), (57, 1), (66, 1)] }, { coefficient := 1, powers := [(7, 1), (32, 1), (35, 1), (60, 1), (63, 1)] }, { coefficient := -1, powers := [(13, 1), (32, 1), (37, 1), (46, 1), (63, 1)] }, { coefficient := -1, powers := [(13, 1), (32, 1), (40, 1), (46, 1), (57, 1)] }, { coefficient := 1, powers := [(32, 1), (34, 1), (35, 1), (43, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (32, 1), (52, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (32, 1), (52, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (24, 1), (52, 1), (69, 1)] }, { coefficient := -1, powers := [(24, 1), (34, 1), (43, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(30, 1), (32, 1), (37, 1), (63, 1)] }, { coefficient := -1, powers := [(30, 1), (32, 1), (40, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (7, 1), (24, 1), (52, 1), (69, 1)] }, { coefficient := 1, powers := [(0, 1), (24, 1), (34, 1), (43, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (7, 1), (52, 1), (69, 1)] }, { coefficient := -1, powers := [(0, 1), (34, 1), (43, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (7, 1), (47, 1), (54, 1), (69, 1)] }, { coefficient := -1, powers := [(0, 1), (7, 1), (47, 1), (57, 1), (66, 1)] }, { coefficient := -1, powers := [(0, 1), (7, 1), (47, 1), (60, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (34, 1), (37, 1), (47, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (34, 1), (40, 1), (47, 1), (57, 1)] }, { coefficient := -1, powers := [(0, 1), (34, 1), (43, 1), (47, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (24, 1), (54, 1), (69, 1)] }, { coefficient := 1, powers := [(7, 1), (24, 1), (57, 1), (66, 1)] }, { coefficient := 1, powers := [(7, 1), (24, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(24, 1), (34, 1), (37, 1), (63, 1)] }, { coefficient := 1, powers := [(24, 1), (34, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(24, 1), (34, 1), (43, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (16, 1), (54, 1), (69, 1)] }, { coefficient := 1, powers := [(7, 1), (16, 1), (57, 1), (66, 1)] }, { coefficient := 1, powers := [(7, 1), (16, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(16, 1), (34, 1), (37, 1), (63, 1)] }, { coefficient := 1, powers := [(16, 1), (34, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(16, 1), (34, 1), (43, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(31, 1)] }],
  [{ coefficient := 1, powers := [(23, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (8, 1), (54, 1), (69, 1)] }, { coefficient := 1, powers := [(7, 1), (8, 1), (57, 1), (66, 1)] }, { coefficient := 1, powers := [(7, 1), (8, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (37, 1), (63, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (43, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(15, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (52, 1), (69, 1)] }, { coefficient := 1, powers := [(34, 1), (43, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (7, 1), (54, 1), (69, 1)] }, { coefficient := 1, powers := [(0, 1), (7, 1), (57, 1), (66, 1)] }, { coefficient := 1, powers := [(0, 1), (7, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(0, 1), (34, 1), (37, 1), (63, 1)] }, { coefficient := 1, powers := [(0, 1), (34, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (34, 1), (43, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(32, 1), (37, 1), (63, 1)] }, { coefficient := 1, powers := [(32, 1), (40, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (54, 1), (69, 1)] }, { coefficient := -1, powers := [(7, 1), (57, 1), (66, 1)] }, { coefficient := -1, powers := [(7, 1), (60, 1), (63, 1)] }, { coefficient := -1, powers := [(34, 1), (37, 1), (63, 1)] }, { coefficient := -1, powers := [(34, 1), (40, 1), (57, 1)] }, { coefficient := -1, powers := [(34, 1), (43, 1), (54, 1)] }],
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
    ¬ ∀ index : Fin 20,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.X5Case33Selected.selectedHasNoCommonZero

end Krenn.X5Case33Selected
