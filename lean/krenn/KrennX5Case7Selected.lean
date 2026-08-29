import KrennSparseCertificate

/-! Selected core of a strict exact certificate over a frozen system. -/

namespace Krenn.X5Case7Selected

open Krenn.SparseCertificate
open MvPolynomial

def sourceSystemFileSHA256 : String := "04da96aaa52b3a073a2d11675fcf380759ed907dc6e14315084b6d0eb5265d33"
def sourceSystemSemanticSHA256 : String := "59b37f6f0e2815dff3baa1197954e3aaf2835f629b802d539c7697ac5658eefc"
def certificateSHA256 : String := "2456d96ce52c0cf4bcb235b887fb1a42563d575076d750987db051dd4f55d8dc"
def sourceEquationCount : Nat := 675

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedIndices : Fin 18 → Fin 675 := ![
  0,
  1,
  2,
  3,
  32,
  33,
  41,
  404,
  421,
  422,
  424,
  425,
  426,
  429,
  458,
  659,
  672,
  674
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 18 → SparsePoly (Fin 70) := ![
  [{ coefficient := 1, powers := [(55, 1)] }],
  [{ coefficient := 1, powers := [(57, 1)] }],
  [{ coefficient := 1, powers := [(61, 1)] }],
  [{ coefficient := 1, powers := [(63, 1)] }],
  [{ coefficient := 1, powers := [(41, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(41, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(46, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (46, 1), (54, 1)] }, { coefficient := 1, powers := [(54, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(35, 1), (64, 1)] }, { coefficient := 1, powers := [(38, 1), (58, 1)] }, { coefficient := 1, powers := [(44, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(35, 1), (67, 1)] }, { coefficient := 1, powers := [(41, 1), (58, 1)] }, { coefficient := 1, powers := [(44, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(37, 1), (69, 1)] }, { coefficient := 1, powers := [(43, 1), (60, 1)] }, { coefficient := 1, powers := [(51, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(38, 1), (67, 1)] }, { coefficient := 1, powers := [(41, 1), (64, 1)] }, { coefficient := 1, powers := [(44, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(40, 1), (69, 1)] }, { coefficient := 1, powers := [(43, 1), (66, 1)] }, { coefficient := 1, powers := [(51, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (54, 1), (67, 1)] }, { coefficient := 1, powers := [(24, 1), (44, 1), (54, 1)] }, { coefficient := 1, powers := [(32, 1), (41, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (41, 1), (66, 1)] }, { coefficient := 1, powers := [(17, 1), (41, 1), (60, 1)] }, { coefficient := 1, powers := [(24, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (46, 1), (61, 1)] }, { coefficient := 1, powers := [(16, 1), (46, 1), (55, 1)] }, { coefficient := 1, powers := [(24, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(52, 1), (67, 1)] }, { coefficient := 1, powers := [(55, 1), (64, 1)] }, { coefficient := 1, powers := [(58, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (52, 1), (67, 1)] }, { coefficient := 1, powers := [(0, 1), (55, 1), (64, 1)] }, { coefficient := 1, powers := [(0, 1), (58, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (38, 1), (67, 1)] }, { coefficient := 1, powers := [(8, 1), (41, 1), (64, 1)] }, { coefficient := 1, powers := [(8, 1), (44, 1), (61, 1)] }, { coefficient := 1, powers := [(16, 1), (35, 1), (67, 1)] }, { coefficient := 1, powers := [(16, 1), (41, 1), (58, 1)] }, { coefficient := 1, powers := [(16, 1), (44, 1), (55, 1)] }, { coefficient := 1, powers := [(24, 1), (35, 1), (64, 1)] }, { coefficient := 1, powers := [(24, 1), (38, 1), (58, 1)] }, { coefficient := 1, powers := [(24, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(32, 1), (35, 1), (61, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1), (55, 1)] }, { coefficient := 1, powers := [(32, 1), (41, 1), (52, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(7, 1), (54, 1), (69, 1)] }, { coefficient := 1, powers := [(7, 1), (57, 1), (66, 1)] }, { coefficient := 1, powers := [(7, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(15, 1), (40, 1), (69, 1)] }, { coefficient := 1, powers := [(15, 1), (43, 1), (66, 1)] }, { coefficient := 1, powers := [(15, 1), (51, 1), (63, 1)] }, { coefficient := 1, powers := [(23, 1), (37, 1), (69, 1)] }, { coefficient := 1, powers := [(23, 1), (43, 1), (60, 1)] }, { coefficient := 1, powers := [(23, 1), (51, 1), (57, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1), (66, 1)] }, { coefficient := 1, powers := [(31, 1), (40, 1), (60, 1)] }, { coefficient := 1, powers := [(31, 1), (51, 1), (54, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1), (63, 1)] }, { coefficient := 1, powers := [(34, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(34, 1), (43, 1), (54, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 18 → SparsePoly (Fin 70) := ![
  [{ coefficient := -1, powers := [(0, 1), (7, 1), (16, 1), (46, 1), (54, 1), (69, 1)] }, { coefficient := -1, powers := [(0, 1), (16, 1), (31, 1), (37, 1), (46, 1), (66, 1)] }, { coefficient := -1, powers := [(0, 1), (16, 1), (31, 1), (40, 1), (46, 1), (60, 1)] }, { coefficient := -1, powers := [(0, 1), (16, 1), (31, 1), (46, 1), (51, 1), (54, 1)] }, { coefficient := -1, powers := [(0, 1), (16, 1), (34, 1), (43, 1), (46, 1), (54, 1)] }, { coefficient := 1, powers := [(7, 1), (32, 1), (38, 1), (54, 1), (69, 1)] }, { coefficient := 1, powers := [(31, 1), (32, 1), (37, 1), (38, 1), (66, 1)] }, { coefficient := 1, powers := [(31, 1), (32, 1), (38, 1), (40, 1), (60, 1)] }, { coefficient := 1, powers := [(31, 1), (32, 1), (38, 1), (51, 1), (54, 1)] }, { coefficient := 1, powers := [(32, 1), (34, 1), (38, 1), (43, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (66, 1)] }, { coefficient := 1, powers := [(34, 1), (40, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (7, 1), (8, 1), (46, 1), (54, 1), (69, 1)] }, { coefficient := -1, powers := [(0, 1), (8, 1), (31, 1), (37, 1), (46, 1), (66, 1)] }, { coefficient := -1, powers := [(0, 1), (8, 1), (31, 1), (40, 1), (46, 1), (60, 1)] }, { coefficient := -1, powers := [(0, 1), (8, 1), (31, 1), (46, 1), (51, 1), (54, 1)] }, { coefficient := -1, powers := [(0, 1), (8, 1), (34, 1), (43, 1), (46, 1), (54, 1)] }, { coefficient := 1, powers := [(7, 1), (32, 1), (35, 1), (54, 1), (69, 1)] }, { coefficient := 1, powers := [(31, 1), (32, 1), (35, 1), (37, 1), (66, 1)] }, { coefficient := 1, powers := [(31, 1), (32, 1), (35, 1), (40, 1), (60, 1)] }, { coefficient := 1, powers := [(31, 1), (32, 1), (35, 1), (51, 1), (54, 1)] }, { coefficient := 1, powers := [(32, 1), (34, 1), (35, 1), (43, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (60, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (7, 1), (17, 1), (46, 1), (52, 1), (69, 1)] }, { coefficient := -1, powers := [(0, 1), (17, 1), (31, 1), (46, 1), (51, 1), (52, 1)] }, { coefficient := -1, powers := [(0, 1), (17, 1), (34, 1), (43, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(7, 1), (17, 1), (44, 1), (52, 1), (69, 1)] }, { coefficient := 1, powers := [(17, 1), (31, 1), (44, 1), (51, 1), (52, 1)] }, { coefficient := 1, powers := [(17, 1), (34, 1), (43, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(31, 1), (32, 1), (40, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (7, 1), (9, 1), (46, 1), (52, 1), (69, 1)] }, { coefficient := -1, powers := [(0, 1), (9, 1), (31, 1), (46, 1), (51, 1), (52, 1)] }, { coefficient := -1, powers := [(0, 1), (9, 1), (34, 1), (43, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(7, 1), (9, 1), (44, 1), (52, 1), (69, 1)] }, { coefficient := 1, powers := [(9, 1), (31, 1), (44, 1), (51, 1), (52, 1)] }, { coefficient := 1, powers := [(9, 1), (34, 1), (43, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(31, 1), (32, 1), (37, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (7, 1), (24, 1), (54, 1), (69, 1)] }, { coefficient := -1, powers := [(0, 1), (24, 1), (31, 1), (37, 1), (66, 1)] }, { coefficient := -1, powers := [(0, 1), (24, 1), (31, 1), (40, 1), (60, 1)] }, { coefficient := -1, powers := [(0, 1), (24, 1), (31, 1), (51, 1), (54, 1)] }, { coefficient := -1, powers := [(0, 1), (24, 1), (34, 1), (43, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (7, 1), (52, 1), (69, 1)] }, { coefficient := -1, powers := [(0, 1), (31, 1), (51, 1), (52, 1)] }, { coefficient := -1, powers := [(0, 1), (34, 1), (43, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (24, 1), (54, 1), (69, 1)] }, { coefficient := 1, powers := [(24, 1), (31, 1), (37, 1), (66, 1)] }, { coefficient := 1, powers := [(24, 1), (31, 1), (40, 1), (60, 1)] }, { coefficient := 1, powers := [(24, 1), (31, 1), (51, 1), (54, 1)] }, { coefficient := 1, powers := [(24, 1), (34, 1), (43, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (16, 1), (54, 1), (69, 1)] }, { coefficient := 1, powers := [(16, 1), (31, 1), (37, 1), (66, 1)] }, { coefficient := 1, powers := [(16, 1), (31, 1), (40, 1), (60, 1)] }, { coefficient := 1, powers := [(16, 1), (31, 1), (51, 1), (54, 1)] }, { coefficient := 1, powers := [(16, 1), (34, 1), (43, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(23, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (8, 1), (54, 1), (69, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1), (37, 1), (66, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1), (40, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1), (51, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (43, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(15, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (52, 1), (69, 1)] }, { coefficient := 1, powers := [(31, 1), (51, 1), (52, 1)] }, { coefficient := 1, powers := [(34, 1), (43, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (7, 1), (46, 1), (52, 1), (69, 1)] }, { coefficient := 1, powers := [(0, 1), (31, 1), (46, 1), (51, 1), (52, 1)] }, { coefficient := 1, powers := [(0, 1), (34, 1), (43, 1), (46, 1), (52, 1)] }, { coefficient := -1, powers := [(7, 1), (44, 1), (52, 1), (69, 1)] }, { coefficient := -1, powers := [(31, 1), (44, 1), (51, 1), (52, 1)] }, { coefficient := -1, powers := [(34, 1), (43, 1), (44, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (7, 1), (54, 1), (69, 1)] }, { coefficient := 1, powers := [(0, 1), (31, 1), (37, 1), (66, 1)] }, { coefficient := 1, powers := [(0, 1), (31, 1), (40, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (31, 1), (51, 1), (54, 1)] }, { coefficient := 1, powers := [(0, 1), (34, 1), (43, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (54, 1), (69, 1)] }, { coefficient := -1, powers := [(31, 1), (37, 1), (66, 1)] }, { coefficient := -1, powers := [(31, 1), (40, 1), (60, 1)] }, { coefficient := -1, powers := [(31, 1), (51, 1), (54, 1)] }, { coefficient := -1, powers := [(34, 1), (43, 1), (54, 1)] }],
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
    ¬ ∀ index : Fin 18,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.X5Case7Selected.selectedHasNoCommonZero

end Krenn.X5Case7Selected
