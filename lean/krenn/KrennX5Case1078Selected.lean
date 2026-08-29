import KrennSparseCertificate

/-! Selected core of a strict exact certificate over a frozen system. -/

namespace Krenn.X5Case1078Selected

open Krenn.SparseCertificate
open MvPolynomial

def sourceSystemFileSHA256 : String := "a02facbf8950e9e072910f0fd2fd64a0e6f254437d0718f6b6fce32ea6946885"
def sourceSystemSemanticSHA256 : String := "799059a0cc22a5c3b9c81fd3eb0bc1f917c74c47dee4413962ed92767ae652ac"
def certificateSHA256 : String := "8a3f6b9de8dc557a843b5aac00279c455eee529193b04efcb2cbae76721f0a89"
def sourceEquationCount : Nat := 675

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedIndices : Fin 17 → Fin 675 := ![
  0,
  1,
  2,
  3,
  26,
  27,
  47,
  419,
  422,
  424,
  425,
  426,
  428,
  445,
  661,
  672,
  674
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 17 → SparsePoly (Fin 70) := ![
  [{ coefficient := 1, powers := [(52, 1)] }],
  [{ coefficient := 1, powers := [(54, 1)] }],
  [{ coefficient := 1, powers := [(55, 1)] }],
  [{ coefficient := 1, powers := [(57, 1)] }],
  [{ coefficient := 1, powers := [(37, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(37, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(49, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(15, 1), (61, 1)] }, { coefficient := 1, powers := [(22, 1), (37, 1), (67, 1)] }, { coefficient := 1, powers := [(30, 1), (37, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(35, 1), (64, 1)] }, { coefficient := 1, powers := [(38, 1), (58, 1)] }, { coefficient := 1, powers := [(44, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(35, 1), (67, 1)] }, { coefficient := 1, powers := [(41, 1), (58, 1)] }, { coefficient := 1, powers := [(44, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(37, 1), (66, 1)] }, { coefficient := 1, powers := [(40, 1), (60, 1)] }, { coefficient := 1, powers := [(51, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(37, 1), (69, 1)] }, { coefficient := 1, powers := [(43, 1), (60, 1)] }, { coefficient := 1, powers := [(51, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(40, 1), (69, 1)] }, { coefficient := 1, powers := [(43, 1), (66, 1)] }, { coefficient := 1, powers := [(51, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (60, 1), (61, 1)] }, { coefficient := 1, powers := [(15, 1), (51, 1), (61, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (49, 1), (63, 1)] }, { coefficient := 1, powers := [(18, 1), (49, 1), (57, 1)] }, { coefficient := 1, powers := [(26, 1), (49, 1), (54, 1)] }, { coefficient := 1, powers := [(54, 1), (69, 1)] }, { coefficient := 1, powers := [(57, 1), (66, 1)] }, { coefficient := 1, powers := [(60, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (52, 1), (67, 1)] }, { coefficient := 1, powers := [(0, 1), (55, 1), (64, 1)] }, { coefficient := 1, powers := [(0, 1), (58, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (38, 1), (67, 1)] }, { coefficient := 1, powers := [(8, 1), (41, 1), (64, 1)] }, { coefficient := 1, powers := [(8, 1), (44, 1), (61, 1)] }, { coefficient := 1, powers := [(16, 1), (35, 1), (67, 1)] }, { coefficient := 1, powers := [(16, 1), (41, 1), (58, 1)] }, { coefficient := 1, powers := [(16, 1), (44, 1), (55, 1)] }, { coefficient := 1, powers := [(24, 1), (35, 1), (64, 1)] }, { coefficient := 1, powers := [(24, 1), (38, 1), (58, 1)] }, { coefficient := 1, powers := [(24, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(32, 1), (35, 1), (61, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1), (55, 1)] }, { coefficient := 1, powers := [(32, 1), (41, 1), (52, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(7, 1), (54, 1), (69, 1)] }, { coefficient := 1, powers := [(7, 1), (57, 1), (66, 1)] }, { coefficient := 1, powers := [(7, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(15, 1), (40, 1), (69, 1)] }, { coefficient := 1, powers := [(15, 1), (43, 1), (66, 1)] }, { coefficient := 1, powers := [(15, 1), (51, 1), (63, 1)] }, { coefficient := 1, powers := [(23, 1), (37, 1), (69, 1)] }, { coefficient := 1, powers := [(23, 1), (43, 1), (60, 1)] }, { coefficient := 1, powers := [(23, 1), (51, 1), (57, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1), (66, 1)] }, { coefficient := 1, powers := [(31, 1), (40, 1), (60, 1)] }, { coefficient := 1, powers := [(31, 1), (51, 1), (54, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1), (63, 1)] }, { coefficient := 1, powers := [(34, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(34, 1), (43, 1), (54, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 17 → SparsePoly (Fin 70) := ![
  [{ coefficient := 1, powers := [(0, 1), (67, 1)] }, { coefficient := 1, powers := [(32, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (7, 1), (58, 1), (61, 1), (69, 1)] }, { coefficient := 1, powers := [(0, 1), (34, 1), (43, 1), (58, 1), (61, 1)] }, { coefficient := -1, powers := [(7, 1), (8, 1), (26, 1), (38, 1), (49, 1), (67, 1)] }, { coefficient := -1, powers := [(7, 1), (8, 1), (26, 1), (41, 1), (49, 1), (64, 1)] }, { coefficient := 1, powers := [(7, 1), (8, 1), (44, 1), (61, 1), (69, 1)] }, { coefficient := 1, powers := [(7, 1), (32, 1), (35, 1), (61, 1), (69, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (38, 1), (43, 1), (67, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (41, 1), (43, 1), (64, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (43, 1), (44, 1), (61, 1)] }, { coefficient := 1, powers := [(32, 1), (34, 1), (35, 1), (43, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (64, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (7, 1), (58, 1), (61, 1), (66, 1)] }, { coefficient := 1, powers := [(0, 1), (34, 1), (40, 1), (58, 1), (61, 1)] }, { coefficient := -1, powers := [(7, 1), (8, 1), (18, 1), (38, 1), (49, 1), (67, 1)] }, { coefficient := -1, powers := [(7, 1), (8, 1), (18, 1), (41, 1), (49, 1), (64, 1)] }, { coefficient := 1, powers := [(7, 1), (8, 1), (44, 1), (61, 1), (66, 1)] }, { coefficient := 1, powers := [(7, 1), (32, 1), (35, 1), (61, 1), (66, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (38, 1), (40, 1), (67, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (40, 1), (41, 1), (64, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (40, 1), (44, 1), (61, 1)] }, { coefficient := 1, powers := [(32, 1), (34, 1), (35, 1), (40, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (30, 1), (51, 1), (58, 1), (63, 1)] }, { coefficient := 1, powers := [(8, 1), (30, 1), (44, 1), (51, 1), (63, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (41, 1), (63, 1)] }, { coefficient := 1, powers := [(30, 1), (32, 1), (35, 1), (51, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (22, 1), (51, 1), (58, 1), (63, 1)] }, { coefficient := 1, powers := [(8, 1), (22, 1), (44, 1), (51, 1), (63, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (38, 1), (63, 1)] }, { coefficient := 1, powers := [(22, 1), (32, 1), (35, 1), (51, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (8, 1), (10, 1), (38, 1), (67, 1)] }, { coefficient := -1, powers := [(7, 1), (8, 1), (10, 1), (41, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (51, 1), (58, 1), (63, 1)] }, { coefficient := -1, powers := [(8, 1), (44, 1), (51, 1), (63, 1)] }, { coefficient := -1, powers := [(32, 1), (35, 1), (51, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(24, 1)] }],
  [{ coefficient := 1, powers := [(16, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (31, 1), (58, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1), (38, 1), (67, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1), (41, 1), (64, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1), (44, 1), (61, 1)] }, { coefficient := 1, powers := [(31, 1), (32, 1), (35, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (23, 1), (58, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (23, 1), (38, 1), (67, 1)] }, { coefficient := 1, powers := [(8, 1), (23, 1), (41, 1), (64, 1)] }, { coefficient := 1, powers := [(8, 1), (23, 1), (44, 1), (61, 1)] }, { coefficient := 1, powers := [(23, 1), (32, 1), (35, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (15, 1), (58, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (15, 1), (38, 1), (67, 1)] }, { coefficient := 1, powers := [(8, 1), (15, 1), (41, 1), (64, 1)] }, { coefficient := 1, powers := [(8, 1), (15, 1), (44, 1), (61, 1)] }, { coefficient := 1, powers := [(15, 1), (32, 1), (35, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (58, 1), (63, 1)] }, { coefficient := 1, powers := [(8, 1), (44, 1), (63, 1)] }, { coefficient := 1, powers := [(32, 1), (35, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (8, 1), (38, 1), (67, 1)] }, { coefficient := 1, powers := [(7, 1), (8, 1), (41, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(0, 1), (58, 1), (61, 1)] }, { coefficient := -1, powers := [(8, 1), (38, 1), (67, 1)] }, { coefficient := -1, powers := [(8, 1), (41, 1), (64, 1)] }, { coefficient := -1, powers := [(8, 1), (44, 1), (61, 1)] }, { coefficient := -1, powers := [(32, 1), (35, 1), (61, 1)] }]
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
    ¬ ∀ index : Fin 17,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.X5Case1078Selected.selectedHasNoCommonZero

end Krenn.X5Case1078Selected
