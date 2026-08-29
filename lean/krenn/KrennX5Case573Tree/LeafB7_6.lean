import KrennSparseCertificate

/-! Selected core of a strict exact certificate over a frozen system. -/

namespace Krenn.X5Case573Tree.LeafB7_6

open Krenn.SparseCertificate
open MvPolynomial

def sourceSystemFileSHA256 : String := "d83ef16ae30f78bc03ddc41b9e4b127f706af7b757e5eaba48010abea60e6833"
def sourceSystemSemanticSHA256 : String := "3de93d495cc198db0e8902f01d1d965581f516f9fa14b0312b6ba620e46cee59"
def certificateSHA256 : String := "6d0633d36fc8c033cae10797ba984340c326f86a291d03307662afb0f5dc4a3f"
def sourceEquationCount : Nat := 681

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedIndices : Fin 21 → Fin 681 := ![
  18,
  21,
  24,
  33,
  34,
  37,
  50,
  386,
  413,
  414,
  421,
  422,
  429,
  537,
  593,
  622,
  660,
  667,
  672,
  677,
  679
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 21 → SparsePoly (Fin 75) := ![
  [{ coefficient := 1, powers := [(25, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(28, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(35, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(42, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(42, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(44, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(49, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (56, 1), (64, 1)] }, { coefficient := 1, powers := [(21, 1), (49, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(34, 1), (42, 1), (52, 1)] }, { coefficient := 1, powers := [(52, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (61, 1)] }, { coefficient := 1, powers := [(16, 1), (55, 1)] }, { coefficient := 1, powers := [(24, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(35, 1), (64, 1)] }, { coefficient := 1, powers := [(38, 1), (58, 1)] }, { coefficient := 1, powers := [(44, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(35, 1), (67, 1)] }, { coefficient := 1, powers := [(41, 1), (58, 1)] }, { coefficient := 1, powers := [(44, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (56, 1), (64, 1)] }, { coefficient := 1, powers := [(16, 1), (44, 1), (56, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (42, 1), (58, 1)] }, { coefficient := 1, powers := [(28, 1), (47, 1), (52, 1)] }, { coefficient := 1, powers := [(42, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (56, 1), (66, 1)] }, { coefficient := 1, powers := [(11, 1), (42, 1), (66, 1)] }, { coefficient := 1, powers := [(28, 1), (36, 1), (66, 1)] }, { coefficient := 1, powers := [(56, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (42, 1), (64, 1)] }, { coefficient := 1, powers := [(16, 1), (42, 1), (58, 1)] }, { coefficient := 1, powers := [(25, 1), (47, 1), (52, 1)] }, { coefficient := 1, powers := [(32, 1), (42, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (47, 1), (61, 1)] }, { coefficient := 1, powers := [(16, 1), (47, 1), (55, 1)] }, { coefficient := 1, powers := [(24, 1), (47, 1), (52, 1)] }, { coefficient := 1, powers := [(52, 1), (67, 1)] }, { coefficient := 1, powers := [(55, 1), (64, 1)] }, { coefficient := 1, powers := [(58, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (52, 1), (67, 1)] }, { coefficient := 1, powers := [(2, 1), (55, 1), (64, 1)] }, { coefficient := 1, powers := [(2, 1), (58, 1), (61, 1)] }, { coefficient := 1, powers := [(19, 1), (35, 1), (67, 1)] }, { coefficient := 1, powers := [(19, 1), (41, 1), (58, 1)] }, { coefficient := 1, powers := [(19, 1), (44, 1), (55, 1)] }, { coefficient := 1, powers := [(27, 1), (35, 1), (64, 1)] }, { coefficient := 1, powers := [(27, 1), (38, 1), (58, 1)] }, { coefficient := 1, powers := [(27, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(38, 1), (67, 1)] }, { coefficient := 1, powers := [(41, 1), (64, 1)] }, { coefficient := 1, powers := [(44, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (52, 1), (67, 1)] }, { coefficient := 1, powers := [(0, 1), (55, 1), (64, 1)] }, { coefficient := 1, powers := [(0, 1), (58, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (38, 1), (67, 1)] }, { coefficient := 1, powers := [(8, 1), (41, 1), (64, 1)] }, { coefficient := 1, powers := [(8, 1), (44, 1), (61, 1)] }, { coefficient := 1, powers := [(16, 1), (35, 1), (67, 1)] }, { coefficient := 1, powers := [(16, 1), (41, 1), (58, 1)] }, { coefficient := 1, powers := [(16, 1), (44, 1), (55, 1)] }, { coefficient := 1, powers := [(24, 1), (35, 1), (64, 1)] }, { coefficient := 1, powers := [(24, 1), (38, 1), (58, 1)] }, { coefficient := 1, powers := [(24, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(32, 1), (35, 1), (61, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1), (55, 1)] }, { coefficient := 1, powers := [(32, 1), (41, 1), (52, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(7, 1), (72, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(56, 1), (74, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 21 → SparsePoly (Fin 75) := ![
  [{ coefficient := 1, powers := [(34, 1), (41, 1), (47, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (34, 1), (41, 1), (47, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (32, 1), (56, 1), (61, 1), (74, 1)] }, { coefficient := -1, powers := [(28, 1), (32, 1), (36, 1), (61, 1), (74, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (19, 1), (34, 1), (41, 1)] }, { coefficient := 1, powers := [(16, 1), (34, 1), (41, 1)] }],
  [{ coefficient := -1, powers := [(11, 1), (32, 1), (35, 1), (61, 1), (74, 1)] }],
  [{ coefficient := -1, powers := [(16, 1), (55, 1), (74, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (21, 1), (55, 1), (72, 1), (74, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (55, 1), (72, 1), (74, 1)] }],
  [{ coefficient := 1, powers := [(32, 1), (41, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (47, 1)] }, { coefficient := 1, powers := [(2, 1), (8, 1), (47, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (27, 1)] }, { coefficient := 1, powers := [(24, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (19, 1)] }, { coefficient := 1, powers := [(16, 1)] }],
  [{ coefficient := 1, powers := [(55, 1), (74, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (34, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(32, 1), (35, 1), (61, 1), (74, 1)] }],
  [{ coefficient := -1, powers := [(34, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(0, 1)] }, { coefficient := -1, powers := [(2, 1), (8, 1)] }],
  [{ coefficient := 1, powers := [(8, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (55, 1), (56, 1), (64, 1), (74, 1)] }],
  [{ coefficient := -1, powers := [(32, 1), (35, 1), (61, 1)] }, { coefficient := -1, powers := [(32, 1), (38, 1), (55, 1)] }]
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
    (values : Fin 75 → R) :
    ¬ ∀ index : Fin 21,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.X5Case573Tree.LeafB7_6.selectedHasNoCommonZero

end Krenn.X5Case573Tree.LeafB7_6
