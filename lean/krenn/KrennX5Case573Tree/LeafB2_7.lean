import KrennSparseCertificate

/-! Selected core of a strict exact certificate over a frozen system. -/

namespace Krenn.X5Case573Tree.LeafB2_7

open Krenn.SparseCertificate
open MvPolynomial

def sourceSystemFileSHA256 : String := "50cfe79bef2c981cfcd6a9ee39ce92502e8e13415a69a13bd4a6ca7b60c34caf"
def sourceSystemSemanticSHA256 : String := "685b2c1b8df87c0ba107d80143c7a6ecf2f815f2384325e0a083c14785367fe9"
def certificateSHA256 : String := "2880420641c104700eb1a92053345926f459afc5bcdbcf9407bbbe71875407cc"
def sourceEquationCount : Nat := 681

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedIndices : Fin 19 → Fin 681 := ![
  18,
  21,
  24,
  33,
  34,
  37,
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
  675,
  679
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 19 → SparsePoly (Fin 74) := ![
  [{ coefficient := 1, powers := [(25, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(28, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(35, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(42, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(42, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(44, 1), (56, 1)] }],
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
  [{ coefficient := 1, powers := [(0, 1)] }],
  [{ coefficient := 1, powers := [(56, 1), (72, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 19 → SparsePoly (Fin 74) := ![
  [{ coefficient := 1, powers := [(34, 1), (41, 1), (47, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (34, 1), (41, 1), (47, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (32, 1), (56, 1), (61, 1), (72, 1)] }, { coefficient := -1, powers := [(28, 1), (32, 1), (36, 1), (61, 1), (72, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (19, 1), (34, 1), (41, 1)] }, { coefficient := 1, powers := [(16, 1), (34, 1), (41, 1)] }],
  [{ coefficient := -1, powers := [(11, 1), (32, 1), (35, 1), (61, 1), (72, 1)] }],
  [{ coefficient := -1, powers := [(16, 1), (55, 1), (72, 1)] }],
  [{ coefficient := 1, powers := [(32, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (8, 1), (47, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (27, 1)] }, { coefficient := 1, powers := [(24, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (19, 1)] }, { coefficient := 1, powers := [(16, 1)] }],
  [{ coefficient := 1, powers := [(55, 1), (72, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (34, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(32, 1), (35, 1), (61, 1), (72, 1)] }],
  [{ coefficient := -1, powers := [(34, 1), (41, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (8, 1)] }],
  [{ coefficient := 1, powers := [(8, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(52, 1), (67, 1)] }, { coefficient := -1, powers := [(55, 1), (56, 1), (64, 1), (72, 1)] }, { coefficient := 1, powers := [(55, 1), (64, 1)] }, { coefficient := 1, powers := [(58, 1), (61, 1)] }],
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
    (values : Fin 74 → R) :
    ¬ ∀ index : Fin 19,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.X5Case573Tree.LeafB2_7.selectedHasNoCommonZero

end Krenn.X5Case573Tree.LeafB2_7
