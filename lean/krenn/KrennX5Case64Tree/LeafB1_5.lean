import KrennSparseCertificate

/-! Selected core of a strict exact certificate over a frozen system. -/

namespace Krenn.X5Case64Tree.LeafB1_5

open Krenn.SparseCertificate
open MvPolynomial

def sourceSystemFileSHA256 : String := "c0e43d232e2b354410b0138bbb7fec5b4fb17d11d4e6ae9019e6a99e6ac2b403"
def sourceSystemSemanticSHA256 : String := "e14630a6889ca47e9a2f8c9a71a922657fd8859676a783eb6f26480e99afee3f"
def certificateSHA256 : String := "d73d09c4557387e59d8387ca3c06c0ac182ce35dc3bf16f4393b19ebd46cb298"
def sourceEquationCount : Nat := 681

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedIndices : Fin 25 → Fin 681 := ![
  1,
  30,
  31,
  43,
  46,
  50,
  51,
  52,
  307,
  397,
  400,
  422,
  423,
  535,
  582,
  619,
  620,
  629,
  642,
  662,
  673,
  676,
  678,
  679,
  680
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 25 → SparsePoly (Fin 73) := ![
  [{ coefficient := 1, powers := [(63, 1)] }],
  [{ coefficient := 1, powers := [(40, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(40, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(47, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(48, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(50, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(50, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(50, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(26, 1), (53, 1)] }, { coefficient := 1, powers := [(32, 1), (43, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (48, 1), (55, 1)] }, { coefficient := 1, powers := [(55, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (50, 1), (55, 1)] }, { coefficient := 1, powers := [(33, 1), (40, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(36, 1), (65, 1)] }, { coefficient := 1, powers := [(39, 1), (59, 1)] }, { coefficient := 1, powers := [(48, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(36, 1), (68, 1)] }, { coefficient := 1, powers := [(42, 1), (59, 1)] }, { coefficient := 1, powers := [(48, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (43, 1), (59, 1)] }, { coefficient := 1, powers := [(26, 1), (50, 1), (53, 1)] }, { coefficient := 1, powers := [(43, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (59, 1), (63, 1)] }, { coefficient := 1, powers := [(26, 1), (40, 1), (59, 1)] }, { coefficient := 1, powers := [(43, 1), (59, 1)] }, { coefficient := 1, powers := [(50, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (39, 1), (67, 1)] }, { coefficient := 1, powers := [(17, 1), (47, 1), (55, 1)] }, { coefficient := 1, powers := [(24, 1), (39, 1), (58, 1)] }, { coefficient := 1, powers := [(32, 1), (39, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (40, 1), (67, 1)] }, { coefficient := 1, powers := [(24, 1), (40, 1), (58, 1)] }, { coefficient := 1, powers := [(32, 1), (40, 1), (55, 1)] }, { coefficient := 1, powers := [(55, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (43, 1), (65, 1)] }, { coefficient := 1, powers := [(19, 1), (43, 1), (59, 1)] }, { coefficient := 1, powers := [(29, 1), (50, 1), (53, 1)] }, { coefficient := 1, powers := [(33, 1), (43, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (63, 1)] }, { coefficient := 1, powers := [(26, 1), (54, 1)] }, { coefficient := 1, powers := [(32, 1), (37, 1), (63, 1)] }, { coefficient := 1, powers := [(32, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(32, 1), (43, 1), (54, 1)] }, { coefficient := 1, powers := [(57, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (50, 1), (63, 1)] }, { coefficient := 1, powers := [(20, 1), (50, 1), (57, 1)] }, { coefficient := 1, powers := [(29, 1), (50, 1), (54, 1)] }, { coefficient := 1, powers := [(33, 1), (37, 1), (63, 1)] }, { coefficient := 1, powers := [(33, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(33, 1), (43, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (53, 1), (68, 1)] }, { coefficient := 1, powers := [(3, 1), (56, 1), (65, 1)] }, { coefficient := 1, powers := [(3, 1), (59, 1), (62, 1)] }, { coefficient := 1, powers := [(11, 1), (39, 1), (68, 1)] }, { coefficient := 1, powers := [(11, 1), (42, 1), (65, 1)] }, { coefficient := 1, powers := [(11, 1), (48, 1), (62, 1)] }, { coefficient := 1, powers := [(19, 1), (36, 1), (68, 1)] }, { coefficient := 1, powers := [(19, 1), (42, 1), (59, 1)] }, { coefficient := 1, powers := [(19, 1), (48, 1), (56, 1)] }, { coefficient := 1, powers := [(28, 1), (36, 1), (65, 1)] }, { coefficient := 1, powers := [(28, 1), (39, 1), (59, 1)] }, { coefficient := 1, powers := [(28, 1), (48, 1), (53, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1), (62, 1)] }, { coefficient := 1, powers := [(33, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(33, 1), (42, 1), (53, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(3, 1)] }],
  [{ coefficient := 1, powers := [(55, 1), (71, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(56, 1)] }],
  [{ coefficient := 1, powers := [(57, 1), (72, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 25 → SparsePoly (Fin 73) := ![
  [{ coefficient := -1, powers := [(1, 1), (11, 1), (17, 1), (32, 1), (42, 1), (54, 1), (59, 1), (72, 1)] }, { coefficient := 1, powers := [(1, 1), (19, 1), (32, 1), (42, 1), (54, 1), (59, 1), (72, 1)] }, { coefficient := -1, powers := [(9, 1), (33, 1), (42, 1), (53, 1), (72, 1)] }, { coefficient := -1, powers := [(11, 1), (17, 1), (32, 1), (42, 1), (50, 1), (54, 1), (72, 1)] }, { coefficient := 1, powers := [(12, 1), (32, 1), (42, 1), (50, 1), (53, 1), (72, 1)] }, { coefficient := 1, powers := [(19, 1), (32, 1), (42, 1), (50, 1), (54, 1), (72, 1)] }],
  [{ coefficient := -1, powers := [(11, 1), (17, 1), (26, 1), (32, 1), (42, 1), (54, 1), (72, 1)] }, { coefficient := 1, powers := [(19, 1), (26, 1), (32, 1), (42, 1), (54, 1), (72, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (33, 1), (36, 1), (62, 1), (71, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (17, 1), (40, 1), (68, 1), (71, 1)] }],
  [{ coefficient := -1, powers := [(11, 1), (17, 1), (42, 1), (71, 1)] }, { coefficient := 1, powers := [(11, 1), (62, 1), (71, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (26, 1), (32, 1), (42, 1), (54, 1), (72, 1)] }, { coefficient := -1, powers := [(29, 1), (32, 1), (42, 1), (54, 1), (72, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (32, 1), (42, 1), (53, 1), (72, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (24, 1), (36, 1), (58, 1), (62, 1), (71, 2)] }, { coefficient := 1, powers := [(20, 1), (32, 1), (36, 1), (62, 1), (71, 1)] }, { coefficient := 1, powers := [(20, 1), (32, 1), (42, 1), (53, 1), (57, 1), (71, 1), (72, 1)] }],
  [{ coefficient := -1, powers := [(33, 1), (42, 1), (54, 1), (72, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (42, 1), (71, 1)] }],
  [{ coefficient := -1, powers := [(24, 1), (36, 1), (58, 1), (62, 1), (71, 2)] }, { coefficient := -1, powers := [(32, 1), (36, 1), (62, 1), (71, 1)] }],
  [{ coefficient := 1, powers := [(28, 1)] }],
  [{ coefficient := 1, powers := [(19, 1)] }],
  [{ coefficient := -1, powers := [(11, 1), (32, 1), (42, 1), (54, 1), (72, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (17, 1), (32, 1), (42, 1), (54, 1), (72, 1)] }, { coefficient := -1, powers := [(19, 1), (32, 1), (42, 1), (54, 1), (72, 1)] }],
  [{ coefficient := -1, powers := [(11, 1), (40, 1), (68, 1), (71, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (39, 1), (68, 1), (71, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1), (62, 1), (71, 1)] }],
  [{ coefficient := 1, powers := [(32, 1), (42, 1), (54, 1), (72, 1)] }],
  [{ coefficient := 1, powers := [(33, 1), (42, 1), (53, 1), (72, 1)] }],
  [{ coefficient := -1, powers := [(32, 1), (42, 1), (53, 1), (72, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(53, 1), (68, 1)] }, { coefficient := 1, powers := [(59, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(11, 1), (39, 1), (68, 1)] }, { coefficient := -1, powers := [(11, 1), (42, 1), (65, 1)] }, { coefficient := -1, powers := [(11, 1), (48, 1), (62, 1)] }, { coefficient := -1, powers := [(20, 1), (32, 1), (42, 1), (50, 1), (53, 1), (57, 1), (72, 1)] }, { coefficient := 1, powers := [(24, 1), (33, 1), (36, 1), (40, 1), (58, 1), (62, 1), (71, 1)] }, { coefficient := -1, powers := [(33, 1), (36, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (65, 1)] }, { coefficient := 1, powers := [(33, 1), (39, 1)] }],
  [{ coefficient := -1, powers := [(33, 1), (42, 1), (53, 1)] }]
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

#print axioms Krenn.X5Case64Tree.LeafB1_5.selectedHasNoCommonZero

end Krenn.X5Case64Tree.LeafB1_5
