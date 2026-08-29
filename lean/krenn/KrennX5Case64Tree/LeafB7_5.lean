import KrennSparseCertificate

/-! Selected core of a strict exact certificate over a frozen system. -/

namespace Krenn.X5Case64Tree.LeafB7_5

open Krenn.SparseCertificate
open MvPolynomial

def sourceSystemFileSHA256 : String := "4f1d87d9dcb3f5ce1df4e3cdfb34359b857a7aa654da4fd7ae945b7750a99081"
def sourceSystemSemanticSHA256 : String := "0a76342061a32d60574e4a351e071299e1f7875a0da6a95f62c1a5c8573a20dd"
def certificateSHA256 : String := "0db7400d3bdf43c00324cd3d2baf025eb95cfdc4f1ecb84b04911da648ff42f2"
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
  671,
  673,
  678,
  679,
  680
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 25 → SparsePoly (Fin 75) := ![
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
  [{ coefficient := 1, powers := [(17, 1), (36, 1), (68, 1)] }, { coefficient := 1, powers := [(17, 1), (42, 1), (59, 1)] }, { coefficient := 1, powers := [(17, 1), (48, 1), (56, 1)] }, { coefficient := 1, powers := [(25, 1), (36, 1), (65, 1)] }, { coefficient := 1, powers := [(25, 1), (39, 1), (59, 1)] }, { coefficient := 1, powers := [(25, 1), (48, 1), (53, 1)] }, { coefficient := 1, powers := [(39, 1), (68, 1)] }, { coefficient := 1, powers := [(42, 1), (65, 1)] }, { coefficient := 1, powers := [(48, 1), (62, 1)] }, { coefficient := 1, powers := [(53, 1), (68, 1)] }, { coefficient := 1, powers := [(56, 1), (65, 1)] }, { coefficient := 1, powers := [(59, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (53, 1), (68, 1)] }, { coefficient := 1, powers := [(3, 1), (56, 1), (65, 1)] }, { coefficient := 1, powers := [(3, 1), (59, 1), (62, 1)] }, { coefficient := 1, powers := [(11, 1), (39, 1), (68, 1)] }, { coefficient := 1, powers := [(11, 1), (42, 1), (65, 1)] }, { coefficient := 1, powers := [(11, 1), (48, 1), (62, 1)] }, { coefficient := 1, powers := [(19, 1), (36, 1), (68, 1)] }, { coefficient := 1, powers := [(19, 1), (42, 1), (59, 1)] }, { coefficient := 1, powers := [(19, 1), (48, 1), (56, 1)] }, { coefficient := 1, powers := [(28, 1), (36, 1), (65, 1)] }, { coefficient := 1, powers := [(28, 1), (39, 1), (59, 1)] }, { coefficient := 1, powers := [(28, 1), (48, 1), (53, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1), (62, 1)] }, { coefficient := 1, powers := [(33, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(33, 1), (42, 1), (53, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(55, 1), (73, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(56, 1)] }],
  [{ coefficient := 1, powers := [(57, 1), (74, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 25 → SparsePoly (Fin 75) := ![
  [{ coefficient := -1, powers := [(1, 1), (11, 1), (17, 1), (32, 1), (42, 1), (54, 1), (59, 1), (74, 1)] }, { coefficient := 1, powers := [(1, 1), (19, 1), (32, 1), (42, 1), (54, 1), (59, 1), (74, 1)] }, { coefficient := -1, powers := [(9, 1), (33, 1), (42, 1), (53, 1), (74, 1)] }, { coefficient := -1, powers := [(11, 1), (17, 1), (32, 1), (42, 1), (50, 1), (54, 1), (74, 1)] }, { coefficient := 1, powers := [(12, 1), (32, 1), (42, 1), (50, 1), (53, 1), (74, 1)] }, { coefficient := 1, powers := [(19, 1), (32, 1), (42, 1), (50, 1), (54, 1), (74, 1)] }],
  [{ coefficient := -1, powers := [(11, 1), (17, 1), (26, 1), (32, 1), (42, 1), (54, 1), (74, 1)] }, { coefficient := 1, powers := [(19, 1), (26, 1), (32, 1), (42, 1), (54, 1), (74, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (33, 1), (36, 1), (62, 1), (73, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (17, 1), (40, 1), (68, 1), (73, 1)] }, { coefficient := 1, powers := [(11, 1), (17, 1), (40, 1), (68, 1), (73, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (17, 1), (42, 1), (73, 1)] }, { coefficient := -1, powers := [(3, 1), (62, 1), (73, 1)] }, { coefficient := -1, powers := [(11, 1), (17, 1), (42, 1), (73, 1)] }, { coefficient := 1, powers := [(11, 1), (62, 1), (73, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (26, 1), (32, 1), (42, 1), (54, 1), (74, 1)] }, { coefficient := -1, powers := [(29, 1), (32, 1), (42, 1), (54, 1), (74, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (32, 1), (42, 1), (53, 1), (74, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (24, 1), (36, 1), (58, 1), (62, 1), (73, 2)] }, { coefficient := 1, powers := [(20, 1), (32, 1), (36, 1), (62, 1), (73, 1)] }, { coefficient := 1, powers := [(20, 1), (32, 1), (42, 1), (53, 1), (57, 1), (73, 1), (74, 1)] }],
  [{ coefficient := -1, powers := [(33, 1), (42, 1), (54, 1), (74, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (42, 1), (73, 1)] }, { coefficient := 1, powers := [(11, 1), (42, 1), (73, 1)] }],
  [{ coefficient := -1, powers := [(24, 1), (36, 1), (58, 1), (62, 1), (73, 2)] }, { coefficient := -1, powers := [(32, 1), (36, 1), (62, 1), (73, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (25, 1)] }, { coefficient := 1, powers := [(28, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (17, 1)] }, { coefficient := 1, powers := [(19, 1)] }],
  [{ coefficient := -1, powers := [(11, 1), (32, 1), (42, 1), (54, 1), (74, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (17, 1), (32, 1), (42, 1), (54, 1), (74, 1)] }, { coefficient := -1, powers := [(19, 1), (32, 1), (42, 1), (54, 1), (74, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (40, 1), (68, 1), (73, 1)] }, { coefficient := -1, powers := [(11, 1), (40, 1), (68, 1), (73, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (39, 1), (68, 1), (73, 1)] }, { coefficient := 1, powers := [(11, 1), (39, 1), (68, 1), (73, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1), (62, 1), (73, 1)] }],
  [{ coefficient := 1, powers := [(32, 1), (42, 1), (54, 1), (74, 1)] }],
  [{ coefficient := 1, powers := [(33, 1), (42, 1), (53, 1), (74, 1)] }],
  [{ coefficient := -1, powers := [(32, 1), (42, 1), (53, 1), (74, 1)] }],
  [{ coefficient := 1, powers := [(3, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(3, 1), (39, 1), (68, 1)] }, { coefficient := 1, powers := [(3, 1), (42, 1), (65, 1)] }, { coefficient := 1, powers := [(3, 1), (48, 1), (62, 1)] }, { coefficient := -1, powers := [(11, 1), (39, 1), (68, 1)] }, { coefficient := -1, powers := [(11, 1), (42, 1), (65, 1)] }, { coefficient := -1, powers := [(11, 1), (48, 1), (62, 1)] }, { coefficient := -1, powers := [(20, 1), (32, 1), (42, 1), (50, 1), (53, 1), (57, 1), (74, 1)] }, { coefficient := 1, powers := [(24, 1), (33, 1), (36, 1), (40, 1), (58, 1), (62, 1), (73, 1)] }, { coefficient := -1, powers := [(33, 1), (36, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(33, 1), (39, 1)] }],
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
    (values : Fin 75 → R) :
    ¬ ∀ index : Fin 25,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.X5Case64Tree.LeafB7_5.selectedHasNoCommonZero

end Krenn.X5Case64Tree.LeafB7_5
