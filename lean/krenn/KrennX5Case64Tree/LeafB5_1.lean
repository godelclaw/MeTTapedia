import KrennSparseCertificate

/-! Selected core of a strict exact certificate over a frozen system. -/

namespace Krenn.X5Case64Tree.LeafB5_1

open Krenn.SparseCertificate
open MvPolynomial

def sourceSystemFileSHA256 : String := "2988b0ceb9f95e1105ab553856e736a62bf0b674a28735887e90fc926252293c"
def sourceSystemSemanticSHA256 : String := "c3b1a3d6ad201b0592100d5f36847671b88c6c10cf47c5e66332af7c9ef203f9"
def certificateSHA256 : String := "8b244c3822ed24cb4fb9c0e5b6f32c6a72108563003cef3e877e4741d51f29d8"
def sourceEquationCount : Nat := 681

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedIndices : Fin 23 → Fin 681 := ![
  1,
  26,
  30,
  50,
  307,
  384,
  416,
  420,
  422,
  423,
  535,
  582,
  629,
  642,
  643,
  662,
  671,
  673,
  675,
  676,
  677,
  679,
  680
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 23 → SparsePoly (Fin 73) := ![
  [{ coefficient := 1, powers := [(63, 1)] }],
  [{ coefficient := 1, powers := [(36, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(40, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(50, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(26, 1), (53, 1)] }, { coefficient := 1, powers := [(32, 1), (43, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (53, 1), (67, 1)] }, { coefficient := 1, powers := [(53, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (63, 1)] }, { coefficient := 1, powers := [(20, 1), (57, 1)] }, { coefficient := 1, powers := [(29, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (56, 1)] }, { coefficient := 1, powers := [(25, 1), (53, 1)] }, { coefficient := 1, powers := [(62, 1)] }],
  [{ coefficient := 1, powers := [(36, 1), (65, 1)] }, { coefficient := 1, powers := [(39, 1), (59, 1)] }, { coefficient := 1, powers := [(48, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(36, 1), (68, 1)] }, { coefficient := 1, powers := [(42, 1), (59, 1)] }, { coefficient := 1, powers := [(48, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (43, 1), (59, 1)] }, { coefficient := 1, powers := [(26, 1), (50, 1), (53, 1)] }, { coefficient := 1, powers := [(43, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (59, 1), (63, 1)] }, { coefficient := 1, powers := [(26, 1), (40, 1), (59, 1)] }, { coefficient := 1, powers := [(43, 1), (59, 1)] }, { coefficient := 1, powers := [(50, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (43, 1), (65, 1)] }, { coefficient := 1, powers := [(19, 1), (43, 1), (59, 1)] }, { coefficient := 1, powers := [(29, 1), (50, 1), (53, 1)] }, { coefficient := 1, powers := [(33, 1), (43, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (63, 1)] }, { coefficient := 1, powers := [(26, 1), (54, 1)] }, { coefficient := 1, powers := [(32, 1), (37, 1), (63, 1)] }, { coefficient := 1, powers := [(32, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(32, 1), (43, 1), (54, 1)] }, { coefficient := 1, powers := [(57, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (53, 1), (68, 1)] }, { coefficient := 1, powers := [(0, 1), (56, 1), (65, 1)] }, { coefficient := 1, powers := [(0, 1), (59, 1), (62, 1)] }, { coefficient := 1, powers := [(17, 1), (45, 1), (56, 1)] }, { coefficient := 1, powers := [(25, 1), (45, 1), (53, 1)] }, { coefficient := 1, powers := [(45, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (50, 1), (63, 1)] }, { coefficient := 1, powers := [(20, 1), (50, 1), (57, 1)] }, { coefficient := 1, powers := [(29, 1), (50, 1), (54, 1)] }, { coefficient := 1, powers := [(33, 1), (37, 1), (63, 1)] }, { coefficient := 1, powers := [(33, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(33, 1), (43, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (36, 1), (68, 1)] }, { coefficient := 1, powers := [(17, 1), (42, 1), (59, 1)] }, { coefficient := 1, powers := [(17, 1), (48, 1), (56, 1)] }, { coefficient := 1, powers := [(25, 1), (36, 1), (65, 1)] }, { coefficient := 1, powers := [(25, 1), (39, 1), (59, 1)] }, { coefficient := 1, powers := [(25, 1), (48, 1), (53, 1)] }, { coefficient := 1, powers := [(39, 1), (68, 1)] }, { coefficient := 1, powers := [(42, 1), (65, 1)] }, { coefficient := 1, powers := [(48, 1), (62, 1)] }, { coefficient := 1, powers := [(53, 1), (68, 1)] }, { coefficient := 1, powers := [(56, 1), (65, 1)] }, { coefficient := 1, powers := [(59, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (53, 1), (68, 1)] }, { coefficient := 1, powers := [(3, 1), (56, 1), (65, 1)] }, { coefficient := 1, powers := [(3, 1), (59, 1), (62, 1)] }, { coefficient := 1, powers := [(11, 1), (39, 1), (68, 1)] }, { coefficient := 1, powers := [(11, 1), (42, 1), (65, 1)] }, { coefficient := 1, powers := [(11, 1), (48, 1), (62, 1)] }, { coefficient := 1, powers := [(19, 1), (36, 1), (68, 1)] }, { coefficient := 1, powers := [(19, 1), (42, 1), (59, 1)] }, { coefficient := 1, powers := [(19, 1), (48, 1), (56, 1)] }, { coefficient := 1, powers := [(28, 1), (36, 1), (65, 1)] }, { coefficient := 1, powers := [(28, 1), (39, 1), (59, 1)] }, { coefficient := 1, powers := [(28, 1), (48, 1), (53, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1), (62, 1)] }, { coefficient := 1, powers := [(33, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(33, 1), (42, 1), (53, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (70, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(3, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (71, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(56, 1)] }],
  [{ coefficient := 1, powers := [(57, 1), (72, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 23 → SparsePoly (Fin 73) := ![
  [{ coefficient := -1, powers := [(1, 1), (11, 1), (17, 1), (32, 1), (42, 1), (54, 1), (59, 1), (72, 1)] }, { coefficient := 1, powers := [(1, 1), (19, 1), (32, 1), (42, 1), (54, 1), (59, 1), (72, 1)] }, { coefficient := -1, powers := [(9, 1), (33, 1), (42, 1), (53, 1), (72, 1)] }, { coefficient := -1, powers := [(11, 1), (17, 1), (32, 1), (42, 1), (50, 1), (54, 1), (72, 1)] }, { coefficient := 1, powers := [(19, 1), (32, 1), (42, 1), (50, 1), (54, 1), (72, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (33, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(11, 1), (17, 1), (26, 1), (32, 1), (42, 1), (54, 1), (72, 1)] }, { coefficient := 1, powers := [(19, 1), (26, 1), (32, 1), (42, 1), (54, 1), (72, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (26, 1), (32, 1), (42, 1), (54, 1), (72, 1)] }, { coefficient := -1, powers := [(29, 1), (32, 1), (42, 1), (54, 1), (72, 1)] }],
  [{ coefficient := -1, powers := [(33, 1), (42, 1), (54, 1), (72, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (25, 1), (33, 1), (36, 1), (71, 1)] }],
  [{ coefficient := 1, powers := [(32, 1), (42, 1), (50, 1), (53, 1), (72, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (33, 1), (36, 1), (67, 1)] }, { coefficient := 1, powers := [(7, 1), (33, 1), (36, 1), (71, 1)] }, { coefficient := 1, powers := [(11, 1), (45, 1), (70, 1)] }],
  [{ coefficient := -1, powers := [(11, 1), (25, 1)] }, { coefficient := 1, powers := [(28, 1)] }],
  [{ coefficient := -1, powers := [(11, 1), (17, 1)] }, { coefficient := 1, powers := [(19, 1)] }],
  [{ coefficient := -1, powers := [(11, 1), (32, 1), (42, 1), (54, 1), (72, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (17, 1), (32, 1), (42, 1), (54, 1), (72, 1)] }, { coefficient := -1, powers := [(19, 1), (32, 1), (42, 1), (54, 1), (72, 1)] }],
  [{ coefficient := 1, powers := [(32, 1), (42, 1), (54, 1), (72, 1)] }],
  [{ coefficient := 1, powers := [(33, 1), (42, 1), (53, 1), (72, 1)] }],
  [{ coefficient := -1, powers := [(11, 1), (70, 1)] }],
  [{ coefficient := -1, powers := [(32, 1), (42, 1), (53, 1), (72, 1)] }],
  [{ coefficient := 1, powers := [(11, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(11, 1), (53, 1), (68, 1)] }, { coefficient := 1, powers := [(11, 1), (59, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(53, 1), (68, 1)] }, { coefficient := 1, powers := [(59, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (25, 1), (33, 1), (36, 1), (53, 1), (67, 1)] }, { coefficient := -1, powers := [(33, 1), (36, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (11, 1), (65, 1), (70, 1)] }, { coefficient := 1, powers := [(3, 1), (65, 1)] }, { coefficient := -1, powers := [(7, 1), (17, 1), (33, 1), (36, 1), (67, 1)] }, { coefficient := -1, powers := [(7, 1), (17, 1), (33, 1), (36, 1), (71, 1)] }, { coefficient := -1, powers := [(11, 1), (65, 1)] }, { coefficient := 1, powers := [(33, 1), (39, 1)] }],
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
    ¬ ∀ index : Fin 23,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.X5Case64Tree.LeafB5_1.selectedHasNoCommonZero

end Krenn.X5Case64Tree.LeafB5_1
