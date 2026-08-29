import KrennSparseCertificate

/-! Selected core of a strict exact certificate over a frozen system. -/

namespace Krenn.X5Case64Tree.LeafB7_0

open Krenn.SparseCertificate
open MvPolynomial

def sourceSystemFileSHA256 : String := "4a2b06405cf1f79948c45282a96c5256eb1f21b79fc33a872f724db351d3cc0f"
def sourceSystemSemanticSHA256 : String := "cd1f411dedab01d04b4bd175683e57c221e0d9da2da90d2523133e74eb0ab042"
def certificateSHA256 : String := "ad0b2102ecd5ff275aa8f709df4983f9236707aa78b82d6f53b255b10d6af6fa"
def sourceEquationCount : Nat := 681

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedIndices : Fin 18 → Fin 681 := ![
  1,
  47,
  48,
  420,
  422,
  423,
  424,
  426,
  643,
  660,
  664,
  666,
  671,
  673,
  674,
  675,
  679,
  680
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 18 → SparsePoly (Fin 73) := ![
  [{ coefficient := 1, powers := [(63, 1)] }],
  [{ coefficient := 1, powers := [(49, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(49, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (56, 1)] }, { coefficient := 1, powers := [(25, 1), (53, 1)] }, { coefficient := 1, powers := [(62, 1)] }],
  [{ coefficient := 1, powers := [(36, 1), (65, 1)] }, { coefficient := 1, powers := [(39, 1), (59, 1)] }, { coefficient := 1, powers := [(48, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(36, 1), (68, 1)] }, { coefficient := 1, powers := [(42, 1), (59, 1)] }, { coefficient := 1, powers := [(48, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(37, 1), (66, 1)] }, { coefficient := 1, powers := [(40, 1), (60, 1)] }, { coefficient := 1, powers := [(51, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(40, 1), (69, 1)] }, { coefficient := 1, powers := [(43, 1), (66, 1)] }, { coefficient := 1, powers := [(51, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (53, 1), (68, 1)] }, { coefficient := 1, powers := [(0, 1), (56, 1), (65, 1)] }, { coefficient := 1, powers := [(0, 1), (59, 1), (62, 1)] }, { coefficient := 1, powers := [(17, 1), (45, 1), (56, 1)] }, { coefficient := 1, powers := [(25, 1), (45, 1), (53, 1)] }, { coefficient := 1, powers := [(45, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (49, 1), (63, 1)] }, { coefficient := 1, powers := [(26, 1), (49, 1), (54, 1)] }, { coefficient := 1, powers := [(49, 1), (57, 1)] }, { coefficient := 1, powers := [(54, 1), (69, 1)] }, { coefficient := 1, powers := [(57, 1), (66, 1)] }, { coefficient := 1, powers := [(60, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (49, 1), (62, 1)] }, { coefficient := 1, powers := [(22, 1), (49, 1), (56, 1)] }, { coefficient := 1, powers := [(30, 1), (49, 1), (53, 1)] }, { coefficient := 1, powers := [(34, 1), (36, 1), (62, 1)] }, { coefficient := 1, powers := [(34, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(34, 1), (42, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (54, 1), (69, 1)] }, { coefficient := 1, powers := [(1, 1), (57, 1), (66, 1)] }, { coefficient := 1, powers := [(1, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(9, 1), (40, 1), (69, 1)] }, { coefficient := 1, powers := [(9, 1), (43, 1), (66, 1)] }, { coefficient := 1, powers := [(9, 1), (51, 1), (63, 1)] }, { coefficient := 1, powers := [(26, 1), (37, 1), (66, 1)] }, { coefficient := 1, powers := [(26, 1), (40, 1), (60, 1)] }, { coefficient := 1, powers := [(26, 1), (51, 1), (54, 1)] }, { coefficient := 1, powers := [(37, 1), (69, 1)] }, { coefficient := 1, powers := [(43, 1), (60, 1)] }, { coefficient := 1, powers := [(51, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (36, 1), (68, 1)] }, { coefficient := 1, powers := [(17, 1), (42, 1), (59, 1)] }, { coefficient := 1, powers := [(17, 1), (48, 1), (56, 1)] }, { coefficient := 1, powers := [(25, 1), (36, 1), (65, 1)] }, { coefficient := 1, powers := [(25, 1), (39, 1), (59, 1)] }, { coefficient := 1, powers := [(25, 1), (48, 1), (53, 1)] }, { coefficient := 1, powers := [(39, 1), (68, 1)] }, { coefficient := 1, powers := [(42, 1), (65, 1)] }, { coefficient := 1, powers := [(48, 1), (62, 1)] }, { coefficient := 1, powers := [(53, 1), (68, 1)] }, { coefficient := 1, powers := [(56, 1), (65, 1)] }, { coefficient := 1, powers := [(59, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (53, 1), (68, 1)] }, { coefficient := 1, powers := [(3, 1), (56, 1), (65, 1)] }, { coefficient := 1, powers := [(3, 1), (59, 1), (62, 1)] }, { coefficient := 1, powers := [(11, 1), (39, 1), (68, 1)] }, { coefficient := 1, powers := [(11, 1), (42, 1), (65, 1)] }, { coefficient := 1, powers := [(11, 1), (48, 1), (62, 1)] }, { coefficient := 1, powers := [(19, 1), (36, 1), (68, 1)] }, { coefficient := 1, powers := [(19, 1), (42, 1), (59, 1)] }, { coefficient := 1, powers := [(19, 1), (48, 1), (56, 1)] }, { coefficient := 1, powers := [(28, 1), (36, 1), (65, 1)] }, { coefficient := 1, powers := [(28, 1), (39, 1), (59, 1)] }, { coefficient := 1, powers := [(28, 1), (48, 1), (53, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1), (62, 1)] }, { coefficient := 1, powers := [(33, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(33, 1), (42, 1), (53, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(7, 1), (54, 1), (69, 1)] }, { coefficient := 1, powers := [(7, 1), (57, 1), (66, 1)] }, { coefficient := 1, powers := [(7, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(15, 1), (40, 1), (69, 1)] }, { coefficient := 1, powers := [(15, 1), (43, 1), (66, 1)] }, { coefficient := 1, powers := [(15, 1), (51, 1), (63, 1)] }, { coefficient := 1, powers := [(23, 1), (37, 1), (69, 1)] }, { coefficient := 1, powers := [(23, 1), (43, 1), (60, 1)] }, { coefficient := 1, powers := [(23, 1), (51, 1), (57, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1), (66, 1)] }, { coefficient := 1, powers := [(31, 1), (40, 1), (60, 1)] }, { coefficient := 1, powers := [(31, 1), (51, 1), (54, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1), (63, 1)] }, { coefficient := 1, powers := [(34, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(34, 1), (43, 1), (54, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (70, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(56, 1)] }],
  [{ coefficient := 1, powers := [(57, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 18 → SparsePoly (Fin 73) := ![
  [{ coefficient := 1, powers := [(1, 1), (9, 1), (23, 1), (49, 1)] }, { coefficient := -1, powers := [(7, 1), (9, 1), (49, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (25, 1), (33, 1), (43, 1), (54, 1)] }, { coefficient := -1, powers := [(30, 1), (33, 1), (43, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (23, 1), (26, 1)] }, { coefficient := -1, powers := [(7, 1), (26, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (34, 1), (43, 1), (45, 1), (54, 1), (70, 1)] }, { coefficient := 1, powers := [(11, 1), (34, 1), (43, 1), (45, 1), (54, 1), (70, 1)] }, { coefficient := -1, powers := [(14, 1), (33, 1), (43, 1), (49, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(11, 1), (25, 1), (34, 1), (43, 1), (54, 1)] }, { coefficient := 1, powers := [(28, 1), (34, 1), (43, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(11, 1), (17, 1), (34, 1), (43, 1), (54, 1)] }, { coefficient := 1, powers := [(19, 1), (34, 1), (43, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(23, 1), (26, 1)] }, { coefficient := 1, powers := [(31, 1)] }],
  [{ coefficient := -1, powers := [(9, 1), (23, 1)] }, { coefficient := 1, powers := [(15, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (34, 1), (43, 1), (54, 1), (70, 1)] }, { coefficient := -1, powers := [(11, 1), (34, 1), (43, 1), (54, 1), (70, 1)] }],
  [{ coefficient := -1, powers := [(1, 1), (23, 1)] }, { coefficient := 1, powers := [(7, 1)] }],
  [{ coefficient := 1, powers := [(33, 1), (43, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(23, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (34, 1), (43, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(34, 1), (43, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(3, 1), (34, 1), (43, 1), (53, 1), (54, 1), (68, 1)] }, { coefficient := -1, powers := [(3, 1), (34, 1), (43, 1), (54, 1), (59, 1), (62, 1)] }, { coefficient := 1, powers := [(11, 1), (34, 1), (43, 1), (53, 1), (54, 1), (68, 1)] }, { coefficient := 1, powers := [(11, 1), (34, 1), (43, 1), (54, 1), (59, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (3, 1), (34, 1), (43, 1), (54, 1), (65, 1), (70, 1)] }, { coefficient := 1, powers := [(0, 1), (11, 1), (34, 1), (43, 1), (54, 1), (65, 1), (70, 1)] }, { coefficient := 1, powers := [(3, 1), (34, 1), (43, 1), (54, 1), (65, 1)] }, { coefficient := -1, powers := [(11, 1), (34, 1), (43, 1), (54, 1), (65, 1)] }, { coefficient := 1, powers := [(14, 1), (17, 1), (33, 1), (43, 1), (49, 1), (54, 1)] }, { coefficient := -1, powers := [(22, 1), (33, 1), (43, 1), (49, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (23, 1), (49, 1)] }, { coefficient := -1, powers := [(7, 1), (49, 1)] }, { coefficient := 1, powers := [(34, 1), (40, 1)] }]
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
    ¬ ∀ index : Fin 18,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.X5Case64Tree.LeafB7_0.selectedHasNoCommonZero

end Krenn.X5Case64Tree.LeafB7_0
