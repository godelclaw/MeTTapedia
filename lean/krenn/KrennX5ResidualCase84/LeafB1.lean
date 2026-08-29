import KrennSparseCertificate

/-! Selected core of a strict exact certificate over a frozen system. -/

namespace Krenn.X5ResidualCase84.LeafB1

open Krenn.SparseCertificate
open MvPolynomial

def sourceSystemFileSHA256 : String := "fe89aae2c85416287db328bd023b96d50123afd94be5543f1699715dc1f67a72"
def sourceSystemSemanticSHA256 : String := "b608a1d5044cad3c97561a4fbaf7d201bf4b65341e542f520ff7c237788e307d"
def certificateSHA256 : String := "9378c72d4c47b623d0a4108514e7be03db30d99dfc02b87527913da52c14c980"
def sourceEquationCount : Nat := 678

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedIndices : Fin 27 → Fin 678 := ![
  2,
  7,
  24,
  25,
  26,
  27,
  29,
  33,
  416,
  417,
  422,
  423,
  424,
  425,
  427,
  445,
  542,
  624,
  632,
  660,
  662,
  671,
  673,
  674,
  675,
  676,
  677
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 27 → SparsePoly (Fin 71) := ![
  [{ coefficient := 1, powers := [(9, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(15, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(36, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(36, 1), (69, 1)] }],
  [{ coefficient := 1, powers := [(37, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(37, 1), (68, 1)] }],
  [{ coefficient := 1, powers := [(39, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(42, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (63, 1)] }, { coefficient := 1, powers := [(18, 1), (57, 1)] }, { coefficient := 1, powers := [(26, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (63, 1)] }, { coefficient := 1, powers := [(20, 1), (57, 1)] }, { coefficient := 1, powers := [(28, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(36, 1), (65, 1)] }, { coefficient := 1, powers := [(39, 1), (59, 1)] }, { coefficient := 1, powers := [(47, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(36, 1), (68, 1)] }, { coefficient := 1, powers := [(42, 1), (59, 1)] }, { coefficient := 1, powers := [(47, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(37, 1), (66, 1)] }, { coefficient := 1, powers := [(40, 1), (60, 1)] }, { coefficient := 1, powers := [(51, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(37, 1), (69, 1)] }, { coefficient := 1, powers := [(43, 1), (60, 1)] }, { coefficient := 1, powers := [(51, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(40, 1), (69, 1)] }, { coefficient := 1, powers := [(43, 1), (66, 1)] }, { coefficient := 1, powers := [(51, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (60, 1), (62, 1)] }, { coefficient := 1, powers := [(15, 1), (51, 1), (62, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (36, 1), (69, 1)] }, { coefficient := 1, powers := [(26, 1), (36, 1), (66, 1)] }, { coefficient := 1, powers := [(48, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (48, 1), (62, 1)] }, { coefficient := 1, powers := [(17, 1), (42, 1), (60, 1)] }, { coefficient := 1, powers := [(25, 1), (39, 1), (60, 1)] }, { coefficient := 1, powers := [(60, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (48, 1), (63, 1)] }, { coefficient := 1, powers := [(23, 1), (36, 1), (69, 1)] }, { coefficient := 1, powers := [(31, 1), (36, 1), (66, 1)] }, { coefficient := 1, powers := [(34, 1), (36, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (48, 1), (63, 1)] }, { coefficient := 1, powers := [(18, 1), (48, 1), (57, 1)] }, { coefficient := 1, powers := [(26, 1), (48, 1), (54, 1)] }, { coefficient := 1, powers := [(54, 1), (69, 1)] }, { coefficient := 1, powers := [(57, 1), (66, 1)] }, { coefficient := 1, powers := [(60, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (50, 1), (63, 1)] }, { coefficient := 1, powers := [(20, 1), (50, 1), (57, 1)] }, { coefficient := 1, powers := [(28, 1), (50, 1), (54, 1)] }, { coefficient := 1, powers := [(33, 1), (37, 1), (63, 1)] }, { coefficient := 1, powers := [(33, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(33, 1), (43, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (36, 1), (68, 1)] }, { coefficient := 1, powers := [(17, 1), (42, 1), (59, 1)] }, { coefficient := 1, powers := [(17, 1), (47, 1), (56, 1)] }, { coefficient := 1, powers := [(25, 1), (36, 1), (65, 1)] }, { coefficient := 1, powers := [(25, 1), (39, 1), (59, 1)] }, { coefficient := 1, powers := [(25, 1), (47, 1), (53, 1)] }, { coefficient := 1, powers := [(39, 1), (68, 1)] }, { coefficient := 1, powers := [(42, 1), (65, 1)] }, { coefficient := 1, powers := [(47, 1), (62, 1)] }, { coefficient := 1, powers := [(53, 1), (68, 1)] }, { coefficient := 1, powers := [(56, 1), (65, 1)] }, { coefficient := 1, powers := [(59, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (53, 1), (68, 1)] }, { coefficient := 1, powers := [(3, 1), (56, 1), (65, 1)] }, { coefficient := 1, powers := [(3, 1), (59, 1), (62, 1)] }, { coefficient := 1, powers := [(11, 1), (39, 1), (68, 1)] }, { coefficient := 1, powers := [(11, 1), (42, 1), (65, 1)] }, { coefficient := 1, powers := [(11, 1), (47, 1), (62, 1)] }, { coefficient := 1, powers := [(19, 1), (36, 1), (68, 1)] }, { coefficient := 1, powers := [(19, 1), (42, 1), (59, 1)] }, { coefficient := 1, powers := [(19, 1), (47, 1), (56, 1)] }, { coefficient := 1, powers := [(27, 1), (36, 1), (65, 1)] }, { coefficient := 1, powers := [(27, 1), (39, 1), (59, 1)] }, { coefficient := 1, powers := [(27, 1), (47, 1), (53, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1), (62, 1)] }, { coefficient := 1, powers := [(33, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(33, 1), (42, 1), (53, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(7, 1), (54, 1), (69, 1)] }, { coefficient := 1, powers := [(7, 1), (57, 1), (66, 1)] }, { coefficient := 1, powers := [(7, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(15, 1), (40, 1), (69, 1)] }, { coefficient := 1, powers := [(15, 1), (43, 1), (66, 1)] }, { coefficient := 1, powers := [(15, 1), (51, 1), (63, 1)] }, { coefficient := 1, powers := [(23, 1), (37, 1), (69, 1)] }, { coefficient := 1, powers := [(23, 1), (43, 1), (60, 1)] }, { coefficient := 1, powers := [(23, 1), (51, 1), (57, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1), (66, 1)] }, { coefficient := 1, powers := [(31, 1), (40, 1), (60, 1)] }, { coefficient := 1, powers := [(31, 1), (51, 1), (54, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1), (63, 1)] }, { coefficient := 1, powers := [(34, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(34, 1), (43, 1), (54, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(54, 1)] }],
  [{ coefficient := 1, powers := [(57, 1)] }],
  [{ coefficient := 1, powers := [(63, 1), (70, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 27 → SparsePoly (Fin 71) := ![
  [{ coefficient := 1, powers := [(3, 1), (7, 1), (48, 1), (59, 1), (63, 1)] }, { coefficient := -1, powers := [(7, 1), (11, 1), (48, 1), (59, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (51, 1), (59, 1), (63, 1)] }, { coefficient := 1, powers := [(11, 1), (51, 1), (59, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (26, 1), (33, 1), (37, 1), (62, 1)] }, { coefficient := -1, powers := [(31, 1), (33, 1), (37, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (18, 1), (33, 1), (37, 1), (62, 1)] }, { coefficient := -1, powers := [(23, 1), (33, 1), (37, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (34, 1), (56, 1), (63, 1)] }, { coefficient := -1, powers := [(11, 1), (34, 1), (56, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (34, 1), (53, 1), (63, 1)] }, { coefficient := -1, powers := [(11, 1), (34, 1), (53, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (7, 1), (25, 1), (59, 1), (63, 1)] }, { coefficient := -1, powers := [(7, 1), (11, 1), (25, 1), (59, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (7, 1), (17, 1), (59, 1), (63, 1)] }, { coefficient := -1, powers := [(7, 1), (11, 1), (17, 1), (59, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (7, 1), (48, 1), (53, 1), (68, 1)] }, { coefficient := -1, powers := [(3, 1), (7, 1), (48, 1), (56, 1), (65, 1)] }, { coefficient := -1, powers := [(3, 1), (7, 1), (48, 1), (59, 1), (62, 1), (63, 1), (70, 1)] }, { coefficient := 1, powers := [(7, 1), (11, 1), (48, 1), (53, 1), (68, 1)] }, { coefficient := 1, powers := [(7, 1), (11, 1), (48, 1), (56, 1), (65, 1)] }, { coefficient := 1, powers := [(7, 1), (11, 1), (48, 1), (59, 1), (62, 1), (63, 1), (70, 1)] }, { coefficient := -1, powers := [(7, 1), (33, 1), (36, 1), (48, 1), (62, 1)] }, { coefficient := -1, powers := [(7, 1), (33, 1), (39, 1), (48, 1), (56, 1)] }, { coefficient := -1, powers := [(7, 1), (33, 1), (42, 1), (48, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(34, 1), (39, 1), (50, 1), (56, 1)] }, { coefficient := -1, powers := [(34, 1), (42, 1), (50, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(11, 1), (25, 1)] }, { coefficient := 1, powers := [(27, 1)] }],
  [{ coefficient := -1, powers := [(11, 1), (17, 1)] }, { coefficient := 1, powers := [(19, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (31, 1), (53, 1), (68, 1)] }, { coefficient := 1, powers := [(3, 1), (31, 1), (56, 1), (65, 1)] }, { coefficient := 1, powers := [(3, 1), (31, 1), (59, 1), (62, 1), (63, 1), (70, 1)] }, { coefficient := -1, powers := [(11, 1), (31, 1), (53, 1), (68, 1)] }, { coefficient := -1, powers := [(11, 1), (31, 1), (56, 1), (65, 1)] }, { coefficient := -1, powers := [(11, 1), (31, 1), (59, 1), (62, 1), (63, 1), (70, 1)] }, { coefficient := 1, powers := [(31, 1), (33, 1), (36, 1), (62, 1)] }, { coefficient := 1, powers := [(31, 1), (33, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(31, 1), (33, 1), (42, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (23, 1), (53, 1), (68, 1)] }, { coefficient := 1, powers := [(3, 1), (23, 1), (56, 1), (65, 1)] }, { coefficient := 1, powers := [(3, 1), (23, 1), (59, 1), (62, 1), (63, 1), (70, 1)] }, { coefficient := -1, powers := [(11, 1), (23, 1), (53, 1), (68, 1)] }, { coefficient := -1, powers := [(11, 1), (23, 1), (56, 1), (65, 1)] }, { coefficient := -1, powers := [(11, 1), (23, 1), (59, 1), (62, 1), (63, 1), (70, 1)] }, { coefficient := 1, powers := [(23, 1), (33, 1), (36, 1), (62, 1)] }, { coefficient := 1, powers := [(23, 1), (33, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(23, 1), (33, 1), (42, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (15, 1), (53, 1), (68, 1)] }, { coefficient := 1, powers := [(3, 1), (15, 1), (56, 1), (65, 1)] }, { coefficient := 1, powers := [(3, 1), (15, 1), (59, 1), (62, 1), (63, 1), (70, 1)] }, { coefficient := -1, powers := [(11, 1), (15, 1), (53, 1), (68, 1)] }, { coefficient := -1, powers := [(11, 1), (15, 1), (56, 1), (65, 1)] }, { coefficient := -1, powers := [(11, 1), (15, 1), (59, 1), (62, 1), (63, 1), (70, 1)] }, { coefficient := 1, powers := [(15, 1), (33, 1), (36, 1), (62, 1)] }, { coefficient := 1, powers := [(15, 1), (33, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(15, 1), (33, 1), (42, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (59, 1), (63, 1)] }, { coefficient := -1, powers := [(11, 1), (59, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(14, 1), (33, 1), (37, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (7, 1), (59, 1), (63, 1)] }, { coefficient := 1, powers := [(7, 1), (11, 1), (59, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(33, 1), (37, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (7, 1), (53, 1), (68, 1)] }, { coefficient := 1, powers := [(3, 1), (7, 1), (56, 1), (65, 1)] }, { coefficient := 1, powers := [(3, 1), (7, 1), (59, 1), (62, 1), (63, 1), (70, 1)] }, { coefficient := -1, powers := [(7, 1), (11, 1), (53, 1), (68, 1)] }, { coefficient := -1, powers := [(7, 1), (11, 1), (56, 1), (65, 1)] }, { coefficient := -1, powers := [(7, 1), (11, 1), (59, 1), (62, 1), (63, 1), (70, 1)] }, { coefficient := 1, powers := [(7, 1), (33, 1), (36, 1), (62, 1)] }, { coefficient := 1, powers := [(7, 1), (33, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(7, 1), (33, 1), (42, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(34, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(34, 1), (42, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(11, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(3, 1), (53, 1), (68, 1)] }, { coefficient := -1, powers := [(3, 1), (56, 1), (65, 1)] }, { coefficient := -1, powers := [(3, 1), (59, 1), (62, 1), (63, 1), (70, 1)] }, { coefficient := 1, powers := [(11, 1), (53, 1), (68, 1)] }, { coefficient := 1, powers := [(11, 1), (56, 1), (65, 1)] }, { coefficient := 1, powers := [(11, 1), (59, 1), (62, 1), (63, 1), (70, 1)] }, { coefficient := -1, powers := [(33, 1), (36, 1), (62, 1)] }, { coefficient := -1, powers := [(33, 1), (39, 1), (56, 1)] }, { coefficient := -1, powers := [(33, 1), (42, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (34, 1), (43, 1), (53, 1), (68, 1)] }, { coefficient := 1, powers := [(3, 1), (34, 1), (43, 1), (56, 1), (65, 1)] }, { coefficient := 1, powers := [(3, 1), (34, 1), (43, 1), (59, 1), (62, 1), (63, 1), (70, 1)] }, { coefficient := -1, powers := [(11, 1), (34, 1), (43, 1), (53, 1), (68, 1)] }, { coefficient := -1, powers := [(11, 1), (34, 1), (43, 1), (56, 1), (65, 1)] }, { coefficient := -1, powers := [(11, 1), (34, 1), (43, 1), (59, 1), (62, 1), (63, 1), (70, 1)] }, { coefficient := 1, powers := [(33, 1), (34, 1), (36, 1), (43, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (34, 1), (40, 1), (53, 1), (68, 1)] }, { coefficient := 1, powers := [(3, 1), (34, 1), (40, 1), (56, 1), (65, 1)] }, { coefficient := 1, powers := [(3, 1), (34, 1), (40, 1), (59, 1), (62, 1), (63, 1), (70, 1)] }, { coefficient := -1, powers := [(11, 1), (34, 1), (40, 1), (53, 1), (68, 1)] }, { coefficient := -1, powers := [(11, 1), (34, 1), (40, 1), (56, 1), (65, 1)] }, { coefficient := -1, powers := [(11, 1), (34, 1), (40, 1), (59, 1), (62, 1), (63, 1), (70, 1)] }, { coefficient := 1, powers := [(33, 1), (34, 1), (36, 1), (40, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (34, 1), (37, 1), (59, 1), (62, 1), (63, 1)] }, { coefficient := -1, powers := [(3, 1), (59, 1), (62, 1)] }, { coefficient := -1, powers := [(11, 1), (34, 1), (37, 1), (59, 1), (62, 1), (63, 1)] }, { coefficient := 1, powers := [(11, 1), (59, 1), (62, 1)] }]
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
    (values : Fin 71 → R) :
    ¬ ∀ index : Fin 27,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.X5ResidualCase84.LeafB1.selectedHasNoCommonZero

end Krenn.X5ResidualCase84.LeafB1
