import KrennSparseCertificate

/-! Selected core of a strict exact certificate over a frozen system. -/

namespace Krenn.X5ResidualCase429.LeafB7

open Krenn.SparseCertificate
open MvPolynomial

def sourceSystemFileSHA256 : String := "6ffc10dda401eb3ce05ff82b22213e0cd975ebbb5745b32cf2d8398a96e5a125"
def sourceSystemSemanticSHA256 : String := "4a8bc72c016044a9aebf44d5cffa6be0f567c854e7bc0d6a3069324d4fd55ecd"
def certificateSHA256 : String := "ca2bc40343d9f4239a38c6f7fb1e9f0c11b8bae3abf9b9e339d8a663e4335e1a"
def sourceEquationCount : Nat := 678

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedIndices : Fin 16 → Fin 678 := ![
  18,
  55,
  56,
  307,
  309,
  413,
  424,
  425,
  440,
  442,
  444,
  538,
  674,
  675,
  676,
  677
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 16 → SparsePoly (Fin 73) := ![
  [{ coefficient := 1, powers := [(25, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(51, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(51, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (55, 1)] }, { coefficient := 1, powers := [(55, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(60, 1), (61, 1)] }, { coefficient := 1, powers := [(61, 1)] }],
  [{ coefficient := 1, powers := [(34, 1), (42, 1), (52, 1)] }, { coefficient := 1, powers := [(52, 1)] }],
  [{ coefficient := 1, powers := [(37, 1), (66, 1)] }, { coefficient := 1, powers := [(40, 1), (60, 1)] }, { coefficient := 1, powers := [(51, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(37, 1), (69, 1)] }, { coefficient := 1, powers := [(43, 1), (60, 1)] }, { coefficient := 1, powers := [(51, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (52, 1), (69, 1)] }, { coefficient := 1, powers := [(31, 1), (51, 1), (52, 1)] }, { coefficient := 1, powers := [(34, 1), (43, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (55, 1), (66, 1)] }, { coefficient := 1, powers := [(23, 1), (51, 1), (55, 1)] }, { coefficient := 1, powers := [(34, 1), (40, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (60, 1), (61, 1)] }, { coefficient := 1, powers := [(15, 1), (51, 1), (61, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (42, 1), (60, 1)] }, { coefficient := 1, powers := [(25, 1), (54, 1)] }, { coefficient := 1, powers := [(42, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (54, 1), (69, 1)] }, { coefficient := 1, powers := [(7, 1), (57, 1), (66, 1)] }, { coefficient := 1, powers := [(7, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(15, 1), (40, 1), (69, 1)] }, { coefficient := 1, powers := [(15, 1), (43, 1), (66, 1)] }, { coefficient := 1, powers := [(15, 1), (51, 1), (63, 1)] }, { coefficient := 1, powers := [(23, 1), (37, 1), (69, 1)] }, { coefficient := 1, powers := [(23, 1), (43, 1), (60, 1)] }, { coefficient := 1, powers := [(23, 1), (51, 1), (57, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1), (66, 1)] }, { coefficient := 1, powers := [(31, 1), (40, 1), (60, 1)] }, { coefficient := 1, powers := [(31, 1), (51, 1), (54, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1), (63, 1)] }, { coefficient := 1, powers := [(34, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(34, 1), (43, 1), (54, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(52, 1), (70, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(55, 1), (71, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(61, 1), (72, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 16 → SparsePoly (Fin 73) := ![
  [{ coefficient := -1, powers := [(7, 1), (15, 1), (54, 1), (69, 1), (70, 1)] }],
  [{ coefficient := -1, powers := [(15, 1), (54, 1), (69, 1), (70, 1)] }, { coefficient := 1, powers := [(15, 1), (57, 1), (66, 1), (70, 1)] }, { coefficient := -1, powers := [(15, 1), (61, 1), (63, 1), (70, 1), (72, 1)] }, { coefficient := 1, powers := [(15, 1), (63, 1), (70, 1)] }, { coefficient := -1, powers := [(31, 1), (54, 1), (70, 1)] }],
  [{ coefficient := 2, powers := [(15, 1), (23, 1), (42, 1), (69, 1), (71, 1)] }, { coefficient := -1, powers := [(23, 1), (57, 1), (71, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (15, 1), (42, 1), (69, 1), (71, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (15, 1), (18, 1), (42, 1), (69, 1), (72, 1)] }, { coefficient := -1, powers := [(15, 1), (40, 1), (69, 1), (72, 1)] }, { coefficient := 1, powers := [(15, 1), (43, 1), (66, 1), (72, 1)] }],
  [{ coefficient := 2, powers := [(15, 1), (40, 1), (69, 1), (70, 1)] }],
  [{ coefficient := 1, powers := [(15, 1), (69, 1)] }, { coefficient := 1, powers := [(31, 1)] }],
  [{ coefficient := -1, powers := [(15, 1), (66, 1)] }, { coefficient := 1, powers := [(23, 1)] }],
  [{ coefficient := 1, powers := [(54, 1), (70, 1)] }],
  [{ coefficient := -2, powers := [(15, 1), (42, 1), (69, 1), (71, 1)] }, { coefficient := 1, powers := [(57, 1), (71, 1)] }],
  [{ coefficient := 1, powers := [(63, 1), (72, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (15, 1), (69, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(7, 1), (15, 1), (25, 1), (54, 1), (69, 1)] }, { coefficient := -1, powers := [(7, 1), (54, 1), (69, 1)] }, { coefficient := -2, powers := [(15, 1), (34, 1), (40, 1), (42, 1), (69, 1)] }, { coefficient := -2, powers := [(15, 1), (40, 1), (69, 1)] }, { coefficient := 1, powers := [(15, 1), (51, 1), (54, 1), (69, 1)] }, { coefficient := -1, powers := [(15, 1), (51, 1), (57, 1), (66, 1)] }, { coefficient := 1, powers := [(15, 1), (51, 1), (61, 1), (63, 1), (72, 1)] }, { coefficient := -1, powers := [(15, 1), (51, 1), (63, 1)] }, { coefficient := -1, powers := [(34, 1), (43, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (15, 1), (18, 1), (42, 1), (69, 1)] }, { coefficient := 1, powers := [(7, 1), (15, 1), (42, 1), (66, 1), (69, 1)] }, { coefficient := -1, powers := [(7, 1), (57, 1), (66, 1)] }, { coefficient := 2, powers := [(15, 1), (34, 1), (40, 1), (42, 1), (69, 1)] }, { coefficient := -1, powers := [(34, 1), (40, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (15, 1), (18, 1), (42, 1), (60, 1), (69, 1)] }, { coefficient := 1, powers := [(7, 1), (15, 1), (18, 1), (42, 1), (69, 1)] }, { coefficient := -1, powers := [(7, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(15, 1), (40, 1), (60, 1), (69, 1)] }, { coefficient := 1, powers := [(15, 1), (40, 1), (69, 1)] }, { coefficient := -1, powers := [(15, 1), (43, 1), (60, 1), (66, 1)] }, { coefficient := -1, powers := [(15, 1), (43, 1), (66, 1)] }, { coefficient := -1, powers := [(34, 1), (37, 1), (63, 1)] }]
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
    ¬ ∀ index : Fin 16,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.X5ResidualCase429.LeafB7.selectedHasNoCommonZero

end Krenn.X5ResidualCase429.LeafB7
