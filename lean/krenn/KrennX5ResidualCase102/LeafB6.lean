import KrennSparseCertificate

/-! Selected core of a strict exact certificate over a frozen system. -/

namespace Krenn.X5ResidualCase102.LeafB6

open Krenn.SparseCertificate
open MvPolynomial

def sourceSystemFileSHA256 : String := "8dfa5eaa3ce141460c62cb2a3e48c0de811636aaf826f9ca6cadca4f9939d5f4"
def sourceSystemSemanticSHA256 : String := "1f03d110543676b0ede25c8daf75902b378842b45320dd8e1553450fc2970555"
def certificateSHA256 : String := "54e000dd031848da10426912cbd5d23001153675c54277f63f6f1a8cb5401117"
def sourceEquationCount : Nat := 678

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedIndices : Fin 18 → Fin 678 := ![
  13,
  17,
  27,
  28,
  29,
  54,
  407,
  412,
  416,
  424,
  425,
  427,
  440,
  601,
  633,
  660,
  674,
  675
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 18 → SparsePoly (Fin 72) := ![
  [{ coefficient := 1, powers := [(21, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(26, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(37, 1), (68, 1)] }],
  [{ coefficient := 1, powers := [(38, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(38, 1), (69, 1)] }],
  [{ coefficient := 1, powers := [(51, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(26, 1), (48, 1), (52, 1)] }, { coefficient := 1, powers := [(52, 1), (69, 1)] }],
  [{ coefficient := 1, powers := [(33, 1), (38, 1), (57, 1)] }, { coefficient := 1, powers := [(57, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (63, 1)] }, { coefficient := 1, powers := [(18, 1), (57, 1)] }, { coefficient := 1, powers := [(26, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(37, 1), (66, 1)] }, { coefficient := 1, powers := [(40, 1), (60, 1)] }, { coefficient := 1, powers := [(51, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(37, 1), (69, 1)] }, { coefficient := 1, powers := [(43, 1), (60, 1)] }, { coefficient := 1, powers := [(51, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(40, 1), (69, 1)] }, { coefficient := 1, powers := [(43, 1), (66, 1)] }, { coefficient := 1, powers := [(51, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (52, 1), (69, 1)] }, { coefficient := 1, powers := [(31, 1), (51, 1), (52, 1)] }, { coefficient := 1, powers := [(34, 1), (43, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (52, 1), (68, 1)] }, { coefficient := 1, powers := [(13, 1), (38, 1), (68, 1)] }, { coefficient := 1, powers := [(21, 1), (35, 1), (68, 1)] }, { coefficient := 1, powers := [(52, 1)] }],
  [{ coefficient := 1, powers := [(15, 1), (38, 1), (69, 1)] }, { coefficient := 1, powers := [(21, 1), (45, 1), (57, 1)] }, { coefficient := 1, powers := [(31, 1), (38, 1), (60, 1)] }, { coefficient := 1, powers := [(34, 1), (38, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (48, 1), (63, 1)] }, { coefficient := 1, powers := [(18, 1), (48, 1), (57, 1)] }, { coefficient := 1, powers := [(26, 1), (48, 1), (54, 1)] }, { coefficient := 1, powers := [(54, 1), (69, 1)] }, { coefficient := 1, powers := [(57, 1), (66, 1)] }, { coefficient := 1, powers := [(60, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (54, 1), (69, 1)] }, { coefficient := 1, powers := [(7, 1), (57, 1), (66, 1)] }, { coefficient := 1, powers := [(7, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(15, 1), (40, 1), (69, 1)] }, { coefficient := 1, powers := [(15, 1), (43, 1), (66, 1)] }, { coefficient := 1, powers := [(15, 1), (51, 1), (63, 1)] }, { coefficient := 1, powers := [(23, 1), (37, 1), (69, 1)] }, { coefficient := 1, powers := [(23, 1), (43, 1), (60, 1)] }, { coefficient := 1, powers := [(23, 1), (51, 1), (57, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1), (66, 1)] }, { coefficient := 1, powers := [(31, 1), (40, 1), (60, 1)] }, { coefficient := 1, powers := [(31, 1), (51, 1), (54, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1), (63, 1)] }, { coefficient := 1, powers := [(34, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(34, 1), (43, 1), (54, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(52, 1), (70, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 18 → SparsePoly (Fin 72) := ![
  [{ coefficient := 1, powers := [(33, 1), (40, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (48, 1), (54, 1), (70, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (34, 1), (52, 1), (63, 1), (70, 1)] }, { coefficient := -1, powers := [(13, 1), (34, 1), (38, 1), (63, 1), (70, 1)] }, { coefficient := -1, powers := [(21, 1), (34, 1), (35, 1), (63, 1), (70, 1)] }],
  [{ coefficient := 1, powers := [(31, 1), (33, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(15, 1), (33, 1), (40, 1)] }],
  [{ coefficient := -1, powers := [(31, 1), (54, 1), (70, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (54, 1), (70, 1)] }],
  [{ coefficient := 1, powers := [(34, 1), (40, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(31, 1)] }],
  [{ coefficient := 1, powers := [(23, 1)] }],
  [{ coefficient := 1, powers := [(15, 1)] }],
  [{ coefficient := 1, powers := [(54, 1), (70, 1)] }],
  [{ coefficient := 1, powers := [(34, 1), (37, 1), (63, 1), (70, 1)] }],
  [{ coefficient := -1, powers := [(33, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(7, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(34, 1), (37, 1), (63, 1)] }, { coefficient := -1, powers := [(34, 1), (43, 1), (54, 1)] }]
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
    (values : Fin 72 → R) :
    ¬ ∀ index : Fin 18,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.X5ResidualCase102.LeafB6.selectedHasNoCommonZero

end Krenn.X5ResidualCase102.LeafB6
