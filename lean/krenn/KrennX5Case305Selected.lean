import KrennSparseCertificate

/-! Selected core of a strict exact certificate over a frozen system. -/

namespace Krenn.X5Case305Selected

open Krenn.SparseCertificate
open MvPolynomial

def sourceSystemFileSHA256 : String := "e04bcd3f0bcb9e995a55ce2f4a6a6d5dfe176654547bdbfae8219a40e1bbea37"
def sourceSystemSemanticSHA256 : String := "a13443f6bcd6892f4db85f83e0f70bf5079cd40b10a9a659b1d7a992c18d12b6"
def certificateSHA256 : String := "6e14c31327e6d39ee88ee40812131771522b98bbf21f56fd59a871c99ac96bb5"
def sourceEquationCount : Nat := 675

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedIndices : Fin 8 → Fin 675 := ![
  1,
  3,
  418,
  419,
  422,
  423,
  666,
  674
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 8 → SparsePoly (Fin 70) := ![
  [{ coefficient := 1, powers := [(54, 1)] }],
  [{ coefficient := 1, powers := [(57, 1)] }],
  [{ coefficient := 1, powers := [(15, 1), (63, 1)] }, { coefficient := 1, powers := [(23, 1), (57, 1)] }, { coefficient := 1, powers := [(31, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (57, 1)] }, { coefficient := 1, powers := [(26, 1), (54, 1)] }, { coefficient := 1, powers := [(63, 1)] }],
  [{ coefficient := 1, powers := [(37, 1), (66, 1)] }, { coefficient := 1, powers := [(40, 1), (60, 1)] }, { coefficient := 1, powers := [(51, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(37, 1), (69, 1)] }, { coefficient := 1, powers := [(43, 1), (60, 1)] }, { coefficient := 1, powers := [(51, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (54, 1), (69, 1)] }, { coefficient := 1, powers := [(1, 1), (57, 1), (66, 1)] }, { coefficient := 1, powers := [(1, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(18, 1), (37, 1), (69, 1)] }, { coefficient := 1, powers := [(18, 1), (43, 1), (60, 1)] }, { coefficient := 1, powers := [(18, 1), (51, 1), (57, 1)] }, { coefficient := 1, powers := [(26, 1), (37, 1), (66, 1)] }, { coefficient := 1, powers := [(26, 1), (40, 1), (60, 1)] }, { coefficient := 1, powers := [(26, 1), (51, 1), (54, 1)] }, { coefficient := 1, powers := [(40, 1), (69, 1)] }, { coefficient := 1, powers := [(43, 1), (66, 1)] }, { coefficient := 1, powers := [(51, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (54, 1), (69, 1)] }, { coefficient := 1, powers := [(7, 1), (57, 1), (66, 1)] }, { coefficient := 1, powers := [(7, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(15, 1), (40, 1), (69, 1)] }, { coefficient := 1, powers := [(15, 1), (43, 1), (66, 1)] }, { coefficient := 1, powers := [(15, 1), (51, 1), (63, 1)] }, { coefficient := 1, powers := [(23, 1), (37, 1), (69, 1)] }, { coefficient := 1, powers := [(23, 1), (43, 1), (60, 1)] }, { coefficient := 1, powers := [(23, 1), (51, 1), (57, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1), (66, 1)] }, { coefficient := 1, powers := [(31, 1), (40, 1), (60, 1)] }, { coefficient := 1, powers := [(31, 1), (51, 1), (54, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1), (63, 1)] }, { coefficient := 1, powers := [(34, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(34, 1), (43, 1), (54, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 8 → SparsePoly (Fin 70) := ![
  [{ coefficient := 1, powers := [(1, 1), (15, 1), (26, 1), (60, 1)] }, { coefficient := -1, powers := [(1, 1), (15, 1), (69, 1)] }, { coefficient := -1, powers := [(7, 1), (26, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (69, 1)] }, { coefficient := 1, powers := [(15, 1), (26, 1), (51, 1)] }, { coefficient := -1, powers := [(26, 1), (34, 1), (37, 1)] }, { coefficient := -1, powers := [(31, 1), (51, 1)] }, { coefficient := 1, powers := [(34, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (15, 1), (18, 1), (60, 1)] }, { coefficient := -1, powers := [(1, 1), (15, 1), (66, 1)] }, { coefficient := -1, powers := [(7, 1), (18, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (66, 1)] }, { coefficient := 1, powers := [(15, 1), (18, 1), (51, 1)] }, { coefficient := -1, powers := [(18, 1), (34, 1), (37, 1)] }, { coefficient := -1, powers := [(23, 1), (51, 1)] }, { coefficient := 1, powers := [(34, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(51, 1)] }],
  [{ coefficient := -1, powers := [(1, 1), (15, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (60, 1)] }, { coefficient := -1, powers := [(15, 1), (51, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1)] }],
  [{ coefficient := -1, powers := [(15, 1), (26, 1)] }, { coefficient := 1, powers := [(31, 1)] }],
  [{ coefficient := -1, powers := [(15, 1), (18, 1)] }, { coefficient := 1, powers := [(23, 1)] }],
  [{ coefficient := 1, powers := [(15, 1)] }],
  [{ coefficient := -1, powers := [] }]
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
    ¬ ∀ index : Fin 8,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.X5Case305Selected.selectedHasNoCommonZero

end Krenn.X5Case305Selected
