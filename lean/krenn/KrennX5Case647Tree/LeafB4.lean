import KrennSparseCertificate

/-! Selected core of a strict exact certificate over a frozen system. -/

namespace Krenn.X5Case647Tree.LeafB4

open Krenn.SparseCertificate
open MvPolynomial

def sourceSystemFileSHA256 : String := "11a14655f9d025ebdba7818f3bd1b2a3fd6fd70491d4c36f2189ca3cc517de27"
def sourceSystemSemanticSHA256 : String := "8d6cb431caf623dcd9f860348e01f3a3c9927382d15e744a75fcd5de77232139"
def certificateSHA256 : String := "134fe405c7b04c982dab8e2ec1a3b9418c647bb71ca1f367e4b84fa1f6d4a552"
def sourceEquationCount : Nat := 678

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedIndices : Fin 12 → Fin 678 := ![
  0,
  1,
  31,
  35,
  418,
  423,
  424,
  426,
  614,
  616,
  674,
  677
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 12 → SparsePoly (Fin 71) := ![
  [{ coefficient := 1, powers := [(62, 1)] }],
  [{ coefficient := 1, powers := [(63, 1)] }],
  [{ coefficient := 1, powers := [(40, 1), (68, 1)] }],
  [{ coefficient := 1, powers := [(43, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(15, 1), (62, 1)] }, { coefficient := 1, powers := [(37, 1), (65, 1)] }, { coefficient := 1, powers := [(37, 1), (68, 1)] }],
  [{ coefficient := 1, powers := [(37, 1), (66, 1)] }, { coefficient := 1, powers := [(40, 1), (60, 1)] }, { coefficient := 1, powers := [(51, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(37, 1), (69, 1)] }, { coefficient := 1, powers := [(43, 1), (60, 1)] }, { coefficient := 1, powers := [(51, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(40, 1), (69, 1)] }, { coefficient := 1, powers := [(43, 1), (66, 1)] }, { coefficient := 1, powers := [(51, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (54, 1), (68, 1)] }, { coefficient := 1, powers := [(15, 1), (40, 1), (68, 1)] }, { coefficient := 1, powers := [(23, 1), (37, 1), (68, 1)] }, { coefficient := 1, powers := [(54, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (57, 1), (65, 1)] }, { coefficient := 1, powers := [(15, 1), (43, 1), (65, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1), (65, 1)] }, { coefficient := 1, powers := [(57, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (54, 1), (69, 1)] }, { coefficient := 1, powers := [(7, 1), (57, 1), (66, 1)] }, { coefficient := 1, powers := [(7, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(15, 1), (40, 1), (69, 1)] }, { coefficient := 1, powers := [(15, 1), (43, 1), (66, 1)] }, { coefficient := 1, powers := [(15, 1), (51, 1), (63, 1)] }, { coefficient := 1, powers := [(23, 1), (37, 1), (69, 1)] }, { coefficient := 1, powers := [(23, 1), (43, 1), (60, 1)] }, { coefficient := 1, powers := [(23, 1), (51, 1), (57, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1), (66, 1)] }, { coefficient := 1, powers := [(31, 1), (40, 1), (60, 1)] }, { coefficient := 1, powers := [(31, 1), (51, 1), (54, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1), (63, 1)] }, { coefficient := 1, powers := [(34, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(34, 1), (43, 1), (54, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(7, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 12 → SparsePoly (Fin 71) := ![
  [{ coefficient := 1, powers := [(15, 1), (23, 1), (34, 1), (43, 1)] }, { coefficient := 1, powers := [(15, 1), (31, 1), (34, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (60, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1)] }],
  [{ coefficient := -1, powers := [(15, 1), (34, 1), (43, 1)] }, { coefficient := 1, powers := [(31, 1), (34, 1), (37, 1)] }],
  [{ coefficient := -1, powers := [(15, 1), (34, 1), (40, 1)] }, { coefficient := 1, powers := [(23, 1), (34, 1), (37, 1)] }],
  [{ coefficient := -1, powers := [(23, 1), (34, 1), (43, 1)] }, { coefficient := -1, powers := [(31, 1), (34, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(31, 1)] }],
  [{ coefficient := 1, powers := [(23, 1)] }],
  [{ coefficient := 1, powers := [(15, 1)] }],
  [{ coefficient := 1, powers := [(34, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(34, 1), (40, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(34, 1), (40, 1), (57, 1), (65, 1)] }, { coefficient := -1, powers := [(34, 1), (43, 1), (54, 1), (68, 1)] }, { coefficient := 1, powers := [(54, 1), (69, 1)] }, { coefficient := 1, powers := [(57, 1), (66, 1)] }]
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
    ¬ ∀ index : Fin 12,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.X5Case647Tree.LeafB4.selectedHasNoCommonZero

end Krenn.X5Case647Tree.LeafB4
