import KrennSparseCertificate

/-! Selected core of a strict exact certificate over a frozen system. -/

namespace Krenn.X5Case142Selected

open Krenn.SparseCertificate
open MvPolynomial

def sourceSystemFileSHA256 : String := "9e383dbf8cf779f836907a09008429bc1513afaed7c0fa909bd82b7d17624b6b"
def sourceSystemSemanticSHA256 : String := "84ea6062b82feb17691af905ccfd6332764fc6e21ed9107fe9e8047141a0923e"
def certificateSHA256 : String := "cff70bbfd0c8d1ee5f6631307367a382e93705fba4e9b7a72b09f3b41be1c0d3"
def sourceEquationCount : Nat := 675

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedIndices : Fin 8 → Fin 675 := ![
  1,
  4,
  416,
  419,
  424,
  426,
  668,
  674
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 8 → SparsePoly (Fin 70) := ![
  [{ coefficient := 1, powers := [(54, 1)] }],
  [{ coefficient := 1, powers := [(63, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (63, 1)] }, { coefficient := 1, powers := [(29, 1), (54, 1)] }, { coefficient := 1, powers := [(57, 1)] }],
  [{ coefficient := 1, powers := [(15, 1), (63, 1)] }, { coefficient := 1, powers := [(23, 1), (57, 1)] }, { coefficient := 1, powers := [(31, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(37, 1), (66, 1)] }, { coefficient := 1, powers := [(40, 1), (60, 1)] }, { coefficient := 1, powers := [(51, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(40, 1), (69, 1)] }, { coefficient := 1, powers := [(43, 1), (66, 1)] }, { coefficient := 1, powers := [(51, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (54, 1), (69, 1)] }, { coefficient := 1, powers := [(4, 1), (57, 1), (66, 1)] }, { coefficient := 1, powers := [(4, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(12, 1), (40, 1), (69, 1)] }, { coefficient := 1, powers := [(12, 1), (43, 1), (66, 1)] }, { coefficient := 1, powers := [(12, 1), (51, 1), (63, 1)] }, { coefficient := 1, powers := [(29, 1), (37, 1), (66, 1)] }, { coefficient := 1, powers := [(29, 1), (40, 1), (60, 1)] }, { coefficient := 1, powers := [(29, 1), (51, 1), (54, 1)] }, { coefficient := 1, powers := [(37, 1), (69, 1)] }, { coefficient := 1, powers := [(43, 1), (60, 1)] }, { coefficient := 1, powers := [(51, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (54, 1), (69, 1)] }, { coefficient := 1, powers := [(7, 1), (57, 1), (66, 1)] }, { coefficient := 1, powers := [(7, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(15, 1), (40, 1), (69, 1)] }, { coefficient := 1, powers := [(15, 1), (43, 1), (66, 1)] }, { coefficient := 1, powers := [(15, 1), (51, 1), (63, 1)] }, { coefficient := 1, powers := [(23, 1), (37, 1), (69, 1)] }, { coefficient := 1, powers := [(23, 1), (43, 1), (60, 1)] }, { coefficient := 1, powers := [(23, 1), (51, 1), (57, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1), (66, 1)] }, { coefficient := 1, powers := [(31, 1), (40, 1), (60, 1)] }, { coefficient := 1, powers := [(31, 1), (51, 1), (54, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1), (63, 1)] }, { coefficient := 1, powers := [(34, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(34, 1), (43, 1), (54, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 8 → SparsePoly (Fin 70) := ![
  [{ coefficient := 1, powers := [(4, 1), (23, 1), (29, 1), (66, 1)] }, { coefficient := -1, powers := [(4, 1), (23, 1), (69, 1)] }, { coefficient := -1, powers := [(7, 1), (29, 1), (66, 1)] }, { coefficient := 1, powers := [(7, 1), (69, 1)] }, { coefficient := 1, powers := [(23, 1), (29, 1), (51, 1)] }, { coefficient := -1, powers := [(29, 1), (34, 1), (40, 1)] }, { coefficient := -1, powers := [(31, 1), (51, 1)] }, { coefficient := 1, powers := [(34, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (12, 1), (23, 1), (66, 1)] }, { coefficient := -1, powers := [(4, 1), (23, 1), (60, 1)] }, { coefficient := -1, powers := [(7, 1), (12, 1), (66, 1)] }, { coefficient := 1, powers := [(7, 1), (60, 1)] }, { coefficient := 1, powers := [(12, 1), (23, 1), (51, 1)] }, { coefficient := -1, powers := [(12, 1), (34, 1), (40, 1)] }, { coefficient := -1, powers := [(15, 1), (51, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (23, 1), (66, 1)] }, { coefficient := 1, powers := [(7, 1), (66, 1)] }, { coefficient := -1, powers := [(23, 1), (51, 1)] }, { coefficient := 1, powers := [(34, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(51, 1)] }],
  [{ coefficient := -1, powers := [(23, 1), (29, 1)] }, { coefficient := 1, powers := [(31, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (23, 1)] }, { coefficient := 1, powers := [(15, 1)] }],
  [{ coefficient := 1, powers := [(23, 1)] }],
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

#print axioms Krenn.X5Case142Selected.selectedHasNoCommonZero

end Krenn.X5Case142Selected
