import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component18.SelectedLeafB7_6_0

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "8491da188a8f9813e5c9559665f1ffd1ad07978a1cec7f52dfe9fe3bd3ca8562"
def certificateSHA256 : String := "b7d8342b29e72e017b9f6e6cdc35ef20e626125ce0b5037ff4c1b04c8eeb21f9"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 17 → Fin 667 := ![
  10,
  15,
  19,
  143,
  246,
  301,
  318,
  437,
  443,
  584,
  657,
  658,
  659,
  660,
  663,
  665,
  666
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 17 → SparsePoly (Fin 66) := ![
  [{ coefficient := 1, powers := [(13, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(15, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (54, 1)] }, { coefficient := 1, powers := [(15, 1), (21, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (19, 1), (56, 1)] }, { coefficient := 1, powers := [(13, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (60, 1)] }, { coefficient := 1, powers := [(13, 1), (49, 1)] }, { coefficient := 1, powers := [(18, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (54, 1)] }, { coefficient := 1, powers := [(31, 1), (43, 1)] }, { coefficient := 1, powers := [(34, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1)] }, { coefficient := 1, powers := [(13, 1), (31, 1)] }, { coefficient := 1, powers := [(17, 1), (23, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (60, 1)] }, { coefficient := 1, powers := [(13, 1), (26, 1), (47, 1)] }, { coefficient := 1, powers := [(13, 1), (57, 1)] }, { coefficient := 1, powers := [(18, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (40, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (43, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (49, 1), (54, 1)] }, { coefficient := 1, powers := [(20, 1), (45, 1), (54, 1)] }, { coefficient := 1, powers := [(26, 1), (43, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (40, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (43, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (49, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (37, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (49, 1)] }, { coefficient := 1, powers := [(8, 1), (37, 1), (43, 1)] }, { coefficient := 1, powers := [(13, 1), (24, 1), (57, 1)] }, { coefficient := 1, powers := [(13, 1), (31, 1), (49, 1)] }, { coefficient := 1, powers := [(13, 1), (37, 1), (40, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (54, 1)] }, { coefficient := 1, powers := [(18, 1), (31, 1), (43, 1)] }, { coefficient := 1, powers := [(18, 1), (34, 1), (40, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (61, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(43, 1)] }],
  [{ coefficient := 1, powers := [(56, 1)] }],
  [{ coefficient := 1, powers := [(57, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 17 → SparsePoly (Fin 66) := ![
  [{ coefficient := -1, powers := [(2, 1), (24, 1), (26, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (5, 1), (21, 1), (37, 1), (62, 1), (63, 1)] }, { coefficient := 1, powers := [(2, 1), (18, 1), (21, 1), (24, 1), (62, 1), (63, 1)] }, { coefficient := 1, powers := [(2, 1), (20, 1), (21, 1), (45, 1), (61, 1), (62, 1)] }, { coefficient := 1, powers := [(2, 1), (21, 1), (49, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (17, 1), (49, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (5, 1), (37, 1), (62, 1), (63, 1)] }, { coefficient := -1, powers := [(2, 1), (18, 1), (24, 1), (62, 1), (63, 1)] }, { coefficient := -1, powers := [(2, 1), (20, 1), (45, 1), (61, 1), (62, 1)] }, { coefficient := -1, powers := [(2, 1), (49, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (31, 1), (49, 1), (63, 1)] }, { coefficient := 1, powers := [(2, 1), (37, 1), (40, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (31, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (18, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (49, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (24, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (40, 1), (60, 1)] }, { coefficient := -1, powers := [(2, 1), (49, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (5, 1), (37, 1), (54, 1), (63, 1)] }, { coefficient := 1, powers := [(2, 1), (18, 1), (24, 1), (54, 1), (63, 1)] }, { coefficient := 1, powers := [(2, 1), (20, 1), (45, 1), (54, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (49, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (40, 1), (60, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (8, 1), (37, 1), (63, 1)] }, { coefficient := -1, powers := [(2, 1), (18, 1), (31, 1), (63, 1)] }, { coefficient := -1, powers := [(2, 1), (26, 1), (45, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (13, 1), (19, 1), (31, 1), (49, 1), (63, 1)] }, { coefficient := -1, powers := [(2, 1), (13, 1), (19, 1), (37, 1), (40, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (2, 1), (43, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 2), (43, 1), (63, 1)] }, { coefficient := 1, powers := [(2, 1), (5, 1), (34, 1), (63, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
/-- Lean replays the exact selected-row integer certificate. -/
theorem constantIdentity :
    ∑ index, (multipliers index).toPoly *
      (selectedEquations index).toPoly = C (1 : ℤ) := by
  simp (config := { maxSteps := 1000000 })
    [Fin.sum_univ_succ, multipliers, selectedEquations,
    SparsePoly.toPoly, SparseTerm.toPoly]
  ring

/-- The selected rows have no common zero in a characteristic-zero ring. -/
theorem selectedHasNoCommonZero {R : Type*} [CommRing R] [Nontrivial R] [CharZero R]
    (values : Fin 66 → R) :
    ¬ ∀ index : Fin 17,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component18.SelectedLeafB7_6_0.selectedHasNoCommonZero

end Krenn.Component18.SelectedLeafB7_6_0
