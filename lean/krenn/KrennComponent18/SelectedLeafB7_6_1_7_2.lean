import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component18.SelectedLeafB7_6_1_7_2

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "db8810f4ab2fd46b1ce8ef313d9b67b1b9f2688c1e4b122844fbc05e6521d56f"
def certificateSHA256 : String := "6e102920ab98cc786052e06d7824268c20a8bf642c0cfe097ad78d71188347be"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 18 → Fin 673 := ![
  7,
  19,
  150,
  165,
  299,
  301,
  318,
  349,
  437,
  496,
  581,
  657,
  659,
  663,
  665,
  667,
  669,
  672
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 18 → SparsePoly (Fin 71) := ![
  [{ coefficient := 1, powers := [(13, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (29, 1)] }, { coefficient := 1, powers := [(15, 1), (23, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (29, 1)] }, { coefficient := -1, powers := [(23, 1), (27, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (53, 1)] }, { coefficient := 1, powers := [(11, 1), (27, 1), (53, 1)] }, { coefficient := 1, powers := [(15, 1), (21, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (60, 1)] }, { coefficient := 1, powers := [(13, 1), (49, 1)] }, { coefficient := 1, powers := [(18, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (54, 1)] }, { coefficient := 1, powers := [(31, 1), (43, 1)] }, { coefficient := 1, powers := [(34, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (31, 1), (59, 1)] }, { coefficient := 1, powers := [(23, 1), (53, 1)] }, { coefficient := 1, powers := [(31, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1)] }, { coefficient := 1, powers := [(13, 1), (31, 1)] }, { coefficient := 1, powers := [(17, 1), (23, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (31, 1), (60, 1)] }, { coefficient := 1, powers := [(3, 1), (34, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (37, 1), (54, 1)] }, { coefficient := 1, powers := [(23, 1), (45, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (52, 1)] }, { coefficient := 1, powers := [(3, 1), (59, 1)] }, { coefficient := 1, powers := [(19, 1), (52, 1)] }, { coefficient := 1, powers := [(19, 1), (56, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (40, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (43, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (49, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (37, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (49, 1)] }, { coefficient := 1, powers := [(8, 1), (37, 1), (43, 1)] }, { coefficient := 1, powers := [(13, 1), (24, 1), (57, 1)] }, { coefficient := 1, powers := [(13, 1), (31, 1), (49, 1)] }, { coefficient := 1, powers := [(13, 1), (37, 1), (40, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (54, 1)] }, { coefficient := 1, powers := [(18, 1), (31, 1), (43, 1)] }, { coefficient := 1, powers := [(18, 1), (34, 1), (40, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(43, 1)] }],
  [{ coefficient := 1, powers := [(56, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (67, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(31, 1), (69, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(60, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 18 → SparsePoly (Fin 71) := ![
  [{ coefficient := -1, powers := [(3, 1), (24, 1), (57, 1), (59, 1), (67, 1)] }, { coefficient := 1, powers := [(3, 1), (31, 1), (49, 1), (59, 1), (67, 1)] }, { coefficient := -1, powers := [(3, 1), (37, 1), (40, 1), (59, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (17, 1), (49, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (45, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (53, 1), (62, 1), (69, 1)] }],
  [{ coefficient := -1, powers := [(11, 1), (53, 1), (62, 1), (69, 1)] }],
  [{ coefficient := -1, powers := [(23, 1), (62, 1), (69, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (31, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (18, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(69, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (49, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(31, 1), (69, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(3, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (53, 1), (69, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (3, 1), (57, 1), (59, 1)] }, { coefficient := -1, powers := [(3, 1), (8, 1), (37, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (18, 1), (31, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (31, 1), (69, 1)] }, { coefficient := -1, powers := [(19, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (13, 1), (24, 1), (57, 1), (59, 1)] }, { coefficient := -1, powers := [(3, 1), (13, 1), (31, 1), (49, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (13, 1), (37, 1), (40, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (52, 1)] }, { coefficient := 1, powers := [(19, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (3, 1), (40, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (5, 1), (31, 1), (59, 1)] }, { coefficient := -1, powers := [(3, 1), (8, 1), (24, 1), (59, 1)] }]
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
    (values : Fin 71 → R) :
    ¬ ∀ index : Fin 18,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component18.SelectedLeafB7_6_1_7_2.selectedHasNoCommonZero

end Krenn.Component18.SelectedLeafB7_6_1_7_2
