import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component18.SelectedLeafB7_6_1_7_7

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "a30a29b6c421a61096f75f189dae13ad0be357b4faddf84f1d6764e217dfb14f"
def certificateSHA256 : String := "cf35919136223a1003c1066d2dd234da8a44dde63c253b329c31724730957e6f"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 15 → Fin 673 := ![
  3,
  7,
  19,
  146,
  187,
  301,
  318,
  342,
  437,
  657,
  663,
  664,
  667,
  670,
  672
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 15 → SparsePoly (Fin 73) := ![
  [{ coefficient := 1, powers := [(8, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (35, 1)] }, { coefficient := 1, powers := [(17, 1), (20, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (35, 1), (51, 1)] }, { coefficient := 1, powers := [(5, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (60, 1)] }, { coefficient := 1, powers := [(13, 1), (49, 1)] }, { coefficient := 1, powers := [(18, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (54, 1)] }, { coefficient := 1, powers := [(31, 1), (43, 1)] }, { coefficient := 1, powers := [(34, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (40, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (58, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1)] }, { coefficient := 1, powers := [(13, 1), (31, 1)] }, { coefficient := 1, powers := [(17, 1), (23, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (40, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (43, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (49, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (37, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (49, 1)] }, { coefficient := 1, powers := [(8, 1), (37, 1), (43, 1)] }, { coefficient := 1, powers := [(13, 1), (24, 1), (57, 1)] }, { coefficient := 1, powers := [(13, 1), (31, 1), (49, 1)] }, { coefficient := 1, powers := [(13, 1), (37, 1), (40, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (54, 1)] }, { coefficient := 1, powers := [(18, 1), (31, 1), (43, 1)] }, { coefficient := 1, powers := [(18, 1), (34, 1), (40, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(43, 1)] }],
  [{ coefficient := 1, powers := [(55, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (67, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(58, 1), (70, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(60, 1), (72, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 15 → SparsePoly (Fin 73) := ![
  [{ coefficient := 1, powers := [(24, 1), (58, 1), (60, 1), (70, 2)] }, { coefficient := -1, powers := [(24, 1), (60, 1), (70, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (57, 1), (58, 1), (67, 1), (70, 1)] }, { coefficient := -1, powers := [(31, 1), (49, 1), (58, 1), (67, 1), (70, 1)] }, { coefficient := -1, powers := [(34, 1), (49, 1), (57, 1), (58, 1), (67, 1), (70, 1), (72, 1)] }, { coefficient := 1, powers := [(37, 1), (40, 1), (58, 1), (67, 1), (70, 1)] }, { coefficient := -1, powers := [(37, 1), (49, 1), (54, 1), (58, 1), (67, 1), (70, 1), (72, 1)] }],
  [{ coefficient := -1, powers := [(17, 1), (49, 1), (58, 1), (70, 1)] }],
  [{ coefficient := 1, powers := [(31, 1), (51, 1), (60, 1), (70, 1)] }],
  [{ coefficient := -1, powers := [(31, 1), (60, 1), (70, 1)] }],
  [{ coefficient := 1, powers := [(31, 1), (58, 1), (70, 1)] }, { coefficient := 1, powers := [(34, 1), (57, 1), (58, 1), (70, 1), (72, 1)] }, { coefficient := 1, powers := [(37, 1), (54, 1), (58, 1), (70, 1), (72, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (58, 1), (70, 1)] }],
  [{ coefficient := 1, powers := [(60, 1), (70, 1)] }],
  [{ coefficient := 1, powers := [(49, 1), (58, 1), (70, 1)] }],
  [{ coefficient := -1, powers := [(58, 1), (70, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (57, 1), (58, 1), (70, 1)] }, { coefficient := 1, powers := [(8, 1), (37, 1), (58, 1), (70, 1)] }, { coefficient := -1, powers := [(18, 1), (31, 1), (58, 1), (70, 1)] }, { coefficient := -1, powers := [(18, 1), (34, 1), (57, 1), (58, 1), (70, 1), (72, 1)] }, { coefficient := -1, powers := [(18, 1), (37, 1), (54, 1), (58, 1), (70, 1), (72, 1)] }],
  [{ coefficient := -1, powers := [(17, 1), (20, 1), (31, 1), (51, 1), (60, 1), (70, 1)] }],
  [{ coefficient := -1, powers := [(13, 1), (24, 1), (57, 1), (58, 1), (70, 1)] }, { coefficient := 1, powers := [(13, 1), (31, 1), (49, 1), (58, 1), (70, 1)] }, { coefficient := 1, powers := [(13, 1), (34, 1), (49, 1), (57, 1), (58, 1), (70, 1), (72, 1)] }, { coefficient := -1, powers := [(13, 1), (37, 1), (40, 1), (58, 1), (70, 1)] }, { coefficient := 1, powers := [(13, 1), (37, 1), (49, 1), (54, 1), (58, 1), (70, 1), (72, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (24, 1), (58, 1), (60, 1), (70, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(5, 1), (34, 1), (57, 1), (58, 1), (70, 1)] }, { coefficient := -1, powers := [(5, 1), (37, 1), (54, 1), (58, 1), (70, 1)] }]
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
    (values : Fin 73 → R) :
    ¬ ∀ index : Fin 15,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component18.SelectedLeafB7_6_1_7_7.selectedHasNoCommonZero

end Krenn.Component18.SelectedLeafB7_6_1_7_7
