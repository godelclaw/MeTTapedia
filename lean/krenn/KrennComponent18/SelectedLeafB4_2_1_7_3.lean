import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component18.SelectedLeafB4_2_1_7_3

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "6f572cfaa9dcd5b0e6efc9d30d586b58749afb3410dcb4100477e7e97a493bd9"
def certificateSHA256 : String := "df197f1f0140507c1a8c0f049b813d1d4dc7215a664edc5ed183991f254efa7f"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 13 → Fin 673 := ![
  7,
  19,
  168,
  301,
  318,
  437,
  618,
  657,
  660,
  663,
  667,
  671,
  672
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 13 → SparsePoly (Fin 69) := ![
  [{ coefficient := 1, powers := [(13, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (53, 1)] }, { coefficient := 1, powers := [(31, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (60, 1)] }, { coefficient := 1, powers := [(13, 1), (49, 1)] }, { coefficient := 1, powers := [(18, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (54, 1)] }, { coefficient := 1, powers := [(31, 1), (43, 1)] }, { coefficient := 1, powers := [(34, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1)] }, { coefficient := 1, powers := [(13, 1), (31, 1)] }, { coefficient := 1, powers := [(17, 1), (23, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (40, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (48, 1), (53, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (59, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (59, 1)] }, { coefficient := 1, powers := [(17, 1), (24, 1), (53, 1)] }, { coefficient := 1, powers := [(17, 1), (31, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (40, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (43, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (49, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (37, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (49, 1)] }, { coefficient := 1, powers := [(8, 1), (37, 1), (43, 1)] }, { coefficient := 1, powers := [(13, 1), (24, 1), (57, 1)] }, { coefficient := 1, powers := [(13, 1), (31, 1), (49, 1)] }, { coefficient := 1, powers := [(13, 1), (37, 1), (40, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (54, 1)] }, { coefficient := 1, powers := [(18, 1), (31, 1), (43, 1)] }, { coefficient := 1, powers := [(18, 1), (34, 1), (40, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(43, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (64, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(59, 1), (67, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(60, 1), (68, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 13 → SparsePoly (Fin 69) := ![
  [{ coefficient := 1, powers := [(24, 1), (57, 1), (64, 1)] }, { coefficient := 1, powers := [(31, 1), (49, 1), (59, 1), (60, 1), (64, 1), (67, 1), (68, 1)] }, { coefficient := -1, powers := [(31, 1), (49, 1), (64, 1)] }, { coefficient := -1, powers := [(34, 1), (49, 1), (57, 1), (64, 1), (68, 1)] }, { coefficient := 1, powers := [(37, 1), (40, 1), (64, 1)] }, { coefficient := -1, powers := [(37, 1), (49, 1), (54, 1), (64, 1), (68, 1)] }],
  [{ coefficient := -1, powers := [(17, 1), (49, 1)] }],
  [{ coefficient := -1, powers := [(17, 1), (60, 1), (67, 1)] }],
  [{ coefficient := -1, powers := [(31, 1), (59, 1), (60, 1), (67, 1), (68, 1)] }, { coefficient := 1, powers := [(31, 1)] }, { coefficient := 1, powers := [(34, 1), (57, 1), (68, 1)] }, { coefficient := 1, powers := [(37, 1), (54, 1), (68, 1)] }],
  [{ coefficient := 1, powers := [(18, 1)] }],
  [{ coefficient := 1, powers := [(49, 1)] }],
  [{ coefficient := 1, powers := [(60, 1), (67, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(40, 1), (59, 1), (60, 1), (67, 1)] }, { coefficient := 1, powers := [(40, 1), (60, 1)] }, { coefficient := -1, powers := [(48, 1), (53, 1), (60, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (57, 1)] }, { coefficient := 1, powers := [(8, 1), (37, 1)] }, { coefficient := 1, powers := [(18, 1), (31, 1), (59, 1), (60, 1), (67, 1), (68, 1)] }, { coefficient := -1, powers := [(18, 1), (31, 1)] }, { coefficient := -1, powers := [(18, 1), (34, 1), (57, 1), (68, 1)] }, { coefficient := -1, powers := [(18, 1), (37, 1), (54, 1), (68, 1)] }],
  [{ coefficient := -1, powers := [(13, 1), (24, 1), (57, 1)] }, { coefficient := -1, powers := [(13, 1), (31, 1), (49, 1), (59, 1), (60, 1), (67, 1), (68, 1)] }, { coefficient := 1, powers := [(13, 1), (31, 1), (49, 1)] }, { coefficient := 1, powers := [(13, 1), (34, 1), (49, 1), (57, 1), (68, 1)] }, { coefficient := -1, powers := [(13, 1), (37, 1), (40, 1)] }, { coefficient := 1, powers := [(13, 1), (37, 1), (49, 1), (54, 1), (68, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (24, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (31, 1), (59, 1), (60, 1), (67, 1)] }, { coefficient := -1, powers := [(5, 1), (34, 1), (57, 1)] }, { coefficient := -1, powers := [(5, 1), (37, 1), (54, 1)] }]
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
    (values : Fin 69 → R) :
    ¬ ∀ index : Fin 13,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component18.SelectedLeafB4_2_1_7_3.selectedHasNoCommonZero

end Krenn.Component18.SelectedLeafB4_2_1_7_3
