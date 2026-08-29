import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component39.SelectedLeafB5_1_6

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "8678feaccb23a51a67141cc4689e6c8fcd50d38eb6bec7d4bc0e485b9e39915e"
def certificateSHA256 : String := "beb0b821a6bd4a5db7f5c0aa4c8703e574a575aa7e725189ece2228a4952b89d"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 23 → Fin 670 := ![
  187,
  250,
  302,
  317,
  321,
  345,
  384,
  396,
  411,
  416,
  422,
  439,
  441,
  465,
  467,
  497,
  580,
  644,
  649,
  663,
  665,
  666,
  668
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 23 → SparsePoly (Fin 66) := ![
  [{ coefficient := 1, powers := [(16, 1), (18, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (23, 1), (44, 1)] }, { coefficient := 1, powers := [(16, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (49, 1)] }, { coefficient := 1, powers := [(18, 1), (49, 1)] }, { coefficient := 1, powers := [(23, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (51, 1)] }, { coefficient := 1, powers := [(22, 1), (56, 1)] }, { coefficient := 1, powers := [(27, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1), (49, 1)] }, { coefficient := 1, powers := [(23, 1), (44, 1), (49, 1)] }, { coefficient := 1, powers := [(49, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (44, 1), (49, 1)] }, { coefficient := 1, powers := [(12, 1), (26, 1), (44, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (23, 1), (46, 1)] }, { coefficient := 1, powers := [(16, 1), (19, 1), (49, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (23, 1), (39, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1), (44, 1)] }, { coefficient := 1, powers := [(16, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1)] }, { coefficient := 1, powers := [(6, 1), (19, 1), (59, 1)] }, { coefficient := 1, powers := [(19, 1)] }, { coefficient := 1, powers := [(23, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (44, 1)] }, { coefficient := 1, powers := [(16, 1), (26, 1), (39, 1)] }, { coefficient := 1, powers := [(16, 1), (26, 1), (44, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (51, 1)] }, { coefficient := 1, powers := [(16, 1), (21, 1), (51, 1)] }, { coefficient := 1, powers := [(16, 1), (21, 1), (56, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (39, 1)] }, { coefficient := 1, powers := [(16, 1), (44, 1)] }, { coefficient := 1, powers := [(16, 1), (51, 1)] }, { coefficient := 1, powers := [(16, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (39, 1)] }, { coefficient := 1, powers := [(27, 1), (44, 1)] }, { coefficient := 1, powers := [(27, 1), (51, 1)] }, { coefficient := 1, powers := [(27, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1), (49, 1)] }, { coefficient := 1, powers := [(19, 1), (49, 1)] }, { coefficient := 1, powers := [(23, 1), (40, 1)] }, { coefficient := 1, powers := [(23, 1), (46, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1), (51, 1)] }, { coefficient := 1, powers := [(19, 1), (51, 1)] }, { coefficient := 1, powers := [(19, 1), (56, 1)] }, { coefficient := 1, powers := [(46, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (46, 1), (49, 1)] }, { coefficient := 1, powers := [(12, 1), (26, 1), (46, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1), (49, 1)] }, { coefficient := 1, powers := [(16, 1), (26, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1)] }, { coefficient := 1, powers := [(6, 1), (59, 1)] }, { coefficient := 1, powers := [(23, 1), (39, 1)] }, { coefficient := 1, powers := [(23, 1), (44, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (36, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (44, 1), (51, 1)] }, { coefficient := 1, powers := [(39, 1)] }, { coefficient := 1, powers := [(44, 1)] }, { coefficient := 1, powers := [(51, 1)] }, { coefficient := 1, powers := [(56, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (36, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (44, 1), (51, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1), (39, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1), (44, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1), (51, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(39, 1)] }],
  [{ coefficient := 1, powers := [(40, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(56, 1), (65, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 23 → SparsePoly (Fin 66) := ![
  [{ coefficient := -1, powers := [(21, 1), (44, 1), (51, 1), (62, 1), (65, 1)] }, { coefficient := -1, powers := [(21, 1), (44, 1), (56, 1), (62, 1), (65, 1)] }, { coefficient := 1, powers := [(26, 1), (44, 1), (51, 1), (62, 1), (65, 1)] }, { coefficient := -1, powers := [(26, 1), (46, 1), (49, 1), (51, 2), (62, 1), (63, 1), (65, 1)] }, { coefficient := -1, powers := [(27, 1), (46, 1), (49, 1), (51, 1), (62, 1), (63, 1), (65, 1)] }, { coefficient := 2, powers := [(27, 1), (51, 1), (62, 1), (65, 1)] }, { coefficient := 1, powers := [(27, 1), (56, 1), (62, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(26, 1), (46, 1), (51, 1), (62, 1), (63, 1), (65, 1)] }, { coefficient := 1, powers := [(27, 1), (46, 1), (62, 1), (63, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (26, 1), (46, 1), (51, 2), (62, 1), (63, 1), (65, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1), (46, 1), (51, 1), (62, 1), (63, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (49, 1), (62, 1), (63, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (19, 1), (27, 1), (51, 1), (62, 1), (63, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(46, 1), (62, 1), (63, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(26, 1), (44, 1), (51, 1), (62, 1), (63, 1), (65, 1)] }, { coefficient := -1, powers := [(27, 1), (44, 1), (62, 1), (63, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (51, 1), (62, 1), (65, 1)] }, { coefficient := 1, powers := [(21, 1), (56, 1), (62, 1), (65, 1)] }, { coefficient := 1, powers := [(26, 1), (40, 1), (51, 1), (62, 1), (63, 1), (65, 1)] }, { coefficient := -1, powers := [(26, 1), (51, 1), (62, 1), (65, 1)] }, { coefficient := 1, powers := [(27, 1), (40, 1), (62, 1), (63, 1), (65, 1)] }, { coefficient := 1, powers := [(27, 1), (62, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (27, 1), (49, 1), (51, 1), (62, 1), (63, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(18, 1), (51, 1), (62, 1), (65, 1)] }, { coefficient := -1, powers := [(40, 1), (62, 1), (63, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(18, 1), (51, 1), (62, 1), (65, 1)] }, { coefficient := -1, powers := [(18, 1), (56, 1), (62, 1), (65, 1)] }, { coefficient := -1, powers := [(62, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (21, 1), (51, 1), (62, 1), (65, 1)] }, { coefficient := 1, powers := [(18, 1), (21, 1), (56, 1), (62, 1), (65, 1)] }, { coefficient := 1, powers := [(19, 1), (26, 1), (49, 1), (51, 1), (62, 1), (63, 1), (65, 1)] }, { coefficient := 1, powers := [(19, 1), (27, 1), (49, 1), (62, 1), (63, 1), (65, 1)] }, { coefficient := -1, powers := [(22, 1), (49, 1), (62, 1), (63, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (16, 1), (18, 1), (51, 1), (62, 1), (65, 1)] }, { coefficient := 1, powers := [(0, 1), (16, 1), (62, 1), (65, 1)] }, { coefficient := -1, powers := [(16, 1), (23, 1), (62, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(16, 1), (27, 1), (51, 1), (62, 1), (63, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(16, 1), (26, 1), (49, 1), (51, 1), (62, 1), (63, 1), (65, 1)] }, { coefficient := -1, powers := [(16, 1), (27, 1), (49, 1), (62, 1), (63, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(44, 1), (62, 1), (63, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(16, 1), (19, 1), (27, 1), (49, 1), (51, 1), (62, 1), (63, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (18, 1), (51, 1), (62, 1), (65, 1)] }, { coefficient := 1, powers := [(65, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (18, 1), (51, 1), (62, 1), (65, 1)] }, { coefficient := -1, powers := [(0, 1), (62, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (36, 1), (59, 1), (65, 1)] }, { coefficient := 1, powers := [(0, 1), (44, 1), (51, 1), (65, 1)] }, { coefficient := 1, powers := [(44, 1), (65, 1)] }, { coefficient := 1, powers := [(51, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (2, 1), (56, 1), (62, 1), (65, 1)] }, { coefficient := -1, powers := [(0, 1), (56, 1), (65, 1)] }, { coefficient := -1, powers := [(2, 1), (18, 1), (51, 1), (62, 1), (65, 1)] }, { coefficient := -1, powers := [(16, 1), (18, 1), (21, 1), (51, 1), (62, 1), (65, 1)] }, { coefficient := -1, powers := [(16, 1), (18, 1), (21, 1), (56, 1), (62, 1), (65, 1)] }, { coefficient := 1, powers := [(16, 1), (18, 1), (26, 1), (51, 1), (62, 1), (65, 1)] }, { coefficient := 1, powers := [(16, 1), (19, 1), (23, 1), (27, 1), (49, 1), (51, 1), (62, 1), (63, 1), (65, 1)] }, { coefficient := -1, powers := [(16, 1), (19, 1), (26, 1), (49, 1), (51, 1), (62, 1), (63, 1), (65, 1)] }, { coefficient := -1, powers := [(16, 1), (19, 1), (27, 1), (49, 1), (62, 1), (63, 1), (65, 1)] }, { coefficient := -1, powers := [(16, 1), (21, 1), (23, 1), (51, 1), (62, 1), (65, 1)] }, { coefficient := -1, powers := [(16, 1), (21, 1), (23, 1), (56, 1), (62, 1), (65, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1), (49, 1), (62, 1), (63, 1), (65, 1)] }, { coefficient := -1, powers := [(16, 1), (23, 1), (26, 1), (40, 1), (51, 1), (62, 1), (63, 1), (65, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1), (26, 1), (51, 1), (62, 1), (65, 1)] }, { coefficient := -1, powers := [(16, 1), (23, 1), (27, 1), (40, 1), (62, 1), (63, 1), (65, 1)] }, { coefficient := 1, powers := [(16, 1), (26, 1), (40, 1), (62, 1), (63, 1), (65, 1)] }, { coefficient := -1, powers := [(65, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (44, 1), (62, 1), (65, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1), (27, 1), (51, 1), (62, 1), (65, 1)] }, { coefficient := -1, powers := [(16, 1), (26, 1), (51, 1), (62, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [] }]
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
    ¬ ∀ index : Fin 23,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component39.SelectedLeafB5_1_6.selectedHasNoCommonZero

end Krenn.Component39.SelectedLeafB5_1_6
