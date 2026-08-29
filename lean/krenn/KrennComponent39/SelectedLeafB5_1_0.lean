import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component39.SelectedLeafB5_1_0

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "038693f50e6b530c5c0f18872344a869dd6b374f0e63640ae7e82554e98e47b3"
def certificateSHA256 : String := "9a84099dac212b43e9b7ed162c163c3c58ad0ee28106236a15254e21d5c477fc"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 18 → Fin 670 := ![
  187,
  195,
  250,
  313,
  321,
  345,
  382,
  411,
  423,
  467,
  508,
  580,
  608,
  661,
  663,
  665,
  666,
  668
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 18 → SparsePoly (Fin 64) := ![
  [{ coefficient := 1, powers := [(16, 1), (18, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1)] }],
  [{ coefficient := 1, powers := [(26, 1), (52, 1)] }, { coefficient := -1, powers := [(27, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (23, 1), (44, 1)] }, { coefficient := 1, powers := [(16, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (44, 1)] }, { coefficient := 1, powers := [(12, 1), (56, 1)] }, { coefficient := 1, powers := [(16, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1), (49, 1)] }, { coefficient := 1, powers := [(23, 1), (44, 1), (49, 1)] }, { coefficient := 1, powers := [(49, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (44, 1), (49, 1)] }, { coefficient := 1, powers := [(12, 1), (26, 1), (44, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (18, 1), (56, 1)] }, { coefficient := 1, powers := [(12, 1)] }, { coefficient := 1, powers := [(16, 1), (18, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1)] }, { coefficient := 1, powers := [(6, 1), (19, 1), (59, 1)] }, { coefficient := 1, powers := [(19, 1)] }, { coefficient := 1, powers := [(23, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (52, 1)] }, { coefficient := 1, powers := [(12, 1), (21, 1), (56, 1)] }, { coefficient := 1, powers := [(12, 1), (27, 1)] }, { coefficient := 1, powers := [(16, 1), (21, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1), (51, 1)] }, { coefficient := 1, powers := [(19, 1), (51, 1)] }, { coefficient := 1, powers := [(19, 1), (56, 1)] }, { coefficient := 1, powers := [(46, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (31, 1), (56, 1)] }, { coefficient := 1, powers := [(21, 1), (49, 1), (56, 1)] }, { coefficient := 1, powers := [(21, 1), (52, 1)] }, { coefficient := 1, powers := [(27, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1)] }, { coefficient := 1, powers := [(6, 1), (59, 1)] }, { coefficient := 1, powers := [(23, 1), (39, 1)] }, { coefficient := 1, powers := [(23, 1), (44, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (40, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(19, 1), (49, 1), (56, 1)] }, { coefficient := 1, powers := [(19, 1), (52, 1)] }, { coefficient := 1, powers := [(40, 1)] }, { coefficient := 1, powers := [(46, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (61, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(39, 1)] }],
  [{ coefficient := 1, powers := [(40, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(56, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 18 → SparsePoly (Fin 64) := ![
  [{ coefficient := -1, powers := [(0, 1), (19, 1), (27, 1), (52, 1), (61, 1), (62, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (27, 1), (46, 1), (52, 1), (62, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(0, 2), (16, 1), (19, 1), (51, 1), (61, 1), (62, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (16, 1), (19, 1), (23, 1), (51, 1), (61, 1), (62, 1), (63, 1)] }, { coefficient := 1, powers := [(0, 1), (16, 1), (19, 1), (51, 1), (62, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (19, 1), (27, 1), (61, 1), (62, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (27, 1), (46, 1), (62, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(0, 2), (19, 1), (26, 1), (51, 1), (61, 1), (62, 1), (63, 1)] }, { coefficient := 1, powers := [(0, 1), (19, 1), (23, 1), (26, 1), (51, 1), (61, 1), (62, 1), (63, 1)] }, { coefficient := 1, powers := [(0, 1), (19, 1), (23, 1), (27, 1), (61, 1), (62, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (19, 1), (26, 1), (51, 1), (62, 1), (63, 1)] }, { coefficient := 1, powers := [(0, 1), (23, 1), (27, 1), (46, 1), (62, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (19, 1), (44, 1), (51, 1), (63, 1)] }, { coefficient := 1, powers := [(0, 1), (19, 1), (51, 1), (61, 1), (63, 1)] }, { coefficient := 1, powers := [(0, 1), (46, 1), (51, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(0, 2), (19, 1), (51, 1), (61, 1), (62, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (19, 1), (23, 1), (51, 1), (61, 1), (62, 1), (63, 1)] }, { coefficient := 1, powers := [(0, 1), (19, 1), (51, 1), (62, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (19, 1), (27, 1), (61, 1), (62, 1), (63, 1)] }, { coefficient := 1, powers := [(0, 1), (27, 1), (46, 1), (62, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (44, 1), (49, 1), (51, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (19, 1), (61, 1), (62, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (46, 1), (62, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(0, 2), (52, 1), (61, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (49, 1), (61, 1), (63, 1)] }, { coefficient := 1, powers := [(0, 1), (52, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (16, 1), (19, 1), (61, 1), (62, 1), (63, 1)] }, { coefficient := 1, powers := [(0, 1), (16, 1), (46, 1), (62, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (19, 1), (44, 1), (49, 1), (51, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(0, 2), (51, 1), (61, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (51, 1), (63, 1)] }, { coefficient := 1, powers := [(0, 1), (61, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (40, 1), (51, 1), (63, 1)] }, { coefficient := -1, powers := [(40, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(0, 2), (19, 1), (44, 1), (49, 1), (51, 1), (61, 1), (63, 1)] }, { coefficient := 1, powers := [(0, 1), (19, 1), (23, 1), (44, 1), (49, 1), (51, 1), (61, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (19, 1), (44, 1), (49, 1), (51, 1), (63, 1)] }, { coefficient := 1, powers := [(0, 1), (19, 1), (52, 1), (61, 1), (63, 1)] }, { coefficient := 1, powers := [(0, 1), (46, 1), (52, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (19, 1), (23, 1), (44, 1), (49, 1), (51, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(0, 3), (40, 1), (51, 1), (61, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 2), (12, 1), (19, 1), (26, 1), (51, 1), (61, 1), (62, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 2), (19, 1), (49, 1), (51, 1), (61, 1), (63, 1)] }, { coefficient := 1, powers := [(0, 2), (19, 1), (52, 1), (61, 1), (63, 1)] }, { coefficient := 1, powers := [(0, 2), (40, 1), (51, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 2), (40, 1), (61, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (3, 1), (16, 1), (19, 1), (31, 1), (61, 1), (62, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (3, 1), (16, 1), (31, 1), (46, 1), (62, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (12, 1), (18, 1), (19, 1), (27, 1), (61, 1), (62, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (12, 1), (18, 1), (27, 1), (46, 1), (62, 1), (63, 1)] }, { coefficient := 1, powers := [(0, 1), (12, 1), (19, 1), (21, 1), (61, 1), (62, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (12, 1), (19, 1), (23, 1), (26, 1), (51, 1), (61, 1), (62, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (12, 1), (19, 1), (23, 1), (27, 1), (61, 1), (62, 1), (63, 1)] }, { coefficient := 1, powers := [(0, 1), (12, 1), (19, 1), (26, 1), (51, 1), (62, 1), (63, 1)] }, { coefficient := 1, powers := [(0, 1), (12, 1), (21, 1), (46, 1), (62, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (12, 1), (23, 1), (27, 1), (46, 1), (62, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (16, 1), (19, 1), (21, 1), (49, 1), (61, 1), (62, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (16, 1), (21, 1), (46, 1), (49, 1), (62, 1), (63, 1)] }, { coefficient := 1, powers := [(0, 1), (19, 1), (49, 1), (51, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (19, 1), (52, 1), (63, 1)] }]
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
    (values : Fin 64 → R) :
    ¬ ∀ index : Fin 18,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component39.SelectedLeafB5_1_0.selectedHasNoCommonZero

end Krenn.Component39.SelectedLeafB5_1_0
