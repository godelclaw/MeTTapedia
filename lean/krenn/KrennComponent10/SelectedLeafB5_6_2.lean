import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component10.SelectedLeafB5_6_2

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "89d29ff939ebb50693bffee3d9b1fe4e3db22e7044bfb332d94fa0b162f63e61"
def certificateSHA256 : String := "2c8918540ec8d62b69bd7d6d458ff1f25c612284fec263355bf93ae72e4e5538"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 37 → Fin 644 := ![
  0,
  2,
  8,
  19,
  21,
  24,
  69,
  161,
  162,
  164,
  167,
  169,
  170,
  190,
  349,
  350,
  356,
  359,
  361,
  363,
  446,
  462,
  463,
  465,
  466,
  473,
  490,
  499,
  550,
  582,
  595,
  634,
  635,
  638,
  639,
  640,
  643
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 37 → SparsePoly (Fin 65) := ![
  [{ coefficient := 1, powers := [(3, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (29, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1)] }, { coefficient := 1, powers := [(24, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (48, 1)] }, { coefficient := 1, powers := [(24, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (53, 1)] }, { coefficient := 1, powers := [(19, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (58, 1)] }, { coefficient := 1, powers := [(17, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (58, 1)] }, { coefficient := 1, powers := [(17, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (29, 1)] }, { coefficient := 1, powers := [(29, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (52, 1)] }, { coefficient := 1, powers := [(29, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (59, 1)] }, { coefficient := 1, powers := [(12, 1), (48, 1)] }, { coefficient := 1, powers := [(18, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (59, 1)] }, { coefficient := 1, powers := [(12, 1), (56, 1)] }, { coefficient := 1, powers := [(18, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (46, 1)] }, { coefficient := 1, powers := [(18, 1), (40, 1)] }, { coefficient := 1, powers := [(18, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (53, 1)] }, { coefficient := 1, powers := [(29, 1), (41, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (36, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (24, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (19, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (38, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (41, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (48, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (24, 1), (46, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (40, 1)] }, { coefficient := 1, powers := [(18, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (47, 1)] }, { coefficient := 1, powers := [(5, 1), (27, 1), (58, 1)] }, { coefficient := 1, powers := [(17, 1), (23, 1)] }, { coefficient := 1, powers := [(17, 1), (27, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (48, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1)] }, { coefficient := 1, powers := [(17, 1), (27, 1), (48, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (52, 1)] }, { coefficient := 1, powers := [(8, 1), (22, 1), (58, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (52, 1)] }, { coefficient := 1, powers := [(17, 1), (29, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (53, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1)] }, { coefficient := 1, powers := [(12, 1), (29, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (40, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(43, 1), (52, 1)] }, { coefficient := 1, powers := [(56, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (36, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1)] }, { coefficient := 1, powers := [(17, 1), (27, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (27, 1), (58, 1)] }, { coefficient := 1, powers := [(6, 1), (22, 1), (58, 1)] }, { coefficient := 1, powers := [(22, 1)] }, { coefficient := 1, powers := [(27, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (43, 1), (52, 1)] }, { coefficient := 1, powers := [(23, 1), (56, 1)] }, { coefficient := 1, powers := [(29, 1), (48, 1)] }, { coefficient := 1, powers := [(35, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (36, 1), (58, 1)] }, { coefficient := 1, powers := [(0, 1)] }, { coefficient := 1, powers := [(3, 1), (24, 1), (58, 1)] }, { coefficient := 1, powers := [(6, 1), (19, 1), (58, 1)] }, { coefficient := 1, powers := [(19, 1)] }, { coefficient := 1, powers := [(24, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (47, 1), (52, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (58, 1)] }, { coefficient := 1, powers := [(8, 1), (23, 1), (58, 1)] }, { coefficient := 1, powers := [(17, 1), (23, 1), (52, 1)] }, { coefficient := 1, powers := [(17, 1), (29, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (41, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (48, 1), (53, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (53, 1)] }, { coefficient := 1, powers := [(8, 1), (23, 1), (59, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (48, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(12, 1), (23, 1), (56, 1)] }, { coefficient := 1, powers := [(12, 1), (29, 1), (48, 1)] }, { coefficient := 1, powers := [(12, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (53, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (41, 1)] }, { coefficient := 1, powers := [(18, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (60, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(39, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(40, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(41, 1)] }],
  [{ coefficient := 1, powers := [(56, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 37 → SparsePoly (Fin 65) := ![
  [{ coefficient := 2, powers := [(17, 1), (27, 1), (38, 1), (58, 1)] }],
  [{ coefficient := 2, powers := [(17, 1), (22, 1), (38, 1), (58, 1)] }],
  [{ coefficient := 2, powers := [(29, 1), (48, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(27, 1), (53, 1)] }],
  [{ coefficient := -2, powers := [(23, 1), (24, 1), (46, 1), (51, 1), (63, 1)] }, { coefficient := 2, powers := [(23, 1), (46, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(17, 1), (48, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (24, 1), (46, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (29, 1), (46, 1)] }],
  [{ coefficient := -2, powers := [(12, 1), (29, 1), (60, 1)] }],
  [{ coefficient := 2, powers := [(18, 1), (23, 1), (51, 1)] }],
  [{ coefficient := -1, powers := [(27, 1), (36, 1), (52, 1), (59, 1)] }, { coefficient := 2, powers := [(29, 1), (36, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(22, 1), (36, 1), (47, 1), (59, 1)] }, { coefficient := 2, powers := [(23, 1), (36, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (24, 1), (46, 1), (47, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (12, 1), (46, 1)] }, { coefficient := -1, powers := [(12, 1), (24, 1), (39, 1), (46, 1), (62, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (46, 1)] }, { coefficient := -1, powers := [(17, 1), (36, 1), (59, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (29, 1), (60, 1)] }, { coefficient := -1, powers := [(29, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (23, 1), (51, 1)] }, { coefficient := -2, powers := [(19, 1), (23, 1), (51, 1)] }, { coefficient := -2, powers := [(23, 1), (24, 1), (40, 1), (51, 1), (63, 1)] }, { coefficient := 2, powers := [(23, 1), (40, 1), (63, 1)] }, { coefficient := -1, powers := [(23, 1)] }],
  [{ coefficient := -2, powers := [(23, 1), (53, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(18, 1)] }],
  [{ coefficient := -2, powers := [(8, 1), (23, 1), (51, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (60, 1)] }],
  [{ coefficient := 2, powers := [(23, 1), (51, 1), (53, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(36, 1), (52, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(53, 1)] }],
  [{ coefficient := 1, powers := [(36, 1), (47, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(48, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (23, 1)] }],
  [{ coefficient := 2, powers := [(38, 1), (59, 1)] }],
  [{ coefficient := -2, powers := [(17, 1), (38, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(12, 1)] }],
  [{ coefficient := 2, powers := [(8, 1), (23, 1), (51, 1), (59, 1)] }],
  [{ coefficient := -2, powers := [(36, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (48, 1), (53, 1)] }, { coefficient := -2, powers := [(5, 1), (29, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (23, 1), (24, 1), (46, 1), (52, 1)] }],
  [{ coefficient := 2, powers := [(8, 1), (23, 1), (24, 1), (51, 1), (59, 1)] }, { coefficient := -2, powers := [(8, 1), (23, 1), (59, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (18, 1), (29, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (2, 1), (41, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (12, 1), (23, 1), (40, 1)] }, { coefficient := 2, powers := [(0, 1), (12, 1), (23, 1), (51, 1)] }, { coefficient := 1, powers := [(2, 1), (41, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1)] }, { coefficient := 2, powers := [(12, 1), (19, 1), (23, 1), (51, 1)] }, { coefficient := 2, powers := [(12, 1), (23, 1), (24, 1), (40, 1), (51, 1), (63, 1)] }, { coefficient := -2, powers := [(12, 1), (23, 1), (40, 1), (63, 1)] }, { coefficient := 2, powers := [(12, 1), (23, 1)] }]
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
    (values : Fin 65 → R) :
    ¬ ∀ index : Fin 37,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component10.SelectedLeafB5_6_2.selectedHasNoCommonZero

end Krenn.Component10.SelectedLeafB5_6_2
