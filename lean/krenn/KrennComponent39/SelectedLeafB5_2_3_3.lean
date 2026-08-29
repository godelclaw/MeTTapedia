import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component39.SelectedLeafB5_2_3_3

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "598f38941f289c66100d2d100d30316c79cf3f5bb189a94c8f70728265475ac1"
def certificateSHA256 : String := "3c0649daf5881c587b61806e543fdd52d5d3ad20651c3d228b7078d81225b05c"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 29 → Fin 673 := ![
  16,
  22,
  30,
  31,
  192,
  193,
  277,
  301,
  317,
  318,
  365,
  397,
  410,
  419,
  430,
  462,
  471,
  580,
  607,
  645,
  651,
  660,
  661,
  666,
  668,
  669,
  670,
  671,
  672
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 29 → SparsePoly (Fin 68) := ![
  [{ coefficient := 1, powers := [(12, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (42, 1)] }, { coefficient := 1, powers := [(26, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (53, 1)] }, { coefficient := 1, powers := [(28, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (23, 1), (47, 1)] }, { coefficient := 1, powers := [(17, 1), (19, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (42, 1)] }, { coefficient := 1, powers := [(23, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (51, 1)] }, { coefficient := 1, powers := [(22, 1), (56, 1)] }, { coefficient := 1, powers := [(27, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (53, 1)] }, { coefficient := 1, powers := [(28, 1), (39, 1)] }, { coefficient := 1, powers := [(28, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (22, 1), (59, 1)] }, { coefficient := 1, powers := [(22, 1)] }, { coefficient := 1, powers := [(26, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (23, 1), (45, 1)] }, { coefficient := 1, powers := [(17, 1), (23, 1), (39, 1)] }, { coefficient := 1, powers := [(17, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1)] }, { coefficient := 1, powers := [(23, 1), (39, 1), (42, 1)] }, { coefficient := 1, powers := [(23, 1), (45, 1)] }, { coefficient := 1, powers := [(42, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (47, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1)] }, { coefficient := 1, powers := [(16, 1), (26, 1), (47, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (60, 1)] }, { coefficient := 1, powers := [(12, 1), (47, 1)] }, { coefficient := 1, powers := [(17, 1), (19, 1), (52, 1)] }, { coefficient := 1, powers := [(17, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1), (51, 1)] }, { coefficient := 1, powers := [(39, 1), (42, 1)] }, { coefficient := 1, powers := [(42, 1), (51, 1)] }, { coefficient := 1, powers := [(45, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1), (53, 1)] }, { coefficient := 1, powers := [(19, 1), (42, 1), (53, 1)] }, { coefficient := 1, powers := [(19, 1), (57, 1)] }, { coefficient := 1, powers := [(24, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1)] }, { coefficient := 1, powers := [(6, 1), (59, 1)] }, { coefficient := 1, powers := [(23, 1), (39, 1)] }, { coefficient := 1, powers := [(23, 1), (44, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (39, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (45, 1), (53, 1)] }, { coefficient := 1, powers := [(24, 1), (39, 1), (42, 1)] }, { coefficient := 1, powers := [(24, 1), (45, 1)] }, { coefficient := 1, powers := [(42, 1), (53, 1)] }, { coefficient := 1, powers := [(57, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (37, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (47, 1), (54, 1)] }, { coefficient := 1, powers := [(19, 1), (42, 1), (54, 1)] }, { coefficient := 1, powers := [(19, 1), (49, 1), (57, 1)] }, { coefficient := 1, powers := [(24, 1), (40, 1), (42, 1)] }, { coefficient := 1, powers := [(24, 1), (47, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (40, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (56, 1)] }, { coefficient := 1, powers := [(12, 1), (22, 1), (56, 1)] }, { coefficient := 1, powers := [(12, 1), (27, 1), (46, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1), (52, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (37, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (47, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (28, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (22, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1), (47, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (40, 1)] }, { coefficient := 1, powers := [(12, 1), (22, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1), (28, 1), (47, 1)] }, { coefficient := 1, powers := [(12, 1), (34, 1), (37, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (54, 1)] }, { coefficient := 1, powers := [(17, 1), (28, 1), (40, 1)] }, { coefficient := 1, powers := [(17, 1), (31, 1), (37, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (61, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(40, 1)] }],
  [{ coefficient := 1, powers := [(56, 1), (64, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(57, 1), (65, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(23, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (66, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(28, 1), (67, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 29 → SparsePoly (Fin 68) := ![
  [{ coefficient := 1, powers := [(22, 1), (51, 1), (57, 1), (64, 1), (66, 1)] }, { coefficient := 1, powers := [(22, 1), (57, 1), (66, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (42, 1), (54, 1), (66, 1)] }, { coefficient := -1, powers := [(22, 1), (52, 1), (57, 1), (64, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (8, 1), (26, 1), (60, 1), (61, 1), (66, 1)] }, { coefficient := -1, powers := [(0, 1), (8, 1), (27, 1), (60, 1), (66, 1)] }, { coefficient := -1, powers := [(2, 1), (52, 1), (57, 1), (64, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (31, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(16, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (8, 1), (27, 1), (60, 1), (67, 1)] }],
  [{ coefficient := -1, powers := [(28, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (49, 1), (53, 1), (61, 1)] }, { coefficient := -1, powers := [(2, 1), (54, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (57, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (8, 1), (22, 1), (60, 1), (67, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (8, 1), (60, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(31, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (22, 1), (24, 1), (51, 1), (60, 1), (65, 1)] }, { coefficient := -1, powers := [(8, 1), (22, 1), (53, 1), (60, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(54, 1)] }],
  [{ coefficient := 1, powers := [(28, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (22, 1), (24, 1), (60, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (49, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (8, 1), (22, 1), (60, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (22, 1), (60, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(57, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(0, 1), (8, 1), (22, 1), (44, 1), (60, 1)] }, { coefficient := -1, powers := [(2, 1), (37, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (2, 1), (57, 1), (61, 1)] }, { coefficient := -1, powers := [(2, 1), (24, 1), (42, 1), (61, 1)] }, { coefficient := -1, powers := [(2, 1), (56, 1), (57, 1), (64, 1)] }, { coefficient := 1, powers := [(2, 1), (57, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1)] }, { coefficient := -1, powers := [(16, 1), (27, 1), (57, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (31, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (8, 1), (22, 1), (39, 1), (60, 1)] }, { coefficient := -1, powers := [(8, 1), (22, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (8, 1), (22, 1), (39, 1), (60, 1), (61, 1)] }, { coefficient := -1, powers := [(0, 1), (8, 1), (22, 1), (44, 1), (60, 1), (61, 1)] }, { coefficient := -1, powers := [(2, 1), (47, 1), (49, 1), (53, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (47, 1), (54, 1), (61, 1)] }, { coefficient := -1, powers := [(8, 1), (22, 1), (24, 1), (39, 1), (42, 1), (51, 1), (60, 1), (65, 1)] }, { coefficient := -1, powers := [(8, 1), (22, 1), (24, 1), (45, 1), (51, 1), (60, 1), (65, 1)] }, { coefficient := 1, powers := [(8, 1), (22, 1), (39, 1), (42, 1), (53, 1), (60, 1), (65, 1)] }, { coefficient := 1, powers := [(8, 1), (22, 1), (45, 1), (53, 1), (60, 1), (65, 1)] }, { coefficient := 1, powers := [(16, 1), (28, 1), (47, 1), (52, 1)] }, { coefficient := -1, powers := [(16, 1), (31, 1), (37, 1), (45, 1)] }, { coefficient := -1, powers := [(17, 1), (31, 1), (37, 1), (39, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (8, 1), (26, 1), (46, 1), (60, 1), (61, 1)] }, { coefficient := 1, powers := [(0, 1), (8, 1), (27, 1), (46, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (46, 1), (52, 1), (57, 1), (64, 1)] }, { coefficient := -1, powers := [(8, 1), (31, 1), (47, 1)] }, { coefficient := -1, powers := [(12, 1), (22, 1), (51, 1), (57, 1), (64, 1)] }, { coefficient := -1, powers := [(12, 1), (22, 1), (57, 1)] }, { coefficient := -1, powers := [(12, 1), (34, 1), (37, 1)] }, { coefficient := -1, powers := [(16, 1), (22, 1), (42, 1), (54, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1), (52, 1), (57, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (8, 1), (22, 1), (39, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (8, 1), (22, 1), (44, 1), (60, 1)] }, { coefficient := -1, powers := [(0, 1), (8, 1), (27, 1), (46, 1), (60, 1)] }]
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
    (values : Fin 68 → R) :
    ¬ ∀ index : Fin 29,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component39.SelectedLeafB5_2_3_3.selectedHasNoCommonZero

end Krenn.Component39.SelectedLeafB5_2_3_3
