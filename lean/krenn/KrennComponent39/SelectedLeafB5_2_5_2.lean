import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component39.SelectedLeafB5_2_5_2

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "d79de0185342e28b934ebf28663c49084597f15fd8ad869b901d3d4a051519c8"
def certificateSHA256 : String := "d7608433e28da3442375e06dc1d7528dd04da36b2c4e19c4f3d5a30b4e1c96fa"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 27 → Fin 673 := ![
  16,
  22,
  31,
  184,
  191,
  192,
  193,
  301,
  397,
  419,
  425,
  429,
  434,
  440,
  471,
  482,
  566,
  645,
  660,
  661,
  663,
  666,
  668,
  669,
  670,
  671,
  672
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 27 → SparsePoly (Fin 67) := ![
  [{ coefficient := 1, powers := [(12, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (45, 1)] }, { coefficient := 1, powers := [(17, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (54, 1)] }, { coefficient := 1, powers := [(28, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (42, 1)] }, { coefficient := 1, powers := [(26, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (53, 1)] }, { coefficient := 1, powers := [(28, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (42, 1)] }, { coefficient := 1, powers := [(23, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (23, 1), (45, 1)] }, { coefficient := 1, powers := [(17, 1), (23, 1), (39, 1)] }, { coefficient := 1, powers := [(17, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (47, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1)] }, { coefficient := 1, powers := [(16, 1), (26, 1), (47, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1)] }, { coefficient := 1, powers := [(12, 1), (28, 1)] }, { coefficient := 1, powers := [(16, 1), (21, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (59, 1)] }, { coefficient := 1, powers := [(16, 1), (19, 1), (51, 1)] }, { coefficient := 1, powers := [(16, 1), (19, 1), (56, 1)] }, { coefficient := 1, powers := [(16, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (60, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (45, 1)] }, { coefficient := 1, powers := [(12, 1), (57, 1)] }, { coefficient := 1, powers := [(17, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (54, 1)] }, { coefficient := 1, powers := [(28, 1), (40, 1)] }, { coefficient := 1, powers := [(28, 1), (46, 1), (49, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1), (53, 1)] }, { coefficient := 1, powers := [(19, 1), (42, 1), (53, 1)] }, { coefficient := 1, powers := [(19, 1), (57, 1)] }, { coefficient := 1, powers := [(24, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (35, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1)] }, { coefficient := 1, powers := [(16, 1), (21, 1)] }, { coefficient := 1, powers := [(16, 1), (26, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (42, 1), (53, 1)] }, { coefficient := 1, powers := [(22, 1), (57, 1)] }, { coefficient := 1, powers := [(28, 1), (47, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (37, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (47, 1), (54, 1)] }, { coefficient := 1, powers := [(19, 1), (42, 1), (54, 1)] }, { coefficient := 1, powers := [(19, 1), (49, 1), (57, 1)] }, { coefficient := 1, powers := [(24, 1), (40, 1), (42, 1)] }, { coefficient := 1, powers := [(24, 1), (47, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (37, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (47, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (28, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (22, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1), (47, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (40, 1)] }, { coefficient := 1, powers := [(12, 1), (22, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1), (28, 1), (47, 1)] }, { coefficient := 1, powers := [(12, 1), (34, 1), (37, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (54, 1)] }, { coefficient := 1, powers := [(17, 1), (28, 1), (40, 1)] }, { coefficient := 1, powers := [(17, 1), (31, 1), (37, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (61, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(40, 1)] }],
  [{ coefficient := 1, powers := [(56, 1)] }],
  [{ coefficient := 1, powers := [(57, 1), (65, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(23, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (66, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(28, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 27 → SparsePoly (Fin 67) := ![
  [{ coefficient := -1, powers := [(22, 1), (57, 2), (65, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (21, 1), (31, 1), (57, 1), (62, 1), (66, 1)] }, { coefficient := -1, powers := [(5, 1), (26, 1), (31, 1), (57, 1), (62, 1), (66, 1)] }, { coefficient := 1, powers := [(19, 1), (31, 1), (35, 1), (51, 1), (57, 1), (66, 1)] }, { coefficient := 1, powers := [(22, 1), (42, 1), (54, 1), (57, 1), (65, 1), (66, 1)] }, { coefficient := 1, powers := [(31, 1), (35, 1), (46, 1), (57, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (54, 1), (57, 1), (65, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(22, 1), (24, 1), (57, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(16, 1), (47, 1), (57, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(16, 1), (54, 1), (57, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (42, 1), (57, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (49, 1), (53, 1), (57, 1), (61, 1), (65, 1)] }, { coefficient := -1, powers := [(2, 1), (54, 1), (57, 1), (61, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (24, 1), (52, 1), (57, 1), (65, 1)] }, { coefficient := -2, powers := [(22, 1), (54, 1), (57, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(54, 1), (57, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(47, 1), (57, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(31, 1), (35, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (57, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (57, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (49, 1), (57, 1), (61, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (31, 1), (57, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (57, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (57, 1), (61, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(57, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (37, 1), (57, 1), (60, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (31, 1), (35, 1), (57, 1), (59, 1)] }, { coefficient := -1, powers := [(5, 1), (31, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (2, 1), (57, 2), (61, 1), (65, 1)] }, { coefficient := -1, powers := [(2, 1), (24, 1), (42, 1), (57, 1), (61, 1), (65, 1)] }, { coefficient := 1, powers := [(2, 1), (57, 2), (65, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (57, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (19, 1), (31, 1), (35, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (31, 1), (57, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(2, 1), (47, 1), (49, 1), (53, 1), (57, 1), (61, 1), (65, 1)] }, { coefficient := 1, powers := [(2, 1), (47, 1), (54, 1), (57, 1), (61, 1), (65, 1)] }, { coefficient := -1, powers := [(16, 1), (22, 1), (24, 1), (45, 1), (52, 1), (57, 1), (65, 1)] }, { coefficient := 2, powers := [(16, 1), (22, 1), (45, 1), (54, 1), (57, 1), (65, 1)] }, { coefficient := -1, powers := [(17, 1), (22, 1), (24, 1), (39, 1), (52, 1), (57, 1), (65, 1)] }, { coefficient := 2, powers := [(17, 1), (22, 1), (39, 1), (54, 1), (57, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (47, 1), (54, 1), (57, 1), (65, 1)] }, { coefficient := 1, powers := [(5, 1), (16, 1), (21, 1), (31, 1), (57, 1), (62, 1)] }, { coefficient := 1, powers := [(5, 1), (16, 1), (26, 1), (31, 1), (57, 1), (62, 1)] }, { coefficient := 1, powers := [(12, 1), (22, 1), (57, 2), (65, 1)] }, { coefficient := -1, powers := [(16, 1), (19, 1), (31, 1), (35, 1), (51, 1), (57, 1)] }, { coefficient := -1, powers := [(16, 1), (22, 1), (42, 1), (54, 1), (57, 1), (65, 1)] }, { coefficient := -1, powers := [(16, 1), (31, 1), (35, 1), (46, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (57, 1), (60, 1), (65, 1)] }, { coefficient := 1, powers := [(12, 1), (42, 1), (46, 1), (57, 1), (65, 1)] }, { coefficient := -1, powers := [(12, 1), (47, 1), (57, 1), (65, 1)] }, { coefficient := 1, powers := [(16, 1), (47, 1), (49, 1), (57, 1), (65, 1)] }, { coefficient := -1, powers := [(17, 1), (46, 1), (49, 1), (57, 1), (65, 1)] }]
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
    (values : Fin 67 → R) :
    ¬ ∀ index : Fin 27,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component39.SelectedLeafB5_2_5_2.selectedHasNoCommonZero

end Krenn.Component39.SelectedLeafB5_2_5_2
