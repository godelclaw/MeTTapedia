import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component39.SelectedLeafB1_2_2_6

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "5ebf05d330876256974e688776dbb16b748df36a8ec052865261394343153a6c"
def certificateSHA256 : String := "1e4efa7170d48e445a42516e528da137081206662d695c303f1144654700ecd6"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 29 → Fin 673 := ![
  16,
  22,
  29,
  30,
  31,
  191,
  192,
  193,
  419,
  425,
  427,
  429,
  433,
  434,
  439,
  440,
  482,
  502,
  523,
  566,
  581,
  615,
  660,
  661,
  663,
  666,
  669,
  671,
  672
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 29 → SparsePoly (Fin 66) := ![
  [{ coefficient := 1, powers := [(12, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (54, 1)] }, { coefficient := 1, powers := [(28, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (42, 1)] }, { coefficient := 1, powers := [(26, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (53, 1)] }, { coefficient := 1, powers := [(28, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (47, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1)] }, { coefficient := 1, powers := [(16, 1), (26, 1), (47, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1)] }, { coefficient := 1, powers := [(12, 1), (28, 1)] }, { coefficient := 1, powers := [(16, 1), (21, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (34, 1)] }, { coefficient := 1, powers := [(21, 1), (42, 1)] }, { coefficient := 1, powers := [(26, 1), (42, 1)] }, { coefficient := 1, powers := [(34, 1), (35, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (59, 1)] }, { coefficient := 1, powers := [(16, 1), (19, 1), (51, 1)] }, { coefficient := 1, powers := [(16, 1), (19, 1), (56, 1)] }, { coefficient := 1, powers := [(16, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (59, 1)] }, { coefficient := 1, powers := [(16, 1), (24, 1), (39, 1)] }, { coefficient := 1, powers := [(16, 1), (24, 1), (44, 1)] }, { coefficient := 1, powers := [(16, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (60, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (45, 1)] }, { coefficient := 1, powers := [(12, 1), (57, 1)] }, { coefficient := 1, powers := [(17, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (39, 1)] }, { coefficient := 1, powers := [(16, 1), (44, 1)] }, { coefficient := 1, powers := [(16, 1), (51, 1)] }, { coefficient := 1, powers := [(16, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (54, 1)] }, { coefficient := 1, powers := [(28, 1), (40, 1)] }, { coefficient := 1, powers := [(28, 1), (46, 1), (49, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (35, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1)] }, { coefficient := 1, powers := [(16, 1), (21, 1)] }, { coefficient := 1, powers := [(16, 1), (26, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (25, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (30, 1), (56, 1)] }, { coefficient := 1, powers := [(3, 1), (33, 1), (51, 1)] }, { coefficient := 1, powers := [(25, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (25, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (51, 1)] }, { coefficient := 1, powers := [(16, 1), (25, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (42, 1), (53, 1)] }, { coefficient := 1, powers := [(22, 1), (57, 1)] }, { coefficient := 1, powers := [(28, 1), (47, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (51, 1)] }, { coefficient := 1, powers := [(3, 1), (59, 1)] }, { coefficient := 1, powers := [(18, 1), (51, 1)] }, { coefficient := 1, powers := [(18, 1), (56, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (37, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (46, 1), (53, 1)] }, { coefficient := 1, powers := [(5, 1), (28, 1), (59, 1)] }, { coefficient := 1, powers := [(8, 1), (22, 1), (59, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1), (53, 1)] }, { coefficient := 1, powers := [(16, 1), (28, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (37, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (47, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (28, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (22, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1), (47, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (40, 1)] }, { coefficient := 1, powers := [(12, 1), (22, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1), (28, 1), (47, 1)] }, { coefficient := 1, powers := [(12, 1), (34, 1), (37, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (54, 1)] }, { coefficient := 1, powers := [(17, 1), (28, 1), (40, 1)] }, { coefficient := 1, powers := [(17, 1), (31, 1), (37, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (61, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(40, 1)] }],
  [{ coefficient := 1, powers := [(57, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (65, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(28, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 29 → SparsePoly (Fin 66) := ![
  [{ coefficient := -1, powers := [(22, 1), (24, 1), (45, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (19, 1), (25, 1), (34, 1), (51, 1), (54, 1), (65, 2)] }, { coefficient := -1, powers := [(3, 1), (19, 1), (25, 1), (34, 1), (54, 1), (56, 1), (65, 2)] }, { coefficient := -1, powers := [(3, 1), (25, 1), (34, 1), (46, 1), (54, 1), (65, 2)] }, { coefficient := 1, powers := [(3, 1), (34, 1), (46, 1), (54, 1), (65, 1)] }, { coefficient := -1, powers := [(5, 1), (21, 1), (34, 1), (54, 1), (61, 1), (65, 1)] }, { coefficient := -1, powers := [(5, 1), (26, 1), (34, 1), (54, 1), (61, 1), (65, 1)] }, { coefficient := -1, powers := [(21, 1), (37, 1), (60, 1), (65, 1)] }, { coefficient := 1, powers := [(22, 1), (24, 1), (35, 1), (51, 1), (60, 1), (65, 1)] }, { coefficient := 1, powers := [(22, 1), (24, 1), (35, 1), (56, 1), (60, 1), (65, 1)] }, { coefficient := -1, powers := [(22, 1), (35, 1), (53, 1), (60, 1), (65, 1)] }, { coefficient := -1, powers := [(22, 1), (42, 1), (54, 1), (65, 1)] }, { coefficient := -1, powers := [(26, 1), (37, 1), (60, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (21, 1), (54, 1), (59, 1), (65, 1)] }, { coefficient := 1, powers := [(5, 1), (26, 1), (54, 1), (59, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (35, 1), (53, 1), (60, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (54, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(16, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (42, 1)] }, { coefficient := 1, powers := [(16, 1), (35, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(54, 1)] }],
  [{ coefficient := 1, powers := [(47, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (54, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (25, 1), (34, 1), (54, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (35, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(22, 1)] }],
  [{ coefficient := -1, powers := [(22, 1), (24, 1), (35, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(17, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (34, 1), (54, 1), (61, 1)] }, { coefficient := 1, powers := [(37, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (34, 1), (54, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (34, 1), (54, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(12, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (25, 1), (34, 1), (54, 1), (65, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(35, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(5, 1), (25, 1), (34, 1), (51, 1), (54, 1), (65, 1)] }, { coefficient := -1, powers := [(5, 1), (34, 1), (51, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (34, 1), (35, 1), (54, 1), (59, 1)] }, { coefficient := -1, powers := [(5, 1), (34, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (34, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (40, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1)] }, { coefficient := -1, powers := [(12, 1), (22, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (35, 1), (46, 1), (53, 1), (60, 1)] }, { coefficient := -1, powers := [(2, 1), (47, 1), (54, 1)] }, { coefficient := 1, powers := [(3, 1), (16, 1), (19, 1), (25, 1), (34, 1), (51, 1), (54, 1), (65, 1)] }, { coefficient := 1, powers := [(3, 1), (16, 1), (19, 1), (25, 1), (34, 1), (54, 1), (56, 1), (65, 1)] }, { coefficient := 1, powers := [(3, 1), (16, 1), (25, 1), (34, 1), (46, 1), (54, 1), (65, 1)] }, { coefficient := 1, powers := [(5, 1), (16, 1), (21, 1), (34, 1), (54, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (16, 1), (26, 1), (34, 1), (54, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (18, 1), (34, 1), (51, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (18, 1), (34, 1), (54, 1), (56, 1)] }, { coefficient := -1, powers := [(5, 1), (21, 1), (42, 1), (54, 1), (59, 1)] }, { coefficient := -1, powers := [(5, 1), (26, 1), (42, 1), (54, 1), (59, 1)] }, { coefficient := 1, powers := [(12, 1), (22, 1), (24, 1), (45, 1)] }, { coefficient := 1, powers := [(16, 1), (21, 1), (37, 1), (60, 1)] }, { coefficient := -1, powers := [(16, 1), (22, 1), (24, 1), (35, 1), (51, 1), (60, 1)] }, { coefficient := -1, powers := [(16, 1), (22, 1), (24, 1), (35, 1), (56, 1), (60, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1), (35, 1), (53, 1), (60, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1), (42, 1), (54, 1)] }, { coefficient := 1, powers := [(16, 1), (26, 1), (37, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (35, 1), (59, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (60, 1)] }, { coefficient := 1, powers := [(12, 1), (42, 1), (46, 1)] }, { coefficient := -1, powers := [(12, 1), (47, 1)] }, { coefficient := 1, powers := [(16, 1), (47, 1), (49, 1)] }, { coefficient := -1, powers := [(17, 1), (46, 1), (49, 1)] }]
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
    ¬ ∀ index : Fin 29,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component39.SelectedLeafB1_2_2_6.selectedHasNoCommonZero

end Krenn.Component39.SelectedLeafB1_2_2_6
