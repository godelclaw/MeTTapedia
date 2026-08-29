import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component39.SelectedLeafB5_2_2_7

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "af9208ab57cd3b65a84f054a376df4be824746d8342c3904eeac41a7481c9ed0"
def certificateSHA256 : String := "20aeac8c55df4960969707074b09a86490e3637210c87b1c7a2e92da9ce04d7a"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 25 → Fin 673 := ![
  16,
  22,
  29,
  30,
  31,
  192,
  277,
  301,
  419,
  427,
  429,
  430,
  434,
  440,
  482,
  502,
  523,
  581,
  645,
  660,
  661,
  663,
  666,
  669,
  671
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 25 → SparsePoly (Fin 68) := ![
  [{ coefficient := 1, powers := [(12, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (42, 1)] }, { coefficient := 1, powers := [(26, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (23, 1), (47, 1)] }, { coefficient := 1, powers := [(17, 1), (19, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (42, 1)] }, { coefficient := 1, powers := [(23, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (47, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1)] }, { coefficient := 1, powers := [(16, 1), (26, 1), (47, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (34, 1)] }, { coefficient := 1, powers := [(21, 1), (42, 1)] }, { coefficient := 1, powers := [(26, 1), (42, 1)] }, { coefficient := 1, powers := [(34, 1), (35, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (59, 1)] }, { coefficient := 1, powers := [(16, 1), (19, 1), (51, 1)] }, { coefficient := 1, powers := [(16, 1), (19, 1), (56, 1)] }, { coefficient := 1, powers := [(16, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (60, 1)] }, { coefficient := 1, powers := [(12, 1), (47, 1)] }, { coefficient := 1, powers := [(17, 1), (19, 1), (52, 1)] }, { coefficient := 1, powers := [(17, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (60, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (45, 1)] }, { coefficient := 1, powers := [(12, 1), (57, 1)] }, { coefficient := 1, powers := [(17, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (54, 1)] }, { coefficient := 1, powers := [(28, 1), (40, 1)] }, { coefficient := 1, powers := [(28, 1), (46, 1), (49, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (35, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1)] }, { coefficient := 1, powers := [(16, 1), (21, 1)] }, { coefficient := 1, powers := [(16, 1), (26, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (25, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (30, 1), (56, 1)] }, { coefficient := 1, powers := [(3, 1), (33, 1), (51, 1)] }, { coefficient := 1, powers := [(25, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (25, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (51, 1)] }, { coefficient := 1, powers := [(16, 1), (25, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (51, 1)] }, { coefficient := 1, powers := [(3, 1), (59, 1)] }, { coefficient := 1, powers := [(18, 1), (51, 1)] }, { coefficient := 1, powers := [(18, 1), (56, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (37, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (47, 1), (54, 1)] }, { coefficient := 1, powers := [(19, 1), (42, 1), (54, 1)] }, { coefficient := 1, powers := [(19, 1), (49, 1), (57, 1)] }, { coefficient := 1, powers := [(24, 1), (40, 1), (42, 1)] }, { coefficient := 1, powers := [(24, 1), (47, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (37, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (47, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (28, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (22, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1), (47, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (40, 1)] }, { coefficient := 1, powers := [(12, 1), (22, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1), (28, 1), (47, 1)] }, { coefficient := 1, powers := [(12, 1), (34, 1), (37, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (54, 1)] }, { coefficient := 1, powers := [(17, 1), (28, 1), (40, 1)] }, { coefficient := 1, powers := [(17, 1), (31, 1), (37, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (61, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(40, 1)] }],
  [{ coefficient := 1, powers := [(57, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (66, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 25 → SparsePoly (Fin 68) := ![
  [{ coefficient := -1, powers := [(22, 1), (24, 1), (45, 1), (66, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (28, 1), (47, 1), (52, 1), (66, 1)] }, { coefficient := -1, powers := [(3, 1), (19, 1), (25, 1), (34, 1), (51, 1), (54, 1), (66, 2)] }, { coefficient := -1, powers := [(3, 1), (19, 1), (25, 1), (34, 1), (54, 1), (56, 1), (66, 2)] }, { coefficient := -1, powers := [(3, 1), (25, 1), (34, 1), (46, 1), (54, 1), (66, 2)] }, { coefficient := 1, powers := [(3, 1), (34, 1), (46, 1), (54, 1), (66, 1)] }, { coefficient := -1, powers := [(5, 1), (21, 1), (34, 1), (54, 1), (62, 1), (66, 1)] }, { coefficient := -1, powers := [(5, 1), (26, 1), (34, 1), (54, 1), (62, 1), (66, 1)] }, { coefficient := -1, powers := [(19, 1), (28, 1), (42, 1), (52, 1), (66, 1)] }, { coefficient := -1, powers := [(22, 1), (42, 1), (54, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (19, 1), (54, 1), (61, 1), (66, 1)] }, { coefficient := 1, powers := [(5, 1), (21, 1), (54, 1), (59, 1), (66, 1)] }, { coefficient := 1, powers := [(5, 1), (26, 1), (54, 1), (59, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(17, 1), (28, 1), (49, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (2, 1), (54, 1), (61, 1), (66, 1)] }, { coefficient := -1, powers := [(2, 1), (24, 1), (49, 1), (61, 1), (66, 1)] }, { coefficient := 2, powers := [(2, 1), (54, 1), (66, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(28, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (28, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(54, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (54, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (25, 1), (34, 1), (54, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(28, 1)] }],
  [{ coefficient := 1, powers := [(22, 1)] }],
  [{ coefficient := 1, powers := [(17, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (34, 1), (54, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (34, 1), (54, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (34, 1), (54, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (25, 1), (34, 1), (54, 1), (66, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(2, 1), (37, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (34, 1), (35, 1), (54, 1), (59, 1)] }, { coefficient := -1, powers := [(5, 1), (34, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (24, 1), (42, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1)] }, { coefficient := -1, powers := [(17, 1), (28, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (2, 1), (40, 1), (61, 1)] }, { coefficient := -1, powers := [(2, 1), (19, 1), (49, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (40, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (2, 1), (47, 1), (54, 1), (61, 1)] }, { coefficient := 1, powers := [(0, 1), (5, 1), (34, 1), (51, 1), (54, 1)] }, { coefficient := 1, powers := [(0, 1), (16, 1), (28, 1), (47, 1), (52, 1)] }, { coefficient := 1, powers := [(2, 1), (19, 1), (42, 1), (54, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (24, 1), (47, 1), (49, 1), (61, 1)] }, { coefficient := -2, powers := [(2, 1), (47, 1), (54, 1)] }, { coefficient := 1, powers := [(3, 1), (16, 1), (19, 1), (25, 1), (34, 1), (51, 1), (54, 1), (66, 1)] }, { coefficient := 1, powers := [(3, 1), (16, 1), (19, 1), (25, 1), (34, 1), (54, 1), (56, 1), (66, 1)] }, { coefficient := 1, powers := [(3, 1), (16, 1), (25, 1), (34, 1), (46, 1), (54, 1), (66, 1)] }, { coefficient := 1, powers := [(5, 1), (16, 1), (21, 1), (34, 1), (54, 1), (62, 1)] }, { coefficient := 1, powers := [(5, 1), (16, 1), (26, 1), (34, 1), (54, 1), (62, 1)] }, { coefficient := 1, powers := [(5, 1), (18, 1), (34, 1), (51, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (18, 1), (34, 1), (54, 1), (56, 1)] }, { coefficient := -1, powers := [(5, 1), (21, 1), (42, 1), (54, 1), (59, 1)] }, { coefficient := -1, powers := [(5, 1), (26, 1), (42, 1), (54, 1), (59, 1)] }, { coefficient := -1, powers := [(8, 1), (31, 1), (47, 1)] }, { coefficient := 1, powers := [(12, 1), (22, 1), (24, 1), (45, 1)] }, { coefficient := -1, powers := [(12, 1), (34, 1), (37, 1)] }, { coefficient := 1, powers := [(16, 1), (19, 1), (28, 1), (42, 1), (52, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1), (42, 1), (54, 1)] }, { coefficient := 1, powers := [(17, 1), (28, 1), (46, 1), (49, 1)] }]
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
    ¬ ∀ index : Fin 25,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component39.SelectedLeafB5_2_2_7.selectedHasNoCommonZero

end Krenn.Component39.SelectedLeafB5_2_2_7
