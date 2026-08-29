import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component39.SelectedLeafB6_3

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "de9c7f3c931dc837676061af20127ee7c5e6a9772b63bcf9a6b79c6827879a4c"
def certificateSHA256 : String := "f9fff2115b979a21e4928c78a744b945eeda07b37409f6e9834c192bfb9e7a06"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 27 → Fin 667 := ![
  1,
  3,
  4,
  6,
  7,
  8,
  9,
  184,
  193,
  317,
  318,
  430,
  434,
  440,
  472,
  475,
  566,
  567,
  570,
  608,
  650,
  651,
  660,
  662,
  663,
  665,
  666
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 27 → SparsePoly (Fin 65) := ![
  [{ coefficient := 1, powers := [(1, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (45, 1)] }, { coefficient := 1, powers := [(17, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (53, 1)] }, { coefficient := 1, powers := [(28, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (51, 1)] }, { coefficient := 1, powers := [(22, 1), (56, 1)] }, { coefficient := 1, powers := [(27, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (53, 1)] }, { coefficient := 1, powers := [(28, 1), (39, 1)] }, { coefficient := 1, powers := [(28, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (60, 1)] }, { coefficient := 1, powers := [(12, 1), (47, 1)] }, { coefficient := 1, powers := [(17, 1), (19, 1), (52, 1)] }, { coefficient := 1, powers := [(17, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (60, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (45, 1)] }, { coefficient := 1, powers := [(12, 1), (57, 1)] }, { coefficient := 1, powers := [(17, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (54, 1)] }, { coefficient := 1, powers := [(28, 1), (40, 1)] }, { coefficient := 1, powers := [(28, 1), (46, 1), (49, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (35, 1), (59, 1)] }, { coefficient := 1, powers := [(1, 1)] }, { coefficient := 1, powers := [(10, 1), (33, 1), (35, 1)] }, { coefficient := 1, powers := [(14, 1), (30, 1), (35, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (37, 1), (59, 1)] }, { coefficient := 1, powers := [(1, 1), (46, 1), (53, 1)] }, { coefficient := 1, powers := [(10, 1), (33, 1), (37, 1)] }, { coefficient := 1, powers := [(14, 1), (30, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (42, 1), (53, 1)] }, { coefficient := 1, powers := [(22, 1), (57, 1)] }, { coefficient := 1, powers := [(28, 1), (47, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (49, 1), (56, 1)] }, { coefficient := 1, powers := [(22, 1), (52, 1)] }, { coefficient := 1, powers := [(27, 1), (40, 1)] }, { coefficient := 1, powers := [(27, 1), (46, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (42, 1), (53, 1)] }, { coefficient := 1, powers := [(27, 1), (57, 1)] }, { coefficient := 1, powers := [(28, 1), (39, 1), (42, 1)] }, { coefficient := 1, powers := [(28, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (40, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(19, 1), (49, 1), (56, 1)] }, { coefficient := 1, powers := [(19, 1), (52, 1)] }, { coefficient := 1, powers := [(40, 1)] }, { coefficient := 1, powers := [(46, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (39, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (45, 1), (53, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (39, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1), (57, 1)] }, { coefficient := 1, powers := [(16, 1), (28, 1), (45, 1)] }, { coefficient := 1, powers := [(17, 1), (27, 1), (53, 1)] }, { coefficient := 1, powers := [(17, 1), (28, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (40, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (56, 1)] }, { coefficient := 1, powers := [(12, 1), (22, 1), (56, 1)] }, { coefficient := 1, powers := [(12, 1), (27, 1), (46, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1), (52, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (37, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (47, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (28, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (22, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1), (47, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (40, 1)] }, { coefficient := 1, powers := [(12, 1), (22, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1), (28, 1), (47, 1)] }, { coefficient := 1, powers := [(12, 1), (34, 1), (37, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (54, 1)] }, { coefficient := 1, powers := [(17, 1), (28, 1), (40, 1)] }, { coefficient := 1, powers := [(17, 1), (31, 1), (37, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(39, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(40, 1), (64, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 27 → SparsePoly (Fin 65) := ![
  [{ coefficient := -1, powers := [(12, 1), (28, 1), (46, 1), (62, 1)] }, { coefficient := -1, powers := [(16, 1), (28, 1), (40, 1), (44, 1), (62, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (12, 1), (27, 1), (57, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (31, 1), (62, 1)] }, { coefficient := 1, powers := [(12, 1), (28, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (16, 1), (22, 1), (51, 1), (57, 1), (62, 1)] }, { coefficient := -1, powers := [(5, 1), (19, 1), (31, 1), (56, 1), (57, 1), (62, 1), (64, 1)] }, { coefficient := -1, powers := [(5, 1), (31, 1), (46, 1), (57, 1), (62, 1), (64, 1)] }, { coefficient := -1, powers := [(12, 1), (19, 1), (22, 1), (56, 1), (57, 1), (62, 1), (64, 1)] }, { coefficient := -1, powers := [(12, 1), (22, 1), (46, 1), (57, 1), (62, 1), (64, 1)] }, { coefficient := 1, powers := [(17, 1), (28, 1), (46, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (5, 1), (31, 1), (46, 1), (57, 1), (62, 1), (64, 1)] }, { coefficient := -1, powers := [(0, 1), (12, 1), (22, 1), (46, 1), (57, 1), (62, 1), (64, 1)] }, { coefficient := -1, powers := [(5, 1), (19, 1), (31, 1), (57, 1), (62, 1), (64, 1)] }, { coefficient := -1, powers := [(12, 1), (19, 1), (22, 1), (57, 1), (62, 1), (64, 1)] }, { coefficient := -1, powers := [(17, 1), (19, 1), (28, 1), (62, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (24, 1), (62, 1)] }],
  [{ coefficient := 2, powers := [(12, 1), (34, 1), (35, 1), (46, 1), (62, 1)] }, { coefficient := -1, powers := [(17, 1), (27, 1), (40, 1), (62, 1), (63, 1)] }, { coefficient := 2, powers := [(17, 1), (31, 1), (35, 1), (46, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (34, 1), (62, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(22, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (42, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (16, 1), (49, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (40, 1), (42, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(28, 1)] }],
  [{ coefficient := 1, powers := [(22, 1)] }],
  [{ coefficient := -1, powers := [(17, 1)] }],
  [{ coefficient := 2, powers := [(12, 1), (34, 1), (37, 1), (62, 1)] }, { coefficient := 2, powers := [(17, 1), (31, 1), (37, 1), (62, 1)] }],
  [{ coefficient := -2, powers := [(12, 1), (34, 1), (35, 1), (62, 1)] }, { coefficient := -2, powers := [(17, 1), (31, 1), (35, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(12, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (16, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [(16, 1), (40, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (31, 1), (57, 1), (64, 1)] }, { coefficient := 1, powers := [(12, 1), (22, 1), (57, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(40, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (5, 1), (31, 1), (46, 1), (52, 1), (57, 1), (64, 1)] }, { coefficient := 1, powers := [(0, 1), (12, 1), (22, 1), (46, 1), (52, 1), (57, 1), (64, 1)] }, { coefficient := -1, powers := [(0, 1), (12, 1), (27, 1), (46, 1), (57, 1)] }, { coefficient := -1, powers := [(0, 1), (16, 1), (22, 1), (49, 1), (51, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (19, 1), (31, 1), (49, 1), (56, 1), (57, 1), (64, 1)] }, { coefficient := 1, powers := [(5, 1), (19, 1), (31, 1), (52, 1), (57, 1), (64, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (46, 1), (49, 1), (57, 1), (64, 1)] }, { coefficient := -1, powers := [(5, 1), (34, 1), (54, 1)] }, { coefficient := -1, powers := [(8, 1), (31, 1), (47, 1)] }, { coefficient := 1, powers := [(12, 1), (19, 1), (22, 1), (49, 1), (56, 1), (57, 1), (64, 1)] }, { coefficient := 1, powers := [(12, 1), (19, 1), (22, 1), (52, 1), (57, 1), (64, 1)] }, { coefficient := 1, powers := [(12, 1), (22, 1), (46, 1), (49, 1), (57, 1), (64, 1)] }, { coefficient := 1, powers := [(12, 1), (28, 1), (42, 1), (46, 1)] }, { coefficient := -1, powers := [(12, 1), (28, 1), (47, 1)] }, { coefficient := -2, powers := [(12, 1), (34, 1), (37, 1)] }, { coefficient := 1, powers := [(16, 1), (28, 1), (40, 1), (42, 1), (44, 1), (63, 1)] }, { coefficient := 1, powers := [(17, 1), (19, 1), (28, 1), (52, 1)] }, { coefficient := -1, powers := [(17, 1), (22, 1), (24, 1), (52, 1)] }, { coefficient := -1, powers := [(17, 1), (22, 1), (54, 1)] }, { coefficient := 1, powers := [(17, 1), (27, 1), (40, 1), (53, 1), (63, 1)] }, { coefficient := -1, powers := [(17, 1), (28, 1), (46, 1), (49, 1)] }, { coefficient := -2, powers := [(17, 1), (31, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (40, 1), (56, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (46, 1), (52, 1), (57, 1)] }, { coefficient := 1, powers := [(37, 1), (60, 1)] }, { coefficient := -1, powers := [(39, 1), (40, 1), (57, 1), (63, 1)] }, { coefficient := -1, powers := [(40, 1), (45, 1), (53, 1), (63, 1)] }, { coefficient := 1, powers := [(40, 1), (57, 1)] }, { coefficient := 1, powers := [(47, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (34, 1), (40, 1)] }, { coefficient := -1, powers := [(17, 1), (28, 1), (40, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (5, 1), (31, 1), (56, 1), (57, 1)] }, { coefficient := -1, powers := [(0, 1), (12, 1), (22, 1), (56, 1), (57, 1)] }, { coefficient := -1, powers := [(5, 1), (31, 1), (57, 1)] }, { coefficient := -1, powers := [(12, 1), (22, 1), (57, 1)] }]
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
    ¬ ∀ index : Fin 27,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component39.SelectedLeafB6_3.selectedHasNoCommonZero

end Krenn.Component39.SelectedLeafB6_3
