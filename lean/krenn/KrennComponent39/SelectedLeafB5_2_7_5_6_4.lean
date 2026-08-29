import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component39.SelectedLeafB5_2_7_5_6_4

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "b31bb6343b9d8ad2ac3a1d08874195adc7119944f3616c2b5d936f5003dc75c5"
def certificateSHA256 : String := "b16aa2f5a532a27c15ab785a1be2a19255f21a44b53b0d81dba4d51536ddb8b7"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 31 → Fin 679 := ![
  11,
  14,
  19,
  20,
  26,
  27,
  64,
  192,
  193,
  201,
  232,
  280,
  304,
  305,
  440,
  470,
  471,
  542,
  566,
  603,
  621,
  659,
  660,
  662,
  666,
  669,
  671,
  675,
  676,
  677,
  678
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 31 → SparsePoly (Fin 72) := ![
  [{ coefficient := 1, powers := [(8, 1), (30, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (33, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (42, 1)] }, { coefficient := 1, powers := [(26, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (53, 1)] }, { coefficient := 1, powers := [(28, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (33, 1), (52, 1)] }, { coefficient := 1, powers := [(25, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (24, 1), (45, 1)] }, { coefficient := 1, powers := [(10, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (42, 1), (53, 1)] }, { coefficient := 1, powers := [(20, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (44, 1)] }, { coefficient := 1, powers := [(4, 1), (33, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (51, 1)] }, { coefficient := 1, powers := [(7, 1), (30, 1)] }, { coefficient := 1, powers := [(10, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (54, 1)] }, { coefficient := 1, powers := [(28, 1), (40, 1)] }, { coefficient := 1, powers := [(28, 1), (46, 1), (49, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1), (52, 1)] }, { coefficient := 1, powers := [(19, 1), (42, 1), (52, 1)] }, { coefficient := 1, powers := [(40, 1), (42, 1)] }, { coefficient := 1, powers := [(47, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1), (53, 1)] }, { coefficient := 1, powers := [(19, 1), (42, 1), (53, 1)] }, { coefficient := 1, powers := [(19, 1), (57, 1)] }, { coefficient := 1, powers := [(24, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (20, 1), (59, 1)] }, { coefficient := 1, powers := [(8, 1), (30, 1), (44, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (39, 1)] }, { coefficient := 1, powers := [(16, 1), (20, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (42, 1), (53, 1)] }, { coefficient := 1, powers := [(22, 1), (57, 1)] }, { coefficient := 1, powers := [(28, 1), (47, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (51, 1)] }, { coefficient := 1, powers := [(20, 1), (56, 1)] }, { coefficient := 1, powers := [(25, 1), (39, 1)] }, { coefficient := 1, powers := [(25, 1), (44, 1)] }, { coefficient := 1, powers := [(30, 1), (36, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (47, 1), (49, 1)] }, { coefficient := 1, powers := [(5, 1), (26, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (49, 1)] }, { coefficient := 1, powers := [(12, 1), (26, 1), (47, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (49, 1)] }, { coefficient := 1, powers := [(17, 1), (26, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (36, 1), (59, 1)] }, { coefficient := 1, powers := [(1, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(1, 1), (44, 1), (51, 1)] }, { coefficient := 1, powers := [(4, 1), (25, 1), (59, 1)] }, { coefficient := 1, powers := [(4, 1), (30, 1), (56, 1)] }, { coefficient := 1, powers := [(4, 1), (33, 1), (51, 1)] }, { coefficient := 1, powers := [(7, 1), (20, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (30, 1), (44, 1)] }, { coefficient := 1, powers := [(7, 1), (33, 1), (39, 1)] }, { coefficient := 1, powers := [(10, 1), (20, 1), (56, 1)] }, { coefficient := 1, powers := [(10, 1), (25, 1), (44, 1)] }, { coefficient := 1, powers := [(10, 1), (33, 1), (36, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1), (51, 1)] }, { coefficient := 1, powers := [(14, 1), (25, 1), (39, 1)] }, { coefficient := 1, powers := [(14, 1), (30, 1), (36, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (37, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (47, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (28, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (22, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1), (47, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (40, 1)] }, { coefficient := 1, powers := [(12, 1), (22, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1), (28, 1), (47, 1)] }, { coefficient := 1, powers := [(12, 1), (34, 1), (37, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (54, 1)] }, { coefficient := 1, powers := [(17, 1), (28, 1), (40, 1)] }, { coefficient := 1, powers := [(17, 1), (31, 1), (37, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1)] }],
  [{ coefficient := 1, powers := [(40, 1)] }],
  [{ coefficient := 1, powers := [(57, 1), (66, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(25, 1)] }],
  [{ coefficient := 1, powers := [(60, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (71, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(4, 1)] }],
  [{ coefficient := 1, powers := [(5, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 31 → SparsePoly (Fin 72) := ![
  [{ coefficient := -1, powers := [(7, 1), (31, 1), (44, 1), (47, 1)] }, { coefficient := -1, powers := [(10, 1), (31, 1), (36, 1), (47, 1)] }, { coefficient := 1, powers := [(14, 1), (31, 1), (36, 1), (47, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (19, 1), (20, 1), (24, 1), (51, 1), (52, 1), (57, 1), (66, 1)] }, { coefficient := -1, powers := [(2, 1), (19, 1), (24, 1), (30, 1), (36, 1), (52, 1), (57, 1), (66, 1)] }, { coefficient := -1, powers := [(2, 1), (20, 1), (24, 2), (47, 1), (51, 1), (52, 1), (66, 1)] }, { coefficient := -1, powers := [(2, 1), (24, 2), (30, 1), (36, 1), (47, 1), (52, 1), (66, 1)] }, { coefficient := 1, powers := [(2, 1), (24, 1), (30, 1), (36, 1), (47, 1), (54, 1), (66, 1)] }, { coefficient := 1, powers := [(8, 1), (20, 1), (24, 1), (31, 1), (47, 1), (51, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (19, 1), (30, 1), (36, 1), (57, 1)] }, { coefficient := -1, powers := [(2, 1), (24, 1), (30, 1), (36, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (30, 1), (36, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (7, 1), (19, 1), (42, 1), (52, 1), (57, 1), (59, 1), (66, 1)] }, { coefficient := 1, powers := [(2, 1), (7, 1), (24, 1), (42, 1), (47, 1), (52, 1), (59, 1), (66, 1)] }, { coefficient := -1, powers := [(7, 1), (16, 1), (31, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (7, 1), (47, 1), (59, 1)] }, { coefficient := -1, powers := [(2, 1), (10, 1), (47, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (7, 1), (39, 1), (47, 1), (71, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(17, 1), (49, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (7, 1), (19, 1), (39, 1), (57, 1), (71, 1)] }, { coefficient := -1, powers := [(2, 1), (7, 1), (24, 1), (39, 1), (47, 1), (71, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (19, 1), (20, 1), (51, 1), (52, 1), (57, 1), (66, 1)] }, { coefficient := 1, powers := [(2, 1), (19, 1), (30, 1), (36, 1), (52, 1), (57, 1), (66, 1)] }, { coefficient := 1, powers := [(2, 1), (20, 1), (24, 1), (47, 1), (51, 1), (52, 1), (66, 1)] }, { coefficient := 1, powers := [(2, 1), (24, 1), (30, 1), (36, 1), (47, 1), (52, 1), (66, 1)] }, { coefficient := -1, powers := [(2, 1), (30, 1), (36, 1), (47, 1), (54, 1), (66, 1)] }, { coefficient := -1, powers := [(8, 1), (20, 1), (31, 1), (47, 1), (51, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (7, 1), (19, 1), (52, 1), (57, 1), (59, 1), (66, 1)] }, { coefficient := -1, powers := [(2, 1), (7, 1), (24, 1), (47, 1), (52, 1), (59, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (19, 1), (51, 1), (52, 1), (57, 1)] }, { coefficient := -1, powers := [(2, 1), (24, 1), (47, 1), (51, 1), (52, 1)] }, { coefficient := 1, powers := [(2, 1), (47, 1), (51, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1), (47, 1), (51, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (19, 1), (44, 1), (52, 1), (57, 1)] }, { coefficient := -1, powers := [(2, 1), (24, 1), (44, 1), (47, 1), (52, 1)] }, { coefficient := 1, powers := [(2, 1), (44, 1), (47, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1), (44, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(17, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (31, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(12, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (10, 1), (19, 1), (52, 1), (57, 1)] }, { coefficient := -1, powers := [(2, 1), (10, 1), (24, 1), (47, 1), (52, 1)] }, { coefficient := 1, powers := [(2, 1), (10, 1), (47, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (10, 1), (31, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(53, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (19, 1), (52, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (24, 1), (47, 1), (52, 1)] }, { coefficient := -1, powers := [(2, 1), (47, 1), (54, 1)] }, { coefficient := -1, powers := [(8, 1), (31, 1), (47, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(2, 1), (19, 1), (36, 1), (52, 1), (57, 1), (59, 1)] }, { coefficient := -1, powers := [(2, 1), (19, 1), (39, 1), (52, 1), (56, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (19, 1), (44, 1), (51, 1), (52, 1), (57, 1)] }, { coefficient := -1, powers := [(2, 1), (24, 1), (36, 1), (47, 1), (52, 1), (59, 1)] }, { coefficient := -1, powers := [(2, 1), (24, 1), (39, 1), (47, 1), (52, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (24, 1), (44, 1), (47, 1), (51, 1), (52, 1)] }, { coefficient := 1, powers := [(2, 1), (36, 1), (47, 1), (54, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (39, 1), (47, 1), (54, 1), (56, 1)] }, { coefficient := -1, powers := [(2, 1), (44, 1), (47, 1), (51, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1), (36, 1), (47, 1), (59, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1), (39, 1), (47, 1), (56, 1)] }, { coefficient := -1, powers := [(8, 1), (31, 1), (44, 1), (47, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (42, 1), (53, 1)] }, { coefficient := 1, powers := [(2, 1), (57, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1)] }, { coefficient := -1, powers := [(17, 1), (26, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (7, 1), (19, 1), (20, 1), (52, 1), (57, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (7, 1), (20, 1), (24, 1), (47, 1), (52, 1), (59, 1)] }, { coefficient := -1, powers := [(2, 1), (10, 1), (19, 1), (20, 1), (51, 1), (52, 1), (57, 1)] }, { coefficient := -1, powers := [(2, 1), (10, 1), (19, 1), (30, 1), (36, 1), (52, 1), (57, 1)] }, { coefficient := -1, powers := [(2, 1), (10, 1), (20, 1), (24, 1), (47, 1), (51, 1), (52, 1)] }, { coefficient := -1, powers := [(2, 1), (10, 1), (24, 1), (30, 1), (36, 1), (47, 1), (52, 1)] }, { coefficient := 1, powers := [(2, 1), (10, 1), (30, 1), (36, 1), (47, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (10, 1), (20, 1), (31, 1), (47, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (7, 1), (19, 1), (39, 1), (49, 1), (57, 1), (71, 1)] }, { coefficient := 1, powers := [(2, 1), (7, 1), (24, 1), (39, 1), (47, 1), (49, 1), (71, 1)] }, { coefficient := 1, powers := [(2, 1), (10, 1), (19, 1), (39, 1), (52, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (10, 1), (19, 1), (44, 1), (52, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (10, 1), (24, 1), (39, 1), (47, 1), (52, 1)] }, { coefficient := 1, powers := [(2, 1), (10, 1), (24, 1), (44, 1), (47, 1), (52, 1)] }, { coefficient := -1, powers := [(2, 1), (10, 1), (39, 1), (47, 1), (54, 1)] }, { coefficient := -1, powers := [(2, 1), (10, 1), (44, 1), (47, 1), (54, 1)] }, { coefficient := -1, powers := [(2, 1), (14, 1), (19, 1), (39, 1), (52, 1), (57, 1)] }, { coefficient := -1, powers := [(2, 1), (14, 1), (24, 1), (39, 1), (47, 1), (52, 1)] }, { coefficient := 1, powers := [(2, 1), (14, 1), (39, 1), (47, 1), (54, 1)] }, { coefficient := -1, powers := [(8, 1), (10, 1), (31, 1), (39, 1), (47, 1)] }, { coefficient := -1, powers := [(8, 1), (10, 1), (31, 1), (44, 1), (47, 1)] }, { coefficient := 1, powers := [(8, 1), (14, 1), (31, 1), (39, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (37, 1)] }, { coefficient := 1, powers := [(8, 1), (22, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (7, 1), (19, 1), (33, 1), (39, 1), (52, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (7, 1), (24, 1), (33, 1), (39, 1), (47, 1), (52, 1)] }, { coefficient := -1, powers := [(2, 1), (7, 1), (33, 1), (39, 1), (47, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (19, 1), (25, 1), (52, 1), (57, 1), (59, 1)] }, { coefficient := -1, powers := [(2, 1), (19, 1), (30, 1), (52, 1), (56, 1), (57, 1)] }, { coefficient := -1, powers := [(2, 1), (24, 1), (25, 1), (47, 1), (52, 1), (59, 1)] }, { coefficient := -1, powers := [(2, 1), (24, 1), (30, 1), (47, 1), (52, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (25, 1), (47, 1), (54, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (30, 1), (47, 1), (54, 1), (56, 1)] }, { coefficient := 1, powers := [(8, 1), (25, 1), (31, 1), (47, 1), (59, 1)] }, { coefficient := 1, powers := [(8, 1), (30, 1), (31, 1), (47, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [(26, 1), (53, 1), (60, 1)] }, { coefficient := 1, powers := [(28, 1), (60, 1)] }, { coefficient := 1, powers := [(31, 1), (57, 1)] }, { coefficient := -1, powers := [(34, 1), (49, 1), (53, 1)] }, { coefficient := 1, powers := [(34, 1), (54, 1)] }]
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
    (values : Fin 72 → R) :
    ¬ ∀ index : Fin 31,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component39.SelectedLeafB5_2_7_5_6_4.selectedHasNoCommonZero

end Krenn.Component39.SelectedLeafB5_2_7_5_6_4
