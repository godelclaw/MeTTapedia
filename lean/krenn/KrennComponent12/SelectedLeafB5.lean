import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component12.SelectedLeafB5

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "04d7edf67b3ab91045fe0345c56fbb7d9a1585cb3231bb299f52d175537cde9d"
def certificateSHA256 : String := "5033eb41e08d9d0ed5b3fe2e6aa00070e8527375254803488e7bb3c1537fb049"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 26 → Fin 616 := ![
  5,
  7,
  8,
  11,
  12,
  16,
  18,
  44,
  198,
  209,
  211,
  218,
  227,
  292,
  309,
  338,
  339,
  340,
  350,
  352,
  464,
  489,
  565,
  612,
  613,
  615
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 26 → SparsePoly (Fin 61) := ![
  [{ coefficient := 1, powers := [(2, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(40, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (46, 1)] }, { coefficient := 1, powers := [(5, 1), (26, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (44, 1)] }, { coefficient := 1, powers := [(12, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (39, 1)] }, { coefficient := 1, powers := [(17, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(52, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (35, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (18, 1), (54, 1)] }, { coefficient := 1, powers := [(12, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (23, 1), (39, 1)] }, { coefficient := 1, powers := [(17, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (47, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (52, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1)] }, { coefficient := 1, powers := [(12, 1), (28, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (58, 1)] }, { coefficient := 1, powers := [(12, 1), (47, 1)] }, { coefficient := 1, powers := [(17, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (52, 1)] }, { coefficient := 1, powers := [(28, 1), (40, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (35, 1), (58, 1)] }, { coefficient := 1, powers := [(3, 1), (23, 1), (58, 1)] }, { coefficient := 1, powers := [(6, 1), (18, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (58, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (45, 1)] }, { coefficient := 1, powers := [(12, 1), (55, 1)] }, { coefficient := 1, powers := [(17, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (37, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (46, 1), (51, 1)] }, { coefficient := 1, powers := [(5, 1), (28, 1), (57, 1)] }, { coefficient := 1, powers := [(8, 1), (22, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (37, 1), (58, 1)] }, { coefficient := 1, powers := [(0, 1), (40, 1), (55, 1)] }, { coefficient := 1, powers := [(0, 1), (47, 1), (52, 1)] }, { coefficient := 1, powers := [(19, 1), (42, 1), (52, 1)] }, { coefficient := 1, powers := [(24, 1), (40, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (37, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (40, 1), (55, 1)] }, { coefficient := 1, powers := [(2, 1), (47, 1), (52, 1)] }, { coefficient := 1, powers := [(5, 1), (28, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (52, 1)] }, { coefficient := 1, powers := [(8, 1), (22, 1), (58, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1), (47, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (40, 1)] }, { coefficient := 1, powers := [(12, 1), (22, 1), (55, 1)] }, { coefficient := 1, powers := [(12, 1), (28, 1), (47, 1)] }, { coefficient := 1, powers := [(12, 1), (34, 1), (37, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (52, 1)] }, { coefficient := 1, powers := [(17, 1), (28, 1), (40, 1)] }, { coefficient := 1, powers := [(17, 1), (31, 1), (37, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (59, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (60, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 26 → SparsePoly (Fin 61) := ![
  [{ coefficient := -1, powers := [(0, 2), (2, 1), (35, 1), (47, 1), (52, 1), (57, 1), (59, 1), (60, 1)] }, { coefficient := -1, powers := [(0, 1), (2, 2), (35, 1), (47, 1), (52, 1), (57, 1), (60, 2)] }, { coefficient := -2, powers := [(0, 1), (2, 1), (17, 1), (22, 1), (35, 1), (52, 1), (57, 1), (60, 2)] }, { coefficient := -1, powers := [(0, 1), (2, 1), (19, 1), (35, 1), (42, 1), (52, 1), (57, 1), (59, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (12, 1), (18, 1), (28, 1), (35, 1), (47, 1), (57, 1), (60, 2)] }, { coefficient := -1, powers := [(2, 1), (12, 1), (18, 1), (34, 1), (35, 1), (37, 1), (57, 1), (60, 2)] }],
  [{ coefficient := 1, powers := [(2, 1), (17, 1), (23, 1), (28, 1), (35, 1), (40, 1), (57, 1), (60, 2)] }],
  [{ coefficient := -1, powers := [(2, 1), (23, 1), (37, 1), (57, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (26, 1), (35, 1), (51, 1), (58, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (28, 1), (35, 1), (58, 1), (60, 1)] }, { coefficient := -1, powers := [(2, 1), (31, 1), (35, 1), (55, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (18, 1), (37, 1), (57, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (22, 1), (35, 1), (58, 1), (60, 1)] }, { coefficient := -1, powers := [(2, 1), (34, 1), (35, 1), (40, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (22, 1), (35, 1), (45, 1), (57, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (24, 1), (35, 1), (57, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (35, 1), (51, 1), (58, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (18, 1), (28, 1), (35, 1), (47, 1), (57, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (18, 1), (34, 1), (35, 1), (37, 1), (57, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (23, 1), (28, 1), (35, 1), (40, 1), (57, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (2, 1), (35, 1), (47, 1), (57, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 2), (35, 1), (47, 1), (57, 1), (60, 1)] }, { coefficient := 2, powers := [(2, 1), (17, 1), (22, 1), (35, 1), (57, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (19, 1), (35, 1), (42, 1), (57, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (60, 2)] }],
  [{ coefficient := 1, powers := [(2, 1), (28, 1), (35, 1), (47, 1), (57, 1), (60, 1)] }, { coefficient := -1, powers := [(2, 1), (34, 1), (35, 1), (37, 1), (57, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (28, 1), (35, 1), (40, 1), (57, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (35, 1), (52, 1), (57, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (35, 1), (47, 1), (57, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (28, 1), (35, 1), (57, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (17, 1), (35, 1), (57, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (37, 1), (57, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (22, 1), (35, 1), (57, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (35, 1), (58, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (35, 1), (57, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (35, 1), (57, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (35, 1), (40, 1), (55, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(0, 2), (2, 1), (35, 1), (44, 1), (47, 1), (52, 1), (57, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (2, 2), (35, 1), (44, 1), (47, 1), (52, 1), (57, 1), (60, 1)] }, { coefficient := 2, powers := [(0, 1), (2, 1), (17, 1), (22, 1), (35, 1), (44, 1), (52, 1), (57, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (2, 1), (19, 1), (35, 1), (42, 1), (44, 1), (52, 1), (57, 1), (59, 1)] }, { coefficient := -1, powers := [(2, 1), (12, 1), (18, 1), (28, 1), (35, 1), (44, 1), (47, 1), (57, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (12, 1), (18, 1), (34, 1), (35, 1), (37, 1), (44, 1), (57, 1), (60, 1)] }, { coefficient := -1, powers := [(2, 1), (17, 1), (23, 1), (28, 1), (35, 1), (40, 1), (50, 1), (57, 1), (60, 1)] }, { coefficient := -1, powers := [(2, 1), (35, 1), (40, 1), (55, 1), (57, 1)] }, { coefficient := -1, powers := [(2, 1), (35, 1), (57, 1), (60, 1)] }, { coefficient := -1, powers := [(2, 1), (60, 1)] }, { coefficient := -1, powers := [] }]
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
    (values : Fin 61 → R) :
    ¬ ∀ index : Fin 26,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component12.SelectedLeafB5.selectedHasNoCommonZero

end Krenn.Component12.SelectedLeafB5
