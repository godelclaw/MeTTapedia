import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component14.SelectedLeafB4_7

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "1a26e7db597181ce0bc581c783d1700a1cd696ef30657a1310125000fc65de6c"
def certificateSHA256 : String := "e00a24d9223de7c6a04e666bacdfc96eea321f527aa0eeb78ba07bd9816cd7e1"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 33 → Fin 640 := ![
  13,
  16,
  20,
  132,
  133,
  179,
  191,
  192,
  194,
  195,
  198,
  282,
  309,
  342,
  343,
  348,
  349,
  350,
  351,
  362,
  383,
  384,
  460,
  465,
  470,
  476,
  524,
  633,
  634,
  636,
  637,
  638,
  639
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 33 → SparsePoly (Fin 63) := ![
  [{ coefficient := 1, powers := [(12, 1), (23, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (17, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (42, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (48, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (44, 1)] }, { coefficient := 1, powers := [(12, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (50, 1)] }, { coefficient := 1, powers := [(22, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (51, 1)] }, { coefficient := 1, powers := [(28, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(28, 1), (39, 1)] }, { coefficient := 1, powers := [(28, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(39, 1), (42, 1)] }, { coefficient := 1, powers := [(42, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(44, 1), (48, 1)] }, { coefficient := 1, powers := [(48, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (17, 1), (54, 1)] }, { coefficient := 1, powers := [(12, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (17, 1), (49, 1)] }, { coefficient := 1, powers := [(16, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1)] }, { coefficient := 1, powers := [(17, 1), (42, 1)] }, { coefficient := 1, powers := [(23, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1)] }, { coefficient := 1, powers := [(18, 1), (42, 1)] }, { coefficient := 1, powers := [(23, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (46, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (52, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1)] }, { coefficient := 1, powers := [(12, 1), (28, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (58, 1)] }, { coefficient := 1, powers := [(12, 1), (46, 1)] }, { coefficient := 1, powers := [(16, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (58, 1)] }, { coefficient := 1, powers := [(12, 1), (55, 1)] }, { coefficient := 1, powers := [(16, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1), (48, 1)] }, { coefficient := 1, powers := [(23, 1), (44, 1), (48, 1)] }, { coefficient := 1, powers := [(48, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (39, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (39, 1)] }, { coefficient := 1, powers := [(16, 1), (28, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (40, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (54, 1)] }, { coefficient := 1, powers := [(12, 1), (22, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (52, 1)] }, { coefficient := 1, powers := [(28, 1), (40, 1)] }, { coefficient := 1, powers := [(28, 1), (45, 1), (48, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (40, 1), (54, 1)] }, { coefficient := 1, powers := [(18, 1), (48, 1), (54, 1)] }, { coefficient := 1, powers := [(40, 1)] }, { coefficient := 1, powers := [(45, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1), (51, 1)] }, { coefficient := 1, powers := [(17, 1), (42, 1), (51, 1)] }, { coefficient := 1, powers := [(17, 1), (55, 1)] }, { coefficient := 1, powers := [(24, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1), (48, 1)] }, { coefficient := 1, powers := [(18, 1), (48, 1)] }, { coefficient := 1, powers := [(23, 1), (40, 1)] }, { coefficient := 1, powers := [(23, 1), (45, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (42, 1), (51, 1)] }, { coefficient := 1, powers := [(22, 1), (55, 1)] }, { coefficient := 1, powers := [(28, 1), (46, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (37, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (40, 1), (55, 1)] }, { coefficient := 1, powers := [(2, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(5, 1), (28, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (52, 1)] }, { coefficient := 1, powers := [(8, 1), (22, 1), (58, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1), (46, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (40, 1)] }, { coefficient := 1, powers := [(12, 1), (22, 1), (55, 1)] }, { coefficient := 1, powers := [(12, 1), (28, 1), (46, 1)] }, { coefficient := 1, powers := [(12, 1), (34, 1), (37, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1), (52, 1)] }, { coefficient := 1, powers := [(16, 1), (28, 1), (40, 1)] }, { coefficient := 1, powers := [(16, 1), (31, 1), (37, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (59, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(38, 1), (60, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(39, 1), (61, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(40, 1), (62, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 33 → SparsePoly (Fin 63) := ![
  [{ coefficient := 4, powers := [(0, 1), (28, 1), (44, 1), (46, 1), (59, 1)] }],
  [{ coefficient := 4, powers := [(0, 1), (18, 1), (28, 1), (44, 1), (59, 1)] }, { coefficient := -4, powers := [(0, 1), (22, 1), (23, 1), (44, 1), (50, 1), (51, 1)] }, { coefficient := 4, powers := [(0, 1), (22, 1), (24, 1), (44, 1), (50, 1)] }],
  [{ coefficient := 4, powers := [(0, 1), (22, 1), (49, 1), (50, 1), (52, 1), (60, 1)] }, { coefficient := -4, powers := [(0, 1), (28, 1), (40, 1), (49, 1), (54, 1), (60, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (12, 1), (51, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (16, 1), (51, 1)] }],
  [{ coefficient := 4, powers := [(0, 1), (17, 1), (22, 1), (50, 1), (55, 1)] }, { coefficient := -2, powers := [(0, 1), (22, 1), (55, 1)] }, { coefficient := 2, powers := [(0, 1), (28, 1), (46, 1)] }, { coefficient := -2, powers := [(0, 1), (34, 1), (37, 1)] }],
  [{ coefficient := 4, powers := [(0, 1), (12, 1), (55, 1)] }, { coefficient := 4, powers := [(0, 1), (16, 1), (52, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (12, 1), (39, 1), (42, 1)] }, { coefficient := -2, powers := [(0, 1), (12, 1), (42, 1), (44, 1)] }, { coefficient := 2, powers := [(0, 1), (16, 1), (48, 1), (54, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (12, 1), (42, 1), (45, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (12, 1), (22, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(0, 2), (45, 1), (59, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 1), (18, 1), (23, 1), (59, 2), (62, 1)] }, { coefficient := -1, powers := [(0, 1), (18, 1), (59, 1), (62, 1)] }, { coefficient := 1, powers := [(0, 1), (23, 1), (45, 1), (59, 1), (62, 1)] }],
  [{ coefficient := -4, powers := [(0, 1), (22, 1), (50, 1), (55, 1)] }],
  [{ coefficient := -4, powers := [(0, 1), (22, 1), (50, 1), (52, 1), (60, 1)] }, { coefficient := 4, powers := [(0, 1), (28, 1), (40, 1), (54, 1), (60, 1)] }],
  [{ coefficient := 4, powers := [(0, 1), (12, 1), (22, 1), (44, 1), (50, 1), (51, 1)] }],
  [{ coefficient := -4, powers := [(0, 1), (12, 1), (28, 1), (44, 1), (59, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (52, 1), (54, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (46, 1), (54, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (28, 1), (54, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (22, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (18, 1), (59, 2), (62, 1)] }, { coefficient := -1, powers := [(0, 1), (45, 1), (59, 1), (62, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (40, 1), (54, 1), (61, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (55, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (16, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (23, 1), (59, 2), (62, 1)] }, { coefficient := 2, powers := [(0, 1), (59, 1), (62, 1)] }],
  [{ coefficient := -4, powers := [(0, 1), (12, 1), (22, 1), (44, 1), (50, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (54, 1), (59, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 1), (59, 2), (62, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (12, 1), (44, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (54, 1)] }],
  [{ coefficient := 4, powers := [(0, 1), (12, 1), (28, 1), (44, 1), (46, 1)] }, { coefficient := -1, powers := [(0, 1), (18, 1), (44, 1), (48, 1), (59, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 1), (23, 1), (40, 1), (54, 1), (59, 1), (62, 1)] }, { coefficient := 1, powers := [(0, 1), (45, 1), (48, 1), (59, 1), (62, 1)] }, { coefficient := -2, powers := [(0, 1), (54, 1)] }, { coefficient := -2, powers := [] }],
  [{ coefficient := -2, powers := [(0, 1), (37, 1), (54, 1), (58, 1)] }, { coefficient := 2, powers := [(0, 1), (39, 1), (40, 1), (54, 1), (55, 1), (61, 1)] }, { coefficient := 2, powers := [(0, 1), (46, 1), (52, 1), (54, 1)] }],
  [{ coefficient := 4, powers := [(0, 1), (16, 1), (22, 1), (50, 1), (52, 1)] }, { coefficient := -4, powers := [(0, 1), (16, 1), (28, 1), (40, 1), (54, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (8, 1), (34, 1), (40, 1), (54, 1)] }, { coefficient := 2, powers := [(0, 1), (16, 1), (28, 1), (40, 1), (54, 1)] }],
  [{ coefficient := -2, powers := [(0, 2), (54, 1), (59, 1)] }, { coefficient := -2, powers := [(0, 1), (59, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
/-- Lean replays the exact selected-row integer certificate. -/
theorem constantIdentity :
    ∑ index, (multipliers index).toPoly *
      (selectedEquations index).toPoly = C (2 : ℤ) := by
  simp (config := { maxSteps := 1000000 })
    [Fin.sum_univ_succ, multipliers, selectedEquations,
    SparsePoly.toPoly, SparseTerm.toPoly]
  ring

/-- The selected rows have no common zero in a characteristic-zero ring. -/
theorem selectedHasNoCommonZero {R : Type*} [CommRing R] [Nontrivial R] [CharZero R]
    (values : Fin 63 → R) :
    ¬ ∀ index : Fin 33,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((2 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (2 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (2 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component14.SelectedLeafB4_7.selectedHasNoCommonZero

end Krenn.Component14.SelectedLeafB4_7
