import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component14.SelectedLeafB6_2_3

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "ce26d76dfddb48c38a5fc6c5181dcd0f41166f300c608e4e65f67e576ae4566f"
def certificateSHA256 : String := "e4437e45a2d4b76b22c21bb25a992a00e377e86d8fe94a3e39888fd796ae5546"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 37 → Fin 643 := ![
  6,
  11,
  13,
  16,
  19,
  133,
  162,
  164,
  167,
  171,
  175,
  179,
  184,
  190,
  191,
  192,
  194,
  196,
  198,
  343,
  346,
  348,
  349,
  350,
  384,
  406,
  460,
  524,
  555,
  556,
  633,
  634,
  635,
  636,
  638,
  639,
  641
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 37 → SparsePoly (Fin 64) := ![
  [{ coefficient := 1, powers := [(5, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (23, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(15, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (48, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (46, 1)] }, { coefficient := 1, powers := [(11, 1), (25, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (52, 1)] }, { coefficient := 1, powers := [(15, 1), (19, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (48, 1)] }, { coefficient := 1, powers := [(12, 1), (27, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (58, 1)] }, { coefficient := 1, powers := [(42, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (27, 1)] }, { coefficient := 1, powers := [(15, 1), (21, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (44, 1)] }, { coefficient := 1, powers := [(12, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (27, 1)] }, { coefficient := -1, powers := [(21, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (42, 1)] }, { coefficient := 1, powers := [(27, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (50, 1)] }, { coefficient := 1, powers := [(22, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (51, 1)] }, { coefficient := 1, powers := [(28, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(28, 1), (39, 1)] }, { coefficient := 1, powers := [(28, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(40, 1), (42, 1)] }, { coefficient := 1, powers := [(46, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(44, 1), (48, 1)] }, { coefficient := 1, powers := [(48, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1)] }, { coefficient := 1, powers := [(18, 1), (42, 1)] }, { coefficient := 1, powers := [(23, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (45, 1)] }, { coefficient := 1, powers := [(11, 1), (25, 1), (45, 1)] }, { coefficient := 1, powers := [(15, 1), (19, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (46, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (52, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1)] }, { coefficient := 1, powers := [(12, 1), (28, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (58, 1)] }, { coefficient := 1, powers := [(12, 1), (46, 1)] }, { coefficient := 1, powers := [(16, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (40, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (54, 1)] }, { coefficient := 1, powers := [(12, 1), (22, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (22, 1), (57, 1)] }, { coefficient := 1, powers := [(22, 1)] }, { coefficient := 1, powers := [(27, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (52, 1)] }, { coefficient := 1, powers := [(28, 1), (40, 1)] }, { coefficient := 1, powers := [(28, 1), (45, 1), (48, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (42, 1), (51, 1)] }, { coefficient := 1, powers := [(22, 1), (55, 1)] }, { coefficient := 1, powers := [(28, 1), (46, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1)] }, { coefficient := 1, powers := [(6, 1), (57, 1)] }, { coefficient := 1, powers := [(23, 1), (39, 1)] }, { coefficient := 1, powers := [(23, 1), (44, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (50, 1)] }, { coefficient := 1, powers := [(3, 1), (57, 1)] }, { coefficient := 1, powers := [(17, 1), (50, 1)] }, { coefficient := 1, powers := [(17, 1), (54, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (37, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (40, 1), (55, 1)] }, { coefficient := 1, powers := [(2, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(5, 1), (28, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (52, 1)] }, { coefficient := 1, powers := [(8, 1), (22, 1), (58, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1), (46, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (40, 1)] }, { coefficient := 1, powers := [(12, 1), (22, 1), (55, 1)] }, { coefficient := 1, powers := [(12, 1), (28, 1), (46, 1)] }, { coefficient := 1, powers := [(12, 1), (34, 1), (37, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1), (52, 1)] }, { coefficient := 1, powers := [(16, 1), (28, 1), (40, 1)] }, { coefficient := 1, powers := [(16, 1), (31, 1), (37, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (59, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1), (60, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(39, 1), (61, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(40, 1)] }],
  [{ coefficient := 1, powers := [(54, 1), (62, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 37 → SparsePoly (Fin 64) := ![
  [{ coefficient := -1, powers := [(3, 1), (31, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (25, 1), (27, 1), (51, 1), (60, 1)] }, { coefficient := 1, powers := [(12, 1), (25, 1), (28, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(22, 1), (39, 1), (55, 1)] }, { coefficient := -1, powers := [(22, 1), (44, 1), (55, 1)] }, { coefficient := 1, powers := [(28, 1), (46, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (28, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (19, 1), (22, 1), (39, 1), (60, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (51, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (27, 1), (51, 1), (60, 1)] }, { coefficient := -1, powers := [(12, 1), (28, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(16, 1), (22, 1), (39, 1), (60, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(45, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (22, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (25, 1), (45, 1), (58, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (22, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (15, 1), (45, 1), (58, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (48, 1), (57, 1)] }, { coefficient := -1, powers := [(12, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (12, 1), (55, 1)] }, { coefficient := 1, powers := [(12, 1), (17, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (44, 1), (48, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(16, 1), (45, 1), (48, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (27, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [(16, 1), (22, 1), (51, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (28, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (27, 1), (58, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(52, 1)] }],
  [{ coefficient := 1, powers := [(46, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (28, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (55, 1), (57, 1), (62, 1)] }, { coefficient := 1, powers := [(55, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (58, 1)] }, { coefficient := -1, powers := [(12, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (39, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(12, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (22, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (22, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(5, 1), (28, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (27, 1), (45, 1), (58, 1)] }, { coefficient := -1, powers := [(12, 1), (27, 1), (46, 1), (51, 1)] }, { coefficient := 1, powers := [(12, 1), (28, 1), (46, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1), (39, 1), (52, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(37, 1), (58, 1)] }, { coefficient := -1, powers := [(45, 1), (48, 1), (55, 1)] }, { coefficient := -1, powers := [(46, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(16, 1), (31, 1), (37, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (16, 1), (28, 1), (59, 1)] }, { coefficient := -1, powers := [(2, 1), (3, 1), (54, 1), (55, 1), (57, 1), (62, 1)] }, { coefficient := -1, powers := [(2, 1), (54, 1), (55, 1), (62, 1)] }, { coefficient := 1, powers := [(2, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (27, 1), (42, 1), (57, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1)] }, { coefficient := -1, powers := [(16, 1), (28, 1), (39, 1), (61, 1)] }, { coefficient := 1, powers := [(16, 1), (28, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (5, 1), (31, 1), (55, 1), (57, 1)] }, { coefficient := -1, powers := [(3, 1), (12, 1), (22, 1), (55, 1), (57, 1)] }, { coefficient := -1, powers := [(5, 1), (31, 1), (55, 1)] }, { coefficient := -1, powers := [(12, 1), (22, 1), (55, 1)] }]
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
    ¬ ∀ index : Fin 37,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component14.SelectedLeafB6_2_3.selectedHasNoCommonZero

end Krenn.Component14.SelectedLeafB6_2_3
