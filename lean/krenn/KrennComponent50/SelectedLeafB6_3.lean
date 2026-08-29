import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component50.SelectedLeafB6_3

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "b737734cfd3efe2a78a60a448b3d6e95913592c8e541096ae523595e3cde5338"
def certificateSHA256 : String := "a1d8a6cce6deca9687c5ecd26debe278b1a58865980aea27013a7397ef630b03"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 33 → Fin 641 := ![
  2,
  3,
  17,
  30,
  58,
  60,
  162,
  166,
  168,
  175,
  228,
  243,
  304,
  348,
  350,
  359,
  362,
  363,
  368,
  395,
  443,
  481,
  560,
  576,
  577,
  627,
  632,
  634,
  635,
  637,
  638,
  639,
  640
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 33 → SparsePoly (Fin 64) := ![
  [{ coefficient := 1, powers := [(3, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(15, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (33, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (36, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1)] }, { coefficient := 1, powers := [(25, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (45, 1)] }, { coefficient := 1, powers := [(19, 1), (29, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (50, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (33, 1)] }, { coefficient := 1, powers := [(33, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (30, 1), (58, 1)] }, { coefficient := 1, powers := [(30, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (24, 1), (58, 1)] }, { coefficient := 1, powers := [(24, 1)] }],
  [{ coefficient := 1, powers := [(15, 1), (21, 1), (51, 1)] }, { coefficient := 1, powers := [(15, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (47, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (57, 1)] }, { coefficient := 1, powers := [(9, 1), (54, 1)] }, { coefficient := 1, powers := [(15, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (45, 1)] }, { coefficient := 1, powers := [(19, 1), (41, 1)] }, { coefficient := 1, powers := [(19, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (53, 1)] }, { coefficient := 1, powers := [(30, 1), (42, 1)] }, { coefficient := 1, powers := [(33, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (56, 1)] }, { coefficient := 1, powers := [(30, 1), (47, 1)] }, { coefficient := 1, powers := [(36, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1), (54, 1)] }, { coefficient := 1, powers := [(6, 1), (34, 1), (42, 1)] }, { coefficient := 1, powers := [(15, 1), (25, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (33, 1), (54, 1)] }, { coefficient := 1, powers := [(6, 1), (33, 1), (43, 1)] }, { coefficient := 1, powers := [(15, 1), (33, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (25, 1), (45, 1)] }, { coefficient := 1, powers := [(19, 1), (25, 1), (41, 1)] }, { coefficient := 1, powers := [(19, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1), (48, 1)] }, { coefficient := 1, powers := [(6, 1), (31, 1), (44, 1)] }, { coefficient := 1, powers := [(9, 1), (25, 1), (44, 1)] }, { coefficient := 1, powers := [(48, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (41, 1), (54, 1)] }, { coefficient := 1, powers := [(6, 1), (34, 1), (41, 1)] }, { coefficient := 1, powers := [(15, 1), (25, 1), (41, 1)] }, { coefficient := 1, powers := [(15, 1)] }, { coefficient := 1, powers := [(54, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1)] }, { coefficient := 1, powers := [(3, 1), (34, 1)] }, { coefficient := 1, powers := [(15, 1), (20, 1)] }, { coefficient := 1, powers := [(20, 1), (54, 1)] }, { coefficient := 1, powers := [(25, 1), (43, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (48, 1)] }, { coefficient := 1, powers := [(6, 1), (31, 1)] }, { coefficient := 1, powers := [(9, 1), (25, 1)] }, { coefficient := 1, powers := [(20, 1), (48, 1)] }, { coefficient := 1, powers := [(25, 1), (40, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (41, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (45, 1), (52, 1)] }, { coefficient := 1, powers := [(8, 1), (36, 1), (41, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (56, 1)] }, { coefficient := 1, powers := [(18, 1), (30, 1), (45, 1)] }, { coefficient := 1, powers := [(19, 1), (29, 1), (52, 1)] }, { coefficient := 1, powers := [(19, 1), (30, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (37, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (40, 1), (54, 1)] }, { coefficient := 1, powers := [(0, 1), (43, 1), (48, 1)] }, { coefficient := 1, powers := [(3, 1), (25, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (31, 1), (54, 1)] }, { coefficient := 1, powers := [(3, 1), (34, 1), (48, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1), (57, 1)] }, { coefficient := 1, powers := [(6, 1), (31, 1), (43, 1)] }, { coefficient := 1, powers := [(6, 1), (34, 1), (40, 1)] }, { coefficient := 1, powers := [(9, 1), (20, 1), (54, 1)] }, { coefficient := 1, powers := [(9, 1), (25, 1), (43, 1)] }, { coefficient := 1, powers := [(9, 1), (34, 1), (37, 1)] }, { coefficient := 1, powers := [(15, 1), (20, 1), (48, 1)] }, { coefficient := 1, powers := [(15, 1), (25, 1), (40, 1)] }, { coefficient := 1, powers := [(15, 1), (31, 1), (37, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (39, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (42, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (47, 1), (53, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1), (53, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (59, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (47, 1)] }, { coefficient := 1, powers := [(8, 1), (36, 1), (42, 1)] }, { coefficient := 1, powers := [(14, 1), (24, 1), (56, 1)] }, { coefficient := 1, powers := [(14, 1), (30, 1), (47, 1)] }, { coefficient := 1, powers := [(14, 1), (36, 1), (39, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (53, 1)] }, { coefficient := 1, powers := [(19, 1), (30, 1), (42, 1)] }, { coefficient := 1, powers := [(19, 1), (33, 1), (39, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (60, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(40, 1)] }],
  [{ coefficient := 1, powers := [(41, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(42, 1), (63, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 33 → SparsePoly (Fin 64) := ![
  [{ coefficient := -1, powers := [(5, 1), (30, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (24, 1), (58, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (5, 1), (9, 1), (21, 1), (33, 1), (56, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (5, 1), (21, 1), (33, 1), (48, 1), (56, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (5, 1), (33, 1), (56, 1), (57, 1), (63, 1)] }, { coefficient := 1, powers := [(5, 1), (9, 1), (15, 1), (33, 1), (56, 1), (63, 1)] }, { coefficient := 1, powers := [(5, 1), (9, 1), (33, 1), (43, 1), (56, 1), (63, 1)] }, { coefficient := -1, powers := [(5, 1), (33, 1), (43, 1), (48, 1), (56, 1), (63, 1)] }, { coefficient := -1, powers := [(8, 1), (33, 1), (47, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(19, 1), (30, 1), (42, 1), (50, 2), (62, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (20, 1), (34, 1), (48, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (34, 1), (37, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (53, 1), (58, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (33, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(42, 1), (52, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(42, 1), (56, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (5, 1), (56, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (9, 1), (34, 1), (56, 1)] }, { coefficient := -1, powers := [(5, 1), (20, 1), (34, 1), (44, 1), (48, 1), (56, 1)] }, { coefficient := -1, powers := [(5, 1), (31, 1), (34, 1), (37, 1), (44, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (59, 1)] }, { coefficient := -1, powers := [(19, 1), (53, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (5, 1), (9, 1), (33, 1), (56, 1), (63, 1)] }, { coefficient := 1, powers := [(0, 1), (5, 1), (33, 1), (48, 1), (56, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (53, 1), (58, 1)] }, { coefficient := 1, powers := [(53, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (5, 1), (33, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (20, 1), (33, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [(25, 1), (30, 1), (42, 1), (50, 1), (62, 1)] }, { coefficient := -1, powers := [(30, 1), (42, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(19, 1)] }],
  [{ coefficient := 1, powers := [(14, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (5, 1), (9, 1), (33, 1), (41, 1), (56, 1), (63, 1)] }, { coefficient := -1, powers := [(5, 1), (9, 1), (33, 1), (56, 1), (63, 1)] }, { coefficient := 1, powers := [(5, 1), (20, 1), (33, 1), (41, 1), (48, 1), (56, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (31, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(30, 1), (42, 1), (50, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (33, 1), (34, 1), (37, 1), (56, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (5, 1), (9, 1), (33, 1), (56, 1)] }, { coefficient := -1, powers := [(5, 1), (20, 1), (33, 1), (48, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (33, 1), (48, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (33, 1), (34, 1), (37, 1), (44, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(42, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (33, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(8, 1), (33, 1), (47, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (47, 1), (53, 1), (58, 1)] }, { coefficient := 1, powers := [(39, 1), (59, 1)] }, { coefficient := -1, powers := [(41, 1), (42, 1), (56, 1), (62, 1)] }, { coefficient := 1, powers := [(42, 1), (50, 1), (56, 1), (62, 1)] }, { coefficient := 1, powers := [(42, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (5, 1), (33, 1), (54, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (6, 1), (33, 1), (34, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (15, 1), (25, 1), (33, 1), (56, 1)] }, { coefficient := -1, powers := [(5, 1), (25, 1), (33, 1), (34, 1), (37, 1), (44, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (6, 1), (36, 1), (53, 1), (58, 1)] }, { coefficient := -1, powers := [(8, 1), (36, 1), (42, 1)] }],
  [{ coefficient := 2, powers := [(0, 2), (5, 1), (9, 1), (33, 1), (41, 1), (54, 1), (56, 1)] }, { coefficient := 2, powers := [(0, 1), (5, 1), (6, 1), (9, 1), (33, 1), (34, 1), (41, 1), (56, 1)] }, { coefficient := 2, powers := [(0, 1), (5, 1), (9, 1), (15, 1), (25, 1), (33, 1), (41, 1), (56, 1)] }, { coefficient := 2, powers := [(0, 1), (5, 1), (9, 1), (15, 1), (33, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (5, 1), (9, 1), (33, 1), (54, 1), (56, 1)] }, { coefficient := -1, powers := [(0, 1), (5, 1), (15, 1), (33, 1), (48, 1), (56, 1)] }, { coefficient := -1, powers := [(0, 1), (5, 1), (20, 1), (33, 1), (41, 1), (48, 1), (54, 1), (56, 1)] }, { coefficient := -1, powers := [(3, 1), (5, 1), (25, 1), (33, 1), (56, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (6, 1), (9, 1), (33, 1), (34, 1), (56, 1)] }, { coefficient := -1, powers := [(5, 1), (6, 1), (20, 1), (33, 1), (34, 1), (41, 1), (48, 1), (56, 1)] }, { coefficient := -1, powers := [(5, 1), (9, 1), (25, 1), (33, 1), (43, 1), (56, 1)] }, { coefficient := -1, powers := [(5, 1), (15, 1), (20, 1), (25, 1), (33, 1), (41, 1), (48, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (25, 1), (33, 1), (43, 1), (48, 1), (56, 1)] }, { coefficient := 1, powers := [(8, 1), (25, 1), (33, 1), (47, 1), (60, 1)] }, { coefficient := -1, powers := [(19, 1), (25, 1), (30, 1), (42, 1), (50, 2), (62, 1)] }]
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
    ¬ ∀ index : Fin 33,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component50.SelectedLeafB6_3.selectedHasNoCommonZero

end Krenn.Component50.SelectedLeafB6_3
