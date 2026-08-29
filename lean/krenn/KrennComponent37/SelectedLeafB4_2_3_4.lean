import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component37.SelectedLeafB4_2_3_4

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "e84226ff8de42915b33635e3c161dcd6f39862a2e5ad57ae71e6d577327f3ca1"
def certificateSHA256 : String := "584d363ac49cd23409a8db8b0ca59a3db8cb24e15825900a6ff835ee40220898"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 36 → Fin 670 := ![
  5,
  23,
  167,
  171,
  175,
  176,
  179,
  180,
  181,
  283,
  296,
  297,
  298,
  299,
  311,
  433,
  438,
  450,
  454,
  495,
  497,
  519,
  566,
  567,
  604,
  605,
  656,
  657,
  658,
  659,
  660,
  663,
  666,
  667,
  668,
  669
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 36 → SparsePoly (Fin 67) := ![
  [{ coefficient := 1, powers := [(5, 1), (35, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (25, 1)] }, { coefficient := 1, powers := [(18, 1), (20, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (20, 1)] }, { coefficient := 1, powers := [(18, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (44, 1)] }, { coefficient := 1, powers := [(19, 1), (20, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (55, 1)] }, { coefficient := 1, powers := [(30, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (44, 1)] }, { coefficient := 1, powers := [(28, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (54, 1)] }, { coefficient := 1, powers := [(30, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (44, 1), (54, 1)] }, { coefficient := 1, powers := [(22, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (51, 1)] }, { coefficient := 1, powers := [(20, 1), (51, 1)] }, { coefficient := 1, powers := [(25, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (55, 1)] }, { coefficient := 1, powers := [(20, 1), (55, 1)] }, { coefficient := 1, powers := [(26, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (46, 1)] }, { coefficient := 1, powers := [(4, 1), (35, 1)] }, { coefficient := 1, powers := [(15, 1), (22, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (52, 1)] }, { coefficient := 1, powers := [(7, 1), (32, 1)] }, { coefficient := 1, powers := [(10, 1), (27, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (52, 1)] }, { coefficient := 1, powers := [(24, 1), (57, 1)] }, { coefficient := 1, powers := [(29, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (49, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1)] }, { coefficient := 1, powers := [(18, 1), (28, 1), (49, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1)] }, { coefficient := 1, powers := [(12, 1), (30, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (61, 1)] }, { coefficient := 1, powers := [(12, 1), (26, 1), (47, 1)] }, { coefficient := 1, powers := [(12, 1), (58, 1)] }, { coefficient := 1, powers := [(19, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (55, 1)] }, { coefficient := 1, powers := [(30, 1), (42, 1)] }, { coefficient := 1, powers := [(30, 1), (48, 1), (51, 1)] }, { coefficient := 1, powers := [(33, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (46, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (46, 1)] }, { coefficient := 1, powers := [(12, 1), (30, 1), (46, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (49, 1), (52, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1), (52, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (49, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (27, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (52, 1)] }, { coefficient := 1, powers := [(18, 1), (27, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (44, 1), (54, 1)] }, { coefficient := 1, powers := [(24, 1), (58, 1)] }, { coefficient := 1, powers := [(30, 1), (49, 1)] }, { coefficient := 1, powers := [(36, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (51, 1), (57, 1)] }, { coefficient := 1, powers := [(24, 1), (53, 1)] }, { coefficient := 1, powers := [(29, 1), (42, 1)] }, { coefficient := 1, powers := [(29, 1), (48, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (60, 1)] }, { coefficient := 1, powers := [(10, 1), (46, 1)] }, { coefficient := 1, powers := [(10, 1), (57, 1)] }, { coefficient := 1, powers := [(15, 1), (41, 1)] }, { coefficient := 1, powers := [(15, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (52, 1)] }, { coefficient := 1, powers := [(22, 1), (57, 1)] }, { coefficient := 1, powers := [(27, 1), (41, 1)] }, { coefficient := 1, powers := [(27, 1), (46, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1)] }, { coefficient := 1, powers := [(35, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (38, 1), (60, 1)] }, { coefficient := 1, powers := [(1, 1), (41, 1), (57, 1)] }, { coefficient := 1, powers := [(1, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(4, 1), (27, 1), (60, 1)] }, { coefficient := 1, powers := [(4, 1), (32, 1), (57, 1)] }, { coefficient := 1, powers := [(4, 1), (35, 1), (52, 1)] }, { coefficient := 1, powers := [(7, 1), (22, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (32, 1), (46, 1)] }, { coefficient := 1, powers := [(7, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(10, 1), (22, 1), (57, 1)] }, { coefficient := 1, powers := [(10, 1), (27, 1), (46, 1)] }, { coefficient := 1, powers := [(10, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(15, 1), (22, 1), (52, 1)] }, { coefficient := 1, powers := [(15, 1), (27, 1), (41, 1)] }, { coefficient := 1, powers := [(15, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (39, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (42, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (49, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (49, 1)] }, { coefficient := 1, powers := [(8, 1), (36, 1), (42, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (58, 1)] }, { coefficient := 1, powers := [(12, 1), (30, 1), (49, 1)] }, { coefficient := 1, powers := [(12, 1), (36, 1), (39, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (55, 1)] }, { coefficient := 1, powers := [(19, 1), (30, 1), (42, 1)] }, { coefficient := 1, powers := [(19, 1), (33, 1), (39, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1)] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(42, 1)] }],
  [{ coefficient := 1, powers := [(58, 1), (65, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(25, 1), (66, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(27, 1)] }],
  [{ coefficient := 1, powers := [(30, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 36 → SparsePoly (Fin 67) := ![
  [{ coefficient := 1, powers := [(0, 1), (4, 1), (36, 1), (41, 1), (52, 1), (55, 1)] }, { coefficient := 1, powers := [(0, 1), (4, 1), (36, 1), (52, 2), (55, 1)] }, { coefficient := 1, powers := [(0, 1), (4, 1), (36, 1), (52, 1), (55, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (7, 1), (36, 1), (41, 1), (52, 1), (55, 1)] }, { coefficient := 1, powers := [(0, 1), (10, 1), (36, 1), (38, 1), (52, 1), (55, 1)] }, { coefficient := -1, powers := [(0, 1), (15, 1), (36, 1), (38, 1), (52, 1), (55, 1)] }, { coefficient := 1, powers := [(4, 1), (33, 1), (41, 1), (58, 1)] }, { coefficient := 1, powers := [(4, 1), (33, 1), (52, 1), (58, 1)] }, { coefficient := 1, powers := [(4, 1), (33, 1), (57, 1), (58, 1)] }, { coefficient := 2, powers := [(4, 1), (36, 1), (41, 1), (55, 1)] }, { coefficient := 2, powers := [(4, 1), (36, 1), (52, 1), (55, 1)] }, { coefficient := 2, powers := [(4, 1), (36, 1), (55, 1), (57, 1)] }, { coefficient := 1, powers := [(7, 1), (33, 1), (41, 1), (58, 1)] }, { coefficient := 2, powers := [(7, 1), (36, 1), (41, 1), (55, 1)] }, { coefficient := 1, powers := [(10, 1), (33, 1), (38, 1), (58, 1)] }, { coefficient := 2, powers := [(10, 1), (36, 1), (38, 1), (55, 1)] }, { coefficient := -1, powers := [(15, 1), (33, 1), (38, 1), (58, 1)] }, { coefficient := -2, powers := [(15, 1), (36, 1), (38, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (4, 1), (5, 1), (36, 1), (44, 1), (52, 1), (55, 1), (60, 1), (65, 1)] }, { coefficient := 1, powers := [(0, 1), (5, 1), (10, 1), (36, 1), (44, 1), (46, 1), (52, 1), (55, 1), (65, 1)] }, { coefficient := 1, powers := [(4, 1), (5, 1), (33, 1), (44, 1), (58, 1), (60, 1), (65, 1)] }, { coefficient := 2, powers := [(4, 1), (5, 1), (36, 1), (44, 1), (55, 1), (60, 1), (65, 1)] }, { coefficient := 1, powers := [(5, 1), (10, 1), (33, 1), (44, 1), (46, 1), (58, 1), (65, 1)] }, { coefficient := 2, powers := [(5, 1), (10, 1), (36, 1), (44, 1), (46, 1), (55, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(24, 1), (58, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(24, 1), (26, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (51, 1), (58, 1), (62, 1)] }, { coefficient := 1, powers := [(24, 1), (51, 1), (58, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(24, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (18, 1), (46, 1), (49, 1)] }, { coefficient := -1, powers := [(18, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (44, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (4, 1), (5, 1), (36, 1), (52, 1), (55, 1), (60, 1), (65, 1)] }, { coefficient := -1, powers := [(0, 1), (5, 1), (10, 1), (36, 1), (46, 1), (52, 1), (55, 1), (65, 1)] }, { coefficient := -1, powers := [(4, 1), (5, 1), (33, 1), (58, 1), (60, 1), (65, 1)] }, { coefficient := -2, powers := [(4, 1), (5, 1), (36, 1), (55, 1), (60, 1), (65, 1)] }, { coefficient := -1, powers := [(5, 1), (10, 1), (33, 1), (46, 1), (58, 1), (65, 1)] }, { coefficient := -2, powers := [(5, 1), (10, 1), (36, 1), (46, 1), (55, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(18, 1), (24, 1), (58, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (24, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (5, 1), (36, 1), (41, 1), (52, 1), (55, 1)] }, { coefficient := -1, powers := [(0, 1), (5, 1), (36, 1), (52, 2), (55, 1)] }, { coefficient := -1, powers := [(0, 1), (5, 1), (36, 1), (52, 1), (55, 1), (57, 1)] }, { coefficient := -1, powers := [(5, 1), (33, 1), (41, 1), (58, 1)] }, { coefficient := -1, powers := [(5, 1), (33, 1), (52, 1), (58, 1)] }, { coefficient := -1, powers := [(5, 1), (33, 1), (57, 1), (58, 1)] }, { coefficient := -2, powers := [(5, 1), (36, 1), (41, 1), (55, 1)] }, { coefficient := -2, powers := [(5, 1), (36, 1), (52, 1), (55, 1)] }, { coefficient := -2, powers := [(5, 1), (36, 1), (55, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (5, 1), (36, 1), (46, 1), (52, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (46, 1), (58, 1)] }, { coefficient := 2, powers := [(5, 1), (36, 1), (46, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(19, 1), (26, 1), (51, 1)] }],
  [{ coefficient := -1, powers := [(55, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (46, 1), (49, 1)] }, { coefficient := 1, powers := [(49, 1)] }],
  [{ coefficient := 1, powers := [(24, 1)] }],
  [{ coefficient := 1, powers := [(19, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (49, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (4, 1), (36, 1), (52, 1), (55, 1)] }, { coefficient := 1, powers := [(4, 1), (33, 1), (58, 1)] }, { coefficient := 2, powers := [(4, 1), (36, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(12, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (26, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (5, 1), (22, 1), (36, 1), (52, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (22, 1), (33, 1), (58, 1)] }, { coefficient := 2, powers := [(5, 1), (22, 1), (36, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (5, 1), (15, 1), (36, 1), (52, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (15, 1), (33, 1), (58, 1)] }, { coefficient := 2, powers := [(5, 1), (15, 1), (36, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (5, 1), (36, 1), (52, 1), (55, 1)] }, { coefficient := -1, powers := [(5, 1), (33, 1), (58, 1)] }, { coefficient := -2, powers := [(5, 1), (36, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(18, 1), (24, 1), (51, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (5, 1), (36, 1), (38, 1), (52, 1), (55, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (5, 1), (36, 1), (41, 1), (46, 1), (52, 1), (55, 1)] }, { coefficient := 1, powers := [(0, 1), (5, 1), (36, 1), (41, 1), (52, 1), (55, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (5, 1), (36, 1), (46, 1), (52, 2), (55, 1)] }, { coefficient := 1, powers := [(0, 1), (5, 1), (36, 1), (46, 1), (52, 1), (55, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (38, 1), (58, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (41, 1), (46, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (41, 1), (57, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (46, 1), (52, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (46, 1), (57, 1), (58, 1)] }, { coefficient := 2, powers := [(5, 1), (36, 1), (38, 1), (55, 1), (60, 1)] }, { coefficient := 2, powers := [(5, 1), (36, 1), (41, 1), (46, 1), (55, 1)] }, { coefficient := 2, powers := [(5, 1), (36, 1), (41, 1), (55, 1), (57, 1)] }, { coefficient := 2, powers := [(5, 1), (36, 1), (46, 1), (52, 1), (55, 1)] }, { coefficient := 2, powers := [(5, 1), (36, 1), (46, 1), (55, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (49, 1), (52, 1), (55, 1)] }, { coefficient := 1, powers := [(39, 1), (61, 1)] }, { coefficient := 1, powers := [(42, 1), (58, 1)] }, { coefficient := 1, powers := [(49, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (36, 1)] }, { coefficient := -1, powers := [(19, 1), (26, 1), (29, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (4, 1), (5, 1), (22, 1), (36, 1), (52, 1), (55, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (5, 1), (10, 1), (22, 1), (36, 1), (46, 1), (52, 1), (55, 1)] }, { coefficient := 1, powers := [(4, 1), (5, 1), (22, 1), (33, 1), (58, 1), (60, 1)] }, { coefficient := 2, powers := [(4, 1), (5, 1), (22, 1), (36, 1), (55, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (10, 1), (22, 1), (33, 1), (46, 1), (58, 1)] }, { coefficient := 2, powers := [(5, 1), (10, 1), (22, 1), (36, 1), (46, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (24, 1), (58, 1)] }, { coefficient := -1, powers := [(18, 1), (24, 1), (51, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (4, 1), (18, 1), (36, 1), (48, 1), (52, 1), (55, 1)] }, { coefficient := -1, powers := [(0, 1), (5, 1), (15, 1), (36, 1), (46, 1), (52, 1), (55, 1)] }, { coefficient := -1, powers := [(4, 1), (18, 1), (33, 1), (48, 1), (58, 1)] }, { coefficient := -2, powers := [(4, 1), (18, 1), (36, 1), (48, 1), (55, 1)] }, { coefficient := -1, powers := [(5, 1), (15, 1), (33, 1), (46, 1), (58, 1)] }, { coefficient := -2, powers := [(5, 1), (15, 1), (36, 1), (46, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (18, 1), (46, 1), (49, 1), (51, 1)] }, { coefficient := 1, powers := [(5, 1), (61, 1)] }, { coefficient := 1, powers := [(12, 1), (44, 1), (48, 1)] }, { coefficient := -1, powers := [(12, 1), (49, 1)] }, { coefficient := 1, powers := [(18, 1), (49, 1), (51, 1)] }, { coefficient := -1, powers := [(19, 1), (48, 1), (51, 1)] }]
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
    ¬ ∀ index : Fin 36,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component37.SelectedLeafB4_2_3_4.selectedHasNoCommonZero

end Krenn.Component37.SelectedLeafB4_2_3_4
