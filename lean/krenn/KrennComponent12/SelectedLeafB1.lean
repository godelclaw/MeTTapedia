import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component12.SelectedLeafB1

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "4e0222991fdde61543dd42dc7217e58684d9dc6db0f59e5d5388a65718c413bc"
def certificateSHA256 : String := "4e81c160612913935d9ab598ae758a1ab225dada00ff6f084e78711d646cc1bb"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 27 → Fin 616 := ![
  5,
  7,
  10,
  11,
  16,
  23,
  198,
  209,
  216,
  218,
  227,
  292,
  335,
  336,
  339,
  350,
  400,
  464,
  489,
  578,
  579,
  605,
  611,
  612,
  613,
  614,
  615
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 27 → SparsePoly (Fin 60) := ![
  [{ coefficient := 1, powers := [(2, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (33, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (46, 1)] }, { coefficient := 1, powers := [(5, 1), (26, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (44, 1)] }, { coefficient := 1, powers := [(12, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (40, 1), (54, 1)] }, { coefficient := 1, powers := [(40, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(52, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (35, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (18, 1), (54, 1)] }, { coefficient := 1, powers := [(12, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (44, 1)] }, { coefficient := 1, powers := [(4, 1), (33, 1)] }, { coefficient := 1, powers := [(15, 1), (20, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (50, 1)] }, { coefficient := 1, powers := [(7, 1), (30, 1)] }, { coefficient := 1, powers := [(11, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (52, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1)] }, { coefficient := 1, powers := [(12, 1), (28, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (52, 1)] }, { coefficient := 1, powers := [(28, 1), (40, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (25, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (58, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (45, 1)] }, { coefficient := 1, powers := [(12, 1), (55, 1)] }, { coefficient := 1, powers := [(17, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (37, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (46, 1), (51, 1)] }, { coefficient := 1, powers := [(5, 1), (28, 1), (57, 1)] }, { coefficient := 1, powers := [(8, 1), (22, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (57, 1)] }, { coefficient := 1, powers := [(7, 1), (57, 1)] }, { coefficient := 1, powers := [(11, 1), (44, 1)] }, { coefficient := 1, powers := [(11, 1), (54, 1)] }, { coefficient := 1, powers := [(15, 1), (39, 1)] }, { coefficient := 1, powers := [(15, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (50, 1)] }, { coefficient := 1, powers := [(20, 1), (54, 1)] }, { coefficient := 1, powers := [(25, 1), (39, 1)] }, { coefficient := 1, powers := [(25, 1), (44, 1)] }, { coefficient := 1, powers := [(30, 1), (36, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (36, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (39, 1), (54, 1)] }, { coefficient := 1, powers := [(0, 1), (44, 1), (50, 1)] }, { coefficient := 1, powers := [(39, 1)] }, { coefficient := 1, powers := [(44, 1)] }, { coefficient := 1, powers := [(50, 1)] }, { coefficient := 1, powers := [(54, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (36, 1), (57, 1)] }, { coefficient := 1, powers := [(1, 1), (39, 1), (54, 1)] }, { coefficient := 1, powers := [(1, 1), (44, 1), (50, 1)] }, { coefficient := 1, powers := [(4, 1), (25, 1), (57, 1)] }, { coefficient := 1, powers := [(4, 1), (30, 1), (54, 1)] }, { coefficient := 1, powers := [(4, 1), (33, 1), (50, 1)] }, { coefficient := 1, powers := [(7, 1), (20, 1), (57, 1)] }, { coefficient := 1, powers := [(7, 1), (30, 1), (44, 1)] }, { coefficient := 1, powers := [(7, 1), (33, 1), (39, 1)] }, { coefficient := 1, powers := [(11, 1), (20, 1), (54, 1)] }, { coefficient := 1, powers := [(11, 1), (25, 1), (44, 1)] }, { coefficient := 1, powers := [(11, 1), (33, 1), (36, 1)] }, { coefficient := 1, powers := [(15, 1), (20, 1), (50, 1)] }, { coefficient := 1, powers := [(15, 1), (25, 1), (39, 1)] }, { coefficient := 1, powers := [(15, 1), (30, 1), (36, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (37, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (40, 1), (55, 1)] }, { coefficient := 1, powers := [(2, 1), (47, 1), (52, 1)] }, { coefficient := 1, powers := [(5, 1), (28, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (52, 1)] }, { coefficient := 1, powers := [(8, 1), (22, 1), (58, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1), (47, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (40, 1)] }, { coefficient := 1, powers := [(12, 1), (22, 1), (55, 1)] }, { coefficient := 1, powers := [(12, 1), (28, 1), (47, 1)] }, { coefficient := 1, powers := [(12, 1), (34, 1), (37, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (52, 1)] }, { coefficient := 1, powers := [(17, 1), (28, 1), (40, 1)] }, { coefficient := 1, powers := [(17, 1), (31, 1), (37, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1)] }],
  [{ coefficient := 1, powers := [(1, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (59, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 27 → SparsePoly (Fin 60) := ![
  [{ coefficient := -1, powers := [(4, 1), (5, 1), (28, 1), (33, 1), (58, 1), (59, 1)] }, { coefficient := -1, powers := [(4, 1), (5, 1), (31, 1), (33, 1), (55, 1), (59, 1)] }, { coefficient := -1, powers := [(5, 1), (7, 1), (28, 1), (33, 1), (58, 1), (59, 1)] }, { coefficient := -1, powers := [(5, 1), (7, 1), (31, 1), (33, 1), (55, 1), (59, 1)] }, { coefficient := -1, powers := [(5, 1), (11, 1), (20, 1), (28, 1), (58, 1), (59, 1)] }, { coefficient := -1, powers := [(5, 1), (11, 1), (20, 1), (31, 1), (55, 1), (59, 1)] }, { coefficient := -1, powers := [(5, 1), (15, 1), (25, 1), (28, 1), (58, 1), (59, 1)] }, { coefficient := -1, powers := [(5, 1), (15, 1), (25, 1), (31, 1), (55, 1), (59, 1)] }, { coefficient := 1, powers := [(12, 1), (18, 1), (34, 1), (37, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (5, 1), (28, 1), (33, 1), (58, 1), (59, 1)] }, { coefficient := 1, powers := [(4, 1), (5, 1), (31, 1), (33, 1), (55, 1), (59, 1)] }, { coefficient := -1, powers := [(5, 1), (7, 1), (28, 1), (33, 1), (58, 1), (59, 1)] }, { coefficient := -1, powers := [(5, 1), (7, 1), (31, 1), (33, 1), (55, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (28, 1), (50, 1), (58, 1)] }, { coefficient := -1, powers := [(4, 1), (31, 1), (50, 1), (55, 1)] }, { coefficient := -1, powers := [(7, 1), (28, 1), (54, 1), (58, 1)] }, { coefficient := -1, powers := [(7, 1), (31, 1), (54, 1), (55, 1)] }, { coefficient := 1, powers := [(11, 1), (28, 1), (36, 1), (58, 1)] }, { coefficient := 1, powers := [(11, 1), (31, 1), (36, 1), (55, 1)] }, { coefficient := -1, powers := [(15, 1), (28, 1), (36, 1), (58, 1)] }, { coefficient := -1, powers := [(15, 1), (31, 1), (36, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (20, 1), (28, 1), (58, 1)] }, { coefficient := -1, powers := [(4, 1), (20, 1), (31, 1), (55, 1)] }, { coefficient := -1, powers := [(26, 1), (35, 1), (51, 1), (58, 1)] }, { coefficient := 1, powers := [(28, 1), (35, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (35, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(22, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(35, 1), (51, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(18, 1), (34, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (34, 1)] }, { coefficient := -1, powers := [(17, 1), (22, 1)] }],
  [{ coefficient := 1, powers := [(37, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(34, 1), (37, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (28, 1), (39, 1), (58, 1)] }, { coefficient := -1, powers := [(5, 1), (28, 1), (50, 1), (58, 1)] }, { coefficient := -1, powers := [(5, 1), (28, 1), (54, 1), (58, 1)] }, { coefficient := -1, powers := [(5, 1), (31, 1), (39, 1), (55, 1)] }, { coefficient := -1, powers := [(5, 1), (31, 1), (50, 1), (55, 1)] }, { coefficient := -1, powers := [(5, 1), (31, 1), (54, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (28, 1), (44, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (44, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(47, 1)] }],
  [{ coefficient := 1, powers := [(17, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (28, 1), (58, 1)] }, { coefficient := 1, powers := [(4, 1), (31, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(22, 1)] }],
  [{ coefficient := -1, powers := [(35, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (20, 1), (28, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (20, 1), (31, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (15, 1), (28, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (15, 1), (31, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (5, 1), (28, 1), (33, 1), (58, 1)] }, { coefficient := 1, powers := [(4, 1), (5, 1), (31, 1), (33, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (7, 1), (28, 1), (33, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (7, 1), (31, 1), (33, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (28, 1), (58, 1)] }, { coefficient := -1, powers := [(5, 1), (31, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(2, 1), (40, 1), (54, 1), (55, 1)] }, { coefficient := -1, powers := [(4, 1), (5, 1), (28, 1), (33, 1), (36, 1), (57, 1), (58, 1)] }, { coefficient := -1, powers := [(4, 1), (5, 1), (28, 1), (33, 1), (39, 1), (54, 1), (58, 1)] }, { coefficient := -1, powers := [(4, 1), (5, 1), (28, 1), (33, 1), (44, 1), (50, 1), (58, 1)] }, { coefficient := -1, powers := [(4, 1), (5, 1), (31, 1), (33, 1), (36, 1), (55, 1), (57, 1)] }, { coefficient := -1, powers := [(4, 1), (5, 1), (31, 1), (33, 1), (39, 1), (54, 1), (55, 1)] }, { coefficient := -1, powers := [(4, 1), (5, 1), (31, 1), (33, 1), (44, 1), (50, 1), (55, 1)] }, { coefficient := -1, powers := [(5, 1), (7, 1), (28, 1), (33, 1), (36, 1), (57, 1), (58, 1)] }, { coefficient := -1, powers := [(5, 1), (7, 1), (28, 1), (33, 1), (39, 1), (54, 1), (58, 1)] }, { coefficient := -1, powers := [(5, 1), (7, 1), (28, 1), (33, 1), (44, 1), (50, 1), (58, 1)] }, { coefficient := -1, powers := [(5, 1), (7, 1), (31, 1), (33, 1), (36, 1), (55, 1), (57, 1)] }, { coefficient := -1, powers := [(5, 1), (7, 1), (31, 1), (33, 1), (39, 1), (54, 1), (55, 1)] }, { coefficient := -1, powers := [(5, 1), (7, 1), (31, 1), (33, 1), (44, 1), (50, 1), (55, 1)] }, { coefficient := -1, powers := [(5, 1), (34, 1), (44, 1), (52, 1)] }, { coefficient := -1, powers := [(8, 1), (34, 1), (40, 1), (54, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (44, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (28, 1), (36, 1), (57, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (28, 1), (39, 1), (44, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (28, 1), (39, 1), (54, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (28, 1), (44, 1), (50, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (28, 1), (44, 1), (54, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (36, 1), (55, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (39, 1), (44, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (39, 1), (54, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (44, 1), (50, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (44, 1), (54, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (5, 1), (28, 1), (33, 1), (44, 1), (58, 1)] }, { coefficient := -1, powers := [(4, 1), (5, 1), (28, 1), (33, 1), (50, 1), (58, 1)] }, { coefficient := 1, powers := [(4, 1), (5, 1), (31, 1), (33, 1), (44, 1), (55, 1)] }, { coefficient := -1, powers := [(4, 1), (5, 1), (31, 1), (33, 1), (50, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (7, 1), (28, 1), (33, 1), (44, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (7, 1), (28, 1), (33, 1), (50, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (7, 1), (31, 1), (33, 1), (44, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (7, 1), (31, 1), (33, 1), (50, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (11, 1), (20, 1), (28, 1), (44, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (11, 1), (20, 1), (31, 1), (44, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (15, 1), (25, 1), (28, 1), (44, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (15, 1), (25, 1), (31, 1), (44, 1), (55, 1)] }, { coefficient := -1, powers := [(12, 1), (18, 1), (34, 1), (37, 1), (44, 1)] }]
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
    (values : Fin 60 → R) :
    ¬ ∀ index : Fin 27,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component12.SelectedLeafB1.selectedHasNoCommonZero

end Krenn.Component12.SelectedLeafB1
