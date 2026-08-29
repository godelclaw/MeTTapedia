import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component47.SelectedLeafB6_1

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "eae37822775852b8bbb95f85ff645a56c7593b9536fc7e14e0763658d244a309"
def certificateSHA256 : String := "35b6ef26bbba7e733aa850c1b5acb1303186e9700dbe70b0abfb984bee33726d"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 33 → Fin 593 := ![
  3,
  10,
  21,
  31,
  40,
  50,
  208,
  220,
  221,
  250,
  287,
  341,
  360,
  363,
  365,
  366,
  376,
  377,
  418,
  423,
  436,
  481,
  532,
  534,
  544,
  584,
  586,
  587,
  588,
  589,
  590,
  591,
  592
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 33 → SparsePoly (Fin 61) := ![
  [{ coefficient := 1, powers := [(6, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(15, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(33, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1)] }, { coefficient := 1, powers := [(25, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (33, 1)] }, { coefficient := 1, powers := [(18, 1), (21, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (32, 1)] }, { coefficient := 1, powers := [(32, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (40, 1), (54, 1)] }, { coefficient := 1, powers := [(54, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (24, 1), (56, 1)] }, { coefficient := 1, powers := [(24, 1)] }],
  [{ coefficient := 1, powers := [(15, 1), (21, 1), (50, 1)] }, { coefficient := 1, powers := [(15, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (42, 1)] }, { coefficient := 1, powers := [(11, 1), (22, 1), (52, 1)] }, { coefficient := 1, powers := [(11, 1), (26, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (46, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (55, 1)] }, { coefficient := 1, powers := [(9, 1), (52, 1)] }, { coefficient := 1, powers := [(15, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (57, 1)] }, { coefficient := 1, powers := [(14, 1), (54, 1)] }, { coefficient := 1, powers := [(19, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (51, 1)] }, { coefficient := 1, powers := [(29, 1), (41, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (54, 1)] }, { coefficient := 1, powers := [(29, 1), (46, 1)] }, { coefficient := 1, powers := [(35, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (33, 1), (51, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (41, 1)] }, { coefficient := 1, powers := [(14, 1), (33, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (24, 1), (57, 1)] }, { coefficient := 1, powers := [(6, 1), (32, 1), (46, 1)] }, { coefficient := 1, powers := [(6, 1), (35, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (20, 1), (52, 1)] }, { coefficient := 1, powers := [(10, 1), (25, 1), (42, 1)] }, { coefficient := 1, powers := [(10, 1), (33, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1), (49, 1)] }, { coefficient := 1, powers := [(3, 1), (33, 1), (49, 1)] }, { coefficient := 1, powers := [(15, 1), (20, 1), (49, 1)] }, { coefficient := 1, powers := [(42, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (40, 1), (52, 1)] }, { coefficient := 1, powers := [(6, 1), (33, 1), (40, 1)] }, { coefficient := 1, powers := [(15, 1), (25, 1), (40, 1)] }, { coefficient := 1, powers := [(15, 1)] }, { coefficient := 1, powers := [(52, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (36, 1), (55, 1)] }, { coefficient := 1, powers := [(1, 1), (39, 1), (52, 1)] }, { coefficient := 1, powers := [(1, 1), (42, 1), (47, 1)] }, { coefficient := 1, powers := [(10, 1), (22, 1), (52, 1)] }, { coefficient := 1, powers := [(10, 1), (26, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1)] }, { coefficient := 1, powers := [(3, 1), (33, 1)] }, { coefficient := 1, powers := [(15, 1), (20, 1)] }, { coefficient := 1, powers := [(20, 1), (52, 1)] }, { coefficient := 1, powers := [(25, 1), (42, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (36, 1), (55, 1)] }, { coefficient := 1, powers := [(0, 1), (39, 1), (52, 1)] }, { coefficient := 1, powers := [(0, 1), (42, 1), (47, 1)] }, { coefficient := 1, powers := [(3, 1), (25, 1), (55, 1)] }, { coefficient := 1, powers := [(3, 1), (30, 1), (52, 1)] }, { coefficient := 1, powers := [(3, 1), (33, 1), (47, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1), (55, 1)] }, { coefficient := 1, powers := [(6, 1), (30, 1), (42, 1)] }, { coefficient := 1, powers := [(6, 1), (33, 1), (39, 1)] }, { coefficient := 1, powers := [(9, 1), (20, 1), (52, 1)] }, { coefficient := 1, powers := [(9, 1), (25, 1), (42, 1)] }, { coefficient := 1, powers := [(9, 1), (33, 1), (36, 1)] }, { coefficient := 1, powers := [(15, 1), (20, 1), (47, 1)] }, { coefficient := 1, powers := [(15, 1), (25, 1), (39, 1)] }, { coefficient := 1, powers := [(15, 1), (30, 1), (36, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (41, 1), (54, 1)] }, { coefficient := 1, powers := [(2, 1), (46, 1), (51, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (51, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (57, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (46, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(14, 1), (24, 1), (54, 1)] }, { coefficient := 1, powers := [(14, 1), (29, 1), (46, 1)] }, { coefficient := 1, powers := [(14, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (51, 1)] }, { coefficient := 1, powers := [(19, 1), (29, 1), (41, 1)] }, { coefficient := 1, powers := [(19, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (58, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1), (59, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(39, 1)] }],
  [{ coefficient := 1, powers := [(40, 1)] }],
  [{ coefficient := 1, powers := [(41, 1), (60, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 33 → SparsePoly (Fin 61) := ![
  [{ coefficient := 1, powers := [(5, 1), (29, 1), (30, 1), (42, 1)] }, { coefficient := -2, powers := [(8, 1), (9, 1), (24, 1), (33, 1), (36, 1), (56, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (30, 1), (42, 1)] }, { coefficient := 2, powers := [(8, 1), (24, 1), (33, 1), (36, 1), (47, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (26, 1), (47, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (10, 1), (21, 1), (22, 1), (59, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (11, 1), (21, 1), (22, 1), (47, 1), (59, 1), (60, 1)] }, { coefficient := 1, powers := [(3, 1), (21, 1), (30, 1), (60, 1)] }, { coefficient := -1, powers := [(21, 1), (30, 1), (36, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(9, 1), (21, 1), (29, 1), (36, 1), (57, 1)] }, { coefficient := 1, powers := [(9, 1), (21, 1), (35, 1), (36, 1), (51, 1)] }, { coefficient := 1, powers := [(21, 1), (29, 1), (36, 1), (47, 1), (57, 1)] }, { coefficient := -1, powers := [(21, 1), (35, 1), (36, 1), (47, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (55, 1), (60, 1)] }, { coefficient := -1, powers := [(6, 1), (8, 1), (30, 1), (32, 1), (42, 1), (46, 1), (58, 1), (60, 1)] }, { coefficient := -1, powers := [(8, 1), (9, 1), (32, 1), (33, 1), (36, 1), (46, 1), (58, 1), (60, 1)] }, { coefficient := -1, powers := [(8, 1), (30, 1), (32, 1), (36, 1), (42, 1), (46, 1), (58, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (33, 1), (36, 1), (46, 1), (47, 1), (58, 1), (60, 1)] }, { coefficient := 1, powers := [(9, 1), (42, 1), (60, 1)] }, { coefficient := -1, powers := [(42, 1), (47, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(9, 1), (14, 1), (35, 1), (36, 1)] }, { coefficient := 1, powers := [(14, 1), (35, 1), (36, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (8, 1), (30, 1), (32, 1), (42, 1), (58, 1)] }, { coefficient := 1, powers := [(8, 1), (9, 1), (32, 1), (33, 1), (36, 1), (58, 1)] }, { coefficient := 1, powers := [(8, 1), (30, 1), (32, 1), (36, 1), (42, 1), (58, 1)] }, { coefficient := -1, powers := [(8, 1), (32, 1), (33, 1), (36, 1), (47, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (29, 1), (36, 1), (57, 1)] }, { coefficient := -1, powers := [(9, 1), (35, 1), (36, 1), (51, 1)] }, { coefficient := -1, powers := [(29, 1), (36, 1), (47, 1), (57, 1)] }, { coefficient := 1, powers := [(35, 1), (36, 1), (47, 1), (51, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (30, 1), (42, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (6, 1), (30, 1), (32, 1), (42, 1)] }, { coefficient := 1, powers := [(5, 1), (9, 1), (32, 1), (33, 1), (36, 1)] }, { coefficient := -1, powers := [(5, 1), (32, 1), (33, 1), (36, 1), (47, 1)] }, { coefficient := 1, powers := [(6, 1), (14, 1), (24, 1), (30, 1), (42, 1)] }, { coefficient := 1, powers := [(9, 1), (14, 1), (24, 1), (33, 1), (36, 1)] }, { coefficient := -1, powers := [(14, 1), (24, 1), (33, 1), (36, 1), (47, 1)] }],
  [{ coefficient := 2, powers := [(8, 1), (9, 1), (33, 1), (36, 1), (57, 1)] }, { coefficient := -2, powers := [(8, 1), (33, 1), (36, 1), (47, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (10, 1), (22, 1), (59, 1), (60, 1)] }, { coefficient := -1, powers := [(0, 1), (11, 1), (22, 1), (47, 1), (59, 1), (60, 1)] }, { coefficient := -1, powers := [(3, 1), (30, 1), (60, 1)] }, { coefficient := 1, powers := [(30, 1), (36, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (47, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (30, 1), (42, 1), (51, 1)] }, { coefficient := 1, powers := [(9, 1), (33, 1), (36, 1), (51, 1)] }, { coefficient := -1, powers := [(33, 1), (36, 1), (47, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(20, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (24, 1), (30, 1), (42, 1)] }, { coefficient := -1, powers := [(9, 1), (24, 1), (33, 1), (36, 1)] }, { coefficient := 1, powers := [(24, 1), (33, 1), (36, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (19, 1), (30, 1), (42, 1)] }, { coefficient := 1, powers := [(9, 1), (19, 1), (33, 1), (36, 1)] }, { coefficient := -1, powers := [(19, 1), (33, 1), (36, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (14, 1), (30, 1), (42, 1)] }, { coefficient := 1, powers := [(9, 1), (14, 1), (33, 1), (36, 1)] }, { coefficient := -1, powers := [(14, 1), (33, 1), (36, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (35, 1), (36, 1)] }, { coefficient := -1, powers := [(35, 1), (36, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (30, 1), (42, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (26, 1), (49, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (10, 1), (26, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (10, 1), (22, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (11, 1), (22, 1), (47, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (30, 1)] }, { coefficient := -1, powers := [(20, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (10, 1), (26, 1), (49, 1), (59, 1)] }, { coefficient := 1, powers := [(47, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(6, 1), (30, 1), (42, 1)] }, { coefficient := -1, powers := [(9, 1), (33, 1), (36, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1), (47, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (8, 1), (30, 1), (32, 1), (42, 1), (46, 1)] }, { coefficient := -1, powers := [(8, 1), (9, 1), (32, 1), (33, 1), (36, 1), (46, 1)] }, { coefficient := -1, powers := [(8, 1), (30, 1), (32, 1), (36, 1), (42, 1), (46, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (33, 1), (36, 1), (46, 1), (47, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (36, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (30, 1), (38, 1), (42, 1), (57, 1)] }, { coefficient := 1, powers := [(6, 1), (30, 1), (41, 1), (42, 1), (54, 1)] }, { coefficient := 1, powers := [(9, 1), (33, 1), (36, 1), (38, 1), (57, 1)] }, { coefficient := 1, powers := [(9, 1), (33, 1), (36, 1), (41, 1), (54, 1)] }, { coefficient := -1, powers := [(33, 1), (36, 1), (38, 1), (47, 1), (57, 1)] }, { coefficient := -1, powers := [(33, 1), (36, 1), (41, 1), (47, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (1, 1), (52, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (52, 1)] }, { coefficient := 1, powers := [(6, 1), (33, 1)] }, { coefficient := 1, powers := [(15, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(0, 2), (10, 1), (22, 1), (52, 1), (59, 1)] }, { coefficient := -1, powers := [(0, 2), (11, 1), (22, 1), (47, 1), (52, 1), (59, 1)] }, { coefficient := -1, powers := [(0, 1), (3, 1), (30, 1), (52, 1)] }, { coefficient := -1, powers := [(0, 1), (5, 1), (6, 1), (30, 1), (32, 1), (42, 1), (54, 1)] }, { coefficient := -1, powers := [(0, 1), (5, 1), (9, 1), (32, 1), (33, 1), (36, 1), (54, 1)] }, { coefficient := 1, powers := [(0, 1), (5, 1), (32, 1), (33, 1), (36, 1), (47, 1), (54, 1)] }, { coefficient := 1, powers := [(0, 1), (6, 1), (10, 1), (22, 1), (33, 1), (59, 1)] }, { coefficient := -1, powers := [(0, 1), (6, 1), (11, 1), (22, 1), (33, 1), (47, 1), (59, 1)] }, { coefficient := -1, powers := [(0, 1), (6, 1), (14, 1), (24, 1), (30, 1), (42, 1), (54, 1)] }, { coefficient := -1, powers := [(0, 1), (9, 1), (14, 1), (24, 1), (33, 1), (36, 1), (54, 1)] }, { coefficient := 1, powers := [(0, 1), (10, 1), (15, 1), (22, 1), (25, 1), (59, 1)] }, { coefficient := -1, powers := [(0, 1), (11, 1), (15, 1), (22, 1), (25, 1), (47, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (14, 1), (24, 1), (33, 1), (36, 1), (47, 1), (54, 1)] }, { coefficient := 1, powers := [(0, 1), (20, 1), (47, 1), (52, 1)] }, { coefficient := -1, powers := [(3, 1), (6, 1), (30, 1), (33, 1)] }, { coefficient := -1, powers := [(3, 1), (15, 1), (25, 1), (30, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1), (33, 1), (47, 1)] }, { coefficient := 1, powers := [(15, 1), (20, 1), (25, 1), (47, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (10, 1), (15, 1), (22, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (11, 1), (15, 1), (22, 1), (47, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (15, 1), (30, 1)] }, { coefficient := -1, powers := [(3, 1), (25, 1), (55, 1)] }, { coefficient := 1, powers := [(6, 1), (8, 1), (25, 1), (30, 1), (32, 1), (42, 1), (46, 1), (58, 1)] }, { coefficient := 1, powers := [(8, 1), (9, 1), (25, 1), (32, 1), (33, 1), (36, 1), (46, 1), (58, 1)] }, { coefficient := 1, powers := [(8, 1), (25, 1), (30, 1), (32, 1), (36, 1), (42, 1), (46, 1), (58, 1)] }, { coefficient := -1, powers := [(8, 1), (25, 1), (32, 1), (33, 1), (36, 1), (46, 1), (47, 1), (58, 1)] }, { coefficient := -1, powers := [(9, 1), (25, 1), (42, 1)] }, { coefficient := -1, powers := [(15, 1), (30, 1), (36, 1)] }, { coefficient := 1, powers := [(25, 1), (42, 1), (47, 1)] }]
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
    ¬ ∀ index : Fin 33,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component47.SelectedLeafB6_1.selectedHasNoCommonZero

end Krenn.Component47.SelectedLeafB6_1
