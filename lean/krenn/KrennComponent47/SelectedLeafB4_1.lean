import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component47.SelectedLeafB4_1

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "f59b0a4dbc1fa08f064787761566dbd82d9d819714ff17d8ee17b49b03d9f9d5"
def certificateSHA256 : String := "487a2179dcfb565f18884928038e9a16d3a42fd95492cad48778d87461588267"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 30 → Fin 593 := ![
  3,
  5,
  21,
  31,
  40,
  50,
  208,
  220,
  221,
  247,
  250,
  287,
  341,
  363,
  365,
  366,
  376,
  377,
  418,
  423,
  528,
  532,
  544,
  584,
  586,
  587,
  589,
  590,
  591,
  592
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 30 → SparsePoly (Fin 60) := ![
  [{ coefficient := 1, powers := [(6, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(15, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(33, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1)] }, { coefficient := 1, powers := [(25, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (33, 1)] }, { coefficient := 1, powers := [(18, 1), (21, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (32, 1)] }, { coefficient := 1, powers := [(32, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (40, 1)] }, { coefficient := 1, powers := [(29, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (40, 1), (54, 1)] }, { coefficient := 1, powers := [(54, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (24, 1), (56, 1)] }, { coefficient := 1, powers := [(24, 1)] }],
  [{ coefficient := 1, powers := [(15, 1), (21, 1), (50, 1)] }, { coefficient := 1, powers := [(15, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (46, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (55, 1)] }, { coefficient := 1, powers := [(9, 1), (52, 1)] }, { coefficient := 1, powers := [(15, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (57, 1)] }, { coefficient := 1, powers := [(14, 1), (54, 1)] }, { coefficient := 1, powers := [(19, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (51, 1)] }, { coefficient := 1, powers := [(29, 1), (41, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (54, 1)] }, { coefficient := 1, powers := [(29, 1), (46, 1)] }, { coefficient := 1, powers := [(35, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (33, 1), (51, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (41, 1)] }, { coefficient := 1, powers := [(14, 1), (33, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (24, 1), (57, 1)] }, { coefficient := 1, powers := [(6, 1), (32, 1), (46, 1)] }, { coefficient := 1, powers := [(6, 1), (35, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1)] }, { coefficient := 1, powers := [(6, 1), (56, 1)] }, { coefficient := 1, powers := [(25, 1), (40, 1)] }, { coefficient := 1, powers := [(25, 1), (43, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (40, 1), (52, 1)] }, { coefficient := 1, powers := [(6, 1), (33, 1), (40, 1)] }, { coefficient := 1, powers := [(15, 1), (25, 1), (40, 1)] }, { coefficient := 1, powers := [(15, 1)] }, { coefficient := 1, powers := [(52, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1)] }, { coefficient := 1, powers := [(3, 1), (33, 1)] }, { coefficient := 1, powers := [(15, 1), (20, 1)] }, { coefficient := 1, powers := [(20, 1), (52, 1)] }, { coefficient := 1, powers := [(25, 1), (42, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (36, 1), (55, 1)] }, { coefficient := 1, powers := [(0, 1), (39, 1), (52, 1)] }, { coefficient := 1, powers := [(0, 1), (42, 1), (47, 1)] }, { coefficient := 1, powers := [(3, 1), (25, 1), (55, 1)] }, { coefficient := 1, powers := [(3, 1), (30, 1), (52, 1)] }, { coefficient := 1, powers := [(3, 1), (33, 1), (47, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1), (55, 1)] }, { coefficient := 1, powers := [(6, 1), (30, 1), (42, 1)] }, { coefficient := 1, powers := [(6, 1), (33, 1), (39, 1)] }, { coefficient := 1, powers := [(9, 1), (20, 1), (52, 1)] }, { coefficient := 1, powers := [(9, 1), (25, 1), (42, 1)] }, { coefficient := 1, powers := [(9, 1), (33, 1), (36, 1)] }, { coefficient := 1, powers := [(15, 1), (20, 1), (47, 1)] }, { coefficient := 1, powers := [(15, 1), (25, 1), (39, 1)] }, { coefficient := 1, powers := [(15, 1), (30, 1), (36, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (41, 1), (54, 1)] }, { coefficient := 1, powers := [(2, 1), (46, 1), (51, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (51, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (57, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (46, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(14, 1), (24, 1), (54, 1)] }, { coefficient := 1, powers := [(14, 1), (29, 1), (46, 1)] }, { coefficient := 1, powers := [(14, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (51, 1)] }, { coefficient := 1, powers := [(19, 1), (29, 1), (41, 1)] }, { coefficient := 1, powers := [(19, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (58, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(39, 1)] }],
  [{ coefficient := 1, powers := [(40, 1)] }],
  [{ coefficient := 1, powers := [(41, 1), (59, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 30 → SparsePoly (Fin 60) := ![
  [{ coefficient := -1, powers := [(0, 1), (5, 1), (29, 1), (36, 1), (41, 1), (55, 1), (56, 1), (59, 1)] }, { coefficient := -2, powers := [(0, 1), (8, 1), (24, 1), (36, 1), (41, 1), (55, 1), (56, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (30, 1), (42, 1)] }, { coefficient := -2, powers := [(8, 1), (9, 1), (24, 1), (33, 1), (36, 1), (56, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (30, 1), (42, 1)] }, { coefficient := 2, powers := [(8, 1), (24, 1), (33, 1), (36, 1), (47, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (35, 1), (36, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (21, 1), (30, 1), (59, 1)] }, { coefficient := -1, powers := [(21, 1), (30, 1), (36, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(9, 1), (21, 1), (29, 1), (36, 1), (57, 1)] }, { coefficient := 1, powers := [(9, 1), (21, 1), (35, 1), (36, 1), (51, 1)] }, { coefficient := 1, powers := [(21, 1), (29, 1), (36, 1), (47, 1), (57, 1)] }, { coefficient := -1, powers := [(21, 1), (35, 1), (36, 1), (47, 1), (51, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (8, 1), (32, 1), (36, 1), (41, 1), (46, 1), (55, 1), (58, 1), (59, 2)] }, { coefficient := 1, powers := [(3, 1), (55, 1), (59, 1)] }, { coefficient := -1, powers := [(6, 1), (8, 1), (30, 1), (32, 1), (42, 1), (46, 1), (58, 1), (59, 1)] }, { coefficient := -1, powers := [(8, 1), (9, 1), (32, 1), (33, 1), (36, 1), (46, 1), (58, 1), (59, 1)] }, { coefficient := -1, powers := [(8, 1), (30, 1), (32, 1), (36, 1), (42, 1), (46, 1), (58, 1), (59, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (33, 1), (36, 1), (46, 1), (47, 1), (58, 1), (59, 1)] }, { coefficient := 1, powers := [(9, 1), (42, 1), (59, 1)] }, { coefficient := -1, powers := [(42, 1), (47, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(9, 1), (14, 1), (35, 1), (36, 1)] }, { coefficient := 1, powers := [(14, 1), (35, 1), (36, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (8, 1), (32, 1), (36, 1), (41, 1), (55, 1), (58, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (8, 1), (30, 1), (32, 1), (42, 1), (58, 1)] }, { coefficient := 1, powers := [(8, 1), (9, 1), (32, 1), (33, 1), (36, 1), (58, 1)] }, { coefficient := 1, powers := [(8, 1), (30, 1), (32, 1), (36, 1), (42, 1), (58, 1)] }, { coefficient := -1, powers := [(8, 1), (32, 1), (33, 1), (36, 1), (47, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (29, 1), (36, 1), (57, 1)] }, { coefficient := -1, powers := [(9, 1), (35, 1), (36, 1), (51, 1)] }, { coefficient := -1, powers := [(29, 1), (36, 1), (47, 1), (57, 1)] }, { coefficient := 1, powers := [(35, 1), (36, 1), (47, 1), (51, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (30, 1), (42, 1), (46, 1)] }],
  [{ coefficient := -1, powers := [(0, 2), (5, 1), (36, 1), (41, 1), (55, 1), (57, 1), (59, 1)] }, { coefficient := -1, powers := [(0, 1), (5, 1), (25, 1), (36, 1), (41, 1), (55, 1), (57, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (5, 1), (32, 1), (36, 1), (41, 1), (55, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (14, 1), (24, 1), (36, 1), (41, 1), (55, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (6, 1), (30, 1), (32, 1), (42, 1)] }, { coefficient := 1, powers := [(5, 1), (9, 1), (32, 1), (33, 1), (36, 1)] }, { coefficient := -1, powers := [(5, 1), (32, 1), (33, 1), (36, 1), (47, 1)] }, { coefficient := 1, powers := [(6, 1), (14, 1), (24, 1), (30, 1), (42, 1)] }, { coefficient := 1, powers := [(9, 1), (14, 1), (24, 1), (33, 1), (36, 1)] }, { coefficient := -1, powers := [(14, 1), (24, 1), (33, 1), (36, 1), (47, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (8, 1), (36, 1), (41, 1), (55, 1), (57, 1), (59, 1)] }, { coefficient := 2, powers := [(8, 1), (9, 1), (33, 1), (36, 1), (57, 1)] }, { coefficient := -2, powers := [(8, 1), (33, 1), (36, 1), (47, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (30, 1), (59, 1)] }, { coefficient := 1, powers := [(30, 1), (36, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (36, 1), (41, 1), (51, 1), (55, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (30, 1), (42, 1), (51, 1)] }, { coefficient := 1, powers := [(9, 1), (33, 1), (36, 1), (51, 1)] }, { coefficient := -1, powers := [(33, 1), (36, 1), (47, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(20, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (24, 1), (36, 1), (41, 1), (55, 1), (59, 1)] }, { coefficient := -1, powers := [(6, 1), (24, 1), (30, 1), (42, 1)] }, { coefficient := -1, powers := [(9, 1), (24, 1), (33, 1), (36, 1)] }, { coefficient := 1, powers := [(24, 1), (33, 1), (36, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (19, 1), (36, 1), (41, 1), (55, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (19, 1), (30, 1), (42, 1)] }, { coefficient := 1, powers := [(9, 1), (19, 1), (33, 1), (36, 1)] }, { coefficient := -1, powers := [(19, 1), (33, 1), (36, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (14, 1), (36, 1), (41, 1), (55, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (14, 1), (30, 1), (42, 1)] }, { coefficient := 1, powers := [(9, 1), (14, 1), (33, 1), (36, 1)] }, { coefficient := -1, powers := [(14, 1), (33, 1), (36, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (35, 1), (36, 1)] }, { coefficient := -1, powers := [(35, 1), (36, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (30, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (5, 1), (29, 1), (36, 1), (41, 1), (55, 1), (57, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (30, 1)] }, { coefficient := -1, powers := [(20, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(47, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(0, 1), (36, 1), (41, 1), (55, 1), (59, 1)] }, { coefficient := -1, powers := [(6, 1), (30, 1), (42, 1)] }, { coefficient := -1, powers := [(9, 1), (33, 1), (36, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1), (47, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (8, 1), (32, 1), (36, 1), (41, 1), (46, 1), (55, 1), (59, 1)] }, { coefficient := -1, powers := [(6, 1), (8, 1), (30, 1), (32, 1), (42, 1), (46, 1)] }, { coefficient := -1, powers := [(8, 1), (9, 1), (32, 1), (33, 1), (36, 1), (46, 1)] }, { coefficient := -1, powers := [(8, 1), (30, 1), (32, 1), (36, 1), (42, 1), (46, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (33, 1), (36, 1), (46, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (36, 1), (38, 1), (41, 1), (55, 1), (57, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (36, 1), (41, 2), (54, 1), (55, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (30, 1), (38, 1), (42, 1), (57, 1)] }, { coefficient := 1, powers := [(6, 1), (30, 1), (41, 1), (42, 1), (54, 1)] }, { coefficient := 1, powers := [(9, 1), (33, 1), (36, 1), (38, 1), (57, 1)] }, { coefficient := 1, powers := [(9, 1), (33, 1), (36, 1), (41, 1), (54, 1)] }, { coefficient := -1, powers := [(33, 1), (36, 1), (38, 1), (47, 1), (57, 1)] }, { coefficient := -1, powers := [(33, 1), (36, 1), (41, 1), (47, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (52, 1)] }, { coefficient := 1, powers := [(6, 1), (33, 1)] }, { coefficient := 1, powers := [(15, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(0, 2), (5, 1), (29, 1), (36, 1), (41, 1), (55, 1), (57, 1), (59, 1)] }, { coefficient := -1, powers := [(0, 2), (5, 1), (32, 1), (36, 1), (41, 1), (54, 1), (55, 1), (59, 1)] }, { coefficient := -1, powers := [(0, 2), (14, 1), (24, 1), (36, 1), (41, 1), (54, 1), (55, 1), (59, 1)] }, { coefficient := -1, powers := [(0, 1), (3, 1), (30, 1), (52, 1)] }, { coefficient := -1, powers := [(0, 1), (5, 1), (6, 1), (30, 1), (32, 1), (42, 1), (54, 1)] }, { coefficient := -1, powers := [(0, 1), (5, 1), (9, 1), (32, 1), (33, 1), (36, 1), (54, 1)] }, { coefficient := 1, powers := [(0, 1), (5, 1), (32, 1), (33, 1), (36, 1), (47, 1), (54, 1)] }, { coefficient := -1, powers := [(0, 1), (6, 1), (14, 1), (24, 1), (30, 1), (42, 1), (54, 1)] }, { coefficient := -1, powers := [(0, 1), (9, 1), (14, 1), (24, 1), (33, 1), (36, 1), (54, 1)] }, { coefficient := 1, powers := [(0, 1), (14, 1), (24, 1), (33, 1), (36, 1), (47, 1), (54, 1)] }, { coefficient := 1, powers := [(0, 1), (20, 1), (47, 1), (52, 1)] }, { coefficient := -1, powers := [(3, 1), (6, 1), (30, 1), (33, 1)] }, { coefficient := -1, powers := [(3, 1), (15, 1), (25, 1), (30, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1), (33, 1), (47, 1)] }, { coefficient := 1, powers := [(15, 1), (20, 1), (25, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (8, 1), (25, 1), (32, 1), (36, 1), (41, 1), (46, 1), (55, 1), (58, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (8, 1), (35, 1), (36, 1), (41, 1), (55, 1)] }, { coefficient := -1, powers := [(0, 1), (36, 1), (55, 1)] }, { coefficient := 1, powers := [(3, 1), (15, 1), (30, 1)] }, { coefficient := -1, powers := [(3, 1), (25, 1), (55, 1)] }, { coefficient := 1, powers := [(6, 1), (8, 1), (25, 1), (30, 1), (32, 1), (42, 1), (46, 1), (58, 1)] }, { coefficient := 1, powers := [(8, 1), (9, 1), (25, 1), (32, 1), (33, 1), (36, 1), (46, 1), (58, 1)] }, { coefficient := 1, powers := [(8, 1), (25, 1), (30, 1), (32, 1), (36, 1), (42, 1), (46, 1), (58, 1)] }, { coefficient := -1, powers := [(8, 1), (25, 1), (32, 1), (33, 1), (36, 1), (46, 1), (47, 1), (58, 1)] }, { coefficient := -1, powers := [(9, 1), (25, 1), (42, 1)] }, { coefficient := -1, powers := [(15, 1), (30, 1), (36, 1)] }, { coefficient := 1, powers := [(25, 1), (42, 1), (47, 1)] }]
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
    ¬ ∀ index : Fin 30,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component47.SelectedLeafB4_1.selectedHasNoCommonZero

end Krenn.Component47.SelectedLeafB4_1
