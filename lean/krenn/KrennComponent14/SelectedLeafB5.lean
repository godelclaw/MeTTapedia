import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component14.SelectedLeafB5

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "e8733b36b4325878255453ae6b070b54e1e1223cd4ce7e1f4a8d7a7197068b36"
def certificateSHA256 : String := "e870f158e89c8fe96b04615615afa882959a884e3b178f413796e9849c4744fb"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 38 → Fin 637 := ![
  1,
  3,
  6,
  7,
  9,
  12,
  17,
  20,
  23,
  24,
  166,
  168,
  179,
  183,
  195,
  208,
  282,
  313,
  320,
  343,
  345,
  348,
  350,
  351,
  365,
  368,
  369,
  400,
  434,
  454,
  488,
  579,
  580,
  632,
  633,
  634,
  635,
  636
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 38 → SparsePoly (Fin 61) := ![
  [{ coefficient := 1, powers := [(2, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (31, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(15, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (17, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(31, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (45, 1)] }, { coefficient := 1, powers := [(5, 1), (27, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (51, 1)] }, { coefficient := 1, powers := [(8, 1), (21, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (44, 1)] }, { coefficient := 1, powers := [(12, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (39, 1)] }, { coefficient := 1, powers := [(16, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(39, 1), (42, 1)] }, { coefficient := 1, powers := [(42, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (35, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (17, 1), (54, 1)] }, { coefficient := 1, powers := [(12, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (23, 1), (39, 1)] }, { coefficient := 1, powers := [(16, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (48, 1), (54, 1)] }, { coefficient := 1, powers := [(26, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1)] }, { coefficient := 1, powers := [(18, 1), (42, 1)] }, { coefficient := 1, powers := [(23, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (52, 1)] }, { coefficient := 1, powers := [(17, 1), (52, 1)] }, { coefficient := 1, powers := [(24, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (46, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (58, 1)] }, { coefficient := 1, powers := [(12, 1), (46, 1)] }, { coefficient := 1, powers := [(16, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (58, 1)] }, { coefficient := 1, powers := [(12, 1), (55, 1)] }, { coefficient := 1, powers := [(16, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1), (50, 1)] }, { coefficient := 1, powers := [(18, 1), (42, 1), (50, 1)] }, { coefficient := 1, powers := [(46, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (39, 1), (55, 1)] }, { coefficient := 1, powers := [(4, 1), (30, 1), (55, 1)] }, { coefficient := 1, powers := [(11, 1), (20, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (40, 1), (54, 1)] }, { coefficient := 1, powers := [(7, 1), (33, 1), (40, 1)] }, { coefficient := 1, powers := [(15, 1), (26, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (31, 1), (54, 1)] }, { coefficient := 1, powers := [(7, 1), (31, 1), (44, 1)] }, { coefficient := 1, powers := [(15, 1), (31, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (42, 1), (51, 1)] }, { coefficient := 1, powers := [(20, 1), (55, 1)] }, { coefficient := 1, powers := [(25, 1), (39, 1), (42, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (45, 1), (48, 1), (54, 1)] }, { coefficient := 1, powers := [(26, 1), (40, 1)] }, { coefficient := 1, powers := [(26, 1), (45, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (37, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (45, 1), (51, 1)] }, { coefficient := 1, powers := [(5, 1), (28, 1), (57, 1)] }, { coefficient := 1, powers := [(8, 1), (22, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (57, 1)] }, { coefficient := 1, powers := [(7, 1), (57, 1)] }, { coefficient := 1, powers := [(11, 1), (44, 1)] }, { coefficient := 1, powers := [(11, 1), (54, 1)] }, { coefficient := 1, powers := [(15, 1), (39, 1)] }, { coefficient := 1, powers := [(15, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (50, 1)] }, { coefficient := 1, powers := [(20, 1), (54, 1)] }, { coefficient := 1, powers := [(26, 1), (39, 1)] }, { coefficient := 1, powers := [(26, 1), (44, 1)] }, { coefficient := 1, powers := [(30, 1), (36, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (36, 1), (57, 1)] }, { coefficient := 1, powers := [(1, 1), (39, 1), (54, 1)] }, { coefficient := 1, powers := [(1, 1), (44, 1), (50, 1)] }, { coefficient := 1, powers := [(4, 1), (26, 1), (57, 1)] }, { coefficient := 1, powers := [(4, 1), (30, 1), (54, 1)] }, { coefficient := 1, powers := [(4, 1), (33, 1), (50, 1)] }, { coefficient := 1, powers := [(7, 1), (20, 1), (57, 1)] }, { coefficient := 1, powers := [(7, 1), (30, 1), (44, 1)] }, { coefficient := 1, powers := [(7, 1), (33, 1), (39, 1)] }, { coefficient := 1, powers := [(11, 1), (20, 1), (54, 1)] }, { coefficient := 1, powers := [(11, 1), (26, 1), (44, 1)] }, { coefficient := 1, powers := [(11, 1), (33, 1), (36, 1)] }, { coefficient := 1, powers := [(15, 1), (20, 1), (50, 1)] }, { coefficient := 1, powers := [(15, 1), (26, 1), (39, 1)] }, { coefficient := 1, powers := [(15, 1), (30, 1), (36, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (37, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (40, 1), (55, 1)] }, { coefficient := 1, powers := [(2, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(5, 1), (28, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (52, 1)] }, { coefficient := 1, powers := [(8, 1), (22, 1), (58, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1), (46, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (40, 1)] }, { coefficient := 1, powers := [(12, 1), (22, 1), (55, 1)] }, { coefficient := 1, powers := [(12, 1), (28, 1), (46, 1)] }, { coefficient := 1, powers := [(12, 1), (34, 1), (37, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1), (52, 1)] }, { coefficient := 1, powers := [(16, 1), (28, 1), (40, 1)] }, { coefficient := 1, powers := [(16, 1), (31, 1), (37, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (59, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (60, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 38 → SparsePoly (Fin 61) := ![
  [{ coefficient := 1, powers := [(2, 1), (7, 1), (30, 1), (40, 1), (55, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (11, 1), (26, 1), (40, 1), (55, 1), (60, 1)] }, { coefficient := -1, powers := [(2, 1), (15, 1), (26, 1), (40, 1), (55, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (7, 1), (30, 1), (31, 1), (55, 1), (60, 1)] }, { coefficient := 1, powers := [(12, 1), (17, 1), (34, 1), (37, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (4, 1), (33, 1), (40, 1), (55, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (7, 1), (25, 1), (40, 1), (42, 1), (51, 1), (57, 1), (60, 1)] }, { coefficient := 1, powers := [(4, 1), (5, 1), (31, 1), (33, 1), (55, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (15, 1), (20, 1), (31, 1), (55, 1), (60, 1)] }, { coefficient := -1, powers := [(5, 1), (15, 1), (26, 1), (31, 1), (55, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (23, 1), (31, 1), (46, 1), (60, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1), (31, 1), (37, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(27, 1), (35, 1), (51, 1), (58, 1)] }, { coefficient := 1, powers := [(28, 1), (35, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (20, 1), (55, 1), (57, 1)] }, { coefficient := -1, powers := [(5, 1), (26, 1), (55, 1), (57, 1)] }, { coefficient := -1, powers := [(5, 1), (30, 1), (44, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (39, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (7, 1), (20, 1), (21, 1), (40, 1), (42, 1), (57, 1), (60, 1)] }, { coefficient := 1, powers := [(22, 1), (35, 1), (58, 1)] }, { coefficient := -1, powers := [(34, 1), (35, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (33, 1), (36, 1), (40, 1)] }, { coefficient := 1, powers := [(5, 1), (20, 1), (31, 1), (54, 1)] }, { coefficient := -1, powers := [(5, 1), (26, 1), (31, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (20, 1), (54, 1), (55, 1)] }, { coefficient := -1, powers := [(2, 1), (26, 1), (39, 1), (55, 1)] }, { coefficient := -1, powers := [(2, 1), (33, 1), (36, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (52, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (24, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (11, 1), (33, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(35, 1), (51, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (7, 1), (20, 1), (40, 1), (42, 1), (57, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(17, 1), (34, 1), (37, 1)] }],
  [{ coefficient := -1, powers := [(23, 1), (31, 1), (37, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (7, 1), (25, 1), (40, 1), (51, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (34, 1), (40, 1), (60, 1)] }, { coefficient := 1, powers := [(37, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(34, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(31, 1), (37, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (4, 1), (45, 1), (55, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (31, 1), (50, 1)] }],
  [{ coefficient := -1, powers := [(16, 1), (22, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(52, 1)] }],
  [{ coefficient := 1, powers := [(28, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (22, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (31, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (40, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (39, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (30, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (7, 1), (40, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (4, 1), (55, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [(35, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (26, 1), (31, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (15, 1), (40, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (40, 1), (55, 1)] }, { coefficient := -1, powers := [(5, 1), (31, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(8, 1), (22, 1), (58, 1)] }, { coefficient := -1, powers := [(12, 1), (22, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (36, 1), (40, 1), (55, 1), (57, 1)] }, { coefficient := -1, powers := [(2, 1), (39, 1), (40, 1), (54, 1), (55, 1)] }, { coefficient := 1, powers := [(2, 1), (40, 1), (44, 1), (50, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (36, 1), (55, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (39, 1), (54, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (44, 1), (50, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (4, 1), (33, 1), (40, 1), (50, 1), (55, 1)] }, { coefficient := 1, powers := [(2, 1), (7, 1), (20, 1), (40, 1), (42, 1), (51, 1), (57, 1)] }, { coefficient := -1, powers := [(2, 1), (7, 1), (25, 1), (40, 1), (42, 1), (50, 1), (51, 1), (57, 1)] }, { coefficient := -1, powers := [(2, 1), (7, 1), (30, 1), (40, 1), (44, 1), (55, 1)] }, { coefficient := -1, powers := [(2, 1), (11, 1), (26, 1), (40, 1), (44, 1), (55, 1)] }, { coefficient := 1, powers := [(2, 1), (15, 1), (26, 1), (40, 1), (44, 1), (55, 1)] }, { coefficient := -1, powers := [(4, 1), (5, 1), (31, 1), (33, 1), (50, 1), (55, 1)] }, { coefficient := -1, powers := [(5, 1), (7, 1), (30, 1), (31, 1), (44, 1), (55, 1)] }, { coefficient := -1, powers := [(5, 1), (15, 1), (20, 1), (31, 1), (50, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (15, 1), (26, 1), (31, 1), (50, 1), (55, 1)] }, { coefficient := -1, powers := [(8, 1), (23, 1), (31, 1), (46, 1), (50, 1)] }, { coefficient := -1, powers := [(8, 1), (34, 1), (35, 1), (40, 1), (57, 1)] }, { coefficient := -1, powers := [(8, 1), (34, 1), (40, 1)] }, { coefficient := -1, powers := [(12, 1), (17, 1), (34, 1), (37, 1), (44, 1)] }, { coefficient := -1, powers := [(16, 1), (23, 1), (31, 1), (37, 1), (50, 1)] }]
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
    ¬ ∀ index : Fin 38,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component14.SelectedLeafB5.selectedHasNoCommonZero

end Krenn.Component14.SelectedLeafB5
