import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component14.SelectedLeafB7

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "e59bbc1fd1b7b75a5eb310cd97e0d157b23364c823da0e5a14f8abbcc1ccd14a"
def certificateSHA256 : String := "be5f7260f0ce3f990c510298d123f3f41b67e55c5d98ea572a0c34f798b94aa7"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 36 → Fin 637 := ![
  1,
  3,
  6,
  7,
  9,
  12,
  19,
  20,
  23,
  24,
  164,
  165,
  166,
  171,
  179,
  183,
  199,
  208,
  282,
  313,
  343,
  345,
  348,
  350,
  351,
  365,
  367,
  381,
  400,
  488,
  579,
  632,
  633,
  634,
  635,
  636
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 36 → SparsePoly (Fin 62) := ![
  [{ coefficient := 1, powers := [(2, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (31, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(15, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (17, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(31, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (52, 1)] }, { coefficient := 1, powers := [(15, 1), (19, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (42, 1)] }, { coefficient := 1, powers := [(16, 1), (21, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (45, 1)] }, { coefficient := 1, powers := [(5, 1), (27, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (58, 1)] }, { coefficient := 1, powers := [(42, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (44, 1)] }, { coefficient := 1, powers := [(12, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (39, 1)] }, { coefficient := 1, powers := [(16, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (35, 1), (58, 1)] }, { coefficient := 1, powers := [(1, 1), (42, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (35, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (17, 1), (54, 1)] }, { coefficient := 1, powers := [(12, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (23, 1), (39, 1)] }, { coefficient := 1, powers := [(16, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1)] }, { coefficient := 1, powers := [(18, 1), (42, 1)] }, { coefficient := 1, powers := [(23, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (52, 1)] }, { coefficient := 1, powers := [(17, 1), (52, 1)] }, { coefficient := 1, powers := [(24, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (46, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (58, 1)] }, { coefficient := 1, powers := [(12, 1), (46, 1)] }, { coefficient := 1, powers := [(16, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (58, 1)] }, { coefficient := 1, powers := [(12, 1), (55, 1)] }, { coefficient := 1, powers := [(16, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1), (50, 1)] }, { coefficient := 1, powers := [(18, 1), (42, 1), (50, 1)] }, { coefficient := 1, powers := [(46, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (37, 1), (58, 1)] }, { coefficient := 1, powers := [(1, 1), (40, 1), (55, 1)] }, { coefficient := 1, powers := [(1, 1), (46, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (36, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (39, 1), (54, 1)] }, { coefficient := 1, powers := [(2, 1), (44, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (31, 1), (54, 1)] }, { coefficient := 1, powers := [(7, 1), (31, 1), (44, 1)] }, { coefficient := 1, powers := [(15, 1), (31, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (37, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (45, 1), (51, 1)] }, { coefficient := 1, powers := [(5, 1), (28, 1), (57, 1)] }, { coefficient := 1, powers := [(8, 1), (22, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (57, 1)] }, { coefficient := 1, powers := [(7, 1), (57, 1)] }, { coefficient := 1, powers := [(11, 1), (44, 1)] }, { coefficient := 1, powers := [(11, 1), (54, 1)] }, { coefficient := 1, powers := [(15, 1), (39, 1)] }, { coefficient := 1, powers := [(15, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (36, 1), (57, 1)] }, { coefficient := 1, powers := [(1, 1), (39, 1), (54, 1)] }, { coefficient := 1, powers := [(1, 1), (44, 1), (50, 1)] }, { coefficient := 1, powers := [(4, 1), (26, 1), (57, 1)] }, { coefficient := 1, powers := [(4, 1), (30, 1), (54, 1)] }, { coefficient := 1, powers := [(4, 1), (33, 1), (50, 1)] }, { coefficient := 1, powers := [(7, 1), (20, 1), (57, 1)] }, { coefficient := 1, powers := [(7, 1), (30, 1), (44, 1)] }, { coefficient := 1, powers := [(7, 1), (33, 1), (39, 1)] }, { coefficient := 1, powers := [(11, 1), (20, 1), (54, 1)] }, { coefficient := 1, powers := [(11, 1), (26, 1), (44, 1)] }, { coefficient := 1, powers := [(11, 1), (33, 1), (36, 1)] }, { coefficient := 1, powers := [(15, 1), (20, 1), (50, 1)] }, { coefficient := 1, powers := [(15, 1), (26, 1), (39, 1)] }, { coefficient := 1, powers := [(15, 1), (30, 1), (36, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (37, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (40, 1), (55, 1)] }, { coefficient := 1, powers := [(2, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(5, 1), (28, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (52, 1)] }, { coefficient := 1, powers := [(8, 1), (22, 1), (58, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1), (46, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (40, 1)] }, { coefficient := 1, powers := [(12, 1), (22, 1), (55, 1)] }, { coefficient := 1, powers := [(12, 1), (28, 1), (46, 1)] }, { coefficient := 1, powers := [(12, 1), (34, 1), (37, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1), (52, 1)] }, { coefficient := 1, powers := [(16, 1), (28, 1), (40, 1)] }, { coefficient := 1, powers := [(16, 1), (31, 1), (37, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (59, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1), (60, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (61, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 36 → SparsePoly (Fin 62) := ![
  [{ coefficient := 1, powers := [(5, 1), (7, 1), (30, 1), (31, 1), (55, 1), (61, 1)] }, { coefficient := 1, powers := [(12, 1), (17, 1), (34, 1), (37, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (5, 1), (31, 1), (33, 1), (55, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (15, 1), (20, 1), (31, 1), (55, 1), (61, 1)] }, { coefficient := -1, powers := [(5, 1), (15, 1), (26, 1), (31, 1), (55, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (23, 1), (31, 1), (46, 1), (61, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1), (31, 1), (37, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(27, 1), (35, 1), (51, 1), (58, 1)] }, { coefficient := 1, powers := [(28, 1), (35, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (20, 1), (55, 1), (57, 1)] }, { coefficient := -1, powers := [(5, 1), (26, 1), (55, 1), (57, 1)] }, { coefficient := -1, powers := [(5, 1), (30, 1), (44, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (39, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (35, 1), (58, 1)] }, { coefficient := -1, powers := [(34, 1), (35, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (20, 1), (31, 1), (54, 1)] }, { coefficient := -1, powers := [(5, 1), (26, 1), (31, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (19, 1), (46, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (52, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (21, 1), (37, 1), (57, 1), (61, 1)] }, { coefficient := 1, powers := [(22, 1), (24, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (11, 1), (33, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (46, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (37, 1), (48, 1), (57, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(35, 1), (51, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(1, 1), (2, 1), (37, 1), (57, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 2), (37, 1), (57, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(17, 1), (34, 1), (37, 1)] }],
  [{ coefficient := -1, powers := [(23, 1), (31, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (37, 1), (57, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (37, 1), (58, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (40, 1), (61, 1)] }, { coefficient := 1, powers := [(37, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(34, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(31, 1), (37, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (31, 1), (50, 1)] }],
  [{ coefficient := -1, powers := [(16, 1), (22, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(52, 1)] }],
  [{ coefficient := 1, powers := [(28, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (22, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (31, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (5, 1), (31, 1), (55, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (30, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(35, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (26, 1), (31, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (31, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(8, 1), (22, 1), (58, 1)] }, { coefficient := -1, powers := [(12, 1), (22, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (6, 1), (37, 1), (57, 1), (58, 1)] }, { coefficient := -1, powers := [(2, 1), (35, 1), (37, 1), (57, 1), (58, 1)] }, { coefficient := -1, powers := [(2, 1), (37, 1), (58, 1)] }, { coefficient := -1, powers := [(2, 1), (40, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(1, 1), (5, 1), (31, 1), (36, 1), (55, 1), (57, 1)] }, { coefficient := -1, powers := [(1, 1), (5, 1), (31, 1), (39, 1), (54, 1), (55, 1)] }, { coefficient := -1, powers := [(1, 1), (5, 1), (31, 1), (44, 1), (50, 1), (55, 1)] }, { coefficient := -1, powers := [(2, 1), (6, 1), (37, 1), (57, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (35, 1), (37, 1), (57, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (37, 1), (58, 1)] }, { coefficient := -1, powers := [(4, 1), (5, 1), (31, 1), (33, 1), (50, 1), (55, 1)] }, { coefficient := -1, powers := [(5, 1), (7, 1), (30, 1), (31, 1), (44, 1), (55, 1)] }, { coefficient := -1, powers := [(5, 1), (15, 1), (20, 1), (31, 1), (50, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (15, 1), (26, 1), (31, 1), (50, 1), (55, 1)] }, { coefficient := -1, powers := [(8, 1), (23, 1), (31, 1), (46, 1), (50, 1)] }, { coefficient := -1, powers := [(8, 1), (34, 1), (35, 1), (40, 1), (57, 1)] }, { coefficient := -1, powers := [(8, 1), (34, 1), (40, 1)] }, { coefficient := -1, powers := [(12, 1), (17, 1), (34, 1), (37, 1), (44, 1)] }, { coefficient := -1, powers := [(16, 1), (23, 1), (31, 1), (37, 1), (50, 1)] }]
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
    (values : Fin 62 → R) :
    ¬ ∀ index : Fin 36,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component14.SelectedLeafB7.selectedHasNoCommonZero

end Krenn.Component14.SelectedLeafB7
