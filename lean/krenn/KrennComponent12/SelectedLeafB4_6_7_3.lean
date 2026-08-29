import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component12.SelectedLeafB4_6_7_3

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "f62da1679d16df17d37eb22c44aa6f53973d42734ce5afc92994a03463b01c5e"
def certificateSHA256 : String := "e41a01e805bb996b9a1cecefbdc2d0b5295a339c59204afc0a4e3427706df3ea"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 24 → Fin 625 := ![
  12,
  13,
  19,
  39,
  40,
  43,
  309,
  335,
  336,
  338,
  340,
  350,
  396,
  407,
  501,
  579,
  611,
  612,
  614,
  615,
  618,
  620,
  622,
  623
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 24 → SparsePoly (Fin 67) := ![
  [{ coefficient := 1, powers := [(6, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (31, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(31, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (23, 1), (39, 1)] }, { coefficient := 1, powers := [(17, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (44, 1)] }, { coefficient := 1, powers := [(4, 1), (33, 1)] }, { coefficient := 1, powers := [(15, 1), (20, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (50, 1)] }, { coefficient := 1, powers := [(7, 1), (30, 1)] }, { coefficient := 1, powers := [(11, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (47, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (58, 1)] }, { coefficient := 1, powers := [(12, 1), (47, 1)] }, { coefficient := 1, powers := [(17, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (52, 1)] }, { coefficient := 1, powers := [(28, 1), (40, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (31, 1), (54, 1)] }, { coefficient := 1, powers := [(7, 1), (31, 1), (44, 1)] }, { coefficient := 1, powers := [(15, 1), (31, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (22, 1), (57, 1)] }, { coefficient := 1, powers := [(22, 1)] }, { coefficient := 1, powers := [(26, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (23, 1), (57, 1)] }, { coefficient := 1, powers := [(11, 1), (23, 1), (44, 1)] }, { coefficient := 1, powers := [(15, 1), (23, 1), (39, 1)] }, { coefficient := 1, powers := [(15, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (50, 1)] }, { coefficient := 1, powers := [(20, 1), (54, 1)] }, { coefficient := 1, powers := [(25, 1), (39, 1)] }, { coefficient := 1, powers := [(25, 1), (44, 1)] }, { coefficient := 1, powers := [(30, 1), (36, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (36, 1), (57, 1)] }, { coefficient := 1, powers := [(1, 1), (39, 1), (54, 1)] }, { coefficient := 1, powers := [(1, 1), (44, 1), (50, 1)] }, { coefficient := 1, powers := [(4, 1), (25, 1), (57, 1)] }, { coefficient := 1, powers := [(4, 1), (30, 1), (54, 1)] }, { coefficient := 1, powers := [(4, 1), (33, 1), (50, 1)] }, { coefficient := 1, powers := [(7, 1), (20, 1), (57, 1)] }, { coefficient := 1, powers := [(7, 1), (30, 1), (44, 1)] }, { coefficient := 1, powers := [(7, 1), (33, 1), (39, 1)] }, { coefficient := 1, powers := [(11, 1), (20, 1), (54, 1)] }, { coefficient := 1, powers := [(11, 1), (25, 1), (44, 1)] }, { coefficient := 1, powers := [(11, 1), (33, 1), (36, 1)] }, { coefficient := 1, powers := [(15, 1), (20, 1), (50, 1)] }, { coefficient := 1, powers := [(15, 1), (25, 1), (39, 1)] }, { coefficient := 1, powers := [(15, 1), (30, 1), (36, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (37, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (40, 1), (55, 1)] }, { coefficient := 1, powers := [(2, 1), (47, 1), (52, 1)] }, { coefficient := 1, powers := [(5, 1), (28, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (52, 1)] }, { coefficient := 1, powers := [(8, 1), (22, 1), (58, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1), (47, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (40, 1)] }, { coefficient := 1, powers := [(12, 1), (22, 1), (55, 1)] }, { coefficient := 1, powers := [(12, 1), (28, 1), (47, 1)] }, { coefficient := 1, powers := [(12, 1), (34, 1), (37, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (52, 1)] }, { coefficient := 1, powers := [(17, 1), (28, 1), (40, 1)] }, { coefficient := 1, powers := [(17, 1), (31, 1), (37, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1)] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(40, 1)] }],
  [{ coefficient := 1, powers := [(54, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(23, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (65, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 24 → SparsePoly (Fin 67) := ![
  [{ coefficient := -1, powers := [(8, 1), (22, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (20, 1), (30, 1), (54, 1), (55, 1), (65, 1)] }, { coefficient := 1, powers := [(5, 1), (20, 1), (55, 1), (57, 1)] }, { coefficient := -1, powers := [(5, 1), (25, 1), (44, 1), (55, 1), (57, 1), (63, 1)] }, { coefficient := -1, powers := [(5, 1), (30, 1), (44, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (39, 1), (55, 1)] }, { coefficient := -1, powers := [(5, 1), (33, 1), (44, 1), (50, 1), (55, 1), (63, 1)] }, { coefficient := -1, powers := [(5, 1), (33, 1), (44, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (55, 1), (65, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (26, 1), (58, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (31, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (11, 1), (33, 1), (55, 1)] }, { coefficient := -1, powers := [(5, 1), (15, 1), (25, 1), (55, 1), (57, 1), (63, 1)] }, { coefficient := -1, powers := [(5, 1), (15, 1), (30, 1), (55, 1)] }, { coefficient := -1, powers := [(5, 1), (15, 1), (33, 1), (50, 1), (55, 1), (63, 1)] }, { coefficient := -1, powers := [(5, 1), (15, 1), (33, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(22, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (31, 1), (54, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (20, 1), (31, 1), (54, 1), (55, 1), (65, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (44, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(52, 1)] }],
  [{ coefficient := 1, powers := [(28, 1)] }],
  [{ coefficient := 1, powers := [(17, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (25, 1), (55, 1), (57, 1), (63, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (50, 1), (55, 1), (63, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (25, 1), (31, 1), (44, 1), (55, 1)] }, { coefficient := -1, powers := [(5, 1), (31, 1), (33, 1), (36, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (15, 1), (31, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (31, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(5, 1), (20, 1), (31, 1), (50, 1), (54, 1), (55, 1), (65, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (36, 1), (55, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (39, 1), (54, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (44, 1), (54, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(37, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1)] }, { coefficient := -1, powers := [(17, 1), (28, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (5, 1), (25, 1), (31, 1), (55, 1), (57, 1)] }, { coefficient := -1, powers := [(4, 1), (5, 1), (31, 1), (33, 1), (50, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (5, 1), (25, 1), (31, 1), (44, 1), (55, 1), (57, 1)] }, { coefficient := 1, powers := [(4, 1), (5, 1), (31, 1), (33, 1), (36, 1), (55, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (11, 1), (25, 1), (31, 1), (44, 2), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (11, 1), (31, 1), (33, 1), (36, 1), (44, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (15, 1), (25, 1), (31, 1), (39, 1), (44, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (15, 1), (31, 1), (33, 1), (36, 1), (39, 1), (55, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (39, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (11, 1), (20, 1), (31, 1), (54, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (26, 1), (46, 1), (58, 1)] }, { coefficient := -1, powers := [(8, 1), (31, 1), (47, 1)] }, { coefficient := -1, powers := [(12, 1), (22, 1), (55, 1)] }, { coefficient := -1, powers := [(12, 1), (34, 1), (37, 1)] }]
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
    ¬ ∀ index : Fin 24,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component12.SelectedLeafB4_6_7_3.selectedHasNoCommonZero

end Krenn.Component12.SelectedLeafB4_6_7_3
