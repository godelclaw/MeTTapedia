import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component12.SelectedLeafB6

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "e756d365e40ccbfaa2cac8ad44c4b533dd4429b6f22ba7df8ecf369256475a69"
def certificateSHA256 : String := "28c1f658d7f28ff48d926150f03d19190505d02e77548e6f62608dd5bd374f21"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 31 → Fin 616 := ![
  0,
  1,
  2,
  3,
  10,
  11,
  16,
  17,
  25,
  35,
  149,
  201,
  202,
  209,
  211,
  292,
  309,
  335,
  338,
  339,
  340,
  350,
  405,
  407,
  485,
  486,
  549,
  561,
  612,
  614,
  615
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 31 → SparsePoly (Fin 61) := ![
  [{ coefficient := 1, powers := [(1, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (33, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (23, 1)] }],
  [{ coefficient := 1, powers := [(15, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(15, 1), (31, 1), (35, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (31, 1)] }, { coefficient := 1, powers := [(31, 1), (35, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (23, 1)] }, { coefficient := 1, powers := [(15, 1), (18, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (44, 1)] }, { coefficient := 1, powers := [(12, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (39, 1)] }, { coefficient := 1, powers := [(17, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (18, 1), (54, 1)] }, { coefficient := 1, powers := [(12, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (23, 1), (39, 1)] }, { coefficient := 1, powers := [(17, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (44, 1)] }, { coefficient := 1, powers := [(4, 1), (33, 1)] }, { coefficient := 1, powers := [(15, 1), (20, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (47, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (52, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1)] }, { coefficient := 1, powers := [(12, 1), (28, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (58, 1)] }, { coefficient := 1, powers := [(12, 1), (47, 1)] }, { coefficient := 1, powers := [(17, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (52, 1)] }, { coefficient := 1, powers := [(28, 1), (40, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (33, 1), (52, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (40, 1)] }, { coefficient := 1, powers := [(12, 1), (33, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (22, 1), (57, 1)] }, { coefficient := 1, powers := [(22, 1)] }, { coefficient := 1, powers := [(26, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (35, 1), (57, 1)] }, { coefficient := 1, powers := [(1, 1)] }, { coefficient := 1, powers := [(11, 1), (33, 1), (35, 1)] }, { coefficient := 1, powers := [(15, 1), (30, 1), (35, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (37, 1), (57, 1)] }, { coefficient := 1, powers := [(1, 1), (46, 1), (51, 1)] }, { coefficient := 1, powers := [(11, 1), (33, 1), (37, 1)] }, { coefficient := 1, powers := [(15, 1), (30, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (42, 1), (51, 1)] }, { coefficient := 1, powers := [(22, 1), (55, 1)] }, { coefficient := 1, powers := [(28, 1), (47, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1)] }, { coefficient := 1, powers := [(6, 1), (57, 1)] }, { coefficient := 1, powers := [(23, 1), (39, 1)] }, { coefficient := 1, powers := [(23, 1), (44, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (37, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (40, 1), (55, 1)] }, { coefficient := 1, powers := [(2, 1), (47, 1), (52, 1)] }, { coefficient := 1, powers := [(5, 1), (28, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (52, 1)] }, { coefficient := 1, powers := [(8, 1), (22, 1), (58, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1), (47, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (40, 1)] }, { coefficient := 1, powers := [(12, 1), (22, 1), (55, 1)] }, { coefficient := 1, powers := [(12, 1), (28, 1), (47, 1)] }, { coefficient := 1, powers := [(12, 1), (34, 1), (37, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (52, 1)] }, { coefficient := 1, powers := [(17, 1), (28, 1), (40, 1)] }, { coefficient := 1, powers := [(17, 1), (31, 1), (37, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1), (60, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 31 → SparsePoly (Fin 61) := ![
  [{ coefficient := -1, powers := [(8, 1), (26, 1), (58, 1), (60, 1)] }],
  [{ coefficient := -2, powers := [(12, 1), (28, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (12, 1), (34, 1), (35, 1), (44, 1), (46, 1), (60, 1)] }, { coefficient := -1, powers := [(12, 1), (22, 1), (42, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(17, 1), (22, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (4, 1), (34, 1), (52, 1), (60, 1)] }, { coefficient := 1, powers := [(6, 1), (11, 1), (31, 1), (55, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (6, 1), (31, 1), (55, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(1, 1), (6, 1), (34, 1), (40, 1), (60, 1)] }, { coefficient := -1, powers := [(6, 1), (22, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (11, 1), (20, 1), (34, 1), (37, 1), (44, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (8, 1), (20, 1), (34, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(1, 1), (8, 1), (34, 1), (39, 1), (60, 1)] }, { coefficient := -1, powers := [(1, 1), (8, 1), (34, 1), (44, 1), (60, 1)] }, { coefficient := -1, powers := [(17, 1), (28, 1), (50, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (30, 1), (55, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(1, 1), (5, 1), (55, 1), (57, 1), (60, 1)] }, { coefficient := -1, powers := [(5, 1), (11, 1), (33, 1), (55, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (12, 1), (20, 1), (34, 1), (37, 1), (44, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (15, 1), (18, 1), (20, 1), (34, 1), (37, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (28, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (15, 1), (20, 1), (34, 1), (37, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(28, 1), (40, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (8, 1), (34, 1), (40, 1), (60, 1)] }, { coefficient := -1, powers := [(0, 1), (12, 1), (34, 1), (37, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(52, 1)] }],
  [{ coefficient := 1, powers := [(47, 1)] }],
  [{ coefficient := 1, powers := [(28, 1)] }],
  [{ coefficient := 1, powers := [(17, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (4, 1), (34, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (12, 1), (34, 1), (37, 1), (44, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (55, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (12, 1), (34, 1), (35, 1), (44, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(12, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (8, 1), (34, 1), (40, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(5, 1), (31, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (26, 1), (46, 1), (58, 1)] }, { coefficient := -1, powers := [(8, 1), (34, 1), (40, 1)] }, { coefficient := 1, powers := [(12, 1), (22, 1), (42, 1), (51, 1)] }, { coefficient := 2, powers := [(12, 1), (28, 1), (47, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(37, 1), (58, 1)] }, { coefficient := 1, powers := [(40, 1), (55, 1)] }, { coefficient := -1, powers := [(47, 1), (52, 1)] }]
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
    ¬ ∀ index : Fin 31,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component12.SelectedLeafB6.selectedHasNoCommonZero

end Krenn.Component12.SelectedLeafB6
