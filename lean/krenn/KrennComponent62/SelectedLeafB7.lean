import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component62.SelectedLeafB7

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "4bbd0740c0c469320e0c917d38852ba216f489b6320e51446ee358dea319d86d"
def certificateSHA256 : String := "ad5bf9451284966a1557f6f5ff0280a800c7f27ef40746a9952cc0b42d279f91"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 38 → Fin 661 := ![
  1,
  4,
  5,
  17,
  18,
  21,
  133,
  135,
  137,
  153,
  158,
  159,
  172,
  208,
  256,
  294,
  296,
  298,
  300,
  309,
  316,
  318,
  322,
  390,
  396,
  440,
  443,
  453,
  454,
  458,
  480,
  544,
  557,
  619,
  657,
  658,
  659,
  660
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 38 → SparsePoly (Fin 63) := ![
  [{ coefficient := 1, powers := [(2, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (53, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (45, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (52, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (18, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (50, 1)] }, { coefficient := 1, powers := [(22, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (52, 1)] }, { coefficient := 1, powers := [(27, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (34, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (24, 1), (45, 1)] }, { coefficient := 1, powers := [(14, 1), (19, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (25, 1), (52, 1)] }, { coefficient := -1, powers := [(20, 1), (24, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1)] }, { coefficient := 1, powers := [(19, 1), (41, 1)] }, { coefficient := 1, powers := [(23, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (53, 1)] }, { coefficient := 1, powers := [(18, 1), (53, 1)] }, { coefficient := 1, powers := [(24, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (45, 1)] }, { coefficient := 1, powers := [(10, 1), (25, 1), (45, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (52, 1)] }, { coefficient := 1, powers := [(10, 1), (25, 1), (52, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (43, 1)] }, { coefficient := 1, powers := [(12, 1), (55, 1)] }, { coefficient := 1, powers := [(16, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1), (53, 1)] }, { coefficient := 1, powers := [(24, 1), (43, 1), (48, 1)] }, { coefficient := 1, powers := [(53, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1), (50, 1)] }, { coefficient := 1, powers := [(19, 1), (41, 1), (50, 1)] }, { coefficient := 1, powers := [(46, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (36, 1), (59, 1)] }, { coefficient := 1, powers := [(1, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(1, 1), (46, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (18, 1), (55, 1)] }, { coefficient := 1, powers := [(12, 1)] }, { coefficient := 1, powers := [(16, 1), (18, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (24, 1), (45, 1)] }, { coefficient := 1, powers := [(16, 1), (19, 1), (53, 1)] }, { coefficient := 1, powers := [(16, 1), (24, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (58, 1)] }, { coefficient := 1, powers := [(16, 1), (19, 1), (50, 1)] }, { coefficient := 1, powers := [(16, 1), (19, 1), (55, 1)] }, { coefficient := 1, powers := [(16, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (58, 1)] }, { coefficient := 1, powers := [(16, 1), (24, 1), (38, 1)] }, { coefficient := 1, powers := [(16, 1), (24, 1), (43, 1)] }, { coefficient := 1, powers := [(16, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (38, 1)] }, { coefficient := 1, powers := [(16, 1), (43, 1)] }, { coefficient := 1, powers := [(16, 1), (50, 1)] }, { coefficient := 1, powers := [(16, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (53, 1)] }, { coefficient := 1, powers := [(27, 1), (39, 1)] }, { coefficient := 1, powers := [(27, 1), (45, 1), (48, 1)] }, { coefficient := 1, powers := [(30, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (36, 1), (58, 1)] }, { coefficient := 1, powers := [(0, 1), (45, 1), (52, 1)] }, { coefficient := 1, powers := [(19, 1), (52, 1)] }, { coefficient := 1, powers := [(24, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1), (50, 1)] }, { coefficient := 1, powers := [(19, 1), (50, 1)] }, { coefficient := 1, powers := [(19, 1), (55, 1)] }, { coefficient := 1, powers := [(45, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (19, 1), (55, 1)] }, { coefficient := 1, powers := [(12, 1), (45, 1)] }, { coefficient := 1, powers := [(16, 1), (19, 1), (51, 1)] }, { coefficient := 1, powers := [(16, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (41, 1), (52, 1)] }, { coefficient := 1, powers := [(22, 1), (56, 1)] }, { coefficient := 1, powers := [(27, 1), (46, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (36, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (45, 1), (52, 1)] }, { coefficient := 1, powers := [(5, 1), (27, 1), (58, 1)] }, { coefficient := 1, powers := [(8, 1), (22, 1), (58, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1), (52, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (36, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (46, 1), (53, 1)] }, { coefficient := 1, powers := [(5, 1), (27, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (53, 1)] }, { coefficient := 1, powers := [(8, 1), (22, 1), (59, 1)] }, { coefficient := 1, powers := [(8, 1), (30, 1), (46, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (39, 1)] }, { coefficient := 1, powers := [(12, 1), (22, 1), (56, 1)] }, { coefficient := 1, powers := [(12, 1), (27, 1), (46, 1)] }, { coefficient := 1, powers := [(12, 1), (33, 1), (36, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (53, 1)] }, { coefficient := 1, powers := [(17, 1), (27, 1), (39, 1)] }, { coefficient := 1, powers := [(17, 1), (30, 1), (36, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (60, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1), (61, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (62, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 38 → SparsePoly (Fin 63) := ![
  [{ coefficient := -2, powers := [(5, 1), (18, 1), (33, 1), (34, 1), (53, 1), (58, 1), (62, 1)] }, { coefficient := -2, powers := [(12, 1), (18, 1), (33, 1), (34, 1), (45, 1), (52, 1), (62, 1)] }, { coefficient := 2, powers := [(12, 1), (19, 1), (33, 1), (34, 1), (52, 1), (62, 1)] }, { coefficient := 2, powers := [(16, 1), (18, 1), (19, 1), (33, 1), (34, 1), (53, 1), (55, 1), (62, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (16, 1), (30, 1), (34, 1), (45, 1), (56, 1), (62, 1)] }, { coefficient := -2, powers := [(2, 1), (23, 1), (34, 1), (46, 1), (53, 1), (58, 1), (62, 1)] }, { coefficient := -2, powers := [(8, 1), (23, 1), (30, 1), (34, 1), (46, 1), (58, 1), (62, 1)] }, { coefficient := -2, powers := [(12, 1), (24, 1), (33, 1), (34, 1), (45, 1), (62, 1)] }, { coefficient := -2, powers := [(16, 1), (24, 1), (33, 1), (34, 1), (39, 1), (62, 1)] }],
  [{ coefficient := -2, powers := [(16, 1), (18, 1), (33, 1), (34, 1), (45, 1), (52, 1), (62, 1)] }, { coefficient := -2, powers := [(16, 1), (23, 1), (33, 1), (34, 1), (45, 1), (52, 1), (62, 1)] }],
  [{ coefficient := -2, powers := [(2, 1), (20, 1), (34, 1), (46, 1), (58, 1), (61, 1)] }],
  [{ coefficient := 2, powers := [(12, 1), (34, 1), (52, 1), (58, 1)] }],
  [{ coefficient := 2, powers := [(17, 1), (34, 1), (45, 1), (58, 1)] }],
  [{ coefficient := 2, powers := [(2, 1), (34, 1), (46, 1), (58, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (2, 1), (34, 1), (52, 1), (59, 1), (60, 1), (62, 1)] }, { coefficient := 2, powers := [(12, 1), (24, 1), (33, 1), (34, 1), (50, 1), (62, 1)] }, { coefficient := 2, powers := [(12, 1), (24, 1), (33, 1), (34, 1), (55, 1), (62, 1)] }, { coefficient := 1, powers := [(34, 1), (52, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (2, 1), (34, 1), (45, 1), (59, 1), (60, 1), (62, 1)] }, { coefficient := 1, powers := [(34, 1), (45, 1), (59, 1)] }],
  [{ coefficient := 2, powers := [(33, 1), (34, 1), (45, 1), (51, 1), (52, 1)] }],
  [{ coefficient := -2, powers := [(12, 1), (16, 1), (24, 1), (33, 1), (34, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (2, 1), (16, 1), (34, 1), (59, 1), (60, 1), (62, 1)] }, { coefficient := 1, powers := [(16, 1), (34, 1), (59, 1)] }],
  [{ coefficient := 2, powers := [(62, 1)] }],
  [{ coefficient := 2, powers := [(2, 1), (20, 1), (34, 1), (59, 1), (60, 1), (61, 1)] }, { coefficient := 2, powers := [(2, 1), (25, 1), (34, 1), (59, 1), (60, 1), (61, 1)] }],
  [{ coefficient := 2, powers := [(2, 1), (10, 1), (34, 1), (59, 1), (60, 1), (61, 1)] }, { coefficient := -2, powers := [(2, 1), (14, 1), (34, 1), (59, 1), (60, 1), (61, 1)] }],
  [{ coefficient := 2, powers := [(2, 1), (34, 1), (50, 1), (53, 1), (58, 1)] }, { coefficient := 2, powers := [(8, 1), (30, 1), (34, 1), (50, 1), (58, 1)] }],
  [{ coefficient := 2, powers := [(5, 1), (33, 1), (34, 1), (43, 1), (58, 1)] }, { coefficient := -2, powers := [(16, 1), (19, 1), (33, 1), (34, 1), (43, 1), (55, 1)] }],
  [{ coefficient := -2, powers := [(2, 1), (24, 1), (34, 1), (59, 1), (60, 1), (61, 1)] }],
  [{ coefficient := -2, powers := [(2, 1), (19, 1), (34, 1), (59, 1), (60, 1), (61, 1)] }],
  [{ coefficient := 2, powers := [(18, 1), (33, 1), (34, 1), (45, 1), (52, 1)] }, { coefficient := -2, powers := [(19, 1), (33, 1), (34, 1), (52, 1)] }],
  [{ coefficient := -2, powers := [(5, 1), (33, 1), (34, 1), (58, 1)] }, { coefficient := 2, powers := [(16, 1), (19, 1), (33, 1), (34, 1), (55, 1)] }],
  [{ coefficient := -2, powers := [(2, 1), (34, 1), (53, 1), (58, 1)] }, { coefficient := -2, powers := [(8, 1), (30, 1), (34, 1), (58, 1)] }],
  [{ coefficient := -2, powers := [(2, 1), (34, 1), (58, 1), (61, 1)] }],
  [{ coefficient := -2, powers := [(33, 1), (34, 1), (45, 1), (52, 1)] }],
  [{ coefficient := -2, powers := [(33, 1), (34, 1), (55, 1)] }],
  [{ coefficient := -2, powers := [(30, 1), (34, 1), (56, 1)] }],
  [{ coefficient := -2, powers := [(33, 1), (34, 1), (39, 1)] }],
  [{ coefficient := 2, powers := [(24, 1), (33, 1), (34, 1), (39, 1)] }],
  [{ coefficient := -2, powers := [(17, 1), (34, 1), (58, 1)] }],
  [{ coefficient := 2, powers := [(2, 1), (34, 1), (59, 1), (60, 1)] }],
  [{ coefficient := 2, powers := [(16, 1), (30, 1), (34, 1), (56, 1)] }],
  [{ coefficient := 2, powers := [(33, 1), (34, 1), (52, 1)] }],
  [{ coefficient := -2, powers := [(12, 1), (34, 1), (58, 1)] }],
  [{ coefficient := -2, powers := [(34, 1), (59, 1)] }],
  [{ coefficient := 2, powers := [(34, 1), (58, 1)] }],
  [{ coefficient := -2, powers := [(2, 1), (34, 1), (36, 1), (58, 1), (59, 1)] }],
  [{ coefficient := 2, powers := [(2, 1), (19, 1), (34, 1), (52, 1), (59, 1), (60, 1)] }, { coefficient := 2, powers := [(2, 1), (24, 1), (34, 1), (45, 1), (59, 1), (60, 1)] }, { coefficient := 2, powers := [(2, 1), (34, 1), (36, 1), (58, 1), (59, 1)] }, { coefficient := 2, powers := [(2, 1), (34, 1), (39, 1), (56, 1), (58, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (2, 1), (34, 1), (45, 1), (52, 1), (59, 1), (60, 1)] }, { coefficient := 2, powers := [(0, 1), (16, 1), (30, 1), (34, 1), (45, 1), (50, 1), (56, 1)] }, { coefficient := 2, powers := [(2, 1), (23, 1), (34, 1), (46, 1), (50, 1), (53, 1), (58, 1)] }, { coefficient := 2, powers := [(5, 1), (18, 1), (33, 1), (34, 1), (43, 1), (53, 1), (58, 1)] }, { coefficient := 2, powers := [(8, 1), (23, 1), (30, 1), (34, 1), (46, 1), (50, 1), (58, 1)] }, { coefficient := 2, powers := [(12, 1), (18, 1), (33, 1), (34, 1), (43, 1), (45, 1), (52, 1)] }, { coefficient := -2, powers := [(12, 1), (19, 1), (33, 1), (34, 1), (43, 1), (52, 1)] }, { coefficient := -2, powers := [(12, 1), (24, 1), (33, 1), (34, 1), (45, 1), (55, 1)] }, { coefficient := -2, powers := [(16, 1), (18, 1), (19, 1), (33, 1), (34, 1), (43, 1), (53, 1), (55, 1)] }, { coefficient := 2, powers := [(16, 1), (18, 1), (33, 1), (34, 1), (45, 1), (51, 1), (52, 1)] }, { coefficient := 2, powers := [(16, 1), (23, 1), (33, 1), (34, 1), (45, 1), (51, 1), (52, 1)] }, { coefficient := 2, powers := [(16, 1), (24, 1), (33, 1), (34, 1), (39, 1), (50, 1)] }, { coefficient := -2, powers := [(34, 1), (58, 1)] }, { coefficient := -2, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
/-- Lean replays the exact selected-row integer certificate. -/
theorem constantIdentity :
    ∑ index, (multipliers index).toPoly *
      (selectedEquations index).toPoly = C (2 : ℤ) := by
  simp (config := { maxSteps := 1000000 })
    [Fin.sum_univ_succ, multipliers, selectedEquations,
    SparsePoly.toPoly, SparseTerm.toPoly]
  ring

/-- The selected rows have no common zero in a characteristic-zero ring. -/
theorem selectedHasNoCommonZero {R : Type*} [CommRing R] [Nontrivial R] [CharZero R]
    (values : Fin 63 → R) :
    ¬ ∀ index : Fin 38,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((2 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (2 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (2 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component62.SelectedLeafB7.selectedHasNoCommonZero

end Krenn.Component62.SelectedLeafB7
