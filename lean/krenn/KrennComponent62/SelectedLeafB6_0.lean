import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component62.SelectedLeafB6_0

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "1912cb28804ad4562c4596a28578674ca068c3b8a64d0f427ecfd527d3af53cd"
def certificateSHA256 : String := "511246182e5513ecccf07249a3d7c382f10cc6d538cc9b3d8d220baba812a527"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 26 → Fin 664 := ![
  10,
  11,
  17,
  18,
  21,
  128,
  129,
  133,
  135,
  137,
  160,
  191,
  301,
  302,
  309,
  390,
  454,
  557,
  578,
  609,
  619,
  657,
  659,
  660,
  662,
  663
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 26 → SparsePoly (Fin 62) := ![
  [{ coefficient := 1, powers := [(10, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (41, 1)] }, { coefficient := 1, powers := [(10, 1), (25, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (44, 1)] }, { coefficient := 1, powers := [(10, 1), (25, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (53, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (45, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (52, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (38, 1)] }, { coefficient := 1, powers := [(27, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (22, 1), (58, 1)] }, { coefficient := 1, powers := [(22, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (46, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (53, 1)] }, { coefficient := 1, powers := [(8, 1), (30, 1)] }, { coefficient := 1, powers := [(12, 1), (27, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (43, 1)] }, { coefficient := 1, powers := [(12, 1), (55, 1)] }, { coefficient := 1, powers := [(16, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (18, 1), (55, 1)] }, { coefficient := 1, powers := [(12, 1)] }, { coefficient := 1, powers := [(16, 1), (18, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (53, 1)] }, { coefficient := 1, powers := [(27, 1), (39, 1)] }, { coefficient := 1, powers := [(27, 1), (45, 1), (48, 1)] }, { coefficient := 1, powers := [(30, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (41, 1), (52, 1)] }, { coefficient := 1, powers := [(22, 1), (56, 1)] }, { coefficient := 1, powers := [(27, 1), (46, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1)] }, { coefficient := 1, powers := [(6, 1), (58, 1)] }, { coefficient := 1, powers := [(23, 1), (38, 1)] }, { coefficient := 1, powers := [(23, 1), (43, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (38, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(24, 1), (38, 1), (41, 1)] }, { coefficient := 1, powers := [(24, 1), (44, 1)] }, { coefficient := 1, powers := [(41, 1), (52, 1)] }, { coefficient := 1, powers := [(56, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (36, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (45, 1), (52, 1)] }, { coefficient := 1, powers := [(5, 1), (27, 1), (58, 1)] }, { coefficient := 1, powers := [(8, 1), (22, 1), (58, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1), (52, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (36, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (46, 1), (53, 1)] }, { coefficient := 1, powers := [(5, 1), (27, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (53, 1)] }, { coefficient := 1, powers := [(8, 1), (22, 1), (59, 1)] }, { coefficient := 1, powers := [(8, 1), (30, 1), (46, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (39, 1)] }, { coefficient := 1, powers := [(12, 1), (22, 1), (56, 1)] }, { coefficient := 1, powers := [(12, 1), (27, 1), (46, 1)] }, { coefficient := 1, powers := [(12, 1), (33, 1), (36, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (53, 1)] }, { coefficient := 1, powers := [(17, 1), (27, 1), (39, 1)] }, { coefficient := 1, powers := [(17, 1), (30, 1), (36, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1), (61, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(38, 1)] }],
  [{ coefficient := 1, powers := [(39, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 26 → SparsePoly (Fin 62) := ![
  [{ coefficient := 1, powers := [(5, 1), (25, 1), (30, 1), (52, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (5, 1), (25, 1), (30, 1), (52, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (24, 1), (25, 1), (30, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (20, 1), (22, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(17, 1), (45, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (30, 1), (52, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (5, 1), (30, 1), (52, 1), (61, 1)] }, { coefficient := -1, powers := [(5, 1), (24, 1), (30, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(17, 1), (22, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (52, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (45, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (5, 1), (59, 1)] }, { coefficient := -1, powers := [(5, 1), (23, 1), (59, 1)] }, { coefficient := -1, powers := [(12, 1), (18, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(53, 1)] }],
  [{ coefficient := 1, powers := [(46, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (27, 1), (46, 1)] }],
  [{ coefficient := -1, powers := [(27, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(17, 1)] }],
  [{ coefficient := 1, powers := [(12, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (27, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (30, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (5, 1), (30, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(5, 1), (24, 1), (30, 1), (44, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (41, 1), (52, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (36, 1), (58, 1), (59, 1)] }, { coefficient := -1, powers := [(6, 1), (45, 1), (52, 1), (59, 1)] }, { coefficient := 1, powers := [(36, 1), (59, 1)] }, { coefficient := 1, powers := [(39, 1), (56, 1)] }, { coefficient := -1, powers := [(46, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (5, 1), (27, 1), (59, 1)] }, { coefficient := -1, powers := [(0, 1), (5, 1), (30, 1), (56, 1)] }, { coefficient := -1, powers := [(5, 1), (24, 1), (30, 1), (41, 1)] }, { coefficient := 1, powers := [(12, 1), (18, 1), (27, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (33, 1)] }]
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
    ¬ ∀ index : Fin 26,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component62.SelectedLeafB6_0.selectedHasNoCommonZero

end Krenn.Component62.SelectedLeafB6_0
