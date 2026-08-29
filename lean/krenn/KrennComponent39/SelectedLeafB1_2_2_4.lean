import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component39.SelectedLeafB1_2_2_4

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "30ba3a47e522d04eacd4a19e566cf95a73f64555b565066a4907f265ed303e48"
def certificateSHA256 : String := "28c3454ce898b1134605ee1d97559f51cee6e03f44286b7bbe2f2063c0014d9a"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 46 → Fin 673 := ![
  181,
  184,
  187,
  191,
  192,
  193,
  195,
  251,
  303,
  317,
  321,
  322,
  324,
  347,
  396,
  418,
  419,
  425,
  429,
  433,
  434,
  439,
  440,
  441,
  444,
  458,
  463,
  467,
  470,
  471,
  482,
  505,
  532,
  566,
  580,
  581,
  615,
  644,
  645,
  660,
  661,
  663,
  666,
  669,
  670,
  672
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 46 → SparsePoly (Fin 65) := ![
  [{ coefficient := 1, powers := [(12, 1), (24, 1)] }, { coefficient := 1, powers := [(16, 1), (18, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (45, 1)] }, { coefficient := 1, powers := [(17, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (18, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (54, 1)] }, { coefficient := 1, powers := [(28, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (42, 1)] }, { coefficient := 1, powers := [(26, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (53, 1)] }, { coefficient := 1, powers := [(28, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(26, 1), (52, 1)] }, { coefficient := -1, powers := [(27, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (23, 1), (45, 1)] }, { coefficient := 1, powers := [(17, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (54, 1)] }, { coefficient := 1, powers := [(18, 1), (54, 1)] }, { coefficient := 1, powers := [(24, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (51, 1)] }, { coefficient := 1, powers := [(22, 1), (56, 1)] }, { coefficient := 1, powers := [(27, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1), (49, 1)] }, { coefficient := 1, powers := [(23, 1), (44, 1), (49, 1)] }, { coefficient := 1, powers := [(49, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1), (54, 1)] }, { coefficient := 1, powers := [(24, 1), (44, 1), (49, 1)] }, { coefficient := 1, powers := [(54, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1), (51, 1)] }, { coefficient := 1, powers := [(19, 1), (42, 1), (51, 1)] }, { coefficient := 1, powers := [(47, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (45, 1), (49, 1)] }, { coefficient := 1, powers := [(12, 1), (26, 1), (45, 1)] }, { coefficient := 1, powers := [(17, 1), (27, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (23, 1), (39, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1), (44, 1)] }, { coefficient := 1, powers := [(16, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (46, 1)] }, { coefficient := 1, powers := [(5, 1), (26, 1), (59, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1)] }, { coefficient := 1, powers := [(16, 1), (26, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (47, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1)] }, { coefficient := 1, powers := [(16, 1), (26, 1), (47, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1)] }, { coefficient := 1, powers := [(12, 1), (28, 1)] }, { coefficient := 1, powers := [(16, 1), (21, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (59, 1)] }, { coefficient := 1, powers := [(16, 1), (19, 1), (51, 1)] }, { coefficient := 1, powers := [(16, 1), (19, 1), (56, 1)] }, { coefficient := 1, powers := [(16, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (59, 1)] }, { coefficient := 1, powers := [(16, 1), (24, 1), (39, 1)] }, { coefficient := 1, powers := [(16, 1), (24, 1), (44, 1)] }, { coefficient := 1, powers := [(16, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (60, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (45, 1)] }, { coefficient := 1, powers := [(12, 1), (57, 1)] }, { coefficient := 1, powers := [(17, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (39, 1)] }, { coefficient := 1, powers := [(16, 1), (44, 1)] }, { coefficient := 1, powers := [(16, 1), (51, 1)] }, { coefficient := 1, powers := [(16, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (54, 1)] }, { coefficient := 1, powers := [(28, 1), (40, 1)] }, { coefficient := 1, powers := [(28, 1), (46, 1), (49, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (39, 1)] }, { coefficient := 1, powers := [(27, 1), (44, 1)] }, { coefficient := 1, powers := [(27, 1), (51, 1)] }, { coefficient := 1, powers := [(27, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (36, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (45, 1), (52, 1)] }, { coefficient := 1, powers := [(42, 1), (52, 1)] }, { coefficient := 1, powers := [(45, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1), (53, 1)] }, { coefficient := 1, powers := [(24, 1), (39, 1)] }, { coefficient := 1, powers := [(24, 1), (44, 1)] }, { coefficient := 1, powers := [(53, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1), (54, 1)] }, { coefficient := 1, powers := [(24, 1), (45, 1), (49, 1)] }, { coefficient := 1, powers := [(42, 1), (54, 1)] }, { coefficient := 1, powers := [(49, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1), (51, 1)] }, { coefficient := 1, powers := [(19, 1), (51, 1)] }, { coefficient := 1, powers := [(19, 1), (56, 1)] }, { coefficient := 1, powers := [(46, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1), (52, 1)] }, { coefficient := 1, powers := [(19, 1), (42, 1), (52, 1)] }, { coefficient := 1, powers := [(40, 1), (42, 1)] }, { coefficient := 1, powers := [(47, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1), (53, 1)] }, { coefficient := 1, powers := [(19, 1), (42, 1), (53, 1)] }, { coefficient := 1, powers := [(19, 1), (57, 1)] }, { coefficient := 1, powers := [(24, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (35, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1)] }, { coefficient := 1, powers := [(16, 1), (21, 1)] }, { coefficient := 1, powers := [(16, 1), (26, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (27, 1), (59, 1)] }, { coefficient := 1, powers := [(21, 1), (51, 1)] }, { coefficient := 1, powers := [(21, 1), (56, 1)] }, { coefficient := 1, powers := [(27, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (27, 1), (59, 1)] }, { coefficient := 1, powers := [(26, 1), (39, 1)] }, { coefficient := 1, powers := [(26, 1), (44, 1)] }, { coefficient := 1, powers := [(27, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (42, 1), (53, 1)] }, { coefficient := 1, powers := [(22, 1), (57, 1)] }, { coefficient := 1, powers := [(28, 1), (47, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1)] }, { coefficient := 1, powers := [(6, 1), (59, 1)] }, { coefficient := 1, powers := [(23, 1), (39, 1)] }, { coefficient := 1, powers := [(23, 1), (44, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (51, 1)] }, { coefficient := 1, powers := [(3, 1), (59, 1)] }, { coefficient := 1, powers := [(18, 1), (51, 1)] }, { coefficient := 1, powers := [(18, 1), (56, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (37, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (46, 1), (53, 1)] }, { coefficient := 1, powers := [(5, 1), (28, 1), (59, 1)] }, { coefficient := 1, powers := [(8, 1), (22, 1), (59, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1), (53, 1)] }, { coefficient := 1, powers := [(16, 1), (28, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (36, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (44, 1), (51, 1)] }, { coefficient := 1, powers := [(39, 1)] }, { coefficient := 1, powers := [(44, 1)] }, { coefficient := 1, powers := [(51, 1)] }, { coefficient := 1, powers := [(56, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (37, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (47, 1), (54, 1)] }, { coefficient := 1, powers := [(19, 1), (42, 1), (54, 1)] }, { coefficient := 1, powers := [(19, 1), (49, 1), (57, 1)] }, { coefficient := 1, powers := [(24, 1), (40, 1), (42, 1)] }, { coefficient := 1, powers := [(24, 1), (47, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (37, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (47, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (28, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (22, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1), (47, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (40, 1)] }, { coefficient := 1, powers := [(12, 1), (22, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1), (28, 1), (47, 1)] }, { coefficient := 1, powers := [(12, 1), (34, 1), (37, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (54, 1)] }, { coefficient := 1, powers := [(17, 1), (28, 1), (40, 1)] }, { coefficient := 1, powers := [(17, 1), (31, 1), (37, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (61, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(40, 1)] }],
  [{ coefficient := 1, powers := [(57, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (64, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(28, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 46 → SparsePoly (Fin 65) := ![
  [{ coefficient := -1, powers := [(22, 1), (35, 1), (45, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (19, 1), (26, 1), (35, 1), (53, 1), (59, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (27, 1), (51, 1), (61, 1)] }, { coefficient := 1, powers := [(18, 1), (27, 1), (56, 1), (61, 1)] }, { coefficient := -1, powers := [(21, 1), (51, 1), (61, 1)] }, { coefficient := -1, powers := [(21, 1), (56, 1), (61, 1)] }, { coefficient := -1, powers := [(27, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (35, 1), (47, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (35, 1), (54, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (35, 1), (42, 1), (59, 1)] }, { coefficient := 1, powers := [(16, 1), (35, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (17, 1), (19, 1), (35, 1), (53, 1), (59, 1), (61, 1)] }],
  [{ coefficient := 2, powers := [(22, 1), (24, 1), (35, 1), (59, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (22, 1), (35, 1), (45, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(16, 1), (23, 1), (35, 1), (53, 1), (60, 1)] }],
  [{ coefficient := -2, powers := [(17, 1), (22, 1), (24, 1), (35, 1), (59, 1), (64, 1)] }],
  [{ coefficient := 2, powers := [(17, 1), (22, 1), (23, 1), (35, 1), (59, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (35, 1), (49, 1), (53, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (35, 1), (54, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (19, 1), (35, 1), (53, 1), (59, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (27, 1), (61, 1)] }, { coefficient := -1, powers := [(21, 1), (61, 1)] }, { coefficient := -1, powers := [(22, 1), (35, 1), (53, 1), (60, 1)] }, { coefficient := 1, powers := [(23, 1), (27, 1), (35, 1), (46, 1), (53, 1), (60, 1)] }, { coefficient := 1, powers := [(23, 1), (27, 1), (61, 1)] }, { coefficient := -1, powers := [(26, 1), (35, 1), (46, 1), (53, 1), (60, 1)] }, { coefficient := -1, powers := [(26, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(35, 1), (53, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(35, 1), (54, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(35, 1), (47, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(26, 1), (35, 1), (53, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (35, 1), (60, 1)] }],
  [{ coefficient := -2, powers := [(22, 1), (23, 1), (35, 1), (59, 1), (64, 1)] }, { coefficient := 1, powers := [(22, 1), (35, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(18, 1), (23, 1), (27, 1), (61, 1)] }, { coefficient := 1, powers := [(21, 1), (23, 1), (61, 1)] }, { coefficient := 1, powers := [(22, 1), (23, 1), (35, 1), (53, 1), (60, 1)] }, { coefficient := -1, powers := [(22, 1), (24, 1), (35, 1), (60, 1)] }, { coefficient := -1, powers := [(23, 2), (27, 1), (35, 1), (46, 1), (53, 1), (60, 1)] }, { coefficient := -1, powers := [(23, 2), (27, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(17, 1), (35, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (23, 2), (35, 1), (46, 1), (53, 1), (60, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 2), (61, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (19, 1), (35, 1), (53, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(16, 1), (22, 1), (35, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(16, 1), (22, 1), (35, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (26, 1), (35, 1), (53, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (35, 1), (53, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (35, 1), (49, 1), (51, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(61, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (18, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (23, 1), (35, 1), (46, 1), (53, 1), (60, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (35, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(16, 1), (23, 1), (27, 1), (35, 1), (46, 1), (53, 1), (60, 1)] }, { coefficient := -1, powers := [(16, 1), (23, 1), (27, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(16, 1), (18, 1), (27, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(35, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (22, 1), (24, 1), (35, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (35, 1), (51, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(35, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (19, 1), (35, 1), (36, 1), (53, 1), (59, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (19, 1), (35, 1), (45, 1), (52, 1), (53, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (35, 1), (37, 1), (51, 1), (59, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (35, 1), (40, 1), (51, 1), (57, 1), (59, 1)] }, { coefficient := -1, powers := [(2, 1), (35, 1), (47, 1), (52, 1), (53, 1), (59, 1)] }, { coefficient := 1, powers := [(16, 1), (18, 1), (27, 1), (51, 1), (61, 1)] }, { coefficient := -1, powers := [(16, 1), (22, 1), (24, 1), (35, 1), (36, 1), (59, 1), (60, 1)] }, { coefficient := -1, powers := [(16, 1), (22, 1), (24, 1), (35, 1), (39, 1), (56, 1), (60, 1)] }, { coefficient := -1, powers := [(16, 1), (22, 1), (24, 1), (35, 1), (44, 1), (51, 1), (60, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1), (35, 1), (44, 1), (53, 1), (60, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1), (27, 1), (35, 1), (44, 1), (46, 1), (53, 1), (60, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1), (27, 1), (44, 1), (61, 1)] }, { coefficient := -1, powers := [(16, 1), (26, 1), (35, 1), (46, 1), (51, 1), (53, 1), (60, 1)] }, { coefficient := -2, powers := [(17, 1), (22, 1), (23, 1), (35, 1), (44, 1), (54, 1), (59, 1), (64, 1)] }, { coefficient := 2, powers := [(17, 1), (22, 1), (24, 1), (35, 1), (44, 1), (49, 1), (59, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (19, 1), (35, 1), (45, 1), (49, 1), (53, 1), (59, 1)] }, { coefficient := -1, powers := [(35, 1), (59, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (24, 1), (35, 1), (42, 1), (51, 1), (59, 1)] }, { coefficient := -1, powers := [(2, 1), (35, 1), (42, 1), (53, 1), (59, 1)] }, { coefficient := -1, powers := [(8, 1), (34, 1), (35, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (35, 1), (40, 1), (59, 1)] }, { coefficient := -1, powers := [(5, 1), (31, 1), (35, 1), (59, 1)] }, { coefficient := 2, powers := [(12, 1), (22, 1), (23, 1), (35, 1), (59, 1), (64, 1)] }, { coefficient := -1, powers := [(12, 1), (22, 1), (35, 1), (59, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1), (35, 1), (49, 1), (59, 1)] }],
  [{ coefficient := 2, powers := [(8, 1), (22, 1), (35, 1), (59, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (35, 1), (42, 1), (46, 1), (59, 1)] }, { coefficient := 1, powers := [(12, 1), (35, 1), (47, 1), (59, 1)] }, { coefficient := -1, powers := [(16, 1), (35, 1), (47, 1), (49, 1), (59, 1)] }, { coefficient := 1, powers := [(17, 1), (35, 1), (46, 1), (49, 1), (59, 1)] }]
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
    (values : Fin 65 → R) :
    ¬ ∀ index : Fin 46,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component39.SelectedLeafB1_2_2_4.selectedHasNoCommonZero

end Krenn.Component39.SelectedLeafB1_2_2_4
