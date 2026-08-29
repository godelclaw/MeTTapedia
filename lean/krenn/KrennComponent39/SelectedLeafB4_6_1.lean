import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component39.SelectedLeafB4_6_1

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "118b6b6cba7b3b91935d869302429b44e3c59d472acf44095df9ec44f7d0115e"
def certificateSHA256 : String := "e5e0f86545397922f3c8a97c31acc8f7271997a300e99949ac773a56693f27ea"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 38 → Fin 670 := ![
  10,
  22,
  26,
  181,
  183,
  187,
  191,
  193,
  250,
  254,
  276,
  280,
  302,
  303,
  305,
  313,
  322,
  382,
  412,
  425,
  430,
  434,
  440,
  463,
  502,
  523,
  566,
  603,
  608,
  618,
  659,
  660,
  661,
  662,
  663,
  666,
  668,
  669
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 38 → SparsePoly (Fin 65) := ![
  [{ coefficient := 1, powers := [(5, 1), (33, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (24, 1)] }, { coefficient := 1, powers := [(16, 1), (18, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (42, 1)] }, { coefficient := 1, powers := [(17, 1), (18, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (18, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (54, 1)] }, { coefficient := 1, powers := [(28, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (53, 1)] }, { coefficient := 1, powers := [(28, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (23, 1), (44, 1)] }, { coefficient := 1, powers := [(16, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (24, 1), (44, 1)] }, { coefficient := 1, powers := [(16, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (23, 1), (42, 1)] }, { coefficient := 1, powers := [(17, 1), (18, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (42, 1), (53, 1)] }, { coefficient := 1, powers := [(20, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (49, 1)] }, { coefficient := 1, powers := [(18, 1), (49, 1)] }, { coefficient := 1, powers := [(23, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (54, 1)] }, { coefficient := 1, powers := [(18, 1), (54, 1)] }, { coefficient := 1, powers := [(24, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (51, 1)] }, { coefficient := 1, powers := [(7, 1), (30, 1)] }, { coefficient := 1, powers := [(10, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (44, 1)] }, { coefficient := 1, powers := [(12, 1), (56, 1)] }, { coefficient := 1, powers := [(16, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1), (54, 1)] }, { coefficient := 1, powers := [(24, 1), (44, 1), (49, 1)] }, { coefficient := 1, powers := [(54, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (18, 1), (56, 1)] }, { coefficient := 1, powers := [(12, 1)] }, { coefficient := 1, powers := [(16, 1), (18, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (52, 1)] }, { coefficient := 1, powers := [(18, 1), (49, 1), (56, 1)] }, { coefficient := 1, powers := [(18, 1), (52, 1)] }, { coefficient := 1, powers := [(49, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1)] }, { coefficient := 1, powers := [(12, 1), (28, 1)] }, { coefficient := 1, powers := [(16, 1), (21, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (60, 1)] }, { coefficient := 1, powers := [(12, 1), (47, 1)] }, { coefficient := 1, powers := [(17, 1), (19, 1), (52, 1)] }, { coefficient := 1, powers := [(17, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (60, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (45, 1)] }, { coefficient := 1, powers := [(12, 1), (57, 1)] }, { coefficient := 1, powers := [(17, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (54, 1)] }, { coefficient := 1, powers := [(28, 1), (40, 1)] }, { coefficient := 1, powers := [(28, 1), (46, 1), (49, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1), (54, 1)] }, { coefficient := 1, powers := [(24, 1), (45, 1), (49, 1)] }, { coefficient := 1, powers := [(42, 1), (54, 1)] }, { coefficient := 1, powers := [(49, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (25, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (30, 1), (56, 1)] }, { coefficient := 1, powers := [(3, 1), (33, 1), (51, 1)] }, { coefficient := 1, powers := [(25, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (25, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (51, 1)] }, { coefficient := 1, powers := [(16, 1), (25, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (42, 1), (53, 1)] }, { coefficient := 1, powers := [(22, 1), (57, 1)] }, { coefficient := 1, powers := [(28, 1), (47, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (51, 1)] }, { coefficient := 1, powers := [(20, 1), (56, 1)] }, { coefficient := 1, powers := [(25, 1), (39, 1)] }, { coefficient := 1, powers := [(25, 1), (44, 1)] }, { coefficient := 1, powers := [(30, 1), (36, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (40, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(19, 1), (49, 1), (56, 1)] }, { coefficient := 1, powers := [(19, 1), (52, 1)] }, { coefficient := 1, powers := [(40, 1)] }, { coefficient := 1, powers := [(46, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (42, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (21, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1), (42, 1)] }, { coefficient := 1, powers := [(12, 1), (21, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1), (28, 1), (42, 1)] }, { coefficient := 1, powers := [(17, 1), (21, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (36, 1), (59, 1)] }, { coefficient := 1, powers := [(1, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(1, 1), (44, 1), (51, 1)] }, { coefficient := 1, powers := [(4, 1), (25, 1), (59, 1)] }, { coefficient := 1, powers := [(4, 1), (30, 1), (56, 1)] }, { coefficient := 1, powers := [(4, 1), (33, 1), (51, 1)] }, { coefficient := 1, powers := [(7, 1), (20, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (30, 1), (44, 1)] }, { coefficient := 1, powers := [(7, 1), (33, 1), (39, 1)] }, { coefficient := 1, powers := [(10, 1), (20, 1), (56, 1)] }, { coefficient := 1, powers := [(10, 1), (25, 1), (44, 1)] }, { coefficient := 1, powers := [(10, 1), (33, 1), (36, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1), (51, 1)] }, { coefficient := 1, powers := [(14, 1), (25, 1), (39, 1)] }, { coefficient := 1, powers := [(14, 1), (30, 1), (36, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (37, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (47, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (28, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (22, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1), (47, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (40, 1)] }, { coefficient := 1, powers := [(12, 1), (22, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1), (28, 1), (47, 1)] }, { coefficient := 1, powers := [(12, 1), (34, 1), (37, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (54, 1)] }, { coefficient := 1, powers := [(17, 1), (28, 1), (40, 1)] }, { coefficient := 1, powers := [(17, 1), (31, 1), (37, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (61, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1)] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(40, 1)] }],
  [{ coefficient := 1, powers := [(56, 1)] }],
  [{ coefficient := 1, powers := [(57, 1), (64, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 38 → SparsePoly (Fin 65) := ![
  [{ coefficient := 1, powers := [(7, 1), (31, 1), (39, 1), (57, 1)] }, { coefficient := 1, powers := [(7, 1), (34, 1), (39, 1), (54, 1)] }, { coefficient := 1, powers := [(10, 1), (31, 1), (36, 1), (57, 1)] }, { coefficient := 1, powers := [(10, 1), (34, 1), (36, 1), (54, 1)] }, { coefficient := -1, powers := [(14, 1), (31, 1), (36, 1), (57, 1)] }, { coefficient := -1, powers := [(14, 1), (34, 1), (36, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (14, 1), (31, 1), (44, 1), (46, 1), (57, 1)] }, { coefficient := -1, powers := [(3, 1), (14, 1), (34, 1), (44, 1), (46, 1), (54, 1)] }, { coefficient := -1, powers := [(4, 1), (31, 1), (46, 1), (57, 1)] }, { coefficient := -1, powers := [(4, 1), (34, 1), (46, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (7, 1), (31, 1), (42, 1), (57, 1), (59, 1), (64, 1)] }, { coefficient := -1, powers := [(5, 1), (7, 1), (34, 1), (42, 1), (54, 1), (59, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (42, 1), (44, 1), (46, 1)] }, { coefficient := 1, powers := [(21, 1), (45, 1), (46, 1)] }, { coefficient := -1, powers := [(22, 1), (42, 1), (44, 1)] }, { coefficient := -1, powers := [(22, 1), (45, 1)] }],
  [{ coefficient := -1, powers := [(28, 1), (46, 1)] }],
  [{ coefficient := -1, powers := [(18, 1), (21, 1), (44, 1), (46, 1), (49, 1), (57, 1), (61, 1)] }, { coefficient := -1, powers := [(18, 1), (21, 1), (44, 1), (46, 1), (52, 1), (57, 1)] }, { coefficient := 1, powers := [(18, 1), (22, 1), (44, 1), (49, 1), (57, 1), (61, 1)] }, { coefficient := 1, powers := [(18, 1), (22, 1), (44, 1), (52, 1), (57, 1)] }, { coefficient := -1, powers := [(21, 1), (42, 1), (44, 1), (46, 1), (54, 1)] }, { coefficient := 2, powers := [(21, 1), (46, 1), (49, 1), (57, 1), (61, 1)] }, { coefficient := 1, powers := [(21, 1), (46, 1), (52, 1), (57, 1)] }, { coefficient := 1, powers := [(22, 1), (42, 1), (44, 1), (54, 1)] }, { coefficient := -1, powers := [(22, 1), (49, 1), (57, 1), (61, 1)] }, { coefficient := -1, powers := [(28, 1), (42, 1), (46, 1), (49, 1), (61, 1)] }, { coefficient := -2, powers := [(28, 1), (42, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(28, 1), (47, 1), (49, 1), (61, 1)] }, { coefficient := 2, powers := [(28, 1), (47, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (42, 1), (46, 1)] }, { coefficient := -1, powers := [(16, 1), (47, 1)] }, { coefficient := -1, powers := [(17, 1), (46, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (42, 1)] }],
  [{ coefficient := -1, powers := [(18, 1), (21, 1), (44, 1), (46, 1), (57, 1)] }, { coefficient := 1, powers := [(18, 1), (22, 1), (44, 1), (57, 1)] }, { coefficient := 1, powers := [(21, 1), (46, 1), (57, 1)] }, { coefficient := -2, powers := [(28, 1), (42, 1), (46, 1)] }, { coefficient := 2, powers := [(28, 1), (47, 1)] }],
  [{ coefficient := -1, powers := [(21, 1), (42, 1), (46, 1)] }, { coefficient := 1, powers := [(22, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (44, 1), (46, 1), (54, 1)] }, { coefficient := -1, powers := [(22, 1), (44, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (7, 1), (31, 1), (57, 1), (59, 1), (64, 1)] }, { coefficient := 1, powers := [(5, 1), (7, 1), (34, 1), (54, 1), (59, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (18, 1), (21, 1), (44, 1), (46, 1), (57, 1), (61, 1)] }, { coefficient := -1, powers := [(16, 1), (18, 1), (22, 1), (44, 1), (57, 1), (61, 1)] }, { coefficient := -2, powers := [(16, 1), (21, 1), (46, 1), (57, 1), (61, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1), (57, 1), (61, 1)] }, { coefficient := 1, powers := [(16, 1), (28, 1), (42, 1), (46, 1), (61, 1)] }, { coefficient := -1, powers := [(16, 1), (28, 1), (47, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(16, 1), (21, 1), (45, 1), (46, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1), (45, 1)] }, { coefficient := -1, powers := [(17, 1), (21, 1), (44, 1), (46, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (31, 1), (44, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (44, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (21, 1), (23, 1), (44, 1), (46, 1), (57, 1)] }, { coefficient := -1, powers := [(18, 1), (21, 1), (46, 1), (57, 1)] }, { coefficient := -1, powers := [(18, 1), (22, 1), (23, 1), (44, 1), (57, 1)] }, { coefficient := 1, powers := [(18, 1), (22, 1), (57, 1)] }, { coefficient := -1, powers := [(21, 1), (23, 1), (46, 1), (57, 1)] }, { coefficient := 2, powers := [(23, 1), (28, 1), (42, 1), (46, 1)] }, { coefficient := -2, powers := [(23, 1), (28, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (21, 1), (46, 1)] }, { coefficient := -1, powers := [(17, 1), (22, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (21, 1), (44, 1), (46, 1), (57, 1)] }, { coefficient := -1, powers := [(18, 1), (22, 1), (44, 1), (57, 1)] }, { coefficient := -1, powers := [(22, 1), (57, 1)] }, { coefficient := 2, powers := [(28, 1), (42, 1), (46, 1)] }, { coefficient := -2, powers := [(28, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (28, 1), (46, 1)] }],
  [{ coefficient := -1, powers := [(42, 1), (46, 1)] }, { coefficient := 1, powers := [(47, 1)] }],
  [{ coefficient := 1, powers := [(28, 1)] }],
  [{ coefficient := -1, powers := [(21, 1), (46, 1)] }, { coefficient := 1, powers := [(22, 1)] }],
  [{ coefficient := 1, powers := [(17, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (21, 1), (46, 1)] }, { coefficient := -1, powers := [(16, 1), (22, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (14, 1), (31, 1), (44, 1), (57, 1)] }, { coefficient := -1, powers := [(5, 1), (14, 1), (34, 1), (44, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (14, 1), (31, 1), (44, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (14, 1), (34, 1), (44, 1), (54, 1)] }, { coefficient := 1, powers := [(4, 1), (31, 1), (57, 1)] }, { coefficient := 1, powers := [(4, 1), (34, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(12, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (14, 1), (31, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (14, 1), (34, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(17, 1), (28, 1)] }],
  [{ coefficient := 1, powers := [(46, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (31, 1), (57, 1)] }, { coefficient := -1, powers := [(5, 1), (34, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(16, 1), (18, 1), (21, 1), (44, 1), (46, 1), (49, 1), (57, 1)] }, { coefficient := 1, powers := [(16, 1), (18, 1), (22, 1), (44, 1), (49, 1), (57, 1)] }, { coefficient := 2, powers := [(16, 1), (21, 1), (46, 1), (49, 1), (57, 1)] }, { coefficient := -1, powers := [(16, 1), (22, 1), (49, 1), (57, 1)] }, { coefficient := -1, powers := [(16, 1), (28, 1), (42, 1), (46, 1), (49, 1)] }, { coefficient := 1, powers := [(16, 1), (28, 1), (47, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (31, 1), (36, 1), (57, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (39, 1), (56, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (36, 1), (54, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (39, 1), (54, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(37, 1), (60, 1)] }, { coefficient := 1, powers := [(40, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (17, 1), (28, 1), (56, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (10, 1), (20, 1), (31, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (10, 1), (20, 1), (34, 1), (54, 1)] }, { coefficient := -1, powers := [(5, 1), (14, 1), (20, 1), (31, 1), (57, 1)] }, { coefficient := -1, powers := [(5, 1), (14, 1), (20, 1), (34, 1), (54, 1)] }, { coefficient := -1, powers := [(12, 1), (18, 2), (21, 1), (44, 1), (46, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1), (18, 2), (22, 1), (44, 1), (57, 1)] }, { coefficient := -1, powers := [(12, 1), (18, 1), (21, 1), (23, 1), (44, 1), (46, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1), (18, 1), (21, 1), (46, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1), (18, 1), (22, 1), (23, 1), (44, 1), (57, 1)] }, { coefficient := -2, powers := [(12, 1), (18, 1), (28, 1), (42, 1), (46, 1)] }, { coefficient := 2, powers := [(12, 1), (18, 1), (28, 1), (47, 1)] }, { coefficient := 1, powers := [(12, 1), (21, 1), (23, 1), (46, 1), (57, 1)] }, { coefficient := -2, powers := [(12, 1), (23, 1), (28, 1), (42, 1), (46, 1)] }, { coefficient := 2, powers := [(12, 1), (23, 1), (28, 1), (47, 1)] }, { coefficient := -1, powers := [(17, 1), (18, 1), (28, 1), (46, 1), (49, 1)] }, { coefficient := 1, powers := [(17, 1), (19, 1), (28, 1), (49, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (7, 1), (20, 1), (31, 1), (57, 1), (59, 1)] }, { coefficient := -1, powers := [(5, 1), (7, 1), (20, 1), (34, 1), (54, 1), (59, 1)] }]
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
    ¬ ∀ index : Fin 38,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component39.SelectedLeafB4_6_1.selectedHasNoCommonZero

end Krenn.Component39.SelectedLeafB4_6_1
