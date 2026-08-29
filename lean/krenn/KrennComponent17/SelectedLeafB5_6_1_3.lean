import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component17.SelectedLeafB5_6_1_3

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "be5460db82f3c205bf1c9d07193076b1538b3563f404bc44d693e95b8de4a5c8"
def certificateSHA256 : String := "f1e4aa093718044f202a36f9ba0563ad52df185b5fa1f1c203993b4a6502856c"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 35 → Fin 614 := ![
  12,
  25,
  30,
  35,
  36,
  56,
  206,
  300,
  306,
  312,
  357,
  427,
  431,
  445,
  454,
  455,
  458,
  468,
  535,
  544,
  549,
  553,
  557,
  567,
  568,
  570,
  571,
  599,
  604,
  606,
  608,
  609,
  610,
  611,
  612
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 35 → SparsePoly (Fin 66) := ![
  [{ coefficient := 1, powers := [(12, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (26, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(26, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(26, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (37, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (19, 1)] }, { coefficient := 1, powers := [(17, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (43, 1), (51, 1)] }, { coefficient := 1, powers := [(21, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1)] }, { coefficient := 1, powers := [(19, 1), (43, 1)] }, { coefficient := 1, powers := [(24, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (56, 1)] }, { coefficient := 1, powers := [(9, 1), (53, 1)] }, { coefficient := 1, powers := [(14, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (26, 1), (56, 1)] }, { coefficient := 1, powers := [(9, 1), (26, 1), (42, 1)] }, { coefficient := 1, powers := [(14, 1), (26, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (44, 1)] }, { coefficient := 1, powers := [(17, 1), (27, 1), (40, 1)] }, { coefficient := 1, powers := [(17, 1), (27, 1), (44, 1)] }, { coefficient := 1, powers := [(17, 1), (28, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (48, 1)] }, { coefficient := 1, powers := [(12, 1), (27, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (48, 1)] }, { coefficient := 1, powers := [(17, 1), (27, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (40, 1)] }, { coefficient := 1, powers := [(17, 1), (44, 1)] }, { coefficient := 1, powers := [(17, 1), (50, 1)] }, { coefficient := 1, powers := [(17, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1), (51, 1)] }, { coefficient := 1, powers := [(19, 1), (43, 1), (51, 1)] }, { coefficient := 1, powers := [(19, 1), (55, 1)] }, { coefficient := 1, powers := [(25, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1), (48, 1)] }, { coefficient := 1, powers := [(6, 1), (30, 1), (44, 1)] }, { coefficient := 1, powers := [(9, 1), (24, 1), (44, 1)] }, { coefficient := 1, powers := [(48, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1), (49, 1)] }, { coefficient := 1, powers := [(9, 1), (45, 1)] }, { coefficient := 1, powers := [(30, 1), (37, 1), (43, 1)] }, { coefficient := 1, powers := [(43, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (36, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1)] }, { coefficient := 1, powers := [(17, 1), (27, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (19, 1), (54, 1)] }, { coefficient := 1, powers := [(12, 1)] }, { coefficient := 1, powers := [(17, 1), (19, 1), (49, 1)] }, { coefficient := 1, powers := [(17, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (25, 1), (45, 1), (49, 1)] }, { coefficient := 1, powers := [(9, 1), (25, 1), (45, 1)] }, { coefficient := 1, powers := [(9, 1), (55, 1)] }, { coefficient := 1, powers := [(25, 1), (43, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1)] }, { coefficient := 1, powers := [(6, 1), (57, 1)] }, { coefficient := 1, powers := [(24, 1), (40, 1)] }, { coefficient := 1, powers := [(24, 1), (44, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (40, 1), (53, 1)] }, { coefficient := 1, powers := [(6, 1), (33, 1), (40, 1)] }, { coefficient := 1, powers := [(14, 1), (24, 1), (40, 1)] }, { coefficient := 1, powers := [(14, 1)] }, { coefficient := 1, powers := [(53, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (36, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (39, 1), (53, 1)] }, { coefficient := 1, powers := [(2, 1), (42, 1), (48, 1)] }, { coefficient := 1, powers := [(12, 1), (22, 1), (53, 1)] }, { coefficient := 1, powers := [(12, 1), (27, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1)] }, { coefficient := 1, powers := [(3, 1), (33, 1)] }, { coefficient := 1, powers := [(14, 1), (19, 1)] }, { coefficient := 1, powers := [(19, 1), (53, 1)] }, { coefficient := 1, powers := [(24, 1), (42, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (48, 1)] }, { coefficient := 1, powers := [(6, 1), (30, 1)] }, { coefficient := 1, powers := [(9, 1), (24, 1)] }, { coefficient := 1, powers := [(19, 1), (48, 1)] }, { coefficient := 1, powers := [(24, 1), (39, 1)] }, { coefficient := 1, powers := [(30, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (50, 1)] }, { coefficient := 1, powers := [(21, 1), (54, 1)] }, { coefficient := 1, powers := [(26, 1), (40, 1)] }, { coefficient := 1, powers := [(26, 1), (44, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (36, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1)] }, { coefficient := 1, powers := [(3, 1), (24, 1), (57, 1)] }, { coefficient := 1, powers := [(6, 1), (19, 1), (57, 1)] }, { coefficient := 1, powers := [(19, 1)] }, { coefficient := 1, powers := [(24, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (36, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (39, 1), (53, 1)] }, { coefficient := 1, powers := [(0, 1), (42, 1), (48, 1)] }, { coefficient := 1, powers := [(3, 1), (24, 1), (56, 1)] }, { coefficient := 1, powers := [(3, 1), (30, 1), (53, 1)] }, { coefficient := 1, powers := [(3, 1), (33, 1), (48, 1)] }, { coefficient := 1, powers := [(6, 1), (19, 1), (56, 1)] }, { coefficient := 1, powers := [(6, 1), (30, 1), (42, 1)] }, { coefficient := 1, powers := [(6, 1), (33, 1), (39, 1)] }, { coefficient := 1, powers := [(9, 1), (19, 1), (53, 1)] }, { coefficient := 1, powers := [(9, 1), (24, 1), (42, 1)] }, { coefficient := 1, powers := [(9, 1), (33, 1), (36, 1)] }, { coefficient := 1, powers := [(14, 1), (19, 1), (48, 1)] }, { coefficient := 1, powers := [(14, 1), (24, 1), (39, 1)] }, { coefficient := 1, powers := [(14, 1), (30, 1), (36, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (60, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(40, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(53, 1)] }],
  [{ coefficient := 1, powers := [(54, 1)] }],
  [{ coefficient := 1, powers := [(55, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(24, 1)] }],
  [{ coefficient := 1, powers := [(26, 1), (64, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 35 → SparsePoly (Fin 66) := ![
  [{ coefficient := -2, powers := [(0, 1), (27, 1), (60, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (6, 1), (27, 1), (50, 1), (56, 1), (60, 1), (62, 1), (64, 1)] }, { coefficient := 2, powers := [(0, 1), (6, 1), (28, 1), (56, 1), (60, 1), (62, 1), (64, 1)] }, { coefficient := -2, powers := [(0, 1), (14, 1), (22, 1), (48, 1), (60, 1), (64, 1)] }, { coefficient := -2, powers := [(0, 1), (14, 1), (27, 1), (48, 1), (60, 1), (64, 1)] }, { coefficient := -2, powers := [(3, 1), (27, 1), (50, 1), (56, 1), (60, 1), (62, 2), (64, 1)] }, { coefficient := 2, powers := [(3, 1), (28, 1), (56, 1), (60, 1), (62, 2), (64, 1)] }, { coefficient := -1, powers := [(14, 1), (19, 1), (22, 1), (48, 1), (60, 1), (64, 1)] }, { coefficient := -1, powers := [(14, 1), (19, 1), (27, 1), (48, 1), (60, 1), (64, 1)] }, { coefficient := -1, powers := [(14, 1), (22, 1), (30, 1), (36, 1), (60, 1), (64, 1)] }, { coefficient := -1, powers := [(14, 1), (27, 1), (30, 1), (36, 1), (60, 1), (64, 1)] }, { coefficient := 2, powers := [(22, 1), (33, 1), (36, 1), (48, 1), (60, 1), (64, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (6, 1), (43, 1), (50, 1), (56, 1), (62, 1), (63, 1), (64, 1)] }, { coefficient := 2, powers := [(3, 1), (43, 1), (50, 1), (56, 1), (62, 2), (63, 1), (64, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (2, 1), (48, 1), (60, 1), (64, 1)] }, { coefficient := -2, powers := [(0, 1), (48, 1), (64, 1)] }, { coefficient := 2, powers := [(9, 1), (62, 1), (64, 1)] }, { coefficient := -2, powers := [(19, 1), (48, 1), (64, 1)] }, { coefficient := -2, powers := [(30, 1), (36, 1), (64, 1)] }],
  [{ coefficient := -3, powers := [(6, 1), (25, 1), (56, 1), (63, 1), (64, 1)] }, { coefficient := 2, powers := [(25, 1), (30, 1), (33, 1), (36, 1), (37, 1), (63, 1), (64, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (6, 1), (31, 1), (60, 1), (62, 1), (64, 1)] }, { coefficient := -2, powers := [(0, 1), (6, 1), (34, 1), (60, 1), (62, 1), (64, 1)] }, { coefficient := -2, powers := [(3, 1), (31, 1), (60, 1), (62, 2), (64, 1)] }, { coefficient := -2, powers := [(3, 1), (34, 1), (60, 1), (62, 2), (64, 1)] }],
  [{ coefficient := -2, powers := [(27, 1), (33, 1), (36, 1), (49, 1), (60, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (6, 1), (50, 1), (56, 1), (62, 1), (63, 1), (64, 1)] }, { coefficient := -2, powers := [(3, 1), (50, 1), (56, 1), (62, 2), (63, 1), (64, 1)] }],
  [{ coefficient := -3, powers := [(6, 1), (51, 1), (56, 1), (63, 1)] }],
  [{ coefficient := -2, powers := [(0, 1)] }, { coefficient := -1, powers := [(19, 1)] }],
  [{ coefficient := -2, powers := [(62, 1), (64, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (6, 1), (56, 1), (60, 1), (62, 1)] }, { coefficient := -2, powers := [(3, 1), (56, 1), (60, 1), (62, 2)] }],
  [{ coefficient := -2, powers := [(33, 1), (36, 1), (60, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (6, 1), (27, 1), (56, 1), (60, 1), (62, 1)] }, { coefficient := 2, powers := [(3, 1), (27, 1), (56, 1), (60, 1), (62, 2)] }],
  [{ coefficient := 3, powers := [(6, 1), (56, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (14, 1)] }],
  [{ coefficient := -2, powers := [(25, 1), (33, 1), (36, 1), (63, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (14, 1), (48, 1), (60, 1)] }, { coefficient := 1, powers := [(14, 1), (19, 1), (48, 1), (60, 1)] }, { coefficient := 1, powers := [(14, 1), (30, 1), (36, 1), (60, 1)] }],
  [{ coefficient := 2, powers := [(27, 1), (33, 1), (36, 1), (60, 1)] }],
  [{ coefficient := 2, powers := [(33, 1), (36, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (19, 1), (48, 1)] }, { coefficient := 1, powers := [(14, 1), (30, 1), (36, 1)] }],
  [{ coefficient := 2, powers := [(39, 1), (62, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (60, 1)] }],
  [{ coefficient := 2, powers := [(48, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (14, 1), (44, 1)] }, { coefficient := -1, powers := [(14, 1), (36, 1), (57, 1)] }, { coefficient := 2, powers := [(42, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (6, 1), (56, 1), (62, 1), (64, 1)] }, { coefficient := 2, powers := [(3, 1), (56, 1), (62, 2), (64, 1)] }],
  [{ coefficient := -1, powers := [(14, 1), (48, 1)] }],
  [{ coefficient := -2, powers := [] }],
  [{ coefficient := 2, powers := [(0, 1), (6, 1), (31, 1), (37, 1), (56, 1), (62, 1), (64, 1)] }, { coefficient := 2, powers := [(0, 1), (6, 1), (34, 1), (37, 1), (56, 1), (62, 1), (64, 1)] }, { coefficient := 2, powers := [(0, 1), (6, 1), (44, 1), (56, 1), (62, 1)] }, { coefficient := -2, powers := [(0, 1), (14, 1), (36, 1), (48, 1), (57, 1)] }, { coefficient := -2, powers := [(0, 1), (14, 1), (48, 1)] }, { coefficient := -2, powers := [(0, 1), (36, 1), (56, 1)] }, { coefficient := 2, powers := [(3, 1), (31, 1), (37, 1), (56, 1), (62, 2), (64, 1)] }, { coefficient := 2, powers := [(3, 1), (34, 1), (37, 1), (56, 1), (62, 2), (64, 1)] }, { coefficient := 2, powers := [(3, 1), (44, 1), (56, 1), (62, 2)] }, { coefficient := -1, powers := [(14, 1), (19, 1), (36, 1), (48, 1), (57, 1)] }, { coefficient := -1, powers := [(14, 1), (19, 1), (48, 1)] }, { coefficient := -1, powers := [(14, 1), (30, 1), (36, 2), (57, 1)] }, { coefficient := -1, powers := [(14, 1), (30, 1), (36, 1)] }, { coefficient := 2, powers := [(33, 1), (36, 1), (48, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (6, 1), (56, 1)] }, { coefficient := -2, powers := [(3, 1), (56, 1), (62, 1)] }, { coefficient := -2, powers := [(6, 1), (33, 1), (39, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (2, 1), (39, 1), (60, 1)] }, { coefficient := 2, powers := [(0, 1), (9, 1)] }, { coefficient := -2, powers := [(0, 1), (12, 1), (22, 1), (60, 1)] }, { coefficient := -2, powers := [(0, 1), (39, 1), (40, 1), (62, 1)] }, { coefficient := 2, powers := [(0, 1), (39, 1)] }, { coefficient := 2, powers := [(3, 1), (30, 1)] }, { coefficient := 3, powers := [(9, 1), (19, 1)] }, { coefficient := -2, powers := [(19, 1), (48, 1)] }, { coefficient := -2, powers := [(39, 1), (62, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (6, 1), (17, 1), (27, 1), (56, 1), (60, 1), (62, 1)] }, { coefficient := -2, powers := [(0, 1), (6, 1), (21, 1), (56, 1), (62, 1), (64, 1)] }, { coefficient := -2, powers := [(3, 1), (17, 1), (27, 1), (56, 1), (60, 1), (62, 2)] }, { coefficient := -2, powers := [(3, 1), (21, 1), (56, 1), (62, 2), (64, 1)] }, { coefficient := -2, powers := [(12, 1), (19, 1), (27, 1), (33, 1), (36, 1), (60, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (6, 1), (21, 1), (50, 1), (56, 1), (62, 1), (64, 1)] }, { coefficient := 2, powers := [(3, 1), (21, 1), (50, 1), (56, 1), (62, 2), (64, 1)] }, { coefficient := -3, powers := [(6, 1), (19, 1), (56, 1)] }, { coefficient := -2, powers := [(9, 1), (33, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (14, 1), (39, 1), (44, 1)] }, { coefficient := 1, powers := [(3, 1), (14, 1), (48, 1), (57, 1)] }, { coefficient := 2, powers := [(3, 1), (56, 1)] }, { coefficient := 3, powers := [(6, 1), (43, 1), (51, 1), (56, 1), (63, 1)] }, { coefficient := 1, powers := [(9, 1), (14, 1), (36, 1), (57, 1)] }, { coefficient := -1, powers := [(14, 1), (19, 1), (40, 1), (48, 1)] }, { coefficient := -1, powers := [(14, 1), (19, 1), (44, 1), (48, 1)] }, { coefficient := -1, powers := [(14, 1), (30, 1), (36, 1), (40, 1)] }, { coefficient := -1, powers := [(14, 1), (30, 1), (36, 1), (44, 1)] }, { coefficient := 1, powers := [(14, 1), (36, 1), (39, 1), (57, 1)] }, { coefficient := -2, powers := [(14, 1), (39, 1), (40, 1), (62, 1)] }, { coefficient := 2, powers := [(14, 1), (39, 1)] }, { coefficient := 1, powers := [(14, 1), (48, 1)] }, { coefficient := 2, powers := [(17, 1), (27, 1), (33, 1), (36, 1), (49, 1), (60, 1)] }, { coefficient := -2, powers := [(39, 1), (42, 1)] }, { coefficient := -2, powers := [(42, 1), (48, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (2, 1), (42, 1), (48, 1), (60, 1)] }, { coefficient := 2, powers := [(0, 1), (6, 1), (17, 1), (27, 1), (50, 1), (56, 1), (60, 1), (62, 1)] }, { coefficient := -2, powers := [(0, 1), (6, 1), (17, 1), (28, 1), (56, 1), (60, 1), (62, 1)] }, { coefficient := -2, powers := [(0, 1), (6, 1), (40, 1), (56, 1), (62, 1)] }, { coefficient := -2, powers := [(0, 1), (6, 1), (44, 1), (56, 1), (62, 1)] }, { coefficient := 2, powers := [(0, 1), (14, 1), (17, 1), (22, 1), (48, 1), (60, 1)] }, { coefficient := 2, powers := [(0, 1), (14, 1), (17, 1), (27, 1), (48, 1), (60, 1)] }, { coefficient := 2, powers := [(0, 1), (42, 1), (48, 1)] }, { coefficient := 2, powers := [(3, 1), (17, 1), (27, 1), (50, 1), (56, 1), (60, 1), (62, 2)] }, { coefficient := -2, powers := [(3, 1), (17, 1), (28, 1), (56, 1), (60, 1), (62, 2)] }, { coefficient := -2, powers := [(3, 1), (40, 1), (56, 1), (62, 2)] }, { coefficient := -2, powers := [(3, 1), (44, 1), (56, 1), (62, 2)] }, { coefficient := 2, powers := [(3, 1), (56, 1), (62, 1)] }, { coefficient := 3, powers := [(6, 1), (25, 1), (43, 1), (56, 1), (63, 1)] }, { coefficient := 1, powers := [(14, 1), (17, 1), (19, 1), (22, 1), (48, 1), (60, 1)] }, { coefficient := 1, powers := [(14, 1), (17, 1), (19, 1), (27, 1), (48, 1), (60, 1)] }, { coefficient := 1, powers := [(14, 1), (17, 1), (22, 1), (30, 1), (36, 1), (60, 1)] }, { coefficient := 1, powers := [(14, 1), (17, 1), (27, 1), (30, 1), (36, 1), (60, 1)] }, { coefficient := 2, powers := [(14, 1), (39, 1), (62, 1)] }, { coefficient := -2, powers := [(17, 1), (22, 1), (33, 1), (36, 1), (48, 1), (60, 1)] }, { coefficient := 2, powers := [(19, 1), (42, 1), (48, 1)] }, { coefficient := -2, powers := [(25, 1), (30, 1), (33, 1), (36, 1), (37, 1), (43, 1), (63, 1)] }, { coefficient := 2, powers := [(30, 1), (36, 1), (42, 1)] }]
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
    (values : Fin 66 → R) :
    ¬ ∀ index : Fin 35,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((2 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (2 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (2 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component17.SelectedLeafB5_6_1_3.selectedHasNoCommonZero

end Krenn.Component17.SelectedLeafB5_6_1_3
