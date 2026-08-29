import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component44.SelectedLeafB6

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "a10afdc04d9e1b7721f09ab565ce766c7563e1260bd827b2ab65fa5819626f5f"
def certificateSHA256 : String := "ace3ac6ec673fac3af1d1086f111643b95f5cb30a15f719cab305e4792ba5f24"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 53 → Fin 611 := ![
  4,
  5,
  6,
  10,
  12,
  14,
  15,
  19,
  22,
  23,
  24,
  28,
  30,
  32,
  151,
  152,
  153,
  159,
  162,
  181,
  192,
  197,
  201,
  202,
  207,
  224,
  228,
  242,
  243,
  309,
  333,
  355,
  356,
  362,
  363,
  367,
  369,
  377,
  379,
  395,
  415,
  483,
  484,
  485,
  535,
  550,
  551,
  573,
  584,
  607,
  608,
  609,
  610
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 53 → SparsePoly (Fin 62) := ![
  [{ coefficient := 1, powers := [(3, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (31, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (31, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (26, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (27, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (21, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (21, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (22, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(26, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (48, 1)] }, { coefficient := 1, powers := [(26, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (52, 1)] }, { coefficient := 1, powers := [(21, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (53, 1)] }, { coefficient := 1, powers := [(21, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (37, 1)] }, { coefficient := 1, powers := [(18, 1), (30, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (34, 1)] }, { coefficient := 1, powers := [(12, 1), (30, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (46, 1)] }, { coefficient := 1, powers := [(14, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (42, 1)] }, { coefficient := 1, powers := [(20, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (52, 1)] }, { coefficient := 1, powers := [(30, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(30, 1), (56, 1)] }, { coefficient := 1, powers := [(31, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(31, 1), (42, 1)] }, { coefficient := 1, powers := [(31, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(52, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (27, 1), (58, 1)] }, { coefficient := 1, powers := [(27, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (31, 1), (58, 1)] }, { coefficient := 1, powers := [(31, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (22, 1), (58, 1)] }, { coefficient := 1, powers := [(22, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (25, 1), (58, 1)] }, { coefficient := 1, powers := [(25, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (21, 1), (55, 1)] }, { coefficient := 1, powers := [(14, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (26, 1), (42, 1)] }, { coefficient := 1, powers := [(20, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (48, 1)] }, { coefficient := 1, powers := [(5, 1), (37, 1)] }, { coefficient := 1, powers := [(20, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (53, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1)] }, { coefficient := 1, powers := [(14, 1), (31, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (53, 1)] }, { coefficient := 1, powers := [(31, 1), (43, 1)] }, { coefficient := 1, powers := [(34, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (56, 1)] }, { coefficient := 1, powers := [(31, 1), (48, 1)] }, { coefficient := 1, powers := [(37, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1), (56, 1)] }, { coefficient := 1, powers := [(27, 1), (47, 1)] }, { coefficient := 1, powers := [(56, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1), (55, 1)] }, { coefficient := 1, powers := [(22, 1), (52, 1)] }, { coefficient := 1, powers := [(43, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (42, 1), (56, 1)] }, { coefficient := 1, powers := [(4, 1), (33, 1), (56, 1)] }, { coefficient := 1, powers := [(11, 1), (24, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (43, 1), (55, 1)] }, { coefficient := 1, powers := [(7, 1), (36, 1), (43, 1)] }, { coefficient := 1, powers := [(17, 1), (29, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (42, 1), (56, 1)] }, { coefficient := 1, powers := [(8, 1), (37, 1), (42, 1)] }, { coefficient := 1, powers := [(20, 1), (31, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (31, 1), (58, 1)] }, { coefficient := 1, powers := [(11, 1), (31, 1), (46, 1)] }, { coefficient := 1, powers := [(17, 1), (31, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (59, 1)] }, { coefficient := 1, powers := [(12, 1), (47, 1)] }, { coefficient := 1, powers := [(18, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (59, 1)] }, { coefficient := 1, powers := [(14, 1), (48, 1)] }, { coefficient := 1, powers := [(20, 1), (22, 1), (52, 1)] }, { coefficient := 1, powers := [(20, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (59, 1)] }, { coefficient := 1, powers := [(14, 1), (27, 1), (47, 1)] }, { coefficient := 1, powers := [(14, 1), (56, 1)] }, { coefficient := 1, powers := [(20, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1)] }, { coefficient := 1, powers := [(6, 1), (58, 1)] }, { coefficient := 1, powers := [(26, 1), (42, 1)] }, { coefficient := 1, powers := [(26, 1), (46, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1), (51, 1)] }, { coefficient := 1, powers := [(7, 1), (23, 1), (58, 1)] }, { coefficient := 1, powers := [(7, 1), (33, 1)] }, { coefficient := 1, powers := [(11, 1), (23, 1), (55, 1)] }, { coefficient := 1, powers := [(11, 1), (29, 1)] }, { coefficient := 1, powers := [(17, 1), (23, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (58, 1)] }, { coefficient := 1, powers := [(7, 1), (58, 1)] }, { coefficient := 1, powers := [(11, 1), (46, 1)] }, { coefficient := 1, powers := [(11, 1), (55, 1)] }, { coefficient := 1, powers := [(17, 1), (42, 1)] }, { coefficient := 1, powers := [(17, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (31, 1), (59, 1)] }, { coefficient := 1, powers := [(4, 1), (34, 1), (56, 1)] }, { coefficient := 1, powers := [(4, 1), (37, 1), (53, 1)] }, { coefficient := 1, powers := [(12, 1), (30, 1), (56, 1)] }, { coefficient := 1, powers := [(12, 1), (31, 1), (47, 1)] }, { coefficient := 1, powers := [(18, 1), (30, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (25, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (34, 1), (48, 1)] }, { coefficient := 1, powers := [(7, 1), (37, 1), (43, 1)] }, { coefficient := 1, powers := [(12, 1), (30, 1), (48, 1)] }, { coefficient := 1, powers := [(18, 1), (25, 1), (52, 1)] }, { coefficient := 1, powers := [(18, 1), (30, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (40, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (43, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (48, 1), (53, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (37, 1), (53, 1)] }, { coefficient := 1, powers := [(8, 1), (25, 1), (59, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (48, 1)] }, { coefficient := 1, powers := [(8, 1), (37, 1), (43, 1)] }, { coefficient := 1, powers := [(14, 1), (25, 1), (56, 1)] }, { coefficient := 1, powers := [(14, 1), (31, 1), (48, 1)] }, { coefficient := 1, powers := [(14, 1), (37, 1), (40, 1)] }, { coefficient := 1, powers := [(20, 1), (25, 1), (53, 1)] }, { coefficient := 1, powers := [(20, 1), (31, 1), (43, 1)] }, { coefficient := 1, powers := [(20, 1), (34, 1), (40, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (60, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1), (61, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 53 → SparsePoly (Fin 62) := ![
  [{ coefficient := 1, powers := [(0, 1), (1, 1), (5, 1), (31, 1), (51, 1), (58, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (27, 1), (34, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (7, 1), (8, 1), (25, 1), (36, 1), (58, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (5, 1), (29, 1), (59, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (5, 1), (33, 1), (47, 1), (61, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (1, 1), (31, 1), (46, 1), (48, 1), (60, 1), (61, 1)] }, { coefficient := -2, powers := [(0, 1), (31, 1), (46, 1), (48, 1), (60, 1)] }, { coefficient := 2, powers := [(31, 1), (48, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (1, 1), (25, 1), (42, 1), (47, 1), (61, 1)] }, { coefficient := -1, powers := [(0, 1), (25, 1), (42, 1), (47, 1)] }, { coefficient := -1, powers := [(25, 1), (47, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (5, 1), (31, 1), (33, 1), (52, 1), (60, 1), (61, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (1, 1), (25, 1), (51, 1), (53, 1), (60, 1), (61, 1)] }, { coefficient := -2, powers := [(0, 1), (25, 1), (51, 1), (53, 1), (60, 1)] }, { coefficient := 2, powers := [(25, 1), (53, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (1, 1), (31, 1), (42, 1), (52, 1), (61, 1)] }, { coefficient := -1, powers := [(0, 1), (31, 1), (42, 1), (52, 1)] }, { coefficient := -1, powers := [(31, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (1, 1), (14, 1), (25, 1), (42, 1), (46, 1), (61, 1)] }, { coefficient := -1, powers := [(0, 1), (14, 1), (25, 1), (42, 1), (46, 1)] }, { coefficient := -1, powers := [(14, 1), (25, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (5, 1), (11, 1), (34, 1), (61, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (1, 1), (20, 1), (31, 1), (51, 2), (61, 1)] }, { coefficient := 1, powers := [(0, 1), (8, 1), (37, 1), (42, 1), (55, 1)] }, { coefficient := 1, powers := [(0, 1), (8, 1), (37, 1), (46, 1), (55, 1)] }, { coefficient := 2, powers := [(0, 1), (20, 1), (31, 1), (51, 2)] }, { coefficient := 1, powers := [(8, 1), (37, 1), (42, 1)] }, { coefficient := 1, powers := [(8, 1), (37, 1), (46, 1)] }, { coefficient := -1, powers := [(20, 1), (31, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (8, 1), (17, 1), (37, 1), (61, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (1, 1), (14, 1), (31, 1), (46, 1), (60, 1), (61, 1)] }, { coefficient := 2, powers := [(0, 1), (14, 1), (31, 1), (46, 1), (60, 1)] }, { coefficient := -2, powers := [(14, 1), (31, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (5, 1), (18, 1), (31, 1), (33, 1), (60, 1), (61, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (1, 1), (20, 1), (25, 1), (51, 1), (60, 1), (61, 1)] }, { coefficient := 2, powers := [(0, 1), (20, 1), (25, 1), (51, 1), (60, 1)] }, { coefficient := -2, powers := [(20, 1), (25, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (5, 1), (33, 1), (53, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (8, 1), (36, 1), (48, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (1, 1), (21, 1), (25, 1), (42, 1), (56, 1), (61, 1)] }, { coefficient := 1, powers := [(0, 1), (21, 1), (25, 1), (42, 1), (56, 1)] }, { coefficient := 1, powers := [(21, 1), (25, 1), (56, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (1, 1), (25, 1), (53, 1), (61, 1)] }, { coefficient := 2, powers := [(0, 1), (1, 1), (26, 1), (31, 1), (43, 1), (51, 1), (61, 1)] }, { coefficient := 2, powers := [(0, 1), (1, 1), (31, 1), (43, 1), (61, 1)] }, { coefficient := -2, powers := [(0, 1), (25, 1), (53, 1)] }, { coefficient := -2, powers := [(0, 1), (26, 1), (31, 1), (43, 1), (51, 1)] }, { coefficient := -2, powers := [(0, 1), (31, 1), (43, 1)] }, { coefficient := 1, powers := [(26, 1), (31, 1), (43, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (8, 1), (18, 1), (36, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (5, 1), (12, 1), (33, 1), (61, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (1, 1), (14, 1), (48, 1), (61, 1)] }, { coefficient := -2, powers := [(0, 1), (14, 1), (48, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (22, 1), (37, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (34, 1), (47, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (1, 1), (5, 1), (51, 1), (59, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (37, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (7, 1), (8, 1), (36, 1), (59, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (1, 1), (25, 1), (42, 1), (56, 1), (61, 1)] }, { coefficient := -1, powers := [(0, 1), (25, 1), (42, 1), (56, 1)] }, { coefficient := -1, powers := [(25, 1), (56, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (1, 1), (31, 1), (43, 1), (51, 1), (61, 1)] }, { coefficient := 2, powers := [(0, 1), (31, 1), (43, 1), (51, 1)] }, { coefficient := -1, powers := [(31, 1), (43, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (1, 1), (42, 1), (53, 1), (61, 1)] }, { coefficient := 1, powers := [(0, 1), (42, 1), (53, 1)] }, { coefficient := 1, powers := [(53, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (1, 1), (42, 1), (48, 1), (61, 1)] }, { coefficient := 1, powers := [(0, 1), (42, 1), (48, 1)] }, { coefficient := 1, powers := [(48, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (1, 1), (20, 1), (42, 1), (61, 1)] }, { coefficient := 1, powers := [(0, 1), (20, 1), (42, 1)] }, { coefficient := 1, powers := [(20, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (1, 1), (14, 1), (42, 1), (61, 1)] }, { coefficient := 1, powers := [(0, 1), (14, 1), (42, 1)] }, { coefficient := 1, powers := [(14, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (34, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (26, 1), (37, 1), (42, 1)] }, { coefficient := -1, powers := [(8, 1), (26, 1), (37, 1), (46, 1)] }, { coefficient := 1, powers := [(8, 1), (37, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (5, 1), (34, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (8, 1), (37, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (1, 1), (43, 1), (61, 1)] }, { coefficient := 1, powers := [(0, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (5, 1), (23, 1), (59, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (5, 1), (31, 1), (33, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (1, 1), (31, 1), (42, 1), (61, 1)] }, { coefficient := 1, powers := [(0, 1), (31, 1), (42, 1)] }, { coefficient := 1, powers := [(31, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (1, 1), (25, 1), (42, 1), (61, 1)] }, { coefficient := 1, powers := [(0, 1), (25, 1), (42, 1)] }, { coefficient := 1, powers := [(25, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (22, 1), (37, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (5, 1), (31, 1), (59, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (5, 1), (23, 1), (31, 1), (59, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (5, 1), (33, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (8, 1), (36, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (1, 1), (42, 1), (61, 1)] }, { coefficient := -1, powers := [(0, 1), (42, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 2, powers := [(0, 1), (1, 1), (14, 1), (31, 1), (46, 1), (48, 1), (61, 1)] }, { coefficient := 2, powers := [(0, 1), (1, 1), (20, 1), (25, 1), (51, 1), (53, 1), (61, 1)] }, { coefficient := -1, powers := [(0, 1), (5, 1), (18, 1), (31, 1), (33, 1), (52, 1), (61, 1)] }, { coefficient := -2, powers := [(0, 1), (14, 1), (31, 1), (46, 1), (48, 1)] }, { coefficient := -2, powers := [(0, 1), (20, 1), (25, 1), (51, 1), (53, 1)] }, { coefficient := 2, powers := [(14, 1), (31, 1), (48, 1)] }, { coefficient := 2, powers := [(20, 1), (25, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (8, 1), (37, 1), (43, 1), (55, 1)] }, { coefficient := 1, powers := [(0, 1), (42, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (1, 1), (40, 1), (42, 1), (59, 1), (61, 1)] }, { coefficient := 1, powers := [(0, 1), (1, 1), (42, 1), (48, 1), (53, 1), (61, 1)] }, { coefficient := 1, powers := [(0, 1), (40, 1), (42, 1), (59, 1)] }, { coefficient := -1, powers := [(0, 1), (42, 1), (48, 1), (53, 1)] }, { coefficient := 1, powers := [(40, 1), (59, 1)] }, { coefficient := 1, powers := [(43, 1), (56, 1)] }, { coefficient := -1, powers := [(48, 1), (53, 1)] }]
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
    ¬ ∀ index : Fin 53,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component44.SelectedLeafB6.selectedHasNoCommonZero

end Krenn.Component44.SelectedLeafB6
