import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component46.SelectedLeafB4_1

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "9e9898ea8a9e15cc723791543c1e9717ca23c7764a01d0a825b77b624acdd2bd"
def certificateSHA256 : String := "abc3e441afb6e1f3ec31bd1f177868b4fcb9f08ac0edad41ad49990b98c7d064"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 29 → Fin 646 := ![
  3,
  4,
  18,
  29,
  39,
  162,
  173,
  204,
  207,
  208,
  240,
  252,
  350,
  352,
  361,
  362,
  367,
  406,
  450,
  520,
  561,
  581,
  637,
  639,
  640,
  642,
  643,
  644,
  645
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 29 → SparsePoly (Fin 63) := ![
  [{ coefficient := 1, powers := [(6, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (32, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(35, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (49, 1)] }, { coefficient := 1, powers := [(27, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (34, 1)] }, { coefficient := 1, powers := [(34, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(31, 1), (42, 1)] }, { coefficient := 1, powers := [(31, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1), (57, 1)] }, { coefficient := 1, powers := [(57, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1), (53, 1)] }, { coefficient := 1, powers := [(15, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (26, 1), (59, 1)] }, { coefficient := 1, powers := [(26, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (32, 1), (45, 1)] }, { coefficient := 1, powers := [(8, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (49, 1)] }, { coefficient := 1, powers := [(5, 1), (37, 1)] }, { coefficient := 1, powers := [(21, 1), (26, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (60, 1)] }, { coefficient := 1, powers := [(14, 1), (57, 1)] }, { coefficient := 1, powers := [(21, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(26, 1), (54, 1)] }, { coefficient := 1, powers := [(31, 1), (43, 1)] }, { coefficient := 1, powers := [(34, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(26, 1), (57, 1)] }, { coefficient := 1, powers := [(31, 1), (49, 1)] }, { coefficient := 1, powers := [(37, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1), (55, 1)] }, { coefficient := 1, powers := [(6, 1), (35, 1), (43, 1)] }, { coefficient := 1, powers := [(15, 1), (27, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (26, 1), (60, 1)] }, { coefficient := 1, powers := [(6, 1), (34, 1), (49, 1)] }, { coefficient := 1, powers := [(6, 1), (37, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (23, 1), (45, 1), (53, 1)] }, { coefficient := 1, powers := [(15, 1), (23, 1), (53, 1)] }, { coefficient := 1, powers := [(15, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (35, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (43, 1)] }, { coefficient := 1, powers := [(14, 1), (35, 1), (40, 1)] }, { coefficient := 1, powers := [(19, 1), (23, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1)] }, { coefficient := 1, powers := [(6, 1), (59, 1)] }, { coefficient := 1, powers := [(27, 1), (42, 1)] }, { coefficient := 1, powers := [(27, 1), (46, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1)] }, { coefficient := 1, powers := [(3, 1), (35, 1)] }, { coefficient := 1, powers := [(15, 1), (22, 1)] }, { coefficient := 1, powers := [(22, 1), (55, 1)] }, { coefficient := 1, powers := [(27, 1), (44, 1)] }, { coefficient := 1, powers := [(35, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (38, 1), (58, 1)] }, { coefficient := 1, powers := [(0, 1), (41, 1), (55, 1)] }, { coefficient := 1, powers := [(0, 1), (44, 1), (50, 1)] }, { coefficient := 1, powers := [(3, 1), (27, 1), (58, 1)] }, { coefficient := 1, powers := [(3, 1), (32, 1), (55, 1)] }, { coefficient := 1, powers := [(3, 1), (35, 1), (50, 1)] }, { coefficient := 1, powers := [(6, 1), (22, 1), (58, 1)] }, { coefficient := 1, powers := [(6, 1), (32, 1), (44, 1)] }, { coefficient := 1, powers := [(6, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(9, 1), (22, 1), (55, 1)] }, { coefficient := 1, powers := [(9, 1), (27, 1), (44, 1)] }, { coefficient := 1, powers := [(9, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(15, 1), (22, 1), (50, 1)] }, { coefficient := 1, powers := [(15, 1), (27, 1), (41, 1)] }, { coefficient := 1, powers := [(15, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (40, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (43, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (49, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (37, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (26, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (49, 1)] }, { coefficient := 1, powers := [(8, 1), (37, 1), (43, 1)] }, { coefficient := 1, powers := [(14, 1), (26, 1), (57, 1)] }, { coefficient := 1, powers := [(14, 1), (31, 1), (49, 1)] }, { coefficient := 1, powers := [(14, 1), (37, 1), (40, 1)] }, { coefficient := 1, powers := [(21, 1), (26, 1), (54, 1)] }, { coefficient := 1, powers := [(21, 1), (31, 1), (43, 1)] }, { coefficient := 1, powers := [(21, 1), (34, 1), (40, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (61, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(41, 1)] }],
  [{ coefficient := 1, powers := [(42, 1)] }],
  [{ coefficient := 1, powers := [(43, 1), (62, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 29 → SparsePoly (Fin 63) := ![
  [{ coefficient := -1, powers := [(0, 1), (5, 1), (31, 1), (38, 1), (43, 1), (58, 1), (59, 1), (62, 1)] }, { coefficient := -2, powers := [(0, 1), (8, 1), (26, 1), (38, 1), (43, 1), (58, 1), (59, 1), (62, 1)] }, { coefficient := -1, powers := [(3, 1), (5, 1), (31, 1), (32, 1), (35, 1), (61, 1)] }, { coefficient := -1, powers := [(3, 1), (8, 1), (26, 1), (32, 1), (35, 1), (61, 1)] }, { coefficient := -1, powers := [(5, 1), (9, 1), (22, 1), (31, 1), (35, 1), (61, 1)] }, { coefficient := -1, powers := [(5, 1), (9, 1), (31, 1), (35, 1), (38, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (22, 1), (31, 1), (35, 1), (50, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (22, 1), (31, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (32, 1), (44, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (35, 1), (38, 1), (50, 1), (59, 1)] }, { coefficient := -1, powers := [(8, 1), (9, 1), (22, 1), (26, 1), (35, 1), (61, 1)] }, { coefficient := -1, powers := [(8, 1), (9, 1), (26, 1), (35, 1), (38, 1), (59, 1)] }, { coefficient := 1, powers := [(8, 1), (22, 1), (26, 1), (35, 1), (50, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (22, 1), (26, 1), (58, 1)] }, { coefficient := 1, powers := [(8, 1), (26, 1), (32, 1), (44, 1)] }, { coefficient := 1, powers := [(8, 1), (26, 1), (35, 1), (38, 1), (50, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (37, 1), (38, 1), (43, 1), (45, 1)] }],
  [{ coefficient := -1, powers := [(9, 1), (23, 1), (37, 1), (38, 1)] }, { coefficient := 1, powers := [(23, 1), (37, 1), (38, 1), (50, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (8, 1), (34, 1), (38, 1), (43, 1), (49, 1), (58, 1), (61, 1), (62, 2)] }, { coefficient := 1, powers := [(3, 1), (6, 1), (8, 1), (32, 1), (34, 1), (35, 1), (49, 1), (61, 2), (62, 1)] }, { coefficient := 1, powers := [(3, 1), (8, 1), (32, 1), (34, 1), (35, 1), (38, 1), (49, 1), (61, 2), (62, 1)] }, { coefficient := -1, powers := [(3, 1), (15, 1), (32, 1), (61, 1), (62, 1)] }, { coefficient := 1, powers := [(3, 1), (58, 1), (62, 1)] }, { coefficient := 1, powers := [(6, 1), (8, 1), (9, 1), (22, 1), (34, 1), (35, 1), (49, 1), (61, 2), (62, 1)] }, { coefficient := -1, powers := [(6, 1), (8, 1), (22, 1), (34, 1), (35, 1), (49, 1), (50, 1), (61, 2), (62, 1)] }, { coefficient := -1, powers := [(6, 1), (8, 1), (22, 1), (34, 1), (49, 1), (58, 1), (61, 1), (62, 1)] }, { coefficient := -1, powers := [(6, 1), (8, 1), (32, 1), (34, 1), (44, 1), (49, 1), (61, 1), (62, 1)] }, { coefficient := 1, powers := [(8, 1), (9, 1), (22, 1), (34, 1), (35, 1), (38, 1), (49, 1), (61, 2), (62, 1)] }, { coefficient := -1, powers := [(8, 1), (9, 1), (34, 1), (35, 1), (38, 1), (49, 1), (61, 1), (62, 1)] }, { coefficient := -1, powers := [(8, 1), (22, 1), (34, 1), (35, 1), (38, 1), (49, 1), (50, 1), (61, 2), (62, 1)] }, { coefficient := -1, powers := [(8, 1), (22, 1), (34, 1), (38, 1), (49, 1), (58, 1), (61, 1), (62, 1)] }, { coefficient := -1, powers := [(8, 1), (32, 1), (34, 1), (38, 1), (44, 1), (49, 1), (61, 1), (62, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (35, 1), (38, 1), (49, 1), (50, 1), (61, 1), (62, 1)] }, { coefficient := -1, powers := [(9, 1), (15, 1), (22, 1), (61, 1), (62, 1)] }, { coefficient := 1, powers := [(9, 1), (44, 1), (62, 1)] }, { coefficient := 1, powers := [(15, 1), (22, 1), (50, 1), (61, 1), (62, 1)] }, { coefficient := -1, powers := [(44, 1), (50, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(9, 1), (14, 1), (37, 1), (38, 1)] }, { coefficient := 1, powers := [(14, 1), (37, 1), (38, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (8, 1), (34, 1), (38, 1), (43, 1), (58, 1), (61, 1), (62, 1)] }, { coefficient := -1, powers := [(3, 1), (6, 1), (8, 1), (32, 1), (34, 1), (35, 1), (61, 2)] }, { coefficient := -1, powers := [(3, 1), (8, 1), (32, 1), (34, 1), (35, 1), (38, 1), (61, 2)] }, { coefficient := -1, powers := [(6, 1), (8, 1), (9, 1), (22, 1), (34, 1), (35, 1), (61, 2)] }, { coefficient := 1, powers := [(6, 1), (8, 1), (22, 1), (34, 1), (35, 1), (50, 1), (61, 2)] }, { coefficient := 1, powers := [(6, 1), (8, 1), (22, 1), (34, 1), (58, 1), (61, 1)] }, { coefficient := 1, powers := [(6, 1), (8, 1), (32, 1), (34, 1), (44, 1), (61, 1)] }, { coefficient := -1, powers := [(8, 1), (9, 1), (22, 1), (34, 1), (35, 1), (38, 1), (61, 2)] }, { coefficient := 1, powers := [(8, 1), (9, 1), (34, 1), (35, 1), (38, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (22, 1), (34, 1), (35, 1), (38, 1), (50, 1), (61, 2)] }, { coefficient := 1, powers := [(8, 1), (22, 1), (34, 1), (38, 1), (58, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (34, 1), (38, 1), (44, 1), (61, 1)] }, { coefficient := -1, powers := [(8, 1), (34, 1), (35, 1), (38, 1), (50, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (8, 1), (32, 1), (35, 1), (49, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (9, 1), (22, 1), (35, 1), (49, 1), (61, 1)] }, { coefficient := -1, powers := [(8, 1), (22, 1), (35, 1), (49, 1), (50, 1), (61, 1)] }, { coefficient := -1, powers := [(8, 1), (22, 1), (49, 1), (58, 1)] }, { coefficient := -1, powers := [(8, 1), (32, 1), (44, 1), (49, 1)] }],
  [{ coefficient := -1, powers := [(0, 2), (5, 1), (38, 1), (43, 1), (58, 1), (60, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 1), (5, 1), (9, 1), (35, 1), (38, 1), (60, 1)] }, { coefficient := -1, powers := [(0, 1), (5, 1), (27, 1), (38, 1), (43, 1), (58, 1), (60, 1), (62, 1)] }, { coefficient := 1, powers := [(0, 1), (5, 1), (35, 1), (38, 1), (50, 1), (60, 1)] }, { coefficient := -1, powers := [(5, 1), (9, 1), (27, 1), (35, 1), (38, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (27, 1), (35, 1), (38, 1), (50, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (5, 1), (34, 1), (38, 1), (43, 1), (58, 1), (62, 1)] }, { coefficient := 1, powers := [(0, 1), (14, 1), (26, 1), (38, 1), (43, 1), (58, 1), (62, 1)] }, { coefficient := -1, powers := [(3, 1), (5, 1), (6, 1), (32, 1), (34, 1), (35, 1), (61, 1)] }, { coefficient := -1, powers := [(3, 1), (6, 1), (14, 1), (26, 1), (32, 1), (35, 1), (61, 1)] }, { coefficient := -1, powers := [(5, 1), (6, 1), (9, 1), (22, 1), (34, 1), (35, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (6, 1), (22, 1), (34, 1), (35, 1), (50, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (6, 1), (22, 1), (34, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (6, 1), (32, 1), (34, 1), (44, 1)] }, { coefficient := 1, powers := [(5, 1), (9, 1), (34, 1), (35, 1), (38, 1)] }, { coefficient := -1, powers := [(5, 1), (34, 1), (35, 1), (38, 1), (50, 1)] }, { coefficient := -1, powers := [(6, 1), (9, 1), (14, 1), (22, 1), (26, 1), (35, 1), (61, 1)] }, { coefficient := 1, powers := [(6, 1), (14, 1), (22, 1), (26, 1), (35, 1), (50, 1), (61, 1)] }, { coefficient := 1, powers := [(6, 1), (14, 1), (22, 1), (26, 1), (58, 1)] }, { coefficient := 1, powers := [(6, 1), (14, 1), (26, 1), (32, 1), (44, 1)] }],
  [{ coefficient := -1, powers := [(23, 1), (32, 1), (38, 1), (62, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (8, 1), (38, 1), (43, 1), (58, 1), (60, 1), (62, 1)] }, { coefficient := 1, powers := [(8, 1), (9, 1), (35, 1), (38, 1), (60, 1)] }, { coefficient := -1, powers := [(8, 1), (35, 1), (38, 1), (50, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (37, 1), (38, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (38, 1), (43, 1), (54, 1), (58, 1), (62, 1)] }, { coefficient := -1, powers := [(3, 1), (6, 1), (32, 1), (35, 1), (54, 1), (61, 1)] }, { coefficient := -1, powers := [(6, 1), (9, 1), (22, 1), (35, 1), (54, 1), (61, 1)] }, { coefficient := 1, powers := [(6, 1), (22, 1), (35, 1), (50, 1), (54, 1), (61, 1)] }, { coefficient := 1, powers := [(6, 1), (22, 1), (54, 1), (58, 1)] }, { coefficient := 1, powers := [(6, 1), (32, 1), (44, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (26, 1), (38, 1), (43, 1), (58, 1), (62, 1)] }, { coefficient := 1, powers := [(3, 1), (6, 1), (26, 1), (32, 1), (35, 1), (61, 1)] }, { coefficient := 1, powers := [(6, 1), (9, 1), (22, 1), (26, 1), (35, 1), (61, 1)] }, { coefficient := -1, powers := [(6, 1), (22, 1), (26, 1), (35, 1), (50, 1), (61, 1)] }, { coefficient := -1, powers := [(6, 1), (22, 1), (26, 1), (58, 1)] }, { coefficient := -1, powers := [(6, 1), (26, 1), (32, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (21, 1), (38, 1), (43, 1), (58, 1), (62, 1)] }, { coefficient := -1, powers := [(3, 1), (6, 1), (21, 1), (32, 1), (35, 1), (61, 1)] }, { coefficient := -1, powers := [(6, 1), (9, 1), (21, 1), (22, 1), (35, 1), (61, 1)] }, { coefficient := 1, powers := [(6, 1), (21, 1), (22, 1), (35, 1), (50, 1), (61, 1)] }, { coefficient := 1, powers := [(6, 1), (21, 1), (22, 1), (58, 1)] }, { coefficient := 1, powers := [(6, 1), (21, 1), (32, 1), (44, 1)] }, { coefficient := 1, powers := [(9, 1), (21, 1), (35, 1), (38, 1)] }, { coefficient := -1, powers := [(21, 1), (35, 1), (38, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (14, 1), (38, 1), (43, 1), (58, 1), (62, 1)] }, { coefficient := -1, powers := [(3, 1), (6, 1), (14, 1), (32, 1), (35, 1), (61, 1)] }, { coefficient := -1, powers := [(6, 1), (9, 1), (14, 1), (22, 1), (35, 1), (61, 1)] }, { coefficient := 1, powers := [(6, 1), (14, 1), (22, 1), (35, 1), (50, 1), (61, 1)] }, { coefficient := 1, powers := [(6, 1), (14, 1), (22, 1), (58, 1)] }, { coefficient := 1, powers := [(6, 1), (14, 1), (32, 1), (44, 1)] }, { coefficient := 1, powers := [(9, 1), (14, 1), (35, 1), (38, 1)] }, { coefficient := -1, powers := [(14, 1), (35, 1), (38, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (32, 1), (61, 1), (62, 1)] }, { coefficient := 1, powers := [(9, 1), (22, 1), (61, 1), (62, 1)] }, { coefficient := -1, powers := [(22, 1), (50, 1), (61, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (8, 1), (32, 1), (35, 1), (61, 1)] }, { coefficient := -1, powers := [(8, 1), (9, 1), (22, 1), (35, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (22, 1), (35, 1), (50, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (22, 1), (58, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(32, 1), (38, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (37, 1), (38, 1)] }, { coefficient := -1, powers := [(37, 1), (38, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (5, 1), (31, 1), (38, 1), (43, 1), (58, 1), (60, 1), (62, 1)] }, { coefficient := 1, powers := [(5, 1), (9, 1), (31, 1), (35, 1), (38, 1), (60, 1)] }, { coefficient := -1, powers := [(5, 1), (31, 1), (35, 1), (38, 1), (50, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(50, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(0, 1), (38, 1), (43, 1), (58, 1), (62, 1)] }, { coefficient := 1, powers := [(3, 1), (6, 1), (32, 1), (35, 1), (61, 1)] }, { coefficient := 1, powers := [(6, 1), (9, 1), (22, 1), (35, 1), (61, 1)] }, { coefficient := -1, powers := [(6, 1), (22, 1), (35, 1), (50, 1), (61, 1)] }, { coefficient := -1, powers := [(6, 1), (22, 1), (58, 1)] }, { coefficient := -1, powers := [(6, 1), (32, 1), (44, 1)] }, { coefficient := -1, powers := [(9, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(35, 1), (38, 1), (50, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (8, 1), (34, 1), (38, 1), (43, 1), (49, 1), (58, 1), (62, 1)] }, { coefficient := 1, powers := [(3, 1), (6, 1), (8, 1), (32, 1), (34, 1), (35, 1), (49, 1), (61, 1)] }, { coefficient := 1, powers := [(3, 1), (8, 1), (32, 1), (34, 1), (35, 1), (38, 1), (49, 1), (61, 1)] }, { coefficient := -1, powers := [(3, 1), (32, 1), (55, 1)] }, { coefficient := 1, powers := [(6, 1), (8, 1), (9, 1), (22, 1), (34, 1), (35, 1), (49, 1), (61, 1)] }, { coefficient := -1, powers := [(6, 1), (8, 1), (22, 1), (34, 1), (35, 1), (49, 1), (50, 1), (61, 1)] }, { coefficient := -1, powers := [(6, 1), (8, 1), (22, 1), (34, 1), (49, 1), (58, 1)] }, { coefficient := -1, powers := [(6, 1), (8, 1), (32, 1), (34, 1), (44, 1), (49, 1)] }, { coefficient := 1, powers := [(8, 1), (9, 1), (22, 1), (34, 1), (35, 1), (38, 1), (49, 1), (61, 1)] }, { coefficient := -1, powers := [(8, 1), (9, 1), (34, 1), (35, 1), (38, 1), (49, 1)] }, { coefficient := -1, powers := [(8, 1), (22, 1), (34, 1), (35, 1), (38, 1), (49, 1), (50, 1), (61, 1)] }, { coefficient := -1, powers := [(8, 1), (22, 1), (34, 1), (38, 1), (49, 1), (58, 1)] }, { coefficient := -1, powers := [(8, 1), (32, 1), (34, 1), (38, 1), (44, 1), (49, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (35, 1), (38, 1), (49, 1), (50, 1)] }, { coefficient := -1, powers := [(9, 1), (22, 1), (55, 1)] }, { coefficient := 1, powers := [(22, 1), (50, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (38, 1), (40, 1), (43, 1), (58, 1), (60, 1), (62, 1)] }, { coefficient := 1, powers := [(0, 1), (38, 1), (43, 2), (57, 1), (58, 1), (62, 1)] }, { coefficient := -1, powers := [(3, 1), (6, 1), (32, 1), (35, 1), (40, 1), (60, 1), (61, 1)] }, { coefficient := -1, powers := [(3, 1), (6, 1), (32, 1), (35, 1), (43, 1), (57, 1), (61, 1)] }, { coefficient := -1, powers := [(6, 1), (9, 1), (22, 1), (35, 1), (40, 1), (60, 1), (61, 1)] }, { coefficient := -1, powers := [(6, 1), (9, 1), (22, 1), (35, 1), (43, 1), (57, 1), (61, 1)] }, { coefficient := 1, powers := [(6, 1), (22, 1), (35, 1), (40, 1), (50, 1), (60, 1), (61, 1)] }, { coefficient := 1, powers := [(6, 1), (22, 1), (35, 1), (43, 1), (50, 1), (57, 1), (61, 1)] }, { coefficient := 1, powers := [(6, 1), (22, 1), (40, 1), (58, 1), (60, 1)] }, { coefficient := 1, powers := [(6, 1), (22, 1), (43, 1), (57, 1), (58, 1)] }, { coefficient := 1, powers := [(6, 1), (32, 1), (40, 1), (44, 1), (60, 1)] }, { coefficient := 1, powers := [(6, 1), (32, 1), (43, 1), (44, 1), (57, 1)] }, { coefficient := 1, powers := [(9, 1), (35, 1), (38, 1), (40, 1), (60, 1)] }, { coefficient := 1, powers := [(9, 1), (35, 1), (38, 1), (43, 1), (57, 1)] }, { coefficient := 1, powers := [(9, 1), (35, 1), (38, 1), (49, 1), (54, 1)] }, { coefficient := -1, powers := [(35, 1), (38, 1), (40, 1), (50, 1), (60, 1)] }, { coefficient := -1, powers := [(35, 1), (38, 1), (43, 1), (50, 1), (57, 1)] }, { coefficient := -1, powers := [(35, 1), (38, 1), (49, 1), (50, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (55, 1)] }, { coefficient := 1, powers := [(6, 1), (35, 1)] }, { coefficient := 1, powers := [(15, 1), (27, 1)] }],
  [{ coefficient := 1, powers := [(0, 2), (5, 1), (31, 1), (38, 1), (43, 1), (58, 1), (60, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 2), (5, 1), (34, 1), (38, 1), (43, 1), (57, 1), (58, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 2), (14, 1), (26, 1), (38, 1), (43, 1), (57, 1), (58, 1), (62, 1)] }, { coefficient := 1, powers := [(0, 1), (3, 1), (5, 1), (6, 1), (32, 1), (34, 1), (35, 1), (57, 1), (61, 1)] }, { coefficient := 1, powers := [(0, 1), (3, 1), (6, 1), (14, 1), (26, 1), (32, 1), (35, 1), (57, 1), (61, 1)] }, { coefficient := 1, powers := [(0, 1), (5, 1), (6, 1), (9, 1), (22, 1), (34, 1), (35, 1), (57, 1), (61, 1)] }, { coefficient := -1, powers := [(0, 1), (5, 1), (6, 1), (22, 1), (34, 1), (35, 1), (50, 1), (57, 1), (61, 1)] }, { coefficient := -1, powers := [(0, 1), (5, 1), (6, 1), (22, 1), (34, 1), (57, 1), (58, 1)] }, { coefficient := -1, powers := [(0, 1), (5, 1), (6, 1), (32, 1), (34, 1), (44, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (5, 1), (9, 1), (31, 1), (35, 1), (38, 1), (60, 1)] }, { coefficient := -1, powers := [(0, 1), (5, 1), (9, 1), (34, 1), (35, 1), (38, 1), (57, 1)] }, { coefficient := -1, powers := [(0, 1), (5, 1), (31, 1), (35, 1), (38, 1), (50, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (5, 1), (34, 1), (35, 1), (38, 1), (50, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (6, 1), (9, 1), (14, 1), (22, 1), (26, 1), (35, 1), (57, 1), (61, 1)] }, { coefficient := -1, powers := [(0, 1), (6, 1), (14, 1), (22, 1), (26, 1), (35, 1), (50, 1), (57, 1), (61, 1)] }, { coefficient := -1, powers := [(0, 1), (6, 1), (14, 1), (22, 1), (26, 1), (57, 1), (58, 1)] }, { coefficient := -1, powers := [(0, 1), (6, 1), (14, 1), (26, 1), (32, 1), (44, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (3, 1), (32, 1), (55, 1), (61, 1)] }, { coefficient := 1, powers := [(0, 1), (8, 1), (27, 1), (34, 1), (38, 1), (43, 1), (49, 1), (58, 1), (61, 1), (62, 1)] }, { coefficient := 1, powers := [(0, 1), (8, 1), (37, 1), (38, 1), (43, 1), (58, 1)] }, { coefficient := -1, powers := [(0, 1), (9, 1), (22, 1), (55, 1), (61, 1)] }, { coefficient := 1, powers := [(0, 1), (22, 1), (50, 1), (55, 1), (61, 1)] }, { coefficient := -1, powers := [(0, 1), (38, 1), (58, 1)] }, { coefficient := -1, powers := [(3, 1), (6, 1), (8, 1), (27, 1), (32, 1), (34, 1), (35, 1), (49, 1), (61, 2)] }, { coefficient := -1, powers := [(3, 1), (6, 1), (32, 1), (35, 1), (61, 1)] }, { coefficient := -1, powers := [(3, 1), (8, 1), (27, 1), (32, 1), (34, 1), (35, 1), (38, 1), (49, 1), (61, 2)] }, { coefficient := -1, powers := [(3, 1), (27, 1), (58, 1)] }, { coefficient := -1, powers := [(6, 1), (8, 1), (9, 1), (22, 1), (27, 1), (34, 1), (35, 1), (49, 1), (61, 2)] }, { coefficient := 1, powers := [(6, 1), (8, 1), (22, 1), (27, 1), (34, 1), (35, 1), (49, 1), (50, 1), (61, 2)] }, { coefficient := 1, powers := [(6, 1), (8, 1), (22, 1), (27, 1), (34, 1), (49, 1), (58, 1), (61, 1)] }, { coefficient := 1, powers := [(6, 1), (8, 1), (27, 1), (32, 1), (34, 1), (44, 1), (49, 1), (61, 1)] }, { coefficient := -1, powers := [(6, 1), (9, 1), (22, 1), (35, 1), (61, 1)] }, { coefficient := 1, powers := [(6, 1), (22, 1), (35, 1), (50, 1), (61, 1)] }, { coefficient := -1, powers := [(8, 1), (9, 1), (22, 1), (27, 1), (34, 1), (35, 1), (38, 1), (49, 1), (61, 2)] }, { coefficient := 1, powers := [(8, 1), (9, 1), (27, 1), (34, 1), (35, 1), (38, 1), (49, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (22, 1), (27, 1), (34, 1), (35, 1), (38, 1), (49, 1), (50, 1), (61, 2)] }, { coefficient := 1, powers := [(8, 1), (22, 1), (27, 1), (34, 1), (38, 1), (49, 1), (58, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (27, 1), (32, 1), (34, 1), (38, 1), (44, 1), (49, 1), (61, 1)] }, { coefficient := -1, powers := [(8, 1), (27, 1), (34, 1), (35, 1), (38, 1), (49, 1), (50, 1), (61, 1)] }, { coefficient := -1, powers := [(9, 1), (27, 1), (44, 1)] }, { coefficient := -1, powers := [(15, 1), (32, 1), (38, 1)] }, { coefficient := 1, powers := [(27, 1), (44, 1), (50, 1)] }]
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
    (values : Fin 63 → R) :
    ¬ ∀ index : Fin 29,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component46.SelectedLeafB4_1.selectedHasNoCommonZero

end Krenn.Component46.SelectedLeafB4_1
