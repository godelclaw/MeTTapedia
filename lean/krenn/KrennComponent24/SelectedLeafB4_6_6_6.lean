import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component24.SelectedLeafB4_6_6_6

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "4bd7dd17d5e8d2e01f3e8d29d6ac620ddcb576b7a2200de049685f9f5f4a1f2f"
def certificateSHA256 : String := "965dbebfe61b8d681595a9939fbde496d38b08559139ea8cd242c21e383c28fe"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 21 → Fin 676 := ![
  15,
  128,
  159,
  161,
  299,
  300,
  307,
  323,
  457,
  471,
  478,
  490,
  585,
  635,
  653,
  663,
  666,
  667,
  669,
  672,
  675
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 21 → SparsePoly (Fin 69) := ![
  [{ coefficient := 1, powers := [(18, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (55, 1)] }, { coefficient := 1, powers := [(20, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (55, 1)] }, { coefficient := 1, powers := [(31, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (45, 1)] }, { coefficient := 1, powers := [(29, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1)] }, { coefficient := 1, powers := [(20, 1), (45, 1)] }, { coefficient := 1, powers := [(26, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (49, 1)] }, { coefficient := 1, powers := [(21, 1), (45, 1)] }, { coefficient := 1, powers := [(26, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (61, 1)] }, { coefficient := 1, powers := [(14, 1), (58, 1)] }, { coefficient := 1, powers := [(19, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (58, 1)] }, { coefficient := 1, powers := [(31, 1), (49, 1)] }, { coefficient := 1, powers := [(37, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1)] }, { coefficient := 1, powers := [(14, 1), (31, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (55, 1)] }, { coefficient := 1, powers := [(31, 1), (43, 1)] }, { coefficient := 1, powers := [(31, 1), (48, 1), (51, 1)] }, { coefficient := 1, powers := [(34, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1), (54, 1)] }, { coefficient := 1, powers := [(3, 1), (61, 1)] }, { coefficient := 1, powers := [(20, 1), (45, 1), (54, 1)] }, { coefficient := 1, powers := [(45, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (49, 1), (54, 1)] }, { coefficient := 1, powers := [(21, 1), (45, 1), (54, 1)] }, { coefficient := 1, powers := [(43, 1), (45, 1)] }, { coefficient := 1, powers := [(49, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (53, 1)] }, { coefficient := 1, powers := [(3, 1), (60, 1)] }, { coefficient := 1, powers := [(20, 1), (53, 1)] }, { coefficient := 1, powers := [(20, 1), (57, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(3, 1), (31, 1), (61, 1)] }, { coefficient := 1, powers := [(3, 1), (34, 1), (58, 1)] }, { coefficient := 1, powers := [(3, 1), (37, 1), (55, 1)] }, { coefficient := 1, powers := [(24, 1), (45, 1), (55, 1)] }, { coefficient := 1, powers := [(24, 1), (51, 1), (58, 1)] }, { coefficient := 1, powers := [(31, 1), (45, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (41, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (52, 1)] }, { coefficient := 1, powers := [(3, 1), (32, 1), (57, 1)] }, { coefficient := 1, powers := [(9, 1), (20, 1), (57, 1)] }, { coefficient := 1, powers := [(9, 1)] }, { coefficient := 1, powers := [(20, 1), (52, 1)] }, { coefficient := 1, powers := [(41, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (40, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (43, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (49, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (37, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (25, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (49, 1)] }, { coefficient := 1, powers := [(8, 1), (37, 1), (43, 1)] }, { coefficient := 1, powers := [(14, 1), (25, 1), (58, 1)] }, { coefficient := 1, powers := [(14, 1), (31, 1), (49, 1)] }, { coefficient := 1, powers := [(14, 1), (37, 1), (40, 1)] }, { coefficient := 1, powers := [(19, 1), (25, 1), (55, 1)] }, { coefficient := 1, powers := [(19, 1), (31, 1), (43, 1)] }, { coefficient := 1, powers := [(19, 1), (34, 1), (40, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(41, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(43, 1)] }],
  [{ coefficient := 1, powers := [(58, 1)] }],
  [{ coefficient := 1, powers := [(31, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 21 → SparsePoly (Fin 69) := ![
  [{ coefficient := -1, powers := [(0, 1), (9, 1), (24, 1), (49, 1), (53, 1), (63, 1)] }, { coefficient := 1, powers := [(0, 1), (24, 1), (41, 1), (49, 1), (53, 1), (63, 1)] }, { coefficient := 1, powers := [(0, 1), (24, 1), (41, 1), (49, 1), (57, 1), (63, 1)] }, { coefficient := 1, powers := [(0, 1), (24, 1), (49, 1), (52, 1), (63, 1)] }, { coefficient := -1, powers := [(3, 1), (9, 1), (24, 1), (49, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(3, 1), (24, 1), (32, 1), (49, 1), (57, 1), (63, 1)] }, { coefficient := 1, powers := [(3, 1), (24, 1), (41, 1), (49, 1), (60, 1), (63, 1)] }, { coefficient := -1, powers := [(9, 1), (20, 1), (24, 1), (49, 1), (53, 1), (63, 1)] }, { coefficient := 1, powers := [(20, 1), (24, 1), (41, 1), (49, 1), (53, 1), (63, 1)] }, { coefficient := 1, powers := [(20, 1), (24, 1), (41, 1), (49, 1), (57, 1), (63, 1)] }, { coefficient := 1, powers := [(20, 1), (24, 1), (49, 1), (52, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (9, 1), (37, 1), (53, 1), (63, 1)] }, { coefficient := -1, powers := [(5, 1), (37, 1), (41, 1), (53, 1), (63, 1)] }, { coefficient := -1, powers := [(5, 1), (37, 1), (41, 1), (57, 1), (63, 1)] }, { coefficient := -1, powers := [(5, 1), (37, 1), (52, 1), (63, 1)] }, { coefficient := -1, powers := [(9, 1), (19, 1), (25, 1), (53, 1), (63, 1)] }, { coefficient := 1, powers := [(19, 1), (25, 1), (41, 1), (53, 1), (63, 1)] }, { coefficient := 1, powers := [(19, 1), (25, 1), (41, 1), (57, 1), (63, 1)] }, { coefficient := 1, powers := [(19, 1), (25, 1), (52, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (9, 1), (45, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (45, 1), (57, 1), (63, 1)] }, { coefficient := 1, powers := [(5, 1), (41, 1), (45, 1), (60, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (9, 1), (26, 1), (54, 1), (60, 1), (63, 1)] }, { coefficient := -1, powers := [(8, 1), (9, 1), (51, 1), (60, 1), (63, 1)] }, { coefficient := -1, powers := [(8, 1), (26, 1), (32, 1), (54, 1), (57, 1), (63, 1)] }, { coefficient := -1, powers := [(8, 1), (26, 1), (41, 1), (54, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (51, 1), (57, 1), (63, 1)] }, { coefficient := 1, powers := [(8, 1), (41, 1), (51, 1), (60, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (9, 1), (25, 1), (54, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(8, 1), (25, 1), (32, 1), (54, 1), (57, 1), (63, 1)] }, { coefficient := 1, powers := [(8, 1), (25, 1), (41, 1), (54, 1), (60, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (9, 1), (29, 1), (54, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(8, 1), (29, 1), (32, 1), (54, 1), (57, 1), (63, 1)] }, { coefficient := 1, powers := [(8, 1), (29, 1), (41, 1), (54, 1), (60, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (9, 1), (25, 1), (53, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (25, 1), (41, 1), (53, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (25, 1), (41, 1), (57, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (25, 1), (52, 1), (63, 1)] }, { coefficient := 1, powers := [(9, 1), (20, 1), (25, 1), (53, 1), (63, 1)] }, { coefficient := -1, powers := [(20, 1), (25, 1), (41, 1), (53, 1), (63, 1)] }, { coefficient := -1, powers := [(20, 1), (25, 1), (41, 1), (57, 1), (63, 1)] }, { coefficient := -1, powers := [(20, 1), (25, 1), (52, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (9, 1), (14, 1), (53, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (14, 1), (41, 1), (53, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (14, 1), (41, 1), (57, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (14, 1), (52, 1), (63, 1)] }, { coefficient := 1, powers := [(3, 1), (9, 1), (14, 1), (60, 1), (63, 1)] }, { coefficient := -1, powers := [(3, 1), (14, 1), (32, 1), (57, 1), (63, 1)] }, { coefficient := -1, powers := [(3, 1), (14, 1), (41, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(9, 1), (14, 1), (20, 1), (53, 1), (63, 1)] }, { coefficient := -1, powers := [(14, 1), (20, 1), (41, 1), (53, 1), (63, 1)] }, { coefficient := -1, powers := [(14, 1), (20, 1), (41, 1), (57, 1), (63, 1)] }, { coefficient := -1, powers := [(14, 1), (20, 1), (52, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (9, 1), (49, 1), (53, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (41, 1), (49, 1), (53, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (41, 1), (49, 1), (57, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (49, 1), (52, 1), (63, 1)] }, { coefficient := 1, powers := [(3, 1), (9, 1), (49, 1), (60, 1), (63, 1)] }, { coefficient := -1, powers := [(3, 1), (32, 1), (49, 1), (57, 1), (63, 1)] }, { coefficient := -1, powers := [(3, 1), (41, 1), (49, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(9, 1), (20, 1), (49, 1), (53, 1), (63, 1)] }, { coefficient := -1, powers := [(20, 1), (41, 1), (49, 1), (53, 1), (63, 1)] }, { coefficient := -1, powers := [(20, 1), (41, 1), (49, 1), (57, 1), (63, 1)] }, { coefficient := -1, powers := [(20, 1), (49, 1), (52, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (9, 1), (19, 1), (53, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (19, 1), (41, 1), (53, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (19, 1), (41, 1), (57, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (19, 1), (52, 1), (63, 1)] }, { coefficient := 1, powers := [(3, 1), (9, 1), (19, 1), (60, 1), (63, 1)] }, { coefficient := -1, powers := [(3, 1), (19, 1), (32, 1), (57, 1), (63, 1)] }, { coefficient := -1, powers := [(3, 1), (19, 1), (41, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(9, 1), (19, 1), (20, 1), (53, 1), (63, 1)] }, { coefficient := -1, powers := [(19, 1), (20, 1), (41, 1), (53, 1), (63, 1)] }, { coefficient := -1, powers := [(19, 1), (20, 1), (41, 1), (57, 1), (63, 1)] }, { coefficient := -1, powers := [(19, 1), (20, 1), (52, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (9, 1), (25, 1), (60, 1), (63, 1)] }, { coefficient := -1, powers := [(8, 1), (25, 1), (32, 1), (57, 1), (63, 1)] }, { coefficient := -1, powers := [(8, 1), (25, 1), (41, 1), (60, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (9, 1), (29, 1), (60, 1), (63, 1)] }, { coefficient := -1, powers := [(8, 1), (29, 1), (32, 1), (57, 1), (63, 1)] }, { coefficient := -1, powers := [(8, 1), (29, 1), (41, 1), (60, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(9, 1), (63, 1)] }, { coefficient := 1, powers := [(41, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (9, 1), (60, 1), (63, 1)] }, { coefficient := -1, powers := [(5, 1), (32, 1), (57, 1), (63, 1)] }, { coefficient := -1, powers := [(5, 1), (41, 1), (60, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(63, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (9, 1), (53, 1), (63, 1)] }, { coefficient := 1, powers := [(0, 1), (41, 1), (53, 1), (63, 1)] }, { coefficient := 1, powers := [(0, 1), (41, 1), (57, 1), (63, 1)] }, { coefficient := 1, powers := [(0, 1), (52, 1), (63, 1)] }, { coefficient := -1, powers := [(3, 1), (9, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(3, 1), (32, 1), (57, 1), (63, 1)] }, { coefficient := 1, powers := [(3, 1), (41, 1), (60, 1), (63, 1)] }, { coefficient := -1, powers := [(9, 1), (20, 1), (53, 1), (63, 1)] }, { coefficient := 1, powers := [(20, 1), (41, 1), (53, 1), (63, 1)] }, { coefficient := 1, powers := [(20, 1), (41, 1), (57, 1), (63, 1)] }, { coefficient := 1, powers := [(20, 1), (52, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (9, 1), (40, 1), (53, 1), (61, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (40, 1), (41, 1), (53, 1), (61, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (40, 1), (41, 1), (57, 1), (61, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (40, 1), (52, 1), (61, 1), (63, 1)] }, { coefficient := 1, powers := [(3, 1), (9, 1), (40, 1), (60, 1), (61, 1), (63, 1)] }, { coefficient := -1, powers := [(3, 1), (32, 1), (40, 1), (57, 1), (61, 1), (63, 1)] }, { coefficient := -1, powers := [(3, 1), (40, 1), (41, 1), (60, 1), (61, 1), (63, 1)] }, { coefficient := 1, powers := [(9, 1), (20, 1), (40, 1), (53, 1), (61, 1), (63, 1)] }, { coefficient := -1, powers := [(20, 1), (40, 1), (41, 1), (53, 1), (61, 1), (63, 1)] }, { coefficient := -1, powers := [(20, 1), (40, 1), (41, 1), (57, 1), (61, 1), (63, 1)] }, { coefficient := -1, powers := [(20, 1), (40, 1), (52, 1), (61, 1), (63, 1)] }],
  [{ coefficient := -2, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (8, 1), (9, 1), (37, 1), (53, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (8, 1), (37, 1), (41, 1), (53, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (8, 1), (37, 1), (41, 1), (57, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (8, 1), (37, 1), (52, 1), (63, 1)] }, { coefficient := 1, powers := [(3, 1), (8, 1), (9, 1), (37, 1), (60, 1), (63, 1)] }, { coefficient := -1, powers := [(3, 1), (8, 1), (32, 1), (37, 1), (57, 1), (63, 1)] }, { coefficient := -1, powers := [(3, 1), (8, 1), (37, 1), (41, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(8, 1), (9, 1), (20, 1), (37, 1), (53, 1), (63, 1)] }, { coefficient := -1, powers := [(8, 1), (9, 1), (29, 1), (45, 1), (60, 1), (63, 1)] }, { coefficient := -1, powers := [(8, 1), (20, 1), (37, 1), (41, 1), (53, 1), (63, 1)] }, { coefficient := -1, powers := [(8, 1), (20, 1), (37, 1), (41, 1), (57, 1), (63, 1)] }, { coefficient := -1, powers := [(8, 1), (20, 1), (37, 1), (52, 1), (63, 1)] }, { coefficient := 1, powers := [(8, 1), (29, 1), (32, 1), (45, 1), (57, 1), (63, 1)] }, { coefficient := 1, powers := [(8, 1), (29, 1), (41, 1), (45, 1), (60, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (2, 1), (9, 1), (43, 1), (53, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (2, 1), (41, 1), (43, 1), (53, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (2, 1), (41, 1), (43, 1), (57, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (2, 1), (43, 1), (52, 1), (63, 1)] }, { coefficient := 1, powers := [(0, 1), (5, 1), (9, 1), (34, 1), (53, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (5, 1), (34, 1), (41, 1), (53, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (5, 1), (34, 1), (41, 1), (57, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (5, 1), (34, 1), (52, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (9, 1), (14, 1), (25, 1), (53, 1), (63, 1)] }, { coefficient := 1, powers := [(0, 1), (14, 1), (25, 1), (41, 1), (53, 1), (63, 1)] }, { coefficient := 1, powers := [(0, 1), (14, 1), (25, 1), (41, 1), (57, 1), (63, 1)] }, { coefficient := 1, powers := [(0, 1), (14, 1), (25, 1), (52, 1), (63, 1)] }, { coefficient := 1, powers := [(2, 1), (3, 1), (9, 1), (43, 1), (60, 1), (63, 1)] }, { coefficient := -1, powers := [(2, 1), (3, 1), (32, 1), (43, 1), (57, 1), (63, 1)] }, { coefficient := -1, powers := [(2, 1), (3, 1), (41, 1), (43, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(2, 1), (9, 1), (20, 1), (43, 1), (53, 1), (63, 1)] }, { coefficient := -1, powers := [(2, 1), (20, 1), (41, 1), (43, 1), (53, 1), (63, 1)] }, { coefficient := -1, powers := [(2, 1), (20, 1), (41, 1), (43, 1), (57, 1), (63, 1)] }, { coefficient := -1, powers := [(2, 1), (20, 1), (43, 1), (52, 1), (63, 1)] }, { coefficient := 1, powers := [(5, 1), (9, 1), (20, 1), (34, 1), (53, 1), (63, 1)] }, { coefficient := -1, powers := [(5, 1), (9, 1), (24, 1), (51, 1), (60, 1), (63, 1)] }, { coefficient := -1, powers := [(5, 1), (20, 1), (34, 1), (41, 1), (53, 1), (63, 1)] }, { coefficient := -1, powers := [(5, 1), (20, 1), (34, 1), (41, 1), (57, 1), (63, 1)] }, { coefficient := -1, powers := [(5, 1), (20, 1), (34, 1), (52, 1), (63, 1)] }, { coefficient := 1, powers := [(5, 1), (24, 1), (32, 1), (51, 1), (57, 1), (63, 1)] }, { coefficient := 1, powers := [(5, 1), (24, 1), (41, 1), (51, 1), (60, 1), (63, 1)] }, { coefficient := -1, powers := [(9, 1), (14, 1), (20, 1), (25, 1), (53, 1), (63, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1), (25, 1), (41, 1), (53, 1), (63, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1), (25, 1), (41, 1), (57, 1), (63, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1), (25, 1), (52, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (5, 1), (9, 1), (53, 1), (61, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (5, 1), (41, 1), (53, 1), (61, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (5, 1), (41, 1), (57, 1), (61, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (5, 1), (52, 1), (61, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (9, 1), (14, 1), (49, 1), (53, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (9, 1), (19, 1), (48, 1), (51, 1), (53, 1), (63, 1)] }, { coefficient := 1, powers := [(0, 1), (14, 1), (41, 1), (49, 1), (53, 1), (63, 1)] }, { coefficient := 1, powers := [(0, 1), (14, 1), (41, 1), (49, 1), (57, 1), (63, 1)] }, { coefficient := 1, powers := [(0, 1), (14, 1), (49, 1), (52, 1), (63, 1)] }, { coefficient := 1, powers := [(0, 1), (19, 1), (41, 1), (48, 1), (51, 1), (53, 1), (63, 1)] }, { coefficient := 1, powers := [(0, 1), (19, 1), (41, 1), (48, 1), (51, 1), (57, 1), (63, 1)] }, { coefficient := 1, powers := [(0, 1), (19, 1), (48, 1), (51, 1), (52, 1), (63, 1)] }, { coefficient := -1, powers := [(3, 1), (9, 1), (14, 1), (49, 1), (60, 1), (63, 1)] }, { coefficient := -1, powers := [(3, 1), (9, 1), (19, 1), (48, 1), (51, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(3, 1), (14, 1), (32, 1), (49, 1), (57, 1), (63, 1)] }, { coefficient := 1, powers := [(3, 1), (14, 1), (41, 1), (49, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(3, 1), (19, 1), (32, 1), (48, 1), (51, 1), (57, 1), (63, 1)] }, { coefficient := 1, powers := [(3, 1), (19, 1), (41, 1), (48, 1), (51, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(5, 1), (9, 1), (20, 1), (53, 1), (61, 1), (63, 1)] }, { coefficient := -1, powers := [(5, 1), (20, 1), (41, 1), (53, 1), (61, 1), (63, 1)] }, { coefficient := -1, powers := [(5, 1), (20, 1), (41, 1), (57, 1), (61, 1), (63, 1)] }, { coefficient := -1, powers := [(5, 1), (20, 1), (52, 1), (61, 1), (63, 1)] }, { coefficient := -1, powers := [(9, 1), (14, 1), (20, 1), (49, 1), (53, 1), (63, 1)] }, { coefficient := -1, powers := [(9, 1), (19, 1), (20, 1), (48, 1), (51, 1), (53, 1), (63, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1), (41, 1), (49, 1), (53, 1), (63, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1), (41, 1), (49, 1), (57, 1), (63, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1), (49, 1), (52, 1), (63, 1)] }, { coefficient := 1, powers := [(19, 1), (20, 1), (41, 1), (48, 1), (51, 1), (53, 1), (63, 1)] }, { coefficient := 1, powers := [(19, 1), (20, 1), (41, 1), (48, 1), (51, 1), (57, 1), (63, 1)] }, { coefficient := 1, powers := [(19, 1), (20, 1), (48, 1), (51, 1), (52, 1), (63, 1)] }]
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
    (values : Fin 69 → R) :
    ¬ ∀ index : Fin 21,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((2 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (2 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (2 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component24.SelectedLeafB4_6_6_6.selectedHasNoCommonZero

end Krenn.Component24.SelectedLeafB4_6_6_6
