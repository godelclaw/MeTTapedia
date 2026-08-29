import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component53.SelectedLeafB4_2

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "088787d63bafbe808cb5cb660647c258351def0173fbb2affdc697d9457ac094"
def certificateSHA256 : String := "36b1b1cce0db76776121d2d1250a8e90111d954fbcb2935e2664816c7e62a483"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 37 → Fin 643 := ![
  2,
  3,
  4,
  5,
  11,
  12,
  22,
  23,
  26,
  27,
  38,
  162,
  164,
  193,
  230,
  240,
  244,
  311,
  347,
  348,
  349,
  359,
  360,
  387,
  394,
  411,
  491,
  513,
  578,
  579,
  584,
  634,
  636,
  637,
  639,
  640,
  642
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 37 → SparsePoly (Fin 63) := ![
  [{ coefficient := 1, powers := [(3, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (35, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (26, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (22, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(32, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (48, 1)] }, { coefficient := 1, powers := [(26, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (54, 1)] }, { coefficient := 1, powers := [(22, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(15, 1), (25, 1)] }, { coefficient := 1, powers := [(25, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (31, 1), (59, 1)] }, { coefficient := 1, powers := [(31, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (35, 1), (50, 1)] }, { coefficient := 1, powers := [(5, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (25, 1), (59, 1)] }, { coefficient := 1, powers := [(25, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (26, 1), (45, 1)] }, { coefficient := 1, powers := [(14, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (48, 1)] }, { coefficient := 1, powers := [(5, 1), (37, 1)] }, { coefficient := 1, powers := [(21, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1)] }, { coefficient := 1, powers := [(14, 1), (31, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (60, 1)] }, { coefficient := 1, powers := [(14, 1), (48, 1)] }, { coefficient := 1, powers := [(21, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (54, 1)] }, { coefficient := 1, powers := [(31, 1), (43, 1)] }, { coefficient := 1, powers := [(34, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (57, 1)] }, { coefficient := 1, powers := [(31, 1), (48, 1)] }, { coefficient := 1, powers := [(37, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (43, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (55, 1)] }, { coefficient := 1, powers := [(14, 1), (25, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (31, 1), (60, 1)] }, { coefficient := 1, powers := [(3, 1), (34, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (37, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (22, 1), (60, 1)] }, { coefficient := 1, powers := [(14, 1), (22, 1), (57, 1)] }, { coefficient := 1, powers := [(21, 1), (22, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (40, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (59, 1)] }, { coefficient := 1, powers := [(8, 1), (25, 1), (59, 1)] }, { coefficient := 1, powers := [(20, 1), (25, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (32, 1), (57, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (48, 1)] }, { coefficient := 1, powers := [(13, 1), (27, 1), (48, 1)] }, { coefficient := 1, powers := [(21, 1), (32, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1)] }, { coefficient := 1, powers := [(3, 1), (35, 1)] }, { coefficient := 1, powers := [(15, 1), (22, 1)] }, { coefficient := 1, powers := [(22, 1), (55, 1)] }, { coefficient := 1, powers := [(26, 1), (44, 1)] }, { coefficient := 1, powers := [(35, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (49, 1)] }, { coefficient := 1, powers := [(6, 1), (32, 1)] }, { coefficient := 1, powers := [(9, 1), (26, 1)] }, { coefficient := 1, powers := [(22, 1), (49, 1)] }, { coefficient := 1, powers := [(26, 1), (41, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (38, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1)] }, { coefficient := 1, powers := [(3, 1), (26, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (22, 1), (59, 1)] }, { coefficient := 1, powers := [(22, 1)] }, { coefficient := 1, powers := [(26, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (38, 1), (58, 1)] }, { coefficient := 1, powers := [(0, 1), (41, 1), (55, 1)] }, { coefficient := 1, powers := [(0, 1), (44, 1), (49, 1)] }, { coefficient := 1, powers := [(3, 1), (26, 1), (58, 1)] }, { coefficient := 1, powers := [(3, 1), (32, 1), (55, 1)] }, { coefficient := 1, powers := [(3, 1), (35, 1), (49, 1)] }, { coefficient := 1, powers := [(6, 1), (22, 1), (58, 1)] }, { coefficient := 1, powers := [(6, 1), (32, 1), (44, 1)] }, { coefficient := 1, powers := [(6, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(9, 1), (22, 1), (55, 1)] }, { coefficient := 1, powers := [(9, 1), (26, 1), (44, 1)] }, { coefficient := 1, powers := [(9, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(15, 1), (22, 1), (49, 1)] }, { coefficient := 1, powers := [(15, 1), (26, 1), (41, 1)] }, { coefficient := 1, powers := [(15, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (40, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (43, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (48, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (37, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (25, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (48, 1)] }, { coefficient := 1, powers := [(8, 1), (37, 1), (43, 1)] }, { coefficient := 1, powers := [(14, 1), (25, 1), (57, 1)] }, { coefficient := 1, powers := [(14, 1), (31, 1), (48, 1)] }, { coefficient := 1, powers := [(14, 1), (37, 1), (40, 1)] }, { coefficient := 1, powers := [(21, 1), (25, 1), (54, 1)] }, { coefficient := 1, powers := [(21, 1), (31, 1), (43, 1)] }, { coefficient := 1, powers := [(21, 1), (34, 1), (40, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (61, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(41, 1)] }],
  [{ coefficient := 1, powers := [(43, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 37 → SparsePoly (Fin 63) := ![
  [{ coefficient := -2, powers := [(5, 1), (6, 1), (22, 1), (31, 1), (58, 1), (59, 1)] }, { coefficient := -2, powers := [(5, 1), (9, 1), (22, 1), (31, 1), (55, 1), (59, 1)] }, { coefficient := -1, powers := [(5, 1), (15, 1), (31, 1), (32, 1), (38, 1), (59, 1)] }, { coefficient := 2, powers := [(5, 1), (22, 1), (31, 1), (49, 1), (55, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (26, 1), (31, 1), (44, 1), (49, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (26, 1), (31, 1), (58, 1)] }, { coefficient := -1, powers := [(5, 1), (31, 1), (32, 1), (38, 1), (44, 1), (59, 1)] }, { coefficient := -2, powers := [(5, 1), (31, 1), (32, 1), (38, 1), (55, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (32, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (25, 1), (26, 1), (44, 1), (49, 1), (59, 1)] }, { coefficient := 1, powers := [(8, 1), (25, 1), (26, 1), (58, 1)] }, { coefficient := 1, powers := [(8, 1), (25, 1), (32, 1), (55, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (31, 1), (38, 1), (50, 1), (60, 1)] }, { coefficient := -1, powers := [(0, 1), (34, 1), (38, 1), (50, 1), (57, 1)] }, { coefficient := -1, powers := [(0, 1), (37, 1), (38, 1), (50, 1), (54, 1)] }, { coefficient := 2, powers := [(9, 1), (31, 1), (38, 1), (60, 1)] }, { coefficient := 1, powers := [(9, 1), (34, 1), (38, 1), (57, 1)] }, { coefficient := 1, powers := [(9, 1), (37, 1), (38, 1), (54, 1)] }, { coefficient := -2, powers := [(31, 1), (38, 1), (49, 1), (60, 1)] }, { coefficient := -1, powers := [(34, 1), (38, 1), (49, 1), (57, 1)] }, { coefficient := -1, powers := [(37, 1), (38, 1), (49, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (31, 1), (38, 1), (44, 1), (49, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (34, 1), (38, 1), (44, 1), (49, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (37, 1), (38, 1), (44, 1), (49, 1), (54, 1)] }, { coefficient := 1, powers := [(6, 1), (22, 1), (31, 1), (44, 1), (49, 1), (60, 1)] }, { coefficient := 1, powers := [(6, 1), (22, 1), (34, 1), (44, 1), (49, 1), (57, 1)] }, { coefficient := 1, powers := [(6, 1), (22, 1), (37, 1), (44, 1), (49, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (8, 1), (25, 1), (32, 1), (38, 1), (44, 1), (59, 1), (61, 1)] }, { coefficient := 1, powers := [(0, 1), (8, 1), (25, 1), (32, 1), (38, 1), (55, 1), (59, 1), (61, 1)] }, { coefficient := -1, powers := [(0, 1), (8, 1), (25, 1), (38, 1), (58, 1), (59, 1)] }, { coefficient := -1, powers := [(8, 1), (9, 1), (25, 1), (35, 1), (38, 1), (59, 1)] }, { coefficient := 1, powers := [(8, 1), (25, 1), (35, 1), (38, 1), (49, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(15, 1), (27, 1), (34, 1), (38, 1)] }, { coefficient := 1, powers := [(27, 1), (34, 1), (38, 1), (44, 1)] }],
  [{ coefficient := -1, powers := [(22, 1), (25, 1), (45, 1), (49, 1), (57, 1)] }, { coefficient := -2, powers := [(31, 1), (32, 1), (38, 1), (44, 1), (48, 1), (61, 1)] }, { coefficient := -2, powers := [(31, 1), (32, 1), (38, 1), (48, 1), (55, 1), (61, 1)] }],
  [{ coefficient := -2, powers := [(6, 1), (25, 1), (54, 1), (58, 1)] }, { coefficient := -2, powers := [(9, 1), (25, 1), (54, 1), (55, 1)] }, { coefficient := -1, powers := [(25, 1), (32, 1), (38, 1), (44, 1), (54, 1), (61, 1)] }, { coefficient := -1, powers := [(25, 1), (32, 1), (38, 1), (54, 1), (55, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (6, 1), (34, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (9, 1), (34, 1), (55, 1)] }, { coefficient := -1, powers := [(6, 1), (14, 1), (25, 1), (58, 1)] }, { coefficient := -1, powers := [(9, 1), (14, 1), (25, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (15, 1), (22, 1), (60, 1)] }, { coefficient := -1, powers := [(15, 1), (21, 1), (22, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (20, 1), (38, 1), (44, 1), (49, 1), (60, 1)] }, { coefficient := -1, powers := [(6, 1), (20, 1), (22, 1), (44, 1), (49, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(15, 1), (21, 1), (34, 1), (38, 1)] }, { coefficient := 1, powers := [(21, 1), (34, 1), (38, 1), (44, 1)] }],
  [{ coefficient := 2, powers := [(14, 1), (31, 1), (32, 1), (38, 1), (44, 1), (61, 1)] }, { coefficient := 2, powers := [(14, 1), (31, 1), (32, 1), (38, 1), (55, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (32, 1), (37, 1), (38, 1), (44, 1), (61, 1)] }, { coefficient := -1, powers := [(5, 1), (32, 1), (37, 1), (38, 1), (55, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (22, 1), (49, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (38, 1), (60, 1)] }, { coefficient := 1, powers := [(21, 1), (22, 1), (49, 1), (54, 1)] }, { coefficient := -1, powers := [(21, 1), (32, 1), (38, 1), (54, 1)] }],
  [{ coefficient := 2, powers := [(5, 1), (6, 1), (22, 1), (58, 1), (60, 1)] }, { coefficient := 2, powers := [(5, 1), (9, 1), (22, 1), (55, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (15, 1), (32, 1), (38, 1), (60, 1)] }, { coefficient := -2, powers := [(5, 1), (22, 1), (49, 1), (55, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (38, 1), (44, 1), (60, 1)] }, { coefficient := 2, powers := [(5, 1), (32, 1), (38, 1), (55, 1), (60, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (31, 1), (38, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (34, 1), (38, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (37, 1), (38, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (8, 1), (32, 1), (38, 1), (44, 1), (60, 1), (61, 1)] }, { coefficient := -1, powers := [(0, 1), (8, 1), (32, 1), (38, 1), (55, 1), (60, 1), (61, 1)] }, { coefficient := 1, powers := [(0, 1), (8, 1), (38, 1), (58, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (9, 1), (35, 1), (38, 1), (60, 1)] }, { coefficient := -1, powers := [(8, 1), (35, 1), (38, 1), (49, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (25, 1), (49, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (22, 1), (54, 1), (58, 1)] }, { coefficient := 1, powers := [(9, 1), (22, 1), (54, 1), (55, 1)] }, { coefficient := 1, powers := [(15, 1), (32, 1), (38, 1), (54, 1)] }, { coefficient := 1, powers := [(22, 1), (32, 1), (38, 1), (44, 1), (54, 1), (61, 1)] }, { coefficient := 1, powers := [(22, 1), (32, 1), (38, 1), (54, 1), (55, 1), (61, 1)] }, { coefficient := -1, powers := [(22, 1), (49, 1), (54, 1), (55, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1), (54, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (32, 1), (38, 1), (44, 1), (48, 1), (61, 1)] }, { coefficient := -1, powers := [(0, 1), (32, 1), (38, 1), (48, 1), (55, 1), (61, 1)] }, { coefficient := 1, powers := [(0, 1), (38, 1), (44, 1), (48, 1), (49, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (38, 1), (48, 1), (58, 1)] }, { coefficient := 1, powers := [(3, 1), (26, 1), (44, 1), (48, 1), (49, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (26, 1), (48, 1), (58, 1)] }, { coefficient := 1, powers := [(3, 1), (32, 1), (48, 1), (55, 1)] }, { coefficient := 1, powers := [(6, 1), (22, 1), (44, 1), (48, 1), (49, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (22, 1), (48, 1), (58, 1)] }, { coefficient := 1, powers := [(9, 1), (22, 1), (48, 1), (55, 1)] }, { coefficient := 1, powers := [(9, 1), (35, 1), (38, 1), (48, 1)] }, { coefficient := -1, powers := [(22, 1), (48, 1), (49, 1), (55, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1), (44, 1), (48, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1), (48, 1), (55, 1)] }, { coefficient := -1, powers := [(35, 1), (38, 1), (48, 1), (49, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (31, 1), (32, 1), (38, 1), (44, 1), (61, 1)] }, { coefficient := -1, powers := [(0, 1), (31, 1), (32, 1), (38, 1), (55, 1), (61, 1)] }, { coefficient := -1, powers := [(0, 1), (31, 1), (38, 1), (44, 1), (49, 1), (59, 1)] }, { coefficient := -1, powers := [(0, 1), (31, 1), (38, 1), (58, 1)] }, { coefficient := -1, powers := [(3, 1), (26, 1), (31, 1), (44, 1), (49, 1), (59, 1)] }, { coefficient := -1, powers := [(3, 1), (26, 1), (31, 1), (58, 1)] }, { coefficient := -1, powers := [(3, 1), (31, 1), (32, 1), (55, 1)] }, { coefficient := -1, powers := [(6, 1), (22, 1), (31, 1), (44, 1), (49, 1), (59, 1)] }, { coefficient := -1, powers := [(6, 1), (22, 1), (31, 1), (58, 1)] }, { coefficient := -1, powers := [(9, 1), (22, 1), (31, 1), (55, 1)] }, { coefficient := -1, powers := [(9, 1), (31, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(22, 1), (31, 1), (49, 1), (55, 1)] }, { coefficient := -1, powers := [(31, 1), (32, 1), (38, 1), (44, 1)] }, { coefficient := -1, powers := [(31, 1), (32, 1), (38, 1), (55, 1)] }, { coefficient := 1, powers := [(31, 1), (35, 1), (38, 1), (49, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (21, 1), (32, 1), (38, 1), (44, 1), (61, 1)] }, { coefficient := -1, powers := [(0, 1), (21, 1), (32, 1), (38, 1), (55, 1), (61, 1)] }, { coefficient := 1, powers := [(0, 1), (21, 1), (38, 1), (44, 1), (49, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (21, 1), (38, 1), (58, 1)] }, { coefficient := 1, powers := [(3, 1), (21, 1), (26, 1), (44, 1), (49, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (21, 1), (26, 1), (58, 1)] }, { coefficient := 1, powers := [(3, 1), (21, 1), (32, 1), (55, 1)] }, { coefficient := 1, powers := [(6, 1), (21, 1), (22, 1), (44, 1), (49, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (21, 1), (22, 1), (58, 1)] }, { coefficient := 1, powers := [(9, 1), (21, 1), (22, 1), (55, 1)] }, { coefficient := 1, powers := [(9, 1), (21, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(15, 1), (21, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [(21, 1), (22, 1), (49, 1), (55, 1)] }, { coefficient := 1, powers := [(21, 1), (32, 1), (38, 1), (55, 1)] }, { coefficient := -1, powers := [(21, 1), (35, 1), (38, 1), (49, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (14, 1), (32, 1), (38, 1), (44, 1), (61, 1)] }, { coefficient := -1, powers := [(0, 1), (14, 1), (32, 1), (38, 1), (55, 1), (61, 1)] }, { coefficient := 1, powers := [(0, 1), (14, 1), (38, 1), (44, 1), (49, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (14, 1), (38, 1), (58, 1)] }, { coefficient := 1, powers := [(3, 1), (14, 1), (26, 1), (44, 1), (49, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (14, 1), (26, 1), (58, 1)] }, { coefficient := 1, powers := [(3, 1), (14, 1), (32, 1), (55, 1)] }, { coefficient := 1, powers := [(6, 1), (14, 1), (22, 1), (44, 1), (49, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (14, 1), (22, 1), (58, 1)] }, { coefficient := 1, powers := [(9, 1), (14, 1), (22, 1), (55, 1)] }, { coefficient := 1, powers := [(9, 1), (14, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(14, 1), (15, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [(14, 1), (22, 1), (49, 1), (55, 1)] }, { coefficient := 1, powers := [(14, 1), (32, 1), (38, 1), (55, 1)] }, { coefficient := -1, powers := [(14, 1), (35, 1), (38, 1), (49, 1)] }],
  [{ coefficient := -1, powers := [(22, 1), (49, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (26, 1), (44, 1), (49, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (26, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (25, 1), (58, 1)] }, { coefficient := 1, powers := [(9, 1), (25, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (38, 1), (44, 1), (49, 1), (60, 1)] }, { coefficient := 1, powers := [(6, 1), (22, 1), (44, 1), (49, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(15, 1), (34, 1), (38, 1)] }, { coefficient := -1, powers := [(34, 1), (38, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(49, 1)] }],
  [{ coefficient := 1, powers := [(44, 1)] }],
  [{ coefficient := -1, powers := [(44, 1), (49, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (32, 1), (38, 1), (44, 1), (61, 1)] }, { coefficient := 1, powers := [(0, 1), (32, 1), (38, 1), (55, 1), (61, 1)] }, { coefficient := -1, powers := [(0, 1), (38, 1), (44, 1), (49, 1), (59, 1)] }, { coefficient := -1, powers := [(0, 1), (38, 1), (58, 1)] }, { coefficient := -1, powers := [(3, 1), (26, 1), (44, 1), (49, 1), (59, 1)] }, { coefficient := -1, powers := [(3, 1), (26, 1), (58, 1)] }, { coefficient := -1, powers := [(3, 1), (32, 1), (55, 1)] }, { coefficient := -1, powers := [(6, 1), (22, 1), (44, 1), (49, 1), (59, 1)] }, { coefficient := -1, powers := [(6, 1), (22, 1), (58, 1)] }, { coefficient := -1, powers := [(9, 1), (22, 1), (55, 1)] }, { coefficient := -1, powers := [(9, 1), (35, 1), (38, 1)] }, { coefficient := -1, powers := [(15, 1), (32, 1), (38, 1)] }, { coefficient := 1, powers := [(22, 1), (49, 1), (55, 1)] }, { coefficient := -1, powers := [(32, 1), (38, 1), (55, 1)] }, { coefficient := 1, powers := [(35, 1), (38, 1), (49, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (32, 1), (34, 1), (38, 1), (44, 1), (57, 1)] }, { coefficient := -1, powers := [(5, 1), (32, 1), (34, 1), (38, 1), (55, 1), (57, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1), (44, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (32, 1), (38, 1), (40, 1), (44, 1), (60, 1), (61, 1)] }, { coefficient := -1, powers := [(0, 1), (32, 1), (38, 1), (40, 1), (55, 1), (60, 1), (61, 1)] }, { coefficient := 1, powers := [(0, 1), (38, 1), (40, 1), (58, 1), (60, 1)] }, { coefficient := 1, powers := [(3, 1), (26, 1), (40, 1), (44, 1), (49, 1), (59, 1), (60, 1)] }, { coefficient := 1, powers := [(3, 1), (26, 1), (40, 1), (58, 1), (60, 1)] }, { coefficient := 1, powers := [(3, 1), (32, 1), (40, 1), (55, 1), (60, 1)] }, { coefficient := 1, powers := [(6, 1), (22, 1), (40, 1), (58, 1), (60, 1)] }, { coefficient := -1, powers := [(6, 1), (22, 1), (48, 1), (54, 1), (58, 1)] }, { coefficient := 1, powers := [(9, 1), (22, 1), (40, 1), (55, 1), (60, 1)] }, { coefficient := -1, powers := [(9, 1), (22, 1), (48, 1), (54, 1), (55, 1)] }, { coefficient := 1, powers := [(9, 1), (35, 1), (38, 1), (40, 1), (60, 1)] }, { coefficient := 1, powers := [(15, 1), (32, 1), (38, 1), (40, 1), (60, 1)] }, { coefficient := -1, powers := [(22, 1), (32, 1), (38, 1), (44, 1), (48, 1), (54, 1), (61, 1)] }, { coefficient := -1, powers := [(22, 1), (32, 1), (38, 1), (48, 1), (54, 1), (55, 1), (61, 1)] }, { coefficient := -1, powers := [(22, 1), (40, 1), (49, 1), (55, 1), (60, 1)] }, { coefficient := 1, powers := [(22, 1), (48, 1), (49, 1), (54, 1), (55, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1), (40, 1), (55, 1), (60, 1)] }, { coefficient := -1, powers := [(32, 1), (38, 1), (44, 1), (48, 1), (54, 1)] }, { coefficient := -1, powers := [(32, 1), (38, 1), (48, 1), (54, 1), (55, 1)] }, { coefficient := -1, powers := [(35, 1), (38, 1), (40, 1), (49, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (55, 1)] }, { coefficient := 1, powers := [(6, 1), (35, 1)] }, { coefficient := 1, powers := [(15, 1), (26, 1)] }, { coefficient := -1, powers := [(26, 1), (44, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (2, 1), (32, 1), (38, 1), (44, 1), (57, 1), (61, 1)] }, { coefficient := -1, powers := [(0, 1), (2, 1), (32, 1), (38, 1), (55, 1), (57, 1), (61, 1)] }, { coefficient := 1, powers := [(0, 1), (2, 1), (38, 1), (44, 1), (49, 1), (57, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (2, 1), (38, 1), (57, 1), (58, 1)] }, { coefficient := -1, powers := [(0, 1), (8, 1), (32, 1), (37, 1), (38, 1), (44, 1), (61, 1)] }, { coefficient := -1, powers := [(0, 1), (8, 1), (32, 1), (37, 1), (38, 1), (55, 1), (61, 1)] }, { coefficient := 1, powers := [(0, 1), (8, 1), (37, 1), (38, 1), (44, 1), (49, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (8, 1), (37, 1), (38, 1), (58, 1)] }, { coefficient := 1, powers := [(0, 1), (21, 1), (31, 1), (32, 1), (38, 1), (44, 1), (61, 1)] }, { coefficient := 1, powers := [(0, 1), (21, 1), (31, 1), (32, 1), (38, 1), (55, 1), (61, 1)] }, { coefficient := 1, powers := [(0, 1), (21, 1), (31, 1), (38, 1), (44, 1), (49, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (21, 1), (31, 1), (38, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (3, 1), (26, 1), (44, 1), (49, 1), (57, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (3, 1), (26, 1), (57, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (3, 1), (32, 1), (55, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (6, 1), (22, 1), (44, 1), (49, 1), (57, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (6, 1), (22, 1), (57, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (9, 1), (22, 1), (55, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (9, 1), (35, 1), (38, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (15, 1), (32, 1), (38, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (32, 1), (38, 1), (55, 1), (57, 1)] }, { coefficient := -1, powers := [(2, 1), (35, 1), (38, 1), (49, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (8, 1), (26, 1), (37, 1), (44, 1), (49, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (8, 1), (26, 1), (37, 1), (58, 1)] }, { coefficient := 1, powers := [(3, 1), (8, 1), (32, 1), (37, 1), (55, 1)] }, { coefficient := 1, powers := [(3, 1), (21, 1), (26, 1), (31, 1), (44, 1), (49, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (21, 1), (26, 1), (31, 1), (58, 1)] }, { coefficient := 1, powers := [(3, 1), (21, 1), (31, 1), (32, 1), (55, 1)] }, { coefficient := 1, powers := [(6, 1), (8, 1), (22, 1), (37, 1), (44, 1), (49, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (8, 1), (22, 1), (37, 1), (58, 1)] }, { coefficient := 1, powers := [(6, 1), (21, 1), (22, 1), (31, 1), (44, 1), (49, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (21, 1), (22, 1), (31, 1), (58, 1)] }, { coefficient := 1, powers := [(8, 1), (9, 1), (22, 1), (37, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (9, 1), (35, 1), (37, 1), (38, 1)] }, { coefficient := 1, powers := [(8, 1), (15, 1), (32, 1), (37, 1), (38, 1)] }, { coefficient := -1, powers := [(8, 1), (22, 1), (37, 1), (49, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (37, 1), (38, 1), (55, 1)] }, { coefficient := -1, powers := [(8, 1), (35, 1), (37, 1), (38, 1), (49, 1)] }, { coefficient := 1, powers := [(9, 1), (21, 1), (22, 1), (31, 1), (55, 1)] }, { coefficient := 1, powers := [(9, 1), (21, 1), (31, 1), (35, 1), (38, 1)] }, { coefficient := -1, powers := [(21, 1), (22, 1), (31, 1), (49, 1), (55, 1)] }, { coefficient := 1, powers := [(21, 1), (31, 1), (32, 1), (38, 1), (44, 1)] }, { coefficient := 1, powers := [(21, 1), (31, 1), (32, 1), (38, 1), (55, 1)] }, { coefficient := -1, powers := [(21, 1), (31, 1), (35, 1), (38, 1), (49, 1)] }]
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
    ¬ ∀ index : Fin 37,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component53.SelectedLeafB4_2.selectedHasNoCommonZero

end Krenn.Component53.SelectedLeafB4_2
