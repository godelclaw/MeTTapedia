import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component24.SelectedLeafB4_2_6_6

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "0ffacad5fa48ad71b6beac423c18878bc24278078ffebbda59827bc6865345cb"
def certificateSHA256 : String := "edfd1de127aab8aaef6c1a15df1e0155163969130f152c34d350782be9bae1a9"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 31 → Fin 676 := ![
  1,
  12,
  15,
  16,
  46,
  128,
  131,
  159,
  161,
  190,
  299,
  300,
  306,
  307,
  323,
  327,
  457,
  471,
  475,
  478,
  490,
  607,
  635,
  661,
  663,
  666,
  667,
  668,
  669,
  672,
  675
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 31 → SparsePoly (Fin 68) := ![
  [{ coefficient := 1, powers := [(8, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(15, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (35, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (55, 1)] }, { coefficient := 1, powers := [(20, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (35, 1)] }, { coefficient := 1, powers := [(18, 1), (21, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (55, 1)] }, { coefficient := 1, powers := [(31, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (45, 1)] }, { coefficient := 1, powers := [(29, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (35, 1), (52, 1)] }, { coefficient := 1, powers := [(5, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1)] }, { coefficient := 1, powers := [(20, 1), (45, 1)] }, { coefficient := 1, powers := [(26, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (49, 1)] }, { coefficient := 1, powers := [(21, 1), (45, 1)] }, { coefficient := 1, powers := [(26, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (59, 1)] }, { coefficient := 1, powers := [(9, 1), (56, 1)] }, { coefficient := 1, powers := [(15, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (61, 1)] }, { coefficient := 1, powers := [(14, 1), (58, 1)] }, { coefficient := 1, powers := [(19, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (58, 1)] }, { coefficient := 1, powers := [(31, 1), (49, 1)] }, { coefficient := 1, powers := [(37, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1), (55, 1)] }, { coefficient := 1, powers := [(3, 1), (35, 1), (55, 1)] }, { coefficient := 1, powers := [(15, 1), (20, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1)] }, { coefficient := 1, powers := [(14, 1), (31, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (55, 1)] }, { coefficient := 1, powers := [(31, 1), (43, 1)] }, { coefficient := 1, powers := [(31, 1), (48, 1), (51, 1)] }, { coefficient := 1, powers := [(34, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1), (53, 1)] }, { coefficient := 1, powers := [(3, 1), (35, 1), (53, 1)] }, { coefficient := 1, powers := [(15, 1), (20, 1), (53, 1)] }, { coefficient := 1, powers := [(44, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1), (54, 1)] }, { coefficient := 1, powers := [(3, 1), (61, 1)] }, { coefficient := 1, powers := [(20, 1), (45, 1), (54, 1)] }, { coefficient := 1, powers := [(45, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (49, 1), (54, 1)] }, { coefficient := 1, powers := [(21, 1), (45, 1), (54, 1)] }, { coefficient := 1, powers := [(43, 1), (45, 1)] }, { coefficient := 1, powers := [(49, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (50, 1)] }, { coefficient := 1, powers := [(6, 1), (32, 1)] }, { coefficient := 1, powers := [(9, 1), (26, 1)] }, { coefficient := 1, powers := [(20, 1), (50, 1)] }, { coefficient := 1, powers := [(26, 1), (41, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (31, 1), (61, 1)] }, { coefficient := 1, powers := [(3, 1), (34, 1), (58, 1)] }, { coefficient := 1, powers := [(3, 1), (37, 1), (55, 1)] }, { coefficient := 1, powers := [(24, 1), (45, 1), (55, 1)] }, { coefficient := 1, powers := [(24, 1), (51, 1), (58, 1)] }, { coefficient := 1, powers := [(31, 1), (45, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (38, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (41, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (44, 1), (50, 1)] }, { coefficient := 1, powers := [(3, 1), (26, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (32, 1), (56, 1)] }, { coefficient := 1, powers := [(3, 1), (35, 1), (50, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (32, 1), (44, 1)] }, { coefficient := 1, powers := [(6, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(9, 1), (20, 1), (56, 1)] }, { coefficient := 1, powers := [(9, 1), (26, 1), (44, 1)] }, { coefficient := 1, powers := [(9, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(15, 1), (20, 1), (50, 1)] }, { coefficient := 1, powers := [(15, 1), (26, 1), (41, 1)] }, { coefficient := 1, powers := [(15, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (40, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (43, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (49, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (37, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (25, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (49, 1)] }, { coefficient := 1, powers := [(8, 1), (37, 1), (43, 1)] }, { coefficient := 1, powers := [(14, 1), (25, 1), (58, 1)] }, { coefficient := 1, powers := [(14, 1), (31, 1), (49, 1)] }, { coefficient := 1, powers := [(14, 1), (37, 1), (40, 1)] }, { coefficient := 1, powers := [(19, 1), (25, 1), (55, 1)] }, { coefficient := 1, powers := [(19, 1), (31, 1), (43, 1)] }, { coefficient := 1, powers := [(19, 1), (34, 1), (40, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(41, 1)] }],
  [{ coefficient := 1, powers := [(42, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(43, 1)] }],
  [{ coefficient := 1, powers := [(58, 1)] }],
  [{ coefficient := 1, powers := [(31, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 31 → SparsePoly (Fin 68) := ![
  [{ coefficient := -1, powers := [(20, 1), (25, 1), (38, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (32, 1), (37, 1), (38, 1)] }, { coefficient := -1, powers := [(19, 1), (25, 1), (32, 1), (38, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (24, 1), (38, 1), (49, 1), (59, 1)] }, { coefficient := -1, powers := [(3, 1), (24, 1), (26, 1), (49, 1), (59, 1)] }, { coefficient := -1, powers := [(3, 1), (24, 1), (32, 1), (49, 1), (56, 1)] }, { coefficient := -1, powers := [(3, 1), (24, 1), (35, 1), (49, 1), (50, 1)] }, { coefficient := -1, powers := [(9, 1), (24, 1), (35, 1), (38, 1), (49, 1)] }, { coefficient := -1, powers := [(15, 1), (24, 1), (32, 1), (38, 1), (49, 1)] }, { coefficient := 1, powers := [(20, 1), (24, 1), (44, 1), (49, 1), (50, 1)] }, { coefficient := 1, powers := [(24, 1), (32, 1), (38, 1), (44, 1), (49, 1)] }],
  [{ coefficient := -1, powers := [(9, 1), (21, 1), (37, 1), (38, 1), (55, 1)] }, { coefficient := -1, powers := [(20, 1), (21, 1), (37, 1), (38, 1), (52, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (25, 1), (38, 1), (61, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (37, 1), (38, 1), (59, 1)] }, { coefficient := -1, powers := [(19, 1), (25, 1), (38, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (37, 1), (38, 1), (55, 1)] }, { coefficient := 1, powers := [(20, 1), (37, 1), (38, 1), (52, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (26, 1), (45, 1), (59, 1)] }, { coefficient := -1, powers := [(5, 1), (32, 1), (45, 1), (56, 1)] }, { coefficient := -1, powers := [(5, 1), (35, 1), (45, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (26, 2), (54, 1), (59, 1)] }, { coefficient := 1, powers := [(8, 1), (26, 1), (32, 1), (54, 1), (56, 1)] }, { coefficient := 1, powers := [(8, 1), (26, 1), (35, 1), (50, 1), (54, 1)] }, { coefficient := -1, powers := [(8, 1), (26, 1), (51, 1), (59, 1)] }, { coefficient := -1, powers := [(8, 1), (32, 1), (51, 1), (56, 1)] }, { coefficient := -1, powers := [(8, 1), (35, 1), (50, 1), (51, 1)] }],
  [{ coefficient := -1, powers := [(20, 1), (37, 1), (38, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (25, 1), (26, 1), (54, 1), (59, 1)] }, { coefficient := -1, powers := [(8, 1), (25, 1), (32, 1), (54, 1), (56, 1)] }, { coefficient := -1, powers := [(8, 1), (25, 1), (35, 1), (50, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (26, 1), (29, 1), (54, 1), (59, 1)] }, { coefficient := -1, powers := [(8, 1), (29, 1), (32, 1), (54, 1), (56, 1)] }, { coefficient := -1, powers := [(8, 1), (29, 1), (35, 1), (50, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(20, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (25, 1), (38, 1), (59, 1)] }, { coefficient := 1, powers := [(15, 1), (25, 1), (32, 1), (38, 1)] }, { coefficient := 1, powers := [(20, 1), (25, 1), (38, 1), (59, 1)] }, { coefficient := -1, powers := [(20, 1), (25, 1), (44, 1), (50, 1)] }, { coefficient := -1, powers := [(25, 1), (32, 1), (38, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (14, 1), (38, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (14, 1), (26, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (14, 1), (32, 1), (56, 1)] }, { coefficient := 1, powers := [(3, 1), (14, 1), (35, 1), (50, 1)] }, { coefficient := 1, powers := [(9, 1), (14, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(14, 1), (15, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [(14, 1), (20, 1), (44, 1), (50, 1)] }, { coefficient := -1, powers := [(14, 1), (32, 1), (38, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (20, 1), (37, 1), (50, 1), (53, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (37, 1), (38, 1), (53, 1)] }, { coefficient := -1, powers := [(19, 1), (20, 1), (25, 1), (50, 1), (53, 1)] }, { coefficient := -1, powers := [(19, 1), (25, 1), (32, 1), (38, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (38, 1), (49, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (26, 1), (49, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (32, 1), (49, 1), (56, 1)] }, { coefficient := 1, powers := [(3, 1), (35, 1), (49, 1), (50, 1)] }, { coefficient := 1, powers := [(9, 1), (35, 1), (38, 1), (49, 1)] }, { coefficient := 1, powers := [(15, 1), (32, 1), (38, 1), (49, 1)] }, { coefficient := -1, powers := [(20, 1), (44, 1), (49, 1), (50, 1)] }, { coefficient := -1, powers := [(32, 1), (38, 1), (44, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (19, 1), (38, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (19, 1), (26, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (19, 1), (32, 1), (56, 1)] }, { coefficient := 1, powers := [(3, 1), (19, 1), (35, 1), (50, 1)] }, { coefficient := 1, powers := [(9, 1), (19, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(15, 1), (19, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [(19, 1), (20, 1), (44, 1), (50, 1)] }, { coefficient := -1, powers := [(19, 1), (32, 1), (38, 1), (44, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (20, 1), (37, 1), (50, 1), (55, 1)] }, { coefficient := -1, powers := [(5, 1), (32, 1), (37, 1), (38, 1), (55, 1)] }, { coefficient := 1, powers := [(19, 1), (20, 1), (25, 1), (50, 1), (55, 1)] }, { coefficient := 1, powers := [(19, 1), (25, 1), (32, 1), (38, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (25, 1), (26, 1), (59, 1)] }, { coefficient := 1, powers := [(8, 1), (25, 1), (32, 1), (56, 1)] }, { coefficient := 1, powers := [(8, 1), (25, 1), (35, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (26, 1), (29, 1), (59, 1)] }, { coefficient := 1, powers := [(8, 1), (29, 1), (32, 1), (56, 1)] }, { coefficient := 1, powers := [(8, 1), (29, 1), (35, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(44, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (26, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (50, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(0, 1), (38, 1), (59, 1)] }, { coefficient := -1, powers := [(3, 1), (26, 1), (59, 1)] }, { coefficient := -1, powers := [(3, 1), (32, 1), (56, 1)] }, { coefficient := -1, powers := [(3, 1), (35, 1), (50, 1)] }, { coefficient := -1, powers := [(9, 1), (35, 1), (38, 1)] }, { coefficient := -1, powers := [(15, 1), (32, 1), (38, 1)] }, { coefficient := 1, powers := [(20, 1), (44, 1), (50, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (38, 1), (40, 1), (59, 1), (61, 1)] }, { coefficient := 1, powers := [(3, 1), (26, 1), (40, 1), (59, 1), (61, 1)] }, { coefficient := 1, powers := [(3, 1), (32, 1), (40, 1), (56, 1), (61, 1)] }, { coefficient := 1, powers := [(3, 1), (35, 1), (40, 1), (50, 1), (61, 1)] }, { coefficient := 1, powers := [(9, 1), (35, 1), (38, 1), (40, 1), (61, 1)] }, { coefficient := 1, powers := [(15, 1), (32, 1), (38, 1), (40, 1), (61, 1)] }, { coefficient := -1, powers := [(20, 1), (40, 1), (44, 1), (50, 1), (61, 1)] }, { coefficient := -1, powers := [(32, 1), (38, 1), (40, 1), (44, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (56, 1)] }, { coefficient := 1, powers := [(6, 1), (35, 1)] }, { coefficient := 1, powers := [(15, 1), (26, 1)] }, { coefficient := -1, powers := [(26, 1), (44, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (9, 1), (25, 1), (35, 1), (38, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (8, 1), (37, 1), (38, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (8, 1), (26, 1), (37, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (8, 1), (32, 1), (37, 1), (56, 1)] }, { coefficient := 1, powers := [(3, 1), (8, 1), (35, 1), (37, 1), (50, 1)] }, { coefficient := 1, powers := [(8, 1), (9, 1), (35, 1), (37, 1), (38, 1)] }, { coefficient := 1, powers := [(8, 1), (15, 1), (32, 1), (37, 1), (38, 1)] }, { coefficient := -1, powers := [(8, 1), (20, 1), (37, 1), (44, 1), (50, 1)] }, { coefficient := -1, powers := [(8, 1), (26, 1), (29, 1), (45, 1), (59, 1)] }, { coefficient := -1, powers := [(8, 1), (29, 1), (32, 1), (45, 1), (56, 1)] }, { coefficient := -1, powers := [(8, 1), (29, 1), (35, 1), (45, 1), (50, 1)] }, { coefficient := -1, powers := [(8, 1), (32, 1), (37, 1), (38, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (2, 1), (38, 1), (43, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (5, 1), (34, 1), (38, 1), (59, 1)] }, { coefficient := -1, powers := [(0, 1), (14, 1), (25, 1), (38, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (3, 1), (26, 1), (43, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (3, 1), (32, 1), (43, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (3, 1), (35, 1), (43, 1), (50, 1)] }, { coefficient := 1, powers := [(2, 1), (9, 1), (35, 1), (38, 1), (43, 1)] }, { coefficient := 1, powers := [(2, 1), (15, 1), (32, 1), (38, 1), (43, 1)] }, { coefficient := -1, powers := [(2, 1), (20, 1), (43, 1), (44, 1), (50, 1)] }, { coefficient := -1, powers := [(2, 1), (32, 1), (38, 1), (43, 1), (44, 1)] }, { coefficient := 1, powers := [(5, 1), (9, 1), (34, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(5, 1), (15, 1), (32, 1), (34, 1), (38, 1)] }, { coefficient := -1, powers := [(5, 1), (20, 1), (34, 1), (44, 1), (50, 1)] }, { coefficient := -1, powers := [(5, 1), (24, 1), (26, 1), (51, 1), (59, 1)] }, { coefficient := -1, powers := [(5, 1), (24, 1), (32, 1), (51, 1), (56, 1)] }, { coefficient := -1, powers := [(5, 1), (24, 1), (35, 1), (50, 1), (51, 1)] }, { coefficient := -1, powers := [(5, 1), (32, 1), (34, 1), (38, 1), (44, 1)] }, { coefficient := -1, powers := [(14, 1), (15, 1), (25, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [(14, 1), (20, 1), (25, 1), (38, 1), (59, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1), (25, 1), (44, 1), (50, 1)] }, { coefficient := 1, powers := [(14, 1), (25, 1), (32, 1), (38, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (5, 1), (38, 1), (59, 1), (61, 1)] }, { coefficient := -1, powers := [(0, 1), (14, 1), (38, 1), (49, 1), (59, 1)] }, { coefficient := -1, powers := [(0, 1), (19, 1), (38, 1), (48, 1), (51, 1), (59, 1)] }, { coefficient := -1, powers := [(3, 1), (14, 1), (26, 1), (49, 1), (59, 1)] }, { coefficient := -1, powers := [(3, 1), (14, 1), (32, 1), (49, 1), (56, 1)] }, { coefficient := -1, powers := [(3, 1), (14, 1), (35, 1), (49, 1), (50, 1)] }, { coefficient := -1, powers := [(3, 1), (19, 1), (26, 1), (48, 1), (51, 1), (59, 1)] }, { coefficient := -1, powers := [(3, 1), (19, 1), (32, 1), (48, 1), (51, 1), (56, 1)] }, { coefficient := -1, powers := [(3, 1), (19, 1), (35, 1), (48, 1), (50, 1), (51, 1)] }, { coefficient := 1, powers := [(5, 1), (9, 1), (35, 1), (38, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (15, 1), (32, 1), (38, 1), (61, 1)] }, { coefficient := -1, powers := [(5, 1), (20, 1), (44, 1), (50, 1), (61, 1)] }, { coefficient := -1, powers := [(5, 1), (32, 1), (38, 1), (44, 1), (61, 1)] }, { coefficient := -1, powers := [(9, 1), (14, 1), (35, 1), (38, 1), (49, 1)] }, { coefficient := -1, powers := [(9, 1), (19, 1), (35, 1), (38, 1), (48, 1), (51, 1)] }, { coefficient := -1, powers := [(14, 1), (15, 1), (32, 1), (38, 1), (49, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1), (44, 1), (49, 1), (50, 1)] }, { coefficient := 1, powers := [(14, 1), (32, 1), (38, 1), (44, 1), (49, 1)] }, { coefficient := -1, powers := [(15, 1), (19, 1), (32, 1), (38, 1), (48, 1), (51, 1)] }, { coefficient := 1, powers := [(19, 1), (20, 1), (44, 1), (48, 1), (50, 1), (51, 1)] }, { coefficient := 1, powers := [(19, 1), (32, 1), (38, 1), (44, 1), (48, 1), (51, 1)] }]
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
    (values : Fin 68 → R) :
    ¬ ∀ index : Fin 31,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component24.SelectedLeafB4_2_6_6.selectedHasNoCommonZero

end Krenn.Component24.SelectedLeafB4_2_6_6
