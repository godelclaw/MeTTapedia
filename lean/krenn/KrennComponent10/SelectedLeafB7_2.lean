import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component10.SelectedLeafB7_2

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "19ece35511dc47de6264e23e8f60f5498a0e1705fce2f3c052b5901d476788c1"
def certificateSHA256 : String := "d4490ee38d08e8ddfcb1374745b795ddd6af2858493b058f6461676193d6db3a"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 68 → Fin 641 := ![
  0,
  2,
  6,
  8,
  10,
  11,
  14,
  15,
  19,
  21,
  28,
  35,
  162,
  163,
  164,
  165,
  167,
  172,
  180,
  181,
  184,
  185,
  186,
  189,
  190,
  197,
  202,
  231,
  284,
  311,
  322,
  343,
  344,
  346,
  349,
  350,
  356,
  358,
  359,
  360,
  363,
  368,
  369,
  409,
  445,
  446,
  456,
  460,
  463,
  464,
  466,
  471,
  473,
  490,
  499,
  550,
  552,
  556,
  557,
  568,
  582,
  620,
  627,
  634,
  635,
  636,
  637,
  640
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 68 → SparsePoly (Fin 64) := ![
  [{ coefficient := 1, powers := [(3, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(15, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(15, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(28, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (48, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (48, 1)] }, { coefficient := 1, powers := [(24, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (52, 1)] }, { coefficient := 1, powers := [(19, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (53, 1)] }, { coefficient := 1, powers := [(19, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (53, 1)] }, { coefficient := 1, powers := [(15, 1), (20, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (58, 1)] }, { coefficient := 1, powers := [(17, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (24, 1)] }, { coefficient := 1, powers := [(15, 1), (19, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (45, 1)] }, { coefficient := 1, powers := [(12, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (47, 1)] }, { coefficient := 1, powers := [(17, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (19, 1)] }, { coefficient := 1, powers := [(17, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (43, 1)] }, { coefficient := 1, powers := [(18, 1), (19, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (56, 1)] }, { coefficient := 1, powers := [(18, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (43, 1)] }, { coefficient := 1, powers := [(27, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (52, 1)] }, { coefficient := 1, powers := [(29, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1), (53, 1)] }, { coefficient := 1, powers := [(53, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (48, 1), (51, 1)] }, { coefficient := 1, powers := [(48, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (32, 1), (47, 1)] }, { coefficient := 1, powers := [(27, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (19, 1), (55, 1)] }, { coefficient := 1, powers := [(12, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (25, 1), (48, 1)] }, { coefficient := 1, powers := [(18, 1), (20, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (43, 1), (51, 1)] }, { coefficient := 1, powers := [(28, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1)] }, { coefficient := 1, powers := [(19, 1), (43, 1)] }, { coefficient := 1, powers := [(24, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (47, 1)] }, { coefficient := 1, powers := [(11, 1), (25, 1), (47, 1)] }, { coefficient := 1, powers := [(15, 1), (20, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (52, 1)] }, { coefficient := 1, powers := [(11, 1), (25, 1), (52, 1)] }, { coefficient := 1, powers := [(15, 1), (20, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (59, 1)] }, { coefficient := 1, powers := [(12, 1), (48, 1)] }, { coefficient := 1, powers := [(18, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (59, 1)] }, { coefficient := 1, powers := [(12, 1), (56, 1)] }, { coefficient := 1, powers := [(18, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (46, 1)] }, { coefficient := 1, powers := [(18, 1), (40, 1)] }, { coefficient := 1, powers := [(18, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (51, 1)] }, { coefficient := 1, powers := [(23, 1), (55, 1)] }, { coefficient := 1, powers := [(28, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (53, 1)] }, { coefficient := 1, powers := [(29, 1), (41, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(28, 1), (52, 1)] }, { coefficient := 1, powers := [(29, 1), (40, 1)] }, { coefficient := 1, powers := [(29, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (38, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (41, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (48, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1), (51, 1)] }, { coefficient := 1, powers := [(19, 1), (43, 1), (51, 1)] }, { coefficient := 1, powers := [(43, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1), (52, 1)] }, { coefficient := 1, powers := [(19, 1), (43, 1), (52, 1)] }, { coefficient := 1, powers := [(19, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (23, 1), (58, 1)] }, { coefficient := 1, powers := [(23, 1)] }, { coefficient := 1, powers := [(27, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (24, 1), (40, 1)] }, { coefficient := 1, powers := [(17, 1), (24, 1), (45, 1)] }, { coefficient := 1, powers := [(17, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (24, 1), (46, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (40, 1)] }, { coefficient := 1, powers := [(18, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1)] }, { coefficient := 1, powers := [(24, 1), (40, 1), (43, 1)] }, { coefficient := 1, powers := [(24, 1), (46, 1)] }, { coefficient := 1, powers := [(43, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (45, 1)] }, { coefficient := 1, powers := [(17, 1), (27, 1), (40, 1)] }, { coefficient := 1, powers := [(17, 1), (27, 1), (45, 1)] }, { coefficient := 1, powers := [(17, 1), (28, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (48, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1)] }, { coefficient := 1, powers := [(17, 1), (27, 1), (48, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (51, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (51, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (55, 1)] }, { coefficient := 1, powers := [(17, 1), (28, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (53, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1)] }, { coefficient := 1, powers := [(12, 1), (29, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (40, 1)] }, { coefficient := 1, powers := [(17, 1), (45, 1)] }, { coefficient := 1, powers := [(17, 1), (51, 1)] }, { coefficient := 1, powers := [(17, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (40, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(43, 1), (52, 1)] }, { coefficient := 1, powers := [(56, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (36, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1)] }, { coefficient := 1, powers := [(17, 1), (27, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (27, 1), (58, 1)] }, { coefficient := 1, powers := [(6, 1), (22, 1), (58, 1)] }, { coefficient := 1, powers := [(22, 1)] }, { coefficient := 1, powers := [(27, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (43, 1), (52, 1)] }, { coefficient := 1, powers := [(23, 1), (56, 1)] }, { coefficient := 1, powers := [(29, 1), (48, 1)] }, { coefficient := 1, powers := [(35, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(28, 1), (43, 1), (52, 1)] }, { coefficient := 1, powers := [(28, 1), (56, 1)] }, { coefficient := 1, powers := [(29, 1), (40, 1), (43, 1)] }, { coefficient := 1, powers := [(29, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1)] }, { coefficient := 1, powers := [(6, 1), (58, 1)] }, { coefficient := 1, powers := [(24, 1), (40, 1)] }, { coefficient := 1, powers := [(24, 1), (45, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (51, 1)] }, { coefficient := 1, powers := [(3, 1), (58, 1)] }, { coefficient := 1, powers := [(19, 1), (51, 1)] }, { coefficient := 1, powers := [(19, 1), (55, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (41, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (55, 1)] }, { coefficient := 1, powers := [(12, 1), (23, 1), (55, 1)] }, { coefficient := 1, powers := [(12, 1), (28, 1), (47, 1)] }, { coefficient := 1, powers := [(17, 1), (28, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (36, 1), (58, 1)] }, { coefficient := 1, powers := [(0, 1)] }, { coefficient := 1, powers := [(3, 1), (24, 1), (58, 1)] }, { coefficient := 1, powers := [(6, 1), (19, 1), (58, 1)] }, { coefficient := 1, powers := [(19, 1)] }, { coefficient := 1, powers := [(24, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (37, 1), (58, 1)] }, { coefficient := 1, powers := [(0, 1), (40, 1), (55, 1)] }, { coefficient := 1, powers := [(0, 1), (45, 1), (51, 1)] }, { coefficient := 1, powers := [(40, 1)] }, { coefficient := 1, powers := [(45, 1)] }, { coefficient := 1, powers := [(51, 1)] }, { coefficient := 1, powers := [(55, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (37, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (40, 1), (55, 1)] }, { coefficient := 1, powers := [(2, 1), (45, 1), (51, 1)] }, { coefficient := 1, powers := [(17, 1), (28, 1), (40, 1)] }, { coefficient := 1, powers := [(17, 1), (28, 1), (45, 1)] }, { coefficient := 1, powers := [(17, 1), (28, 1), (51, 1)] }, { coefficient := 1, powers := [(17, 1), (28, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (41, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (48, 1), (53, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (53, 1)] }, { coefficient := 1, powers := [(8, 1), (23, 1), (59, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (48, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(12, 1), (23, 1), (56, 1)] }, { coefficient := 1, powers := [(12, 1), (29, 1), (48, 1)] }, { coefficient := 1, powers := [(12, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (53, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (41, 1)] }, { coefficient := 1, powers := [(18, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (60, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1), (61, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(41, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 68 → SparsePoly (Fin 64) := ![
  [{ coefficient := -1, powers := [(17, 1), (27, 1), (38, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(17, 1), (22, 1), (38, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (18, 1), (25, 1), (32, 1), (52, 1), (61, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (29, 1), (40, 1), (48, 1), (60, 1)] }, { coefficient := -2, powers := [(19, 1), (29, 1), (48, 1), (51, 1), (60, 1)] }, { coefficient := 2, powers := [(23, 1), (40, 1), (56, 1)] }, { coefficient := 2, powers := [(23, 1), (45, 1), (56, 1)] }, { coefficient := 2, powers := [(24, 1), (29, 1), (40, 1), (48, 1), (60, 1)] }, { coefficient := 1, powers := [(29, 1), (40, 1), (48, 1)] }, { coefficient := 1, powers := [(29, 1), (45, 1), (48, 1)] }, { coefficient := 2, powers := [(29, 1), (48, 1), (51, 1)] }, { coefficient := 6, powers := [(29, 1), (48, 1), (60, 1)] }, { coefficient := 1, powers := [(35, 1), (38, 1), (40, 1)] }, { coefficient := 1, powers := [(35, 1), (38, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (23, 1), (52, 1)] }, { coefficient := -1, powers := [(19, 1), (23, 1), (52, 1)] }, { coefficient := 1, powers := [(23, 1), (24, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (19, 1), (25, 1), (32, 1), (46, 1), (61, 1)] }, { coefficient := -1, powers := [(5, 1), (20, 1), (24, 1), (32, 1), (46, 1), (61, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (2, 1), (20, 1), (40, 1), (48, 1), (61, 1)] }, { coefficient := -1, powers := [(0, 1), (2, 1), (20, 1), (45, 1), (48, 1), (61, 1)] }, { coefficient := -1, powers := [(0, 1), (2, 1), (20, 1), (48, 1), (51, 1), (61, 1)] }, { coefficient := -2, powers := [(0, 1), (18, 1), (20, 1), (23, 1), (51, 1), (61, 1)] }, { coefficient := -2, powers := [(2, 1), (19, 1), (20, 1), (48, 1), (51, 1), (61, 1)] }, { coefficient := -2, powers := [(2, 1), (20, 1), (24, 1), (40, 1), (48, 1), (61, 1)] }, { coefficient := -1, powers := [(2, 1), (20, 1), (24, 1), (45, 1), (48, 1), (61, 1)] }, { coefficient := -3, powers := [(2, 1), (20, 1), (24, 1), (48, 1), (51, 1), (61, 1)] }, { coefficient := 5, powers := [(2, 1), (20, 1), (48, 1), (61, 1)] }, { coefficient := -4, powers := [(18, 1), (19, 1), (20, 1), (23, 1), (51, 1), (61, 1)] }, { coefficient := 2, powers := [(18, 1), (20, 1), (23, 1), (24, 1), (45, 1), (61, 1)] }, { coefficient := -2, powers := [(18, 1), (20, 1), (23, 1), (24, 1), (51, 1), (61, 1)] }, { coefficient := 2, powers := [(18, 1), (20, 1), (23, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (22, 1), (40, 1), (53, 1)] }, { coefficient := 1, powers := [(0, 1), (22, 1), (45, 1), (53, 1)] }, { coefficient := -2, powers := [(0, 1), (27, 1), (40, 1), (53, 1)] }, { coefficient := -2, powers := [(0, 1), (27, 1), (45, 1), (53, 1)] }, { coefficient := -1, powers := [(0, 1), (27, 1), (51, 1), (53, 1)] }, { coefficient := -1, powers := [(0, 1), (27, 1), (53, 1), (55, 1)] }, { coefficient := -2, powers := [(0, 1), (28, 1), (53, 1)] }, { coefficient := -1, powers := [(3, 1), (15, 1), (25, 1), (32, 1), (52, 1), (61, 1)] }, { coefficient := 1, powers := [(19, 1), (27, 1), (51, 1), (53, 1)] }, { coefficient := 1, powers := [(22, 1), (24, 1), (40, 1), (53, 1)] }, { coefficient := 1, powers := [(22, 1), (24, 1), (45, 1), (53, 1)] }, { coefficient := -2, powers := [(24, 1), (27, 1), (40, 1), (53, 1)] }, { coefficient := -2, powers := [(24, 1), (27, 1), (45, 1), (53, 1)] }, { coefficient := -1, powers := [(24, 1), (27, 1), (53, 1), (55, 1)] }, { coefficient := -2, powers := [(24, 1), (28, 1), (53, 1)] }, { coefficient := -3, powers := [(27, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (22, 1), (40, 1), (48, 1)] }, { coefficient := -1, powers := [(0, 1), (22, 1), (45, 1), (48, 1)] }, { coefficient := -1, powers := [(0, 1), (22, 1), (48, 1), (51, 1)] }, { coefficient := -1, powers := [(0, 1), (22, 1), (48, 1), (55, 1)] }, { coefficient := 1, powers := [(19, 1), (22, 1), (48, 1), (51, 1)] }, { coefficient := -2, powers := [(19, 1), (23, 1), (46, 1)] }, { coefficient := -1, powers := [(22, 1), (24, 1), (40, 1), (48, 1)] }, { coefficient := -1, powers := [(22, 1), (24, 1), (45, 1), (48, 1)] }, { coefficient := -1, powers := [(22, 1), (24, 1), (48, 1), (55, 1)] }, { coefficient := -3, powers := [(22, 1), (48, 1)] }, { coefficient := 2, powers := [(23, 1), (24, 1), (46, 1)] }, { coefficient := 2, powers := [(23, 1), (43, 1)] }, { coefficient := -1, powers := [(24, 1), (28, 1), (48, 1)] }, { coefficient := 1, powers := [(27, 1), (48, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (18, 1), (47, 1)] }, { coefficient := 2, powers := [(18, 1), (24, 1), (47, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (12, 1), (28, 1), (60, 1)] }, { coefficient := 1, powers := [(12, 1), (19, 1), (28, 1), (60, 1)] }, { coefficient := -2, powers := [(12, 1), (24, 1), (28, 1), (60, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (12, 1), (29, 1), (40, 1), (60, 1)] }, { coefficient := -2, powers := [(2, 1), (40, 1), (53, 1)] }, { coefficient := -2, powers := [(2, 1), (45, 1), (53, 1)] }, { coefficient := -2, powers := [(2, 1), (51, 1), (53, 1)] }, { coefficient := 2, powers := [(12, 1), (19, 1), (29, 1), (51, 1), (60, 1)] }, { coefficient := -2, powers := [(12, 1), (24, 1), (29, 1), (40, 1), (60, 1)] }, { coefficient := 2, powers := [(12, 1), (27, 1), (51, 1), (52, 1)] }, { coefficient := -2, powers := [(12, 1), (29, 1), (40, 1)] }, { coefficient := -2, powers := [(12, 1), (29, 1), (45, 1)] }, { coefficient := -2, powers := [(12, 1), (29, 1), (51, 1)] }, { coefficient := -6, powers := [(12, 1), (29, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (12, 1), (23, 1), (40, 1), (43, 1), (51, 1)] }, { coefficient := -1, powers := [(0, 1), (12, 1), (23, 1), (43, 1), (45, 1), (51, 1)] }, { coefficient := -1, powers := [(5, 1), (32, 1), (40, 1), (43, 1)] }, { coefficient := 2, powers := [(5, 1), (32, 1), (43, 1), (51, 1)] }, { coefficient := -2, powers := [(12, 1), (23, 1), (24, 1), (43, 1), (45, 1), (51, 1)] }, { coefficient := 4, powers := [(12, 1), (23, 1), (43, 1), (45, 1)] }, { coefficient := 1, powers := [(12, 1), (23, 1), (43, 1), (51, 1)] }, { coefficient := 1, powers := [(12, 1), (23, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (48, 1), (51, 1)] }, { coefficient := -2, powers := [(18, 1), (23, 1), (40, 1)] }, { coefficient := -2, powers := [(18, 1), (23, 1), (51, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (2, 1), (40, 1), (48, 1), (61, 1)] }, { coefficient := 1, powers := [(0, 1), (2, 1), (45, 1), (48, 1), (61, 1)] }, { coefficient := 1, powers := [(0, 1), (2, 1), (48, 1), (51, 1), (61, 1)] }, { coefficient := 2, powers := [(0, 1), (18, 1), (23, 1), (51, 1), (61, 1)] }, { coefficient := 2, powers := [(2, 1), (19, 1), (48, 1), (51, 1), (61, 1)] }, { coefficient := 2, powers := [(2, 1), (24, 1), (40, 1), (48, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (24, 1), (45, 1), (48, 1), (61, 1)] }, { coefficient := 3, powers := [(2, 1), (24, 1), (48, 1), (51, 1), (61, 1)] }, { coefficient := -5, powers := [(2, 1), (48, 1), (61, 1)] }, { coefficient := 4, powers := [(18, 1), (19, 1), (23, 1), (51, 1), (61, 1)] }, { coefficient := -2, powers := [(18, 1), (23, 1), (24, 1), (45, 1), (61, 1)] }, { coefficient := 2, powers := [(18, 1), (23, 1), (24, 1), (51, 1), (61, 1)] }, { coefficient := -2, powers := [(18, 1), (23, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (32, 1), (56, 1)] }, { coefficient := -1, powers := [(6, 1), (32, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (25, 1), (32, 1), (46, 1), (52, 1), (61, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (19, 1), (23, 1), (51, 1), (56, 1)] }, { coefficient := 2, powers := [(0, 1), (23, 1), (56, 1)] }, { coefficient := -1, powers := [(0, 1), (29, 1), (48, 1)] }, { coefficient := 1, powers := [(0, 1), (35, 1), (38, 1)] }, { coefficient := -2, powers := [(19, 1), (23, 1), (24, 1), (51, 1), (56, 1)] }, { coefficient := 4, powers := [(19, 1), (23, 1), (56, 1)] }, { coefficient := 1, powers := [(23, 1), (24, 1), (56, 1)] }, { coefficient := -1, powers := [(24, 1), (29, 1), (48, 1)] }, { coefficient := 1, powers := [(24, 1), (35, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (28, 1), (56, 1)] }, { coefficient := 2, powers := [(19, 1), (28, 1), (56, 1)] }, { coefficient := -2, powers := [(27, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (38, 1), (40, 1), (59, 1)] }, { coefficient := 1, powers := [(22, 1), (38, 1), (45, 1), (59, 1)] }, { coefficient := 1, powers := [(22, 1), (40, 1), (62, 1)] }, { coefficient := 1, powers := [(22, 1), (45, 1), (62, 1)] }, { coefficient := 1, powers := [(27, 1), (40, 1), (62, 1)] }, { coefficient := 1, powers := [(27, 1), (45, 1), (62, 1)] }, { coefficient := -1, powers := [(28, 1), (38, 1), (59, 1)] }],
  [{ coefficient := -2, powers := [(23, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (32, 1), (47, 1)] }, { coefficient := 1, powers := [(6, 1), (32, 1), (47, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (12, 1), (51, 1), (52, 1)] }, { coefficient := -2, powers := [(12, 1), (24, 1), (51, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (12, 1), (43, 1), (45, 1)] }, { coefficient := -1, powers := [(0, 1), (12, 1), (46, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (43, 1), (45, 1)] }, { coefficient := -1, powers := [(12, 1), (24, 1), (46, 1)] }],
  [{ coefficient := -2, powers := [(18, 1), (23, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(18, 1), (52, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (23, 1), (51, 1), (56, 1)] }, { coefficient := 2, powers := [(23, 1), (24, 1), (51, 1), (56, 1)] }, { coefficient := -2, powers := [(23, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (15, 1), (32, 1), (52, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (12, 1), (52, 1)] }, { coefficient := -1, powers := [(12, 1), (19, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (32, 1), (40, 1), (52, 1)] }, { coefficient := 2, powers := [(12, 1), (23, 1), (51, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (18, 1), (32, 1), (52, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (24, 1), (32, 1), (46, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (29, 1), (40, 1)] }, { coefficient := 1, powers := [(0, 1), (29, 1), (45, 1)] }, { coefficient := 1, powers := [(0, 1), (29, 1), (51, 1)] }, { coefficient := 1, powers := [(0, 1), (29, 1), (55, 1)] }, { coefficient := -1, powers := [(19, 1), (29, 1), (51, 1)] }, { coefficient := 1, powers := [(24, 1), (29, 1), (40, 1)] }, { coefficient := 1, powers := [(24, 1), (29, 1), (45, 1)] }, { coefficient := 1, powers := [(24, 1), (29, 1), (55, 1)] }, { coefficient := 3, powers := [(29, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (23, 1), (40, 1)] }, { coefficient := 1, powers := [(0, 1), (23, 1), (45, 1)] }, { coefficient := 1, powers := [(0, 1), (23, 1), (51, 1)] }, { coefficient := 1, powers := [(0, 1), (23, 1), (55, 1)] }, { coefficient := -1, powers := [(19, 1), (23, 1), (51, 1)] }, { coefficient := 1, powers := [(23, 1), (24, 1), (40, 1)] }, { coefficient := 1, powers := [(23, 1), (24, 1), (45, 1)] }, { coefficient := 1, powers := [(23, 1), (24, 1), (55, 1)] }, { coefficient := 3, powers := [(23, 1)] }],
  [{ coefficient := 2, powers := [(19, 1), (23, 1), (53, 1)] }],
  [{ coefficient := -3, powers := [(0, 1), (12, 1), (56, 1)] }, { coefficient := -2, powers := [(0, 1), (18, 1), (53, 1)] }, { coefficient := -1, powers := [(12, 1), (19, 1), (56, 1)] }, { coefficient := -2, powers := [(12, 1), (24, 1), (56, 1)] }, { coefficient := -2, powers := [(18, 1), (24, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (18, 1), (40, 1)] }, { coefficient := 1, powers := [(0, 1), (18, 1), (45, 1)] }, { coefficient := 1, powers := [(0, 1), (18, 1), (51, 1)] }, { coefficient := 1, powers := [(0, 1), (18, 1), (55, 1)] }, { coefficient := -1, powers := [(18, 1), (19, 1), (51, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (40, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (45, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (55, 1)] }, { coefficient := 3, powers := [(18, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (12, 1), (43, 1), (47, 1)] }, { coefficient := 2, powers := [(0, 1), (12, 1), (48, 1)] }, { coefficient := -1, powers := [(12, 1), (24, 1), (43, 1), (47, 1)] }, { coefficient := 2, powers := [(12, 1), (24, 1), (48, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (2, 1), (40, 1), (60, 1)] }, { coefficient := -1, powers := [(0, 1), (2, 1), (45, 1), (60, 1)] }, { coefficient := -1, powers := [(0, 1), (2, 1), (51, 1), (60, 1)] }, { coefficient := -2, powers := [(2, 1), (19, 1), (51, 1), (60, 1)] }, { coefficient := -1, powers := [(2, 1), (24, 1), (45, 1), (60, 1)] }, { coefficient := -1, powers := [(2, 1), (24, 1), (51, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (40, 1)] }, { coefficient := 1, powers := [(2, 1), (45, 1)] }, { coefficient := 1, powers := [(2, 1), (51, 1)] }, { coefficient := 3, powers := [(2, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (12, 1), (23, 1), (40, 1), (52, 1)] }, { coefficient := -1, powers := [(0, 1), (12, 1), (23, 1), (45, 1), (52, 1)] }, { coefficient := -3, powers := [(12, 1), (23, 1), (52, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (12, 1), (23, 1), (45, 1), (51, 1)] }, { coefficient := -2, powers := [(5, 1), (32, 1), (51, 1)] }, { coefficient := 2, powers := [(12, 1), (23, 1), (24, 1), (45, 1), (51, 1)] }, { coefficient := -4, powers := [(12, 1), (23, 1), (45, 1)] }, { coefficient := 2, powers := [(12, 1), (23, 1), (51, 1)] }],
  [{ coefficient := 2, powers := [(12, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [(22, 1), (38, 1), (59, 1)] }, { coefficient := -1, powers := [(22, 1), (62, 1)] }, { coefficient := -1, powers := [(27, 1), (38, 1), (59, 1)] }, { coefficient := -1, powers := [(27, 1), (48, 1), (53, 1)] }, { coefficient := -1, powers := [(27, 1), (62, 1)] }],
  [{ coefficient := -2, powers := [(23, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (32, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (48, 1), (53, 1)] }, { coefficient := -1, powers := [(19, 1), (62, 1)] }, { coefficient := 1, powers := [(24, 1), (38, 1), (59, 1)] }, { coefficient := 2, powers := [(24, 1), (48, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (40, 1), (53, 1)] }, { coefficient := 1, powers := [(0, 1), (45, 1), (53, 1)] }, { coefficient := 1, powers := [(0, 1), (51, 1), (53, 1)] }, { coefficient := 1, powers := [(0, 1), (53, 1), (55, 1)] }, { coefficient := -1, powers := [(19, 1), (51, 1), (53, 1)] }, { coefficient := 1, powers := [(24, 1), (40, 1), (53, 1)] }, { coefficient := 1, powers := [(24, 1), (45, 1), (53, 1)] }, { coefficient := 1, powers := [(24, 1), (53, 1), (55, 1)] }, { coefficient := 3, powers := [(53, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (48, 1), (53, 1)] }, { coefficient := 1, powers := [(19, 1), (38, 1), (59, 1)] }, { coefficient := 1, powers := [(19, 1), (62, 1)] }, { coefficient := 1, powers := [(24, 1), (48, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (40, 1), (48, 1)] }, { coefficient := 1, powers := [(0, 1), (45, 1), (48, 1)] }, { coefficient := 1, powers := [(0, 1), (48, 1), (51, 1)] }, { coefficient := 1, powers := [(0, 1), (48, 1), (55, 1)] }, { coefficient := -1, powers := [(19, 1), (48, 1), (51, 1)] }, { coefficient := 1, powers := [(24, 1), (40, 1), (48, 1)] }, { coefficient := 1, powers := [(24, 1), (45, 1), (48, 1)] }, { coefficient := 1, powers := [(24, 1), (48, 1), (55, 1)] }, { coefficient := 3, powers := [(48, 1)] }],
  [{ coefficient := 1, powers := [(0, 2), (28, 1), (38, 1), (59, 1)] }, { coefficient := -1, powers := [(0, 2), (28, 1), (48, 1), (53, 1)] }, { coefficient := -1, powers := [(0, 2), (28, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 1), (22, 1), (48, 1), (53, 1)] }, { coefficient := 1, powers := [(0, 1), (24, 1), (28, 1), (38, 1), (59, 1)] }, { coefficient := -1, powers := [(0, 1), (24, 1), (28, 1), (48, 1), (53, 1)] }, { coefficient := -1, powers := [(0, 1), (24, 1), (28, 1), (62, 1)] }, { coefficient := -1, powers := [(19, 1), (22, 1), (38, 1), (59, 1)] }, { coefficient := -1, powers := [(19, 1), (22, 1), (62, 1)] }, { coefficient := -1, powers := [(19, 1), (24, 1), (28, 1), (62, 1)] }, { coefficient := -1, powers := [(22, 1), (24, 1), (48, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (32, 1)] }, { coefficient := -1, powers := [(12, 1), (23, 1)] }],
  [{ coefficient := 1, powers := [(62, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (38, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (12, 1), (40, 1)] }, { coefficient := 1, powers := [(0, 1), (12, 1), (51, 1)] }, { coefficient := -1, powers := [(12, 1), (19, 1), (51, 1)] }, { coefficient := -1, powers := [(12, 1), (24, 1), (45, 1)] }, { coefficient := 3, powers := [(12, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (12, 1), (47, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (32, 1), (56, 1)] }, { coefficient := -2, powers := [(12, 1), (23, 1), (56, 1)] }, { coefficient := 1, powers := [(19, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (32, 1), (56, 1)] }, { coefficient := 1, powers := [(24, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (56, 1)] }, { coefficient := -1, powers := [(19, 1), (56, 1)] }, { coefficient := 1, powers := [(24, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [(60, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (2, 1), (38, 1), (59, 1)] }, { coefficient := -1, powers := [(0, 1), (2, 1), (48, 1), (53, 1)] }, { coefficient := -1, powers := [(0, 1)] }, { coefficient := 1, powers := [(2, 1), (24, 1), (38, 1), (59, 1)] }, { coefficient := -1, powers := [(2, 1), (24, 1), (48, 1), (53, 1)] }, { coefficient := -1, powers := [(19, 1), (24, 1), (60, 1)] }, { coefficient := -1, powers := [(24, 1)] }],
  [{ coefficient := -1, powers := [(0, 2), (38, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 2), (48, 1), (53, 1)] }, { coefficient := 1, powers := [(0, 2), (62, 1)] }, { coefficient := -1, powers := [(0, 1), (24, 1), (38, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (24, 1), (48, 1), (53, 1)] }, { coefficient := 1, powers := [(0, 1), (24, 1), (62, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (40, 1)] }, { coefficient := -1, powers := [(0, 1), (45, 1)] }, { coefficient := -1, powers := [(0, 1), (51, 1)] }, { coefficient := -1, powers := [(0, 1), (55, 1)] }, { coefficient := 1, powers := [(19, 1), (51, 1)] }, { coefficient := -1, powers := [(24, 1), (40, 1)] }, { coefficient := -1, powers := [(24, 1), (45, 1)] }, { coefficient := -1, powers := [(24, 1), (55, 1)] }, { coefficient := -3, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (2, 1), (38, 1), (40, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (2, 1), (38, 1), (45, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (2, 1), (38, 1), (51, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (2, 1), (40, 1), (48, 1), (53, 1)] }, { coefficient := 1, powers := [(0, 1), (2, 1), (45, 1), (48, 1), (53, 1)] }, { coefficient := 1, powers := [(0, 1), (2, 1), (48, 1), (51, 1), (53, 1)] }, { coefficient := 1, powers := [(0, 1), (12, 1), (28, 1), (48, 1), (52, 1)] }, { coefficient := 2, powers := [(0, 1), (12, 1), (29, 1), (40, 1), (48, 1)] }, { coefficient := 2, powers := [(2, 1), (19, 1), (38, 1), (51, 1), (59, 1)] }, { coefficient := 2, powers := [(2, 1), (19, 1), (48, 1), (51, 1), (53, 1)] }, { coefficient := 1, powers := [(2, 1), (24, 1), (38, 1), (45, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (24, 1), (38, 1), (51, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (24, 1), (45, 1), (48, 1), (53, 1)] }, { coefficient := 1, powers := [(2, 1), (24, 1), (48, 1), (51, 1), (53, 1)] }, { coefficient := -3, powers := [(2, 1), (38, 1), (59, 1)] }, { coefficient := -3, powers := [(2, 1), (48, 1), (53, 1)] }, { coefficient := -1, powers := [(12, 1), (19, 1), (28, 1), (48, 1), (52, 1)] }, { coefficient := -2, powers := [(12, 1), (19, 1), (29, 1), (48, 1), (51, 1)] }, { coefficient := 2, powers := [(12, 1), (24, 1), (28, 1), (48, 1), (52, 1)] }, { coefficient := 2, powers := [(12, 1), (24, 1), (29, 1), (40, 1), (48, 1)] }, { coefficient := 6, powers := [(12, 1), (29, 1), (48, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (37, 1), (58, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (40, 1), (55, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (45, 1), (51, 1)] }, { coefficient := -1, powers := [(19, 1), (45, 1)] }, { coefficient := -1, powers := [(24, 1), (51, 1)] }, { coefficient := 1, powers := [(36, 1), (58, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := -2, powers := [(0, 1), (2, 1), (40, 1), (48, 1), (53, 1)] }, { coefficient := -1, powers := [(0, 1), (2, 1), (45, 1), (48, 1), (53, 1)] }, { coefficient := -1, powers := [(0, 1), (2, 1), (48, 1), (51, 1), (53, 1)] }, { coefficient := -2, powers := [(0, 1), (18, 1), (23, 1), (51, 1), (53, 1)] }, { coefficient := -2, powers := [(2, 1), (19, 1), (48, 1), (51, 1), (53, 1)] }, { coefficient := -2, powers := [(2, 1), (24, 1), (40, 1), (48, 1), (53, 1)] }, { coefficient := -1, powers := [(2, 1), (24, 1), (45, 1), (48, 1), (53, 1)] }, { coefficient := -3, powers := [(2, 1), (24, 1), (48, 1), (51, 1), (53, 1)] }, { coefficient := 5, powers := [(2, 1), (48, 1), (53, 1)] }, { coefficient := 1, powers := [(3, 1), (18, 1), (32, 1), (47, 1), (52, 1)] }, { coefficient := -1, powers := [(5, 1), (24, 1), (32, 1), (46, 1), (52, 1)] }, { coefficient := -4, powers := [(18, 1), (19, 1), (23, 1), (51, 1), (53, 1)] }, { coefficient := 2, powers := [(18, 1), (23, 1), (24, 1), (45, 1), (53, 1)] }, { coefficient := -2, powers := [(18, 1), (23, 1), (24, 1), (51, 1), (53, 1)] }, { coefficient := 2, powers := [(18, 1), (23, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(0, 2), (37, 1), (58, 1)] }, { coefficient := -1, powers := [(0, 2), (40, 1), (55, 1)] }, { coefficient := -1, powers := [(0, 2), (45, 1), (51, 1)] }, { coefficient := -1, powers := [(0, 1), (24, 1), (37, 1), (58, 1)] }, { coefficient := -1, powers := [(0, 1), (24, 1), (40, 1), (55, 1)] }, { coefficient := -1, powers := [(0, 1), (24, 1), (45, 1), (51, 1)] }, { coefficient := -1, powers := [(19, 1), (24, 1), (37, 1), (58, 1)] }, { coefficient := -1, powers := [(19, 1), (24, 1), (40, 1), (55, 1)] }, { coefficient := -1, powers := [(19, 1), (24, 1), (45, 1), (51, 1)] }, { coefficient := 1, powers := [(19, 1), (45, 1)] }, { coefficient := -1, powers := [(19, 1), (51, 1)] }, { coefficient := -1, powers := [(36, 1), (58, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 2), (2, 1), (40, 1), (56, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 2), (2, 1), (45, 1), (56, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 2), (2, 1), (51, 1), (56, 1), (60, 1)] }, { coefficient := 2, powers := [(0, 1), (2, 1), (19, 1), (51, 1), (56, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (2, 1), (24, 1), (45, 1), (56, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (2, 1), (24, 1), (51, 1), (56, 1), (60, 1)] }, { coefficient := -3, powers := [(0, 1), (2, 1), (56, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (8, 1), (35, 1), (40, 1)] }, { coefficient := 1, powers := [(0, 1), (8, 1), (35, 1), (45, 1)] }, { coefficient := 1, powers := [(0, 1), (8, 1), (35, 1), (51, 1)] }, { coefficient := 1, powers := [(0, 1), (8, 1), (35, 1), (55, 1)] }, { coefficient := -2, powers := [(0, 1), (17, 1), (28, 1), (56, 1)] }, { coefficient := -1, powers := [(0, 1), (18, 1), (29, 1), (40, 1)] }, { coefficient := -1, powers := [(0, 1), (18, 1), (29, 1), (45, 1)] }, { coefficient := -1, powers := [(0, 1), (18, 1), (29, 1), (51, 1)] }, { coefficient := -1, powers := [(0, 1), (18, 1), (29, 1), (55, 1)] }, { coefficient := -1, powers := [(2, 1), (19, 1), (51, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (19, 1), (55, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (24, 1), (40, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (24, 1), (45, 1), (56, 1)] }, { coefficient := 3, powers := [(2, 1), (56, 1)] }, { coefficient := -1, powers := [(8, 1), (19, 1), (35, 1), (51, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (35, 1), (40, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (35, 1), (45, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (35, 1), (55, 1)] }, { coefficient := 3, powers := [(8, 1), (35, 1)] }, { coefficient := -1, powers := [(17, 1), (19, 1), (28, 1), (56, 1)] }, { coefficient := -1, powers := [(17, 1), (24, 1), (28, 1), (56, 1)] }, { coefficient := 2, powers := [(17, 1), (27, 1), (56, 1)] }, { coefficient := 1, powers := [(18, 1), (19, 1), (29, 1), (51, 1)] }, { coefficient := -1, powers := [(18, 1), (24, 1), (29, 1), (40, 1)] }, { coefficient := -1, powers := [(18, 1), (24, 1), (29, 1), (45, 1)] }, { coefficient := -1, powers := [(18, 1), (24, 1), (29, 1), (55, 1)] }, { coefficient := 1, powers := [(18, 1), (27, 1), (52, 1)] }, { coefficient := -3, powers := [(18, 1), (29, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
/-- Lean replays the exact selected-row integer certificate. -/
theorem constantIdentity :
    ∑ index, (multipliers index).toPoly *
      (selectedEquations index).toPoly = C (3 : ℤ) := by
  simp (config := { maxSteps := 1000000 })
    [Fin.sum_univ_succ, multipliers, selectedEquations,
    SparsePoly.toPoly, SparseTerm.toPoly]
  ring

/-- The selected rows have no common zero in a characteristic-zero ring. -/
theorem selectedHasNoCommonZero {R : Type*} [CommRing R] [Nontrivial R] [CharZero R]
    (values : Fin 64 → R) :
    ¬ ∀ index : Fin 68,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((3 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (3 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (3 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component10.SelectedLeafB7_2.selectedHasNoCommonZero

end Krenn.Component10.SelectedLeafB7_2
