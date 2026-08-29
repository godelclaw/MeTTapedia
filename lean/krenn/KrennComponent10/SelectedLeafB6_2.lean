import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component10.SelectedLeafB6_2

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "c45368e0958984d3ae0056bb67ed1c3a2424862146bb56d7b07d351f582bb520"
def certificateSHA256 : String := "6c50bbf44bc508ab3f0b844da0804a545d0bf46f568d27c4c01815385d331580"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 58 → Fin 641 := ![
  8,
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
  166,
  167,
  172,
  174,
  176,
  177,
  180,
  181,
  184,
  185,
  186,
  189,
  190,
  284,
  322,
  343,
  349,
  350,
  353,
  356,
  358,
  359,
  363,
  368,
  369,
  409,
  446,
  456,
  458,
  463,
  466,
  473,
  512,
  513,
  550,
  556,
  557,
  568,
  579,
  580,
  599,
  626,
  634,
  635,
  636,
  637,
  640
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 58 → SparsePoly (Fin 63) := ![
  [{ coefficient := 1, powers := [(12, 1), (24, 1)] }],
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
  [{ coefficient := 1, powers := [(4, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (58, 1)] }, { coefficient := 1, powers := [(17, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (24, 1)] }, { coefficient := 1, powers := [(15, 1), (19, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (29, 1)] }, { coefficient := 1, powers := [(15, 1), (22, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (43, 1)] }, { coefficient := 1, powers := [(16, 1), (19, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (56, 1)] }, { coefficient := 1, powers := [(16, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (45, 1)] }, { coefficient := 1, powers := [(12, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (47, 1)] }, { coefficient := 1, powers := [(17, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (19, 1)] }, { coefficient := 1, powers := [(17, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (43, 1)] }, { coefficient := 1, powers := [(18, 1), (19, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (56, 1)] }, { coefficient := 1, powers := [(18, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (43, 1)] }, { coefficient := 1, powers := [(27, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (52, 1)] }, { coefficient := 1, powers := [(29, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (19, 1), (55, 1)] }, { coefficient := 1, powers := [(12, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (43, 1), (51, 1)] }, { coefficient := 1, powers := [(28, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1)] }, { coefficient := 1, powers := [(19, 1), (43, 1)] }, { coefficient := 1, powers := [(24, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (59, 1)] }, { coefficient := 1, powers := [(12, 1), (48, 1)] }, { coefficient := 1, powers := [(18, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (59, 1)] }, { coefficient := 1, powers := [(12, 1), (56, 1)] }, { coefficient := 1, powers := [(18, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (46, 1)] }, { coefficient := 1, powers := [(16, 1), (40, 1)] }, { coefficient := 1, powers := [(16, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (46, 1)] }, { coefficient := 1, powers := [(18, 1), (40, 1)] }, { coefficient := 1, powers := [(18, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (51, 1)] }, { coefficient := 1, powers := [(23, 1), (55, 1)] }, { coefficient := 1, powers := [(28, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (53, 1)] }, { coefficient := 1, powers := [(29, 1), (41, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (38, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (41, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (48, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1), (51, 1)] }, { coefficient := 1, powers := [(19, 1), (43, 1), (51, 1)] }, { coefficient := 1, powers := [(43, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1), (52, 1)] }, { coefficient := 1, powers := [(19, 1), (43, 1), (52, 1)] }, { coefficient := 1, powers := [(19, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (23, 1), (58, 1)] }, { coefficient := 1, powers := [(23, 1)] }, { coefficient := 1, powers := [(27, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (24, 1), (46, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (40, 1)] }, { coefficient := 1, powers := [(18, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1)] }, { coefficient := 1, powers := [(24, 1), (40, 1), (43, 1)] }, { coefficient := 1, powers := [(24, 1), (46, 1)] }, { coefficient := 1, powers := [(43, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (46, 1)] }, { coefficient := 1, powers := [(11, 1), (25, 1), (46, 1)] }, { coefficient := 1, powers := [(16, 1), (21, 1)] }, { coefficient := 1, powers := [(16, 1), (25, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (48, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1)] }, { coefficient := 1, powers := [(17, 1), (27, 1), (48, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (53, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1)] }, { coefficient := 1, powers := [(12, 1), (29, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (40, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(43, 1), (52, 1)] }, { coefficient := 1, powers := [(56, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (29, 1), (58, 1)] }, { coefficient := 1, powers := [(11, 1), (29, 1), (45, 1)] }, { coefficient := 1, powers := [(15, 1), (28, 1), (52, 1)] }, { coefficient := 1, powers := [(15, 1), (29, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (29, 1), (59, 1)] }, { coefficient := 1, powers := [(4, 1), (32, 1), (56, 1)] }, { coefficient := 1, powers := [(4, 1), (35, 1), (53, 1)] }, { coefficient := 1, powers := [(16, 1), (28, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (43, 1), (52, 1)] }, { coefficient := 1, powers := [(23, 1), (56, 1)] }, { coefficient := 1, powers := [(29, 1), (48, 1)] }, { coefficient := 1, powers := [(35, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1)] }, { coefficient := 1, powers := [(6, 1), (58, 1)] }, { coefficient := 1, powers := [(24, 1), (40, 1)] }, { coefficient := 1, powers := [(24, 1), (45, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (51, 1)] }, { coefficient := 1, powers := [(3, 1), (58, 1)] }, { coefficient := 1, powers := [(19, 1), (51, 1)] }, { coefficient := 1, powers := [(19, 1), (55, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (41, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (55, 1)] }, { coefficient := 1, powers := [(12, 1), (23, 1), (55, 1)] }, { coefficient := 1, powers := [(12, 1), (28, 1), (47, 1)] }, { coefficient := 1, powers := [(17, 1), (28, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (51, 1)] }, { coefficient := 1, powers := [(7, 1), (20, 1), (58, 1)] }, { coefficient := 1, powers := [(7, 1), (31, 1)] }, { coefficient := 1, powers := [(11, 1), (20, 1), (55, 1)] }, { coefficient := 1, powers := [(11, 1), (26, 1)] }, { coefficient := 1, powers := [(15, 1), (20, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (58, 1)] }, { coefficient := 1, powers := [(7, 1), (58, 1)] }, { coefficient := 1, powers := [(11, 1), (45, 1)] }, { coefficient := 1, powers := [(11, 1), (55, 1)] }, { coefficient := 1, powers := [(15, 1), (40, 1)] }, { coefficient := 1, powers := [(15, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (48, 1), (52, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (52, 1)] }, { coefficient := 1, powers := [(17, 1), (23, 1), (56, 1)] }, { coefficient := 1, powers := [(17, 1), (29, 1), (48, 1)] }, { coefficient := 1, powers := [(17, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (40, 1), (56, 1)] }, { coefficient := 1, powers := [(1, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(4, 1), (31, 1), (56, 1)] }, { coefficient := 1, powers := [(11, 1), (21, 1), (56, 1)] }, { coefficient := 1, powers := [(11, 1), (25, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(16, 1), (21, 1), (52, 1)] }, { coefficient := 1, powers := [(16, 1), (25, 1), (40, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (41, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (48, 1), (53, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (53, 1)] }, { coefficient := 1, powers := [(8, 1), (23, 1), (59, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (48, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(12, 1), (23, 1), (56, 1)] }, { coefficient := 1, powers := [(12, 1), (29, 1), (48, 1)] }, { coefficient := 1, powers := [(12, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (53, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (41, 1)] }, { coefficient := 1, powers := [(18, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (60, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1), (61, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(41, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 58 → SparsePoly (Fin 63) := ![
  [{ coefficient := -2, powers := [(0, 1), (1, 1), (5, 1), (29, 2), (48, 1), (51, 1), (59, 1), (60, 1), (61, 1)] }, { coefficient := -2, powers := [(0, 1), (1, 1), (5, 1), (29, 1), (35, 1), (48, 1), (51, 1), (53, 1), (60, 1), (61, 1)] }, { coefficient := -1, powers := [(0, 1), (23, 1), (40, 1), (56, 1), (60, 1)] }, { coefficient := -1, powers := [(0, 1), (23, 1), (45, 1), (56, 1), (60, 1)] }, { coefficient := -2, powers := [(0, 1), (29, 1), (48, 1), (51, 1), (60, 1)] }, { coefficient := 1, powers := [(23, 1), (40, 1), (56, 1)] }, { coefficient := 1, powers := [(23, 1), (45, 1), (56, 1)] }, { coefficient := 2, powers := [(29, 1), (48, 1), (51, 1)] }, { coefficient := 2, powers := [(29, 1), (48, 1), (60, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (5, 1), (19, 1), (21, 1), (32, 1), (46, 1), (61, 1)] }, { coefficient := -1, powers := [(0, 1), (5, 1), (20, 1), (28, 1), (59, 1), (61, 1)] }, { coefficient := 1, powers := [(0, 1), (5, 1), (22, 1), (26, 1), (59, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (1, 1), (5, 1), (12, 1), (20, 1), (29, 1), (35, 1), (48, 1), (51, 1), (61, 2)] }, { coefficient := 1, powers := [(0, 1), (1, 1), (5, 1), (18, 1), (20, 1), (29, 1), (32, 1), (48, 1), (51, 1), (61, 2)] }, { coefficient := 1, powers := [(0, 1), (4, 1), (5, 1), (20, 1), (31, 1), (35, 1), (61, 2)] }, { coefficient := 2, powers := [(0, 1), (18, 1), (19, 1), (20, 1), (23, 1), (51, 1), (60, 1), (61, 1)] }, { coefficient := -2, powers := [(18, 1), (19, 1), (20, 1), (23, 1), (51, 1), (61, 1)] }, { coefficient := 2, powers := [(18, 1), (20, 1), (23, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(0, 2), (27, 1), (51, 1), (53, 1), (60, 1)] }, { coefficient := -1, powers := [(0, 1), (1, 1), (5, 1), (27, 1), (29, 1), (51, 1), (53, 1), (59, 1), (61, 1)] }, { coefficient := -1, powers := [(0, 1), (3, 1), (12, 1), (27, 1), (32, 1), (46, 1), (47, 1), (52, 2)] }, { coefficient := -1, powers := [(0, 1), (3, 1), (12, 1), (27, 1), (32, 1), (47, 1), (52, 1), (56, 1), (60, 1)] }, { coefficient := 2, powers := [(0, 1), (3, 1), (12, 1), (29, 1), (32, 1), (46, 1), (47, 1), (52, 1)] }, { coefficient := 2, powers := [(0, 1), (3, 1), (12, 1), (29, 1), (32, 1), (47, 1), (56, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (3, 1), (17, 1), (27, 1), (32, 1), (46, 1), (47, 1), (52, 1), (53, 1)] }, { coefficient := 1, powers := [(0, 1), (3, 1), (17, 1), (27, 1), (32, 1), (47, 1), (53, 1), (56, 1), (60, 1)] }, { coefficient := -1, powers := [(0, 1), (27, 1), (51, 1), (53, 1)] }, { coefficient := 1, powers := [(3, 1), (12, 1), (27, 1), (32, 1), (47, 1), (52, 1), (56, 1)] }, { coefficient := -2, powers := [(3, 1), (12, 1), (29, 1), (32, 1), (47, 1), (56, 1)] }, { coefficient := -1, powers := [(3, 1), (17, 1), (27, 1), (32, 1), (47, 1), (53, 1), (56, 1)] }, { coefficient := -1, powers := [(27, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(0, 2), (22, 1), (48, 1), (51, 1), (60, 1)] }, { coefficient := 2, powers := [(0, 1), (1, 1), (5, 1), (22, 1), (29, 1), (48, 1), (51, 1), (59, 1), (61, 1)] }, { coefficient := 1, powers := [(0, 1), (3, 1), (17, 1), (22, 1), (32, 1), (46, 1), (47, 1), (48, 1), (52, 1)] }, { coefficient := 1, powers := [(0, 1), (3, 1), (17, 1), (22, 1), (32, 1), (47, 1), (48, 1), (56, 1), (60, 1)] }, { coefficient := 2, powers := [(0, 1), (3, 1), (18, 1), (23, 1), (32, 1), (46, 1), (47, 1), (52, 1)] }, { coefficient := 2, powers := [(0, 1), (3, 1), (18, 1), (23, 1), (32, 1), (47, 1), (56, 1), (60, 1)] }, { coefficient := -1, powers := [(0, 1), (22, 1), (48, 1), (51, 1)] }, { coefficient := -1, powers := [(3, 1), (17, 1), (22, 1), (32, 1), (47, 1), (48, 1), (56, 1)] }, { coefficient := -2, powers := [(3, 1), (18, 1), (23, 1), (32, 1), (47, 1), (56, 1)] }, { coefficient := -1, powers := [(22, 1), (48, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (5, 1), (16, 1), (31, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(0, 2), (12, 1), (28, 1), (60, 2)] }, { coefficient := -1, powers := [(0, 1), (12, 1), (19, 1), (28, 1), (60, 2)] }, { coefficient := 1, powers := [(0, 1), (12, 1), (28, 1), (60, 1)] }, { coefficient := 1, powers := [(12, 1), (19, 1), (28, 1), (60, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (1, 1), (5, 1), (12, 1), (29, 2), (51, 1), (59, 1), (60, 1), (61, 1)] }, { coefficient := 2, powers := [(0, 1), (1, 1), (5, 1), (12, 1), (29, 1), (35, 1), (51, 1), (53, 1), (60, 1), (61, 1)] }, { coefficient := -1, powers := [(0, 1), (12, 1), (27, 1), (51, 1), (52, 1), (60, 1)] }, { coefficient := 2, powers := [(0, 1), (12, 1), (29, 1), (51, 1), (60, 1)] }, { coefficient := 1, powers := [(12, 1), (27, 1), (51, 1), (52, 1)] }, { coefficient := -2, powers := [(12, 1), (29, 1), (51, 1)] }, { coefficient := -2, powers := [(12, 1), (29, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (3, 1), (5, 1), (17, 1), (32, 2), (43, 1), (46, 1), (47, 1), (51, 1), (52, 1)] }, { coefficient := -1, powers := [(0, 1), (3, 1), (5, 1), (17, 1), (32, 2), (43, 1), (47, 1), (51, 1), (56, 1), (60, 1)] }, { coefficient := -2, powers := [(0, 1), (5, 1), (11, 1), (21, 1), (32, 1), (40, 1), (43, 1), (61, 1)] }, { coefficient := 1, powers := [(0, 1), (5, 1), (11, 1), (21, 1), (32, 1), (46, 1), (61, 1)] }, { coefficient := 1, powers := [(0, 1), (5, 1), (16, 1), (21, 1), (32, 1), (40, 1), (61, 1)] }, { coefficient := 1, powers := [(0, 1), (5, 1), (32, 1), (46, 1), (51, 1)] }, { coefficient := -2, powers := [(0, 1), (12, 1), (23, 1), (43, 1), (45, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (12, 1), (23, 1), (43, 1), (51, 1), (60, 1)] }, { coefficient := 1, powers := [(3, 1), (5, 1), (17, 1), (32, 2), (43, 1), (47, 1), (51, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (43, 1), (51, 1)] }, { coefficient := 3, powers := [(12, 1), (23, 1), (43, 1), (45, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (18, 1), (23, 1), (51, 1), (60, 1)] }, { coefficient := -2, powers := [(18, 1), (23, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (1, 1), (5, 1), (12, 1), (29, 1), (35, 1), (48, 1), (51, 1), (61, 2)] }, { coefficient := -1, powers := [(0, 1), (1, 1), (5, 1), (18, 1), (29, 1), (32, 1), (48, 1), (51, 1), (61, 2)] }, { coefficient := -1, powers := [(0, 1), (4, 1), (5, 1), (31, 1), (35, 1), (61, 2)] }, { coefficient := -2, powers := [(0, 1), (18, 1), (19, 1), (23, 1), (51, 1), (60, 1), (61, 1)] }, { coefficient := 2, powers := [(18, 1), (19, 1), (23, 1), (51, 1), (61, 1)] }, { coefficient := -2, powers := [(18, 1), (23, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (5, 1), (29, 1), (31, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (3, 1), (32, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(0, 1), (3, 1), (32, 1), (56, 1), (60, 1)] }, { coefficient := -1, powers := [(3, 1), (32, 1), (56, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (5, 1), (21, 1), (32, 1), (46, 1), (52, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (5, 1), (26, 1), (59, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (5, 1), (21, 1), (32, 1), (52, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(0, 2), (5, 1), (21, 1), (32, 1), (40, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(0, 2), (23, 1), (56, 1), (60, 1)] }, { coefficient := -2, powers := [(0, 1), (19, 1), (23, 1), (56, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (23, 1), (56, 1)] }, { coefficient := 3, powers := [(19, 1), (23, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [(0, 2), (28, 1), (56, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (3, 1), (18, 1), (29, 1), (32, 1), (46, 1), (47, 1), (52, 1)] }, { coefficient := 1, powers := [(0, 1), (3, 1), (18, 1), (29, 1), (32, 1), (47, 1), (56, 1), (60, 1)] }, { coefficient := -1, powers := [(0, 1), (19, 1), (28, 1), (46, 1), (52, 1)] }, { coefficient := -2, powers := [(0, 1), (19, 1), (28, 1), (56, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (27, 1), (56, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (28, 1), (56, 1)] }, { coefficient := -1, powers := [(0, 1), (29, 1), (46, 1)] }, { coefficient := -1, powers := [(3, 1), (18, 1), (29, 1), (32, 1), (47, 1), (56, 1)] }, { coefficient := 2, powers := [(19, 1), (28, 1), (56, 1)] }, { coefficient := -1, powers := [(27, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (3, 1), (5, 1), (32, 2), (46, 1), (47, 1), (51, 1), (52, 1), (56, 1)] }, { coefficient := -1, powers := [(0, 1), (3, 1), (5, 1), (32, 2), (47, 1), (51, 1), (56, 2), (60, 1)] }, { coefficient := 1, powers := [(3, 1), (5, 1), (32, 2), (47, 1), (51, 1), (56, 2)] }],
  [{ coefficient := -1, powers := [(0, 1), (3, 1), (5, 1), (32, 2), (46, 1), (47, 1), (52, 2)] }, { coefficient := -1, powers := [(0, 1), (3, 1), (5, 1), (32, 2), (47, 1), (52, 1), (56, 1), (60, 1)] }, { coefficient := 1, powers := [(3, 1), (5, 1), (32, 2), (47, 1), (52, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (3, 1), (5, 1), (19, 1), (32, 2), (46, 1), (47, 1), (51, 1), (52, 1)] }, { coefficient := 1, powers := [(0, 1), (3, 1), (5, 1), (19, 1), (32, 2), (47, 1), (51, 1), (56, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (3, 1), (5, 1), (24, 1), (32, 2), (46, 1), (47, 1), (51, 1), (52, 1)] }, { coefficient := 1, powers := [(0, 1), (3, 1), (5, 1), (24, 1), (32, 2), (47, 1), (51, 1), (56, 1), (60, 1)] }, { coefficient := -1, powers := [(0, 1), (3, 1), (5, 1), (32, 2), (46, 1), (47, 1), (52, 1)] }, { coefficient := -1, powers := [(0, 1), (3, 1), (5, 1), (32, 2), (47, 1), (56, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (3, 1), (12, 1), (23, 1), (32, 1), (46, 1), (47, 1), (52, 1)] }, { coefficient := 1, powers := [(0, 1), (3, 1), (12, 1), (23, 1), (32, 1), (47, 1), (56, 1), (60, 1)] }, { coefficient := -1, powers := [(3, 1), (5, 1), (19, 1), (32, 2), (47, 1), (51, 1), (56, 1)] }, { coefficient := -1, powers := [(3, 1), (5, 1), (24, 1), (32, 2), (47, 1), (51, 1), (56, 1)] }, { coefficient := 1, powers := [(3, 1), (5, 1), (32, 2), (47, 1), (56, 1)] }, { coefficient := -1, powers := [(3, 1), (12, 1), (23, 1), (32, 1), (47, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(0, 2), (12, 1), (51, 1), (52, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (12, 1), (24, 1), (51, 1), (52, 1), (60, 1)] }, { coefficient := -1, powers := [(0, 1), (12, 1), (51, 1), (52, 1)] }, { coefficient := -1, powers := [(12, 1), (24, 1), (51, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (3, 1), (12, 1), (18, 1), (32, 1), (46, 1), (47, 1), (52, 1)] }, { coefficient := -1, powers := [(0, 1), (3, 1), (12, 1), (18, 1), (32, 1), (47, 1), (56, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (12, 1), (46, 1)] }, { coefficient := 1, powers := [(3, 1), (12, 1), (18, 1), (32, 1), (47, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (23, 1), (46, 1), (52, 1)] }, { coefficient := -1, powers := [(23, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(0, 2), (12, 1), (52, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (12, 1), (19, 1), (52, 1), (60, 1)] }, { coefficient := -1, powers := [(0, 1), (12, 1), (52, 1)] }, { coefficient := -1, powers := [(12, 1), (19, 1), (52, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (5, 1), (11, 1), (21, 1), (32, 1), (40, 1), (52, 1), (61, 1)] }, { coefficient := -1, powers := [(0, 1), (12, 1), (23, 1), (51, 1), (52, 1), (60, 1)] }, { coefficient := 1, powers := [(12, 1), (23, 1), (51, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(0, 2), (29, 1), (51, 1), (60, 1)] }, { coefficient := -1, powers := [(0, 1), (1, 1), (5, 1), (29, 2), (51, 1), (59, 1), (61, 1)] }, { coefficient := -1, powers := [(0, 1), (1, 1), (5, 1), (29, 1), (32, 1), (51, 1), (56, 1), (61, 1)] }, { coefficient := -2, powers := [(0, 1), (1, 1), (5, 1), (29, 1), (35, 1), (51, 1), (53, 1), (61, 1)] }, { coefficient := -1, powers := [(0, 1), (3, 1), (17, 1), (29, 1), (32, 1), (46, 1), (47, 1), (52, 1)] }, { coefficient := -1, powers := [(0, 1), (3, 1), (17, 1), (29, 1), (32, 1), (47, 1), (56, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (29, 1), (51, 1)] }, { coefficient := 1, powers := [(3, 1), (17, 1), (29, 1), (32, 1), (47, 1), (56, 1)] }, { coefficient := 1, powers := [(29, 1)] }],
  [{ coefficient := -1, powers := [(0, 2), (23, 1), (51, 1), (60, 1)] }, { coefficient := -1, powers := [(0, 1), (1, 1), (5, 1), (23, 1), (29, 1), (51, 1), (59, 1), (61, 1)] }, { coefficient := 1, powers := [(0, 1), (1, 1), (5, 1), (29, 1), (32, 1), (48, 1), (51, 1), (61, 1)] }, { coefficient := -1, powers := [(0, 1), (3, 1), (17, 1), (23, 1), (32, 1), (46, 1), (47, 1), (52, 1)] }, { coefficient := -1, powers := [(0, 1), (3, 1), (17, 1), (23, 1), (32, 1), (47, 1), (56, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (23, 1), (51, 1)] }, { coefficient := 1, powers := [(3, 1), (17, 1), (23, 1), (32, 1), (47, 1), (56, 1)] }, { coefficient := 1, powers := [(23, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (5, 1), (19, 1), (21, 1), (32, 1), (52, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (3, 1), (5, 1), (24, 1), (32, 2), (46, 1), (47, 1), (52, 2)] }, { coefficient := -1, powers := [(0, 1), (3, 1), (5, 1), (24, 1), (32, 2), (47, 1), (52, 1), (56, 1), (60, 1)] }, { coefficient := 1, powers := [(3, 1), (5, 1), (24, 1), (32, 2), (47, 1), (52, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(0, 2), (12, 1), (56, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (12, 1), (19, 1), (56, 1), (60, 1)] }, { coefficient := -1, powers := [(0, 1), (12, 1), (56, 1)] }, { coefficient := -1, powers := [(12, 1), (19, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [(0, 2), (18, 1), (51, 1), (60, 1)] }, { coefficient := -1, powers := [(0, 1), (1, 1), (5, 1), (18, 1), (29, 1), (51, 1), (59, 1), (61, 1)] }, { coefficient := -1, powers := [(0, 1), (3, 1), (17, 1), (18, 1), (32, 1), (46, 1), (47, 1), (52, 1)] }, { coefficient := -1, powers := [(0, 1), (3, 1), (17, 1), (18, 1), (32, 1), (47, 1), (56, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (18, 1), (51, 1)] }, { coefficient := 1, powers := [(3, 1), (17, 1), (18, 1), (32, 1), (47, 1), (56, 1)] }, { coefficient := 1, powers := [(18, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (1, 1), (5, 1), (12, 1), (29, 1), (35, 1), (51, 1), (60, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (3, 1), (5, 1), (17, 1), (32, 2), (46, 1), (47, 1), (52, 2)] }, { coefficient := 1, powers := [(0, 1), (3, 1), (5, 1), (17, 1), (32, 2), (47, 1), (52, 1), (56, 1), (60, 1)] }, { coefficient := -1, powers := [(0, 1), (5, 1), (32, 1), (52, 1), (60, 1)] }, { coefficient := -1, powers := [(3, 1), (5, 1), (17, 1), (32, 2), (47, 1), (52, 1), (56, 1)] }, { coefficient := -1, powers := [(12, 1), (23, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (5, 1), (32, 1), (51, 1), (60, 1)] }, { coefficient := 2, powers := [(0, 1), (12, 1), (23, 1), (45, 1), (60, 1)] }, { coefficient := -1, powers := [(0, 1), (12, 1), (23, 1), (51, 1), (60, 1)] }, { coefficient := -1, powers := [(5, 1), (32, 1), (51, 1)] }, { coefficient := -3, powers := [(12, 1), (23, 1), (45, 1)] }, { coefficient := 1, powers := [(12, 1), (23, 1), (51, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (12, 1), (56, 1), (60, 1)] }, { coefficient := 1, powers := [(12, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (3, 1), (5, 1), (32, 2), (46, 1), (47, 1), (52, 2)] }, { coefficient := 1, powers := [(0, 1), (3, 1), (5, 1), (32, 2), (47, 1), (52, 1), (56, 1), (60, 1)] }, { coefficient := -1, powers := [(3, 1), (5, 1), (32, 2), (47, 1), (52, 1), (56, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (5, 1), (11, 1), (21, 1), (32, 1), (52, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (5, 1), (32, 1), (52, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(0, 2), (51, 1), (53, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (1, 1), (5, 1), (29, 1), (51, 1), (53, 1), (59, 1), (61, 1)] }, { coefficient := 1, powers := [(0, 1), (3, 1), (12, 1), (32, 1), (46, 1), (47, 1), (52, 2)] }, { coefficient := 1, powers := [(0, 1), (3, 1), (12, 1), (32, 1), (47, 1), (52, 1), (56, 1), (60, 1)] }, { coefficient := -1, powers := [(0, 1), (3, 1), (17, 1), (32, 1), (46, 1), (47, 1), (52, 1), (53, 1)] }, { coefficient := -1, powers := [(0, 1), (3, 1), (17, 1), (32, 1), (47, 1), (53, 1), (56, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (51, 1), (53, 1)] }, { coefficient := -1, powers := [(3, 1), (12, 1), (32, 1), (47, 1), (52, 1), (56, 1)] }, { coefficient := 1, powers := [(3, 1), (17, 1), (32, 1), (47, 1), (53, 1), (56, 1)] }, { coefficient := 1, powers := [(53, 1)] }],
  [{ coefficient := -1, powers := [(0, 2), (48, 1), (51, 1), (60, 1)] }, { coefficient := -2, powers := [(0, 1), (1, 1), (5, 1), (29, 1), (48, 1), (51, 1), (59, 1), (61, 1)] }, { coefficient := -1, powers := [(0, 1), (3, 1), (17, 1), (32, 1), (46, 1), (47, 1), (48, 1), (52, 1)] }, { coefficient := -1, powers := [(0, 1), (3, 1), (17, 1), (32, 1), (47, 1), (48, 1), (56, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (48, 1), (51, 1)] }, { coefficient := 1, powers := [(3, 1), (17, 1), (32, 1), (47, 1), (48, 1), (56, 1)] }, { coefficient := 1, powers := [(48, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (5, 1), (11, 1), (21, 1), (32, 1), (61, 1)] }, { coefficient := 1, powers := [(0, 1), (5, 1), (32, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (5, 1), (20, 1), (59, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (5, 1), (31, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(0, 2), (12, 1), (51, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (12, 1), (51, 1)] }, { coefficient := 1, powers := [(12, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (12, 1), (23, 1), (56, 1), (60, 1)] }, { coefficient := -1, powers := [(12, 1), (23, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (5, 1), (32, 1), (46, 1), (52, 1)] }, { coefficient := -1, powers := [(0, 1), (5, 1), (32, 1), (56, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (19, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(0, 1), (19, 1), (56, 1), (60, 1)] }, { coefficient := -1, powers := [(19, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (5, 1), (29, 1), (59, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (5, 1), (20, 1), (29, 1), (59, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (3, 1), (12, 1), (32, 1), (46, 1), (47, 1), (52, 1)] }, { coefficient := -1, powers := [(0, 1), (3, 1), (12, 1), (32, 1), (47, 1), (56, 1), (60, 1)] }, { coefficient := 1, powers := [(3, 1), (12, 1), (32, 1), (47, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (5, 1), (32, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(0, 2), (51, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (1, 1), (5, 1), (29, 1), (51, 1), (59, 1), (61, 1)] }, { coefficient := 1, powers := [(0, 1), (3, 1), (17, 1), (32, 1), (46, 1), (47, 1), (52, 1)] }, { coefficient := 1, powers := [(0, 1), (3, 1), (17, 1), (32, 1), (47, 1), (56, 1), (60, 1)] }, { coefficient := -1, powers := [(0, 1), (51, 1)] }, { coefficient := -1, powers := [(3, 1), (17, 1), (32, 1), (47, 1), (56, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 2), (12, 1), (28, 1), (48, 1), (52, 1), (60, 1)] }, { coefficient := -2, powers := [(0, 1), (1, 1), (5, 1), (12, 1), (29, 2), (48, 1), (51, 1), (59, 1), (61, 1)] }, { coefficient := 1, powers := [(0, 1), (1, 1), (5, 1), (12, 1), (29, 1), (35, 1), (38, 1), (51, 1), (59, 1), (61, 1)] }, { coefficient := -1, powers := [(0, 1), (1, 1), (5, 1), (12, 1), (29, 1), (35, 1), (48, 1), (51, 1), (53, 1), (61, 1)] }, { coefficient := -1, powers := [(0, 1), (5, 1), (32, 1), (40, 1), (56, 1)] }, { coefficient := -1, powers := [(0, 1), (5, 1), (32, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(0, 1), (12, 1), (19, 1), (28, 1), (48, 1), (52, 1), (60, 1)] }, { coefficient := -1, powers := [(0, 1), (12, 1), (28, 1), (48, 1), (52, 1)] }, { coefficient := 1, powers := [(0, 1), (51, 1)] }, { coefficient := -1, powers := [(12, 1), (19, 1), (28, 1), (48, 1), (52, 1)] }, { coefficient := 2, powers := [(12, 1), (29, 1), (48, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (1, 1), (5, 1), (12, 1), (29, 1), (35, 1), (48, 1), (51, 1), (53, 1), (61, 1)] }, { coefficient := 1, powers := [(0, 1), (1, 1), (5, 1), (18, 1), (29, 1), (32, 1), (48, 1), (51, 1), (53, 1), (61, 1)] }, { coefficient := 1, powers := [(0, 1), (4, 1), (5, 1), (31, 1), (35, 1), (53, 1), (61, 1)] }, { coefficient := 1, powers := [(0, 1), (5, 1), (32, 1), (40, 1), (56, 1)] }, { coefficient := 2, powers := [(0, 1), (18, 1), (19, 1), (23, 1), (51, 1), (53, 1), (60, 1)] }, { coefficient := -2, powers := [(18, 1), (19, 1), (23, 1), (51, 1), (53, 1)] }, { coefficient := 2, powers := [(18, 1), (23, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(0, 2), (38, 1), (51, 1), (59, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 2), (48, 1), (51, 1), (53, 1), (60, 1)] }, { coefficient := -1, powers := [(0, 1), (1, 1), (5, 1), (29, 1), (38, 1), (51, 1), (59, 2), (61, 1)] }, { coefficient := -1, powers := [(0, 1), (3, 1), (17, 1), (32, 1), (38, 1), (46, 1), (47, 1), (52, 1), (59, 1)] }, { coefficient := -1, powers := [(0, 1), (3, 1), (17, 1), (32, 1), (38, 1), (47, 1), (56, 1), (59, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (3, 1), (17, 1), (32, 1), (46, 1), (47, 1), (48, 1), (52, 1), (53, 1)] }, { coefficient := 1, powers := [(0, 1), (3, 1), (17, 1), (32, 1), (47, 1), (48, 1), (53, 1), (56, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (38, 1), (51, 1), (59, 1)] }, { coefficient := -1, powers := [(0, 1), (48, 1), (51, 1), (53, 1)] }, { coefficient := 1, powers := [(3, 1), (17, 1), (32, 1), (38, 1), (47, 1), (56, 1), (59, 1)] }, { coefficient := -1, powers := [(3, 1), (17, 1), (32, 1), (47, 1), (48, 1), (53, 1), (56, 1)] }, { coefficient := 1, powers := [(38, 1), (59, 1)] }, { coefficient := -1, powers := [(48, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(0, 2), (1, 1), (5, 1), (12, 1), (29, 1), (35, 1), (51, 1), (56, 1), (60, 1), (61, 1)] }, { coefficient := -1, powers := [(0, 2), (2, 1), (51, 1), (56, 1), (60, 1)] }, { coefficient := -1, powers := [(0, 2), (8, 1), (35, 1), (51, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 2), (17, 1), (28, 1), (56, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 2), (18, 1), (29, 1), (51, 1), (60, 1)] }, { coefficient := -1, powers := [(0, 1), (1, 1), (2, 1), (5, 1), (29, 1), (51, 1), (56, 1), (59, 1), (61, 1)] }, { coefficient := -1, powers := [(0, 1), (1, 1), (5, 1), (8, 1), (29, 1), (35, 1), (51, 1), (59, 1), (61, 1)] }, { coefficient := 1, powers := [(0, 1), (1, 1), (5, 1), (18, 1), (29, 2), (51, 1), (59, 1), (61, 1)] }, { coefficient := 1, powers := [(0, 1), (1, 1), (5, 1), (18, 1), (29, 1), (32, 1), (51, 1), (56, 1), (61, 1)] }, { coefficient := 2, powers := [(0, 1), (1, 1), (5, 1), (18, 1), (29, 1), (35, 1), (51, 1), (53, 1), (61, 1)] }, { coefficient := -1, powers := [(0, 1), (2, 1), (3, 1), (17, 1), (32, 1), (46, 1), (47, 1), (52, 1), (56, 1)] }, { coefficient := -1, powers := [(0, 1), (2, 1), (3, 1), (17, 1), (32, 1), (47, 1), (56, 2), (60, 1)] }, { coefficient := -1, powers := [(0, 1), (2, 1), (19, 1), (46, 1), (52, 1), (55, 1)] }, { coefficient := -1, powers := [(0, 1), (2, 1), (19, 1), (55, 1), (56, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (2, 1), (51, 1), (56, 1)] }, { coefficient := -1, powers := [(0, 1), (3, 1), (8, 1), (17, 1), (32, 1), (35, 1), (46, 1), (47, 1), (52, 1)] }, { coefficient := -1, powers := [(0, 1), (3, 1), (8, 1), (17, 1), (32, 1), (35, 1), (47, 1), (56, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (8, 1), (35, 1), (51, 1)] }, { coefficient := 1, powers := [(0, 1), (17, 1), (19, 1), (28, 1), (56, 1), (60, 1)] }, { coefficient := -1, powers := [(0, 1), (17, 1), (27, 1), (56, 1), (60, 1)] }, { coefficient := -1, powers := [(0, 1), (17, 1), (28, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (17, 1), (29, 1), (46, 1)] }, { coefficient := -1, powers := [(0, 1), (18, 1), (29, 1), (51, 1)] }, { coefficient := 1, powers := [(2, 1), (3, 1), (17, 1), (32, 1), (47, 1), (56, 2)] }, { coefficient := 1, powers := [(2, 1), (19, 1), (55, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (56, 1)] }, { coefficient := 1, powers := [(3, 1), (8, 1), (17, 1), (32, 1), (35, 1), (47, 1), (56, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1)] }, { coefficient := -1, powers := [(17, 1), (19, 1), (28, 1), (56, 1)] }, { coefficient := 1, powers := [(17, 1), (27, 1), (56, 1)] }, { coefficient := -1, powers := [(18, 1), (29, 1)] }]
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
    ¬ ∀ index : Fin 58,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component10.SelectedLeafB6_2.selectedHasNoCommonZero

end Krenn.Component10.SelectedLeafB6_2
