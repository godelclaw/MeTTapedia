import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component55.SelectedLeafB4_2_1

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "ffb7f625c349b14d2c0faf46c3889a7bc47d50ee7ea3dbc8c0f2a3209fd5d2a6"
def certificateSHA256 : String := "753f219196b7e66975a32ed70f521c46dd211d13aeb37759e0d7c4ce4951f687"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 64 → Fin 593 := ![
  7,
  24,
  25,
  28,
  36,
  38,
  65,
  76,
  191,
  194,
  195,
  223,
  225,
  226,
  228,
  230,
  232,
  233,
  234,
  235,
  243,
  251,
  257,
  263,
  296,
  341,
  342,
  343,
  345,
  347,
  348,
  354,
  355,
  360,
  361,
  362,
  365,
  390,
  416,
  445,
  450,
  456,
  474,
  480,
  490,
  494,
  515,
  543,
  544,
  551,
  555,
  556,
  559,
  581,
  582,
  583,
  585,
  586,
  587,
  588,
  589,
  590,
  591,
  592
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 64 → SparsePoly (Fin 61) := ![
  [{ coefficient := 1, powers := [(5, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (29, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(30, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (30, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (35, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (35, 1)] }, { coefficient := 1, powers := [(35, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (32, 1)] }, { coefficient := 1, powers := [(32, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (30, 1)] }, { coefficient := 1, powers := [(15, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (20, 1)] }, { coefficient := 1, powers := [(18, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (46, 1)] }, { coefficient := 1, powers := [(19, 1), (21, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (54, 1)] }, { coefficient := 1, powers := [(26, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (49, 1)] }, { coefficient := 1, powers := [(21, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (54, 1)] }, { coefficient := 1, powers := [(26, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (49, 1)] }, { coefficient := 1, powers := [(24, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(26, 1), (40, 1)] }, { coefficient := 1, powers := [(26, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (40, 1)] }, { coefficient := 1, powers := [(29, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(31, 1), (38, 1)] }, { coefficient := 1, powers := [(34, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (26, 1), (56, 1)] }, { coefficient := 1, powers := [(26, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (27, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (24, 1), (56, 1)] }, { coefficient := 1, powers := [(24, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (22, 1), (56, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (25, 1), (44, 1)] }, { coefficient := 1, powers := [(18, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (46, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (51, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1)] }, { coefficient := 1, powers := [(13, 1), (29, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (55, 1)] }, { coefficient := 1, powers := [(9, 1), (42, 1)] }, { coefficient := 1, powers := [(14, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (56, 1)] }, { coefficient := 1, powers := [(18, 1), (21, 1), (49, 1)] }, { coefficient := 1, powers := [(18, 1), (21, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (30, 1)] }, { coefficient := 1, powers := [(12, 1), (26, 1)] }, { coefficient := 1, powers := [(18, 1), (26, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (56, 1)] }, { coefficient := 1, powers := [(18, 1), (26, 1), (40, 1)] }, { coefficient := 1, powers := [(18, 1), (26, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (44, 1)] }, { coefficient := 1, powers := [(13, 1), (53, 1)] }, { coefficient := 1, powers := [(18, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (23, 1)] }, { coefficient := 1, powers := [(14, 1), (27, 1), (40, 1)] }, { coefficient := 1, powers := [(23, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (45, 1)] }, { coefficient := 1, powers := [(19, 1), (40, 1)] }, { coefficient := 1, powers := [(19, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (51, 1)] }, { coefficient := 1, powers := [(29, 1), (41, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (54, 1)] }, { coefficient := 1, powers := [(29, 1), (46, 1)] }, { coefficient := 1, powers := [(35, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1), (49, 1)] }, { coefficient := 1, powers := [(20, 1), (43, 1), (49, 1)] }, { coefficient := 1, powers := [(43, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (56, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (31, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1), (46, 1)] }, { coefficient := 1, powers := [(19, 1), (31, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (20, 1), (53, 1)] }, { coefficient := 1, powers := [(12, 1)] }, { coefficient := 1, powers := [(18, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (20, 1), (53, 1)] }, { coefficient := 1, powers := [(13, 1)] }, { coefficient := 1, powers := [(18, 1), (20, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (23, 1), (49, 1)] }, { coefficient := 1, powers := [(14, 1), (28, 1), (40, 1)] }, { coefficient := 1, powers := [(14, 1), (31, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (50, 1)] }, { coefficient := 1, powers := [(20, 1), (48, 1), (53, 1)] }, { coefficient := 1, powers := [(20, 1), (50, 1)] }, { coefficient := 1, powers := [(48, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (57, 1)] }, { coefficient := 1, powers := [(13, 1), (46, 1)] }, { coefficient := 1, powers := [(19, 1), (21, 1), (50, 1)] }, { coefficient := 1, powers := [(19, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (41, 1), (53, 1)] }, { coefficient := 1, powers := [(21, 1), (48, 1), (53, 1)] }, { coefficient := 1, powers := [(21, 1), (50, 1)] }, { coefficient := 1, powers := [(41, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1), (50, 1)] }, { coefficient := 1, powers := [(3, 1), (57, 1)] }, { coefficient := 1, powers := [(20, 1), (43, 1), (50, 1)] }, { coefficient := 1, powers := [(43, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (29, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (32, 1), (54, 1)] }, { coefficient := 1, powers := [(3, 1), (35, 1), (51, 1)] }, { coefficient := 1, powers := [(29, 1), (43, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (49, 1)] }, { coefficient := 1, powers := [(3, 1), (56, 1)] }, { coefficient := 1, powers := [(20, 1), (49, 1)] }, { coefficient := 1, powers := [(20, 1), (53, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (39, 1), (53, 1)] }, { coefficient := 1, powers := [(3, 1), (30, 1), (53, 1)] }, { coefficient := 1, powers := [(9, 1), (20, 1), (53, 1)] }, { coefficient := 1, powers := [(9, 1)] }, { coefficient := 1, powers := [(39, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (30, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (30, 1), (46, 1)] }, { coefficient := 1, powers := [(12, 1), (21, 1), (54, 1)] }, { coefficient := 1, powers := [(12, 1), (26, 1), (46, 1)] }, { coefficient := 1, powers := [(19, 1), (30, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1)] }, { coefficient := 1, powers := [(6, 1), (30, 1)] }, { coefficient := 1, powers := [(9, 1), (25, 1)] }, { coefficient := 1, powers := [(20, 1), (47, 1)] }, { coefficient := 1, powers := [(25, 1), (39, 1)] }, { coefficient := 1, powers := [(30, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (44, 1)] }, { coefficient := 1, powers := [(4, 1), (27, 1), (56, 1)] }, { coefficient := 1, powers := [(4, 1), (34, 1)] }, { coefficient := 1, powers := [(10, 1), (27, 1), (44, 1)] }, { coefficient := 1, powers := [(15, 1), (23, 1)] }, { coefficient := 1, powers := [(15, 1), (27, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (49, 1)] }, { coefficient := 1, powers := [(23, 1), (53, 1)] }, { coefficient := 1, powers := [(28, 1), (40, 1)] }, { coefficient := 1, powers := [(28, 1), (44, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (36, 1), (55, 1)] }, { coefficient := 1, powers := [(0, 1), (39, 1), (52, 1)] }, { coefficient := 1, powers := [(0, 1), (42, 1), (47, 1)] }, { coefficient := 1, powers := [(3, 1), (25, 1), (55, 1)] }, { coefficient := 1, powers := [(3, 1), (30, 1), (52, 1)] }, { coefficient := 1, powers := [(3, 1), (33, 1), (47, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1), (55, 1)] }, { coefficient := 1, powers := [(6, 1), (30, 1), (42, 1)] }, { coefficient := 1, powers := [(6, 1), (33, 1), (39, 1)] }, { coefficient := 1, powers := [(9, 1), (20, 1), (52, 1)] }, { coefficient := 1, powers := [(9, 1), (25, 1), (42, 1)] }, { coefficient := 1, powers := [(9, 1), (33, 1), (36, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1), (47, 1)] }, { coefficient := 1, powers := [(14, 1), (25, 1), (39, 1)] }, { coefficient := 1, powers := [(14, 1), (30, 1), (36, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1), (37, 1), (56, 1)] }, { coefficient := 1, powers := [(1, 1), (40, 1), (53, 1)] }, { coefficient := 1, powers := [(1, 1), (44, 1), (49, 1)] }, { coefficient := 1, powers := [(4, 1), (28, 1), (56, 1)] }, { coefficient := 1, powers := [(4, 1), (31, 1), (53, 1)] }, { coefficient := 1, powers := [(4, 1), (34, 1), (49, 1)] }, { coefficient := 1, powers := [(7, 1), (23, 1), (56, 1)] }, { coefficient := 1, powers := [(7, 1), (31, 1), (44, 1)] }, { coefficient := 1, powers := [(7, 1), (34, 1), (40, 1)] }, { coefficient := 1, powers := [(10, 1), (23, 1), (53, 1)] }, { coefficient := 1, powers := [(10, 1), (28, 1), (44, 1)] }, { coefficient := 1, powers := [(10, 1), (34, 1), (37, 1)] }, { coefficient := 1, powers := [(15, 1), (23, 1), (49, 1)] }, { coefficient := 1, powers := [(15, 1), (28, 1), (40, 1)] }, { coefficient := 1, powers := [(15, 1), (31, 1), (37, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (41, 1), (54, 1)] }, { coefficient := 1, powers := [(2, 1), (46, 1), (51, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (51, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (57, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (46, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(13, 1), (24, 1), (54, 1)] }, { coefficient := 1, powers := [(13, 1), (29, 1), (46, 1)] }, { coefficient := 1, powers := [(13, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (51, 1)] }, { coefficient := 1, powers := [(19, 1), (29, 1), (41, 1)] }, { coefficient := 1, powers := [(19, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1)] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(39, 1)] }],
  [{ coefficient := 1, powers := [(40, 1), (59, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(41, 1)] }],
  [{ coefficient := 1, powers := [(52, 1)] }],
  [{ coefficient := 1, powers := [(53, 1)] }],
  [{ coefficient := 1, powers := [(54, 1), (60, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 64 → SparsePoly (Fin 61) := ![
  [{ coefficient := 1, powers := [(0, 1), (32, 1), (36, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (36, 1), (45, 1), (51, 1), (55, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (33, 1), (45, 1), (47, 1), (51, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (14, 1), (30, 1), (31, 1), (36, 1), (44, 1), (45, 1), (51, 1), (59, 1)] }, { coefficient := -1, powers := [(30, 1), (36, 1), (42, 1), (45, 1), (51, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (36, 1), (46, 1), (50, 1), (55, 1), (59, 1)] }, { coefficient := -1, powers := [(3, 1), (33, 1), (46, 1), (47, 1), (50, 1), (59, 1)] }, { coefficient := 1, powers := [(30, 1), (36, 1), (42, 1), (46, 1), (50, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (14, 1), (30, 1), (36, 1), (49, 1), (56, 1), (59, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (14, 1), (30, 1), (36, 1), (56, 1), (60, 1)] }, { coefficient := 1, powers := [(10, 1), (14, 1), (30, 1), (36, 1), (44, 1), (49, 1), (59, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (33, 1), (47, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (32, 1), (36, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (28, 1), (36, 1), (56, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (33, 1), (47, 1), (51, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (33, 1), (47, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (33, 1), (38, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (34, 1), (36, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (29, 1), (36, 1), (46, 1), (50, 1), (55, 1)] }, { coefficient := 1, powers := [(3, 1), (29, 1), (33, 1), (46, 1), (47, 1), (50, 1)] }, { coefficient := 1, powers := [(7, 1), (14, 1), (29, 1), (30, 1), (31, 1), (36, 1), (44, 1), (46, 1), (50, 1)] }, { coefficient := -1, powers := [(29, 1), (30, 1), (36, 1), (42, 1), (46, 1), (50, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (29, 1), (36, 1), (48, 1), (55, 1)] }, { coefficient := -1, powers := [(3, 1), (29, 1), (33, 1), (47, 1), (48, 1)] }, { coefficient := -1, powers := [(7, 1), (14, 1), (29, 1), (30, 1), (31, 1), (36, 1), (44, 1), (48, 1)] }, { coefficient := 1, powers := [(29, 1), (30, 1), (36, 1), (42, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (55, 1), (60, 1)] }, { coefficient := 1, powers := [(14, 1), (47, 1), (60, 1)] }, { coefficient := -1, powers := [(42, 1), (47, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (6, 1), (18, 1), (29, 1), (36, 1), (55, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (19, 1), (29, 1), (36, 1), (48, 1), (55, 1)] }, { coefficient := -1, powers := [(3, 1), (6, 1), (18, 1), (29, 1), (33, 1), (47, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (19, 1), (29, 1), (33, 1), (47, 1), (48, 1)] }, { coefficient := 1, powers := [(6, 1), (18, 1), (29, 1), (30, 1), (36, 1), (42, 1), (57, 1)] }, { coefficient := 1, powers := [(7, 1), (14, 1), (18, 1), (27, 1), (30, 1), (35, 1), (36, 1), (44, 1), (51, 1)] }, { coefficient := 1, powers := [(7, 1), (14, 1), (19, 1), (29, 1), (30, 1), (31, 1), (36, 1), (44, 1), (48, 1)] }, { coefficient := -1, powers := [(19, 1), (29, 1), (30, 1), (36, 1), (42, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (32, 1), (36, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (19, 1), (36, 1), (51, 1), (55, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (19, 1), (33, 1), (47, 1), (51, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (14, 1), (19, 1), (30, 1), (31, 1), (36, 1), (44, 1), (51, 1), (59, 1)] }, { coefficient := -1, powers := [(19, 1), (30, 1), (36, 1), (42, 1), (51, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (14, 1), (18, 1), (22, 1), (24, 1), (30, 1), (36, 1), (44, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (13, 1), (36, 1), (46, 1), (55, 1), (59, 1)] }, { coefficient := -1, powers := [(3, 1), (13, 1), (33, 1), (46, 1), (47, 1), (59, 1)] }, { coefficient := 1, powers := [(13, 1), (30, 1), (36, 1), (42, 1), (46, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (14, 1), (19, 1), (30, 1), (32, 1), (36, 1), (44, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (43, 1), (55, 1), (60, 1)] }, { coefficient := -1, powers := [(14, 1), (43, 1), (47, 1), (60, 1)] }, { coefficient := 1, powers := [(42, 1), (43, 1), (47, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (14, 1), (30, 1), (35, 1), (36, 1), (44, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (8, 1), (36, 1), (55, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (8, 1), (33, 1), (47, 1), (57, 1)] }, { coefficient := -1, powers := [(8, 1), (30, 1), (36, 1), (42, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (14, 1), (24, 1), (30, 1), (36, 1), (44, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (29, 1), (36, 1), (46, 1), (55, 1)] }, { coefficient := 1, powers := [(3, 1), (29, 1), (33, 1), (46, 1), (47, 1)] }, { coefficient := 1, powers := [(7, 1), (14, 1), (29, 1), (30, 1), (31, 1), (36, 1), (44, 1), (46, 1)] }, { coefficient := -1, powers := [(29, 1), (30, 1), (36, 1), (42, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (36, 1), (40, 1), (51, 1), (55, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (33, 1), (40, 1), (47, 1), (51, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (33, 1), (47, 1), (51, 1)] }, { coefficient := 1, powers := [(7, 1), (14, 1), (30, 1), (31, 1), (36, 1), (40, 1), (44, 1), (51, 1), (59, 1)] }, { coefficient := -1, powers := [(7, 1), (14, 1), (30, 1), (34, 1), (36, 1), (44, 1), (51, 1)] }, { coefficient := -1, powers := [(30, 1), (36, 1), (40, 1), (42, 1), (51, 1), (59, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1), (47, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (36, 1), (40, 1), (46, 1), (55, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (33, 1), (40, 1), (46, 1), (47, 1), (59, 1)] }, { coefficient := -1, powers := [(30, 1), (36, 1), (40, 1), (42, 1), (46, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(25, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (6, 1), (29, 1), (36, 1), (55, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (6, 1), (29, 1), (33, 1), (47, 1), (57, 1)] }, { coefficient := -1, powers := [(6, 1), (29, 1), (30, 1), (36, 1), (42, 1), (57, 1)] }, { coefficient := -1, powers := [(7, 1), (14, 1), (27, 1), (30, 1), (35, 1), (36, 1), (44, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(32, 1), (36, 1), (42, 1), (46, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (14, 1), (22, 1), (24, 1), (30, 1), (36, 1), (44, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (25, 1), (29, 1), (36, 1), (46, 1), (55, 1)] }, { coefficient := 1, powers := [(0, 1), (29, 1), (36, 1), (46, 1), (55, 1), (59, 1)] }, { coefficient := -1, powers := [(3, 1), (25, 1), (29, 1), (33, 1), (46, 1), (47, 1)] }, { coefficient := 1, powers := [(3, 1), (29, 1), (33, 1), (46, 1), (47, 1), (59, 1)] }, { coefficient := -1, powers := [(7, 1), (14, 1), (25, 1), (29, 1), (30, 1), (31, 1), (36, 1), (44, 1), (46, 1)] }, { coefficient := 1, powers := [(25, 1), (29, 1), (30, 1), (36, 1), (42, 1), (46, 1)] }, { coefficient := -1, powers := [(29, 1), (30, 1), (36, 1), (42, 1), (46, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (30, 1), (36, 1), (49, 1), (56, 1), (59, 1)] }, { coefficient := -1, powers := [(10, 1), (30, 1), (36, 1), (44, 1), (49, 1), (59, 1)] }, { coefficient := -1, powers := [(15, 1), (30, 1), (36, 1), (49, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (24, 1), (36, 1), (51, 1), (55, 1), (59, 1)] }, { coefficient := -1, powers := [(3, 1), (24, 1), (33, 1), (47, 1), (51, 1), (59, 1)] }, { coefficient := -1, powers := [(7, 1), (14, 1), (24, 1), (30, 1), (31, 1), (36, 1), (44, 1), (51, 1), (59, 1)] }, { coefficient := 1, powers := [(24, 1), (30, 1), (36, 1), (42, 1), (51, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (19, 1), (36, 1), (55, 1)] }, { coefficient := 1, powers := [(3, 1), (19, 1), (33, 1), (47, 1)] }, { coefficient := -1, powers := [(6, 1), (19, 1), (33, 1), (47, 1)] }, { coefficient := 1, powers := [(7, 1), (14, 1), (19, 1), (30, 1), (31, 1), (36, 1), (44, 1)] }, { coefficient := 1, powers := [(7, 1), (14, 1), (19, 1), (30, 1), (34, 1), (36, 1), (44, 1)] }, { coefficient := -1, powers := [(19, 1), (30, 1), (36, 1), (42, 1)] }, { coefficient := -1, powers := [(19, 1), (33, 1), (36, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (13, 1), (36, 1), (55, 1)] }, { coefficient := 1, powers := [(3, 1), (13, 1), (33, 1), (47, 1)] }, { coefficient := 1, powers := [(7, 1), (13, 1), (14, 1), (30, 1), (31, 1), (36, 1), (44, 1)] }, { coefficient := -1, powers := [(13, 1), (30, 1), (36, 1), (42, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (26, 1), (55, 1), (60, 1)] }, { coefficient := -1, powers := [(14, 1), (26, 1), (47, 1), (60, 1)] }, { coefficient := 1, powers := [(26, 1), (42, 1), (47, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (6, 1), (36, 1), (55, 1), (57, 1)] }, { coefficient := -1, powers := [(3, 1), (6, 1), (33, 1), (47, 1), (57, 1)] }, { coefficient := 1, powers := [(6, 1), (30, 1), (36, 1), (42, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (14, 1), (30, 1), (32, 1), (36, 1), (44, 1)] }],
  [{ coefficient := -1, powers := [(26, 1), (32, 1), (36, 1), (42, 1), (46, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (29, 1), (36, 1), (46, 1), (55, 1)] }, { coefficient := -1, powers := [(3, 1), (29, 1), (33, 1), (46, 1), (47, 1)] }, { coefficient := -1, powers := [(7, 1), (14, 1), (29, 1), (30, 1), (31, 1), (36, 1), (44, 1), (46, 1)] }, { coefficient := 1, powers := [(29, 1), (30, 1), (36, 1), (42, 1), (46, 1)] }],
  [{ coefficient := -1, powers := [(10, 1), (30, 1), (36, 1)] }, { coefficient := 1, powers := [(15, 1), (30, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (29, 1), (33, 1), (43, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (29, 1), (36, 1), (55, 1)] }, { coefficient := 1, powers := [(3, 1), (29, 1), (33, 1), (47, 1)] }, { coefficient := 1, powers := [(7, 1), (14, 1), (29, 1), (30, 1), (31, 1), (36, 1), (44, 1)] }, { coefficient := -1, powers := [(29, 1), (30, 1), (36, 1), (42, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (19, 1), (29, 1), (36, 1), (55, 1)] }, { coefficient := -1, powers := [(3, 1), (19, 1), (29, 1), (33, 1), (47, 1)] }, { coefficient := -1, powers := [(7, 1), (14, 1), (19, 1), (29, 1), (30, 1), (31, 1), (36, 1), (44, 1)] }, { coefficient := 1, powers := [(19, 1), (29, 1), (30, 1), (36, 1), (42, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (29, 1), (33, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (33, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (26, 1), (43, 1), (55, 1), (60, 1)] }, { coefficient := 1, powers := [(14, 1), (26, 1), (43, 1), (47, 1), (60, 1)] }, { coefficient := -1, powers := [(26, 1), (42, 1), (43, 1), (47, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(25, 1), (42, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1)] }],
  [{ coefficient := -1, powers := [(32, 1), (36, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(42, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (30, 1), (36, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (14, 1), (30, 1), (36, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(14, 1), (30, 1), (36, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (36, 1), (55, 1)] }, { coefficient := -1, powers := [(3, 1), (33, 1), (47, 1)] }, { coefficient := -1, powers := [(7, 1), (14, 1), (30, 1), (31, 1), (36, 1), (44, 1)] }, { coefficient := 1, powers := [(30, 1), (36, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (30, 1), (36, 1), (37, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (6, 1), (36, 1), (38, 1), (55, 1), (56, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (36, 1), (38, 1), (55, 1), (57, 1)] }, { coefficient := -2, powers := [(0, 1), (36, 1), (40, 1), (46, 1), (51, 1), (55, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (36, 1), (46, 1), (51, 1), (55, 1)] }, { coefficient := 1, powers := [(3, 1), (6, 1), (33, 1), (38, 1), (47, 1), (56, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (33, 1), (38, 1), (47, 1), (57, 1)] }, { coefficient := -2, powers := [(3, 1), (33, 1), (40, 1), (46, 1), (47, 1), (51, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (33, 1), (46, 1), (47, 1), (51, 1)] }, { coefficient := -1, powers := [(6, 1), (30, 1), (36, 1), (38, 1), (42, 1), (56, 1), (57, 1)] }, { coefficient := -1, powers := [(6, 1), (33, 1), (46, 1), (47, 1), (51, 1)] }, { coefficient := 1, powers := [(7, 1), (14, 1), (30, 1), (31, 1), (36, 1), (38, 1), (44, 1), (57, 1)] }, { coefficient := -1, powers := [(7, 1), (14, 1), (30, 1), (31, 1), (36, 1), (40, 1), (44, 1), (46, 1), (51, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (14, 1), (30, 1), (31, 1), (36, 1), (44, 1), (46, 1), (51, 1)] }, { coefficient := 1, powers := [(7, 1), (14, 1), (30, 1), (34, 1), (36, 1), (44, 1), (46, 1), (51, 1)] }, { coefficient := -1, powers := [(30, 1), (36, 1), (38, 1), (42, 1), (57, 1)] }, { coefficient := 2, powers := [(30, 1), (36, 1), (40, 1), (42, 1), (46, 1), (51, 1), (59, 1)] }, { coefficient := -1, powers := [(30, 1), (36, 1), (42, 1), (46, 1), (51, 1)] }, { coefficient := -1, powers := [(33, 1), (36, 1), (46, 1), (47, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (33, 1)] }, { coefficient := -1, powers := [(14, 1), (15, 1), (34, 1), (36, 1), (40, 1)] }, { coefficient := -1, powers := [(33, 1), (36, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (5, 1), (35, 1), (36, 1), (51, 1), (55, 1)] }, { coefficient := -1, powers := [(0, 1), (8, 1), (32, 1), (36, 1), (46, 1), (55, 1)] }, { coefficient := -1, powers := [(3, 1), (5, 1), (33, 1), (35, 1), (47, 1), (51, 1)] }, { coefficient := -1, powers := [(3, 1), (8, 1), (32, 1), (33, 1), (46, 1), (47, 1)] }, { coefficient := 1, powers := [(4, 1), (14, 1), (27, 1), (30, 1), (36, 1), (49, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (6, 1), (33, 1), (35, 1), (47, 1), (51, 1)] }, { coefficient := -1, powers := [(5, 1), (7, 1), (14, 1), (30, 1), (31, 1), (35, 1), (36, 1), (44, 1), (51, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (35, 1), (36, 1), (42, 1), (51, 1)] }, { coefficient := 1, powers := [(8, 1), (30, 1), (32, 1), (36, 1), (42, 1), (46, 1)] }, { coefficient := 1, powers := [(10, 1), (14, 1), (27, 1), (30, 1), (36, 1), (44, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (2, 1), (36, 1), (54, 1), (55, 1)] }, { coefficient := 1, powers := [(0, 1), (8, 1), (35, 1), (36, 1), (55, 1)] }, { coefficient := 1, powers := [(2, 1), (3, 1), (33, 1), (47, 1), (54, 1)] }, { coefficient := 1, powers := [(2, 1), (7, 1), (14, 1), (30, 1), (31, 1), (36, 1), (44, 1), (54, 1)] }, { coefficient := -1, powers := [(2, 1), (30, 1), (36, 1), (42, 1), (54, 1)] }, { coefficient := 1, powers := [(3, 1), (8, 1), (33, 1), (35, 1), (47, 1)] }, { coefficient := 1, powers := [(6, 1), (19, 1), (29, 1), (33, 1), (47, 1)] }, { coefficient := 1, powers := [(7, 1), (8, 1), (14, 1), (30, 1), (31, 1), (35, 1), (36, 1), (44, 1)] }, { coefficient := -1, powers := [(7, 1), (14, 1), (19, 1), (29, 1), (30, 1), (34, 1), (36, 1), (44, 1)] }, { coefficient := -1, powers := [(8, 1), (30, 1), (35, 1), (36, 1), (42, 1)] }, { coefficient := 1, powers := [(19, 1), (29, 1), (33, 1), (36, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (39, 1)] }, { coefficient := 1, powers := [(3, 1), (30, 1)] }, { coefficient := 1, powers := [(4, 1), (23, 1), (30, 1), (36, 1), (49, 1), (56, 1), (59, 1)] }, { coefficient := 1, powers := [(9, 1), (20, 1)] }, { coefficient := 1, powers := [(10, 1), (23, 1), (30, 1), (36, 1), (44, 1), (49, 1), (59, 1)] }, { coefficient := 1, powers := [(15, 1), (23, 1), (30, 1), (36, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(0, 2), (19, 1), (29, 1), (36, 1), (41, 1), (55, 1)] }, { coefficient := 1, powers := [(0, 1), (3, 1), (19, 1), (29, 1), (33, 1), (41, 1), (47, 1)] }, { coefficient := 1, powers := [(0, 1), (7, 1), (14, 1), (19, 1), (29, 1), (30, 1), (31, 1), (36, 1), (41, 1), (44, 1)] }, { coefficient := 1, powers := [(0, 1), (13, 1), (20, 1), (29, 1), (36, 1), (46, 1), (55, 1)] }, { coefficient := 1, powers := [(0, 1), (13, 1), (25, 1), (29, 1), (36, 1), (46, 1), (55, 1)] }, { coefficient := -1, powers := [(0, 1), (13, 1), (29, 1), (36, 1), (46, 1), (55, 1), (59, 1)] }, { coefficient := -1, powers := [(0, 1), (19, 1), (24, 1), (36, 1), (51, 1), (55, 1), (59, 1)] }, { coefficient := -1, powers := [(0, 1), (19, 1), (29, 1), (30, 1), (36, 1), (41, 1), (42, 1)] }, { coefficient := 1, powers := [(0, 1), (25, 1), (39, 1), (42, 1)] }, { coefficient := -1, powers := [(0, 1), (33, 1), (36, 1), (39, 1)] }, { coefficient := 1, powers := [(1, 1), (14, 1), (30, 1), (36, 1), (40, 1)] }, { coefficient := 1, powers := [(3, 1), (13, 1), (20, 1), (29, 1), (33, 1), (46, 1), (47, 1)] }, { coefficient := 1, powers := [(3, 1), (13, 1), (25, 1), (29, 1), (33, 1), (46, 1), (47, 1)] }, { coefficient := -1, powers := [(3, 1), (13, 1), (29, 1), (33, 1), (46, 1), (47, 1), (59, 1)] }, { coefficient := -1, powers := [(3, 1), (19, 1), (24, 1), (33, 1), (47, 1), (51, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (25, 1), (30, 1), (42, 1)] }, { coefficient := -1, powers := [(3, 1), (30, 1), (33, 1), (36, 1)] }, { coefficient := 1, powers := [(4, 1), (14, 1), (30, 1), (31, 1), (36, 1)] }, { coefficient := -1, powers := [(5, 1), (20, 1), (29, 1), (33, 1), (43, 1), (47, 1), (48, 1)] }, { coefficient := -1, powers := [(6, 1), (20, 1), (26, 1), (43, 1), (55, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (13, 1), (14, 1), (20, 1), (29, 1), (30, 1), (31, 1), (36, 1), (44, 1), (46, 1)] }, { coefficient := 1, powers := [(7, 1), (13, 1), (14, 1), (25, 1), (29, 1), (30, 1), (31, 1), (36, 1), (44, 1), (46, 1)] }, { coefficient := -1, powers := [(7, 1), (14, 1), (19, 1), (24, 1), (30, 1), (31, 1), (36, 1), (44, 1), (51, 1), (59, 1)] }, { coefficient := 1, powers := [(9, 1), (20, 1), (25, 1), (42, 1)] }, { coefficient := -1, powers := [(9, 1), (20, 1), (33, 1), (36, 1)] }, { coefficient := 1, powers := [(12, 1), (20, 1), (26, 1), (32, 1), (36, 1), (42, 1), (46, 1)] }, { coefficient := -1, powers := [(13, 1), (20, 1), (29, 1), (30, 1), (36, 1), (42, 1), (46, 1)] }, { coefficient := -1, powers := [(13, 1), (25, 1), (29, 1), (30, 1), (36, 1), (42, 1), (46, 1)] }, { coefficient := 1, powers := [(13, 1), (29, 1), (30, 1), (36, 1), (42, 1), (46, 1), (59, 1)] }, { coefficient := -1, powers := [(14, 1), (20, 1), (26, 1), (43, 1), (47, 1), (60, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (30, 1), (36, 1), (42, 1), (51, 1), (59, 1)] }, { coefficient := 1, powers := [(20, 1), (26, 1), (42, 1), (43, 1), (47, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (14, 1), (23, 1), (30, 1), (36, 1), (49, 1), (56, 1), (59, 1)] }, { coefficient := -1, powers := [(4, 1), (14, 1), (28, 1), (30, 1), (36, 1), (56, 1)] }, { coefficient := -1, powers := [(6, 1), (20, 1), (55, 1)] }, { coefficient := -1, powers := [(7, 1), (14, 1), (23, 1), (30, 1), (36, 1), (56, 1)] }, { coefficient := -1, powers := [(10, 1), (14, 1), (23, 1), (30, 1), (36, 1), (44, 1), (49, 1), (59, 1)] }, { coefficient := -1, powers := [(14, 1), (20, 1), (47, 1)] }, { coefficient := 1, powers := [(20, 1), (42, 1), (47, 1)] }]
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
    (values : Fin 61 → R) :
    ¬ ∀ index : Fin 64,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component55.SelectedLeafB4_2_1.selectedHasNoCommonZero

end Krenn.Component55.SelectedLeafB4_2_1
