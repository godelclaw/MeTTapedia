import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component58.SelectedLeafB6_3_7

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "18ea1c61904b4ce4daa4de96fec9dd3f83c70abffa32121c0a4399b46f92c764"
def certificateSHA256 : String := "058b287c30d7dcb9336ee3adad7537a6b4f0ecdf31b5dc51f6920a632f5db8a0"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 45 → Fin 622 := ![
  10,
  11,
  13,
  14,
  20,
  30,
  31,
  34,
  37,
  39,
  192,
  200,
  216,
  227,
  230,
  241,
  253,
  306,
  333,
  335,
  336,
  342,
  353,
  355,
  382,
  424,
  474,
  477,
  480,
  481,
  488,
  532,
  561,
  570,
  576,
  577,
  610,
  612,
  613,
  614,
  615,
  616,
  618,
  619,
  621
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 45 → SparsePoly (Fin 66) := ![
  [{ coefficient := 1, powers := [(8, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(28, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(28, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (52, 1)] }, { coefficient := 1, powers := [(20, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (31, 1)] }, { coefficient := 1, powers := [(31, 1), (35, 1)] }],
  [{ coefficient := 1, powers := [(15, 1), (21, 1)] }, { coefficient := 1, powers := [(21, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (39, 1), (55, 1)] }, { coefficient := 1, powers := [(55, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (38, 1), (55, 1)] }, { coefficient := 1, powers := [(10, 1), (22, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (28, 1), (57, 1)] }, { coefficient := 1, powers := [(28, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (24, 1), (57, 1)] }, { coefficient := 1, powers := [(24, 1)] }],
  [{ coefficient := 1, powers := [(15, 1), (21, 1), (51, 1)] }, { coefficient := 1, powers := [(15, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1)] }, { coefficient := 1, powers := [(20, 1), (42, 1)] }, { coefficient := 1, powers := [(25, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (48, 1)] }, { coefficient := 1, powers := [(20, 1), (48, 1)] }, { coefficient := 1, powers := [(25, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (41, 1)] }, { coefficient := 1, powers := [(11, 1), (22, 1), (53, 1)] }, { coefficient := 1, powers := [(11, 1), (26, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (58, 1)] }, { coefficient := 1, powers := [(14, 1), (55, 1)] }, { coefficient := 1, powers := [(19, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (55, 1)] }, { coefficient := 1, powers := [(28, 1), (46, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (38, 1), (55, 1)] }, { coefficient := 1, powers := [(3, 1), (29, 1), (55, 1)] }, { coefficient := 1, powers := [(9, 1), (20, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (40, 1), (53, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (53, 1)] }, { coefficient := 1, powers := [(14, 1), (24, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (20, 1), (53, 1)] }, { coefficient := 1, powers := [(10, 1), (25, 1), (41, 1)] }, { coefficient := 1, powers := [(10, 1), (32, 1), (35, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (52, 1)] }, { coefficient := 1, powers := [(28, 1), (40, 1)] }, { coefficient := 1, powers := [(28, 1), (45, 1), (48, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (41, 1), (50, 1)] }, { coefficient := 1, powers := [(3, 1), (32, 1), (50, 1)] }, { coefficient := 1, powers := [(15, 1), (20, 1), (50, 1)] }, { coefficient := 1, powers := [(41, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1), (51, 1)] }, { coefficient := 1, powers := [(3, 1), (58, 1)] }, { coefficient := 1, powers := [(20, 1), (42, 1), (51, 1)] }, { coefficient := 1, powers := [(42, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1), (47, 1)] }, { coefficient := 1, powers := [(6, 1), (29, 1), (43, 1)] }, { coefficient := 1, powers := [(9, 1), (25, 1), (43, 1)] }, { coefficient := 1, powers := [(47, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1), (48, 1)] }, { coefficient := 1, powers := [(21, 1), (48, 1)] }, { coefficient := 1, powers := [(25, 1), (40, 1)] }, { coefficient := 1, powers := [(25, 1), (45, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (24, 1), (58, 1)] }, { coefficient := 1, powers := [(6, 1), (31, 1), (46, 1)] }, { coefficient := 1, powers := [(6, 1), (34, 1), (40, 1)] }, { coefficient := 1, powers := [(24, 1), (42, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1)] }, { coefficient := 1, powers := [(6, 1), (57, 1)] }, { coefficient := 1, powers := [(25, 1), (39, 1)] }, { coefficient := 1, powers := [(25, 1), (43, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1), (35, 1), (56, 1)] }, { coefficient := 1, powers := [(1, 1), (38, 1), (53, 1)] }, { coefficient := 1, powers := [(1, 1), (41, 1), (47, 1)] }, { coefficient := 1, powers := [(10, 1), (22, 1), (53, 1)] }, { coefficient := 1, powers := [(10, 1), (26, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (41, 1)] }, { coefficient := 1, powers := [(3, 1), (32, 1)] }, { coefficient := 1, powers := [(15, 1), (20, 1)] }, { coefficient := 1, powers := [(20, 1), (53, 1)] }, { coefficient := 1, powers := [(25, 1), (41, 1)] }, { coefficient := 1, powers := [(32, 1), (35, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1)] }, { coefficient := 1, powers := [(6, 1), (29, 1)] }, { coefficient := 1, powers := [(9, 1), (25, 1)] }, { coefficient := 1, powers := [(20, 1), (47, 1)] }, { coefficient := 1, powers := [(25, 1), (38, 1)] }, { coefficient := 1, powers := [(29, 1), (35, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (35, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (38, 1), (53, 1)] }, { coefficient := 1, powers := [(0, 1), (41, 1), (47, 1)] }, { coefficient := 1, powers := [(3, 1), (25, 1), (56, 1)] }, { coefficient := 1, powers := [(3, 1), (29, 1), (53, 1)] }, { coefficient := 1, powers := [(3, 1), (32, 1), (47, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1), (56, 1)] }, { coefficient := 1, powers := [(6, 1), (29, 1), (41, 1)] }, { coefficient := 1, powers := [(6, 1), (32, 1), (38, 1)] }, { coefficient := 1, powers := [(9, 1), (20, 1), (53, 1)] }, { coefficient := 1, powers := [(9, 1), (25, 1), (41, 1)] }, { coefficient := 1, powers := [(9, 1), (32, 1), (35, 1)] }, { coefficient := 1, powers := [(15, 1), (20, 1), (47, 1)] }, { coefficient := 1, powers := [(15, 1), (25, 1), (38, 1)] }, { coefficient := 1, powers := [(15, 1), (29, 1), (35, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (37, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (40, 1), (55, 1)] }, { coefficient := 1, powers := [(2, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(5, 1), (28, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (52, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (58, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1), (46, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (40, 1)] }, { coefficient := 1, powers := [(14, 1), (24, 1), (55, 1)] }, { coefficient := 1, powers := [(14, 1), (28, 1), (46, 1)] }, { coefficient := 1, powers := [(14, 1), (34, 1), (37, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (52, 1)] }, { coefficient := 1, powers := [(19, 1), (28, 1), (40, 1)] }, { coefficient := 1, powers := [(19, 1), (31, 1), (37, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (59, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1), (60, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(38, 1)] }],
  [{ coefficient := 1, powers := [(40, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(53, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(55, 1), (65, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 45 → SparsePoly (Fin 66) := ![
  [{ coefficient := -1, powers := [(6, 2), (24, 1), (29, 1), (35, 1), (41, 1), (57, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(32, 1), (35, 1), (65, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (26, 1), (47, 1), (60, 1)] }, { coefficient := -1, powers := [(25, 1), (26, 1), (29, 1), (35, 1), (43, 1), (60, 1)] }, { coefficient := 1, powers := [(25, 1), (26, 1), (47, 1), (60, 1)] }, { coefficient := 2, powers := [(26, 1), (29, 1), (35, 1), (60, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (22, 1), (47, 1), (53, 1), (60, 1), (65, 1)] }, { coefficient := -1, powers := [(22, 1), (25, 1), (29, 1), (35, 1), (43, 1), (53, 1), (60, 1), (65, 1)] }, { coefficient := 1, powers := [(22, 1), (25, 1), (47, 1), (53, 1), (60, 1), (65, 1)] }, { coefficient := 2, powers := [(22, 1), (29, 1), (35, 1), (53, 1), (60, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (24, 1), (29, 1), (35, 1), (41, 1), (55, 1), (57, 1), (63, 1)] }, { coefficient := -1, powers := [(24, 1), (29, 1), (35, 2), (41, 1), (55, 1), (57, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (45, 1), (48, 1), (56, 1), (62, 1), (65, 1)] }, { coefficient := 1, powers := [(5, 1), (6, 1), (29, 1), (34, 1), (35, 1), (41, 1), (52, 1), (57, 1), (59, 1), (65, 1)] }, { coefficient := -1, powers := [(6, 1), (19, 1), (24, 1), (29, 1), (35, 1), (41, 1), (52, 1), (57, 1), (59, 1), (65, 1)] }, { coefficient := 1, powers := [(6, 1), (56, 1), (65, 1)] }, { coefficient := -1, powers := [(9, 1), (32, 1), (35, 1), (43, 1), (65, 1)] }, { coefficient := 1, powers := [(15, 1), (29, 1), (35, 1), (43, 1), (65, 1)] }, { coefficient := -1, powers := [(29, 1), (35, 1), (41, 1), (43, 1), (45, 1), (48, 1), (62, 1), (65, 1)] }, { coefficient := 1, powers := [(29, 1), (35, 1), (41, 1), (45, 1), (48, 1), (59, 1), (62, 1), (65, 1)] }, { coefficient := 1, powers := [(29, 1), (35, 1), (43, 1), (53, 1), (65, 1)] }, { coefficient := -1, powers := [(32, 1), (35, 1), (43, 1), (47, 1), (65, 1)] }, { coefficient := -1, powers := [(41, 1), (47, 1), (65, 1)] }, { coefficient := -1, powers := [(47, 1), (53, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (48, 1), (56, 1), (62, 1), (65, 1)] }, { coefficient := 1, powers := [(29, 1), (35, 1), (41, 1), (43, 1), (48, 1), (62, 1), (65, 1)] }, { coefficient := -1, powers := [(29, 1), (35, 1), (41, 1), (48, 1), (59, 1), (62, 1), (65, 1)] }, { coefficient := 1, powers := [(29, 1), (35, 1), (51, 1), (53, 1), (62, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (29, 1), (35, 1), (41, 1), (48, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (6, 1), (25, 1), (29, 1), (35, 1), (41, 1), (51, 1), (57, 2)] }],
  [{ coefficient := -1, powers := [(5, 1), (6, 1), (29, 1), (35, 1), (41, 1), (42, 1), (57, 2)] }, { coefficient := 1, powers := [(6, 1), (19, 1), (29, 1), (35, 1), (41, 1), (45, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (6, 1), (29, 1), (34, 1), (35, 1), (41, 1), (57, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (19, 1), (24, 1), (29, 1), (35, 1), (41, 1), (57, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (29, 1), (35, 1), (41, 1), (55, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [(29, 1), (35, 1), (51, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(25, 1), (29, 1), (35, 1), (41, 1), (59, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (53, 1), (60, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (6, 1), (29, 1), (35, 1), (41, 1), (57, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (8, 1), (29, 1), (35, 1), (41, 1), (57, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (35, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (6, 1), (28, 1), (29, 1), (35, 1), (41, 1), (51, 1), (57, 2)] }],
  [{ coefficient := -1, powers := [(3, 1), (45, 1), (56, 1), (62, 1)] }, { coefficient := 1, powers := [(29, 1), (35, 1), (41, 1), (43, 1), (45, 1), (62, 1)] }, { coefficient := -1, powers := [(29, 1), (35, 1), (41, 1), (45, 1), (59, 1), (62, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (47, 1), (60, 1)] }, { coefficient := 1, powers := [(25, 1), (29, 1), (35, 1), (43, 1), (60, 1)] }, { coefficient := -1, powers := [(25, 1), (47, 1), (60, 1)] }, { coefficient := -2, powers := [(29, 1), (35, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (24, 1), (29, 1), (35, 1), (41, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (14, 1), (29, 1), (35, 1), (41, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(32, 1), (35, 1), (43, 1), (65, 1)] }, { coefficient := 1, powers := [(53, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (35, 2), (41, 1), (55, 1), (57, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (26, 1), (50, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (19, 1), (29, 1), (35, 1), (41, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (10, 1), (26, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (6, 1), (28, 1), (29, 1), (35, 1), (41, 1), (57, 2)] }],
  [{ coefficient := -1, powers := [(32, 1), (35, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (56, 1), (62, 1)] }, { coefficient := -1, powers := [(29, 1), (35, 1), (41, 1), (43, 1), (62, 1)] }, { coefficient := 1, powers := [(29, 1), (35, 1), (41, 1), (59, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (29, 1), (35, 1), (41, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (35, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (10, 1), (26, 1), (50, 1), (60, 1)] }, { coefficient := -1, powers := [(29, 1), (35, 1), (43, 1)] }, { coefficient := 1, powers := [(47, 1)] }],
  [{ coefficient := 1, powers := [(32, 1), (35, 1), (43, 1)] }, { coefficient := 1, powers := [(41, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(6, 1), (29, 1), (35, 1), (41, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (6, 1), (29, 1), (34, 1), (35, 1), (41, 1), (52, 1), (57, 1)] }, { coefficient := -1, powers := [(6, 1), (19, 1), (24, 1), (29, 1), (35, 1), (41, 1), (52, 1), (57, 1)] }, { coefficient := 1, powers := [(25, 1), (29, 1), (35, 1), (39, 1), (41, 1), (55, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (35, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (41, 1), (47, 1)] }, { coefficient := -1, powers := [(25, 1), (29, 1), (35, 1), (41, 1), (43, 1)] }, { coefficient := 1, powers := [(25, 1), (41, 1), (47, 1)] }, { coefficient := 2, powers := [(29, 1), (35, 1), (41, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (29, 1), (35, 1), (37, 1), (41, 1), (57, 1), (58, 1)] }, { coefficient := -1, powers := [(6, 1), (29, 1), (35, 1), (40, 1), (41, 1), (55, 1), (57, 1)] }, { coefficient := -1, powers := [(6, 1), (29, 1), (35, 1), (41, 1), (46, 1), (52, 1), (57, 1)] }, { coefficient := -1, powers := [(29, 1), (35, 2), (40, 1), (41, 1), (53, 1), (55, 1), (57, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (1, 1), (53, 1), (55, 1), (60, 1), (65, 1)] }, { coefficient := -1, powers := [(0, 1), (1, 1), (53, 1), (60, 1)] }, { coefficient := -1, powers := [(0, 1), (32, 1), (35, 1), (43, 1), (55, 1), (65, 1)] }, { coefficient := -1, powers := [(0, 1), (53, 1), (55, 1), (65, 1)] }, { coefficient := 1, powers := [(0, 1), (53, 1)] }, { coefficient := 1, powers := [(6, 1), (32, 1)] }, { coefficient := 1, powers := [(15, 1), (25, 1)] }, { coefficient := -1, powers := [(25, 1), (32, 1), (35, 1), (43, 1)] }, { coefficient := -1, powers := [(25, 1), (41, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (25, 1), (56, 1)] }, { coefficient := -1, powers := [(15, 1), (29, 1), (35, 1)] }, { coefficient := 1, powers := [(25, 1), (29, 1), (35, 1), (41, 1), (43, 1)] }, { coefficient := -1, powers := [(25, 1), (29, 1), (35, 1), (41, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (29, 1), (31, 1), (35, 2), (41, 1), (55, 1), (57, 1)] }, { coefficient := -1, powers := [(6, 1), (14, 1), (24, 1), (29, 1), (35, 1), (41, 1), (55, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (10, 1), (22, 1), (53, 1), (60, 1)] }, { coefficient := -2, powers := [(0, 1), (11, 1), (22, 1), (47, 1), (53, 1), (60, 1)] }, { coefficient := -1, powers := [(3, 1), (20, 1), (45, 1), (48, 1), (56, 1), (62, 1)] }, { coefficient := 1, powers := [(3, 1), (21, 1), (48, 1), (56, 1), (62, 1)] }, { coefficient := -1, powers := [(3, 1), (29, 1), (32, 1), (35, 1), (43, 1)] }, { coefficient := -1, powers := [(3, 1), (29, 1), (53, 1)] }, { coefficient := -1, powers := [(5, 1), (6, 1), (20, 1), (29, 1), (34, 1), (35, 1), (41, 1), (52, 1), (57, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (19, 1), (20, 1), (24, 1), (29, 1), (35, 1), (41, 1), (52, 1), (57, 1), (59, 1)] }, { coefficient := -1, powers := [(6, 1), (20, 1), (56, 1)] }, { coefficient := -1, powers := [(9, 1), (20, 1), (53, 1)] }, { coefficient := -1, powers := [(9, 1), (32, 1), (35, 1)] }, { coefficient := 1, powers := [(11, 1), (22, 1), (25, 1), (29, 1), (35, 1), (43, 1), (53, 1), (60, 1)] }, { coefficient := -1, powers := [(11, 1), (22, 1), (25, 1), (47, 1), (53, 1), (60, 1)] }, { coefficient := -2, powers := [(11, 1), (22, 1), (29, 1), (35, 1), (53, 1), (60, 1)] }, { coefficient := -1, powers := [(15, 1), (20, 1), (29, 1), (35, 1), (43, 1)] }, { coefficient := 1, powers := [(20, 1), (29, 1), (35, 1), (41, 1), (43, 1), (45, 1), (48, 1), (62, 1)] }, { coefficient := -1, powers := [(20, 1), (29, 1), (35, 1), (41, 1), (45, 1), (48, 1), (59, 1), (62, 1)] }, { coefficient := -1, powers := [(20, 1), (29, 1), (35, 1), (43, 1), (53, 1)] }, { coefficient := 1, powers := [(20, 1), (32, 1), (35, 1), (43, 1), (47, 1)] }, { coefficient := 1, powers := [(20, 1), (41, 1), (47, 1)] }, { coefficient := 1, powers := [(20, 1), (47, 1), (53, 1)] }, { coefficient := -1, powers := [(21, 1), (29, 1), (35, 1), (41, 1), (43, 1), (48, 1), (62, 1)] }, { coefficient := 1, powers := [(21, 1), (29, 1), (35, 1), (41, 1), (48, 1), (59, 1), (62, 1)] }, { coefficient := -1, powers := [(21, 1), (29, 1), (35, 1), (51, 1), (53, 1), (62, 1)] }, { coefficient := 1, powers := [(25, 1), (29, 1), (35, 1), (39, 1), (41, 1)] }, { coefficient := 1, powers := [(25, 1), (29, 1), (35, 1), (41, 1), (59, 1)] }]
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
    (values : Fin 66 → R) :
    ¬ ∀ index : Fin 45,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component58.SelectedLeafB6_3_7.selectedHasNoCommonZero

end Krenn.Component58.SelectedLeafB6_3_7
