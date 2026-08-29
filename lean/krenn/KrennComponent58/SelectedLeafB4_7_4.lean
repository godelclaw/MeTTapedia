import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component58.SelectedLeafB4_7_4

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "b117996d81b789582ce74e21de2444aebf67506a23f8a7e4f2d330cc34731700"
def certificateSHA256 : String := "eacd82262e0827535bcaa819fa041a226ea95320b5bf91d8ff143ce97b3ce163"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 32 → Fin 622 := ![
  20,
  22,
  24,
  39,
  204,
  214,
  253,
  279,
  339,
  342,
  353,
  412,
  430,
  460,
  467,
  474,
  537,
  538,
  540,
  546,
  578,
  580,
  581,
  584,
  611,
  612,
  614,
  615,
  618,
  619,
  620,
  621
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 32 → SparsePoly (Fin 64) := ![
  [{ coefficient := 1, powers := [(14, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(28, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (25, 1)] }, { coefficient := 1, powers := [(16, 1), (20, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (42, 1)] }, { coefficient := 1, powers := [(19, 1), (20, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (24, 1), (57, 1)] }, { coefficient := 1, powers := [(24, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (25, 1), (45, 1)] }, { coefficient := 1, powers := [(16, 1), (21, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (46, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (58, 1)] }, { coefficient := 1, powers := [(14, 1), (55, 1)] }, { coefficient := 1, powers := [(19, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (55, 1)] }, { coefficient := 1, powers := [(28, 1), (46, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (24, 1), (57, 1)] }, { coefficient := 1, powers := [(11, 1), (24, 1), (54, 1)] }, { coefficient := 1, powers := [(16, 1), (24, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (20, 1), (54, 1)] }, { coefficient := 1, powers := [(12, 1)] }, { coefficient := 1, powers := [(16, 1), (20, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (51, 1)] }, { coefficient := 1, powers := [(20, 1), (48, 1), (54, 1)] }, { coefficient := 1, powers := [(20, 1), (51, 1)] }, { coefficient := 1, powers := [(48, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (58, 1)] }, { coefficient := 1, powers := [(14, 1), (46, 1)] }, { coefficient := 1, powers := [(19, 1), (21, 1), (51, 1)] }, { coefficient := 1, powers := [(19, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (52, 1)] }, { coefficient := 1, powers := [(28, 1), (40, 1)] }, { coefficient := 1, powers := [(28, 1), (45, 1), (48, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (20, 1), (57, 1)] }, { coefficient := 1, powers := [(11, 1), (20, 1), (54, 1)] }, { coefficient := 1, powers := [(11, 1)] }, { coefficient := 1, powers := [(16, 1), (20, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (21, 1), (57, 1)] }, { coefficient := 1, powers := [(11, 1), (21, 1), (54, 1)] }, { coefficient := 1, powers := [(11, 1), (45, 1)] }, { coefficient := 1, powers := [(16, 1), (21, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (24, 1), (58, 1)] }, { coefficient := 1, powers := [(7, 1), (31, 1), (46, 1)] }, { coefficient := 1, powers := [(7, 1), (34, 1), (40, 1)] }, { coefficient := 1, powers := [(17, 1), (24, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (21, 1), (54, 1)] }, { coefficient := 1, powers := [(12, 1), (45, 1)] }, { coefficient := 1, powers := [(16, 1), (21, 1), (51, 1)] }, { coefficient := 1, powers := [(16, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (43, 1)] }, { coefficient := 1, powers := [(4, 1), (26, 1), (57, 1)] }, { coefficient := 1, powers := [(4, 1), (33, 1)] }, { coefficient := 1, powers := [(11, 1), (26, 1), (43, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1)] }, { coefficient := 1, powers := [(16, 1), (26, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (57, 1)] }, { coefficient := 1, powers := [(7, 1), (57, 1)] }, { coefficient := 1, powers := [(11, 1), (43, 1)] }, { coefficient := 1, powers := [(11, 1), (54, 1)] }, { coefficient := 1, powers := [(16, 1), (39, 1)] }, { coefficient := 1, powers := [(16, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (50, 1)] }, { coefficient := 1, powers := [(23, 1), (54, 1)] }, { coefficient := 1, powers := [(27, 1), (39, 1)] }, { coefficient := 1, powers := [(27, 1), (43, 1)] }, { coefficient := 1, powers := [(30, 1), (36, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (40, 1), (54, 1)] }, { coefficient := 1, powers := [(0, 1), (45, 1), (51, 1)] }, { coefficient := 1, powers := [(21, 1), (48, 1), (54, 1)] }, { coefficient := 1, powers := [(21, 1), (51, 1)] }, { coefficient := 1, powers := [(40, 1)] }, { coefficient := 1, powers := [(45, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (36, 1), (57, 1)] }, { coefficient := 1, powers := [(1, 1), (39, 1), (54, 1)] }, { coefficient := 1, powers := [(1, 1), (43, 1), (50, 1)] }, { coefficient := 1, powers := [(4, 1), (27, 1), (57, 1)] }, { coefficient := 1, powers := [(4, 1), (30, 1), (54, 1)] }, { coefficient := 1, powers := [(4, 1), (33, 1), (50, 1)] }, { coefficient := 1, powers := [(7, 1), (23, 1), (57, 1)] }, { coefficient := 1, powers := [(7, 1), (30, 1), (43, 1)] }, { coefficient := 1, powers := [(7, 1), (33, 1), (39, 1)] }, { coefficient := 1, powers := [(11, 1), (23, 1), (54, 1)] }, { coefficient := 1, powers := [(11, 1), (27, 1), (43, 1)] }, { coefficient := 1, powers := [(11, 1), (33, 1), (36, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1), (50, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1), (39, 1)] }, { coefficient := 1, powers := [(16, 1), (30, 1), (36, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (37, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (40, 1), (55, 1)] }, { coefficient := 1, powers := [(2, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(5, 1), (28, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (52, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (58, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1), (46, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (40, 1)] }, { coefficient := 1, powers := [(14, 1), (24, 1), (55, 1)] }, { coefficient := 1, powers := [(14, 1), (28, 1), (46, 1)] }, { coefficient := 1, powers := [(14, 1), (34, 1), (37, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (52, 1)] }, { coefficient := 1, powers := [(19, 1), (28, 1), (40, 1)] }, { coefficient := 1, powers := [(19, 1), (31, 1), (37, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1)] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(40, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(53, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(54, 1)] }],
  [{ coefficient := 1, powers := [(55, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 32 → SparsePoly (Fin 64) := ![
  [{ coefficient := 1, powers := [(7, 1), (23, 1), (28, 1), (42, 1), (45, 1), (57, 1), (63, 1)] }, { coefficient := -1, powers := [(7, 1), (23, 1), (28, 1), (46, 1), (57, 1), (63, 1)] }, { coefficient := 1, powers := [(7, 1), (26, 1), (28, 1), (42, 1), (45, 1), (50, 1), (57, 1), (63, 1)] }, { coefficient := -1, powers := [(7, 1), (26, 1), (28, 1), (46, 1), (50, 1), (57, 1), (63, 1)] }, { coefficient := -1, powers := [(7, 1), (27, 1), (28, 1), (42, 1), (45, 1), (57, 1), (63, 1)] }, { coefficient := 1, powers := [(7, 1), (27, 1), (28, 1), (46, 1), (57, 1), (63, 1)] }, { coefficient := 1, powers := [(7, 1), (28, 1), (30, 1), (42, 1), (43, 1), (45, 1), (63, 1)] }, { coefficient := -1, powers := [(7, 1), (28, 1), (30, 1), (43, 1), (46, 1), (63, 1)] }, { coefficient := 1, powers := [(7, 1), (28, 1), (33, 1), (39, 1), (42, 1), (45, 1), (63, 1)] }, { coefficient := -1, powers := [(7, 1), (28, 1), (33, 1), (39, 1), (46, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (8, 1), (23, 1), (50, 1), (57, 1), (58, 1)] }, { coefficient := 1, powers := [(6, 1), (8, 1), (26, 1), (50, 2), (57, 1), (58, 1)] }, { coefficient := -1, powers := [(6, 1), (8, 1), (27, 1), (50, 1), (57, 1), (58, 1)] }, { coefficient := 1, powers := [(6, 1), (8, 1), (30, 1), (43, 1), (50, 1), (58, 1)] }, { coefficient := 1, powers := [(6, 1), (8, 1), (33, 1), (39, 1), (50, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (23, 1), (51, 1), (57, 1)] }, { coefficient := -1, powers := [(8, 1), (26, 1), (50, 1), (51, 1), (57, 1)] }, { coefficient := 1, powers := [(8, 1), (27, 1), (51, 1), (57, 1)] }, { coefficient := -1, powers := [(8, 1), (30, 1), (43, 1), (51, 1)] }, { coefficient := -1, powers := [(8, 1), (33, 1), (39, 1), (51, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (19, 1), (23, 1), (45, 1), (57, 1)] }, { coefficient := -1, powers := [(7, 1), (19, 1), (26, 1), (45, 1), (50, 1), (57, 1)] }, { coefficient := 1, powers := [(7, 1), (19, 1), (27, 1), (45, 1), (57, 1)] }, { coefficient := -1, powers := [(7, 1), (19, 1), (30, 1), (43, 1), (45, 1)] }, { coefficient := -1, powers := [(7, 1), (19, 1), (33, 1), (39, 1), (45, 1)] }],
  [{ coefficient := -1, powers := [(23, 1), (45, 1), (50, 1), (51, 1), (62, 1)] }, { coefficient := 1, powers := [(26, 1), (45, 1), (50, 2), (51, 1), (62, 1)] }, { coefficient := -1, powers := [(27, 1), (39, 1), (45, 1), (51, 1), (62, 1)] }, { coefficient := -1, powers := [(27, 1), (43, 1), (45, 1), (51, 1), (62, 1)] }, { coefficient := -1, powers := [(27, 1), (45, 1), (50, 1), (51, 1), (62, 1)] }, { coefficient := -1, powers := [(33, 1), (36, 1), (45, 1), (51, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (23, 1), (28, 1), (45, 1), (57, 1)] }, { coefficient := -1, powers := [(7, 1), (26, 1), (28, 1), (45, 1), (50, 1), (57, 1)] }, { coefficient := 1, powers := [(7, 1), (27, 1), (28, 1), (45, 1), (57, 1)] }, { coefficient := -1, powers := [(7, 1), (28, 1), (30, 1), (43, 1), (45, 1)] }, { coefficient := -1, powers := [(7, 1), (28, 1), (33, 1), (39, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (8, 1), (23, 1), (57, 1), (58, 1)] }, { coefficient := 1, powers := [(7, 1), (8, 1), (26, 1), (50, 1), (57, 1), (58, 1)] }, { coefficient := -1, powers := [(7, 1), (8, 1), (27, 1), (57, 1), (58, 1)] }, { coefficient := 1, powers := [(7, 1), (8, 1), (30, 1), (43, 1), (58, 1)] }, { coefficient := 1, powers := [(7, 1), (8, 1), (33, 1), (39, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (50, 1), (51, 1), (62, 1)] }, { coefficient := -1, powers := [(26, 1), (50, 2), (51, 1), (62, 1)] }, { coefficient := 1, powers := [(27, 1), (39, 1), (51, 1), (62, 1)] }, { coefficient := 1, powers := [(27, 1), (43, 1), (51, 1), (62, 1)] }, { coefficient := 1, powers := [(27, 1), (50, 1), (51, 1), (62, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1), (51, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (23, 1), (52, 1), (57, 1)] }, { coefficient := 1, powers := [(7, 1), (26, 1), (50, 1), (52, 1), (57, 1)] }, { coefficient := -1, powers := [(7, 1), (27, 1), (52, 1), (57, 1)] }, { coefficient := 1, powers := [(7, 1), (30, 1), (43, 1), (52, 1)] }, { coefficient := 1, powers := [(7, 1), (33, 1), (39, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (23, 1), (24, 1), (57, 1)] }, { coefficient := -1, powers := [(7, 1), (24, 1), (26, 1), (50, 1), (57, 1)] }, { coefficient := 1, powers := [(7, 1), (24, 1), (27, 1), (57, 1)] }, { coefficient := -1, powers := [(7, 1), (24, 1), (30, 1), (43, 1)] }, { coefficient := -1, powers := [(7, 1), (24, 1), (33, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (14, 1), (23, 1), (57, 1)] }, { coefficient := 1, powers := [(7, 1), (14, 1), (26, 1), (50, 1), (57, 1)] }, { coefficient := -1, powers := [(7, 1), (14, 1), (27, 1), (57, 1)] }, { coefficient := 1, powers := [(7, 1), (14, 1), (30, 1), (43, 1)] }, { coefficient := 1, powers := [(7, 1), (14, 1), (33, 1), (39, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (8, 1), (23, 1), (57, 1), (58, 1)] }, { coefficient := -1, powers := [(6, 1), (8, 1), (26, 1), (50, 1), (57, 1), (58, 1)] }, { coefficient := 1, powers := [(6, 1), (8, 1), (27, 1), (57, 1), (58, 1)] }, { coefficient := -1, powers := [(6, 1), (8, 1), (30, 1), (43, 1), (58, 1)] }, { coefficient := -1, powers := [(6, 1), (8, 1), (33, 1), (39, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (45, 1), (50, 1), (62, 1)] }, { coefficient := -1, powers := [(26, 1), (45, 1), (50, 2), (62, 1)] }, { coefficient := 1, powers := [(27, 1), (39, 1), (45, 1), (62, 1)] }, { coefficient := 1, powers := [(27, 1), (43, 1), (45, 1), (62, 1)] }, { coefficient := 1, powers := [(27, 1), (45, 1), (50, 1), (62, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1), (45, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (19, 1), (23, 1), (28, 1), (45, 1), (57, 1)] }, { coefficient := 1, powers := [(7, 1), (19, 1), (26, 1), (28, 1), (45, 1), (50, 1), (57, 1)] }, { coefficient := -1, powers := [(7, 1), (19, 1), (27, 1), (28, 1), (45, 1), (57, 1)] }, { coefficient := 1, powers := [(7, 1), (19, 1), (28, 1), (30, 1), (43, 1), (45, 1)] }, { coefficient := 1, powers := [(7, 1), (19, 1), (28, 1), (33, 1), (39, 1), (45, 1)] }, { coefficient := -1, powers := [(11, 1), (33, 1), (36, 1), (45, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (23, 1), (28, 1), (57, 1)] }, { coefficient := 1, powers := [(7, 1), (26, 1), (28, 1), (50, 1), (57, 1)] }, { coefficient := -1, powers := [(7, 1), (27, 1), (28, 1), (57, 1)] }, { coefficient := 1, powers := [(7, 1), (28, 1), (30, 1), (43, 1)] }, { coefficient := 1, powers := [(7, 1), (28, 1), (33, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (19, 1), (23, 1), (57, 1)] }, { coefficient := 1, powers := [(7, 1), (19, 1), (26, 1), (50, 1), (57, 1)] }, { coefficient := -1, powers := [(7, 1), (19, 1), (27, 1), (57, 1)] }, { coefficient := 1, powers := [(7, 1), (19, 1), (30, 1), (43, 1)] }, { coefficient := 1, powers := [(7, 1), (19, 1), (33, 1), (39, 1)] }],
  [{ coefficient := -1, powers := [(21, 1), (33, 1), (36, 1), (51, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (33, 1), (36, 1), (51, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (23, 1), (57, 1)] }, { coefficient := 1, powers := [(8, 1), (26, 1), (50, 1), (57, 1)] }, { coefficient := -1, powers := [(8, 1), (27, 1), (57, 1)] }, { coefficient := 1, powers := [(8, 1), (30, 1), (43, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (39, 1)] }],
  [{ coefficient := -1, powers := [(23, 1), (50, 1), (62, 1)] }, { coefficient := 1, powers := [(26, 1), (50, 2), (62, 1)] }, { coefficient := -1, powers := [(27, 1), (39, 1), (62, 1)] }, { coefficient := -1, powers := [(27, 1), (43, 1), (62, 1)] }, { coefficient := -1, powers := [(27, 1), (50, 1), (62, 1)] }, { coefficient := -1, powers := [(33, 1), (36, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(50, 1)] }],
  [{ coefficient := -1, powers := [(26, 1), (50, 1)] }, { coefficient := 1, powers := [(27, 1)] }],
  [{ coefficient := 1, powers := [(16, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (19, 1), (23, 1), (28, 1), (57, 1)] }, { coefficient := -1, powers := [(7, 1), (19, 1), (26, 1), (28, 1), (50, 1), (57, 1)] }, { coefficient := 1, powers := [(7, 1), (19, 1), (27, 1), (28, 1), (57, 1)] }, { coefficient := -1, powers := [(7, 1), (19, 1), (28, 1), (30, 1), (43, 1)] }, { coefficient := -1, powers := [(7, 1), (19, 1), (28, 1), (33, 1), (39, 1)] }, { coefficient := 1, powers := [(11, 1), (33, 1), (36, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(7, 1), (23, 1), (57, 1)] }, { coefficient := -1, powers := [(7, 1), (26, 1), (50, 1), (57, 1)] }, { coefficient := 1, powers := [(7, 1), (27, 1), (57, 1)] }, { coefficient := -1, powers := [(7, 1), (30, 1), (43, 1)] }, { coefficient := -1, powers := [(7, 1), (33, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(36, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (23, 1), (37, 1), (57, 1), (58, 1)] }, { coefficient := 1, powers := [(7, 1), (26, 1), (37, 1), (50, 1), (57, 1), (58, 1)] }, { coefficient := -1, powers := [(7, 1), (27, 1), (37, 1), (57, 1), (58, 1)] }, { coefficient := 1, powers := [(7, 1), (30, 1), (37, 1), (43, 1), (58, 1)] }, { coefficient := 1, powers := [(7, 1), (33, 1), (37, 1), (39, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(11, 1), (33, 1), (36, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1), (50, 1)] }, { coefficient := -1, powers := [(16, 1), (26, 1), (50, 2)] }, { coefficient := 1, powers := [(16, 1), (27, 1), (39, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1), (43, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1), (50, 1)] }, { coefficient := 1, powers := [(16, 1), (33, 1), (36, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (14, 1), (23, 1), (28, 1), (42, 1), (45, 1), (57, 1)] }, { coefficient := 1, powers := [(7, 1), (14, 1), (23, 1), (28, 1), (46, 1), (57, 1)] }, { coefficient := -1, powers := [(7, 1), (14, 1), (26, 1), (28, 1), (42, 1), (45, 1), (50, 1), (57, 1)] }, { coefficient := 1, powers := [(7, 1), (14, 1), (26, 1), (28, 1), (46, 1), (50, 1), (57, 1)] }, { coefficient := 1, powers := [(7, 1), (14, 1), (27, 1), (28, 1), (42, 1), (45, 1), (57, 1)] }, { coefficient := -1, powers := [(7, 1), (14, 1), (27, 1), (28, 1), (46, 1), (57, 1)] }, { coefficient := -1, powers := [(7, 1), (14, 1), (28, 1), (30, 1), (42, 1), (43, 1), (45, 1)] }, { coefficient := 1, powers := [(7, 1), (14, 1), (28, 1), (30, 1), (43, 1), (46, 1)] }, { coefficient := -1, powers := [(7, 1), (14, 1), (28, 1), (33, 1), (39, 1), (42, 1), (45, 1)] }, { coefficient := 1, powers := [(7, 1), (14, 1), (28, 1), (33, 1), (39, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (7, 1), (19, 1), (23, 1), (28, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (7, 1), (19, 1), (26, 1), (28, 1), (40, 1), (50, 1), (57, 1)] }, { coefficient := -1, powers := [(0, 1), (7, 1), (19, 1), (27, 1), (28, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (7, 1), (19, 1), (28, 1), (30, 1), (40, 1), (43, 1)] }, { coefficient := 1, powers := [(0, 1), (7, 1), (19, 1), (28, 1), (33, 1), (39, 1), (40, 1)] }, { coefficient := -1, powers := [(0, 1), (11, 1), (33, 1), (36, 1), (40, 1), (62, 1)] }, { coefficient := 1, powers := [(1, 1), (39, 1)] }, { coefficient := 1, powers := [(4, 1), (30, 1)] }, { coefficient := 1, powers := [(6, 1), (8, 1), (11, 1), (23, 1), (24, 1), (57, 1), (58, 1)] }, { coefficient := 1, powers := [(6, 1), (8, 1), (11, 1), (24, 1), (26, 1), (50, 1), (57, 1), (58, 1)] }, { coefficient := -1, powers := [(6, 1), (8, 1), (11, 1), (24, 1), (27, 1), (57, 1), (58, 1)] }, { coefficient := 1, powers := [(6, 1), (8, 1), (11, 1), (24, 1), (30, 1), (43, 1), (58, 1)] }, { coefficient := 1, powers := [(6, 1), (8, 1), (11, 1), (24, 1), (33, 1), (39, 1), (58, 1)] }, { coefficient := -1, powers := [(7, 1), (19, 1), (20, 1), (23, 1), (28, 1), (45, 1), (48, 1), (57, 1)] }, { coefficient := -1, powers := [(7, 1), (19, 1), (20, 1), (26, 1), (28, 1), (45, 1), (48, 1), (50, 1), (57, 1)] }, { coefficient := 1, powers := [(7, 1), (19, 1), (20, 1), (27, 1), (28, 1), (45, 1), (48, 1), (57, 1)] }, { coefficient := -1, powers := [(7, 1), (19, 1), (20, 1), (28, 1), (30, 1), (43, 1), (45, 1), (48, 1)] }, { coefficient := -1, powers := [(7, 1), (19, 1), (20, 1), (28, 1), (33, 1), (39, 1), (45, 1), (48, 1)] }, { coefficient := 1, powers := [(7, 1), (19, 1), (21, 1), (23, 1), (28, 1), (48, 1), (57, 1)] }, { coefficient := 1, powers := [(7, 1), (19, 1), (21, 1), (26, 1), (28, 1), (48, 1), (50, 1), (57, 1)] }, { coefficient := -1, powers := [(7, 1), (19, 1), (21, 1), (27, 1), (28, 1), (48, 1), (57, 1)] }, { coefficient := 1, powers := [(7, 1), (19, 1), (21, 1), (28, 1), (30, 1), (43, 1), (48, 1)] }, { coefficient := 1, powers := [(7, 1), (19, 1), (21, 1), (28, 1), (33, 1), (39, 1), (48, 1)] }, { coefficient := 1, powers := [(11, 1), (20, 1), (33, 1), (36, 1), (45, 1), (48, 1), (62, 1)] }, { coefficient := -1, powers := [(11, 1), (21, 1), (33, 1), (36, 1), (48, 1), (62, 1)] }, { coefficient := 1, powers := [(11, 1), (23, 1)] }, { coefficient := 1, powers := [(11, 1), (26, 1), (50, 1)] }, { coefficient := -1, powers := [(11, 1), (27, 1)] }, { coefficient := -1, powers := [(12, 1), (20, 1), (23, 1), (45, 1), (50, 1), (62, 1)] }, { coefficient := 1, powers := [(12, 1), (20, 1), (26, 1), (45, 1), (50, 2), (62, 1)] }, { coefficient := -1, powers := [(12, 1), (20, 1), (27, 1), (39, 1), (45, 1), (62, 1)] }, { coefficient := -1, powers := [(12, 1), (20, 1), (27, 1), (43, 1), (45, 1), (62, 1)] }, { coefficient := -1, powers := [(12, 1), (20, 1), (27, 1), (45, 1), (50, 1), (62, 1)] }, { coefficient := -1, powers := [(12, 1), (20, 1), (33, 1), (36, 1), (45, 1), (62, 1)] }, { coefficient := 1, powers := [(12, 1), (21, 1), (23, 1), (50, 1), (62, 1)] }, { coefficient := -1, powers := [(12, 1), (21, 1), (26, 1), (50, 2), (62, 1)] }, { coefficient := 1, powers := [(12, 1), (21, 1), (27, 1), (39, 1), (62, 1)] }, { coefficient := 1, powers := [(12, 1), (21, 1), (27, 1), (43, 1), (62, 1)] }, { coefficient := 1, powers := [(12, 1), (21, 1), (27, 1), (50, 1), (62, 1)] }, { coefficient := 1, powers := [(12, 1), (21, 1), (33, 1), (36, 1), (62, 1)] }, { coefficient := -1, powers := [(16, 1), (23, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (7, 1), (23, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (7, 1), (26, 1), (40, 1), (50, 1), (57, 1)] }, { coefficient := -1, powers := [(2, 1), (7, 1), (27, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (7, 1), (30, 1), (40, 1), (43, 1)] }, { coefficient := 1, powers := [(2, 1), (7, 1), (33, 1), (39, 1), (40, 1)] }, { coefficient := 1, powers := [(5, 1), (7, 1), (23, 1), (31, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (7, 1), (26, 1), (31, 1), (50, 1), (57, 1)] }, { coefficient := -1, powers := [(5, 1), (7, 1), (27, 1), (31, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (7, 1), (30, 1), (31, 1), (43, 1)] }, { coefficient := 1, powers := [(5, 1), (7, 1), (31, 1), (33, 1), (39, 1)] }, { coefficient := 1, powers := [(7, 1), (14, 1), (23, 1), (24, 1), (57, 1)] }, { coefficient := 1, powers := [(7, 1), (14, 1), (24, 1), (26, 1), (50, 1), (57, 1)] }, { coefficient := -1, powers := [(7, 1), (14, 1), (24, 1), (27, 1), (57, 1)] }, { coefficient := 1, powers := [(7, 1), (14, 1), (24, 1), (30, 1), (43, 1)] }, { coefficient := 1, powers := [(7, 1), (14, 1), (24, 1), (33, 1), (39, 1)] }]
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
    (values : Fin 64 → R) :
    ¬ ∀ index : Fin 32,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component58.SelectedLeafB4_7_4.selectedHasNoCommonZero

end Krenn.Component58.SelectedLeafB4_7_4
