import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component1.SelectedLeafB6_3

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "4a5ef20009efc9ed2be452db2b02ff68274ef41ca9ea39dae8e00cd6035268d2"
def certificateSHA256 : String := "c6fc35f0465d2ec7ed29edce9c51d2911a4878d1075d80508405e3814911b151"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 34 → Fin 588 := ![
  0,
  1,
  2,
  5,
  12,
  25,
  27,
  34,
  37,
  40,
  56,
  219,
  221,
  228,
  276,
  354,
  371,
  384,
  385,
  392,
  443,
  507,
  545,
  548,
  559,
  560,
  579,
  581,
  582,
  583,
  584,
  585,
  586,
  587
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 34 → SparsePoly (Fin 61) := ![
  [{ coefficient := 1, powers := [(1, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(15, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(34, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1)] }, { coefficient := 1, powers := [(24, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (43, 1)] }, { coefficient := 1, powers := [(11, 1), (26, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (34, 1)] }, { coefficient := 1, powers := [(18, 1), (21, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (30, 1), (55, 1)] }, { coefficient := 1, powers := [(30, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (20, 1), (52, 1)] }, { coefficient := 1, powers := [(14, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (54, 1)] }, { coefficient := 1, powers := [(9, 1), (51, 1)] }, { coefficient := 1, powers := [(15, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (50, 1)] }, { coefficient := 1, powers := [(30, 1), (42, 1)] }, { coefficient := 1, powers := [(33, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (53, 1)] }, { coefficient := 1, powers := [(30, 1), (47, 1)] }, { coefficient := 1, powers := [(36, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1), (51, 1)] }, { coefficient := 1, powers := [(6, 1), (34, 1), (42, 1)] }, { coefficient := 1, powers := [(15, 1), (24, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (34, 1), (50, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (42, 1)] }, { coefficient := 1, powers := [(14, 1), (34, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (56, 1)] }, { coefficient := 1, powers := [(14, 1), (25, 1), (45, 1)] }, { coefficient := 1, powers := [(14, 1), (53, 1)] }, { coefficient := 1, powers := [(19, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1)] }, { coefficient := 1, powers := [(6, 1), (55, 1)] }, { coefficient := 1, powers := [(24, 1), (41, 1)] }, { coefficient := 1, powers := [(24, 1), (44, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (41, 1), (51, 1)] }, { coefficient := 1, powers := [(6, 1), (34, 1), (41, 1)] }, { coefficient := 1, powers := [(15, 1), (24, 1), (41, 1)] }, { coefficient := 1, powers := [(15, 1)] }, { coefficient := 1, powers := [(51, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1)] }, { coefficient := 1, powers := [(3, 1), (34, 1)] }, { coefficient := 1, powers := [(15, 1), (20, 1)] }, { coefficient := 1, powers := [(20, 1), (51, 1)] }, { coefficient := 1, powers := [(24, 1), (43, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (48, 1)] }, { coefficient := 1, powers := [(6, 1), (31, 1)] }, { coefficient := 1, powers := [(9, 1), (24, 1)] }, { coefficient := 1, powers := [(20, 1), (48, 1)] }, { coefficient := 1, powers := [(24, 1), (40, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (37, 1), (54, 1)] }, { coefficient := 1, powers := [(0, 1), (40, 1), (51, 1)] }, { coefficient := 1, powers := [(0, 1), (43, 1), (48, 1)] }, { coefficient := 1, powers := [(3, 1), (24, 1), (54, 1)] }, { coefficient := 1, powers := [(3, 1), (31, 1), (51, 1)] }, { coefficient := 1, powers := [(3, 1), (34, 1), (48, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1), (54, 1)] }, { coefficient := 1, powers := [(6, 1), (31, 1), (43, 1)] }, { coefficient := 1, powers := [(6, 1), (34, 1), (40, 1)] }, { coefficient := 1, powers := [(9, 1), (20, 1), (51, 1)] }, { coefficient := 1, powers := [(9, 1), (24, 1), (43, 1)] }, { coefficient := 1, powers := [(9, 1), (34, 1), (37, 1)] }, { coefficient := 1, powers := [(15, 1), (20, 1), (48, 1)] }, { coefficient := 1, powers := [(15, 1), (24, 1), (40, 1)] }, { coefficient := 1, powers := [(15, 1), (31, 1), (37, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (42, 1), (53, 1)] }, { coefficient := 1, powers := [(2, 1), (47, 1), (50, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (53, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1), (50, 1)] }, { coefficient := 1, powers := [(8, 1), (23, 1), (56, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (47, 1)] }, { coefficient := 1, powers := [(8, 1), (36, 1), (42, 1)] }, { coefficient := 1, powers := [(14, 1), (23, 1), (53, 1)] }, { coefficient := 1, powers := [(14, 1), (30, 1), (47, 1)] }, { coefficient := 1, powers := [(14, 1), (36, 1), (39, 1)] }, { coefficient := 1, powers := [(19, 1), (23, 1), (50, 1)] }, { coefficient := 1, powers := [(19, 1), (30, 1), (42, 1)] }, { coefficient := 1, powers := [(19, 1), (33, 1), (39, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (57, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1), (58, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(40, 1)] }],
  [{ coefficient := 1, powers := [(41, 1), (59, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(42, 1), (60, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 34 → SparsePoly (Fin 61) := ![
  [{ coefficient := 1, powers := [(0, 1), (5, 1), (36, 1), (37, 1), (42, 1), (54, 1), (58, 1), (60, 1)] }, { coefficient := -1, powers := [(0, 1), (19, 1), (23, 1), (37, 1), (42, 1), (54, 1), (58, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (9, 1), (34, 1), (36, 1), (37, 1), (58, 1)] }, { coefficient := -1, powers := [(5, 1), (34, 1), (36, 1), (37, 1), (48, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (5, 1), (30, 1), (37, 1), (42, 1), (54, 1), (55, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (33, 1), (37, 1), (42, 1), (53, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (36, 1), (37, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (26, 1), (48, 1), (58, 1)] }, { coefficient := 1, powers := [(20, 1), (26, 1), (48, 1), (58, 1)] }, { coefficient := 1, powers := [(26, 1), (31, 1), (37, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (23, 1), (25, 1), (37, 1), (42, 1), (54, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (3, 1), (31, 1), (41, 1), (44, 1), (59, 1), (60, 1)] }, { coefficient := -1, powers := [(0, 1), (20, 1), (41, 1), (44, 1), (48, 1), (59, 1), (60, 1)] }, { coefficient := 1, powers := [(3, 1), (6, 1), (31, 1), (41, 1), (55, 1), (59, 1), (60, 1)] }, { coefficient := -1, powers := [(6, 1), (20, 1), (41, 1), (48, 1), (55, 1), (59, 1), (60, 1)] }, { coefficient := -1, powers := [(20, 1), (48, 1), (60, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (21, 1), (23, 1), (37, 1), (50, 1), (56, 1), (60, 1)] }, { coefficient := -1, powers := [(9, 1), (21, 1), (30, 1), (37, 1), (56, 1)] }, { coefficient := -1, powers := [(9, 1), (21, 1), (33, 1), (37, 1), (53, 1)] }, { coefficient := 1, powers := [(9, 1), (21, 1), (36, 1), (37, 1), (50, 1)] }, { coefficient := -1, powers := [(21, 1), (23, 1), (37, 1), (48, 1), (50, 1), (56, 1), (60, 1)] }, { coefficient := 1, powers := [(21, 1), (30, 1), (37, 1), (48, 1), (56, 1)] }, { coefficient := 1, powers := [(21, 1), (33, 1), (37, 1), (48, 1), (53, 1)] }, { coefficient := -1, powers := [(21, 1), (36, 1), (37, 1), (48, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (14, 1), (23, 1), (37, 1), (42, 1), (52, 1), (54, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (8, 1), (33, 1), (37, 1), (42, 1), (47, 1), (54, 1), (57, 1), (60, 2)] }, { coefficient := 1, powers := [(3, 1), (15, 1), (31, 1), (41, 1), (44, 1), (59, 1), (60, 1)] }, { coefficient := 1, powers := [(3, 1), (15, 1), (31, 1), (41, 1), (60, 1)] }, { coefficient := 1, powers := [(3, 1), (54, 1), (60, 1)] }, { coefficient := -1, powers := [(8, 1), (9, 1), (33, 1), (34, 1), (37, 1), (47, 1), (57, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (34, 1), (37, 1), (47, 1), (48, 1), (57, 1), (60, 1)] }, { coefficient := -1, powers := [(15, 1), (20, 1), (41, 1), (44, 1), (48, 1), (59, 1), (60, 1)] }, { coefficient := -1, powers := [(15, 1), (20, 1), (41, 1), (48, 1), (60, 1)] }, { coefficient := -1, powers := [(43, 1), (48, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(9, 1), (14, 1), (23, 1), (37, 1), (56, 1), (60, 1)] }, { coefficient := -1, powers := [(9, 1), (14, 1), (36, 1), (37, 1)] }, { coefficient := 1, powers := [(14, 1), (23, 1), (37, 1), (48, 1), (56, 1), (60, 1)] }, { coefficient := 1, powers := [(14, 1), (36, 1), (37, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (8, 1), (33, 1), (37, 1), (42, 1), (54, 1), (57, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (9, 1), (33, 1), (34, 1), (37, 1), (57, 1)] }, { coefficient := -1, powers := [(8, 1), (33, 1), (34, 1), (37, 1), (48, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (48, 1), (58, 1)] }, { coefficient := -1, powers := [(20, 1), (48, 1), (58, 1)] }, { coefficient := -1, powers := [(31, 1), (37, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(9, 1), (23, 1), (37, 1), (50, 1), (56, 1), (60, 1)] }, { coefficient := 1, powers := [(9, 1), (30, 1), (37, 1), (56, 1)] }, { coefficient := 1, powers := [(9, 1), (33, 1), (37, 1), (53, 1)] }, { coefficient := -1, powers := [(9, 1), (36, 1), (37, 1), (50, 1)] }, { coefficient := 1, powers := [(23, 1), (37, 1), (48, 1), (50, 1), (56, 1), (60, 1)] }, { coefficient := -1, powers := [(30, 1), (37, 1), (48, 1), (56, 1)] }, { coefficient := -1, powers := [(33, 1), (37, 1), (48, 1), (53, 1)] }, { coefficient := 1, powers := [(36, 1), (37, 1), (48, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (5, 1), (37, 1), (42, 1), (54, 1), (56, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (23, 1), (37, 1), (42, 1), (53, 1), (54, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(20, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (19, 1), (37, 1), (42, 1), (54, 1), (60, 1)] }, { coefficient := 1, powers := [(9, 1), (19, 1), (34, 1), (37, 1)] }, { coefficient := -1, powers := [(19, 1), (34, 1), (37, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (14, 1), (37, 1), (42, 1), (54, 1), (60, 1)] }, { coefficient := 1, powers := [(9, 1), (14, 1), (34, 1), (37, 1)] }, { coefficient := -1, powers := [(14, 1), (34, 1), (37, 1), (48, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (31, 1), (41, 1), (60, 1)] }, { coefficient := 1, powers := [(20, 1), (41, 1), (48, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (23, 1), (37, 1), (56, 1), (60, 1)] }, { coefficient := 1, powers := [(9, 1), (36, 1), (37, 1)] }, { coefficient := -1, powers := [(23, 1), (37, 1), (48, 1), (56, 1), (60, 1)] }, { coefficient := -1, powers := [(36, 1), (37, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (23, 1), (37, 1), (42, 1), (54, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (15, 1), (31, 1), (41, 1), (59, 1)] }, { coefficient := 1, powers := [(15, 1), (20, 1), (41, 1), (48, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (31, 1), (41, 1), (59, 1)] }, { coefficient := -1, powers := [(20, 1), (41, 1), (48, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(48, 1)] }],
  [{ coefficient := 1, powers := [(43, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(0, 1), (37, 1), (42, 1), (54, 1), (60, 1)] }, { coefficient := -1, powers := [(9, 1), (34, 1), (37, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1), (48, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (8, 1), (33, 1), (37, 1), (42, 1), (47, 1), (54, 1), (60, 1)] }, { coefficient := -1, powers := [(8, 1), (9, 1), (33, 1), (34, 1), (37, 1), (47, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (34, 1), (37, 1), (47, 1), (48, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (5, 1), (36, 1), (37, 1), (42, 1), (50, 1), (54, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (19, 1), (23, 1), (37, 1), (42, 1), (50, 1), (54, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (43, 1), (48, 1)] }, { coefficient := -1, powers := [(5, 1), (9, 1), (34, 1), (36, 1), (37, 1), (50, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (36, 1), (37, 1), (48, 1), (50, 1)] }, { coefficient := 1, powers := [(20, 1), (43, 1), (48, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (37, 1), (39, 1), (42, 1), (54, 1), (56, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (37, 1), (42, 2), (53, 1), (54, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (37, 1), (42, 1), (47, 1), (50, 1), (54, 1), (60, 1)] }, { coefficient := 1, powers := [(9, 1), (34, 1), (37, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(9, 1), (34, 1), (37, 1), (42, 1), (53, 1)] }, { coefficient := 1, powers := [(9, 1), (34, 1), (37, 1), (47, 1), (50, 1)] }, { coefficient := -1, powers := [(34, 1), (37, 1), (39, 1), (48, 1), (56, 1)] }, { coefficient := -1, powers := [(34, 1), (37, 1), (42, 1), (48, 1), (53, 1)] }, { coefficient := -1, powers := [(34, 1), (37, 1), (47, 1), (48, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (51, 1)] }, { coefficient := 1, powers := [(6, 1), (34, 1)] }, { coefficient := 1, powers := [(15, 1), (24, 1)] }, { coefficient := -1, powers := [(24, 1), (43, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (3, 1), (31, 1), (41, 1), (51, 1)] }, { coefficient := 1, powers := [(0, 1), (20, 1), (41, 1), (48, 1), (51, 1)] }, { coefficient := -1, powers := [(3, 1), (6, 1), (31, 1), (34, 1), (41, 1)] }, { coefficient := -1, powers := [(3, 1), (31, 1), (51, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1), (34, 1), (41, 1), (48, 1)] }, { coefficient := 1, powers := [(20, 1), (48, 1), (51, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (3, 1), (15, 1), (31, 1), (41, 1), (44, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (3, 1), (31, 1), (41, 1), (51, 1)] }, { coefficient := 1, powers := [(0, 1), (8, 1), (24, 1), (33, 1), (37, 1), (42, 1), (47, 1), (54, 1), (57, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (8, 1), (36, 1), (37, 1), (42, 1), (54, 1)] }, { coefficient := 1, powers := [(0, 1), (15, 1), (20, 1), (41, 1), (44, 1), (48, 1), (59, 1)] }, { coefficient := -1, powers := [(0, 1), (20, 1), (41, 1), (48, 1), (51, 1)] }, { coefficient := -1, powers := [(0, 1), (37, 1), (54, 1)] }, { coefficient := -1, powers := [(3, 1), (6, 1), (15, 1), (31, 1), (41, 1), (55, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (6, 1), (31, 1), (34, 1), (41, 1)] }, { coefficient := -1, powers := [(3, 1), (15, 1), (24, 1), (31, 1), (41, 1), (44, 1), (59, 1)] }, { coefficient := -1, powers := [(3, 1), (24, 1), (54, 1)] }, { coefficient := 1, powers := [(6, 1), (15, 1), (20, 1), (41, 1), (48, 1), (55, 1), (59, 1)] }, { coefficient := -1, powers := [(6, 1), (20, 1), (34, 1), (41, 1), (48, 1)] }, { coefficient := -1, powers := [(8, 1), (9, 1), (23, 1), (34, 1), (37, 1), (56, 1)] }, { coefficient := 1, powers := [(8, 1), (9, 1), (24, 1), (33, 1), (34, 1), (37, 1), (47, 1), (57, 1)] }, { coefficient := 1, powers := [(8, 1), (23, 1), (34, 1), (37, 1), (48, 1), (56, 1)] }, { coefficient := -1, powers := [(8, 1), (24, 1), (33, 1), (34, 1), (37, 1), (47, 1), (48, 1), (57, 1)] }, { coefficient := 1, powers := [(15, 1), (20, 1), (24, 1), (41, 1), (44, 1), (48, 1), (59, 1)] }, { coefficient := 1, powers := [(15, 1), (20, 1), (48, 1)] }, { coefficient := -1, powers := [(15, 1), (31, 1), (37, 1)] }, { coefficient := 1, powers := [(24, 1), (43, 1), (48, 1)] }]
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
    ¬ ∀ index : Fin 34,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component1.SelectedLeafB6_3.selectedHasNoCommonZero

end Krenn.Component1.SelectedLeafB6_3
