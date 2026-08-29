import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component1.SelectedLeafB6_2_3

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "5d6556d1baca7e833414b48575db4d1383551514cdaf0c7776b8cdf12c55ec7a"
def certificateSHA256 : String := "5bec2e9b304e0b2344db1a0df287205cee4aa42d25d5b5fcc6f5f05eaec216a6"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 31 → Fin 591 := ![
  0,
  1,
  2,
  3,
  6,
  12,
  25,
  37,
  84,
  221,
  229,
  276,
  302,
  354,
  367,
  384,
  385,
  425,
  449,
  507,
  513,
  559,
  560,
  579,
  581,
  583,
  584,
  585,
  587,
  588,
  590
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 31 → SparsePoly (Fin 62) := ![
  [{ coefficient := 1, powers := [(1, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (33, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (43, 1)] }, { coefficient := 1, powers := [(11, 1), (26, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (33, 1)] }, { coefficient := 1, powers := [(33, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (30, 1), (55, 1)] }, { coefficient := 1, powers := [(30, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (25, 1), (45, 1)] }, { coefficient := 1, powers := [(9, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (20, 1), (52, 1)] }, { coefficient := 1, powers := [(14, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (54, 1)] }, { coefficient := 1, powers := [(9, 1), (43, 1)] }, { coefficient := 1, powers := [(15, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (50, 1)] }, { coefficient := 1, powers := [(30, 1), (42, 1)] }, { coefficient := 1, powers := [(33, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (53, 1)] }, { coefficient := 1, powers := [(30, 1), (47, 1)] }, { coefficient := 1, powers := [(36, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (33, 1), (51, 1)] }, { coefficient := 1, powers := [(6, 1), (33, 1), (43, 1)] }, { coefficient := 1, powers := [(15, 1), (33, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (23, 1), (56, 1)] }, { coefficient := 1, powers := [(6, 1), (33, 1), (47, 1)] }, { coefficient := 1, powers := [(6, 1), (36, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (56, 1)] }, { coefficient := 1, powers := [(14, 1), (25, 1), (45, 1)] }, { coefficient := 1, powers := [(14, 1), (53, 1)] }, { coefficient := 1, powers := [(19, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1), (48, 1)] }, { coefficient := 1, powers := [(6, 1), (31, 1), (44, 1)] }, { coefficient := 1, powers := [(9, 1), (24, 1), (44, 1)] }, { coefficient := 1, powers := [(48, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1)] }, { coefficient := 1, powers := [(3, 1), (34, 1)] }, { coefficient := 1, powers := [(15, 1), (20, 1)] }, { coefficient := 1, powers := [(20, 1), (51, 1)] }, { coefficient := 1, powers := [(24, 1), (43, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (48, 1)] }, { coefficient := 1, powers := [(6, 1), (31, 1)] }, { coefficient := 1, powers := [(9, 1), (24, 1)] }, { coefficient := 1, powers := [(20, 1), (48, 1)] }, { coefficient := 1, powers := [(24, 1), (40, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (37, 1), (54, 1)] }, { coefficient := 1, powers := [(0, 1), (40, 1), (51, 1)] }, { coefficient := 1, powers := [(0, 1), (43, 1), (48, 1)] }, { coefficient := 1, powers := [(3, 1), (24, 1), (54, 1)] }, { coefficient := 1, powers := [(3, 1), (31, 1), (51, 1)] }, { coefficient := 1, powers := [(3, 1), (34, 1), (48, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1), (54, 1)] }, { coefficient := 1, powers := [(6, 1), (31, 1), (43, 1)] }, { coefficient := 1, powers := [(6, 1), (34, 1), (40, 1)] }, { coefficient := 1, powers := [(9, 1), (20, 1), (51, 1)] }, { coefficient := 1, powers := [(9, 1), (24, 1), (43, 1)] }, { coefficient := 1, powers := [(9, 1), (34, 1), (37, 1)] }, { coefficient := 1, powers := [(15, 1), (20, 1), (48, 1)] }, { coefficient := 1, powers := [(15, 1), (24, 1), (40, 1)] }, { coefficient := 1, powers := [(15, 1), (31, 1), (37, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (42, 1), (53, 1)] }, { coefficient := 1, powers := [(2, 1), (47, 1), (50, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (53, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1), (50, 1)] }, { coefficient := 1, powers := [(8, 1), (23, 1), (56, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (47, 1)] }, { coefficient := 1, powers := [(8, 1), (36, 1), (42, 1)] }, { coefficient := 1, powers := [(14, 1), (23, 1), (53, 1)] }, { coefficient := 1, powers := [(14, 1), (30, 1), (47, 1)] }, { coefficient := 1, powers := [(14, 1), (36, 1), (39, 1)] }, { coefficient := 1, powers := [(19, 1), (23, 1), (50, 1)] }, { coefficient := 1, powers := [(19, 1), (30, 1), (42, 1)] }, { coefficient := 1, powers := [(19, 1), (33, 1), (39, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1), (58, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(40, 1)] }],
  [{ coefficient := 1, powers := [(42, 1)] }],
  [{ coefficient := 1, powers := [(51, 1)] }],
  [{ coefficient := 1, powers := [(53, 1), (61, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 31 → SparsePoly (Fin 62) := ![
  [{ coefficient := 1, powers := [(0, 1), (5, 1), (36, 1), (37, 1), (54, 1), (58, 1)] }, { coefficient := -1, powers := [(0, 1), (19, 1), (23, 1), (37, 1), (54, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (15, 1), (31, 1), (36, 1), (37, 1), (53, 1), (58, 1), (61, 1)] }, { coefficient := -1, powers := [(5, 1), (31, 1), (34, 1), (36, 1), (37, 2), (44, 1), (58, 1)] }, { coefficient := -1, powers := [(5, 1), (31, 1), (36, 1), (37, 1), (43, 1), (53, 1), (58, 1), (61, 1)] }, { coefficient := -1, powers := [(15, 1), (19, 1), (23, 1), (31, 1), (37, 1), (53, 1), (58, 1), (61, 1)] }, { coefficient := 1, powers := [(19, 1), (23, 1), (31, 1), (34, 1), (37, 2), (44, 1), (58, 1)] }, { coefficient := 1, powers := [(19, 1), (23, 1), (31, 1), (37, 1), (43, 1), (53, 1), (58, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (5, 1), (30, 1), (37, 1), (54, 1), (55, 1)] }, { coefficient := -1, powers := [(5, 1), (15, 1), (30, 1), (31, 1), (37, 1), (53, 1), (55, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (31, 1), (34, 1), (37, 2), (44, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (31, 1), (37, 1), (43, 1), (53, 1), (55, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (33, 1), (37, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (8, 1), (23, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (15, 1), (23, 1), (31, 1), (53, 1), (61, 1)] }, { coefficient := -1, powers := [(8, 1), (23, 1), (31, 1), (34, 1), (37, 1), (44, 1)] }, { coefficient := -1, powers := [(8, 1), (23, 1), (31, 1), (43, 1), (53, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(25, 1), (34, 1), (37, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (26, 1), (48, 1), (58, 1)] }, { coefficient := 1, powers := [(9, 1), (24, 1), (26, 1), (58, 1)] }, { coefficient := 1, powers := [(24, 1), (26, 1), (48, 1), (58, 1)] }, { coefficient := -1, powers := [(26, 1), (31, 1), (37, 1), (53, 1), (58, 1), (61, 1)] }, { coefficient := 1, powers := [(26, 1), (31, 1), (37, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (23, 1), (25, 1), (37, 1), (54, 1)] }, { coefficient := -1, powers := [(15, 1), (23, 1), (25, 1), (31, 1), (37, 1), (53, 1), (61, 1)] }, { coefficient := 1, powers := [(23, 1), (25, 1), (31, 1), (34, 1), (37, 2), (44, 1)] }, { coefficient := 1, powers := [(23, 1), (25, 1), (31, 1), (37, 1), (43, 1), (53, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (14, 1), (23, 1), (37, 1), (52, 1), (53, 1), (54, 1), (61, 1)] }, { coefficient := 1, powers := [(6, 1), (54, 1), (61, 1)] }, { coefficient := 1, powers := [(14, 1), (15, 1), (23, 1), (31, 1), (37, 1), (52, 1), (53, 2), (61, 2)] }, { coefficient := -1, powers := [(14, 1), (23, 1), (31, 1), (34, 1), (37, 2), (44, 1), (52, 1), (53, 1), (61, 1)] }, { coefficient := -1, powers := [(14, 1), (23, 1), (31, 1), (37, 1), (43, 1), (52, 1), (53, 2), (61, 2)] }, { coefficient := -1, powers := [(34, 1), (37, 1), (44, 1), (48, 1), (61, 1)] }, { coefficient := -1, powers := [(43, 1), (48, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (31, 1), (34, 1), (37, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (48, 1), (58, 1)] }, { coefficient := -1, powers := [(9, 1), (24, 1), (58, 1)] }, { coefficient := -1, powers := [(24, 1), (48, 1), (58, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1), (53, 1), (58, 1), (61, 1)] }, { coefficient := -1, powers := [(31, 1), (37, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (8, 1), (47, 1), (54, 1)] }, { coefficient := -1, powers := [(5, 1), (31, 1), (34, 1), (37, 1), (44, 1), (53, 1)] }, { coefficient := -1, powers := [(5, 1), (31, 1), (43, 1), (53, 1)] }, { coefficient := 1, powers := [(8, 1), (15, 1), (31, 1), (47, 1), (53, 1), (61, 1)] }, { coefficient := -1, powers := [(8, 1), (31, 1), (34, 1), (37, 1), (44, 1), (47, 1)] }, { coefficient := -1, powers := [(8, 1), (31, 1), (43, 1), (47, 1), (53, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (5, 1), (37, 1), (54, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (15, 1), (31, 1), (37, 1), (53, 1), (56, 1), (61, 1)] }, { coefficient := -1, powers := [(5, 1), (31, 1), (34, 1), (37, 2), (44, 1), (56, 1)] }, { coefficient := -1, powers := [(5, 1), (31, 1), (37, 1), (43, 1), (53, 1), (56, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(34, 1), (37, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (23, 1), (37, 1), (53, 1), (54, 1)] }, { coefficient := -1, powers := [(15, 1), (23, 1), (31, 1), (37, 1), (53, 2), (61, 1)] }, { coefficient := 1, powers := [(23, 1), (31, 1), (34, 1), (37, 2), (44, 1), (53, 1)] }, { coefficient := 1, powers := [(23, 1), (31, 1), (37, 1), (43, 1), (53, 2), (61, 1)] }],
  [{ coefficient := 1, powers := [(24, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (19, 1), (37, 1), (54, 1)] }, { coefficient := 1, powers := [(15, 1), (19, 1), (31, 1), (37, 1), (53, 1), (61, 1)] }, { coefficient := -1, powers := [(19, 1), (31, 1), (34, 1), (37, 2), (44, 1)] }, { coefficient := -1, powers := [(19, 1), (31, 1), (37, 1), (43, 1), (53, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (14, 1), (37, 1), (54, 1)] }, { coefficient := 1, powers := [(14, 1), (15, 1), (31, 1), (37, 1), (53, 1), (61, 1)] }, { coefficient := -1, powers := [(14, 1), (31, 1), (34, 1), (37, 2), (44, 1)] }, { coefficient := -1, powers := [(14, 1), (31, 1), (37, 1), (43, 1), (53, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (31, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (8, 1), (54, 1)] }, { coefficient := -1, powers := [(8, 1), (15, 1), (31, 1), (53, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1), (34, 1), (37, 1), (44, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1), (43, 1), (53, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (23, 1), (37, 1), (54, 1)] }, { coefficient := 1, powers := [(15, 1), (23, 1), (31, 1), (37, 1), (53, 1), (61, 1)] }, { coefficient := -1, powers := [(23, 1), (31, 1), (34, 1), (37, 2), (44, 1)] }, { coefficient := -1, powers := [(23, 1), (31, 1), (37, 1), (43, 1), (53, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(34, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(48, 1)] }],
  [{ coefficient := 1, powers := [(34, 1), (37, 1), (44, 1)] }, { coefficient := 1, powers := [(43, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(0, 1), (37, 1), (54, 1)] }, { coefficient := -1, powers := [(15, 1), (31, 1), (37, 1), (53, 1), (61, 1)] }, { coefficient := 1, powers := [(31, 1), (34, 1), (37, 2), (44, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1), (43, 1), (53, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (5, 1), (36, 1), (37, 1), (50, 1), (54, 1)] }, { coefficient := 1, powers := [(0, 1), (19, 1), (23, 1), (37, 1), (50, 1), (54, 1)] }, { coefficient := 1, powers := [(0, 1), (43, 1), (48, 1)] }, { coefficient := -1, powers := [(5, 1), (15, 1), (31, 1), (36, 1), (37, 1), (50, 1), (53, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (34, 1), (36, 1), (37, 2), (44, 1), (50, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (36, 1), (37, 1), (43, 1), (50, 1), (53, 1), (61, 1)] }, { coefficient := 1, powers := [(9, 1), (24, 1), (43, 1)] }, { coefficient := 1, powers := [(15, 1), (19, 1), (23, 1), (31, 1), (37, 1), (50, 1), (53, 1), (61, 1)] }, { coefficient := -1, powers := [(19, 1), (23, 1), (31, 1), (34, 1), (37, 2), (44, 1), (50, 1)] }, { coefficient := -1, powers := [(19, 1), (23, 1), (31, 1), (37, 1), (43, 1), (50, 1), (53, 1), (61, 1)] }, { coefficient := 1, powers := [(24, 1), (43, 1), (48, 1)] }, { coefficient := -1, powers := [(31, 1), (37, 1), (43, 1), (53, 1), (61, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (37, 1), (39, 1), (54, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (37, 1), (47, 1), (50, 1), (54, 1)] }, { coefficient := 1, powers := [(15, 1), (31, 1), (37, 1), (39, 1), (53, 1), (56, 1), (61, 1)] }, { coefficient := 1, powers := [(15, 1), (31, 1), (37, 1), (47, 1), (50, 1), (53, 1), (61, 1)] }, { coefficient := -1, powers := [(31, 1), (34, 1), (37, 2), (39, 1), (44, 1), (56, 1)] }, { coefficient := -1, powers := [(31, 1), (34, 1), (37, 2), (44, 1), (47, 1), (50, 1)] }, { coefficient := -1, powers := [(31, 1), (37, 1), (39, 1), (43, 1), (53, 1), (56, 1), (61, 1)] }, { coefficient := -1, powers := [(31, 1), (37, 1), (43, 1), (47, 1), (50, 1), (53, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (34, 1)] }, { coefficient := -1, powers := [(24, 1), (34, 1), (37, 1), (44, 1)] }, { coefficient := -1, powers := [(24, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (2, 1), (37, 1), (53, 1), (54, 1)] }, { coefficient := 1, powers := [(0, 1), (6, 1), (8, 1), (36, 1), (54, 1)] }, { coefficient := 1, powers := [(0, 1), (8, 1), (36, 1), (37, 1), (54, 1)] }, { coefficient := 1, powers := [(2, 1), (15, 1), (31, 1), (37, 1), (53, 2), (61, 1)] }, { coefficient := -1, powers := [(2, 1), (31, 1), (34, 1), (37, 2), (44, 1), (53, 1)] }, { coefficient := -1, powers := [(2, 1), (31, 1), (37, 1), (43, 1), (53, 2), (61, 1)] }, { coefficient := 1, powers := [(6, 1), (8, 1), (15, 1), (31, 1), (36, 1), (53, 1), (61, 1)] }, { coefficient := -1, powers := [(6, 1), (8, 1), (31, 1), (34, 1), (36, 1), (37, 1), (44, 1)] }, { coefficient := -1, powers := [(6, 1), (8, 1), (31, 1), (36, 1), (43, 1), (53, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (15, 1), (31, 1), (36, 1), (37, 1), (53, 1), (61, 1)] }, { coefficient := -1, powers := [(8, 1), (31, 1), (34, 1), (36, 1), (37, 2), (44, 1)] }, { coefficient := -1, powers := [(8, 1), (31, 1), (36, 1), (37, 1), (43, 1), (53, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (40, 1)] }, { coefficient := -1, powers := [(3, 1), (5, 1), (31, 1), (33, 1), (53, 1)] }, { coefficient := 1, powers := [(3, 1), (31, 1)] }, { coefficient := 1, powers := [(9, 1), (20, 1)] }, { coefficient := -1, powers := [(20, 1), (48, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (14, 1), (20, 1), (23, 1), (37, 1), (52, 1), (53, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (15, 1), (31, 1), (33, 1), (37, 1), (53, 1)] }, { coefficient := -1, powers := [(5, 1), (31, 1), (33, 1), (37, 1), (43, 1), (53, 1)] }, { coefficient := -1, powers := [(6, 1), (20, 1), (54, 1)] }, { coefficient := -1, powers := [(9, 1), (34, 1), (37, 1)] }, { coefficient := -1, powers := [(14, 1), (15, 1), (20, 1), (23, 1), (31, 1), (37, 1), (52, 1), (53, 2), (61, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1), (23, 1), (31, 1), (34, 1), (37, 2), (44, 1), (52, 1), (53, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1), (23, 1), (31, 1), (37, 1), (43, 1), (52, 1), (53, 2), (61, 1)] }, { coefficient := -1, powers := [(15, 1), (31, 1), (37, 1)] }, { coefficient := 1, powers := [(20, 1), (34, 1), (37, 1), (44, 1), (48, 1)] }, { coefficient := 1, powers := [(20, 1), (43, 1), (48, 1)] }]
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
    (values : Fin 62 → R) :
    ¬ ∀ index : Fin 31,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component1.SelectedLeafB6_2_3.selectedHasNoCommonZero

end Krenn.Component1.SelectedLeafB6_2_3
