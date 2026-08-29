import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component64.SelectedLeafB6_2

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "98c17bd8fcd60abaff7213231cae94ce575d2b40832b972f853ad0f6bd8becea"
def certificateSHA256 : String := "bbf6db55ef4754a5cba98a2a79a7c979d814c9d87652a15bb3b93b88ebb1e2bb"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 49 → Fin 641 := ![
  7,
  9,
  10,
  13,
  20,
  26,
  27,
  29,
  32,
  71,
  162,
  163,
  170,
  171,
  187,
  191,
  193,
  199,
  231,
  235,
  243,
  283,
  309,
  310,
  343,
  344,
  346,
  349,
  350,
  351,
  352,
  367,
  373,
  390,
  415,
  466,
  476,
  548,
  556,
  576,
  577,
  632,
  634,
  635,
  636,
  637,
  638,
  639,
  640
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 49 → SparsePoly (Fin 63) := ![
  [{ coefficient := 1, powers := [(5, 1), (31, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (28, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (23, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(31, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (33, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1)] }, { coefficient := 1, powers := [(24, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (52, 1)] }, { coefficient := 1, powers := [(20, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (58, 1)] }, { coefficient := 1, powers := [(18, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (30, 1)] }, { coefficient := 1, powers := [(30, 1), (34, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (24, 1)] }, { coefficient := 1, powers := [(18, 1), (20, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (23, 1)] }, { coefficient := 1, powers := [(23, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (20, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (52, 1)] }, { coefficient := 1, powers := [(27, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (31, 1), (49, 1)] }, { coefficient := 1, powers := [(5, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (23, 1), (58, 1)] }, { coefficient := 1, powers := [(23, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (28, 1), (42, 1)] }, { coefficient := 1, powers := [(8, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (24, 1), (42, 1)] }, { coefficient := 1, powers := [(13, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (24, 1), (41, 1)] }, { coefficient := 1, powers := [(19, 1), (20, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (24, 1), (42, 1)] }, { coefficient := 1, powers := [(18, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (41, 1)] }, { coefficient := 1, powers := [(20, 1), (41, 1)] }, { coefficient := 1, powers := [(24, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (48, 1)] }, { coefficient := 1, powers := [(20, 1), (48, 1)] }, { coefficient := 1, powers := [(24, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (46, 1)] }, { coefficient := 1, powers := [(11, 1), (25, 1), (46, 1)] }, { coefficient := 1, powers := [(17, 1), (21, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (46, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1)] }, { coefficient := 1, powers := [(19, 1), (23, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (53, 1)] }, { coefficient := 1, powers := [(8, 1), (30, 1)] }, { coefficient := 1, powers := [(13, 1), (27, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (59, 1)] }, { coefficient := 1, powers := [(13, 1), (46, 1)] }, { coefficient := 1, powers := [(19, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (59, 1)] }, { coefficient := 1, powers := [(13, 1), (56, 1)] }, { coefficient := 1, powers := [(19, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (41, 1), (52, 1)] }, { coefficient := 1, powers := [(20, 1), (41, 1), (52, 1)] }, { coefficient := 1, powers := [(20, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1), (47, 1)] }, { coefficient := 1, powers := [(6, 1), (28, 1), (46, 1)] }, { coefficient := 1, powers := [(9, 1), (24, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (39, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (54, 1)] }, { coefficient := 1, powers := [(13, 1), (23, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (28, 1), (56, 1)] }, { coefficient := 1, powers := [(8, 1), (28, 1), (46, 1)] }, { coefficient := 1, powers := [(19, 1), (28, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (53, 1)] }, { coefficient := 1, powers := [(27, 1), (39, 1)] }, { coefficient := 1, powers := [(27, 1), (45, 1), (48, 1)] }, { coefficient := 1, powers := [(30, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1), (47, 1)] }, { coefficient := 1, powers := [(6, 1), (28, 1), (43, 1)] }, { coefficient := 1, powers := [(9, 1), (24, 1), (43, 1)] }, { coefficient := 1, powers := [(47, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (41, 1), (52, 1)] }, { coefficient := 1, powers := [(23, 1), (56, 1)] }, { coefficient := 1, powers := [(27, 1), (46, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1)] }, { coefficient := 1, powers := [(6, 1), (58, 1)] }, { coefficient := 1, powers := [(24, 1), (38, 1)] }, { coefficient := 1, powers := [(24, 1), (43, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (40, 1)] }, { coefficient := 1, powers := [(3, 1), (31, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1)] }, { coefficient := 1, powers := [(20, 1), (54, 1)] }, { coefficient := 1, powers := [(24, 1), (40, 1)] }, { coefficient := 1, powers := [(31, 1), (34, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1)] }, { coefficient := 1, powers := [(6, 1), (28, 1)] }, { coefficient := 1, powers := [(9, 1), (24, 1)] }, { coefficient := 1, powers := [(20, 1), (47, 1)] }, { coefficient := 1, powers := [(24, 1), (37, 1)] }, { coefficient := 1, powers := [(28, 1), (34, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (34, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (37, 1), (54, 1)] }, { coefficient := 1, powers := [(0, 1), (40, 1), (47, 1)] }, { coefficient := 1, powers := [(3, 1), (24, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (28, 1), (54, 1)] }, { coefficient := 1, powers := [(3, 1), (31, 1), (47, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1), (57, 1)] }, { coefficient := 1, powers := [(6, 1), (28, 1), (40, 1)] }, { coefficient := 1, powers := [(6, 1), (31, 1), (37, 1)] }, { coefficient := 1, powers := [(9, 1), (20, 1), (54, 1)] }, { coefficient := 1, powers := [(9, 1), (24, 1), (40, 1)] }, { coefficient := 1, powers := [(9, 1), (31, 1), (34, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1), (47, 1)] }, { coefficient := 1, powers := [(14, 1), (24, 1), (37, 1)] }, { coefficient := 1, powers := [(14, 1), (28, 1), (34, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (36, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (46, 1), (53, 1)] }, { coefficient := 1, powers := [(5, 1), (27, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (53, 1)] }, { coefficient := 1, powers := [(8, 1), (23, 1), (59, 1)] }, { coefficient := 1, powers := [(8, 1), (30, 1), (46, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (39, 1)] }, { coefficient := 1, powers := [(13, 1), (23, 1), (56, 1)] }, { coefficient := 1, powers := [(13, 1), (27, 1), (46, 1)] }, { coefficient := 1, powers := [(13, 1), (33, 1), (36, 1)] }, { coefficient := 1, powers := [(19, 1), (23, 1), (53, 1)] }, { coefficient := 1, powers := [(19, 1), (27, 1), (39, 1)] }, { coefficient := 1, powers := [(19, 1), (30, 1), (36, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (60, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1), (61, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(37, 1)] }],
  [{ coefficient := 1, powers := [(38, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(39, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 49 → SparsePoly (Fin 63) := ![
  [{ coefficient := -1, powers := [(0, 1), (30, 1), (34, 1), (49, 1), (56, 1)] }, { coefficient := -1, powers := [(0, 1), (33, 1), (34, 1), (49, 1), (53, 1)] }, { coefficient := -1, powers := [(3, 1), (24, 1), (30, 1), (49, 1), (56, 1)] }, { coefficient := -1, powers := [(3, 1), (24, 1), (33, 1), (49, 1), (53, 1)] }, { coefficient := -1, powers := [(6, 1), (20, 1), (30, 1), (49, 1), (56, 1)] }, { coefficient := -1, powers := [(6, 1), (20, 1), (33, 1), (49, 1), (53, 1)] }, { coefficient := 1, powers := [(9, 1), (27, 1), (34, 1), (59, 1)] }, { coefficient := 1, powers := [(9, 1), (30, 1), (34, 1), (56, 1)] }, { coefficient := 2, powers := [(9, 1), (33, 1), (34, 1), (53, 1)] }, { coefficient := -1, powers := [(27, 1), (34, 1), (47, 1), (59, 1)] }, { coefficient := -1, powers := [(30, 1), (34, 1), (47, 1), (56, 1)] }, { coefficient := -2, powers := [(33, 1), (34, 1), (47, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (23, 1), (34, 1), (42, 1), (59, 1)] }, { coefficient := -2, powers := [(0, 1), (30, 1), (34, 1), (42, 1), (46, 1)] }, { coefficient := -1, powers := [(3, 1), (23, 1), (24, 1), (42, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (23, 1), (54, 1), (59, 1)] }, { coefficient := -2, powers := [(3, 1), (24, 1), (30, 1), (42, 1), (46, 1)] }, { coefficient := 1, powers := [(3, 1), (30, 1), (46, 1), (54, 1)] }, { coefficient := -1, powers := [(6, 1), (20, 1), (23, 1), (42, 1), (59, 1)] }, { coefficient := -2, powers := [(6, 1), (20, 1), (30, 1), (42, 1), (46, 1)] }, { coefficient := 1, powers := [(14, 1), (23, 1), (34, 1), (59, 1)] }, { coefficient := 1, powers := [(14, 1), (30, 1), (34, 1), (46, 1)] }, { coefficient := -1, powers := [(23, 1), (24, 1), (34, 1), (40, 1), (43, 1), (59, 1)] }, { coefficient := -1, powers := [(23, 1), (34, 1), (40, 1), (59, 1)] }, { coefficient := -1, powers := [(24, 1), (30, 1), (34, 1), (40, 1), (43, 1), (46, 1)] }, { coefficient := -1, powers := [(30, 1), (34, 1), (40, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (24, 1), (30, 1), (40, 1)] }],
  [{ coefficient := 2, powers := [(9, 1), (13, 1), (20, 1), (25, 1), (27, 1), (54, 1), (61, 1)] }, { coefficient := -2, powers := [(13, 1), (20, 1), (24, 1), (25, 1), (27, 1), (40, 1), (43, 1), (47, 1), (61, 1)] }],
  [{ coefficient := -2, powers := [(9, 1), (13, 1), (20, 1), (21, 1), (52, 1), (54, 1), (61, 1)] }, { coefficient := 2, powers := [(13, 1), (20, 1), (21, 1), (24, 1), (40, 1), (43, 1), (47, 1), (52, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (13, 1), (34, 1), (52, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (13, 1), (40, 1), (47, 1), (52, 1)] }, { coefficient := -1, powers := [(3, 1), (13, 1), (24, 1), (52, 1), (57, 1)] }, { coefficient := -1, powers := [(3, 1), (13, 1), (28, 1), (52, 1), (54, 1)] }, { coefficient := -1, powers := [(6, 1), (13, 1), (20, 1), (52, 1), (57, 1)] }, { coefficient := -1, powers := [(9, 1), (13, 1), (20, 1), (52, 1), (54, 1)] }, { coefficient := -1, powers := [(13, 1), (14, 1), (28, 1), (34, 1), (52, 1)] }, { coefficient := 1, powers := [(13, 1), (20, 1), (24, 1), (40, 1), (43, 1), (47, 1), (52, 1)] }, { coefficient := 1, powers := [(13, 1), (20, 1), (40, 1), (47, 1), (52, 1)] }, { coefficient := 1, powers := [(13, 1), (20, 1), (47, 1), (52, 1), (54, 1)] }, { coefficient := 1, powers := [(13, 1), (24, 1), (28, 1), (34, 1), (40, 1), (43, 1), (52, 1)] }, { coefficient := 1, powers := [(13, 1), (28, 1), (34, 1), (40, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (13, 1), (40, 1), (56, 1)] }, { coefficient := 2, powers := [(0, 1), (19, 1), (40, 1), (53, 1)] }, { coefficient := -2, powers := [(13, 1), (14, 1), (20, 1), (56, 1)] }, { coefficient := 1, powers := [(13, 1), (20, 1), (40, 1), (56, 1)] }, { coefficient := 2, powers := [(19, 1), (20, 1), (40, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (19, 1), (34, 1), (45, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (19, 1), (40, 1), (45, 1), (47, 1)] }, { coefficient := -1, powers := [(3, 1), (19, 1), (24, 1), (45, 1), (57, 1)] }, { coefficient := -1, powers := [(6, 1), (19, 1), (20, 1), (45, 1), (57, 1)] }, { coefficient := -1, powers := [(9, 1), (19, 1), (20, 1), (45, 1), (54, 1)] }, { coefficient := -1, powers := [(9, 1), (19, 1), (31, 1), (34, 1), (45, 1)] }, { coefficient := 1, powers := [(19, 1), (20, 1), (24, 1), (40, 1), (43, 1), (45, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (20, 1), (40, 1), (45, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (20, 1), (45, 1), (47, 1), (54, 1)] }, { coefficient := 1, powers := [(19, 1), (31, 1), (34, 1), (45, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (13, 1), (33, 1), (34, 1)] }, { coefficient := -1, powers := [(13, 1), (33, 1), (34, 1), (47, 1)] }],
  [{ coefficient := 2, powers := [(14, 1), (18, 1), (20, 1), (45, 1), (47, 1), (53, 1), (62, 1)] }],
  [{ coefficient := 2, powers := [(13, 1), (27, 1), (40, 1), (47, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (9, 1), (30, 1), (41, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (24, 1), (30, 1), (40, 1), (41, 1), (43, 1), (47, 1)] }, { coefficient := 1, powers := [(9, 1), (13, 1), (23, 1), (41, 1), (54, 1)] }, { coefficient := -1, powers := [(13, 1), (23, 1), (24, 1), (40, 1), (41, 1), (43, 1), (47, 1)] }],
  [{ coefficient := -2, powers := [(6, 1), (14, 1), (20, 1), (33, 1), (47, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (28, 1), (40, 1), (56, 1)] }],
  [{ coefficient := -2, powers := [(20, 1), (27, 1), (42, 1), (46, 1), (47, 1)] }],
  [{ coefficient := 2, powers := [(13, 1), (20, 1), (47, 1), (56, 1)] }, { coefficient := 2, powers := [(19, 1), (20, 1), (47, 1), (53, 1)] }],
  [{ coefficient := -2, powers := [(9, 1), (23, 1), (24, 1), (41, 1), (53, 1), (54, 1), (60, 1)] }, { coefficient := 2, powers := [(20, 1), (27, 1), (42, 1), (46, 1), (47, 1), (48, 1)] }, { coefficient := -2, powers := [(20, 1), (27, 1), (46, 1), (47, 1), (48, 1), (54, 1), (60, 1)] }, { coefficient := 2, powers := [(23, 1), (24, 2), (40, 1), (41, 1), (43, 1), (47, 1), (53, 1), (60, 1)] }],
  [{ coefficient := 2, powers := [(9, 1), (13, 1), (17, 1), (20, 1), (21, 1), (54, 1), (61, 1)] }, { coefficient := -2, powers := [(13, 1), (17, 1), (20, 1), (21, 1), (24, 1), (40, 1), (43, 1), (47, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (30, 1), (34, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (33, 1), (34, 1), (53, 1)] }, { coefficient := 1, powers := [(3, 1), (24, 1), (30, 1), (56, 1)] }, { coefficient := 1, powers := [(3, 1), (24, 1), (33, 1), (53, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1), (30, 1), (56, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1), (33, 1), (53, 1)] }],
  [{ coefficient := -2, powers := [(14, 1), (19, 1), (20, 1), (47, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (23, 1), (34, 1), (59, 1)] }, { coefficient := 2, powers := [(0, 1), (30, 1), (34, 1), (46, 1)] }, { coefficient := 1, powers := [(3, 1), (23, 1), (24, 1), (59, 1)] }, { coefficient := 2, powers := [(3, 1), (24, 1), (30, 1), (46, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1), (23, 1), (59, 1)] }, { coefficient := 2, powers := [(6, 1), (20, 1), (30, 1), (46, 1)] }],
  [{ coefficient := 2, powers := [(20, 1), (27, 1), (46, 1), (47, 1)] }],
  [{ coefficient := -2, powers := [(9, 1), (23, 1), (53, 1), (54, 1)] }, { coefficient := 2, powers := [(23, 1), (24, 1), (40, 1), (43, 1), (47, 1), (53, 1)] }],
  [{ coefficient := -2, powers := [(20, 1), (27, 1), (46, 1), (47, 1), (48, 1)] }],
  [{ coefficient := 2, powers := [(9, 1), (18, 1), (23, 1), (24, 1), (53, 1), (54, 1), (60, 1)] }, { coefficient := -2, powers := [(18, 1), (23, 1), (24, 2), (40, 1), (43, 1), (47, 1), (53, 1), (60, 1)] }],
  [{ coefficient := 2, powers := [(18, 1), (20, 1), (27, 1), (46, 1), (47, 1), (54, 1), (60, 1)] }],
  [{ coefficient := -2, powers := [(9, 1), (13, 1), (20, 1), (27, 1), (54, 1), (61, 1)] }, { coefficient := 2, powers := [(13, 1), (20, 1), (24, 1), (27, 1), (40, 1), (43, 1), (47, 1), (61, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (14, 1), (20, 1), (43, 1), (47, 1), (53, 1)] }, { coefficient := -1, powers := [(0, 1), (40, 1), (47, 1), (53, 1)] }, { coefficient := 1, powers := [(3, 1), (28, 1), (53, 1), (54, 1)] }, { coefficient := 1, powers := [(9, 1), (20, 1), (53, 1), (54, 1)] }, { coefficient := -1, powers := [(9, 1), (31, 1), (34, 1), (53, 1)] }, { coefficient := -2, powers := [(14, 1), (20, 1), (24, 1), (38, 1), (47, 1), (53, 1)] }, { coefficient := -2, powers := [(14, 1), (20, 1), (24, 1), (43, 1), (47, 1), (53, 1)] }, { coefficient := -2, powers := [(14, 1), (20, 1), (47, 1), (53, 1)] }, { coefficient := 1, powers := [(14, 1), (28, 1), (34, 1), (53, 1)] }, { coefficient := -1, powers := [(20, 1), (24, 1), (40, 1), (43, 1), (47, 1), (53, 1)] }, { coefficient := -1, powers := [(20, 1), (40, 1), (47, 1), (53, 1)] }, { coefficient := -1, powers := [(20, 1), (47, 1), (53, 1), (54, 1)] }, { coefficient := -1, powers := [(24, 1), (28, 1), (34, 1), (40, 1), (43, 1), (53, 1)] }, { coefficient := -1, powers := [(28, 1), (34, 1), (40, 1), (53, 1)] }, { coefficient := 1, powers := [(31, 1), (34, 1), (47, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (34, 1), (46, 1), (57, 1)] }, { coefficient := -1, powers := [(0, 1), (40, 1), (46, 1), (47, 1)] }, { coefficient := -1, powers := [(3, 1), (24, 1), (46, 1), (57, 1)] }, { coefficient := -1, powers := [(3, 1), (28, 1), (46, 1), (54, 1)] }, { coefficient := -1, powers := [(6, 1), (20, 1), (46, 1), (57, 1)] }, { coefficient := 1, powers := [(9, 1), (20, 1), (46, 1), (54, 1)] }, { coefficient := 1, powers := [(9, 1), (31, 1), (34, 1), (46, 1)] }, { coefficient := -1, powers := [(14, 1), (28, 1), (34, 1), (46, 1)] }, { coefficient := -1, powers := [(20, 1), (24, 1), (40, 1), (43, 1), (46, 1), (47, 1)] }, { coefficient := -1, powers := [(20, 1), (40, 1), (46, 1), (47, 1)] }, { coefficient := -1, powers := [(20, 1), (46, 1), (47, 1), (54, 1)] }, { coefficient := 1, powers := [(24, 1), (28, 1), (34, 1), (40, 1), (43, 1), (46, 1)] }, { coefficient := 1, powers := [(28, 1), (34, 1), (40, 1), (46, 1)] }, { coefficient := -1, powers := [(31, 1), (34, 1), (46, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (27, 1), (34, 1), (57, 1)] }, { coefficient := -1, powers := [(0, 1), (27, 1), (40, 1), (47, 1)] }, { coefficient := 1, powers := [(3, 1), (24, 1), (27, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (27, 1), (28, 1), (54, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1), (27, 1), (57, 1)] }, { coefficient := 1, powers := [(9, 1), (20, 1), (27, 1), (54, 1)] }, { coefficient := 1, powers := [(14, 1), (27, 1), (28, 1), (34, 1)] }, { coefficient := -1, powers := [(20, 1), (24, 1), (27, 1), (40, 1), (43, 1), (47, 1)] }, { coefficient := -1, powers := [(20, 1), (27, 1), (40, 1), (47, 1)] }, { coefficient := -1, powers := [(20, 1), (27, 1), (47, 1), (54, 1)] }, { coefficient := -1, powers := [(24, 1), (27, 1), (28, 1), (34, 1), (40, 1), (43, 1)] }, { coefficient := -1, powers := [(27, 1), (28, 1), (34, 1), (40, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (23, 1), (40, 1), (47, 1)] }, { coefficient := 1, powers := [(9, 1), (20, 1), (23, 1), (54, 1)] }, { coefficient := 1, powers := [(9, 1), (23, 1), (31, 1), (34, 1)] }, { coefficient := -1, powers := [(20, 1), (23, 1), (24, 1), (40, 1), (43, 1), (47, 1)] }, { coefficient := -1, powers := [(20, 1), (23, 1), (40, 1), (47, 1)] }, { coefficient := -1, powers := [(20, 1), (23, 1), (47, 1), (54, 1)] }, { coefficient := -1, powers := [(23, 1), (31, 1), (34, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (9, 1), (30, 1), (54, 1)] }, { coefficient := -1, powers := [(5, 1), (24, 1), (30, 1), (40, 1), (43, 1), (47, 1)] }, { coefficient := -1, powers := [(9, 1), (13, 1), (23, 1), (54, 1)] }, { coefficient := 1, powers := [(13, 1), (23, 1), (24, 1), (40, 1), (43, 1), (47, 1)] }],
  [{ coefficient := -2, powers := [(13, 1), (20, 1), (27, 1), (40, 1), (43, 1)] }, { coefficient := 2, powers := [(13, 1), (24, 1), (27, 1), (40, 1), (43, 1)] }],
  [{ coefficient := -1, powers := [(20, 1), (47, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (30, 1), (54, 1)] }, { coefficient := 1, powers := [(14, 1), (30, 1), (34, 1)] }, { coefficient := -1, powers := [(24, 1), (30, 1), (34, 1), (40, 1), (43, 1)] }, { coefficient := -1, powers := [(30, 1), (34, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (19, 1), (34, 1), (57, 1)] }, { coefficient := -1, powers := [(0, 1), (19, 1), (40, 1), (47, 1)] }, { coefficient := 1, powers := [(3, 1), (19, 1), (24, 1), (57, 1)] }, { coefficient := 1, powers := [(6, 1), (19, 1), (20, 1), (57, 1)] }, { coefficient := 1, powers := [(9, 1), (19, 1), (20, 1), (54, 1)] }, { coefficient := 1, powers := [(9, 1), (19, 1), (31, 1), (34, 1)] }, { coefficient := -1, powers := [(19, 1), (20, 1), (24, 1), (40, 1), (43, 1), (47, 1)] }, { coefficient := -1, powers := [(19, 1), (20, 1), (40, 1), (47, 1)] }, { coefficient := -1, powers := [(19, 1), (20, 1), (47, 1), (54, 1)] }, { coefficient := -1, powers := [(19, 1), (31, 1), (34, 1), (47, 1)] }],
  [{ coefficient := 2, powers := [(13, 1), (20, 1), (27, 1), (40, 1), (46, 1)] }, { coefficient := -2, powers := [(13, 1), (24, 1), (27, 1), (40, 1), (46, 1)] }, { coefficient := -1, powers := [(24, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (13, 1), (34, 1), (57, 1)] }, { coefficient := -1, powers := [(0, 1), (13, 1), (40, 1), (47, 1)] }, { coefficient := 1, powers := [(3, 1), (13, 1), (24, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (13, 1), (28, 1), (54, 1)] }, { coefficient := 1, powers := [(6, 1), (13, 1), (20, 1), (57, 1)] }, { coefficient := 1, powers := [(9, 1), (13, 1), (20, 1), (54, 1)] }, { coefficient := 1, powers := [(13, 1), (14, 1), (28, 1), (34, 1)] }, { coefficient := -1, powers := [(13, 1), (20, 1), (24, 1), (40, 1), (43, 1), (47, 1)] }, { coefficient := -1, powers := [(13, 1), (20, 1), (40, 1), (47, 1)] }, { coefficient := -1, powers := [(13, 1), (20, 1), (47, 1), (54, 1)] }, { coefficient := -1, powers := [(13, 1), (24, 1), (28, 1), (34, 1), (40, 1), (43, 1)] }, { coefficient := -1, powers := [(13, 1), (28, 1), (34, 1), (40, 1)] }],
  [{ coefficient := 2, powers := [(5, 1), (14, 1), (20, 1), (33, 1), (47, 1), (53, 1)] }, { coefficient := 2, powers := [(14, 1), (19, 1), (20, 1), (23, 1), (47, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(47, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (30, 1), (40, 1), (56, 1)] }, { coefficient := 1, powers := [(24, 1), (40, 1), (43, 1)] }, { coefficient := 1, powers := [(40, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(0, 1), (34, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (40, 1), (47, 1)] }, { coefficient := -1, powers := [(3, 1), (24, 1), (57, 1)] }, { coefficient := -1, powers := [(3, 1), (28, 1), (54, 1)] }, { coefficient := -1, powers := [(6, 1), (20, 1), (57, 1)] }, { coefficient := -1, powers := [(9, 1), (20, 1), (54, 1)] }, { coefficient := -1, powers := [(9, 1), (31, 1), (34, 1)] }, { coefficient := -1, powers := [(14, 1), (28, 1), (34, 1)] }, { coefficient := 1, powers := [(20, 1), (24, 1), (40, 1), (43, 1), (47, 1)] }, { coefficient := 1, powers := [(20, 1), (40, 1), (47, 1)] }, { coefficient := 1, powers := [(20, 1), (47, 1), (54, 1)] }, { coefficient := 1, powers := [(24, 1), (28, 1), (34, 1), (40, 1), (43, 1)] }, { coefficient := 1, powers := [(28, 1), (34, 1), (40, 1)] }, { coefficient := 1, powers := [(31, 1), (34, 1), (47, 1)] }],
  [{ coefficient := -2, powers := [(9, 1), (18, 1), (23, 1), (24, 1), (41, 1), (53, 1), (54, 1)] }, { coefficient := -2, powers := [(18, 1), (20, 1), (27, 1), (46, 1), (47, 1), (48, 1), (54, 1)] }, { coefficient := 2, powers := [(18, 1), (23, 1), (24, 2), (40, 1), (41, 1), (43, 1), (47, 1), (53, 1)] }],
  [{ coefficient := 2, powers := [(9, 1), (13, 1), (20, 1), (27, 1), (46, 1), (54, 1)] }, { coefficient := -2, powers := [(13, 1), (20, 1), (24, 1), (27, 1), (40, 1), (43, 1), (46, 1), (47, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (14, 1), (20, 1), (43, 1), (46, 1), (47, 1), (53, 1)] }, { coefficient := 1, powers := [(0, 1), (34, 1), (36, 1), (57, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (34, 1), (39, 1), (56, 1), (57, 1)] }, { coefficient := 2, powers := [(0, 1), (34, 1), (46, 1), (53, 1), (57, 1)] }, { coefficient := -1, powers := [(0, 1), (36, 1), (40, 1), (47, 1), (59, 1)] }, { coefficient := -1, powers := [(0, 1), (39, 1), (40, 1), (47, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (40, 1), (46, 1), (47, 1), (53, 1)] }, { coefficient := 1, powers := [(3, 1), (24, 1), (36, 1), (57, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (24, 1), (39, 1), (56, 1), (57, 1)] }, { coefficient := 2, powers := [(3, 1), (24, 1), (46, 1), (53, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (28, 1), (36, 1), (54, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (28, 1), (39, 1), (54, 1), (56, 1)] }, { coefficient := 1, powers := [(3, 1), (28, 1), (46, 1), (53, 1), (54, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1), (36, 1), (57, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1), (39, 1), (56, 1), (57, 1)] }, { coefficient := 2, powers := [(6, 1), (20, 1), (46, 1), (53, 1), (57, 1)] }, { coefficient := 1, powers := [(9, 1), (20, 1), (36, 1), (54, 1), (59, 1)] }, { coefficient := 1, powers := [(9, 1), (20, 1), (39, 1), (54, 1), (56, 1)] }, { coefficient := -1, powers := [(9, 1), (20, 1), (46, 1), (53, 1), (54, 1)] }, { coefficient := 1, powers := [(9, 1), (31, 1), (34, 1), (36, 1), (59, 1)] }, { coefficient := 1, powers := [(9, 1), (31, 1), (34, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(9, 1), (31, 1), (34, 1), (46, 1), (53, 1)] }, { coefficient := 2, powers := [(14, 1), (20, 1), (24, 1), (38, 1), (46, 1), (47, 1), (53, 1)] }, { coefficient := 2, powers := [(14, 1), (20, 1), (24, 1), (43, 1), (46, 1), (47, 1), (53, 1)] }, { coefficient := 2, powers := [(14, 1), (20, 1), (46, 1), (47, 1), (53, 1)] }, { coefficient := 1, powers := [(14, 1), (28, 1), (34, 1), (36, 1), (59, 1)] }, { coefficient := 1, powers := [(14, 1), (28, 1), (34, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(14, 1), (28, 1), (34, 1), (46, 1), (53, 1)] }, { coefficient := -1, powers := [(20, 1), (24, 1), (36, 1), (40, 1), (43, 1), (47, 1), (59, 1)] }, { coefficient := -1, powers := [(20, 1), (24, 1), (39, 1), (40, 1), (43, 1), (47, 1), (56, 1)] }, { coefficient := 1, powers := [(20, 1), (24, 1), (40, 1), (43, 1), (46, 1), (47, 1), (53, 1)] }, { coefficient := -1, powers := [(20, 1), (36, 1), (40, 1), (47, 1), (59, 1)] }, { coefficient := -1, powers := [(20, 1), (36, 1), (47, 1), (54, 1), (59, 1)] }, { coefficient := -1, powers := [(20, 1), (39, 1), (40, 1), (47, 1), (56, 1)] }, { coefficient := 1, powers := [(20, 1), (40, 1), (46, 1), (47, 1), (53, 1)] }, { coefficient := 1, powers := [(20, 1), (46, 1), (47, 1), (53, 1), (54, 1)] }, { coefficient := -1, powers := [(24, 1), (28, 1), (34, 1), (36, 1), (40, 1), (43, 1), (59, 1)] }, { coefficient := -1, powers := [(24, 1), (28, 1), (34, 1), (39, 1), (40, 1), (43, 1), (56, 1)] }, { coefficient := -1, powers := [(24, 1), (28, 1), (34, 1), (40, 1), (43, 1), (46, 1), (53, 1)] }, { coefficient := -1, powers := [(28, 1), (34, 1), (36, 1), (40, 1), (59, 1)] }, { coefficient := -1, powers := [(28, 1), (34, 1), (39, 1), (40, 1), (56, 1)] }, { coefficient := -1, powers := [(28, 1), (34, 1), (40, 1), (46, 1), (53, 1)] }, { coefficient := -1, powers := [(31, 1), (34, 1), (36, 1), (47, 1), (59, 1)] }, { coefficient := -1, powers := [(31, 1), (34, 1), (39, 1), (47, 1), (56, 1)] }, { coefficient := -1, powers := [(31, 1), (34, 1), (46, 1), (47, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (24, 1), (30, 1), (40, 1), (56, 1)] }, { coefficient := 1, powers := [(6, 1), (31, 1)] }, { coefficient := 1, powers := [(14, 1), (24, 1)] }, { coefficient := -1, powers := [(24, 2), (40, 1), (43, 1)] }, { coefficient := -1, powers := [(24, 1), (40, 1)] }],
  [{ coefficient := -2, powers := [(6, 1), (14, 1), (18, 1), (20, 1), (33, 1), (45, 1), (47, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (8, 1), (33, 1), (34, 1), (57, 1)] }, { coefficient := -1, powers := [(0, 1), (8, 1), (33, 1), (40, 1), (47, 1)] }, { coefficient := -1, powers := [(0, 1), (19, 1), (27, 1), (34, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (19, 1), (27, 1), (40, 1), (47, 1)] }, { coefficient := 1, powers := [(3, 1), (8, 1), (24, 1), (33, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (8, 1), (28, 1), (33, 1), (54, 1)] }, { coefficient := -1, powers := [(3, 1), (19, 1), (24, 1), (27, 1), (57, 1)] }, { coefficient := 1, powers := [(6, 1), (8, 1), (20, 1), (33, 1), (57, 1)] }, { coefficient := -1, powers := [(6, 1), (19, 1), (20, 1), (27, 1), (57, 1)] }, { coefficient := 1, powers := [(8, 1), (9, 1), (20, 1), (33, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (9, 1), (31, 1), (33, 1), (34, 1)] }, { coefficient := 1, powers := [(8, 1), (14, 1), (28, 1), (33, 1), (34, 1)] }, { coefficient := -1, powers := [(8, 1), (20, 1), (24, 1), (33, 1), (40, 1), (43, 1), (47, 1)] }, { coefficient := -1, powers := [(8, 1), (20, 1), (33, 1), (40, 1), (47, 1)] }, { coefficient := -1, powers := [(8, 1), (20, 1), (33, 1), (47, 1), (54, 1)] }, { coefficient := -1, powers := [(8, 1), (24, 1), (28, 1), (33, 1), (34, 1), (40, 1), (43, 1)] }, { coefficient := -1, powers := [(8, 1), (28, 1), (33, 1), (34, 1), (40, 1)] }, { coefficient := -1, powers := [(8, 1), (31, 1), (33, 1), (34, 1), (47, 1)] }, { coefficient := -1, powers := [(9, 1), (19, 1), (20, 1), (27, 1), (54, 1)] }, { coefficient := 1, powers := [(19, 1), (20, 1), (24, 1), (27, 1), (40, 1), (43, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (20, 1), (27, 1), (40, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (20, 1), (27, 1), (47, 1), (54, 1)] }]
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
    ¬ ∀ index : Fin 49,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component64.SelectedLeafB6_2.selectedHasNoCommonZero

end Krenn.Component64.SelectedLeafB6_2
