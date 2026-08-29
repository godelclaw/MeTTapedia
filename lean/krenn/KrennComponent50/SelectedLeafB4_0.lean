import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component50.SelectedLeafB4_0

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "1aeb3b777eba76fd16979aa2b99cf27ae4b5291024413bfe4fd772814bede070"
def certificateSHA256 : String := "a951a8e714ec0ec01acc621a9f44f1fa9925da81164de2a54424369d40fec602"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 46 → Fin 641 := ![
  2,
  3,
  4,
  14,
  16,
  24,
  25,
  26,
  58,
  162,
  174,
  175,
  187,
  188,
  196,
  228,
  241,
  243,
  348,
  349,
  350,
  355,
  359,
  362,
  363,
  374,
  387,
  389,
  401,
  406,
  432,
  443,
  463,
  481,
  535,
  556,
  560,
  576,
  577,
  609,
  632,
  634,
  637,
  638,
  639,
  640
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 46 → SparsePoly (Fin 61) := ![
  [{ coefficient := 1, powers := [(3, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (20, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (33, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1)] }, { coefficient := 1, powers := [(25, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (34, 1)] }, { coefficient := 1, powers := [(18, 1), (21, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (33, 1)] }, { coefficient := 1, powers := [(33, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (21, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (52, 1)] }, { coefficient := -1, powers := [(18, 1), (26, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (20, 1)] }, { coefficient := 1, powers := [(18, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (30, 1), (58, 1)] }, { coefficient := 1, powers := [(30, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (34, 1), (49, 1)] }, { coefficient := 1, powers := [(5, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (24, 1), (58, 1)] }, { coefficient := 1, powers := [(24, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (47, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (53, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1)] }, { coefficient := 1, powers := [(14, 1), (30, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (57, 1)] }, { coefficient := 1, powers := [(9, 1), (54, 1)] }, { coefficient := 1, powers := [(15, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (44, 1)] }, { coefficient := 1, powers := [(14, 1), (55, 1)] }, { coefficient := 1, powers := [(18, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (45, 1)] }, { coefficient := 1, powers := [(19, 1), (41, 1)] }, { coefficient := 1, powers := [(19, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (53, 1)] }, { coefficient := 1, powers := [(30, 1), (42, 1)] }, { coefficient := 1, powers := [(33, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (56, 1)] }, { coefficient := 1, powers := [(30, 1), (47, 1)] }, { coefficient := 1, powers := [(36, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1), (52, 1)] }, { coefficient := 1, powers := [(21, 1), (56, 1)] }, { coefficient := 1, powers := [(26, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (39, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (57, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (42, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (54, 1)] }, { coefficient := 1, powers := [(14, 1), (24, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (34, 1), (53, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (42, 1)] }, { coefficient := 1, powers := [(14, 1), (34, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (24, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (33, 1), (47, 1)] }, { coefficient := 1, powers := [(6, 1), (36, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (20, 1), (55, 1)] }, { coefficient := 1, powers := [(14, 1)] }, { coefficient := 1, powers := [(18, 1), (20, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (25, 1), (45, 1)] }, { coefficient := 1, powers := [(19, 1), (25, 1), (41, 1)] }, { coefficient := 1, powers := [(19, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (31, 1)] }, { coefficient := 1, powers := [(13, 1), (26, 1)] }, { coefficient := 1, powers := [(18, 1), (20, 1), (26, 1), (49, 1)] }, { coefficient := 1, powers := [(18, 1), (26, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1), (48, 1)] }, { coefficient := 1, powers := [(6, 1), (31, 1), (44, 1)] }, { coefficient := 1, powers := [(9, 1), (25, 1), (44, 1)] }, { coefficient := 1, powers := [(48, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (20, 1), (55, 1)] }, { coefficient := 1, powers := [(13, 1)] }, { coefficient := 1, powers := [(18, 1), (20, 1), (49, 1)] }, { coefficient := 1, powers := [(18, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1)] }, { coefficient := 1, powers := [(6, 1), (58, 1)] }, { coefficient := 1, powers := [(25, 1), (41, 1)] }, { coefficient := 1, powers := [(25, 1), (44, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (41, 1), (54, 1)] }, { coefficient := 1, powers := [(6, 1), (34, 1), (41, 1)] }, { coefficient := 1, powers := [(15, 1), (25, 1), (41, 1)] }, { coefficient := 1, powers := [(15, 1)] }, { coefficient := 1, powers := [(54, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1)] }, { coefficient := 1, powers := [(3, 1), (34, 1)] }, { coefficient := 1, powers := [(15, 1), (20, 1)] }, { coefficient := 1, powers := [(20, 1), (54, 1)] }, { coefficient := 1, powers := [(25, 1), (43, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (48, 1)] }, { coefficient := 1, powers := [(6, 1), (31, 1)] }, { coefficient := 1, powers := [(9, 1), (25, 1)] }, { coefficient := 1, powers := [(20, 1), (48, 1)] }, { coefficient := 1, powers := [(25, 1), (40, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (31, 1), (56, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1), (47, 1)] }, { coefficient := 1, powers := [(13, 1), (21, 1), (56, 1)] }, { coefficient := 1, powers := [(13, 1), (26, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (21, 1), (26, 1), (49, 1)] }, { coefficient := 1, powers := [(19, 1), (31, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (37, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (40, 1), (54, 1)] }, { coefficient := 1, powers := [(0, 1), (43, 1), (48, 1)] }, { coefficient := 1, powers := [(3, 1), (25, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (31, 1), (54, 1)] }, { coefficient := 1, powers := [(3, 1), (34, 1), (48, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1), (57, 1)] }, { coefficient := 1, powers := [(6, 1), (31, 1), (43, 1)] }, { coefficient := 1, powers := [(6, 1), (34, 1), (40, 1)] }, { coefficient := 1, powers := [(9, 1), (20, 1), (54, 1)] }, { coefficient := 1, powers := [(9, 1), (25, 1), (43, 1)] }, { coefficient := 1, powers := [(9, 1), (34, 1), (37, 1)] }, { coefficient := 1, powers := [(15, 1), (20, 1), (48, 1)] }, { coefficient := 1, powers := [(15, 1), (25, 1), (40, 1)] }, { coefficient := 1, powers := [(15, 1), (31, 1), (37, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (39, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (42, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (47, 1), (53, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1), (53, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (59, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (47, 1)] }, { coefficient := 1, powers := [(8, 1), (36, 1), (42, 1)] }, { coefficient := 1, powers := [(14, 1), (24, 1), (56, 1)] }, { coefficient := 1, powers := [(14, 1), (30, 1), (47, 1)] }, { coefficient := 1, powers := [(14, 1), (36, 1), (39, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (53, 1)] }, { coefficient := 1, powers := [(19, 1), (30, 1), (42, 1)] }, { coefficient := 1, powers := [(19, 1), (33, 1), (39, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(40, 1)] }],
  [{ coefficient := 1, powers := [(41, 1)] }],
  [{ coefficient := 1, powers := [(42, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 46 → SparsePoly (Fin 61) := ![
  [{ coefficient := 1, powers := [(0, 1), (5, 1), (30, 1), (43, 1), (48, 1), (58, 1)] }, { coefficient := -1, powers := [(3, 1), (5, 1), (30, 1), (31, 1), (54, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (20, 1), (30, 1), (43, 1), (48, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (25, 1), (30, 1), (43, 1), (48, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (31, 1), (37, 1), (43, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (31, 1), (37, 1), (54, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (9, 1), (24, 1), (34, 1), (37, 1), (58, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (34, 1), (37, 1), (48, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (33, 1), (37, 1), (47, 1)] }, { coefficient := 1, powers := [(3, 1), (25, 1), (33, 1), (47, 1)] }],
  [{ coefficient := -1, powers := [(9, 1), (24, 1), (34, 1), (37, 1), (44, 1), (56, 1)] }, { coefficient := -1, powers := [(9, 1), (24, 1), (34, 1), (37, 1), (55, 1), (56, 1)] }, { coefficient := 1, powers := [(24, 1), (34, 1), (37, 1), (44, 1), (48, 1), (56, 1)] }, { coefficient := 1, powers := [(24, 1), (34, 1), (37, 1), (48, 1), (55, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (24, 1), (31, 1), (56, 1)] }, { coefficient := 1, powers := [(24, 1), (31, 1), (37, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (21, 1), (33, 1), (37, 1), (49, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (21, 1), (36, 1), (37, 1), (49, 1), (53, 1)] }, { coefficient := 1, powers := [(3, 1), (21, 1), (25, 1), (33, 1), (49, 1), (56, 1)] }, { coefficient := 1, powers := [(3, 1), (21, 1), (25, 1), (36, 1), (49, 1), (53, 1)] }, { coefficient := -1, powers := [(9, 1), (21, 1), (30, 1), (37, 1), (59, 1)] }, { coefficient := -1, powers := [(9, 1), (21, 1), (33, 1), (37, 1), (56, 1)] }, { coefficient := 1, powers := [(21, 1), (30, 1), (37, 1), (48, 1), (59, 1)] }, { coefficient := 1, powers := [(21, 1), (33, 1), (37, 1), (48, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (24, 1), (43, 1), (48, 1), (50, 1), (53, 1)] }, { coefficient := 1, powers := [(3, 1), (24, 1), (31, 1), (50, 1), (53, 1), (54, 1)] }, { coefficient := -1, powers := [(20, 1), (24, 1), (43, 1), (48, 1), (50, 1), (53, 1)] }, { coefficient := -1, powers := [(24, 1), (25, 1), (43, 1), (48, 1), (50, 1), (53, 1)] }, { coefficient := -1, powers := [(24, 1), (31, 1), (37, 1), (43, 1), (50, 1), (53, 1)] }, { coefficient := -1, powers := [(24, 1), (31, 1), (37, 1), (50, 1), (53, 1), (54, 1)] }, { coefficient := -1, powers := [(31, 1), (33, 1), (37, 1), (39, 1), (43, 1), (50, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (5, 1), (33, 1), (43, 1), (44, 1), (48, 1)] }, { coefficient := -1, powers := [(5, 1), (25, 1), (33, 1), (43, 1), (44, 1), (48, 1)] }, { coefficient := -1, powers := [(5, 1), (33, 1), (43, 1), (48, 1)] }, { coefficient := -1, powers := [(9, 1), (14, 1), (24, 1), (34, 1), (37, 1), (55, 1)] }, { coefficient := -2, powers := [(13, 1), (21, 1), (33, 1), (37, 1), (43, 1), (55, 1)] }, { coefficient := 1, powers := [(14, 1), (24, 1), (34, 1), (37, 1), (48, 1), (55, 1)] }, { coefficient := -2, powers := [(18, 1), (21, 1), (33, 1), (37, 1), (43, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (5, 1), (31, 1), (43, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (25, 1), (31, 1), (43, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (8, 1), (33, 1), (43, 1), (44, 1), (48, 1)] }, { coefficient := -1, powers := [(3, 1), (8, 1), (31, 1), (33, 1), (44, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (20, 1), (33, 1), (43, 1), (44, 1), (48, 1)] }, { coefficient := 1, powers := [(8, 1), (25, 1), (33, 1), (43, 1), (44, 1), (48, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1), (33, 1), (37, 1), (43, 1), (44, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1), (33, 1), (37, 1), (44, 1), (54, 1)] }, { coefficient := 1, powers := [(13, 1), (33, 1), (37, 1), (43, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (33, 1), (37, 1), (49, 1), (56, 1)] }, { coefficient := -1, powers := [(0, 1), (36, 1), (37, 1), (49, 1), (53, 1)] }, { coefficient := -1, powers := [(3, 1), (25, 1), (33, 1), (49, 1), (56, 1)] }, { coefficient := -1, powers := [(3, 1), (25, 1), (36, 1), (49, 1), (53, 1)] }, { coefficient := 1, powers := [(9, 1), (30, 1), (37, 1), (59, 1)] }, { coefficient := 1, powers := [(9, 1), (33, 1), (37, 1), (56, 1)] }, { coefficient := -1, powers := [(30, 1), (37, 1), (48, 1), (59, 1)] }, { coefficient := -1, powers := [(33, 1), (37, 1), (48, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (5, 1), (31, 1), (43, 1), (44, 1), (56, 1)] }, { coefficient := -1, powers := [(5, 1), (25, 1), (31, 1), (43, 1), (44, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(26, 1), (33, 1), (37, 1), (43, 1)] }],
  [{ coefficient := -1, powers := [(25, 1), (33, 1), (37, 1), (43, 1), (47, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (24, 1), (43, 1), (45, 1), (48, 1), (53, 1)] }, { coefficient := 1, powers := [(3, 1), (24, 1), (31, 1), (45, 1), (53, 1), (54, 1)] }, { coefficient := -1, powers := [(9, 1), (24, 1), (34, 1), (37, 1), (51, 1), (56, 1)] }, { coefficient := -1, powers := [(20, 1), (24, 1), (43, 1), (45, 1), (48, 1), (53, 1)] }, { coefficient := -1, powers := [(24, 1), (25, 1), (43, 1), (45, 1), (48, 1), (53, 1)] }, { coefficient := -1, powers := [(24, 1), (31, 1), (37, 1), (43, 1), (45, 1), (53, 1)] }, { coefficient := -1, powers := [(24, 1), (31, 1), (37, 1), (45, 1), (53, 1), (54, 1)] }, { coefficient := 1, powers := [(24, 1), (34, 1), (37, 1), (48, 1), (51, 1), (56, 1)] }, { coefficient := -1, powers := [(26, 1), (33, 1), (37, 1), (43, 1), (47, 1), (49, 1)] }, { coefficient := -1, powers := [(31, 1), (33, 1), (37, 1), (39, 1), (43, 1), (45, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (5, 1), (43, 1), (48, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (5, 1), (31, 1), (54, 1), (59, 1)] }, { coefficient := -1, powers := [(5, 1), (20, 1), (43, 1), (48, 1), (59, 1)] }, { coefficient := -1, powers := [(5, 1), (25, 1), (43, 1), (48, 1), (59, 1)] }, { coefficient := -1, powers := [(5, 1), (31, 1), (37, 1), (43, 1), (59, 1)] }, { coefficient := -1, powers := [(5, 1), (31, 1), (37, 1), (54, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (33, 1), (37, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (36, 1), (37, 1), (53, 1)] }, { coefficient := 1, powers := [(3, 1), (25, 1), (33, 1), (56, 1)] }, { coefficient := 1, powers := [(3, 1), (25, 1), (36, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (8, 1), (43, 1), (48, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (8, 1), (31, 1), (54, 1), (59, 1)] }, { coefficient := 1, powers := [(8, 1), (9, 1), (34, 1), (37, 1), (59, 1)] }, { coefficient := -1, powers := [(8, 1), (20, 1), (43, 1), (48, 1), (59, 1)] }, { coefficient := -1, powers := [(8, 1), (25, 1), (43, 1), (48, 1), (59, 1)] }, { coefficient := -1, powers := [(8, 1), (31, 1), (37, 1), (43, 1), (59, 1)] }, { coefficient := -1, powers := [(8, 1), (31, 1), (37, 1), (54, 1), (59, 1)] }, { coefficient := -1, powers := [(8, 1), (34, 1), (37, 1), (48, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (43, 1), (48, 1), (53, 1)] }, { coefficient := 1, powers := [(3, 1), (31, 1), (53, 1), (54, 1)] }, { coefficient := -1, powers := [(20, 1), (43, 1), (48, 1), (53, 1)] }, { coefficient := -1, powers := [(25, 1), (43, 1), (48, 1), (53, 1)] }, { coefficient := -1, powers := [(31, 1), (37, 1), (43, 1), (53, 1)] }, { coefficient := -1, powers := [(31, 1), (37, 1), (53, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (34, 1), (37, 1), (47, 1)] }, { coefficient := -1, powers := [(34, 1), (37, 1), (47, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(20, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (24, 1), (25, 1), (34, 1), (37, 1), (56, 1)] }, { coefficient := -1, powers := [(24, 1), (25, 1), (34, 1), (37, 1), (48, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (20, 1), (24, 1), (43, 1), (48, 1), (53, 1)] }, { coefficient := -1, powers := [(3, 1), (20, 1), (24, 1), (31, 1), (53, 1), (54, 1)] }, { coefficient := 1, powers := [(20, 2), (24, 1), (43, 1), (48, 1), (53, 1)] }, { coefficient := 1, powers := [(20, 1), (24, 1), (25, 1), (43, 1), (48, 1), (53, 1)] }, { coefficient := 1, powers := [(20, 1), (24, 1), (31, 1), (37, 1), (43, 1), (53, 1)] }, { coefficient := 1, powers := [(20, 1), (24, 1), (31, 1), (37, 1), (53, 1), (54, 1)] }, { coefficient := 1, powers := [(20, 1), (31, 1), (33, 1), (37, 1), (39, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (19, 1), (37, 1), (57, 1)] }, { coefficient := -1, powers := [(0, 1), (19, 1), (43, 1), (48, 1)] }, { coefficient := 1, powers := [(3, 1), (19, 1), (25, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (19, 1), (31, 1), (54, 1)] }, { coefficient := 1, powers := [(9, 1), (19, 1), (34, 1), (37, 1)] }, { coefficient := -1, powers := [(19, 1), (20, 1), (43, 1), (48, 1)] }, { coefficient := -1, powers := [(19, 1), (25, 1), (43, 1), (48, 1)] }, { coefficient := -1, powers := [(19, 1), (31, 1), (37, 1), (43, 1)] }, { coefficient := -1, powers := [(19, 1), (31, 1), (37, 1), (54, 1)] }, { coefficient := -1, powers := [(19, 1), (34, 1), (37, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (14, 1), (37, 1), (57, 1)] }, { coefficient := -1, powers := [(0, 1), (14, 1), (43, 1), (48, 1)] }, { coefficient := 1, powers := [(3, 1), (14, 1), (25, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (14, 1), (31, 1), (54, 1)] }, { coefficient := -1, powers := [(14, 1), (20, 1), (43, 1), (48, 1)] }, { coefficient := -1, powers := [(14, 1), (25, 1), (43, 1), (48, 1)] }, { coefficient := -1, powers := [(14, 1), (31, 1), (37, 1), (43, 1)] }, { coefficient := -1, powers := [(14, 1), (31, 1), (37, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(13, 1), (33, 1), (37, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (37, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (25, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (31, 1), (56, 1)] }, { coefficient := -1, powers := [(31, 1), (37, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (36, 1), (37, 1)] }, { coefficient := -1, powers := [(36, 1), (37, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (8, 1), (43, 1), (48, 1), (58, 1)] }, { coefficient := -1, powers := [(3, 1), (8, 1), (31, 1), (54, 1), (58, 1)] }, { coefficient := 1, powers := [(8, 1), (20, 1), (43, 1), (48, 1), (58, 1)] }, { coefficient := 1, powers := [(8, 1), (25, 1), (43, 1), (48, 1), (58, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1), (37, 1), (43, 1), (58, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1), (37, 1), (54, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (24, 1), (34, 1), (37, 1), (56, 1)] }, { coefficient := -1, powers := [(24, 1), (34, 1), (37, 1), (48, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (24, 1), (43, 1), (48, 1), (53, 1)] }, { coefficient := -1, powers := [(3, 1), (24, 1), (31, 1), (53, 1), (54, 1)] }, { coefficient := 1, powers := [(20, 1), (24, 1), (43, 1), (48, 1), (53, 1)] }, { coefficient := 1, powers := [(24, 1), (25, 1), (43, 1), (48, 1), (53, 1)] }, { coefficient := 1, powers := [(24, 1), (31, 1), (37, 1), (43, 1), (53, 1)] }, { coefficient := 1, powers := [(24, 1), (31, 1), (37, 1), (53, 1), (54, 1)] }, { coefficient := 1, powers := [(31, 1), (33, 1), (37, 1), (39, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(33, 1), (37, 1), (43, 1), (47, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (5, 1), (33, 1), (43, 1), (56, 1)] }, { coefficient := -1, powers := [(5, 1), (25, 1), (33, 1), (43, 1), (56, 1)] }],
  [{ coefficient := 2, powers := [(21, 1), (33, 1), (37, 1), (43, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (8, 1), (33, 1), (43, 1), (47, 1), (48, 1)] }, { coefficient := 1, powers := [(3, 1), (8, 1), (31, 1), (33, 1), (47, 1), (54, 1)] }, { coefficient := -1, powers := [(8, 1), (20, 1), (33, 1), (43, 1), (47, 1), (48, 1)] }, { coefficient := -1, powers := [(8, 1), (25, 1), (33, 1), (43, 1), (47, 1), (48, 1)] }, { coefficient := -1, powers := [(8, 1), (31, 1), (33, 1), (37, 1), (43, 1), (47, 1)] }, { coefficient := -1, powers := [(8, 1), (31, 1), (33, 1), (37, 1), (47, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(20, 1), (48, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(48, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (5, 1), (33, 1), (43, 1), (44, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (25, 1), (33, 1), (43, 1), (44, 1), (56, 1)] }, { coefficient := 1, powers := [(43, 1)] }],
  [{ coefficient := -1, powers := [(33, 1), (37, 1), (43, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(0, 1), (37, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (43, 1), (48, 1)] }, { coefficient := -1, powers := [(3, 1), (25, 1), (57, 1)] }, { coefficient := -1, powers := [(3, 1), (31, 1), (54, 1)] }, { coefficient := -1, powers := [(9, 1), (34, 1), (37, 1)] }, { coefficient := 1, powers := [(20, 1), (43, 1), (48, 1)] }, { coefficient := 1, powers := [(25, 1), (43, 1), (48, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1), (43, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1), (54, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (37, 1), (47, 1), (53, 1), (57, 1)] }, { coefficient := -1, powers := [(0, 1), (39, 1), (43, 1), (48, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (25, 1), (47, 1), (53, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (31, 1), (39, 1), (54, 1), (59, 1)] }, { coefficient := 1, powers := [(9, 1), (34, 1), (37, 1), (39, 1), (59, 1)] }, { coefficient := -1, powers := [(20, 1), (39, 1), (43, 1), (48, 1), (59, 1)] }, { coefficient := -1, powers := [(25, 1), (39, 1), (43, 1), (48, 1), (59, 1)] }, { coefficient := -1, powers := [(31, 1), (37, 1), (39, 1), (43, 1), (59, 1)] }, { coefficient := -1, powers := [(31, 1), (37, 1), (39, 1), (54, 1), (59, 1)] }, { coefficient := -1, powers := [(34, 1), (37, 1), (39, 1), (48, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (5, 1), (25, 1), (33, 1), (43, 1), (44, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (54, 1)] }, { coefficient := -1, powers := [(5, 1), (25, 2), (33, 1), (43, 1), (44, 1), (56, 1)] }, { coefficient := 1, powers := [(6, 1), (34, 1)] }, { coefficient := 1, powers := [(15, 1), (25, 1)] }, { coefficient := -2, powers := [(18, 1), (21, 1), (33, 1), (37, 1), (43, 1), (56, 1)] }, { coefficient := -1, powers := [(18, 1), (26, 1), (33, 1), (37, 1), (43, 1), (47, 1)] }, { coefficient := -1, powers := [(25, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (8, 1), (25, 1), (33, 1), (43, 1), (47, 1), (48, 1)] }, { coefficient := -1, powers := [(0, 1), (19, 1), (20, 1), (24, 1), (43, 1), (48, 1), (53, 1)] }, { coefficient := -1, powers := [(0, 1), (19, 1), (24, 1), (25, 1), (43, 1), (48, 1), (53, 1)] }, { coefficient := 1, powers := [(0, 1), (20, 1), (48, 1), (54, 1)] }, { coefficient := -1, powers := [(0, 1), (31, 1), (37, 1), (54, 1)] }, { coefficient := -1, powers := [(3, 1), (8, 1), (25, 1), (31, 1), (33, 1), (47, 1), (54, 1)] }, { coefficient := 1, powers := [(3, 1), (19, 1), (20, 1), (24, 1), (31, 1), (53, 1), (54, 1)] }, { coefficient := 1, powers := [(3, 1), (19, 1), (24, 1), (25, 1), (31, 1), (53, 1), (54, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1), (34, 1), (48, 1)] }, { coefficient := -1, powers := [(6, 1), (31, 1), (34, 1), (37, 1)] }, { coefficient := 1, powers := [(8, 1), (20, 1), (25, 1), (33, 1), (43, 1), (47, 1), (48, 1)] }, { coefficient := 1, powers := [(8, 1), (25, 2), (33, 1), (43, 1), (47, 1), (48, 1)] }, { coefficient := 1, powers := [(8, 1), (25, 1), (31, 1), (33, 1), (37, 1), (43, 1), (47, 1)] }, { coefficient := 1, powers := [(8, 1), (25, 1), (31, 1), (33, 1), (37, 1), (47, 1), (54, 1)] }, { coefficient := 1, powers := [(15, 1), (20, 1), (25, 1), (48, 1)] }, { coefficient := -1, powers := [(15, 1), (25, 1), (31, 1), (37, 1)] }, { coefficient := -1, powers := [(19, 1), (20, 2), (24, 1), (43, 1), (48, 1), (53, 1)] }, { coefficient := -2, powers := [(19, 1), (20, 1), (24, 1), (25, 1), (43, 1), (48, 1), (53, 1)] }, { coefficient := -1, powers := [(19, 1), (20, 1), (24, 1), (31, 1), (37, 1), (43, 1), (53, 1)] }, { coefficient := -1, powers := [(19, 1), (20, 1), (24, 1), (31, 1), (37, 1), (53, 1), (54, 1)] }, { coefficient := -1, powers := [(19, 1), (20, 1), (31, 1), (33, 1), (37, 1), (39, 1), (43, 1)] }, { coefficient := -1, powers := [(19, 1), (24, 1), (25, 2), (43, 1), (48, 1), (53, 1)] }, { coefficient := -1, powers := [(19, 1), (24, 1), (25, 1), (31, 1), (37, 1), (43, 1), (53, 1)] }, { coefficient := -1, powers := [(19, 1), (24, 1), (25, 1), (31, 1), (37, 1), (53, 1), (54, 1)] }, { coefficient := -1, powers := [(19, 1), (25, 1), (31, 1), (33, 1), (37, 1), (39, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (2, 1), (37, 1), (56, 1), (57, 1)] }, { coefficient := -1, powers := [(0, 1), (2, 1), (43, 1), (48, 1), (56, 1)] }, { coefficient := -1, powers := [(0, 1), (6, 1), (8, 1), (36, 1), (43, 1), (48, 1), (58, 1)] }, { coefficient := 1, powers := [(0, 1), (8, 1), (36, 1), (37, 1), (57, 1)] }, { coefficient := -1, powers := [(0, 1), (8, 1), (36, 1), (43, 1), (48, 1)] }, { coefficient := 1, powers := [(2, 1), (3, 1), (25, 1), (56, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (9, 1), (34, 1), (37, 1), (56, 1)] }, { coefficient := -1, powers := [(2, 1), (20, 1), (43, 1), (48, 1), (56, 1)] }, { coefficient := -1, powers := [(2, 1), (25, 1), (43, 1), (48, 1), (56, 1)] }, { coefficient := -1, powers := [(2, 1), (31, 1), (37, 1), (43, 1), (56, 1)] }, { coefficient := -1, powers := [(2, 1), (34, 1), (37, 1), (48, 1), (56, 1)] }, { coefficient := 1, powers := [(3, 1), (6, 1), (8, 1), (31, 1), (36, 1), (54, 1), (58, 1)] }, { coefficient := 1, powers := [(3, 1), (8, 1), (25, 1), (36, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (8, 1), (31, 1), (36, 1), (54, 1)] }, { coefficient := -1, powers := [(6, 1), (8, 1), (20, 1), (36, 1), (43, 1), (48, 1), (58, 1)] }, { coefficient := -1, powers := [(6, 1), (8, 1), (25, 1), (36, 1), (43, 1), (48, 1), (58, 1)] }, { coefficient := -1, powers := [(6, 1), (8, 1), (31, 1), (36, 1), (37, 1), (43, 1), (58, 1)] }, { coefficient := -1, powers := [(6, 1), (8, 1), (31, 1), (36, 1), (37, 1), (54, 1), (58, 1)] }, { coefficient := -1, powers := [(8, 1), (20, 1), (36, 1), (43, 1), (48, 1)] }, { coefficient := -1, powers := [(8, 1), (25, 1), (36, 1), (43, 1), (48, 1)] }, { coefficient := -1, powers := [(8, 1), (31, 1), (36, 1), (37, 1), (43, 1)] }, { coefficient := -1, powers := [(8, 1), (31, 1), (36, 1), (37, 1), (54, 1)] }]
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
    ¬ ∀ index : Fin 46,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component50.SelectedLeafB4_0.selectedHasNoCommonZero

end Krenn.Component50.SelectedLeafB4_0
