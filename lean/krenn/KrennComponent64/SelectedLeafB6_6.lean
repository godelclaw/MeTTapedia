import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component64.SelectedLeafB6_6

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "67e6e6844174f2131c12474c98eb29c770284caba42506d623b080f39f8fb857"
def certificateSHA256 : String := "e2397ffe30d74f084cc9b3a113fd8d300264f194cf603dfd0ccbbb9c79bf4d17"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 61 → Fin 641 := ![
  14,
  18,
  19,
  22,
  24,
  26,
  29,
  31,
  33,
  71,
  82,
  161,
  162,
  163,
  164,
  166,
  170,
  173,
  176,
  187,
  188,
  189,
  193,
  194,
  198,
  199,
  200,
  209,
  222,
  235,
  284,
  343,
  347,
  348,
  349,
  350,
  351,
  352,
  356,
  358,
  367,
  369,
  433,
  444,
  456,
  466,
  468,
  479,
  507,
  548,
  556,
  557,
  571,
  620,
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
def selectedEquations : Fin 61 → SparsePoly (Fin 64) := ![
  [{ coefficient := 1, powers := [(12, 1), (27, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(30, 1), (35, 1)] }],
  [{ coefficient := 1, powers := [(33, 1), (35, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (33, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (27, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1)] }, { coefficient := 1, powers := [(24, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1)] }, { coefficient := 1, powers := [(24, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (52, 1)] }, { coefficient := 1, powers := [(20, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (53, 1)] }, { coefficient := 1, powers := [(20, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (45, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (58, 1)] }, { coefficient := 1, powers := [(18, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (27, 1)] }, { coefficient := 1, powers := [(27, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (24, 1)] }, { coefficient := 1, powers := [(16, 1), (20, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (24, 1)] }, { coefficient := 1, powers := [(18, 1), (20, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (41, 1)] }, { coefficient := 1, powers := [(19, 1), (20, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (44, 1)] }, { coefficient := 1, powers := [(19, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (20, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (41, 1)] }, { coefficient := 1, powers := [(19, 1), (20, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (50, 1)] }, { coefficient := 1, powers := [(23, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (52, 1)] }, { coefficient := 1, powers := [(27, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (38, 1)] }, { coefficient := 1, powers := [(27, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1), (50, 1)] }, { coefficient := 1, powers := [(46, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (27, 1), (58, 1)] }, { coefficient := 1, powers := [(27, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (23, 1), (58, 1)] }, { coefficient := 1, powers := [(23, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (24, 1), (43, 1)] }, { coefficient := 1, powers := [(18, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (41, 1)] }, { coefficient := 1, powers := [(20, 1), (41, 1)] }, { coefficient := 1, powers := [(24, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (52, 1)] }, { coefficient := 1, powers := [(11, 1), (25, 1), (52, 1)] }, { coefficient := 1, powers := [(16, 1), (21, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (53, 1)] }, { coefficient := 1, powers := [(12, 1), (25, 1), (52, 1)] }, { coefficient := 1, powers := [(16, 1), (21, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (46, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1)] }, { coefficient := 1, powers := [(19, 1), (23, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (53, 1)] }, { coefficient := 1, powers := [(8, 1), (30, 1)] }, { coefficient := 1, powers := [(13, 1), (27, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (59, 1)] }, { coefficient := 1, powers := [(13, 1), (46, 1)] }, { coefficient := 1, powers := [(19, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (59, 1)] }, { coefficient := 1, powers := [(13, 1), (56, 1)] }, { coefficient := 1, powers := [(19, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (43, 1)] }, { coefficient := 1, powers := [(13, 1), (55, 1)] }, { coefficient := 1, powers := [(18, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (44, 1)] }, { coefficient := 1, powers := [(19, 1), (38, 1)] }, { coefficient := 1, powers := [(19, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (41, 1), (52, 1)] }, { coefficient := 1, powers := [(20, 1), (41, 1), (52, 1)] }, { coefficient := 1, powers := [(20, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1), (48, 1)] }, { coefficient := 1, powers := [(24, 1), (43, 1), (48, 1)] }, { coefficient := 1, powers := [(48, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (20, 1), (55, 1)] }, { coefficient := 1, powers := [(13, 1)] }, { coefficient := 1, powers := [(18, 1), (20, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (24, 1), (38, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (43, 1)] }, { coefficient := 1, powers := [(18, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1)] }, { coefficient := 1, powers := [(24, 1), (38, 1), (41, 1)] }, { coefficient := 1, powers := [(24, 1), (44, 1)] }, { coefficient := 1, powers := [(41, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (53, 1)] }, { coefficient := 1, powers := [(27, 1), (39, 1)] }, { coefficient := 1, powers := [(27, 1), (45, 1), (48, 1)] }, { coefficient := 1, powers := [(30, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (38, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(41, 1), (52, 1)] }, { coefficient := 1, powers := [(56, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1), (48, 1)] }, { coefficient := 1, powers := [(6, 1), (59, 1)] }, { coefficient := 1, powers := [(24, 1), (44, 1), (48, 1)] }, { coefficient := 1, powers := [(41, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (27, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (30, 1), (56, 1)] }, { coefficient := 1, powers := [(3, 1), (33, 1), (53, 1)] }, { coefficient := 1, powers := [(27, 1), (41, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (41, 1), (52, 1)] }, { coefficient := 1, powers := [(23, 1), (56, 1)] }, { coefficient := 1, powers := [(27, 1), (46, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1)] }, { coefficient := 1, powers := [(6, 1), (58, 1)] }, { coefficient := 1, powers := [(24, 1), (38, 1)] }, { coefficient := 1, powers := [(24, 1), (43, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (50, 1)] }, { coefficient := 1, powers := [(3, 1), (58, 1)] }, { coefficient := 1, powers := [(20, 1), (50, 1)] }, { coefficient := 1, powers := [(20, 1), (55, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (39, 1), (55, 1)] }, { coefficient := 1, powers := [(2, 1), (45, 1), (51, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (55, 1)] }, { coefficient := 1, powers := [(13, 1), (23, 1), (55, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (35, 1), (58, 1)] }, { coefficient := 1, powers := [(0, 1), (38, 1), (55, 1)] }, { coefficient := 1, powers := [(0, 1), (43, 1), (50, 1)] }, { coefficient := 1, powers := [(38, 1)] }, { coefficient := 1, powers := [(43, 1)] }, { coefficient := 1, powers := [(50, 1)] }, { coefficient := 1, powers := [(55, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (36, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (46, 1), (53, 1)] }, { coefficient := 1, powers := [(5, 1), (27, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (53, 1)] }, { coefficient := 1, powers := [(8, 1), (23, 1), (59, 1)] }, { coefficient := 1, powers := [(8, 1), (30, 1), (46, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (39, 1)] }, { coefficient := 1, powers := [(13, 1), (23, 1), (56, 1)] }, { coefficient := 1, powers := [(13, 1), (27, 1), (46, 1)] }, { coefficient := 1, powers := [(13, 1), (33, 1), (36, 1)] }, { coefficient := 1, powers := [(19, 1), (23, 1), (53, 1)] }, { coefficient := 1, powers := [(19, 1), (27, 1), (39, 1)] }, { coefficient := 1, powers := [(19, 1), (30, 1), (36, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (60, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1), (61, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(37, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(38, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(39, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 61 → SparsePoly (Fin 64) := ![
  [{ coefficient := -1, powers := [(0, 1), (19, 1), (25, 1), (43, 1), (45, 1), (61, 1)] }, { coefficient := -3, powers := [(19, 1), (25, 1), (45, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (20, 1), (25, 1), (30, 1), (44, 1), (61, 1)] }, { coefficient := -1, powers := [(5, 1), (21, 1), (24, 1), (30, 1), (44, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (19, 1), (21, 1), (23, 1), (43, 1), (61, 1)] }, { coefficient := 3, powers := [(19, 1), (21, 1), (23, 1), (61, 1)] }],
  [{ coefficient := 2, powers := [(0, 2), (27, 1), (38, 1), (51, 1)] }, { coefficient := 2, powers := [(0, 2), (27, 1), (51, 1), (60, 1)] }],
  [{ coefficient := -2, powers := [(20, 1), (23, 1), (44, 1)] }],
  [{ coefficient := -1, powers := [(0, 2), (13, 1), (38, 1), (52, 1), (55, 1)] }, { coefficient := -1, powers := [(0, 2), (13, 1), (43, 1), (50, 1), (52, 1)] }, { coefficient := -1, powers := [(0, 2), (13, 1), (52, 1), (55, 1), (60, 1)] }, { coefficient := -1, powers := [(0, 1), (13, 1), (38, 1), (52, 1)] }, { coefficient := -1, powers := [(0, 1), (13, 1), (43, 1), (52, 1)] }, { coefficient := -1, powers := [(0, 1), (13, 1), (50, 1), (52, 1)] }, { coefficient := -1, powers := [(0, 1), (18, 1), (43, 1), (53, 1)] }, { coefficient := -2, powers := [(13, 1), (52, 1)] }, { coefficient := 1, powers := [(18, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(0, 2), (19, 1), (35, 1), (45, 1), (58, 1)] }, { coefficient := -1, powers := [(0, 2), (19, 1), (38, 1), (45, 1), (55, 1)] }, { coefficient := -1, powers := [(0, 2), (19, 1), (43, 1), (45, 1), (50, 1)] }, { coefficient := -1, powers := [(0, 2), (19, 1), (45, 1), (55, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (5, 1), (41, 1), (43, 1), (58, 1)] }, { coefficient := -1, powers := [(0, 1), (19, 1), (38, 1), (45, 1)] }, { coefficient := -1, powers := [(0, 1), (19, 1), (43, 1), (45, 1)] }, { coefficient := -1, powers := [(0, 1), (19, 1), (45, 1), (50, 1)] }, { coefficient := 1, powers := [(5, 1), (41, 1), (58, 1)] }, { coefficient := 2, powers := [(18, 1), (46, 1)] }, { coefficient := -2, powers := [(19, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(0, 2), (5, 1), (56, 1), (58, 1)] }, { coefficient := 1, powers := [(0, 2), (8, 1), (46, 1), (58, 1)] }],
  [{ coefficient := 2, powers := [(0, 2), (5, 1), (53, 1), (58, 1)] }, { coefficient := 1, powers := [(0, 2), (13, 1), (36, 1), (58, 1)] }],
  [{ coefficient := -2, powers := [(0, 2), (18, 1), (38, 1), (45, 1), (50, 1), (53, 1), (63, 1)] }, { coefficient := -2, powers := [(0, 2), (18, 1), (45, 1), (50, 1), (53, 1), (60, 1), (63, 1)] }],
  [{ coefficient := -2, powers := [(0, 2), (13, 1), (38, 1), (46, 1), (62, 1)] }, { coefficient := -2, powers := [(0, 2), (13, 1), (46, 1), (60, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (18, 1), (27, 1), (41, 1), (43, 2), (48, 1)] }, { coefficient := 1, powers := [(0, 1), (18, 1), (27, 1), (43, 1), (44, 1), (48, 1)] }, { coefficient := 1, powers := [(18, 1), (27, 1), (41, 1), (43, 1), (48, 1)] }, { coefficient := -1, powers := [(18, 1), (27, 1), (44, 1), (48, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (13, 1), (27, 1), (43, 2)] }, { coefficient := 3, powers := [(13, 1), (27, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (5, 1), (30, 1), (41, 1), (43, 1), (50, 1)] }, { coefficient := 1, powers := [(0, 1), (5, 1), (30, 1), (41, 1), (43, 1), (55, 1)] }, { coefficient := 1, powers := [(0, 1), (13, 1), (23, 1), (41, 1), (43, 2)] }, { coefficient := -1, powers := [(5, 1), (30, 1), (38, 1), (41, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (41, 1), (50, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (41, 1), (55, 1)] }, { coefficient := 1, powers := [(13, 1), (23, 1), (41, 1), (43, 1)] }, { coefficient := 1, powers := [(13, 1), (23, 1), (44, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (5, 1), (33, 1), (43, 1), (50, 1)] }, { coefficient := -2, powers := [(0, 1), (19, 1), (23, 1), (43, 1), (50, 1)] }, { coefficient := -1, powers := [(5, 1), (33, 1), (50, 1)] }, { coefficient := -2, powers := [(19, 1), (23, 1), (38, 1)] }, { coefficient := -2, powers := [(19, 1), (23, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(0, 2), (38, 1), (51, 1), (56, 1)] }, { coefficient := -1, powers := [(0, 2), (43, 1), (51, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 2), (51, 1), (56, 1), (60, 1)] }, { coefficient := 2, powers := [(0, 1), (38, 1), (48, 1), (56, 1)] }, { coefficient := -1, powers := [(0, 1), (43, 1), (48, 1), (56, 1)] }, { coefficient := 2, powers := [(0, 1), (48, 1), (56, 1), (60, 1)] }, { coefficient := -1, powers := [(0, 1), (51, 1), (56, 1)] }, { coefficient := -1, powers := [(48, 1), (56, 1)] }],
  [{ coefficient := 2, powers := [(0, 2), (6, 1), (33, 1), (38, 1), (50, 1), (53, 1)] }, { coefficient := 2, powers := [(0, 2), (6, 1), (33, 1), (50, 1), (53, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (6, 1), (27, 1), (43, 1), (59, 1)] }, { coefficient := -1, powers := [(6, 1), (27, 1), (59, 1)] }],
  [{ coefficient := 2, powers := [(0, 2), (13, 1), (38, 1), (43, 1), (46, 1), (62, 1)] }, { coefficient := 2, powers := [(0, 2), (13, 1), (43, 1), (46, 1), (60, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (25, 1), (30, 1), (44, 1), (52, 1), (61, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (23, 1), (38, 2), (56, 1)] }, { coefficient := -1, powers := [(0, 1), (23, 1), (38, 1), (43, 1), (56, 1)] }, { coefficient := -2, powers := [(0, 1), (23, 1), (38, 1), (56, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (23, 1), (43, 2), (56, 1)] }, { coefficient := -2, powers := [(0, 1), (23, 1), (43, 1), (56, 1), (60, 1)] }, { coefficient := -1, powers := [(0, 1), (27, 1), (38, 1), (43, 1), (46, 1)] }, { coefficient := -1, powers := [(0, 1), (27, 1), (43, 2), (46, 1)] }, { coefficient := 1, powers := [(23, 1), (38, 1), (56, 1)] }, { coefficient := 1, powers := [(23, 1), (43, 1), (56, 1)] }, { coefficient := 1, powers := [(27, 1), (38, 1), (46, 1)] }, { coefficient := 1, powers := [(27, 1), (43, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(20, 1), (23, 1), (52, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (23, 1), (38, 2), (48, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (23, 1), (38, 1), (43, 1), (48, 1), (56, 1)] }, { coefficient := 2, powers := [(0, 1), (23, 1), (38, 1), (48, 1), (56, 1), (60, 1)] }, { coefficient := -1, powers := [(0, 1), (23, 1), (43, 2), (48, 1), (56, 1)] }, { coefficient := 2, powers := [(0, 1), (23, 1), (43, 1), (48, 1), (56, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (27, 1), (38, 1), (43, 1), (46, 1), (48, 1)] }, { coefficient := 1, powers := [(0, 1), (27, 1), (43, 2), (46, 1), (48, 1)] }, { coefficient := -1, powers := [(23, 1), (38, 1), (48, 1), (56, 1)] }, { coefficient := -1, powers := [(23, 1), (43, 1), (48, 1), (56, 1)] }, { coefficient := -1, powers := [(27, 1), (38, 1), (46, 1), (48, 1)] }, { coefficient := -1, powers := [(27, 1), (43, 1), (46, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (23, 1), (43, 1), (53, 1)] }, { coefficient := -1, powers := [(23, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(0, 2), (13, 1), (43, 1), (56, 1)] }, { coefficient := -2, powers := [(0, 2), (19, 1), (38, 1), (53, 1)] }, { coefficient := -2, powers := [(0, 2), (19, 1), (53, 1), (60, 1)] }, { coefficient := -1, powers := [(0, 1), (13, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (19, 1), (20, 1), (43, 1), (53, 1)] }, { coefficient := 1, powers := [(19, 1), (20, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (12, 1), (19, 1), (25, 1), (43, 1), (61, 1)] }, { coefficient := 3, powers := [(12, 1), (19, 1), (25, 1), (61, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (13, 1), (46, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (13, 1), (27, 1), (43, 1)] }, { coefficient := -2, powers := [(13, 1), (27, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (5, 1), (43, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (59, 1)] }],
  [{ coefficient := 2, powers := [(0, 2), (19, 1), (38, 1), (50, 1), (53, 1)] }, { coefficient := 2, powers := [(0, 2), (19, 1), (50, 1), (53, 1), (60, 1)] }, { coefficient := -2, powers := [(0, 1), (13, 1), (38, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (13, 1), (43, 1), (56, 1)] }, { coefficient := -2, powers := [(0, 1), (13, 1), (56, 1), (60, 1)] }, { coefficient := 1, powers := [(13, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (27, 1), (43, 1), (46, 1)] }, { coefficient := -3, powers := [(27, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (30, 1), (38, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (24, 1), (30, 1), (44, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (19, 1), (23, 1), (43, 1), (61, 1)] }, { coefficient := -3, powers := [(19, 1), (23, 1), (61, 1)] }],
  [{ coefficient := 2, powers := [(0, 3), (38, 1), (43, 1), (50, 1), (53, 1)] }, { coefficient := 2, powers := [(0, 3), (43, 1), (50, 1), (53, 1), (60, 1)] }, { coefficient := 2, powers := [(0, 2), (24, 1), (38, 2), (50, 1), (53, 1)] }, { coefficient := 2, powers := [(0, 2), (24, 1), (38, 1), (43, 1), (50, 1), (53, 1)] }, { coefficient := 2, powers := [(0, 2), (24, 1), (38, 1), (50, 1), (53, 1), (60, 1)] }, { coefficient := 2, powers := [(0, 2), (24, 1), (43, 1), (50, 1), (53, 1), (60, 1)] }, { coefficient := -1, powers := [(0, 2), (35, 1), (53, 1), (58, 1)] }, { coefficient := 2, powers := [(0, 2), (38, 1), (50, 1), (53, 1)] }, { coefficient := 1, powers := [(0, 2), (38, 1), (53, 1), (55, 1)] }, { coefficient := 1, powers := [(0, 2), (43, 1), (50, 1), (53, 1)] }, { coefficient := 2, powers := [(0, 2), (50, 1), (53, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 2), (53, 1), (55, 1), (60, 1)] }, { coefficient := -1, powers := [(0, 1), (20, 1), (43, 1), (53, 1), (55, 1)] }, { coefficient := 1, powers := [(0, 1), (38, 1), (53, 1)] }, { coefficient := 1, powers := [(0, 1), (50, 1), (53, 1)] }, { coefficient := -1, powers := [(20, 1), (53, 1), (55, 1)] }, { coefficient := 1, powers := [(53, 1)] }],
  [{ coefficient := 1, powers := [(0, 2), (38, 1), (46, 1), (55, 1)] }, { coefficient := 1, powers := [(0, 2), (43, 1), (46, 1), (50, 1)] }, { coefficient := 1, powers := [(0, 2), (46, 1), (55, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (38, 1), (46, 1)] }, { coefficient := 1, powers := [(0, 1), (43, 1), (46, 1)] }, { coefficient := 1, powers := [(0, 1), (46, 1), (50, 1)] }, { coefficient := 2, powers := [(46, 1)] }],
  [{ coefficient := 1, powers := [(0, 2), (27, 1), (35, 1), (58, 1)] }, { coefficient := 1, powers := [(0, 2), (27, 1), (38, 1), (55, 1)] }, { coefficient := 1, powers := [(0, 2), (27, 1), (43, 2)] }, { coefficient := 1, powers := [(0, 2), (27, 1), (43, 1), (50, 1)] }, { coefficient := 1, powers := [(0, 2), (27, 1), (55, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (24, 1), (27, 1), (38, 1), (43, 1)] }, { coefficient := 1, powers := [(0, 1), (24, 1), (27, 1), (43, 2)] }, { coefficient := 1, powers := [(0, 1), (27, 1), (38, 1)] }, { coefficient := 1, powers := [(0, 1), (27, 1), (50, 1)] }, { coefficient := -1, powers := [(24, 1), (27, 1), (38, 1)] }, { coefficient := -1, powers := [(24, 1), (27, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(0, 2), (23, 1), (35, 1), (58, 1)] }, { coefficient := 1, powers := [(0, 2), (23, 1), (38, 1), (55, 1)] }, { coefficient := 1, powers := [(0, 2), (23, 1), (43, 1), (50, 1)] }, { coefficient := 1, powers := [(0, 2), (23, 1), (55, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (23, 1), (38, 1)] }, { coefficient := 1, powers := [(0, 1), (23, 1), (43, 1)] }, { coefficient := 1, powers := [(0, 1), (23, 1), (50, 1)] }, { coefficient := 2, powers := [(23, 1)] }],
  [{ coefficient := -2, powers := [(0, 2), (23, 1), (38, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 2), (23, 1), (43, 1), (56, 1)] }, { coefficient := -2, powers := [(0, 2), (23, 1), (56, 1), (60, 1)] }, { coefficient := -2, powers := [(0, 2), (27, 1), (38, 1), (46, 1)] }, { coefficient := -2, powers := [(0, 2), (27, 1), (46, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (20, 1), (23, 1), (43, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (23, 1), (56, 1)] }, { coefficient := 1, powers := [(20, 1), (23, 1), (56, 1)] }],
  [{ coefficient := 2, powers := [(20, 1), (23, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (5, 1), (30, 1), (43, 1), (50, 1)] }, { coefficient := -1, powers := [(0, 1), (5, 1), (30, 1), (43, 1), (55, 1)] }, { coefficient := -1, powers := [(0, 1), (13, 1), (23, 1), (43, 2)] }, { coefficient := -1, powers := [(5, 1), (30, 1), (50, 1)] }, { coefficient := -1, powers := [(5, 1), (30, 1), (55, 1)] }, { coefficient := -1, powers := [(13, 1), (23, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (18, 1), (27, 1), (41, 1), (43, 1), (45, 1)] }, { coefficient := -1, powers := [(18, 1), (27, 1), (41, 1), (45, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (23, 1), (43, 1), (56, 1)] }, { coefficient := -1, powers := [(23, 1), (56, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (23, 1), (38, 1), (48, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (23, 1), (43, 1), (48, 1), (56, 1)] }, { coefficient := -2, powers := [(0, 1), (23, 1), (48, 1), (56, 1), (60, 1)] }, { coefficient := -1, powers := [(0, 1), (27, 1), (43, 1), (46, 1), (48, 1)] }, { coefficient := 1, powers := [(23, 1), (48, 1), (56, 1)] }, { coefficient := 1, powers := [(27, 1), (46, 1), (48, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (30, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(0, 2), (19, 1), (35, 1), (58, 1)] }, { coefficient := 1, powers := [(0, 2), (19, 1), (38, 1), (55, 1)] }, { coefficient := 1, powers := [(0, 2), (19, 1), (43, 1), (50, 1)] }, { coefficient := 1, powers := [(0, 2), (19, 1), (55, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (19, 1), (38, 1)] }, { coefficient := 1, powers := [(0, 1), (19, 1), (43, 1)] }, { coefficient := 1, powers := [(0, 1), (19, 1), (50, 1)] }, { coefficient := 2, powers := [(19, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (30, 1)] }, { coefficient := -1, powers := [(13, 1), (23, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (18, 1), (27, 1), (43, 1), (45, 1)] }, { coefficient := 1, powers := [(18, 1), (27, 1), (45, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (5, 1), (43, 1), (58, 1)] }, { coefficient := -1, powers := [(5, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(0, 2), (13, 1), (38, 1), (55, 1)] }, { coefficient := 1, powers := [(0, 2), (13, 1), (43, 1), (50, 1)] }, { coefficient := 1, powers := [(0, 2), (13, 1), (55, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (13, 1), (38, 1)] }, { coefficient := 1, powers := [(0, 1), (13, 1), (43, 1)] }, { coefficient := 1, powers := [(0, 1), (13, 1), (50, 1)] }, { coefficient := 2, powers := [(13, 1)] }],
  [{ coefficient := -2, powers := [(0, 2), (5, 1), (33, 1), (38, 1), (50, 1), (53, 1)] }, { coefficient := -2, powers := [(0, 2), (5, 1), (33, 1), (50, 1), (53, 1), (60, 1)] }, { coefficient := -2, powers := [(0, 2), (19, 1), (23, 1), (38, 1), (50, 1), (53, 1)] }, { coefficient := -2, powers := [(0, 2), (19, 1), (23, 1), (50, 1), (53, 1), (60, 1)] }, { coefficient := -1, powers := [(0, 1), (5, 1), (27, 1), (43, 1), (59, 1)] }, { coefficient := 2, powers := [(0, 1), (13, 1), (23, 1), (38, 1), (56, 1)] }, { coefficient := -1, powers := [(0, 1), (13, 1), (23, 1), (43, 1), (56, 1)] }, { coefficient := 2, powers := [(0, 1), (13, 1), (23, 1), (56, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (27, 1), (59, 1)] }, { coefficient := -1, powers := [(13, 1), (23, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (5, 1), (30, 1), (43, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (5, 1), (33, 1), (43, 1), (53, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(0, 2), (38, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 2), (56, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(0, 1)] }],
  [{ coefficient := -1, powers := [(0, 2), (35, 1), (58, 1)] }, { coefficient := -1, powers := [(0, 2), (38, 1), (55, 1)] }, { coefficient := -1, powers := [(0, 2), (43, 1), (50, 1)] }, { coefficient := -1, powers := [(0, 2), (55, 1), (60, 1)] }, { coefficient := -1, powers := [(0, 1), (38, 1)] }, { coefficient := -1, powers := [(0, 1), (43, 1)] }, { coefficient := -1, powers := [(0, 1), (50, 1)] }, { coefficient := -2, powers := [] }],
  [{ coefficient := -1, powers := [(0, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (19, 1), (23, 1), (43, 1), (53, 1)] }, { coefficient := -1, powers := [(5, 1), (24, 1), (30, 1), (44, 1), (52, 1)] }, { coefficient := 3, powers := [(19, 1), (23, 1), (53, 1)] }],
  [{ coefficient := -2, powers := [(0, 3), (38, 1), (43, 1), (46, 1), (50, 1), (53, 1)] }, { coefficient := -2, powers := [(0, 3), (43, 1), (46, 1), (50, 1), (53, 1), (60, 1)] }, { coefficient := -2, powers := [(0, 2), (24, 1), (38, 2), (46, 1), (50, 1), (53, 1)] }, { coefficient := -2, powers := [(0, 2), (24, 1), (38, 1), (43, 1), (46, 1), (50, 1), (53, 1)] }, { coefficient := -2, powers := [(0, 2), (24, 1), (38, 1), (46, 1), (50, 1), (53, 1), (60, 1)] }, { coefficient := -2, powers := [(0, 2), (24, 1), (43, 1), (46, 1), (50, 1), (53, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 2), (35, 1), (36, 1), (58, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 2), (35, 1), (39, 1), (56, 1), (58, 1)] }, { coefficient := 2, powers := [(0, 2), (35, 1), (46, 1), (53, 1), (58, 1)] }, { coefficient := 1, powers := [(0, 2), (36, 1), (38, 1), (55, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 2), (36, 1), (43, 1), (50, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 2), (36, 1), (55, 1), (59, 1), (60, 1)] }, { coefficient := -2, powers := [(0, 2), (38, 1), (45, 1), (51, 1), (56, 1)] }, { coefficient := -2, powers := [(0, 2), (38, 1), (46, 1), (50, 1), (53, 1)] }, { coefficient := -1, powers := [(0, 2), (38, 1), (46, 1), (53, 1), (55, 1)] }, { coefficient := 1, powers := [(0, 2), (39, 1), (43, 1), (50, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 2), (43, 1), (45, 1), (51, 1), (56, 1)] }, { coefficient := -1, powers := [(0, 2), (43, 1), (46, 1), (50, 1), (53, 1)] }, { coefficient := -2, powers := [(0, 2), (45, 1), (51, 1), (56, 1), (60, 1)] }, { coefficient := -2, powers := [(0, 2), (46, 1), (50, 1), (53, 1), (60, 1)] }, { coefficient := -1, powers := [(0, 2), (46, 1), (53, 1), (55, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (20, 1), (43, 1), (46, 1), (53, 1), (55, 1)] }, { coefficient := 1, powers := [(0, 1), (36, 1), (38, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (36, 1), (43, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (36, 1), (50, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (38, 1), (39, 1), (56, 1)] }, { coefficient := -2, powers := [(0, 1), (38, 1), (45, 1), (48, 1), (56, 1)] }, { coefficient := -1, powers := [(0, 1), (38, 1), (46, 1), (53, 1)] }, { coefficient := 1, powers := [(0, 1), (39, 1), (43, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (39, 1), (50, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (43, 1), (45, 1), (48, 1), (56, 1)] }, { coefficient := -2, powers := [(0, 1), (45, 1), (48, 1), (56, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (45, 1), (51, 1), (56, 1)] }, { coefficient := -1, powers := [(0, 1), (46, 1), (50, 1), (53, 1)] }, { coefficient := 1, powers := [(20, 1), (46, 1), (53, 1), (55, 1)] }, { coefficient := 2, powers := [(36, 1), (59, 1)] }, { coefficient := 2, powers := [(39, 1), (56, 1)] }, { coefficient := 1, powers := [(45, 1), (48, 1), (56, 1)] }, { coefficient := -1, powers := [(46, 1), (53, 1)] }],
  [{ coefficient := -2, powers := [(0, 2), (13, 1), (27, 1), (38, 1), (43, 1), (46, 1)] }, { coefficient := -2, powers := [(0, 2), (13, 1), (27, 1), (43, 1), (46, 1), (60, 1)] }],
  [{ coefficient := 2, powers := [(0, 2), (6, 1), (18, 1), (33, 1), (38, 1), (45, 1), (50, 1), (53, 1)] }, { coefficient := 2, powers := [(0, 2), (6, 1), (18, 1), (33, 1), (45, 1), (50, 1), (53, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(0, 2), (8, 1), (33, 1), (35, 1), (58, 1)] }, { coefficient := 1, powers := [(0, 2), (8, 1), (33, 1), (38, 1), (55, 1)] }, { coefficient := 1, powers := [(0, 2), (8, 1), (33, 1), (43, 1), (50, 1)] }, { coefficient := 1, powers := [(0, 2), (8, 1), (33, 1), (55, 1), (60, 1)] }, { coefficient := -1, powers := [(0, 2), (19, 1), (27, 1), (35, 1), (58, 1)] }, { coefficient := -1, powers := [(0, 2), (19, 1), (27, 1), (38, 1), (55, 1)] }, { coefficient := -1, powers := [(0, 2), (19, 1), (27, 1), (43, 2)] }, { coefficient := -1, powers := [(0, 2), (19, 1), (27, 1), (43, 1), (50, 1)] }, { coefficient := -1, powers := [(0, 2), (19, 1), (27, 1), (55, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (8, 1), (33, 1), (38, 1)] }, { coefficient := 1, powers := [(0, 1), (8, 1), (33, 1), (43, 1)] }, { coefficient := 1, powers := [(0, 1), (8, 1), (33, 1), (50, 1)] }, { coefficient := -1, powers := [(0, 1), (19, 1), (24, 1), (27, 1), (38, 1), (43, 1)] }, { coefficient := -1, powers := [(0, 1), (19, 1), (24, 1), (27, 1), (43, 2)] }, { coefficient := -1, powers := [(0, 1), (19, 1), (27, 1), (38, 1)] }, { coefficient := -1, powers := [(0, 1), (19, 1), (27, 1), (50, 1)] }, { coefficient := 2, powers := [(8, 1), (33, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (27, 1), (38, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (27, 1), (43, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
/-- Lean replays the exact selected-row integer certificate. -/
theorem constantIdentity :
    ∑ index, (multipliers index).toPoly *
      (selectedEquations index).toPoly = C (2 : ℤ) := by
  simp (config := { maxSteps := 1000000 })
    [Fin.sum_univ_succ, multipliers, selectedEquations,
    SparsePoly.toPoly, SparseTerm.toPoly]
  ring

/-- The selected rows have no common zero in a characteristic-zero ring. -/
theorem selectedHasNoCommonZero {R : Type*} [CommRing R] [Nontrivial R] [CharZero R]
    (values : Fin 64 → R) :
    ¬ ∀ index : Fin 61,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((2 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (2 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (2 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component64.SelectedLeafB6_6.selectedHasNoCommonZero

end Krenn.Component64.SelectedLeafB6_6
