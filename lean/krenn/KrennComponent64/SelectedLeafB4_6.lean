import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component64.SelectedLeafB4_6

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "6018e2167ea34621b18bc6d46f1cc51996862a842da0184222e9ab68f3411952"
def certificateSHA256 : String := "70d8b1d6bc1e149ce8203a3fe04227b3c3c4d269f55af127adaadf7bac11909d"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 55 → Fin 641 := ![
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
  187,
  193,
  194,
  198,
  200,
  205,
  209,
  222,
  235,
  284,
  309,
  343,
  349,
  350,
  351,
  352,
  356,
  358,
  366,
  367,
  369,
  433,
  444,
  456,
  466,
  468,
  479,
  481,
  507,
  548,
  556,
  557,
  571,
  620,
  634,
  635,
  637,
  638,
  639,
  640
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 55 → SparsePoly (Fin 63) := ![
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
  [{ coefficient := 1, powers := [(13, 1), (24, 1)] }, { coefficient := 1, powers := [(18, 1), (20, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (20, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (41, 1)] }, { coefficient := 1, powers := [(19, 1), (20, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (50, 1)] }, { coefficient := 1, powers := [(23, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (38, 1)] }, { coefficient := 1, powers := [(27, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1), (53, 1)] }, { coefficient := 1, powers := [(53, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1), (50, 1)] }, { coefficient := 1, powers := [(46, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (27, 1), (58, 1)] }, { coefficient := 1, powers := [(27, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (23, 1), (58, 1)] }, { coefficient := 1, powers := [(23, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (24, 1), (43, 1)] }, { coefficient := 1, powers := [(18, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (24, 1), (41, 1)] }, { coefficient := 1, powers := [(19, 1), (20, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (41, 1)] }, { coefficient := 1, powers := [(20, 1), (41, 1)] }, { coefficient := 1, powers := [(24, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (46, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1)] }, { coefficient := 1, powers := [(19, 1), (23, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (53, 1)] }, { coefficient := 1, powers := [(8, 1), (30, 1)] }, { coefficient := 1, powers := [(13, 1), (27, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (59, 1)] }, { coefficient := 1, powers := [(13, 1), (46, 1)] }, { coefficient := 1, powers := [(19, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (59, 1)] }, { coefficient := 1, powers := [(13, 1), (56, 1)] }, { coefficient := 1, powers := [(19, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (43, 1)] }, { coefficient := 1, powers := [(13, 1), (55, 1)] }, { coefficient := 1, powers := [(18, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (44, 1)] }, { coefficient := 1, powers := [(19, 1), (38, 1)] }, { coefficient := 1, powers := [(19, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (41, 1), (50, 1)] }, { coefficient := 1, powers := [(20, 1), (41, 1), (50, 1)] }, { coefficient := 1, powers := [(41, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (41, 1), (52, 1)] }, { coefficient := 1, powers := [(20, 1), (41, 1), (52, 1)] }, { coefficient := 1, powers := [(20, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1), (48, 1)] }, { coefficient := 1, powers := [(24, 1), (43, 1), (48, 1)] }, { coefficient := 1, powers := [(48, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (20, 1), (55, 1)] }, { coefficient := 1, powers := [(13, 1)] }, { coefficient := 1, powers := [(18, 1), (20, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (24, 1), (38, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (43, 1)] }, { coefficient := 1, powers := [(18, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1)] }, { coefficient := 1, powers := [(24, 1), (38, 1), (41, 1)] }, { coefficient := 1, powers := [(24, 1), (44, 1)] }, { coefficient := 1, powers := [(41, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (53, 1)] }, { coefficient := 1, powers := [(27, 1), (39, 1)] }, { coefficient := 1, powers := [(27, 1), (45, 1), (48, 1)] }, { coefficient := 1, powers := [(30, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (38, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(41, 1), (52, 1)] }, { coefficient := 1, powers := [(56, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1), (48, 1)] }, { coefficient := 1, powers := [(6, 1), (59, 1)] }, { coefficient := 1, powers := [(24, 1), (44, 1), (48, 1)] }, { coefficient := 1, powers := [(41, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1), (50, 1)] }, { coefficient := 1, powers := [(38, 1), (41, 1)] }, { coefficient := 1, powers := [(41, 1), (50, 1)] }, { coefficient := 1, powers := [(44, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (27, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (30, 1), (56, 1)] }, { coefficient := 1, powers := [(3, 1), (33, 1), (53, 1)] }, { coefficient := 1, powers := [(27, 1), (41, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (41, 1), (52, 1)] }, { coefficient := 1, powers := [(23, 1), (56, 1)] }, { coefficient := 1, powers := [(27, 1), (46, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1)] }, { coefficient := 1, powers := [(6, 1), (58, 1)] }, { coefficient := 1, powers := [(24, 1), (38, 1)] }, { coefficient := 1, powers := [(24, 1), (43, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (50, 1)] }, { coefficient := 1, powers := [(3, 1), (58, 1)] }, { coefficient := 1, powers := [(20, 1), (50, 1)] }, { coefficient := 1, powers := [(20, 1), (55, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (39, 1), (55, 1)] }, { coefficient := 1, powers := [(2, 1), (45, 1), (51, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (55, 1)] }, { coefficient := 1, powers := [(13, 1), (23, 1), (55, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (35, 1), (58, 1)] }, { coefficient := 1, powers := [(0, 1), (38, 1), (55, 1)] }, { coefficient := 1, powers := [(0, 1), (43, 1), (50, 1)] }, { coefficient := 1, powers := [(38, 1)] }, { coefficient := 1, powers := [(43, 1)] }, { coefficient := 1, powers := [(50, 1)] }, { coefficient := 1, powers := [(55, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (36, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (46, 1), (53, 1)] }, { coefficient := 1, powers := [(5, 1), (27, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (53, 1)] }, { coefficient := 1, powers := [(8, 1), (23, 1), (59, 1)] }, { coefficient := 1, powers := [(8, 1), (30, 1), (46, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (39, 1)] }, { coefficient := 1, powers := [(13, 1), (23, 1), (56, 1)] }, { coefficient := 1, powers := [(13, 1), (27, 1), (46, 1)] }, { coefficient := 1, powers := [(13, 1), (33, 1), (36, 1)] }, { coefficient := 1, powers := [(19, 1), (23, 1), (53, 1)] }, { coefficient := 1, powers := [(19, 1), (27, 1), (39, 1)] }, { coefficient := 1, powers := [(19, 1), (30, 1), (36, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (60, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(37, 1), (61, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(38, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(39, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 55 → SparsePoly (Fin 63) := ![
  [{ coefficient := -2, powers := [(0, 1), (27, 1), (38, 1), (51, 1), (62, 1)] }, { coefficient := -2, powers := [(0, 1), (27, 1), (51, 1), (60, 1), (62, 1)] }],
  [{ coefficient := -3, powers := [(23, 1), (24, 1), (43, 1), (44, 1), (62, 1)] }, { coefficient := -2, powers := [(23, 1), (24, 1), (44, 1), (50, 1), (62, 1)] }, { coefficient := -1, powers := [(23, 1), (24, 1), (44, 1), (60, 1), (62, 1)] }, { coefficient := 2, powers := [(23, 1), (44, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (13, 1), (38, 1), (52, 1), (55, 1), (62, 1)] }, { coefficient := 1, powers := [(0, 1), (13, 1), (43, 1), (50, 1), (52, 1), (62, 1)] }, { coefficient := 1, powers := [(0, 1), (13, 1), (50, 1), (52, 1), (60, 1), (62, 1)] }, { coefficient := 1, powers := [(0, 1), (13, 1), (52, 1), (55, 1), (60, 1), (62, 1)] }, { coefficient := -1, powers := [(13, 1), (38, 1), (52, 1), (62, 1)] }, { coefficient := 1, powers := [(13, 1), (43, 1), (52, 1), (62, 1)] }, { coefficient := 1, powers := [(18, 1), (43, 1), (53, 1), (62, 1)] }, { coefficient := 1, powers := [(18, 1), (53, 1), (60, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (19, 1), (35, 1), (45, 1), (58, 1), (62, 1)] }, { coefficient := 1, powers := [(0, 1), (19, 1), (38, 1), (45, 1), (55, 1), (62, 1)] }, { coefficient := 1, powers := [(0, 1), (19, 1), (43, 1), (45, 1), (50, 1), (62, 1)] }, { coefficient := 1, powers := [(0, 1), (19, 1), (45, 1), (50, 1), (60, 1), (62, 1)] }, { coefficient := 1, powers := [(0, 1), (19, 1), (45, 1), (55, 1), (60, 1), (62, 1)] }, { coefficient := -1, powers := [(5, 1), (41, 1), (43, 1), (58, 1), (62, 1)] }, { coefficient := -1, powers := [(5, 1), (41, 1), (58, 1), (60, 1), (62, 1)] }, { coefficient := -1, powers := [(19, 1), (38, 1), (45, 1), (62, 1)] }, { coefficient := 1, powers := [(19, 1), (43, 1), (45, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (5, 1), (56, 1), (58, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 1), (8, 1), (46, 1), (58, 1), (62, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (5, 1), (53, 1), (58, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 1), (13, 1), (36, 1), (58, 1), (62, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (18, 1), (38, 1), (45, 1), (50, 1), (53, 1), (62, 2)] }, { coefficient := 2, powers := [(0, 1), (18, 1), (45, 1), (50, 1), (53, 1), (60, 1), (62, 2)] }],
  [{ coefficient := 2, powers := [(0, 1), (13, 1), (38, 1), (46, 1), (61, 1), (62, 1)] }, { coefficient := 2, powers := [(0, 1), (13, 1), (46, 1), (60, 1), (61, 1), (62, 1)] }, { coefficient := -2, powers := [(13, 1), (46, 1), (61, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (27, 1), (41, 1), (43, 2), (48, 1), (62, 1)] }, { coefficient := -2, powers := [(18, 1), (27, 1), (41, 1), (43, 1), (48, 1), (50, 1), (62, 1)] }, { coefficient := 1, powers := [(18, 1), (27, 1), (41, 1), (43, 1), (48, 1), (60, 1), (62, 1)] }, { coefficient := -1, powers := [(18, 1), (27, 1), (43, 1), (44, 1), (48, 1), (62, 1)] }, { coefficient := 2, powers := [(18, 1), (27, 1), (44, 1), (48, 1), (50, 1), (62, 1)] }, { coefficient := -1, powers := [(18, 1), (27, 1), (44, 1), (48, 1), (60, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (27, 1), (43, 2), (62, 1)] }, { coefficient := -2, powers := [(13, 1), (27, 1), (43, 1), (50, 1), (62, 1)] }, { coefficient := 1, powers := [(13, 1), (27, 1), (43, 1), (60, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (5, 1), (30, 1), (38, 1), (41, 1), (50, 2), (62, 1)] }, { coefficient := -1, powers := [(5, 1), (20, 1), (30, 1), (38, 1), (41, 1), (50, 2), (62, 1)] }, { coefficient := -1, powers := [(5, 1), (24, 1), (30, 1), (38, 1), (41, 1), (50, 2), (62, 1)] }, { coefficient := -1, powers := [(5, 1), (24, 1), (30, 1), (41, 1), (50, 3), (62, 1)] }, { coefficient := 1, powers := [(5, 1), (24, 1), (30, 1), (44, 1), (50, 2), (62, 1)] }, { coefficient := -1, powers := [(5, 1), (30, 1), (41, 1), (43, 1), (50, 1), (62, 1)] }, { coefficient := -1, powers := [(5, 1), (30, 1), (41, 1), (43, 1), (55, 1), (62, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (41, 1), (50, 2), (62, 1)] }, { coefficient := -1, powers := [(5, 1), (30, 1), (41, 1), (55, 1), (60, 1), (62, 1)] }, { coefficient := 1, powers := [(13, 1), (23, 1), (38, 1), (41, 1), (43, 1), (62, 1)] }, { coefficient := -1, powers := [(13, 1), (23, 1), (41, 1), (43, 2), (62, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (33, 1), (43, 1), (50, 1), (62, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (50, 1), (60, 1), (62, 1)] }, { coefficient := -3, powers := [(19, 1), (23, 1), (43, 2), (62, 1)] }, { coefficient := -1, powers := [(19, 1), (23, 1), (43, 1), (60, 1), (62, 1)] }, { coefficient := 2, powers := [(19, 1), (23, 1), (50, 1), (60, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (38, 1), (51, 1), (56, 1), (62, 1)] }, { coefficient := 1, powers := [(0, 1), (43, 1), (51, 1), (56, 1), (62, 1)] }, { coefficient := -2, powers := [(38, 1), (48, 1), (56, 1), (62, 1)] }, { coefficient := 1, powers := [(43, 1), (48, 1), (56, 1), (62, 1)] }, { coefficient := -1, powers := [(48, 1), (56, 1), (60, 1), (62, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (6, 1), (33, 1), (38, 1), (50, 1), (53, 1), (62, 1)] }, { coefficient := -2, powers := [(0, 1), (6, 1), (33, 1), (50, 1), (53, 1), (60, 1), (62, 1)] }, { coefficient := -1, powers := [(6, 1), (27, 1), (43, 1), (59, 1), (62, 1)] }, { coefficient := 2, powers := [(6, 1), (27, 1), (50, 1), (59, 1), (62, 1)] }, { coefficient := -1, powers := [(6, 1), (27, 1), (59, 1), (60, 1), (62, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (13, 1), (38, 1), (43, 1), (46, 1), (61, 1), (62, 1)] }, { coefficient := -2, powers := [(0, 1), (13, 1), (43, 1), (46, 1), (60, 1), (61, 1), (62, 1)] }, { coefficient := 2, powers := [(13, 1), (43, 1), (46, 1), (61, 1), (62, 1)] }],
  [{ coefficient := 2, powers := [(23, 1), (38, 2), (56, 1), (62, 1)] }, { coefficient := 1, powers := [(23, 1), (38, 1), (43, 1), (56, 1), (62, 1)] }, { coefficient := 1, powers := [(23, 1), (38, 1), (56, 1), (60, 1), (62, 1)] }, { coefficient := -1, powers := [(23, 1), (43, 2), (56, 1), (62, 1)] }, { coefficient := 1, powers := [(23, 1), (43, 1), (56, 1), (60, 1), (62, 1)] }, { coefficient := 1, powers := [(27, 1), (38, 1), (43, 1), (46, 1), (62, 1)] }, { coefficient := -2, powers := [(27, 1), (38, 1), (46, 1), (50, 1), (62, 1)] }, { coefficient := 1, powers := [(27, 1), (38, 1), (46, 1), (60, 1), (62, 1)] }, { coefficient := 1, powers := [(27, 1), (43, 2), (46, 1), (62, 1)] }, { coefficient := -2, powers := [(27, 1), (43, 1), (46, 1), (50, 1), (62, 1)] }, { coefficient := 1, powers := [(27, 1), (43, 1), (46, 1), (60, 1), (62, 1)] }],
  [{ coefficient := -2, powers := [(23, 1), (38, 2), (48, 1), (56, 1), (62, 1)] }, { coefficient := -1, powers := [(23, 1), (38, 1), (43, 1), (48, 1), (56, 1), (62, 1)] }, { coefficient := -1, powers := [(23, 1), (38, 1), (48, 1), (56, 1), (60, 1), (62, 1)] }, { coefficient := 1, powers := [(23, 1), (43, 2), (48, 1), (56, 1), (62, 1)] }, { coefficient := 3, powers := [(23, 1), (43, 1), (44, 1), (53, 1), (62, 1)] }, { coefficient := -1, powers := [(23, 1), (43, 1), (48, 1), (56, 1), (60, 1), (62, 1)] }, { coefficient := 2, powers := [(23, 1), (44, 1), (50, 1), (53, 1), (62, 1)] }, { coefficient := 1, powers := [(23, 1), (44, 1), (53, 1), (60, 1), (62, 1)] }, { coefficient := -1, powers := [(27, 1), (38, 1), (43, 1), (46, 1), (48, 1), (62, 1)] }, { coefficient := 2, powers := [(27, 1), (38, 1), (46, 1), (48, 1), (50, 1), (62, 1)] }, { coefficient := -1, powers := [(27, 1), (38, 1), (46, 1), (48, 1), (60, 1), (62, 1)] }, { coefficient := -1, powers := [(27, 1), (43, 2), (46, 1), (48, 1), (62, 1)] }, { coefficient := 2, powers := [(27, 1), (43, 1), (46, 1), (48, 1), (50, 1), (62, 1)] }, { coefficient := -1, powers := [(27, 1), (43, 1), (46, 1), (48, 1), (60, 1), (62, 1)] }],
  [{ coefficient := 2, powers := [(23, 1), (43, 1), (53, 1), (62, 1)] }, { coefficient := 2, powers := [(23, 1), (50, 1), (53, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (13, 1), (43, 1), (56, 1), (62, 1)] }, { coefficient := 1, powers := [(0, 1), (13, 1), (56, 1), (60, 1), (62, 1)] }, { coefficient := 2, powers := [(0, 1), (19, 1), (38, 1), (53, 1), (62, 1)] }, { coefficient := 2, powers := [(0, 1), (19, 1), (53, 1), (60, 1), (62, 1)] }, { coefficient := -1, powers := [(19, 1), (20, 1), (43, 1), (53, 1), (62, 1)] }, { coefficient := -1, powers := [(19, 1), (20, 1), (53, 1), (60, 1), (62, 1)] }],
  [{ coefficient := -2, powers := [(13, 1), (46, 1), (62, 1)] }],
  [{ coefficient := 3, powers := [(19, 1), (23, 1), (43, 1), (62, 1)] }, { coefficient := 2, powers := [(19, 1), (23, 1), (50, 1), (62, 1)] }, { coefficient := -1, powers := [(19, 1), (23, 1), (60, 1), (62, 1)] }],
  [{ coefficient := 2, powers := [(13, 1), (27, 1), (43, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (43, 1), (59, 1), (62, 1)] }, { coefficient := -1, powers := [(5, 1), (59, 1), (60, 1), (62, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (19, 1), (38, 1), (50, 1), (53, 1), (62, 1)] }, { coefficient := -2, powers := [(0, 1), (19, 1), (50, 1), (53, 1), (60, 1), (62, 1)] }, { coefficient := 2, powers := [(13, 1), (38, 1), (56, 1), (62, 1)] }, { coefficient := -1, powers := [(13, 1), (43, 1), (56, 1), (62, 1)] }, { coefficient := 1, powers := [(13, 1), (56, 1), (60, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(27, 1), (43, 1), (46, 1), (62, 1)] }, { coefficient := 2, powers := [(27, 1), (46, 1), (50, 1), (62, 1)] }, { coefficient := -1, powers := [(27, 1), (46, 1), (60, 1), (62, 1)] }],
  [{ coefficient := 3, powers := [(23, 1), (38, 1), (43, 1), (53, 1), (62, 1)] }, { coefficient := 2, powers := [(23, 1), (38, 1), (50, 1), (53, 1), (62, 1)] }, { coefficient := 1, powers := [(23, 1), (38, 1), (53, 1), (60, 1), (62, 1)] }, { coefficient := 3, powers := [(23, 1), (43, 2), (53, 1), (62, 1)] }, { coefficient := 2, powers := [(23, 1), (43, 1), (50, 1), (53, 1), (62, 1)] }, { coefficient := 1, powers := [(23, 1), (43, 1), (53, 1), (60, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (20, 1), (30, 1), (38, 1), (50, 2), (52, 1), (62, 1)] }, { coefficient := -1, powers := [(5, 1), (30, 1), (38, 1), (50, 1), (52, 1), (62, 1)] }],
  [{ coefficient := -2, powers := [(0, 2), (38, 1), (43, 1), (50, 1), (53, 1), (62, 1)] }, { coefficient := -2, powers := [(0, 2), (43, 1), (50, 1), (53, 1), (60, 1), (62, 1)] }, { coefficient := -2, powers := [(0, 1), (24, 1), (38, 2), (50, 1), (53, 1), (62, 1)] }, { coefficient := -2, powers := [(0, 1), (24, 1), (38, 1), (43, 1), (50, 1), (53, 1), (62, 1)] }, { coefficient := -2, powers := [(0, 1), (24, 1), (38, 1), (50, 1), (53, 1), (60, 1), (62, 1)] }, { coefficient := -2, powers := [(0, 1), (24, 1), (43, 1), (50, 1), (53, 1), (60, 1), (62, 1)] }, { coefficient := 1, powers := [(0, 1), (35, 1), (53, 1), (58, 1), (62, 1)] }, { coefficient := -2, powers := [(0, 1), (38, 1), (50, 1), (53, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 1), (38, 1), (53, 1), (55, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 1), (43, 1), (50, 1), (53, 1), (62, 1)] }, { coefficient := -3, powers := [(0, 1), (50, 1), (53, 1), (60, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 1), (53, 1), (55, 1), (60, 1), (62, 1)] }, { coefficient := 1, powers := [(20, 1), (43, 1), (53, 1), (55, 1), (62, 1)] }, { coefficient := 1, powers := [(20, 1), (53, 1), (55, 1), (60, 1), (62, 1)] }, { coefficient := 1, powers := [(38, 1), (53, 1), (62, 1)] }, { coefficient := 1, powers := [(53, 1), (60, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (38, 1), (46, 1), (55, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 1), (43, 1), (46, 1), (50, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 1), (46, 1), (50, 1), (60, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 1), (46, 1), (55, 1), (60, 1), (62, 1)] }, { coefficient := 1, powers := [(38, 1), (46, 1), (62, 1)] }, { coefficient := -1, powers := [(43, 1), (46, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (27, 1), (35, 1), (58, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 1), (27, 1), (38, 1), (55, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 1), (27, 1), (43, 2), (62, 1)] }, { coefficient := 1, powers := [(0, 1), (27, 1), (43, 1), (50, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 1), (27, 1), (43, 1), (60, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 1), (27, 1), (50, 1), (60, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 1), (27, 1), (55, 1), (60, 1), (62, 1)] }, { coefficient := -1, powers := [(24, 1), (27, 1), (38, 1), (43, 1), (62, 1)] }, { coefficient := 2, powers := [(24, 1), (27, 1), (38, 1), (50, 1), (62, 1)] }, { coefficient := -1, powers := [(24, 1), (27, 1), (38, 1), (60, 1), (62, 1)] }, { coefficient := -1, powers := [(24, 1), (27, 1), (43, 2), (62, 1)] }, { coefficient := 2, powers := [(24, 1), (27, 1), (43, 1), (50, 1), (62, 1)] }, { coefficient := -1, powers := [(24, 1), (27, 1), (43, 1), (60, 1), (62, 1)] }, { coefficient := 1, powers := [(27, 1), (38, 1), (62, 1)] }, { coefficient := -1, powers := [(27, 1), (43, 1), (62, 1)] }, { coefficient := 2, powers := [(27, 1), (50, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (23, 1), (35, 1), (58, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 1), (23, 1), (38, 1), (55, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 1), (23, 1), (43, 1), (50, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 1), (23, 1), (50, 1), (60, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 1), (23, 1), (55, 1), (60, 1), (62, 1)] }, { coefficient := 1, powers := [(23, 1), (38, 1), (62, 1)] }, { coefficient := -1, powers := [(23, 1), (43, 1), (62, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (23, 1), (38, 1), (56, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 1), (23, 1), (43, 1), (56, 1), (62, 1)] }, { coefficient := 1, powers := [(0, 1), (23, 1), (56, 1), (60, 1), (62, 1)] }, { coefficient := 2, powers := [(0, 1), (27, 1), (38, 1), (46, 1), (62, 1)] }, { coefficient := 2, powers := [(0, 1), (27, 1), (46, 1), (60, 1), (62, 1)] }, { coefficient := 1, powers := [(20, 1), (23, 1), (38, 1), (56, 1), (62, 1)] }, { coefficient := -1, powers := [(20, 1), (23, 1), (43, 1), (56, 1), (62, 1)] }],
  [{ coefficient := -3, powers := [(20, 1), (23, 1), (43, 1), (53, 1), (62, 1)] }, { coefficient := -2, powers := [(20, 1), (23, 1), (50, 1), (53, 1), (62, 1)] }, { coefficient := -1, powers := [(20, 1), (23, 1), (53, 1), (60, 1), (62, 1)] }, { coefficient := -2, powers := [(23, 1), (53, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (24, 1), (30, 1), (38, 1), (50, 1), (52, 1), (62, 1)] }, { coefficient := 1, powers := [(5, 1), (24, 1), (30, 1), (50, 2), (52, 1), (62, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (38, 1), (52, 1), (62, 1)] }, { coefficient := -1, powers := [(5, 1), (30, 1), (52, 1), (60, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (5, 1), (30, 1), (38, 1), (50, 2), (62, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (43, 1), (50, 1), (62, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (43, 1), (55, 1), (62, 1)] }, { coefficient := -1, powers := [(5, 1), (30, 1), (50, 2), (62, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (50, 1), (60, 1), (62, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (55, 1), (60, 1), (62, 1)] }, { coefficient := -1, powers := [(13, 1), (23, 1), (38, 1), (43, 1), (62, 1)] }, { coefficient := 1, powers := [(13, 1), (23, 1), (43, 2), (62, 1)] }],
  [{ coefficient := -1, powers := [(18, 1), (27, 1), (41, 1), (43, 1), (45, 1), (62, 1)] }, { coefficient := 2, powers := [(18, 1), (27, 1), (41, 1), (45, 1), (50, 1), (62, 1)] }, { coefficient := -1, powers := [(18, 1), (27, 1), (41, 1), (45, 1), (60, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(23, 1), (38, 1), (56, 1), (62, 1)] }, { coefficient := 1, powers := [(23, 1), (43, 1), (56, 1), (62, 1)] }],
  [{ coefficient := 2, powers := [(23, 1), (38, 1), (48, 1), (56, 1), (62, 1)] }, { coefficient := -3, powers := [(23, 1), (41, 1), (43, 1), (53, 1), (62, 1)] }, { coefficient := -2, powers := [(23, 1), (41, 1), (50, 1), (53, 1), (62, 1)] }, { coefficient := -1, powers := [(23, 1), (41, 1), (53, 1), (60, 1), (62, 1)] }, { coefficient := -1, powers := [(23, 1), (43, 1), (48, 1), (56, 1), (62, 1)] }, { coefficient := 1, powers := [(23, 1), (48, 1), (56, 1), (60, 1), (62, 1)] }, { coefficient := 1, powers := [(27, 1), (43, 1), (46, 1), (48, 1), (62, 1)] }, { coefficient := -2, powers := [(27, 1), (46, 1), (48, 1), (50, 1), (62, 1)] }, { coefficient := 1, powers := [(27, 1), (46, 1), (48, 1), (60, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (20, 1), (30, 1), (50, 2), (52, 1), (62, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (50, 1), (52, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (19, 1), (35, 1), (58, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 1), (19, 1), (38, 1), (55, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 1), (19, 1), (43, 1), (50, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 1), (19, 1), (50, 1), (60, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 1), (19, 1), (55, 1), (60, 1), (62, 1)] }, { coefficient := 1, powers := [(19, 1), (38, 1), (62, 1)] }, { coefficient := -1, powers := [(19, 1), (43, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (20, 1), (30, 1), (50, 2), (62, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (60, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (27, 1), (43, 1), (45, 1), (62, 1)] }, { coefficient := -2, powers := [(18, 1), (27, 1), (45, 1), (50, 1), (62, 1)] }, { coefficient := 1, powers := [(18, 1), (27, 1), (45, 1), (60, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (24, 1), (30, 1), (50, 1), (52, 1), (62, 1)] }, { coefficient := -1, powers := [(5, 1), (30, 1), (52, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (43, 1), (58, 1), (62, 1)] }, { coefficient := 1, powers := [(5, 1), (58, 1), (60, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (13, 1), (38, 1), (55, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 1), (13, 1), (43, 1), (50, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 1), (13, 1), (50, 1), (60, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 1), (13, 1), (55, 1), (60, 1), (62, 1)] }, { coefficient := 1, powers := [(13, 1), (38, 1), (62, 1)] }, { coefficient := -1, powers := [(13, 1), (43, 1), (62, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (5, 1), (33, 1), (38, 1), (50, 1), (53, 1), (62, 1)] }, { coefficient := 2, powers := [(0, 1), (5, 1), (33, 1), (50, 1), (53, 1), (60, 1), (62, 1)] }, { coefficient := 2, powers := [(0, 1), (19, 1), (23, 1), (38, 1), (50, 1), (53, 1), (62, 1)] }, { coefficient := 2, powers := [(0, 1), (19, 1), (23, 1), (50, 1), (53, 1), (60, 1), (62, 1)] }, { coefficient := 1, powers := [(5, 1), (27, 1), (43, 1), (59, 1), (62, 1)] }, { coefficient := -2, powers := [(5, 1), (27, 1), (50, 1), (59, 1), (62, 1)] }, { coefficient := 1, powers := [(5, 1), (27, 1), (59, 1), (60, 1), (62, 1)] }, { coefficient := -2, powers := [(13, 1), (23, 1), (38, 1), (56, 1), (62, 1)] }, { coefficient := 1, powers := [(13, 1), (23, 1), (43, 1), (56, 1), (62, 1)] }, { coefficient := -1, powers := [(13, 1), (23, 1), (56, 1), (60, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (30, 1), (43, 1), (56, 1), (62, 1)] }, { coefficient := -1, powers := [(5, 1), (30, 1), (56, 1), (60, 1), (62, 1)] }, { coefficient := -1, powers := [(5, 1), (33, 1), (43, 1), (53, 1), (62, 1)] }, { coefficient := -1, powers := [(5, 1), (33, 1), (53, 1), (60, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (38, 1), (56, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 1), (56, 1), (60, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(62, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (35, 1), (58, 1), (62, 1)] }, { coefficient := 1, powers := [(0, 1), (38, 1), (55, 1), (62, 1)] }, { coefficient := 1, powers := [(0, 1), (43, 1), (50, 1), (62, 1)] }, { coefficient := 1, powers := [(0, 1), (50, 1), (60, 1), (62, 1)] }, { coefficient := 1, powers := [(0, 1), (55, 1), (60, 1), (62, 1)] }, { coefficient := -1, powers := [(38, 1), (62, 1)] }, { coefficient := 1, powers := [(43, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (30, 1), (38, 1), (56, 1), (62, 1)] }, { coefficient := -1, powers := [(5, 1), (30, 1), (44, 1), (52, 1), (62, 1)] }, { coefficient := 2, powers := [(13, 1), (27, 1), (46, 1), (50, 1), (62, 1)] }, { coefficient := 2, powers := [(19, 1), (23, 1), (43, 1), (53, 1), (62, 1)] }, { coefficient := 1, powers := [(50, 1), (62, 1)] }, { coefficient := 1, powers := [(55, 1), (62, 1)] }],
  [{ coefficient := 2, powers := [(0, 2), (38, 1), (43, 1), (46, 1), (50, 1), (53, 1), (62, 1)] }, { coefficient := 2, powers := [(0, 2), (43, 1), (46, 1), (50, 1), (53, 1), (60, 1), (62, 1)] }, { coefficient := 2, powers := [(0, 1), (24, 1), (38, 2), (46, 1), (50, 1), (53, 1), (62, 1)] }, { coefficient := 2, powers := [(0, 1), (24, 1), (38, 1), (43, 1), (46, 1), (50, 1), (53, 1), (62, 1)] }, { coefficient := 2, powers := [(0, 1), (24, 1), (38, 1), (46, 1), (50, 1), (53, 1), (60, 1), (62, 1)] }, { coefficient := 2, powers := [(0, 1), (24, 1), (43, 1), (46, 1), (50, 1), (53, 1), (60, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 1), (35, 1), (36, 1), (58, 1), (59, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 1), (35, 1), (39, 1), (56, 1), (58, 1), (62, 1)] }, { coefficient := -2, powers := [(0, 1), (35, 1), (46, 1), (53, 1), (58, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 1), (36, 1), (38, 1), (55, 1), (59, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 1), (36, 1), (43, 1), (50, 1), (59, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 1), (36, 1), (50, 1), (59, 1), (60, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 1), (36, 1), (55, 1), (59, 1), (60, 1), (62, 1)] }, { coefficient := 2, powers := [(0, 1), (38, 1), (45, 1), (51, 1), (56, 1), (62, 1)] }, { coefficient := 2, powers := [(0, 1), (38, 1), (46, 1), (50, 1), (53, 1), (62, 1)] }, { coefficient := 1, powers := [(0, 1), (38, 1), (46, 1), (53, 1), (55, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 1), (39, 1), (43, 1), (50, 1), (56, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 1), (39, 1), (50, 1), (56, 1), (60, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 1), (43, 1), (45, 1), (51, 1), (56, 1), (62, 1)] }, { coefficient := 1, powers := [(0, 1), (43, 1), (46, 1), (50, 1), (53, 1), (62, 1)] }, { coefficient := 1, powers := [(0, 1), (45, 1), (51, 1), (56, 1), (60, 1), (62, 1)] }, { coefficient := 3, powers := [(0, 1), (46, 1), (50, 1), (53, 1), (60, 1), (62, 1)] }, { coefficient := 1, powers := [(0, 1), (46, 1), (53, 1), (55, 1), (60, 1), (62, 1)] }, { coefficient := -1, powers := [(20, 1), (43, 1), (46, 1), (53, 1), (55, 1), (62, 1)] }, { coefficient := -1, powers := [(20, 1), (46, 1), (53, 1), (55, 1), (60, 1), (62, 1)] }, { coefficient := 1, powers := [(36, 1), (38, 1), (59, 1), (62, 1)] }, { coefficient := -1, powers := [(36, 1), (43, 1), (59, 1), (62, 1)] }, { coefficient := 1, powers := [(38, 1), (39, 1), (56, 1), (62, 1)] }, { coefficient := 2, powers := [(38, 1), (45, 1), (48, 1), (56, 1), (62, 1)] }, { coefficient := -1, powers := [(38, 1), (46, 1), (53, 1), (62, 1)] }, { coefficient := -1, powers := [(39, 1), (43, 1), (56, 1), (62, 1)] }, { coefficient := -1, powers := [(43, 1), (45, 1), (48, 1), (56, 1), (62, 1)] }, { coefficient := 1, powers := [(45, 1), (48, 1), (56, 1), (60, 1), (62, 1)] }, { coefficient := -1, powers := [(46, 1), (53, 1), (60, 1), (62, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (13, 1), (27, 1), (38, 1), (43, 1), (46, 1), (62, 1)] }, { coefficient := 2, powers := [(0, 1), (13, 1), (27, 1), (43, 1), (46, 1), (60, 1), (62, 1)] }, { coefficient := -2, powers := [(13, 1), (27, 1), (43, 1), (46, 1), (62, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (6, 1), (18, 1), (33, 1), (38, 1), (45, 1), (50, 1), (53, 1), (62, 1)] }, { coefficient := -2, powers := [(0, 1), (6, 1), (18, 1), (33, 1), (45, 1), (50, 1), (53, 1), (60, 1), (62, 1)] }, { coefficient := -2, powers := [] }],
  [{ coefficient := -1, powers := [(0, 1), (8, 1), (33, 1), (35, 1), (58, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 1), (8, 1), (33, 1), (38, 1), (55, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 1), (8, 1), (33, 1), (43, 1), (50, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 1), (8, 1), (33, 1), (50, 1), (60, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 1), (8, 1), (33, 1), (55, 1), (60, 1), (62, 1)] }, { coefficient := 1, powers := [(0, 1), (19, 1), (27, 1), (35, 1), (58, 1), (62, 1)] }, { coefficient := 1, powers := [(0, 1), (19, 1), (27, 1), (38, 1), (55, 1), (62, 1)] }, { coefficient := 1, powers := [(0, 1), (19, 1), (27, 1), (43, 2), (62, 1)] }, { coefficient := -1, powers := [(0, 1), (19, 1), (27, 1), (43, 1), (50, 1), (62, 1)] }, { coefficient := 1, powers := [(0, 1), (19, 1), (27, 1), (43, 1), (60, 1), (62, 1)] }, { coefficient := 1, powers := [(0, 1), (19, 1), (27, 1), (50, 1), (60, 1), (62, 1)] }, { coefficient := 1, powers := [(0, 1), (19, 1), (27, 1), (55, 1), (60, 1), (62, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (38, 1), (62, 1)] }, { coefficient := -1, powers := [(8, 1), (33, 1), (43, 1), (62, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (27, 1), (38, 1), (43, 1), (62, 1)] }, { coefficient := -2, powers := [(19, 1), (24, 1), (27, 1), (38, 1), (50, 1), (62, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (27, 1), (38, 1), (60, 1), (62, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (27, 1), (43, 2), (62, 1)] }, { coefficient := -2, powers := [(19, 1), (24, 1), (27, 1), (43, 1), (50, 1), (62, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (27, 1), (43, 1), (60, 1), (62, 1)] }, { coefficient := -1, powers := [(19, 1), (27, 1), (38, 1), (62, 1)] }, { coefficient := 1, powers := [(19, 1), (27, 1), (43, 1), (62, 1)] }, { coefficient := -2, powers := [(19, 1), (27, 1), (50, 1), (62, 1)] }]
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
    (values : Fin 63 → R) :
    ¬ ∀ index : Fin 55,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((2 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (2 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (2 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component64.SelectedLeafB4_6.selectedHasNoCommonZero

end Krenn.Component64.SelectedLeafB4_6
