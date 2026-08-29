import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component18.SelectedLeafB4_2_1_4

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "f4b92b55807120dc6a639be73cdb8de9376e4b6a01ebbc847aaed082bf827694"
def certificateSHA256 : String := "f5b034179dd1c4323656af86641526fb9c93c7059a7fccf8cdf2bd593a72be97"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 54 → Fin 670 := ![
  0,
  2,
  7,
  10,
  19,
  23,
  24,
  142,
  145,
  148,
  149,
  152,
  163,
  164,
  168,
  225,
  308,
  315,
  318,
  319,
  323,
  327,
  403,
  405,
  426,
  431,
  433,
  437,
  440,
  442,
  443,
  449,
  458,
  468,
  506,
  551,
  562,
  564,
  580,
  581,
  606,
  607,
  608,
  656,
  657,
  658,
  659,
  660,
  663,
  665,
  666,
  667,
  668,
  669
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 54 → SparsePoly (Fin 65) := ![
  [{ coefficient := 1, powers := [(3, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (34, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(30, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(34, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (54, 1)] }, { coefficient := 1, powers := [(19, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (25, 1)] }, { coefficient := 1, powers := [(15, 1), (19, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (26, 1)] }, { coefficient := 1, powers := [(15, 1), (19, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (45, 1)] }, { coefficient := 1, powers := [(16, 1), (19, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (45, 1)] }, { coefficient := 1, powers := [(18, 1), (19, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (49, 1)] }, { coefficient := 1, powers := [(18, 1), (20, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (53, 1)] }, { coefficient := 1, powers := [(31, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (25, 1), (45, 1)] }, { coefficient := 1, powers := [(16, 1), (19, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (47, 1)] }, { coefficient := 1, powers := [(16, 1), (42, 1)] }, { coefficient := 1, powers := [(16, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (47, 1)] }, { coefficient := 1, powers := [(18, 1), (42, 1)] }, { coefficient := 1, powers := [(18, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (54, 1)] }, { coefficient := 1, powers := [(31, 1), (43, 1)] }, { coefficient := 1, powers := [(34, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(30, 1), (53, 1)] }, { coefficient := 1, powers := [(31, 1), (42, 1)] }, { coefficient := 1, powers := [(31, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1), (52, 1)] }, { coefficient := 1, powers := [(19, 1), (45, 1), (52, 1)] }, { coefficient := 1, powers := [(45, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (49, 1), (52, 1)] }, { coefficient := 1, powers := [(20, 1), (45, 1), (52, 1)] }, { coefficient := 1, powers := [(49, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (19, 1), (52, 1)] }, { coefficient := 1, powers := [(17, 1), (19, 1), (56, 1)] }, { coefficient := 1, powers := [(17, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (19, 1), (57, 1)] }, { coefficient := 1, powers := [(17, 1), (26, 1), (45, 1)] }, { coefficient := 1, powers := [(18, 1), (19, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (53, 1)] }, { coefficient := 1, powers := [(3, 1), (26, 1), (59, 1)] }, { coefficient := 1, powers := [(19, 1), (53, 1)] }, { coefficient := 1, powers := [(26, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (47, 1)] }, { coefficient := 1, powers := [(17, 1), (29, 1), (47, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (42, 1)] }, { coefficient := 1, powers := [(18, 1), (30, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (49, 1)] }, { coefficient := 1, powers := [(5, 1), (37, 1)] }, { coefficient := 1, powers := [(17, 1), (29, 1), (49, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1)] }, { coefficient := 1, powers := [(13, 1), (31, 1)] }, { coefficient := 1, powers := [(17, 1), (23, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (59, 1)] }, { coefficient := 1, powers := [(17, 1), (20, 1), (52, 1)] }, { coefficient := 1, powers := [(17, 1), (20, 1), (56, 1)] }, { coefficient := 1, powers := [(17, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (59, 1)] }, { coefficient := 1, powers := [(17, 1), (26, 1), (42, 1)] }, { coefficient := 1, powers := [(17, 1), (26, 1), (46, 1)] }, { coefficient := 1, powers := [(17, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (60, 1)] }, { coefficient := 1, powers := [(13, 1), (26, 1), (47, 1)] }, { coefficient := 1, powers := [(13, 1), (57, 1)] }, { coefficient := 1, powers := [(18, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (42, 1)] }, { coefficient := 1, powers := [(17, 1), (46, 1)] }, { coefficient := 1, powers := [(17, 1), (52, 1)] }, { coefficient := 1, powers := [(17, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1), (53, 1)] }, { coefficient := 1, powers := [(19, 1), (45, 1), (53, 1)] }, { coefficient := 1, powers := [(19, 1), (57, 1)] }, { coefficient := 1, powers := [(26, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (49, 1), (53, 1)] }, { coefficient := 1, powers := [(20, 1), (45, 1), (53, 1)] }, { coefficient := 1, powers := [(20, 1), (57, 1)] }, { coefficient := 1, powers := [(26, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (31, 1), (60, 1)] }, { coefficient := 1, powers := [(4, 1), (34, 1), (57, 1)] }, { coefficient := 1, powers := [(4, 1), (37, 1), (54, 1)] }, { coefficient := 1, powers := [(16, 1), (30, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (26, 1), (47, 1)] }, { coefficient := 1, powers := [(11, 1), (57, 1)] }, { coefficient := 1, powers := [(16, 1), (26, 1), (42, 1)] }, { coefficient := 1, powers := [(16, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (45, 1), (53, 1)] }, { coefficient := 1, powers := [(24, 1), (57, 1)] }, { coefficient := 1, powers := [(31, 1), (49, 1)] }, { coefficient := 1, powers := [(37, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(30, 1), (45, 1), (53, 1)] }, { coefficient := 1, powers := [(30, 1), (57, 1)] }, { coefficient := 1, powers := [(31, 1), (42, 1), (45, 1)] }, { coefficient := 1, powers := [(31, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1)] }, { coefficient := 1, powers := [(6, 1), (59, 1)] }, { coefficient := 1, powers := [(25, 1), (42, 1)] }, { coefficient := 1, powers := [(25, 1), (46, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (52, 1)] }, { coefficient := 1, powers := [(3, 1), (59, 1)] }, { coefficient := 1, powers := [(19, 1), (52, 1)] }, { coefficient := 1, powers := [(19, 1), (56, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(4, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (59, 1)] }, { coefficient := 1, powers := [(11, 1), (46, 1)] }, { coefficient := 1, powers := [(11, 1), (56, 1)] }, { coefficient := 1, powers := [(15, 1), (42, 1)] }, { coefficient := 1, powers := [(15, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (52, 1)] }, { coefficient := 1, powers := [(22, 1), (56, 1)] }, { coefficient := 1, powers := [(28, 1), (42, 1)] }, { coefficient := 1, powers := [(28, 1), (46, 1)] }, { coefficient := 1, powers := [(33, 1), (39, 1)] }, { coefficient := 1, powers := [(36, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (38, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1)] }, { coefficient := 1, powers := [(3, 1), (25, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (19, 1), (59, 1)] }, { coefficient := 1, powers := [(19, 1)] }, { coefficient := 1, powers := [(25, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (39, 1), (59, 1)] }, { coefficient := 1, powers := [(1, 1), (42, 1), (56, 1)] }, { coefficient := 1, powers := [(1, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(4, 1), (28, 1), (59, 1)] }, { coefficient := 1, powers := [(4, 1), (33, 1), (56, 1)] }, { coefficient := 1, powers := [(4, 1), (36, 1), (52, 1)] }, { coefficient := 1, powers := [(7, 1), (22, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (33, 1), (46, 1)] }, { coefficient := 1, powers := [(7, 1), (36, 1), (42, 1)] }, { coefficient := 1, powers := [(11, 1), (22, 1), (56, 1)] }, { coefficient := 1, powers := [(11, 1), (28, 1), (46, 1)] }, { coefficient := 1, powers := [(11, 1), (36, 1), (39, 1)] }, { coefficient := 1, powers := [(15, 1), (22, 1), (52, 1)] }, { coefficient := 1, powers := [(15, 1), (28, 1), (42, 1)] }, { coefficient := 1, powers := [(15, 1), (33, 1), (39, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (40, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (43, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (49, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (37, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (49, 1)] }, { coefficient := 1, powers := [(8, 1), (37, 1), (43, 1)] }, { coefficient := 1, powers := [(13, 1), (24, 1), (57, 1)] }, { coefficient := 1, powers := [(13, 1), (31, 1), (49, 1)] }, { coefficient := 1, powers := [(13, 1), (37, 1), (40, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (54, 1)] }, { coefficient := 1, powers := [(18, 1), (31, 1), (43, 1)] }, { coefficient := 1, powers := [(18, 1), (34, 1), (40, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (61, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1)] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(43, 1)] }],
  [{ coefficient := 1, powers := [(56, 1)] }],
  [{ coefficient := 1, powers := [(57, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(25, 1), (64, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(28, 1)] }],
  [{ coefficient := 1, powers := [(31, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 54 → SparsePoly (Fin 65) := ![
  [{ coefficient := -2, powers := [(8, 1), (15, 1), (22, 1), (24, 1), (38, 1), (42, 1), (59, 2)] }],
  [{ coefficient := 1, powers := [(5, 1), (33, 1), (46, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1), (42, 1), (57, 1)] }, { coefficient := 1, powers := [(18, 1), (22, 1), (40, 1), (59, 1)] }, { coefficient := 2, powers := [(18, 1), (33, 1), (40, 1), (46, 1)] }, { coefficient := 2, powers := [(18, 1), (36, 1), (40, 1), (42, 1)] }, { coefficient := -1, powers := [(18, 1), (36, 1), (40, 1), (52, 1)] }],
  [{ coefficient := -2, powers := [(3, 1), (15, 1), (22, 1), (24, 1), (38, 1), (42, 1), (57, 1), (59, 2), (64, 1)] }, { coefficient := -1, powers := [(7, 1), (22, 1), (24, 1), (57, 1), (59, 1), (64, 1)] }, { coefficient := -1, powers := [(7, 1), (24, 1), (33, 1), (46, 1), (57, 1), (64, 1)] }, { coefficient := -1, powers := [(7, 1), (24, 1), (36, 1), (42, 1), (57, 1), (64, 1)] }, { coefficient := 1, powers := [(7, 1), (24, 1), (36, 1), (52, 1), (57, 1), (64, 1)] }, { coefficient := -1, powers := [(15, 1), (22, 1), (24, 1), (38, 1), (42, 1), (57, 1), (59, 1), (64, 1)] }, { coefficient := -1, powers := [(15, 1), (24, 1), (25, 1), (33, 1), (39, 1), (42, 1), (57, 1), (64, 1)] }, { coefficient := -1, powers := [(15, 1), (24, 1), (25, 1), (36, 1), (39, 1), (42, 1), (57, 1), (64, 1)] }, { coefficient := -1, powers := [(15, 1), (24, 1), (33, 1), (39, 1), (57, 1), (64, 1)] }],
  [{ coefficient := -2, powers := [(3, 1), (15, 1), (22, 1), (24, 1), (26, 1), (38, 1), (42, 1), (59, 2)] }, { coefficient := -1, powers := [(7, 1), (22, 1), (24, 1), (26, 1), (59, 1)] }, { coefficient := -1, powers := [(7, 1), (24, 1), (26, 1), (33, 1), (46, 1)] }, { coefficient := -1, powers := [(7, 1), (24, 1), (26, 1), (36, 1), (42, 1)] }, { coefficient := 1, powers := [(7, 1), (24, 1), (26, 1), (36, 1), (52, 1)] }, { coefficient := -1, powers := [(15, 1), (22, 1), (24, 1), (26, 1), (38, 1), (42, 1), (59, 1)] }, { coefficient := -1, powers := [(15, 1), (24, 1), (25, 1), (26, 1), (33, 1), (39, 1), (42, 1)] }, { coefficient := -1, powers := [(15, 1), (24, 1), (25, 1), (26, 1), (36, 1), (39, 1), (42, 1)] }, { coefficient := -1, powers := [(15, 1), (24, 1), (26, 1), (33, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (17, 1), (22, 1), (49, 1), (59, 1)] }, { coefficient := -1, powers := [(4, 1), (17, 1), (36, 1), (49, 1), (52, 1)] }, { coefficient := -1, powers := [(7, 1), (17, 1), (33, 1), (46, 1), (49, 1)] }, { coefficient := -1, powers := [(7, 1), (17, 1), (36, 1), (42, 1), (49, 1)] }, { coefficient := 1, powers := [(15, 1), (17, 1), (22, 1), (38, 1), (42, 1), (45, 1), (48, 1), (59, 1)] }, { coefficient := -2, powers := [(15, 1), (17, 1), (22, 1), (38, 1), (42, 1), (49, 1), (59, 1)] }, { coefficient := -1, powers := [(15, 1), (17, 1), (25, 1), (33, 1), (39, 1), (42, 1), (49, 1)] }, { coefficient := -1, powers := [(15, 1), (17, 1), (25, 1), (36, 1), (39, 1), (42, 1), (49, 1)] }, { coefficient := -1, powers := [(15, 1), (17, 1), (33, 1), (39, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (16, 1), (22, 1), (59, 1)] }, { coefficient := -1, powers := [(5, 1), (16, 1), (36, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (15, 1), (25, 1), (33, 1), (42, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (15, 1), (25, 1), (36, 1), (42, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (15, 1), (33, 1), (57, 1)] }, { coefficient := 2, powers := [(15, 1), (18, 1), (25, 1), (33, 1), (40, 1), (42, 1)] }, { coefficient := 2, powers := [(15, 1), (18, 1), (25, 1), (36, 1), (40, 1), (42, 1)] }, { coefficient := 2, powers := [(15, 1), (18, 1), (33, 1), (40, 1)] }],
  [{ coefficient := 2, powers := [(15, 1), (18, 1), (22, 1), (24, 1), (38, 1), (42, 1), (52, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (22, 1), (24, 1), (59, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (36, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (45, 1), (46, 1), (53, 1), (61, 1), (63, 1)] }, { coefficient := -1, powers := [(36, 1), (39, 1), (45, 1), (53, 1), (61, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(22, 1), (45, 1), (46, 1), (61, 1), (63, 1)] }, { coefficient := 1, powers := [(36, 1), (39, 1), (45, 1), (61, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (26, 1), (46, 1), (61, 1), (63, 1)] }, { coefficient := -1, powers := [(26, 1), (36, 1), (39, 1), (61, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(15, 1), (22, 1), (34, 1), (38, 1), (42, 1), (48, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (29, 1), (33, 1), (46, 1), (54, 1)] }, { coefficient := -1, powers := [(7, 1), (29, 1), (36, 1), (42, 1), (54, 1)] }, { coefficient := -1, powers := [(15, 1), (22, 1), (29, 1), (38, 1), (42, 1), (54, 1), (59, 1)] }, { coefficient := -1, powers := [(15, 1), (25, 1), (29, 1), (33, 1), (39, 1), (42, 1), (54, 1)] }, { coefficient := -1, powers := [(15, 1), (25, 1), (29, 1), (36, 1), (39, 1), (42, 1), (54, 1)] }, { coefficient := -1, powers := [(15, 1), (29, 1), (33, 1), (39, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (13, 1), (22, 1), (45, 1), (59, 1)] }, { coefficient := -1, powers := [(4, 1), (13, 1), (36, 1), (45, 1), (52, 1)] }, { coefficient := -1, powers := [(7, 1), (13, 1), (33, 1), (45, 1), (46, 1)] }, { coefficient := -1, powers := [(7, 1), (13, 1), (36, 1), (42, 1), (45, 1)] }, { coefficient := -1, powers := [(13, 1), (15, 1), (22, 1), (38, 1), (42, 1), (45, 1), (59, 1)] }, { coefficient := -1, powers := [(13, 1), (15, 1), (25, 1), (33, 1), (39, 1), (42, 1), (45, 1)] }, { coefficient := -1, powers := [(13, 1), (15, 1), (25, 1), (36, 1), (39, 1), (42, 1), (45, 1)] }, { coefficient := -1, powers := [(13, 1), (15, 1), (33, 1), (39, 1), (45, 1)] }],
  [{ coefficient := -1, powers := [(22, 1), (46, 1), (53, 1), (61, 1), (63, 1)] }, { coefficient := 1, powers := [(36, 1), (39, 1), (53, 1), (61, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (22, 1), (26, 1), (46, 1), (61, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (26, 1), (36, 1), (39, 1), (61, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (20, 1), (29, 1), (33, 1), (46, 1), (54, 1)] }, { coefficient := 1, powers := [(7, 1), (20, 1), (29, 1), (36, 1), (42, 1), (54, 1)] }, { coefficient := 1, powers := [(15, 1), (20, 1), (22, 1), (29, 1), (38, 1), (42, 1), (54, 1), (59, 1)] }, { coefficient := 1, powers := [(15, 1), (20, 1), (25, 1), (29, 1), (33, 1), (39, 1), (42, 1), (54, 1)] }, { coefficient := 1, powers := [(15, 1), (20, 1), (25, 1), (29, 1), (36, 1), (39, 1), (42, 1), (54, 1)] }, { coefficient := 1, powers := [(15, 1), (20, 1), (29, 1), (33, 1), (39, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (18, 1), (22, 1), (59, 1)] }, { coefficient := 1, powers := [(4, 1), (18, 1), (36, 1), (52, 1)] }, { coefficient := -1, powers := [(7, 1), (18, 1), (22, 1), (59, 1)] }, { coefficient := -1, powers := [(7, 1), (18, 1), (33, 1), (46, 1)] }, { coefficient := -1, powers := [(7, 1), (18, 1), (36, 1), (42, 1)] }, { coefficient := 1, powers := [(7, 1), (18, 1), (36, 1), (52, 1)] }, { coefficient := 1, powers := [(15, 1), (18, 1), (22, 1), (38, 1), (42, 1), (59, 1)] }, { coefficient := -1, powers := [(15, 1), (18, 1), (25, 1), (33, 1), (39, 1), (42, 1)] }, { coefficient := -1, powers := [(15, 1), (18, 1), (25, 1), (36, 1), (39, 1), (42, 1)] }, { coefficient := -1, powers := [(15, 1), (18, 1), (33, 1), (39, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (18, 1), (20, 1), (33, 1), (45, 1), (46, 1), (54, 1), (63, 1)] }, { coefficient := -1, powers := [(7, 1), (18, 1), (20, 1), (36, 1), (42, 1), (45, 1), (54, 1), (63, 1)] }, { coefficient := -1, powers := [(15, 1), (18, 1), (20, 1), (22, 1), (38, 1), (42, 1), (45, 1), (54, 1), (59, 1), (63, 1)] }, { coefficient := -1, powers := [(15, 1), (18, 1), (20, 1), (25, 1), (33, 1), (39, 1), (42, 1), (45, 1), (54, 1), (63, 1)] }, { coefficient := -1, powers := [(15, 1), (18, 1), (20, 1), (25, 1), (36, 1), (39, 1), (42, 1), (45, 1), (54, 1), (63, 1)] }, { coefficient := -1, powers := [(15, 1), (18, 1), (20, 1), (33, 1), (39, 1), (45, 1), (54, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(15, 1), (22, 1), (25, 1), (26, 1), (42, 2), (61, 1), (63, 1)] }, { coefficient := 1, powers := [(15, 1), (22, 1), (25, 1), (26, 1), (42, 1), (46, 1), (61, 1), (63, 1)] }, { coefficient := 1, powers := [(15, 1), (22, 1), (25, 1), (26, 1), (42, 1), (52, 1), (61, 1), (63, 1)] }, { coefficient := 1, powers := [(15, 1), (22, 1), (26, 1), (42, 1), (46, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(15, 1), (17, 1), (22, 1), (34, 1), (38, 1), (42, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(15, 1), (22, 1), (34, 1), (38, 1), (42, 1), (48, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(15, 1), (22, 1), (34, 1), (38, 1), (42, 1), (48, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(15, 1), (22, 1), (25, 1), (42, 2), (45, 1), (61, 1), (63, 1)] }, { coefficient := 1, powers := [(15, 1), (22, 1), (25, 1), (42, 1), (45, 1), (46, 1), (61, 1), (63, 1)] }, { coefficient := 1, powers := [(15, 1), (22, 1), (25, 1), (42, 1), (45, 1), (52, 1), (61, 1), (63, 1)] }, { coefficient := 1, powers := [(15, 1), (22, 1), (42, 1), (45, 1), (46, 1), (63, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1), (46, 1), (61, 1), (63, 1)] }, { coefficient := -1, powers := [(16, 1), (36, 1), (39, 1), (61, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (20, 1), (33, 1), (46, 1), (54, 1)] }, { coefficient := -1, powers := [(7, 1), (20, 1), (36, 1), (42, 1), (54, 1)] }, { coefficient := -1, powers := [(15, 1), (20, 1), (22, 1), (38, 1), (42, 1), (54, 1), (59, 1)] }, { coefficient := -1, powers := [(15, 1), (20, 1), (25, 1), (33, 1), (39, 1), (42, 1), (54, 1)] }, { coefficient := -1, powers := [(15, 1), (20, 1), (25, 1), (36, 1), (39, 1), (42, 1), (54, 1)] }, { coefficient := -1, powers := [(15, 1), (20, 1), (33, 1), (39, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (33, 1), (46, 1), (54, 1)] }, { coefficient := 1, powers := [(7, 1), (36, 1), (42, 1), (54, 1)] }, { coefficient := 1, powers := [(15, 1), (22, 1), (38, 1), (42, 1), (54, 1), (59, 1)] }, { coefficient := 1, powers := [(15, 1), (25, 1), (33, 1), (39, 1), (42, 1), (54, 1)] }, { coefficient := 1, powers := [(15, 1), (25, 1), (36, 1), (39, 1), (42, 1), (54, 1)] }, { coefficient := 1, powers := [(15, 1), (33, 1), (39, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (22, 1), (49, 1), (59, 1)] }, { coefficient := 1, powers := [(4, 1), (36, 1), (49, 1), (52, 1)] }, { coefficient := 1, powers := [(7, 1), (33, 1), (46, 1), (49, 1)] }, { coefficient := 1, powers := [(7, 1), (36, 1), (42, 1), (49, 1)] }, { coefficient := -1, powers := [(15, 1), (22, 1), (38, 1), (42, 1), (45, 1), (48, 1), (59, 1)] }, { coefficient := 2, powers := [(15, 1), (22, 1), (38, 1), (42, 1), (49, 1), (59, 1)] }, { coefficient := 1, powers := [(15, 1), (25, 1), (33, 1), (39, 1), (42, 1), (49, 1)] }, { coefficient := 1, powers := [(15, 1), (25, 1), (36, 1), (39, 1), (42, 1), (49, 1)] }, { coefficient := 1, powers := [(15, 1), (33, 1), (39, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(15, 1), (22, 1), (34, 1), (38, 1), (42, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(15, 1), (22, 1), (34, 1), (38, 1), (42, 1), (45, 1), (48, 1)] }, { coefficient := -1, powers := [(15, 1), (22, 1), (34, 1), (38, 1), (42, 1), (49, 1)] }],
  [{ coefficient := 2, powers := [(3, 1), (15, 1), (22, 1), (24, 1), (38, 1), (42, 1), (59, 2)] }, { coefficient := 1, powers := [(7, 1), (22, 1), (24, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (24, 1), (33, 1), (46, 1)] }, { coefficient := 1, powers := [(7, 1), (24, 1), (36, 1), (42, 1)] }, { coefficient := -1, powers := [(7, 1), (24, 1), (36, 1), (52, 1)] }, { coefficient := 1, powers := [(15, 1), (22, 1), (24, 1), (38, 1), (42, 1), (59, 1)] }, { coefficient := 1, powers := [(15, 1), (24, 1), (25, 1), (33, 1), (39, 1), (42, 1)] }, { coefficient := 1, powers := [(15, 1), (24, 1), (25, 1), (36, 1), (39, 1), (42, 1)] }, { coefficient := 1, powers := [(15, 1), (24, 1), (33, 1), (39, 1)] }],
  [{ coefficient := -1, powers := [(15, 1), (22, 1), (26, 1), (34, 1), (38, 1), (42, 1), (45, 1), (48, 1)] }, { coefficient := 1, powers := [(15, 1), (22, 1), (26, 1), (34, 1), (38, 1), (42, 1), (49, 1)] }],
  [{ coefficient := -1, powers := [(15, 1), (22, 1), (25, 1), (42, 2), (61, 1), (63, 1)] }, { coefficient := -1, powers := [(15, 1), (22, 1), (25, 1), (42, 1), (46, 1), (61, 1), (63, 1)] }, { coefficient := -1, powers := [(15, 1), (22, 1), (25, 1), (42, 1), (52, 1), (61, 1), (63, 1)] }, { coefficient := -1, powers := [(15, 1), (22, 1), (42, 1), (46, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(15, 1), (17, 1), (22, 1), (34, 1), (38, 1), (42, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (22, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (22, 1), (46, 1), (61, 1), (63, 1)] }, { coefficient := 1, powers := [(0, 1), (36, 1), (39, 1), (61, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (13, 1), (22, 1), (59, 1)] }, { coefficient := 1, powers := [(4, 1), (13, 1), (36, 1), (52, 1)] }, { coefficient := 1, powers := [(7, 1), (13, 1), (33, 1), (46, 1)] }, { coefficient := 1, powers := [(7, 1), (13, 1), (36, 1), (42, 1)] }, { coefficient := 1, powers := [(13, 1), (15, 1), (22, 1), (38, 1), (42, 1), (59, 1)] }, { coefficient := 1, powers := [(13, 1), (15, 1), (25, 1), (33, 1), (39, 1), (42, 1)] }, { coefficient := 1, powers := [(13, 1), (15, 1), (25, 1), (36, 1), (39, 1), (42, 1)] }, { coefficient := 1, powers := [(13, 1), (15, 1), (33, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (18, 1), (20, 1), (33, 1), (46, 1), (54, 1), (63, 1)] }, { coefficient := 1, powers := [(7, 1), (18, 1), (20, 1), (36, 1), (42, 1), (54, 1), (63, 1)] }, { coefficient := 1, powers := [(15, 1), (18, 1), (20, 1), (22, 1), (38, 1), (42, 1), (54, 1), (59, 1), (63, 1)] }, { coefficient := 1, powers := [(15, 1), (18, 1), (20, 1), (25, 1), (33, 1), (39, 1), (42, 1), (54, 1), (63, 1)] }, { coefficient := 1, powers := [(15, 1), (18, 1), (20, 1), (25, 1), (36, 1), (39, 1), (42, 1), (54, 1), (63, 1)] }, { coefficient := 1, powers := [(15, 1), (18, 1), (20, 1), (33, 1), (39, 1), (54, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(15, 1), (19, 1), (22, 1), (42, 1), (61, 1)] }],
  [{ coefficient := -2, powers := [(15, 1), (18, 1), (22, 1), (24, 1), (38, 1), (42, 1), (54, 1), (59, 1)] }, { coefficient := -1, powers := [(15, 1), (22, 1), (25, 1), (26, 1), (42, 2), (45, 1), (61, 1), (63, 1)] }, { coefficient := -1, powers := [(15, 1), (22, 1), (25, 1), (26, 1), (42, 1), (45, 1), (46, 1), (61, 1), (63, 1)] }, { coefficient := -1, powers := [(15, 1), (22, 1), (25, 1), (26, 1), (42, 1), (45, 1), (52, 1), (61, 1), (63, 1)] }, { coefficient := 1, powers := [(15, 1), (22, 1), (25, 1), (42, 1), (61, 1)] }, { coefficient := -1, powers := [(15, 1), (22, 1), (26, 1), (42, 1), (45, 1), (46, 1), (63, 1)] }, { coefficient := -1, powers := [(16, 1), (22, 1), (26, 1), (46, 1), (61, 1), (63, 1)] }, { coefficient := 1, powers := [(16, 1), (26, 1), (36, 1), (39, 1), (61, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(22, 1)] }],
  [{ coefficient := -1, powers := [(15, 1), (25, 1), (42, 1)] }],
  [{ coefficient := -1, powers := [(15, 1), (22, 1), (42, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(4, 1), (22, 1), (59, 1)] }, { coefficient := -1, powers := [(4, 1), (36, 1), (52, 1)] }, { coefficient := -1, powers := [(7, 1), (33, 1), (46, 1)] }, { coefficient := -1, powers := [(7, 1), (36, 1), (42, 1)] }, { coefficient := -1, powers := [(15, 1), (22, 1), (38, 1), (42, 1), (59, 1)] }, { coefficient := -1, powers := [(15, 1), (25, 1), (33, 1), (39, 1), (42, 1)] }, { coefficient := -1, powers := [(15, 1), (25, 1), (36, 1), (39, 1), (42, 1)] }, { coefficient := -1, powers := [(15, 1), (33, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (22, 1), (46, 1), (57, 1), (63, 1)] }, { coefficient := -1, powers := [(11, 1), (36, 1), (39, 1), (57, 1), (63, 1)] }, { coefficient := -1, powers := [(15, 1), (19, 1), (22, 1), (42, 1), (46, 1)] }, { coefficient := -1, powers := [(15, 1), (22, 1), (25, 1), (42, 1), (52, 1)] }, { coefficient := 1, powers := [(15, 1), (22, 1), (38, 1), (42, 1), (59, 1)] }, { coefficient := 1, powers := [(15, 1), (22, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(39, 1), (59, 1)] }, { coefficient := 1, powers := [(46, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (22, 1), (40, 1), (59, 1), (60, 1)] }, { coefficient := 1, powers := [(4, 1), (36, 1), (40, 1), (52, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (20, 1), (33, 1), (46, 1), (47, 1), (54, 1)] }, { coefficient := 1, powers := [(7, 1), (20, 1), (36, 1), (42, 1), (47, 1), (54, 1)] }, { coefficient := 1, powers := [(7, 1), (33, 1), (40, 1), (46, 1), (60, 1)] }, { coefficient := -1, powers := [(7, 1), (33, 1), (46, 1), (49, 1), (54, 1)] }, { coefficient := 1, powers := [(7, 1), (36, 1), (40, 1), (42, 1), (60, 1)] }, { coefficient := -1, powers := [(7, 1), (36, 1), (42, 1), (49, 1), (54, 1)] }, { coefficient := 1, powers := [(15, 1), (20, 1), (22, 1), (38, 1), (42, 1), (47, 1), (54, 1), (59, 1)] }, { coefficient := 1, powers := [(15, 1), (20, 1), (25, 1), (33, 1), (39, 1), (42, 1), (47, 1), (54, 1)] }, { coefficient := 1, powers := [(15, 1), (20, 1), (25, 1), (36, 1), (39, 1), (42, 1), (47, 1), (54, 1)] }, { coefficient := 1, powers := [(15, 1), (20, 1), (33, 1), (39, 1), (47, 1), (54, 1)] }, { coefficient := 1, powers := [(15, 1), (22, 1), (38, 1), (40, 1), (42, 1), (59, 1), (60, 1)] }, { coefficient := 1, powers := [(15, 1), (22, 1), (38, 1), (42, 1), (45, 1), (48, 1), (54, 1), (59, 1)] }, { coefficient := -2, powers := [(15, 1), (22, 1), (38, 1), (42, 1), (49, 1), (54, 1), (59, 1)] }, { coefficient := 1, powers := [(15, 1), (25, 1), (33, 1), (39, 1), (40, 1), (42, 1), (60, 1)] }, { coefficient := -1, powers := [(15, 1), (25, 1), (33, 1), (39, 1), (42, 1), (49, 1), (54, 1)] }, { coefficient := 1, powers := [(15, 1), (25, 1), (36, 1), (39, 1), (40, 1), (42, 1), (60, 1)] }, { coefficient := -1, powers := [(15, 1), (25, 1), (36, 1), (39, 1), (42, 1), (49, 1), (54, 1)] }, { coefficient := 1, powers := [(15, 1), (33, 1), (39, 1), (40, 1), (60, 1)] }, { coefficient := -1, powers := [(15, 1), (33, 1), (39, 1), (49, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (4, 1), (22, 1), (57, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (4, 1), (36, 1), (52, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (7, 1), (33, 1), (46, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (7, 1), (36, 1), (42, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (15, 1), (22, 1), (38, 1), (42, 1), (57, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (15, 1), (25, 1), (33, 1), (39, 1), (42, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (15, 1), (25, 1), (36, 1), (39, 1), (42, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (15, 1), (33, 1), (39, 1), (57, 1)] }, { coefficient := -1, powers := [(4, 1), (8, 1), (22, 1), (37, 1), (59, 1)] }, { coefficient := 1, powers := [(4, 1), (8, 1), (36, 1), (37, 1), (52, 1)] }, { coefficient := 1, powers := [(7, 1), (8, 1), (33, 1), (37, 1), (46, 1)] }, { coefficient := 1, powers := [(7, 1), (8, 1), (36, 1), (37, 1), (42, 1)] }, { coefficient := 1, powers := [(7, 1), (18, 1), (22, 1), (31, 1), (59, 1)] }, { coefficient := 2, powers := [(7, 1), (18, 1), (31, 1), (33, 1), (46, 1)] }, { coefficient := 2, powers := [(7, 1), (18, 1), (31, 1), (36, 1), (42, 1)] }, { coefficient := -1, powers := [(7, 1), (18, 1), (31, 1), (36, 1), (52, 1)] }, { coefficient := 1, powers := [(8, 1), (15, 1), (22, 1), (37, 1), (38, 1), (42, 1), (59, 1)] }, { coefficient := 1, powers := [(8, 1), (15, 1), (25, 1), (33, 1), (37, 1), (39, 1), (42, 1)] }, { coefficient := 1, powers := [(8, 1), (15, 1), (25, 1), (36, 1), (37, 1), (39, 1), (42, 1)] }, { coefficient := 1, powers := [(8, 1), (15, 1), (33, 1), (37, 1), (39, 1)] }, { coefficient := 2, powers := [(15, 1), (18, 1), (25, 1), (31, 1), (33, 1), (39, 1), (42, 1)] }, { coefficient := 2, powers := [(15, 1), (18, 1), (25, 1), (31, 1), (36, 1), (39, 1), (42, 1)] }, { coefficient := 2, powers := [(15, 1), (18, 1), (31, 1), (33, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (42, 1)] }, { coefficient := 1, powers := [(4, 1), (33, 1)] }, { coefficient := 1, powers := [(15, 1), (17, 1), (19, 1), (22, 1), (34, 1), (38, 1), (42, 1), (48, 1), (57, 1)] }, { coefficient := -1, powers := [(15, 1), (17, 1), (20, 1), (22, 1), (34, 1), (38, 1), (42, 1), (57, 1)] }, { coefficient := 1, powers := [(15, 1), (17, 1), (22, 1), (26, 1), (34, 1), (38, 1), (42, 1), (45, 1), (48, 1)] }, { coefficient := -1, powers := [(15, 1), (17, 1), (22, 1), (26, 1), (34, 1), (38, 1), (42, 1), (49, 1)] }, { coefficient := 2, powers := [(15, 1), (18, 1), (19, 1), (22, 1), (24, 1), (38, 1), (42, 1), (54, 1), (59, 1)] }, { coefficient := 1, powers := [(15, 1), (19, 1), (22, 1), (25, 1), (26, 1), (42, 2), (45, 1), (61, 1), (63, 1)] }, { coefficient := 1, powers := [(15, 1), (19, 1), (22, 1), (25, 1), (26, 1), (42, 1), (45, 1), (46, 1), (61, 1), (63, 1)] }, { coefficient := 1, powers := [(15, 1), (19, 1), (22, 1), (25, 1), (26, 1), (42, 1), (45, 1), (52, 1), (61, 1), (63, 1)] }, { coefficient := -1, powers := [(15, 1), (19, 1), (22, 1), (25, 1), (42, 1), (61, 1)] }, { coefficient := 1, powers := [(15, 1), (19, 1), (22, 1), (26, 1), (42, 1), (45, 1), (46, 1), (63, 1)] }, { coefficient := 1, powers := [(15, 1), (22, 1), (25, 1), (42, 1)] }, { coefficient := 1, powers := [(16, 1), (19, 1), (22, 1), (26, 1), (46, 1), (61, 1), (63, 1)] }, { coefficient := -1, powers := [(16, 1), (19, 1), (26, 1), (36, 1), (39, 1), (61, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (18, 1), (20, 1), (30, 1), (33, 1), (46, 1), (54, 1)] }, { coefficient := -1, powers := [(7, 1), (18, 1), (20, 1), (30, 1), (36, 1), (42, 1), (54, 1)] }, { coefficient := 1, powers := [(11, 1), (22, 1), (46, 1)] }, { coefficient := -1, powers := [(11, 1), (36, 1), (39, 1)] }, { coefficient := -1, powers := [(15, 1), (18, 1), (20, 1), (22, 1), (30, 1), (38, 1), (42, 1), (54, 1), (59, 1)] }, { coefficient := -1, powers := [(15, 1), (18, 1), (20, 1), (25, 1), (30, 1), (33, 1), (39, 1), (42, 1), (54, 1)] }, { coefficient := -1, powers := [(15, 1), (18, 1), (20, 1), (25, 1), (30, 1), (36, 1), (39, 1), (42, 1), (54, 1)] }, { coefficient := -1, powers := [(15, 1), (18, 1), (20, 1), (30, 1), (33, 1), (39, 1), (54, 1)] }, { coefficient := 1, powers := [(15, 1), (19, 1), (22, 1), (25, 1), (42, 2), (61, 1)] }, { coefficient := 1, powers := [(15, 1), (19, 1), (22, 1), (25, 1), (42, 1), (46, 1), (61, 1)] }, { coefficient := 1, powers := [(15, 1), (19, 1), (22, 1), (25, 1), (42, 1), (52, 1), (61, 1)] }, { coefficient := 1, powers := [(15, 1), (19, 1), (22, 1), (42, 1), (46, 1)] }],
  [{ coefficient := 2, powers := [(3, 1), (13, 1), (15, 1), (22, 1), (24, 1), (38, 1), (42, 1), (57, 1), (59, 2)] }, { coefficient := 1, powers := [(7, 1), (13, 1), (22, 1), (24, 1), (57, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (13, 1), (24, 1), (33, 1), (46, 1), (57, 1)] }, { coefficient := 1, powers := [(7, 1), (13, 1), (24, 1), (36, 1), (42, 1), (57, 1)] }, { coefficient := -1, powers := [(7, 1), (13, 1), (24, 1), (36, 1), (52, 1), (57, 1)] }, { coefficient := 1, powers := [(13, 1), (15, 1), (22, 1), (24, 1), (38, 1), (42, 1), (57, 1), (59, 1)] }, { coefficient := 1, powers := [(13, 1), (15, 1), (24, 1), (25, 1), (33, 1), (39, 1), (42, 1), (57, 1)] }, { coefficient := 1, powers := [(13, 1), (15, 1), (24, 1), (25, 1), (36, 1), (39, 1), (42, 1), (57, 1)] }, { coefficient := 1, powers := [(13, 1), (15, 1), (24, 1), (33, 1), (39, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (59, 1)] }, { coefficient := 1, powers := [(11, 1), (46, 1)] }, { coefficient := 1, powers := [(15, 1), (25, 1), (42, 2)] }, { coefficient := 1, powers := [(15, 1), (25, 1), (42, 1), (46, 1)] }, { coefficient := 1, powers := [(15, 1), (42, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (13, 1), (22, 1), (45, 1), (48, 1), (59, 1)] }, { coefficient := 1, powers := [(4, 1), (13, 1), (22, 1), (49, 1), (59, 1)] }, { coefficient := 1, powers := [(4, 1), (13, 1), (36, 1), (45, 1), (48, 1), (52, 1)] }, { coefficient := -1, powers := [(4, 1), (13, 1), (36, 1), (49, 1), (52, 1)] }, { coefficient := 1, powers := [(5, 1), (7, 1), (33, 1), (46, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (7, 1), (36, 1), (42, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (15, 1), (22, 1), (38, 1), (42, 1), (59, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (15, 1), (25, 1), (33, 1), (39, 1), (42, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (15, 1), (25, 1), (36, 1), (39, 1), (42, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (15, 1), (33, 1), (39, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (13, 1), (33, 1), (45, 1), (46, 1), (48, 1)] }, { coefficient := -1, powers := [(7, 1), (13, 1), (33, 1), (46, 1), (49, 1)] }, { coefficient := 1, powers := [(7, 1), (13, 1), (36, 1), (42, 1), (45, 1), (48, 1)] }, { coefficient := -1, powers := [(7, 1), (13, 1), (36, 1), (42, 1), (49, 1)] }, { coefficient := 1, powers := [(7, 1), (18, 1), (20, 1), (33, 1), (45, 1), (46, 2), (54, 1), (63, 1)] }, { coefficient := -1, powers := [(7, 1), (18, 1), (20, 1), (33, 1), (46, 1), (47, 1), (54, 1), (63, 1)] }, { coefficient := 1, powers := [(7, 1), (18, 1), (20, 1), (36, 1), (42, 1), (45, 1), (46, 1), (54, 1), (63, 1)] }, { coefficient := -1, powers := [(7, 1), (18, 1), (20, 1), (36, 1), (42, 1), (47, 1), (54, 1), (63, 1)] }, { coefficient := 2, powers := [(13, 1), (15, 1), (22, 1), (38, 1), (42, 1), (45, 1), (48, 1), (59, 1)] }, { coefficient := -2, powers := [(13, 1), (15, 1), (22, 1), (38, 1), (42, 1), (49, 1), (59, 1)] }, { coefficient := 1, powers := [(13, 1), (15, 1), (25, 1), (33, 1), (39, 1), (42, 1), (45, 1), (48, 1)] }, { coefficient := -1, powers := [(13, 1), (15, 1), (25, 1), (33, 1), (39, 1), (42, 1), (49, 1)] }, { coefficient := 1, powers := [(13, 1), (15, 1), (25, 1), (36, 1), (39, 1), (42, 1), (45, 1), (48, 1)] }, { coefficient := -1, powers := [(13, 1), (15, 1), (25, 1), (36, 1), (39, 1), (42, 1), (49, 1)] }, { coefficient := 1, powers := [(13, 1), (15, 1), (33, 1), (39, 1), (45, 1), (48, 1)] }, { coefficient := -1, powers := [(13, 1), (15, 1), (33, 1), (39, 1), (49, 1)] }, { coefficient := 1, powers := [(15, 1), (18, 1), (20, 1), (22, 1), (38, 1), (42, 1), (45, 1), (46, 1), (54, 1), (59, 1), (63, 1)] }, { coefficient := -1, powers := [(15, 1), (18, 1), (20, 1), (22, 1), (38, 1), (42, 1), (47, 1), (54, 1), (59, 1), (63, 1)] }, { coefficient := 1, powers := [(15, 1), (18, 1), (20, 1), (25, 1), (33, 1), (39, 1), (42, 1), (45, 1), (46, 1), (54, 1), (63, 1)] }, { coefficient := -1, powers := [(15, 1), (18, 1), (20, 1), (25, 1), (33, 1), (39, 1), (42, 1), (47, 1), (54, 1), (63, 1)] }, { coefficient := 1, powers := [(15, 1), (18, 1), (20, 1), (25, 1), (36, 1), (39, 1), (42, 1), (45, 1), (46, 1), (54, 1), (63, 1)] }, { coefficient := -1, powers := [(15, 1), (18, 1), (20, 1), (25, 1), (36, 1), (39, 1), (42, 1), (47, 1), (54, 1), (63, 1)] }, { coefficient := 1, powers := [(15, 1), (18, 1), (20, 1), (33, 1), (39, 1), (45, 1), (46, 1), (54, 1), (63, 1)] }, { coefficient := -1, powers := [(15, 1), (18, 1), (20, 1), (33, 1), (39, 1), (47, 1), (54, 1), (63, 1)] }]
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
    (values : Fin 65 → R) :
    ¬ ∀ index : Fin 54,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component18.SelectedLeafB4_2_1_4.selectedHasNoCommonZero

end Krenn.Component18.SelectedLeafB4_2_1_4
