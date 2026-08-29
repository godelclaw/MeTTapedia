import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component18.SelectedLeafB6_6_1_4

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "3b48b4b21a1a7f49e890ce9b28a7bad637b238e10ab8d429ed1054ba1616b596"
def certificateSHA256 : String := "bca7a83d817ed2e14b86b08fe7a72b655c98544f8fef0bc92b2a29e314888af4"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 54 → Fin 670 := ![
  2,
  7,
  10,
  15,
  19,
  23,
  24,
  143,
  148,
  149,
  152,
  168,
  225,
  277,
  294,
  308,
  318,
  323,
  375,
  414,
  426,
  437,
  443,
  451,
  458,
  462,
  496,
  497,
  506,
  539,
  551,
  562,
  565,
  572,
  574,
  581,
  586,
  596,
  607,
  625,
  646,
  647,
  656,
  657,
  658,
  659,
  660,
  661,
  663,
  665,
  666,
  667,
  668,
  669
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 54 → SparsePoly (Fin 67) := ![
  [{ coefficient := 1, powers := [(7, 1), (34, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(15, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(30, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(34, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (54, 1)] }, { coefficient := 1, powers := [(15, 1), (21, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (25, 1)] }, { coefficient := 1, powers := [(15, 1), (19, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (26, 1)] }, { coefficient := 1, powers := [(15, 1), (19, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (45, 1)] }, { coefficient := 1, powers := [(16, 1), (19, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (53, 1)] }, { coefficient := 1, powers := [(31, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (25, 1), (45, 1)] }, { coefficient := 1, powers := [(16, 1), (19, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (45, 1), (52, 1)] }, { coefficient := 1, powers := [(28, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1)] }, { coefficient := 1, powers := [(19, 1), (45, 1)] }, { coefficient := 1, powers := [(25, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (47, 1)] }, { coefficient := 1, powers := [(16, 1), (42, 1)] }, { coefficient := 1, powers := [(16, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (54, 1)] }, { coefficient := 1, powers := [(31, 1), (43, 1)] }, { coefficient := 1, powers := [(34, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1), (52, 1)] }, { coefficient := 1, powers := [(19, 1), (45, 1), (52, 1)] }, { coefficient := 1, powers := [(45, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (28, 1), (45, 1)] }, { coefficient := 1, powers := [(21, 1), (45, 1), (51, 1)] }, { coefficient := 1, powers := [(28, 1), (41, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (26, 1), (46, 1), (51, 1)] }, { coefficient := 1, powers := [(9, 1), (26, 1), (46, 1)] }, { coefficient := 1, powers := [(26, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (53, 1)] }, { coefficient := 1, powers := [(3, 1), (26, 1), (59, 1)] }, { coefficient := 1, powers := [(19, 1), (53, 1)] }, { coefficient := 1, powers := [(26, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1)] }, { coefficient := 1, powers := [(13, 1), (31, 1)] }, { coefficient := 1, powers := [(17, 1), (23, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (60, 1)] }, { coefficient := 1, powers := [(13, 1), (26, 1), (47, 1)] }, { coefficient := 1, powers := [(13, 1), (57, 1)] }, { coefficient := 1, powers := [(18, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (26, 1), (51, 1)] }, { coefficient := 1, powers := [(9, 1), (26, 1)] }, { coefficient := 1, powers := [(19, 1), (26, 1), (51, 1)] }, { coefficient := 1, powers := [(26, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1), (53, 1)] }, { coefficient := 1, powers := [(19, 1), (45, 1), (53, 1)] }, { coefficient := 1, powers := [(19, 1), (57, 1)] }, { coefficient := 1, powers := [(26, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1), (51, 1)] }, { coefficient := 1, powers := [(9, 1), (47, 1)] }, { coefficient := 1, powers := [(32, 1), (39, 1), (45, 1)] }, { coefficient := 1, powers := [(45, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (31, 1), (60, 1)] }, { coefficient := 1, powers := [(3, 1), (34, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (37, 1), (54, 1)] }, { coefficient := 1, powers := [(23, 1), (45, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (33, 1), (57, 1)] }, { coefficient := 1, powers := [(21, 1), (45, 1), (53, 1)] }, { coefficient := 1, powers := [(21, 1), (57, 1)] }, { coefficient := 1, powers := [(27, 1), (45, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (31, 1), (60, 1)] }, { coefficient := 1, powers := [(4, 1), (34, 1), (57, 1)] }, { coefficient := 1, powers := [(4, 1), (37, 1), (54, 1)] }, { coefficient := 1, powers := [(16, 1), (30, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (21, 1), (57, 1)] }, { coefficient := 1, powers := [(9, 1), (27, 1), (45, 1), (53, 1)] }, { coefficient := 1, powers := [(21, 1), (26, 1), (45, 1), (51, 1)] }, { coefficient := 1, powers := [(27, 1), (41, 1), (45, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (26, 1), (47, 1)] }, { coefficient := 1, powers := [(11, 1), (57, 1)] }, { coefficient := 1, powers := [(16, 1), (26, 1), (42, 1)] }, { coefficient := 1, powers := [(16, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (45, 1), (53, 1)] }, { coefficient := 1, powers := [(24, 1), (57, 1)] }, { coefficient := 1, powers := [(31, 1), (49, 1)] }, { coefficient := 1, powers := [(37, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (26, 1), (47, 1), (51, 1)] }, { coefficient := 1, powers := [(9, 1), (26, 1), (47, 1)] }, { coefficient := 1, powers := [(9, 1), (57, 1)] }, { coefficient := 1, powers := [(26, 1), (45, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (26, 1), (36, 1), (51, 1)] }, { coefficient := 1, powers := [(9, 1), (27, 1), (53, 1)] }, { coefficient := 1, powers := [(21, 1), (26, 1), (51, 1)] }, { coefficient := 1, powers := [(27, 1), (41, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (27, 1), (53, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (36, 1), (53, 1)] }, { coefficient := 1, powers := [(21, 1), (53, 1)] }, { coefficient := 1, powers := [(27, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (52, 1)] }, { coefficient := 1, powers := [(3, 1), (59, 1)] }, { coefficient := 1, powers := [(19, 1), (52, 1)] }, { coefficient := 1, powers := [(19, 1), (56, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1), (51, 1)] }, { coefficient := 1, powers := [(9, 1), (46, 1)] }, { coefficient := 1, powers := [(9, 1), (56, 1)] }, { coefficient := 1, powers := [(32, 1), (39, 1)] }, { coefficient := 1, powers := [(51, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (36, 1), (51, 1)] }, { coefficient := 1, powers := [(9, 1), (21, 1), (56, 1)] }, { coefficient := 1, powers := [(9, 1), (28, 1)] }, { coefficient := 1, powers := [(21, 1), (51, 1)] }, { coefficient := 1, powers := [(28, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (52, 1)] }, { coefficient := 1, powers := [(22, 1), (56, 1)] }, { coefficient := 1, powers := [(28, 1), (42, 1)] }, { coefficient := 1, powers := [(28, 1), (46, 1)] }, { coefficient := 1, powers := [(33, 1), (39, 1)] }, { coefficient := 1, powers := [(36, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (28, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (33, 1), (56, 1)] }, { coefficient := 1, powers := [(3, 1), (36, 1), (52, 1)] }, { coefficient := 1, powers := [(21, 1), (52, 1)] }, { coefficient := 1, powers := [(21, 1), (56, 1)] }, { coefficient := 1, powers := [(28, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (41, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (51, 1)] }, { coefficient := 1, powers := [(3, 1), (32, 1), (56, 1)] }, { coefficient := 1, powers := [(9, 1), (19, 1), (56, 1)] }, { coefficient := 1, powers := [(9, 1)] }, { coefficient := 1, powers := [(19, 1), (51, 1)] }, { coefficient := 1, powers := [(41, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (41, 1), (56, 1)] }, { coefficient := 1, powers := [(1, 1), (51, 1)] }, { coefficient := 1, powers := [(7, 1), (36, 1), (41, 1)] }, { coefficient := 1, powers := [(10, 1), (21, 1), (56, 1)] }, { coefficient := 1, powers := [(10, 1), (28, 1)] }, { coefficient := 1, powers := [(15, 1), (21, 1), (51, 1)] }, { coefficient := 1, powers := [(15, 1), (28, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (39, 1), (59, 1)] }, { coefficient := 1, powers := [(1, 1), (42, 1), (56, 1)] }, { coefficient := 1, powers := [(1, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(4, 1), (28, 1), (59, 1)] }, { coefficient := 1, powers := [(4, 1), (33, 1), (56, 1)] }, { coefficient := 1, powers := [(4, 1), (36, 1), (52, 1)] }, { coefficient := 1, powers := [(7, 1), (22, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (33, 1), (46, 1)] }, { coefficient := 1, powers := [(7, 1), (36, 1), (42, 1)] }, { coefficient := 1, powers := [(11, 1), (22, 1), (56, 1)] }, { coefficient := 1, powers := [(11, 1), (28, 1), (46, 1)] }, { coefficient := 1, powers := [(11, 1), (36, 1), (39, 1)] }, { coefficient := 1, powers := [(15, 1), (22, 1), (52, 1)] }, { coefficient := 1, powers := [(15, 1), (28, 1), (42, 1)] }, { coefficient := 1, powers := [(15, 1), (33, 1), (39, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (40, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (43, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (49, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (37, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (49, 1)] }, { coefficient := 1, powers := [(8, 1), (37, 1), (43, 1)] }, { coefficient := 1, powers := [(13, 1), (24, 1), (57, 1)] }, { coefficient := 1, powers := [(13, 1), (31, 1), (49, 1)] }, { coefficient := 1, powers := [(13, 1), (37, 1), (40, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (54, 1)] }, { coefficient := 1, powers := [(18, 1), (31, 1), (43, 1)] }, { coefficient := 1, powers := [(18, 1), (34, 1), (40, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (61, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(41, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(43, 1)] }],
  [{ coefficient := 1, powers := [(56, 1)] }],
  [{ coefficient := 1, powers := [(57, 1), (65, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(25, 1), (66, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(28, 1)] }],
  [{ coefficient := 1, powers := [(31, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 54 → SparsePoly (Fin 67) := ![
  [{ coefficient := 1, powers := [(0, 1), (5, 1), (36, 1), (46, 1), (52, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (18, 1), (36, 1), (40, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(5, 1), (22, 1), (57, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (46, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1), (42, 1), (57, 1)] }, { coefficient := 1, powers := [(18, 1), (22, 1), (40, 1), (59, 1)] }, { coefficient := 1, powers := [(18, 1), (33, 1), (40, 1), (46, 1)] }, { coefficient := 1, powers := [(18, 1), (36, 1), (40, 1), (42, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (7, 1), (24, 1), (36, 1), (46, 1), (52, 1), (57, 1), (66, 1)] }, { coefficient := -1, powers := [(1, 1), (24, 1), (39, 1), (57, 1), (59, 1), (66, 1)] }, { coefficient := -1, powers := [(3, 1), (15, 1), (24, 1), (33, 1), (46, 1), (52, 1), (57, 1), (66, 1)] }, { coefficient := -1, powers := [(4, 1), (24, 1), (36, 1), (52, 1), (57, 1), (66, 1)] }, { coefficient := -1, powers := [(7, 1), (22, 1), (24, 1), (57, 1), (59, 1), (66, 1)] }, { coefficient := -1, powers := [(7, 1), (24, 1), (33, 1), (46, 1), (57, 1), (66, 1)] }, { coefficient := -1, powers := [(7, 1), (24, 1), (36, 1), (42, 1), (57, 1), (66, 1)] }, { coefficient := 1, powers := [(15, 1), (24, 1), (36, 1), (39, 1), (57, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (7, 1), (24, 1), (26, 1), (36, 1), (46, 1), (52, 1)] }, { coefficient := -1, powers := [(1, 1), (24, 1), (26, 1), (39, 1), (59, 1)] }, { coefficient := -1, powers := [(3, 1), (15, 1), (24, 1), (26, 1), (33, 1), (46, 1), (52, 1)] }, { coefficient := -1, powers := [(4, 1), (24, 1), (26, 1), (36, 1), (52, 1)] }, { coefficient := -1, powers := [(7, 1), (22, 1), (24, 1), (26, 1), (59, 1)] }, { coefficient := -1, powers := [(7, 1), (24, 1), (26, 1), (33, 1), (46, 1)] }, { coefficient := -1, powers := [(7, 1), (24, 1), (26, 1), (36, 1), (42, 1)] }, { coefficient := 1, powers := [(15, 1), (24, 1), (26, 1), (36, 1), (39, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (5, 1), (7, 1), (21, 1), (36, 1), (37, 1), (46, 1), (52, 1), (62, 1)] }, { coefficient := -1, powers := [(1, 1), (5, 1), (21, 1), (37, 1), (39, 1), (59, 1), (62, 1)] }, { coefficient := 1, powers := [(3, 1), (15, 1), (18, 1), (21, 1), (24, 1), (33, 1), (46, 1), (52, 1), (62, 1)] }, { coefficient := 1, powers := [(4, 1), (18, 1), (21, 1), (24, 1), (36, 1), (52, 1), (62, 1)] }, { coefficient := -1, powers := [(5, 1), (7, 1), (21, 1), (22, 1), (37, 1), (59, 1), (62, 1)] }, { coefficient := -1, powers := [(5, 1), (7, 1), (21, 1), (33, 1), (37, 1), (46, 1), (62, 1)] }, { coefficient := -1, powers := [(5, 1), (7, 1), (21, 1), (36, 1), (37, 1), (42, 1), (62, 1)] }, { coefficient := 1, powers := [(5, 1), (15, 1), (21, 1), (36, 1), (37, 1), (39, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (7, 1), (17, 1), (36, 1), (46, 1), (49, 1), (52, 1)] }, { coefficient := -1, powers := [(1, 1), (17, 1), (39, 1), (49, 1), (59, 1)] }, { coefficient := -1, powers := [(3, 1), (15, 1), (17, 1), (33, 1), (46, 1), (49, 1), (52, 1)] }, { coefficient := -1, powers := [(4, 1), (17, 1), (36, 1), (49, 1), (52, 1)] }, { coefficient := -1, powers := [(5, 1), (15, 1), (33, 1), (45, 1), (46, 1), (52, 1)] }, { coefficient := -1, powers := [(7, 1), (17, 1), (22, 1), (49, 1), (59, 1)] }, { coefficient := -1, powers := [(7, 1), (17, 1), (33, 1), (46, 1), (49, 1)] }, { coefficient := -1, powers := [(7, 1), (17, 1), (36, 1), (42, 1), (49, 1)] }, { coefficient := 1, powers := [(15, 1), (17, 1), (36, 1), (39, 1), (49, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (16, 1), (36, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (5, 1), (57, 1), (59, 1)] }, { coefficient := 1, powers := [(1, 1), (18, 1), (40, 1), (59, 1)] }, { coefficient := -1, powers := [(5, 1), (15, 1), (36, 1), (57, 1)] }, { coefficient := -1, powers := [(15, 1), (18, 1), (36, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (5, 1), (7, 1), (36, 1), (37, 1), (46, 1), (52, 1), (62, 1)] }, { coefficient := 1, powers := [(1, 1), (5, 1), (37, 1), (39, 1), (59, 1), (62, 1)] }, { coefficient := -1, powers := [(3, 1), (15, 1), (18, 1), (24, 1), (33, 1), (46, 1), (52, 1), (62, 1)] }, { coefficient := -1, powers := [(4, 1), (18, 1), (24, 1), (36, 1), (52, 1), (62, 1)] }, { coefficient := 1, powers := [(5, 1), (7, 1), (22, 1), (37, 1), (59, 1), (62, 1)] }, { coefficient := 1, powers := [(5, 1), (7, 1), (33, 1), (37, 1), (46, 1), (62, 1)] }, { coefficient := 1, powers := [(5, 1), (7, 1), (36, 1), (37, 1), (42, 1), (62, 1)] }, { coefficient := -1, powers := [(5, 1), (15, 1), (36, 1), (37, 1), (39, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(36, 1), (39, 1), (45, 1), (53, 1), (61, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(36, 1), (39, 1), (45, 1), (61, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(26, 1), (36, 1), (39, 1), (61, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (7, 1), (13, 1), (36, 1), (45, 1), (46, 1), (52, 1)] }, { coefficient := -1, powers := [(1, 1), (13, 1), (39, 1), (45, 1), (59, 1)] }, { coefficient := -1, powers := [(3, 1), (13, 1), (15, 1), (33, 1), (45, 1), (46, 1), (52, 1)] }, { coefficient := -1, powers := [(4, 1), (13, 1), (36, 1), (45, 1), (52, 1)] }, { coefficient := -1, powers := [(7, 1), (13, 1), (22, 1), (45, 1), (59, 1)] }, { coefficient := -1, powers := [(7, 1), (13, 1), (33, 1), (45, 1), (46, 1)] }, { coefficient := -1, powers := [(7, 1), (13, 1), (36, 1), (42, 1), (45, 1)] }, { coefficient := 1, powers := [(13, 1), (15, 1), (36, 1), (39, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(36, 1), (39, 1), (53, 1), (61, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(15, 1), (25, 1), (46, 1), (52, 1), (53, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (15, 1), (36, 1), (46, 1), (52, 2), (53, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (26, 1), (36, 1), (39, 1), (61, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (15, 1), (18, 1), (33, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(4, 1), (18, 1), (36, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (15, 1), (36, 1), (46, 1), (52, 1), (53, 1), (65, 1)] }, { coefficient := -1, powers := [(7, 1), (26, 1), (36, 1), (46, 1), (52, 1), (65, 1)] }, { coefficient := 1, powers := [(15, 1), (27, 1), (46, 1), (52, 1), (53, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(15, 1), (26, 1), (46, 1), (52, 1), (63, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (45, 1), (46, 1), (52, 1), (63, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (36, 1), (45, 1), (46, 1), (52, 1), (65, 1)] }, { coefficient := -1, powers := [(16, 1), (36, 1), (39, 1), (61, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (7, 1), (36, 1), (46, 1), (49, 1), (52, 1)] }, { coefficient := 1, powers := [(1, 1), (39, 1), (49, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (15, 1), (33, 1), (46, 1), (49, 1), (52, 1)] }, { coefficient := 1, powers := [(4, 1), (36, 1), (49, 1), (52, 1)] }, { coefficient := 1, powers := [(7, 1), (22, 1), (49, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (33, 1), (46, 1), (49, 1)] }, { coefficient := 1, powers := [(7, 1), (36, 1), (42, 1), (49, 1)] }, { coefficient := -1, powers := [(15, 1), (36, 1), (39, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (7, 1), (24, 1), (36, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(1, 1), (24, 1), (39, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (15, 1), (24, 1), (33, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(4, 1), (24, 1), (36, 1), (52, 1)] }, { coefficient := 1, powers := [(7, 1), (22, 1), (24, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (24, 1), (33, 1), (46, 1)] }, { coefficient := 1, powers := [(7, 1), (24, 1), (36, 1), (42, 1)] }, { coefficient := -1, powers := [(15, 1), (24, 1), (36, 1), (39, 1)] }],
  [{ coefficient := -1, powers := [(1, 1), (45, 1), (46, 2), (52, 1), (63, 1), (65, 1)] }, { coefficient := 1, powers := [(1, 1), (46, 1), (47, 1), (52, 1), (63, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (36, 1), (46, 1), (52, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (26, 1), (46, 1), (52, 1), (63, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (15, 1), (33, 1), (46, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(15, 1), (46, 1), (52, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (36, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(15, 1), (46, 1), (52, 1), (63, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (36, 1), (39, 1), (61, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (7, 1), (13, 1), (36, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(1, 1), (13, 1), (39, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (13, 1), (15, 1), (33, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(4, 1), (13, 1), (36, 1), (52, 1)] }, { coefficient := 1, powers := [(7, 1), (13, 1), (22, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (13, 1), (33, 1), (46, 1)] }, { coefficient := 1, powers := [(7, 1), (13, 1), (36, 1), (42, 1)] }, { coefficient := -1, powers := [(13, 1), (15, 1), (36, 1), (39, 1)] }],
  [{ coefficient := -1, powers := [(1, 1), (46, 1), (52, 1), (63, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(15, 1), (45, 1), (46, 1), (52, 1), (63, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(15, 1), (45, 1), (46, 1), (52, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (26, 1), (36, 1), (45, 1), (46, 1), (52, 1), (65, 1)] }, { coefficient := -1, powers := [(15, 1), (27, 1), (45, 1), (46, 1), (52, 1), (53, 1), (65, 1)] }, { coefficient := 1, powers := [(16, 1), (26, 1), (36, 1), (39, 1), (61, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(1, 1), (26, 1), (45, 1), (46, 1), (52, 1), (63, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(15, 1), (26, 1), (45, 1), (46, 1), (52, 1), (63, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(15, 1)] }],
  [{ coefficient := -1, powers := [(15, 1), (25, 1), (45, 1), (46, 1), (52, 1), (53, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (26, 1), (45, 1), (46, 2), (52, 1), (63, 1), (65, 1)] }, { coefficient := -1, powers := [(1, 1), (26, 1), (46, 1), (47, 1), (52, 1), (63, 1), (65, 1)] }, { coefficient := 1, powers := [(1, 1), (46, 1), (52, 1), (63, 1)] }, { coefficient := 1, powers := [(15, 1), (21, 1), (46, 1), (52, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (46, 1), (52, 1), (63, 1)] }, { coefficient := -1, powers := [(19, 1), (46, 1), (52, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(0, 1), (7, 1), (36, 1), (46, 1), (52, 1)] }, { coefficient := -1, powers := [(1, 1), (39, 1), (59, 1)] }, { coefficient := -1, powers := [(3, 1), (15, 1), (33, 1), (46, 1), (52, 1)] }, { coefficient := -1, powers := [(4, 1), (36, 1), (52, 1)] }, { coefficient := -1, powers := [(7, 1), (22, 1), (59, 1)] }, { coefficient := -1, powers := [(7, 1), (33, 1), (46, 1)] }, { coefficient := -1, powers := [(7, 1), (36, 1), (42, 1)] }, { coefficient := 1, powers := [(15, 1), (36, 1), (39, 1)] }],
  [{ coefficient := -1, powers := [(11, 1), (36, 1), (39, 1), (57, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (5, 1), (7, 1), (36, 1), (37, 1), (46, 1), (52, 1), (54, 1)] }, { coefficient := -1, powers := [(1, 1), (5, 1), (37, 1), (39, 1), (54, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (15, 1), (18, 1), (24, 1), (33, 1), (46, 1), (52, 1), (54, 1)] }, { coefficient := 1, powers := [(4, 1), (18, 1), (24, 1), (36, 1), (52, 1), (54, 1)] }, { coefficient := -1, powers := [(5, 1), (7, 1), (22, 1), (37, 1), (54, 1), (59, 1)] }, { coefficient := -1, powers := [(5, 1), (7, 1), (33, 1), (37, 1), (46, 1), (54, 1)] }, { coefficient := -1, powers := [(5, 1), (7, 1), (36, 1), (37, 1), (42, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (15, 1), (36, 1), (37, 1), (39, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (7, 1), (36, 1), (40, 1), (46, 1), (52, 1), (60, 1)] }, { coefficient := 1, powers := [(1, 1), (39, 1), (40, 1), (59, 1), (60, 1)] }, { coefficient := 1, powers := [(3, 1), (15, 1), (33, 1), (40, 1), (46, 1), (52, 1), (60, 1)] }, { coefficient := 1, powers := [(4, 1), (36, 1), (40, 1), (52, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (22, 1), (40, 1), (59, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (33, 1), (40, 1), (46, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (36, 1), (40, 1), (42, 1), (60, 1)] }, { coefficient := -1, powers := [(15, 1), (36, 1), (39, 1), (40, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (7, 1), (36, 1), (46, 1), (52, 1)] }, { coefficient := -1, powers := [(1, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(7, 1), (19, 1), (36, 1), (46, 1), (52, 1)] }, { coefficient := -1, powers := [(15, 1), (21, 1), (46, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (2, 1), (7, 1), (36, 1), (46, 1), (52, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (7, 1), (8, 1), (36, 1), (37, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(0, 1), (7, 1), (18, 1), (31, 1), (36, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(1, 1), (2, 1), (39, 1), (57, 1), (59, 1)] }, { coefficient := 1, powers := [(1, 1), (8, 1), (37, 1), (39, 1), (59, 1)] }, { coefficient := 1, powers := [(1, 1), (18, 1), (31, 1), (39, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (3, 1), (15, 1), (33, 1), (46, 1), (52, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (4, 1), (36, 1), (52, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (7, 1), (22, 1), (57, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (7, 1), (33, 1), (46, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (7, 1), (36, 1), (42, 1), (57, 1)] }, { coefficient := -1, powers := [(2, 1), (15, 1), (36, 1), (39, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (8, 1), (15, 1), (33, 1), (37, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(4, 1), (8, 1), (36, 1), (37, 1), (52, 1)] }, { coefficient := 1, powers := [(7, 1), (8, 1), (22, 1), (37, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (8, 1), (33, 1), (37, 1), (46, 1)] }, { coefficient := 1, powers := [(7, 1), (8, 1), (36, 1), (37, 1), (42, 1)] }, { coefficient := 1, powers := [(7, 1), (18, 1), (22, 1), (31, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (18, 1), (31, 1), (33, 1), (46, 1)] }, { coefficient := 1, powers := [(7, 1), (18, 1), (31, 1), (36, 1), (42, 1)] }, { coefficient := -1, powers := [(8, 1), (15, 1), (36, 1), (37, 1), (39, 1)] }, { coefficient := -1, powers := [(15, 1), (18, 1), (31, 1), (36, 1), (39, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (1, 1), (26, 1), (41, 1), (45, 1), (46, 2), (52, 1), (63, 1), (65, 1)] }, { coefficient := 1, powers := [(0, 1), (1, 1), (26, 1), (41, 1), (46, 1), (47, 1), (52, 1), (63, 1), (65, 1)] }, { coefficient := 1, powers := [(0, 1), (10, 1), (21, 1), (46, 1), (52, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (15, 1), (21, 1), (41, 1), (46, 1), (52, 1), (63, 1)] }, { coefficient := -1, powers := [(1, 1), (3, 1), (26, 1), (32, 1), (45, 1), (46, 2), (52, 1), (63, 1), (65, 1)] }, { coefficient := 1, powers := [(1, 1), (3, 1), (26, 1), (32, 1), (46, 1), (47, 1), (52, 1), (63, 1), (65, 1)] }, { coefficient := -1, powers := [(1, 1), (3, 1), (32, 1), (46, 1), (52, 1), (63, 1)] }, { coefficient := -1, powers := [(1, 1), (9, 1), (19, 1), (26, 1), (45, 1), (46, 2), (52, 1), (63, 1), (65, 1)] }, { coefficient := 1, powers := [(1, 1), (9, 1), (19, 1), (26, 1), (46, 1), (47, 1), (52, 1), (63, 1), (65, 1)] }, { coefficient := -1, powers := [(1, 1), (9, 1), (19, 1), (46, 1), (52, 1), (63, 1)] }, { coefficient := 1, powers := [(1, 1), (9, 1), (26, 1), (45, 1), (46, 1), (52, 1), (63, 1), (65, 1)] }, { coefficient := 1, powers := [(1, 1), (19, 1), (41, 1), (46, 1), (52, 1), (63, 1)] }, { coefficient := 1, powers := [(1, 1), (42, 1)] }, { coefficient := -1, powers := [(3, 1), (15, 1), (21, 1), (32, 1), (46, 1), (52, 1), (63, 1)] }, { coefficient := 1, powers := [(3, 1), (15, 1), (25, 1), (33, 1), (45, 1), (46, 1), (52, 1), (53, 1), (65, 1)] }, { coefficient := 1, powers := [(4, 1), (33, 1)] }, { coefficient := -1, powers := [(7, 1), (19, 1), (26, 1), (36, 1), (45, 1), (46, 1), (52, 1), (65, 1)] }, { coefficient := -1, powers := [(9, 1), (15, 1), (19, 1), (21, 1), (46, 1), (52, 1), (63, 1)] }, { coefficient := 1, powers := [(9, 1), (15, 1), (21, 1), (26, 1), (45, 1), (46, 1), (52, 1), (63, 1), (65, 1)] }, { coefficient := 1, powers := [(10, 1), (19, 1), (21, 1), (46, 1), (52, 1), (63, 1)] }, { coefficient := 1, powers := [(11, 1), (22, 1)] }, { coefficient := 1, powers := [(15, 1), (19, 1), (27, 1), (45, 1), (46, 1), (52, 1), (53, 1), (65, 1)] }, { coefficient := 1, powers := [(15, 1), (21, 1), (25, 1), (45, 1), (46, 1), (52, 1), (53, 1), (65, 1)] }, { coefficient := -1, powers := [(15, 1), (22, 1)] }, { coefficient := -1, powers := [(16, 1), (19, 1), (26, 1), (36, 1), (39, 1), (61, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (9, 1), (46, 1), (52, 1), (63, 1)] }, { coefficient := 1, powers := [(3, 1), (15, 1), (33, 1), (46, 1), (52, 1)] }, { coefficient := -1, powers := [(7, 1), (19, 1), (36, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(9, 1), (15, 1), (21, 1), (46, 1), (52, 1), (63, 1)] }, { coefficient := -1, powers := [(11, 1), (36, 1), (39, 1)] }, { coefficient := 1, powers := [(15, 1), (21, 1), (46, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (7, 1), (13, 1), (24, 1), (36, 1), (46, 1), (52, 1), (57, 1)] }, { coefficient := 1, powers := [(1, 1), (13, 1), (24, 1), (39, 1), (57, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (13, 1), (15, 1), (24, 1), (33, 1), (46, 1), (52, 1), (57, 1)] }, { coefficient := 1, powers := [(4, 1), (13, 1), (24, 1), (36, 1), (52, 1), (57, 1)] }, { coefficient := 1, powers := [(7, 1), (13, 1), (22, 1), (24, 1), (57, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (13, 1), (24, 1), (33, 1), (46, 1), (57, 1)] }, { coefficient := 1, powers := [(7, 1), (13, 1), (24, 1), (36, 1), (42, 1), (57, 1)] }, { coefficient := -1, powers := [(13, 1), (15, 1), (24, 1), (36, 1), (39, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (10, 1), (46, 1), (52, 1), (63, 1)] }, { coefficient := 1, powers := [(0, 1), (15, 1), (41, 1), (46, 1), (52, 1), (63, 1)] }, { coefficient := 1, powers := [(3, 1), (15, 1), (25, 1), (45, 1), (46, 1), (52, 1), (53, 1), (59, 1), (65, 1)] }, { coefficient := 1, powers := [(4, 1), (59, 1)] }, { coefficient := 1, powers := [(10, 1), (19, 1), (46, 1), (52, 1), (63, 1)] }, { coefficient := 1, powers := [(11, 1), (46, 1)] }, { coefficient := 1, powers := [(15, 1), (19, 1), (41, 1), (46, 1), (52, 1), (63, 1)] }, { coefficient := -1, powers := [(15, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (5, 1), (7, 1), (36, 1), (46, 1), (52, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (7, 1), (13, 1), (36, 1), (45, 1), (46, 1), (48, 1), (52, 1)] }, { coefficient := -1, powers := [(0, 1), (7, 1), (13, 1), (36, 1), (46, 1), (49, 1), (52, 1)] }, { coefficient := 1, powers := [(1, 1), (5, 1), (39, 1), (59, 1), (60, 1)] }, { coefficient := 1, powers := [(1, 1), (13, 1), (39, 1), (45, 1), (48, 1), (59, 1)] }, { coefficient := -1, powers := [(1, 1), (13, 1), (39, 1), (49, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (13, 1), (15, 1), (33, 1), (45, 1), (46, 1), (48, 1), (52, 1)] }, { coefficient := -1, powers := [(3, 1), (13, 1), (15, 1), (33, 1), (46, 1), (49, 1), (52, 1)] }, { coefficient := 1, powers := [(4, 1), (13, 1), (36, 1), (45, 1), (48, 1), (52, 1)] }, { coefficient := -1, powers := [(4, 1), (13, 1), (36, 1), (49, 1), (52, 1)] }, { coefficient := 1, powers := [(5, 1), (7, 1), (22, 1), (59, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (7, 1), (33, 1), (46, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (7, 1), (36, 1), (42, 1), (60, 1)] }, { coefficient := -1, powers := [(5, 1), (15, 1), (36, 1), (39, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (13, 1), (22, 1), (45, 1), (48, 1), (59, 1)] }, { coefficient := -1, powers := [(7, 1), (13, 1), (22, 1), (49, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (13, 1), (33, 1), (45, 1), (46, 1), (48, 1)] }, { coefficient := -1, powers := [(7, 1), (13, 1), (33, 1), (46, 1), (49, 1)] }, { coefficient := 1, powers := [(7, 1), (13, 1), (36, 1), (42, 1), (45, 1), (48, 1)] }, { coefficient := -1, powers := [(7, 1), (13, 1), (36, 1), (42, 1), (49, 1)] }, { coefficient := -1, powers := [(13, 1), (15, 1), (36, 1), (39, 1), (45, 1), (48, 1)] }, { coefficient := 1, powers := [(13, 1), (15, 1), (36, 1), (39, 1), (49, 1)] }]
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
    (values : Fin 67 → R) :
    ¬ ∀ index : Fin 54,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component18.SelectedLeafB6_6_1_4.selectedHasNoCommonZero

end Krenn.Component18.SelectedLeafB6_6_1_4
