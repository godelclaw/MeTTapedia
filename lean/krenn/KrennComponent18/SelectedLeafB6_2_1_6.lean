import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component18.SelectedLeafB6_2_1_6

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "7337ec7032138d30366872c637e1ab407427a7437c6725ceee77eb87c24b9a42"
def certificateSHA256 : String := "eb9f5a6188f2545b3bd56c6f8480a8441c2d2a7f2677e64b1aa4529eda6c75ec"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 55 → Fin 670 := ![
  7,
  10,
  15,
  19,
  142,
  143,
  147,
  148,
  149,
  152,
  156,
  162,
  163,
  168,
  225,
  294,
  295,
  308,
  318,
  323,
  327,
  355,
  387,
  403,
  405,
  424,
  425,
  426,
  428,
  429,
  437,
  438,
  440,
  442,
  443,
  449,
  458,
  466,
  468,
  496,
  551,
  562,
  580,
  581,
  608,
  609,
  657,
  658,
  659,
  660,
  663,
  665,
  666,
  667,
  669
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 55 → SparsePoly (Fin 67) := ![
  [{ coefficient := 1, powers := [(13, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(15, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (54, 1)] }, { coefficient := 1, powers := [(19, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (54, 1)] }, { coefficient := 1, powers := [(15, 1), (21, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (34, 1)] }, { coefficient := 1, powers := [(34, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (25, 1)] }, { coefficient := 1, powers := [(15, 1), (19, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (26, 1)] }, { coefficient := 1, powers := [(15, 1), (19, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (45, 1)] }, { coefficient := 1, powers := [(16, 1), (19, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (26, 1)] }, { coefficient := 1, powers := [(17, 1), (19, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (19, 1)] }, { coefficient := 1, powers := [(17, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (45, 1)] }, { coefficient := 1, powers := [(18, 1), (19, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (53, 1)] }, { coefficient := 1, powers := [(31, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (25, 1), (45, 1)] }, { coefficient := 1, powers := [(16, 1), (19, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1)] }, { coefficient := 1, powers := [(19, 1), (45, 1)] }, { coefficient := 1, powers := [(25, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (49, 1)] }, { coefficient := 1, powers := [(20, 1), (45, 1)] }, { coefficient := 1, powers := [(25, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (47, 1)] }, { coefficient := 1, powers := [(16, 1), (42, 1)] }, { coefficient := 1, powers := [(16, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (54, 1)] }, { coefficient := 1, powers := [(31, 1), (43, 1)] }, { coefficient := 1, powers := [(34, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1), (52, 1)] }, { coefficient := 1, powers := [(19, 1), (45, 1), (52, 1)] }, { coefficient := 1, powers := [(45, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (49, 1), (52, 1)] }, { coefficient := 1, powers := [(20, 1), (45, 1), (52, 1)] }, { coefficient := 1, powers := [(49, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (25, 1), (59, 1)] }, { coefficient := 1, powers := [(17, 1), (20, 1)] }, { coefficient := 1, powers := [(17, 1), (25, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (25, 1), (47, 1)] }, { coefficient := 1, powers := [(16, 1), (25, 1), (42, 1)] }, { coefficient := 1, powers := [(16, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (19, 1), (52, 1)] }, { coefficient := 1, powers := [(17, 1), (19, 1), (56, 1)] }, { coefficient := 1, powers := [(17, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (19, 1), (57, 1)] }, { coefficient := 1, powers := [(17, 1), (26, 1), (45, 1)] }, { coefficient := 1, powers := [(18, 1), (19, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1)] }, { coefficient := 1, powers := [(25, 1), (42, 1), (45, 1)] }, { coefficient := 1, powers := [(25, 1), (47, 1)] }, { coefficient := 1, powers := [(45, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (48, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1), (59, 1)] }, { coefficient := 1, powers := [(20, 1)] }, { coefficient := 1, powers := [(25, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (53, 1)] }, { coefficient := 1, powers := [(3, 1), (26, 1), (59, 1)] }, { coefficient := 1, powers := [(19, 1), (53, 1)] }, { coefficient := 1, powers := [(26, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (47, 1)] }, { coefficient := 1, powers := [(11, 1), (27, 1), (47, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (45, 1)] }, { coefficient := 1, powers := [(17, 1), (29, 1), (45, 1)] }, { coefficient := 1, powers := [(17, 1), (37, 1), (38, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1)] }, { coefficient := 1, powers := [(13, 1), (31, 1)] }, { coefficient := 1, powers := [(17, 1), (23, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (37, 1)] }, { coefficient := 1, powers := [(23, 1), (45, 1)] }, { coefficient := 1, powers := [(29, 1), (45, 1)] }, { coefficient := 1, powers := [(37, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (59, 1)] }, { coefficient := 1, powers := [(17, 1), (20, 1), (52, 1)] }, { coefficient := 1, powers := [(17, 1), (20, 1), (56, 1)] }, { coefficient := 1, powers := [(17, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (59, 1)] }, { coefficient := 1, powers := [(17, 1), (26, 1), (42, 1)] }, { coefficient := 1, powers := [(17, 1), (26, 1), (46, 1)] }, { coefficient := 1, powers := [(17, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (60, 1)] }, { coefficient := 1, powers := [(13, 1), (26, 1), (47, 1)] }, { coefficient := 1, powers := [(13, 1), (57, 1)] }, { coefficient := 1, powers := [(18, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (42, 1)] }, { coefficient := 1, powers := [(17, 1), (46, 1)] }, { coefficient := 1, powers := [(17, 1), (52, 1)] }, { coefficient := 1, powers := [(17, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1), (53, 1)] }, { coefficient := 1, powers := [(19, 1), (45, 1), (53, 1)] }, { coefficient := 1, powers := [(19, 1), (57, 1)] }, { coefficient := 1, powers := [(26, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (48, 1), (52, 1)] }, { coefficient := 1, powers := [(20, 1), (52, 1)] }, { coefficient := 1, powers := [(20, 1), (56, 1)] }, { coefficient := 1, powers := [(48, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (49, 1), (53, 1)] }, { coefficient := 1, powers := [(20, 1), (45, 1), (53, 1)] }, { coefficient := 1, powers := [(20, 1), (57, 1)] }, { coefficient := 1, powers := [(26, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (31, 1), (60, 1)] }, { coefficient := 1, powers := [(3, 1), (34, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (37, 1), (54, 1)] }, { coefficient := 1, powers := [(23, 1), (45, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (26, 1), (47, 1)] }, { coefficient := 1, powers := [(11, 1), (57, 1)] }, { coefficient := 1, powers := [(16, 1), (26, 1), (42, 1)] }, { coefficient := 1, powers := [(16, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (45, 1), (53, 1)] }, { coefficient := 1, powers := [(24, 1), (57, 1)] }, { coefficient := 1, powers := [(31, 1), (49, 1)] }, { coefficient := 1, powers := [(37, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1)] }, { coefficient := 1, powers := [(6, 1), (59, 1)] }, { coefficient := 1, powers := [(25, 1), (42, 1)] }, { coefficient := 1, powers := [(25, 1), (46, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (52, 1)] }, { coefficient := 1, powers := [(3, 1), (59, 1)] }, { coefficient := 1, powers := [(19, 1), (52, 1)] }, { coefficient := 1, powers := [(19, 1), (56, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (38, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1)] }, { coefficient := 1, powers := [(3, 1), (25, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (19, 1), (59, 1)] }, { coefficient := 1, powers := [(19, 1)] }, { coefficient := 1, powers := [(25, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (47, 1), (53, 1)] }, { coefficient := 1, powers := [(26, 1), (42, 1), (45, 1)] }, { coefficient := 1, powers := [(26, 1), (47, 1)] }, { coefficient := 1, powers := [(45, 1), (53, 1)] }, { coefficient := 1, powers := [(57, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (40, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (43, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (49, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (37, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (49, 1)] }, { coefficient := 1, powers := [(8, 1), (37, 1), (43, 1)] }, { coefficient := 1, powers := [(13, 1), (24, 1), (57, 1)] }, { coefficient := 1, powers := [(13, 1), (31, 1), (49, 1)] }, { coefficient := 1, powers := [(13, 1), (37, 1), (40, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (54, 1)] }, { coefficient := 1, powers := [(18, 1), (31, 1), (43, 1)] }, { coefficient := 1, powers := [(18, 1), (34, 1), (40, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (61, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(43, 1)] }],
  [{ coefficient := 1, powers := [(56, 1)] }],
  [{ coefficient := 1, powers := [(57, 1), (64, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(25, 1), (65, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(31, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 55 → SparsePoly (Fin 67) := ![
  [{ coefficient := 1, powers := [(0, 1), (24, 1), (42, 1), (57, 1), (65, 1)] }, { coefficient := 1, powers := [(0, 1), (24, 1), (46, 1), (57, 1), (65, 1)] }, { coefficient := 1, powers := [(3, 1), (26, 1), (37, 1), (42, 1), (48, 1), (65, 1)] }, { coefficient := 1, powers := [(3, 1), (26, 1), (37, 1), (46, 1), (48, 1), (65, 1)] }, { coefficient := 1, powers := [(6, 1), (24, 1), (57, 1), (59, 1), (65, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (42, 1), (57, 1), (65, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (46, 1), (57, 1), (65, 1)] }, { coefficient := 1, powers := [(24, 1), (25, 1), (42, 1), (57, 1), (65, 1)] }, { coefficient := 1, powers := [(24, 1), (25, 1), (46, 1), (57, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (24, 1), (26, 1), (42, 1)] }, { coefficient := 1, powers := [(0, 1), (24, 1), (26, 1), (46, 1)] }, { coefficient := 1, powers := [(6, 1), (24, 1), (26, 1), (59, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (26, 1), (42, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (26, 1), (46, 1)] }, { coefficient := 1, powers := [(24, 1), (25, 1), (26, 1), (42, 1)] }, { coefficient := 1, powers := [(24, 1), (25, 1), (26, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (6, 1), (21, 1), (37, 1), (59, 1), (62, 1)] }, { coefficient := 1, powers := [(5, 1), (21, 1), (25, 1), (37, 1), (42, 1), (62, 1)] }, { coefficient := 1, powers := [(5, 1), (21, 1), (25, 1), (37, 1), (46, 1), (62, 1)] }, { coefficient := -1, powers := [(6, 1), (18, 1), (21, 1), (24, 1), (59, 1), (62, 1)] }, { coefficient := -1, powers := [(18, 1), (21, 1), (24, 1), (25, 1), (42, 1), (62, 1)] }, { coefficient := -1, powers := [(18, 1), (21, 1), (24, 1), (25, 1), (46, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (17, 1), (42, 1), (49, 1)] }, { coefficient := 1, powers := [(0, 1), (17, 1), (46, 1), (49, 1)] }, { coefficient := -1, powers := [(6, 1), (17, 1), (45, 1), (48, 1), (59, 1)] }, { coefficient := 2, powers := [(6, 1), (17, 1), (49, 1), (59, 1)] }, { coefficient := 1, powers := [(17, 1), (19, 1), (42, 1), (49, 1)] }, { coefficient := 1, powers := [(17, 1), (19, 1), (46, 1), (49, 1)] }, { coefficient := 1, powers := [(17, 1), (25, 1), (42, 1), (45, 1), (48, 1)] }, { coefficient := 1, powers := [(17, 1), (25, 1), (42, 1), (49, 1)] }, { coefficient := 1, powers := [(17, 1), (25, 1), (45, 1), (46, 1), (48, 1)] }, { coefficient := 1, powers := [(17, 1), (25, 1), (46, 1), (49, 1)] }, { coefficient := 1, powers := [(18, 1), (20, 1), (42, 1)] }, { coefficient := 1, powers := [(18, 1), (20, 1), (46, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (37, 1), (42, 1)] }, { coefficient := -1, powers := [(5, 1), (37, 1), (46, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (42, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (46, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (6, 1), (37, 1), (59, 1), (62, 1)] }, { coefficient := -1, powers := [(5, 1), (25, 1), (37, 1), (42, 1), (62, 1)] }, { coefficient := -1, powers := [(5, 1), (25, 1), (37, 1), (46, 1), (62, 1)] }, { coefficient := 1, powers := [(6, 1), (18, 1), (24, 1), (59, 1), (62, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (25, 1), (42, 1), (62, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (25, 1), (46, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (5, 1), (42, 1), (57, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (5, 1), (46, 1), (57, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (57, 1), (62, 1), (64, 1)] }, { coefficient := 1, powers := [(27, 1), (45, 1), (53, 1), (61, 1), (62, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(27, 1), (45, 1), (61, 1), (62, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(26, 1), (27, 1), (61, 1), (62, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (37, 1), (42, 1), (48, 1)] }, { coefficient := -1, powers := [(3, 1), (37, 1), (46, 1), (48, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (3, 1), (34, 1), (42, 1), (48, 1), (52, 1), (57, 1)] }, { coefficient := -1, powers := [(0, 1), (3, 1), (34, 1), (46, 1), (48, 1), (52, 1), (57, 1)] }, { coefficient := -1, powers := [(0, 1), (6, 1), (34, 1), (42, 1), (48, 1), (52, 1), (57, 1)] }, { coefficient := -1, powers := [(0, 1), (6, 1), (34, 1), (46, 1), (48, 1), (52, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (37, 1), (42, 1), (48, 1), (54, 1)] }, { coefficient := 1, powers := [(3, 1), (37, 1), (46, 1), (48, 1), (54, 1)] }, { coefficient := -1, powers := [(6, 1), (20, 1), (34, 1), (42, 1), (52, 1), (57, 1)] }, { coefficient := -1, powers := [(6, 1), (20, 1), (34, 1), (46, 1), (52, 1), (57, 1)] }, { coefficient := -1, powers := [(6, 1), (34, 1), (42, 1), (48, 1), (57, 1)] }, { coefficient := -1, powers := [(6, 1), (34, 1), (46, 1), (48, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (34, 1), (48, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (13, 1), (42, 1), (45, 1)] }, { coefficient := 1, powers := [(0, 1), (13, 1), (45, 1), (46, 1)] }, { coefficient := 1, powers := [(6, 1), (13, 1), (45, 1), (59, 1)] }, { coefficient := 1, powers := [(13, 1), (19, 1), (42, 1), (45, 1)] }, { coefficient := 1, powers := [(13, 1), (19, 1), (45, 1), (46, 1)] }, { coefficient := 1, powers := [(13, 1), (25, 1), (42, 1), (45, 1)] }, { coefficient := 1, powers := [(13, 1), (25, 1), (45, 1), (46, 1)] }],
  [{ coefficient := -1, powers := [(27, 1), (53, 1), (61, 1), (62, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (5, 1), (34, 1), (42, 1), (46, 1), (53, 1)] }, { coefficient := 1, powers := [(0, 1), (5, 1), (34, 1), (46, 2), (53, 1)] }, { coefficient := 1, powers := [(5, 1), (19, 1), (34, 1), (42, 1), (46, 1), (53, 1)] }, { coefficient := 1, powers := [(5, 1), (19, 1), (34, 1), (46, 2), (53, 1)] }, { coefficient := 1, powers := [(5, 1), (26, 1), (34, 1), (42, 1), (46, 1)] }, { coefficient := 1, powers := [(5, 1), (26, 1), (34, 1), (46, 2)] }, { coefficient := -1, powers := [(6, 1), (17, 1), (20, 1), (26, 1), (34, 1), (42, 1), (52, 1), (65, 1)] }, { coefficient := -1, powers := [(6, 1), (17, 1), (20, 1), (26, 1), (34, 1), (46, 1), (52, 1), (65, 1)] }, { coefficient := 1, powers := [(6, 1), (17, 1), (20, 1), (34, 1), (42, 1), (53, 1), (65, 1)] }, { coefficient := 1, powers := [(6, 1), (17, 1), (20, 1), (34, 1), (46, 1), (53, 1), (65, 1)] }, { coefficient := 1, powers := [(42, 1), (53, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (17, 1), (19, 1), (26, 1), (34, 1), (42, 1), (52, 1), (65, 1)] }, { coefficient := 1, powers := [(6, 1), (17, 1), (19, 1), (26, 1), (34, 1), (46, 1), (52, 1), (65, 1)] }, { coefficient := -1, powers := [(6, 1), (17, 1), (19, 1), (34, 1), (42, 1), (53, 1), (65, 1)] }, { coefficient := -1, powers := [(6, 1), (17, 1), (19, 1), (34, 1), (46, 1), (53, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (26, 1), (27, 1), (61, 1), (62, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (18, 1), (42, 1)] }, { coefficient := -1, powers := [(0, 1), (18, 1), (46, 1)] }, { coefficient := -1, powers := [(6, 1), (18, 1), (59, 1)] }, { coefficient := -1, powers := [(18, 1), (19, 1), (42, 1)] }, { coefficient := -1, powers := [(18, 1), (19, 1), (46, 1)] }, { coefficient := -1, powers := [(18, 1), (25, 1), (42, 1)] }, { coefficient := -1, powers := [(18, 1), (25, 1), (46, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (19, 1), (26, 1), (34, 1), (42, 1), (46, 1)] }, { coefficient := -1, powers := [(5, 1), (19, 1), (26, 1), (34, 1), (46, 2)] }, { coefficient := 1, powers := [(5, 1), (25, 1), (26, 1), (34, 1), (42, 2)] }, { coefficient := 1, powers := [(5, 1), (25, 1), (26, 1), (34, 1), (42, 1), (46, 1)] }, { coefficient := 1, powers := [(5, 1), (26, 1), (34, 1), (42, 1)] }, { coefficient := 1, powers := [(5, 1), (26, 1), (34, 1), (46, 1)] }, { coefficient := 1, powers := [(6, 1), (17, 1), (20, 1), (26, 1), (34, 1), (42, 1), (65, 1)] }, { coefficient := 1, powers := [(6, 1), (17, 1), (20, 1), (26, 1), (34, 1), (46, 1), (65, 1)] }, { coefficient := -1, powers := [(6, 1), (17, 1), (26, 1), (34, 1), (42, 1), (48, 1), (57, 1), (64, 1)] }, { coefficient := -1, powers := [(6, 1), (17, 1), (26, 1), (34, 1), (46, 1), (48, 1), (57, 1), (64, 1)] }, { coefficient := 1, powers := [(15, 1), (22, 1), (26, 1), (62, 1), (64, 1)] }, { coefficient := -2, powers := [(26, 1), (42, 1), (64, 1)] }, { coefficient := -1, powers := [(26, 1), (46, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (17, 1), (19, 1), (26, 1), (34, 1), (42, 1), (65, 1)] }, { coefficient := -1, powers := [(6, 1), (17, 1), (19, 1), (26, 1), (34, 1), (46, 1), (65, 1)] }, { coefficient := 1, powers := [(6, 1), (17, 1), (26, 1), (34, 1), (42, 1)] }, { coefficient := 1, powers := [(6, 1), (17, 1), (26, 1), (34, 1), (46, 1)] }, { coefficient := -1, powers := [(6, 1), (17, 1), (34, 1), (53, 1)] }],
  [{ coefficient := 2, powers := [(3, 1), (34, 1), (42, 1), (57, 1)] }, { coefficient := 2, powers := [(3, 1), (34, 1), (46, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (26, 1), (62, 1), (64, 1)] }, { coefficient := -1, powers := [(27, 1), (53, 1), (62, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (3, 1), (34, 1), (42, 1), (48, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (3, 1), (34, 1), (46, 1), (48, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (6, 1), (34, 1), (42, 1), (48, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (6, 1), (34, 1), (46, 1), (48, 1), (57, 1)] }, { coefficient := 1, powers := [(6, 1), (34, 1), (48, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (34, 1), (48, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(53, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (17, 1), (34, 1), (42, 1), (57, 1)] }, { coefficient := -1, powers := [(3, 1), (17, 1), (34, 1), (46, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (19, 1), (34, 1), (42, 1), (45, 1), (46, 1)] }, { coefficient := -1, powers := [(5, 1), (19, 1), (34, 1), (45, 1), (46, 2)] }, { coefficient := 1, powers := [(5, 1), (25, 1), (34, 1), (42, 2), (45, 1)] }, { coefficient := 1, powers := [(5, 1), (25, 1), (34, 1), (42, 1), (45, 1), (46, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (42, 1), (45, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (45, 1), (46, 1)] }, { coefficient := -1, powers := [(6, 1), (17, 1), (34, 1), (42, 1), (45, 1), (48, 1), (57, 1), (64, 1)] }, { coefficient := 1, powers := [(6, 1), (17, 1), (34, 1), (42, 1), (49, 1)] }, { coefficient := -1, powers := [(6, 1), (17, 1), (34, 1), (45, 1), (46, 1), (48, 1), (57, 1), (64, 1)] }, { coefficient := 1, powers := [(6, 1), (17, 1), (34, 1), (46, 1), (49, 1)] }, { coefficient := 1, powers := [(15, 1), (22, 1), (45, 1), (62, 1), (64, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1), (61, 1), (62, 1), (64, 1)] }, { coefficient := -2, powers := [(42, 1), (45, 1), (64, 1)] }, { coefficient := -1, powers := [(45, 1), (46, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (53, 1), (62, 1), (64, 1)] }, { coefficient := -1, powers := [(26, 1), (62, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(20, 1), (42, 1), (54, 1)] }, { coefficient := -1, powers := [(20, 1), (46, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (42, 1), (49, 1)] }, { coefficient := -1, powers := [(0, 1), (46, 1), (49, 1)] }, { coefficient := 1, powers := [(6, 1), (45, 1), (48, 1), (59, 1)] }, { coefficient := -2, powers := [(6, 1), (49, 1), (59, 1)] }, { coefficient := -1, powers := [(19, 1), (42, 1), (49, 1)] }, { coefficient := -1, powers := [(19, 1), (46, 1), (49, 1)] }, { coefficient := -1, powers := [(25, 1), (42, 1), (49, 1)] }, { coefficient := -1, powers := [(25, 1), (46, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (20, 1), (42, 1), (54, 1)] }, { coefficient := 1, powers := [(17, 1), (20, 1), (46, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (6, 1), (34, 1), (42, 1), (57, 1)] }, { coefficient := -1, powers := [(0, 1), (6, 1), (34, 1), (46, 1), (57, 1)] }, { coefficient := -1, powers := [(3, 1), (25, 1), (34, 1), (42, 1), (57, 1)] }, { coefficient := -1, powers := [(3, 1), (25, 1), (34, 1), (46, 1), (57, 1)] }, { coefficient := -1, powers := [(6, 1), (34, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (34, 1), (45, 1), (48, 1)] }, { coefficient := 1, powers := [(6, 1), (34, 1), (49, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (24, 1), (42, 1)] }, { coefficient := -1, powers := [(0, 1), (24, 1), (46, 1)] }, { coefficient := -1, powers := [(6, 1), (24, 1), (59, 1)] }, { coefficient := -1, powers := [(19, 1), (24, 1), (42, 1)] }, { coefficient := -1, powers := [(19, 1), (24, 1), (46, 1)] }, { coefficient := -1, powers := [(24, 1), (25, 1), (42, 1)] }, { coefficient := -1, powers := [(24, 1), (25, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (26, 1), (34, 1), (45, 1), (48, 1)] }, { coefficient := -1, powers := [(6, 1), (26, 1), (34, 1), (49, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (5, 1), (34, 1), (42, 1), (46, 1)] }, { coefficient := -1, powers := [(0, 1), (5, 1), (34, 1), (46, 2)] }, { coefficient := -1, powers := [(5, 1), (25, 1), (34, 1), (42, 2)] }, { coefficient := -2, powers := [(5, 1), (25, 1), (34, 1), (42, 1), (46, 1)] }, { coefficient := -1, powers := [(5, 1), (25, 1), (34, 1), (46, 2)] }, { coefficient := -1, powers := [(5, 1), (34, 1), (42, 1)] }, { coefficient := -1, powers := [(5, 1), (34, 1), (46, 1)] }, { coefficient := -1, powers := [(6, 1), (17, 1), (20, 1), (34, 1), (42, 1), (65, 1)] }, { coefficient := -1, powers := [(6, 1), (17, 1), (20, 1), (34, 1), (46, 1), (65, 1)] }, { coefficient := 1, powers := [(6, 1), (17, 1), (34, 1), (42, 1), (48, 1), (57, 1), (64, 1)] }, { coefficient := 1, powers := [(6, 1), (17, 1), (34, 1), (46, 1), (48, 1), (57, 1), (64, 1)] }, { coefficient := -1, powers := [(15, 1), (22, 1), (62, 1), (64, 1)] }, { coefficient := 1, powers := [(42, 1), (64, 1)] }, { coefficient := 1, powers := [(46, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (17, 1), (25, 1), (34, 1), (42, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (17, 1), (25, 1), (34, 1), (46, 1), (57, 1)] }, { coefficient := 1, powers := [(6, 1), (17, 1), (25, 1), (34, 1), (42, 1), (57, 1)] }, { coefficient := 1, powers := [(6, 1), (17, 1), (25, 1), (34, 1), (46, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (17, 1), (19, 1), (34, 1), (42, 1), (65, 1)] }, { coefficient := 1, powers := [(6, 1), (17, 1), (19, 1), (34, 1), (46, 1), (65, 1)] }, { coefficient := -1, powers := [(6, 1), (17, 1), (34, 1), (42, 1)] }, { coefficient := -1, powers := [(6, 1), (17, 1), (34, 1), (46, 1)] }, { coefficient := 1, powers := [(6, 1), (17, 1), (34, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(17, 1), (20, 1), (42, 1)] }, { coefficient := -1, powers := [(17, 1), (20, 1), (46, 1)] }, { coefficient := -1, powers := [(17, 1), (25, 1), (42, 1), (48, 1)] }, { coefficient := -1, powers := [(17, 1), (25, 1), (46, 1), (48, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (27, 1), (61, 1), (62, 1), (64, 1)] }, { coefficient := -1, powers := [(22, 1), (25, 1), (62, 1), (64, 1)] }, { coefficient := 1, powers := [(27, 1), (62, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (13, 1), (42, 1)] }, { coefficient := -1, powers := [(0, 1), (13, 1), (46, 1)] }, { coefficient := -1, powers := [(6, 1), (13, 1), (59, 1)] }, { coefficient := -1, powers := [(13, 1), (19, 1), (42, 1)] }, { coefficient := -1, powers := [(13, 1), (19, 1), (46, 1)] }, { coefficient := -1, powers := [(13, 1), (25, 1), (42, 1)] }, { coefficient := -1, powers := [(13, 1), (25, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (19, 1), (34, 1), (42, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (19, 1), (34, 1), (46, 1), (57, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(5, 1), (19, 1), (26, 1), (34, 1), (42, 1), (45, 1), (46, 1)] }, { coefficient := 1, powers := [(5, 1), (19, 1), (26, 1), (34, 1), (45, 1), (46, 2)] }, { coefficient := -1, powers := [(5, 1), (25, 1), (26, 1), (34, 1), (42, 2), (45, 1)] }, { coefficient := -1, powers := [(5, 1), (25, 1), (26, 1), (34, 1), (42, 1), (45, 1), (46, 1)] }, { coefficient := -1, powers := [(5, 1), (26, 1), (34, 1), (42, 1), (45, 1)] }, { coefficient := -1, powers := [(5, 1), (26, 1), (34, 1), (45, 1), (46, 1)] }, { coefficient := 1, powers := [(6, 1), (17, 1), (20, 1), (34, 1), (42, 1), (57, 1)] }, { coefficient := 1, powers := [(6, 1), (17, 1), (20, 1), (34, 1), (46, 1), (57, 1)] }, { coefficient := 1, powers := [(6, 1), (17, 1), (26, 1), (34, 1), (42, 1), (45, 1), (48, 1), (57, 1), (64, 1)] }, { coefficient := -1, powers := [(6, 1), (17, 1), (26, 1), (34, 1), (42, 1), (49, 1)] }, { coefficient := 1, powers := [(6, 1), (17, 1), (26, 1), (34, 1), (45, 1), (46, 1), (48, 1), (57, 1), (64, 1)] }, { coefficient := -1, powers := [(6, 1), (17, 1), (26, 1), (34, 1), (46, 1), (49, 1)] }, { coefficient := -1, powers := [(15, 1), (22, 1), (26, 1), (45, 1), (62, 1), (64, 1)] }, { coefficient := -1, powers := [(16, 1), (26, 1), (27, 1), (61, 1), (62, 1), (64, 1)] }, { coefficient := 2, powers := [(26, 1), (42, 1), (45, 1), (64, 1)] }, { coefficient := 1, powers := [(26, 1), (45, 1), (46, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (34, 1), (42, 1), (57, 1)] }, { coefficient := -1, powers := [(5, 1), (34, 1), (46, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(64, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1)] }, { coefficient := 1, powers := [(0, 1), (46, 1)] }, { coefficient := 1, powers := [(6, 1), (59, 1)] }, { coefficient := 1, powers := [(19, 1), (42, 1)] }, { coefficient := 1, powers := [(19, 1), (46, 1)] }, { coefficient := 1, powers := [(25, 1), (42, 1)] }, { coefficient := 1, powers := [(25, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (27, 1), (57, 1), (62, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (6, 1), (37, 1), (54, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (25, 1), (37, 1), (42, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (25, 1), (37, 1), (46, 1), (54, 1)] }, { coefficient := -1, powers := [(6, 1), (18, 1), (24, 1), (54, 1), (59, 1)] }, { coefficient := -1, powers := [(18, 1), (24, 1), (25, 1), (42, 1), (54, 1)] }, { coefficient := -1, powers := [(18, 1), (24, 1), (25, 1), (46, 1), (54, 1)] }, { coefficient := -1, powers := [(25, 1), (47, 1), (53, 1), (64, 1)] }, { coefficient := 1, powers := [(26, 1), (47, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (40, 1), (42, 1), (60, 1)] }, { coefficient := -1, powers := [(0, 1), (40, 1), (46, 1), (60, 1)] }, { coefficient := -1, powers := [(6, 1), (40, 1), (59, 1), (60, 1)] }, { coefficient := -1, powers := [(6, 1), (45, 1), (48, 1), (54, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (49, 1), (54, 1), (59, 1)] }, { coefficient := -1, powers := [(19, 1), (40, 1), (42, 1), (60, 1)] }, { coefficient := -1, powers := [(19, 1), (40, 1), (46, 1), (60, 1)] }, { coefficient := 1, powers := [(20, 1), (42, 1), (45, 1), (54, 1)] }, { coefficient := 1, powers := [(20, 1), (45, 1), (46, 1), (54, 1)] }, { coefficient := -1, powers := [(25, 1), (40, 1), (42, 1), (60, 1)] }, { coefficient := -1, powers := [(25, 1), (40, 1), (46, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (2, 1), (42, 1), (57, 1)] }, { coefficient := -1, powers := [(0, 1), (2, 1), (46, 1), (57, 1)] }, { coefficient := -1, powers := [(0, 1), (8, 1), (37, 1), (42, 1)] }, { coefficient := -1, powers := [(0, 1), (8, 1), (37, 1), (46, 1)] }, { coefficient := -1, powers := [(2, 1), (6, 1), (57, 1), (59, 1)] }, { coefficient := -1, powers := [(2, 1), (19, 1), (42, 1), (57, 1)] }, { coefficient := -1, powers := [(2, 1), (19, 1), (46, 1), (57, 1)] }, { coefficient := -1, powers := [(2, 1), (25, 1), (42, 1), (57, 1)] }, { coefficient := -1, powers := [(2, 1), (25, 1), (46, 1), (57, 1)] }, { coefficient := -1, powers := [(6, 1), (8, 1), (37, 1), (59, 1)] }, { coefficient := -1, powers := [(8, 1), (19, 1), (37, 1), (42, 1)] }, { coefficient := -1, powers := [(8, 1), (19, 1), (37, 1), (46, 1)] }, { coefficient := -1, powers := [(8, 1), (25, 1), (37, 1), (42, 1)] }, { coefficient := -1, powers := [(8, 1), (25, 1), (37, 1), (46, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (3, 1), (17, 1), (19, 1), (34, 1), (42, 1), (48, 1), (57, 1)] }, { coefficient := -1, powers := [(0, 1), (3, 1), (17, 1), (19, 1), (34, 1), (46, 1), (48, 1), (57, 1)] }, { coefficient := -1, powers := [(0, 1), (6, 1), (17, 1), (19, 1), (34, 1), (42, 1), (48, 1), (57, 1)] }, { coefficient := -1, powers := [(0, 1), (6, 1), (17, 1), (19, 1), (34, 1), (46, 1), (48, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (6, 1), (17, 1), (20, 1), (34, 1), (42, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (6, 1), (17, 1), (20, 1), (34, 1), (46, 1), (57, 1)] }, { coefficient := -1, powers := [(5, 1), (19, 2), (26, 1), (34, 1), (42, 1), (45, 1), (46, 1)] }, { coefficient := -1, powers := [(5, 1), (19, 2), (26, 1), (34, 1), (45, 1), (46, 2)] }, { coefficient := 1, powers := [(5, 1), (19, 1), (25, 1), (26, 1), (34, 1), (42, 2), (45, 1)] }, { coefficient := 1, powers := [(5, 1), (19, 1), (25, 1), (26, 1), (34, 1), (42, 1), (45, 1), (46, 1)] }, { coefficient := 1, powers := [(5, 1), (19, 1), (26, 1), (34, 1), (42, 1), (45, 1)] }, { coefficient := 1, powers := [(5, 1), (19, 1), (26, 1), (34, 1), (45, 1), (46, 1)] }, { coefficient := -1, powers := [(6, 1), (17, 1), (19, 1), (20, 1), (34, 1), (42, 1), (57, 1)] }, { coefficient := -1, powers := [(6, 1), (17, 1), (19, 1), (20, 1), (34, 1), (46, 1), (57, 1)] }, { coefficient := -1, powers := [(6, 1), (17, 1), (19, 1), (26, 1), (34, 1), (42, 1), (45, 1), (48, 1), (57, 1), (64, 1)] }, { coefficient := 1, powers := [(6, 1), (17, 1), (19, 1), (26, 1), (34, 1), (42, 1), (49, 1)] }, { coefficient := -1, powers := [(6, 1), (17, 1), (19, 1), (26, 1), (34, 1), (45, 1), (46, 1), (48, 1), (57, 1), (64, 1)] }, { coefficient := 1, powers := [(6, 1), (17, 1), (19, 1), (26, 1), (34, 1), (46, 1), (49, 1)] }, { coefficient := -1, powers := [(6, 1), (17, 1), (19, 1), (34, 1), (48, 1), (57, 1)] }, { coefficient := -1, powers := [(6, 1), (17, 1), (20, 1), (25, 1), (34, 1), (42, 1), (57, 1)] }, { coefficient := -1, powers := [(6, 1), (17, 1), (20, 1), (25, 1), (34, 1), (46, 1), (57, 1)] }, { coefficient := 1, powers := [(6, 1), (17, 1), (20, 1), (34, 1), (57, 1)] }, { coefficient := -1, powers := [(6, 1), (17, 1), (26, 1), (34, 1), (45, 1), (48, 1)] }, { coefficient := 1, powers := [(6, 1), (17, 1), (26, 1), (34, 1), (49, 1)] }, { coefficient := 1, powers := [(15, 1), (19, 1), (22, 1), (26, 1), (45, 1), (62, 1), (64, 1)] }, { coefficient := 1, powers := [(16, 1), (19, 1), (26, 1), (27, 1), (61, 1), (62, 1), (64, 1)] }, { coefficient := -2, powers := [(19, 1), (26, 1), (42, 1), (45, 1), (64, 1)] }, { coefficient := -1, powers := [(19, 1), (26, 1), (45, 1), (46, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (42, 1)] }, { coefficient := -1, powers := [(6, 1), (17, 1), (19, 1), (34, 1), (42, 1), (48, 1), (57, 1)] }, { coefficient := -1, powers := [(6, 1), (17, 1), (19, 1), (34, 1), (46, 1), (48, 1), (57, 1)] }, { coefficient := -1, powers := [(19, 1), (42, 1)] }, { coefficient := -1, powers := [(19, 1), (46, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(0, 1), (13, 1), (24, 1), (42, 1), (57, 1)] }, { coefficient := -1, powers := [(0, 1), (13, 1), (24, 1), (46, 1), (57, 1)] }, { coefficient := -1, powers := [(3, 1), (13, 1), (26, 1), (37, 1), (42, 1), (48, 1)] }, { coefficient := -1, powers := [(3, 1), (13, 1), (26, 1), (37, 1), (46, 1), (48, 1)] }, { coefficient := -1, powers := [(6, 1), (13, 1), (24, 1), (57, 1), (59, 1)] }, { coefficient := -1, powers := [(6, 1), (17, 1), (19, 1), (26, 1), (34, 1), (42, 1), (49, 1), (52, 1)] }, { coefficient := -1, powers := [(6, 1), (17, 1), (19, 1), (26, 1), (34, 1), (46, 1), (49, 1), (52, 1)] }, { coefficient := 1, powers := [(6, 1), (17, 1), (19, 1), (34, 1), (42, 1), (49, 1), (53, 1)] }, { coefficient := 1, powers := [(6, 1), (17, 1), (19, 1), (34, 1), (46, 1), (49, 1), (53, 1)] }, { coefficient := 1, powers := [(6, 1), (17, 1), (20, 1), (26, 1), (34, 1), (42, 1), (45, 1), (52, 1)] }, { coefficient := 1, powers := [(6, 1), (17, 1), (20, 1), (26, 1), (34, 1), (45, 1), (46, 1), (52, 1)] }, { coefficient := -1, powers := [(6, 1), (17, 1), (20, 1), (34, 1), (42, 1), (45, 1), (53, 1)] }, { coefficient := -1, powers := [(6, 1), (17, 1), (20, 1), (34, 1), (45, 1), (46, 1), (53, 1)] }, { coefficient := -1, powers := [(13, 1), (19, 1), (24, 1), (42, 1), (57, 1)] }, { coefficient := -1, powers := [(13, 1), (19, 1), (24, 1), (46, 1), (57, 1)] }, { coefficient := -1, powers := [(13, 1), (24, 1), (25, 1), (42, 1), (57, 1)] }, { coefficient := -1, powers := [(13, 1), (24, 1), (25, 1), (46, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (5, 1), (42, 1), (60, 1)] }, { coefficient := -1, powers := [(0, 1), (5, 1), (46, 1), (60, 1)] }, { coefficient := -1, powers := [(0, 1), (13, 1), (42, 1), (45, 1), (48, 1)] }, { coefficient := 1, powers := [(0, 1), (13, 1), (42, 1), (49, 1)] }, { coefficient := -1, powers := [(0, 1), (13, 1), (45, 1), (46, 1), (48, 1)] }, { coefficient := 1, powers := [(0, 1), (13, 1), (46, 1), (49, 1)] }, { coefficient := 1, powers := [(3, 1), (17, 1), (20, 1), (42, 1), (60, 1)] }, { coefficient := 1, powers := [(3, 1), (17, 1), (20, 1), (46, 1), (60, 1)] }, { coefficient := 1, powers := [(3, 1), (17, 1), (25, 1), (42, 1), (48, 1), (60, 1)] }, { coefficient := 1, powers := [(3, 1), (17, 1), (25, 1), (46, 1), (48, 1), (60, 1)] }, { coefficient := -1, powers := [(5, 1), (6, 1), (59, 1), (60, 1)] }, { coefficient := -1, powers := [(5, 1), (19, 1), (42, 1), (60, 1)] }, { coefficient := -1, powers := [(5, 1), (19, 1), (46, 1), (60, 1)] }, { coefficient := -1, powers := [(5, 1), (25, 1), (42, 1), (60, 1)] }, { coefficient := -1, powers := [(5, 1), (25, 1), (46, 1), (60, 1)] }, { coefficient := -2, powers := [(6, 1), (13, 1), (45, 1), (48, 1), (59, 1)] }, { coefficient := 2, powers := [(6, 1), (13, 1), (49, 1), (59, 1)] }, { coefficient := -1, powers := [(13, 1), (19, 1), (42, 1), (45, 1), (48, 1)] }, { coefficient := 1, powers := [(13, 1), (19, 1), (42, 1), (49, 1)] }, { coefficient := -1, powers := [(13, 1), (19, 1), (45, 1), (46, 1), (48, 1)] }, { coefficient := 1, powers := [(13, 1), (19, 1), (46, 1), (49, 1)] }, { coefficient := -1, powers := [(13, 1), (25, 1), (42, 1), (45, 1), (48, 1)] }, { coefficient := 1, powers := [(13, 1), (25, 1), (42, 1), (49, 1)] }, { coefficient := -1, powers := [(13, 1), (25, 1), (45, 1), (46, 1), (48, 1)] }, { coefficient := 1, powers := [(13, 1), (25, 1), (46, 1), (49, 1)] }]
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
    (values : Fin 67 → R) :
    ¬ ∀ index : Fin 55,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((2 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (2 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (2 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component18.SelectedLeafB6_2_1_6.selectedHasNoCommonZero

end Krenn.Component18.SelectedLeafB6_2_1_6
