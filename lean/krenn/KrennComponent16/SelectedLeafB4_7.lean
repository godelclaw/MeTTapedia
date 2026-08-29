import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component16.SelectedLeafB4_7

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "b5ff296db5fe899b53d2a431184f282ac0c2b1051ac7dcbdbf9a20a7b53e5fd9"
def certificateSHA256 : String := "55a79d71f555d925d967910b7f859a36b4ccdcfa8b0f5add57e4c615071d0604"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 33 → Fin 668 := ![
  13,
  23,
  24,
  30,
  33,
  161,
  162,
  170,
  173,
  299,
  302,
  314,
  315,
  316,
  325,
  366,
  407,
  408,
  428,
  436,
  440,
  448,
  468,
  571,
  584,
  595,
  612,
  654,
  661,
  662,
  664,
  666,
  667
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 33 → SparsePoly (Fin 66) := ![
  [{ coefficient := 1, powers := [(13, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(26, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(30, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(43, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (29, 1)] }, { coefficient := 1, powers := [(19, 1), (34, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (47, 1)] }, { coefficient := 1, powers := [(13, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (45, 1)] }, { coefficient := 1, powers := [(29, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1), (57, 1)] }, { coefficient := 1, powers := [(43, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (50, 1)] }, { coefficient := 1, powers := [(22, 1), (45, 1)] }, { coefficient := 1, powers := [(26, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (61, 1)] }, { coefficient := 1, powers := [(13, 1), (50, 1)] }, { coefficient := 1, powers := [(20, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (48, 1)] }, { coefficient := 1, powers := [(20, 1), (42, 1)] }, { coefficient := 1, powers := [(20, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (53, 1)] }, { coefficient := 1, powers := [(25, 1), (57, 1)] }, { coefficient := 1, powers := [(30, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (55, 1)] }, { coefficient := 1, powers := [(31, 1), (43, 1)] }, { coefficient := 1, powers := [(34, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (50, 1), (53, 1)] }, { coefficient := 1, powers := [(22, 1), (45, 1), (53, 1)] }, { coefficient := 1, powers := [(50, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (25, 1), (60, 1)] }, { coefficient := 1, powers := [(25, 1)] }, { coefficient := 1, powers := [(29, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (26, 1), (42, 1)] }, { coefficient := 1, powers := [(19, 1), (26, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (26, 1), (48, 1)] }, { coefficient := 1, powers := [(20, 1), (26, 1), (42, 1)] }, { coefficient := 1, powers := [(20, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (48, 1)] }, { coefficient := 1, powers := [(26, 1), (42, 1), (45, 1)] }, { coefficient := 1, powers := [(26, 1), (48, 1)] }, { coefficient := 1, powers := [(45, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (50, 1)] }, { coefficient := 1, powers := [(5, 1), (37, 1)] }, { coefficient := 1, powers := [(19, 1), (29, 1), (50, 1)] }, { coefficient := 1, powers := [(20, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1)] }, { coefficient := 1, powers := [(13, 1), (31, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (61, 1)] }, { coefficient := 1, powers := [(13, 1), (27, 1), (48, 1)] }, { coefficient := 1, powers := [(13, 1), (58, 1)] }, { coefficient := 1, powers := [(20, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (48, 1), (53, 1)] }, { coefficient := 1, powers := [(42, 1), (45, 1)] }, { coefficient := 1, powers := [(45, 1), (53, 1)] }, { coefficient := 1, powers := [(48, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (45, 1), (54, 1)] }, { coefficient := 1, powers := [(25, 1), (58, 1)] }, { coefficient := 1, powers := [(31, 1), (50, 1)] }, { coefficient := 1, powers := [(37, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1)] }, { coefficient := 1, powers := [(6, 1), (60, 1)] }, { coefficient := 1, powers := [(26, 1), (42, 1)] }, { coefficient := 1, powers := [(26, 1), (47, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (43, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (57, 1)] }, { coefficient := 1, powers := [(13, 1), (25, 1), (57, 1)] }, { coefficient := 1, powers := [(13, 1), (30, 1), (49, 1)] }, { coefficient := 1, powers := [(19, 1), (30, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1), (58, 1)] }, { coefficient := 1, powers := [(0, 1), (48, 1), (54, 1)] }, { coefficient := 1, powers := [(27, 1), (42, 1), (45, 1)] }, { coefficient := 1, powers := [(27, 1), (48, 1)] }, { coefficient := 1, powers := [(45, 1), (54, 1)] }, { coefficient := 1, powers := [(58, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (42, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (48, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (37, 1), (42, 1)] }, { coefficient := 1, powers := [(19, 1), (30, 1), (58, 1)] }, { coefficient := 1, powers := [(19, 1), (31, 1), (48, 1)] }, { coefficient := 1, powers := [(20, 1), (30, 1), (54, 1)] }, { coefficient := 1, powers := [(20, 1), (31, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (40, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (43, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (50, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (37, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (25, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (50, 1)] }, { coefficient := 1, powers := [(8, 1), (37, 1), (43, 1)] }, { coefficient := 1, powers := [(13, 1), (25, 1), (58, 1)] }, { coefficient := 1, powers := [(13, 1), (31, 1), (50, 1)] }, { coefficient := 1, powers := [(13, 1), (37, 1), (40, 1)] }, { coefficient := 1, powers := [(20, 1), (25, 1), (55, 1)] }, { coefficient := 1, powers := [(20, 1), (31, 1), (43, 1)] }, { coefficient := 1, powers := [(20, 1), (34, 1), (40, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(42, 1), (64, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(43, 1), (65, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 33 → SparsePoly (Fin 66) := ![
  [{ coefficient := -1, powers := [(0, 2), (25, 1), (27, 1), (42, 1), (57, 1)] }, { coefficient := -1, powers := [(0, 1), (25, 1), (27, 1), (42, 1)] }, { coefficient := -1, powers := [(25, 1), (27, 1)] }],
  [{ coefficient := -1, powers := [(0, 2), (19, 1), (42, 1), (50, 1), (57, 1)] }, { coefficient := -1, powers := [(0, 1), (19, 1), (42, 1), (50, 1)] }, { coefficient := -1, powers := [(19, 1), (50, 1)] }],
  [{ coefficient := -2, powers := [(0, 2), (13, 1), (31, 1), (42, 1), (50, 1), (53, 1), (57, 1), (65, 1)] }, { coefficient := -2, powers := [(0, 2), (20, 1), (25, 1), (42, 1), (53, 1), (55, 1), (57, 1), (65, 1)] }, { coefficient := -1, powers := [(0, 2), (20, 1), (31, 1), (42, 1), (43, 1), (53, 1), (57, 1), (65, 1)] }, { coefficient := 1, powers := [(0, 2), (20, 1), (31, 1), (43, 1), (53, 2), (57, 1), (65, 1)] }, { coefficient := -1, powers := [(0, 1), (5, 1), (27, 1), (34, 1), (48, 1), (53, 1), (57, 1), (65, 1)] }, { coefficient := 1, powers := [(0, 1), (5, 1), (34, 1), (48, 1), (54, 1), (57, 1), (65, 1)] }, { coefficient := 1, powers := [(0, 1), (13, 1), (25, 1), (27, 1), (48, 1), (53, 1), (57, 1), (65, 1)] }, { coefficient := 2, powers := [(0, 1), (13, 1), (25, 1), (42, 1), (58, 1), (62, 1), (65, 1)] }, { coefficient := 2, powers := [(0, 1), (13, 1), (25, 1), (47, 1), (58, 1), (62, 1), (65, 1)] }, { coefficient := -1, powers := [(0, 1), (13, 1), (25, 1), (48, 1), (54, 1), (57, 1), (65, 1)] }, { coefficient := -2, powers := [(0, 1), (13, 1), (31, 1), (42, 1), (50, 1), (53, 1), (65, 1)] }, { coefficient := -2, powers := [(0, 1), (19, 1), (34, 1), (38, 1), (42, 1), (49, 1), (58, 1), (62, 1), (65, 1)] }, { coefficient := -2, powers := [(0, 1), (19, 1), (34, 1), (38, 1), (47, 1), (49, 1), (58, 1), (62, 1), (65, 1)] }, { coefficient := -2, powers := [(0, 1), (20, 1), (25, 1), (42, 1), (53, 1), (55, 1), (65, 1)] }, { coefficient := -1, powers := [(0, 1), (20, 1), (31, 1), (42, 1), (43, 1), (53, 1), (65, 1)] }, { coefficient := 1, powers := [(0, 1), (20, 1), (31, 1), (43, 1), (53, 2), (65, 1)] }, { coefficient := -1, powers := [(5, 1), (27, 1), (34, 1), (48, 1), (53, 1), (65, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (48, 1), (54, 1), (65, 1)] }, { coefficient := 1, powers := [(13, 1), (25, 1), (27, 1), (48, 1), (53, 1), (65, 1)] }, { coefficient := -1, powers := [(13, 1), (25, 1), (48, 1), (54, 1), (65, 1)] }, { coefficient := -2, powers := [(13, 1), (31, 1), (50, 1), (53, 1), (65, 1)] }, { coefficient := -2, powers := [(20, 1), (25, 1), (53, 1), (55, 1), (65, 1)] }, { coefficient := 1, powers := [(20, 1), (31, 1), (43, 1), (53, 2), (64, 1), (65, 1)] }, { coefficient := -1, powers := [(20, 1), (31, 1), (43, 1), (53, 1), (65, 1)] }],
  [{ coefficient := 2, powers := [(0, 2), (13, 1), (49, 1), (58, 1), (62, 1), (65, 1)] }, { coefficient := -1, powers := [(0, 2), (19, 1), (43, 1), (57, 1), (58, 1), (65, 1)] }, { coefficient := -1, powers := [(0, 2), (20, 1), (43, 1), (54, 1), (57, 1), (65, 1)] }, { coefficient := -1, powers := [(0, 1), (13, 1), (49, 1), (58, 1), (65, 1)] }, { coefficient := -1, powers := [(0, 1), (19, 1), (43, 1), (58, 1), (65, 1)] }, { coefficient := 1, powers := [(0, 1), (19, 1), (58, 1)] }, { coefficient := -1, powers := [(0, 1), (20, 1), (43, 1), (54, 1), (65, 1)] }, { coefficient := -1, powers := [(19, 1), (43, 1), (58, 1), (64, 1), (65, 1)] }, { coefficient := -1, powers := [(20, 1), (43, 1), (54, 1), (64, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(0, 2), (13, 1), (25, 1), (42, 1), (54, 1), (57, 1), (65, 1)] }, { coefficient := 1, powers := [(0, 2), (19, 1), (25, 1), (42, 1), (55, 1), (57, 1), (65, 1)] }, { coefficient := -1, powers := [(0, 1), (5, 1), (26, 1), (27, 1), (34, 1), (42, 1), (53, 1), (57, 1), (65, 1)] }, { coefficient := 1, powers := [(0, 1), (5, 1), (26, 1), (34, 1), (42, 1), (54, 1), (57, 1), (65, 1)] }, { coefficient := 1, powers := [(0, 1), (13, 1), (25, 1), (26, 1), (27, 1), (42, 1), (53, 1), (57, 1), (65, 1)] }, { coefficient := -1, powers := [(0, 1), (13, 1), (25, 1), (26, 1), (42, 1), (54, 1), (57, 1), (65, 1)] }, { coefficient := -1, powers := [(0, 1), (13, 1), (25, 1), (42, 1), (54, 1), (65, 1)] }, { coefficient := 1, powers := [(0, 1), (19, 1), (25, 1), (42, 1), (55, 1), (65, 1)] }, { coefficient := -1, powers := [(5, 1), (26, 1), (27, 1), (34, 1), (42, 1), (53, 1), (65, 1)] }, { coefficient := 1, powers := [(5, 1), (26, 1), (34, 1), (42, 1), (54, 1), (65, 1)] }, { coefficient := 1, powers := [(13, 1), (25, 1), (26, 1), (27, 1), (42, 1), (53, 1), (65, 1)] }, { coefficient := -1, powers := [(13, 1), (25, 1), (26, 1), (42, 1), (54, 1), (65, 1)] }, { coefficient := -1, powers := [(13, 1), (25, 1), (54, 1), (65, 1)] }, { coefficient := 1, powers := [(19, 1), (25, 1), (55, 1), (65, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (49, 1), (58, 1), (62, 1)] }],
  [{ coefficient := 2, powers := [(0, 2), (25, 1), (58, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(0, 2), (19, 1), (42, 1), (55, 1), (57, 1)] }, { coefficient := -1, powers := [(0, 1), (19, 1), (42, 1), (55, 1)] }, { coefficient := -1, powers := [(19, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (42, 1), (65, 1)] }],
  [{ coefficient := 2, powers := [(0, 2), (13, 1), (31, 1), (42, 1), (53, 1), (57, 1)] }, { coefficient := 2, powers := [(0, 1), (13, 1), (31, 1), (42, 1), (53, 1)] }, { coefficient := 2, powers := [(13, 1), (31, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(0, 2), (31, 1), (42, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (31, 1), (42, 1)] }, { coefficient := 1, powers := [(31, 1)] }],
  [{ coefficient := 2, powers := [(0, 2), (25, 1), (26, 1), (42, 1), (55, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 2), (26, 1), (31, 1), (42, 1), (43, 1), (57, 1)] }, { coefficient := -1, powers := [(0, 2), (26, 1), (31, 1), (43, 1), (53, 1), (57, 1)] }, { coefficient := -1, powers := [(0, 2), (31, 1), (43, 1), (57, 1)] }, { coefficient := 2, powers := [(0, 1), (25, 1), (26, 1), (42, 1), (55, 1)] }, { coefficient := 1, powers := [(0, 1), (26, 1), (31, 1), (42, 1), (43, 1)] }, { coefficient := -1, powers := [(0, 1), (26, 1), (31, 1), (43, 1), (53, 1)] }, { coefficient := -1, powers := [(0, 1), (31, 1), (43, 1)] }, { coefficient := 2, powers := [(25, 1), (26, 1), (55, 1)] }, { coefficient := -1, powers := [(26, 1), (31, 1), (43, 1), (53, 1), (64, 1)] }, { coefficient := 1, powers := [(26, 1), (31, 1), (43, 1)] }, { coefficient := -1, powers := [(31, 1), (43, 1), (64, 1)] }],
  [{ coefficient := -2, powers := [(0, 2), (13, 1), (58, 1), (62, 1)] }, { coefficient := 2, powers := [(0, 1), (13, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(0, 2), (20, 1), (42, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (20, 1), (42, 1)] }, { coefficient := 1, powers := [(20, 1)] }],
  [{ coefficient := -2, powers := [(0, 2), (13, 1), (31, 1), (42, 1), (57, 1)] }, { coefficient := -2, powers := [(0, 1), (13, 1), (31, 1), (42, 1)] }, { coefficient := -2, powers := [(13, 1), (31, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (13, 1), (58, 1), (62, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (34, 1), (38, 1), (49, 1), (58, 1), (62, 1)] }],
  [{ coefficient := -2, powers := [(0, 2), (25, 1), (42, 1), (55, 1), (57, 1)] }, { coefficient := -1, powers := [(0, 2), (31, 1), (42, 1), (43, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 2), (31, 1), (43, 1), (53, 1), (57, 1)] }, { coefficient := -2, powers := [(0, 1), (25, 1), (42, 1), (55, 1)] }, { coefficient := -1, powers := [(0, 1), (31, 1), (42, 1), (43, 1)] }, { coefficient := 1, powers := [(0, 1), (31, 1), (43, 1), (53, 1)] }, { coefficient := -2, powers := [(25, 1), (55, 1)] }, { coefficient := 1, powers := [(31, 1), (43, 1), (53, 1), (64, 1)] }, { coefficient := -1, powers := [(31, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (5, 1), (27, 1), (34, 1), (53, 1), (57, 1)] }, { coefficient := -1, powers := [(0, 1), (5, 1), (34, 1), (54, 1), (57, 1)] }, { coefficient := -1, powers := [(0, 1), (13, 1), (25, 1), (27, 1), (53, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (13, 1), (25, 1), (54, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (27, 1), (34, 1), (53, 1)] }, { coefficient := -1, powers := [(5, 1), (34, 1), (54, 1)] }, { coefficient := -1, powers := [(13, 1), (25, 1), (27, 1), (53, 1)] }, { coefficient := 1, powers := [(13, 1), (25, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(0, 2), (42, 1), (55, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (42, 1), (55, 1)] }, { coefficient := 1, powers := [(55, 1)] }],
  [{ coefficient := 1, powers := [(0, 2), (42, 1), (50, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (42, 1), (50, 1)] }, { coefficient := 1, powers := [(50, 1)] }],
  [{ coefficient := 1, powers := [(0, 2), (25, 1), (42, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (25, 1), (42, 1)] }, { coefficient := 1, powers := [(25, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (5, 1), (27, 1), (34, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (13, 1), (25, 1), (27, 1), (57, 1)] }, { coefficient := -1, powers := [(5, 1), (27, 1), (34, 1)] }, { coefficient := 1, powers := [(13, 1), (25, 1), (27, 1)] }],
  [{ coefficient := 1, powers := [(0, 2), (13, 1), (42, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (13, 1), (42, 1)] }, { coefficient := 1, powers := [(13, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (13, 1), (25, 1), (58, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (5, 1), (34, 1), (57, 1)] }, { coefficient := -1, powers := [(0, 1), (13, 1), (25, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1)] }, { coefficient := -1, powers := [(13, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(0, 2), (43, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (43, 1)] }, { coefficient := 1, powers := [(43, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(0, 2), (42, 1), (57, 1)] }, { coefficient := -1, powers := [(0, 1), (42, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 2, powers := [(0, 1), (13, 1), (25, 1), (53, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(0, 2), (40, 1), (42, 1), (57, 1), (61, 1)] }, { coefficient := -1, powers := [(0, 2), (42, 1), (50, 1), (55, 1), (57, 1)] }, { coefficient := -1, powers := [(0, 2), (43, 1), (48, 1), (54, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (40, 1), (42, 1), (61, 1)] }, { coefficient := -1, powers := [(0, 1), (42, 1), (50, 1), (55, 1)] }, { coefficient := -1, powers := [(0, 1), (43, 1), (48, 1), (54, 1)] }, { coefficient := 1, powers := [(0, 1), (43, 1), (57, 1), (58, 1)] }, { coefficient := 1, powers := [(40, 1), (61, 1)] }, { coefficient := -1, powers := [(42, 1), (43, 1), (58, 1), (64, 1)] }, { coefficient := -1, powers := [(43, 1), (48, 1), (54, 1), (64, 1)] }, { coefficient := 1, powers := [(43, 1), (58, 1)] }, { coefficient := -1, powers := [(50, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (37, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(0, 2), (13, 1), (25, 1), (42, 1), (45, 1), (54, 1), (57, 1)] }, { coefficient := 2, powers := [(0, 2), (13, 1), (26, 1), (31, 1), (42, 1), (50, 1), (53, 1), (57, 1)] }, { coefficient := -2, powers := [(0, 2), (13, 1), (30, 1), (49, 1), (58, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 2), (19, 1), (25, 1), (42, 1), (45, 1), (55, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 2), (19, 1), (30, 1), (43, 1), (57, 1), (58, 1)] }, { coefficient := 2, powers := [(0, 2), (20, 1), (25, 1), (26, 1), (42, 1), (53, 1), (55, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 2), (20, 1), (26, 1), (31, 1), (42, 1), (43, 1), (53, 1), (57, 1)] }, { coefficient := -1, powers := [(0, 2), (20, 1), (26, 1), (31, 1), (43, 1), (53, 2), (57, 1)] }, { coefficient := 1, powers := [(0, 2), (20, 1), (30, 1), (43, 1), (54, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 2), (42, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (5, 1), (26, 1), (27, 1), (34, 1), (42, 1), (45, 1), (53, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (5, 1), (26, 1), (27, 1), (34, 1), (48, 1), (53, 1), (57, 1)] }, { coefficient := -1, powers := [(0, 1), (5, 1), (26, 1), (34, 1), (42, 1), (45, 1), (54, 1), (57, 1)] }, { coefficient := -1, powers := [(0, 1), (5, 1), (26, 1), (34, 1), (48, 1), (54, 1), (57, 1)] }, { coefficient := -1, powers := [(0, 1), (13, 1), (25, 1), (26, 1), (27, 1), (42, 1), (45, 1), (53, 1), (57, 1)] }, { coefficient := -1, powers := [(0, 1), (13, 1), (25, 1), (26, 1), (27, 1), (48, 1), (53, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (13, 1), (25, 1), (26, 1), (42, 1), (45, 1), (54, 1), (57, 1)] }, { coefficient := -2, powers := [(0, 1), (13, 1), (25, 1), (26, 1), (42, 1), (58, 1), (62, 1)] }, { coefficient := -2, powers := [(0, 1), (13, 1), (25, 1), (26, 1), (47, 1), (58, 1), (62, 1)] }, { coefficient := 1, powers := [(0, 1), (13, 1), (25, 1), (26, 1), (48, 1), (54, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (13, 1), (25, 1), (42, 1), (45, 1), (54, 1)] }, { coefficient := 2, powers := [(0, 1), (13, 1), (26, 1), (31, 1), (42, 1), (50, 1), (53, 1)] }, { coefficient := 1, powers := [(0, 1), (13, 1), (30, 1), (49, 1), (58, 1)] }, { coefficient := -1, powers := [(0, 1), (19, 1), (25, 1), (42, 1), (45, 1), (55, 1)] }, { coefficient := 2, powers := [(0, 1), (19, 1), (26, 1), (34, 1), (38, 1), (42, 1), (49, 1), (58, 1), (62, 1)] }, { coefficient := 2, powers := [(0, 1), (19, 1), (26, 1), (34, 1), (38, 1), (47, 1), (49, 1), (58, 1), (62, 1)] }, { coefficient := 1, powers := [(0, 1), (19, 1), (30, 1), (43, 1), (58, 1)] }, { coefficient := 2, powers := [(0, 1), (20, 1), (25, 1), (26, 1), (42, 1), (53, 1), (55, 1)] }, { coefficient := 1, powers := [(0, 1), (20, 1), (26, 1), (31, 1), (42, 1), (43, 1), (53, 1)] }, { coefficient := -1, powers := [(0, 1), (20, 1), (26, 1), (31, 1), (43, 1), (53, 2)] }, { coefficient := 1, powers := [(0, 1), (20, 1), (30, 1), (43, 1), (54, 1)] }, { coefficient := 1, powers := [(0, 1), (42, 1)] }, { coefficient := 1, powers := [(5, 1), (26, 1), (27, 1), (34, 1), (42, 1), (45, 1), (53, 1)] }, { coefficient := 1, powers := [(5, 1), (26, 1), (27, 1), (34, 1), (48, 1), (53, 1)] }, { coefficient := -1, powers := [(5, 1), (26, 1), (34, 1), (42, 1), (45, 1), (54, 1)] }, { coefficient := -1, powers := [(5, 1), (26, 1), (34, 1), (48, 1), (54, 1)] }, { coefficient := -1, powers := [(13, 1), (25, 1), (26, 1), (27, 1), (42, 1), (45, 1), (53, 1)] }, { coefficient := -1, powers := [(13, 1), (25, 1), (26, 1), (27, 1), (48, 1), (53, 1)] }, { coefficient := 1, powers := [(13, 1), (25, 1), (26, 1), (42, 1), (45, 1), (54, 1)] }, { coefficient := 1, powers := [(13, 1), (25, 1), (26, 1), (48, 1), (54, 1)] }, { coefficient := 1, powers := [(13, 1), (25, 1), (45, 1), (54, 1)] }, { coefficient := 2, powers := [(13, 1), (26, 1), (31, 1), (50, 1), (53, 1)] }, { coefficient := -1, powers := [(19, 1), (25, 1), (45, 1), (55, 1)] }, { coefficient := 1, powers := [(19, 1), (30, 1), (43, 1), (58, 1), (64, 1)] }, { coefficient := 2, powers := [(20, 1), (25, 1), (26, 1), (53, 1), (55, 1)] }, { coefficient := -1, powers := [(20, 1), (26, 1), (31, 1), (43, 1), (53, 2), (64, 1)] }, { coefficient := 1, powers := [(20, 1), (26, 1), (31, 1), (43, 1), (53, 1)] }, { coefficient := 1, powers := [(20, 1), (30, 1), (43, 1), (54, 1), (64, 1)] }]
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
    (values : Fin 66 → R) :
    ¬ ∀ index : Fin 33,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component16.SelectedLeafB4_7.selectedHasNoCommonZero

end Krenn.Component16.SelectedLeafB4_7
