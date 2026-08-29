import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component24.SelectedLeafB7_0_0

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "c4590dd2d5ef6f87a7d1d2d21f624a29e4b707608faf76cbf0e126bad057a9e3"
def certificateSHA256 : String := "b21a3e8d1b221a9060525ca14a24e4970fbce9a4281f67689c7480ae3333c0e2"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 55 → Fin 673 := ![
  2,
  5,
  8,
  13,
  14,
  15,
  22,
  23,
  129,
  131,
  153,
  154,
  161,
  162,
  176,
  190,
  196,
  259,
  282,
  299,
  301,
  302,
  305,
  306,
  307,
  316,
  321,
  323,
  350,
  362,
  417,
  430,
  443,
  448,
  452,
  457,
  462,
  471,
  520,
  589,
  596,
  606,
  607,
  624,
  661,
  663,
  664,
  665,
  666,
  667,
  668,
  669,
  670,
  671,
  672
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 55 → SparsePoly (Fin 65) := ![
  [{ coefficient := 1, powers := [(8, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(31, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(31, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (55, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (35, 1)] }, { coefficient := 1, powers := [(18, 1), (21, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (20, 1)] }, { coefficient := 1, powers := [(18, 1), (26, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (45, 1)] }, { coefficient := 1, powers := [(19, 1), (20, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (45, 1)] }, { coefficient := 1, powers := [(29, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (54, 1)] }, { coefficient := -1, powers := [(30, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (31, 1), (60, 1)] }, { coefficient := 1, powers := [(31, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (35, 1), (52, 1)] }, { coefficient := 1, powers := [(5, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (24, 1), (60, 1)] }, { coefficient := 1, powers := [(18, 1), (31, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (26, 1), (46, 1)] }, { coefficient := 1, powers := [(18, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (26, 1), (49, 1)] }, { coefficient := 1, powers := [(19, 1), (21, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1)] }, { coefficient := 1, powers := [(20, 1), (45, 1)] }, { coefficient := 1, powers := [(26, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (51, 1)] }, { coefficient := 1, powers := [(20, 1), (51, 1)] }, { coefficient := 1, powers := [(26, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (44, 1)] }, { coefficient := 1, powers := [(11, 1), (22, 1), (56, 1)] }, { coefficient := 1, powers := [(11, 1), (27, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (44, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (56, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (59, 1)] }, { coefficient := 1, powers := [(9, 1), (56, 1)] }, { coefficient := 1, powers := [(15, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (61, 1)] }, { coefficient := 1, powers := [(14, 1), (58, 1)] }, { coefficient := 1, powers := [(19, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (46, 1)] }, { coefficient := 1, powers := [(14, 1), (57, 1)] }, { coefficient := 1, powers := [(18, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (42, 1)] }, { coefficient := 1, powers := [(19, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (58, 1)] }, { coefficient := 1, powers := [(31, 1), (49, 1)] }, { coefficient := 1, powers := [(37, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (40, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (59, 1)] }, { coefficient := 1, powers := [(8, 1), (25, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (31, 1), (59, 1)] }, { coefficient := 1, powers := [(9, 1), (31, 1), (44, 1)] }, { coefficient := 1, powers := [(15, 1), (31, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (20, 1), (57, 1)] }, { coefficient := 1, powers := [(14, 1)] }, { coefficient := 1, powers := [(18, 1), (20, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (26, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (26, 1), (42, 1)] }, { coefficient := 1, powers := [(19, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (54, 1)] }, { coefficient := 1, powers := [(20, 1), (51, 1), (57, 1)] }, { coefficient := 1, powers := [(20, 1), (54, 1)] }, { coefficient := 1, powers := [(51, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (45, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (45, 1)] }, { coefficient := 1, powers := [(18, 1), (37, 1), (38, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (49, 1)] }, { coefficient := 1, powers := [(5, 1), (37, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (49, 1)] }, { coefficient := 1, powers := [(19, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1)] }, { coefficient := 1, powers := [(14, 1), (31, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (61, 1)] }, { coefficient := 1, powers := [(14, 1), (49, 1)] }, { coefficient := 1, powers := [(19, 1), (21, 1), (54, 1)] }, { coefficient := 1, powers := [(19, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (55, 1)] }, { coefficient := 1, powers := [(31, 1), (43, 1)] }, { coefficient := 1, powers := [(31, 1), (48, 1), (51, 1)] }, { coefficient := 1, powers := [(34, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (34, 1), (57, 1)] }, { coefficient := 1, powers := [(24, 1), (51, 1), (57, 1)] }, { coefficient := 1, powers := [(24, 1), (54, 1)] }, { coefficient := 1, powers := [(30, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1), (56, 1)] }, { coefficient := 1, powers := [(6, 1), (35, 1), (42, 1)] }, { coefficient := 1, powers := [(15, 1), (26, 1), (42, 1)] }, { coefficient := 1, powers := [(15, 1)] }, { coefficient := 1, powers := [(56, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (41, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (44, 1), (50, 1)] }, { coefficient := 1, powers := [(13, 1), (24, 1), (56, 1)] }, { coefficient := 1, powers := [(13, 1), (29, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1)] }, { coefficient := 1, powers := [(3, 1), (35, 1)] }, { coefficient := 1, powers := [(15, 1), (20, 1)] }, { coefficient := 1, powers := [(20, 1), (56, 1)] }, { coefficient := 1, powers := [(26, 1), (44, 1)] }, { coefficient := 1, powers := [(35, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (50, 1)] }, { coefficient := 1, powers := [(6, 1), (32, 1)] }, { coefficient := 1, powers := [(9, 1), (26, 1)] }, { coefficient := 1, powers := [(20, 1), (50, 1)] }, { coefficient := 1, powers := [(26, 1), (41, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (45, 1), (51, 1)] }, { coefficient := 1, powers := [(14, 1), (29, 1), (45, 1)] }, { coefficient := 1, powers := [(14, 1), (37, 1), (38, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (51, 1)] }, { coefficient := 1, powers := [(19, 1), (34, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (38, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (41, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (44, 1), (50, 1)] }, { coefficient := 1, powers := [(3, 1), (26, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (32, 1), (56, 1)] }, { coefficient := 1, powers := [(3, 1), (35, 1), (50, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (32, 1), (44, 1)] }, { coefficient := 1, powers := [(6, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(9, 1), (20, 1), (56, 1)] }, { coefficient := 1, powers := [(9, 1), (26, 1), (44, 1)] }, { coefficient := 1, powers := [(9, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(15, 1), (20, 1), (50, 1)] }, { coefficient := 1, powers := [(15, 1), (26, 1), (41, 1)] }, { coefficient := 1, powers := [(15, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (40, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (43, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (49, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (37, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (25, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (49, 1)] }, { coefficient := 1, powers := [(8, 1), (37, 1), (43, 1)] }, { coefficient := 1, powers := [(14, 1), (25, 1), (58, 1)] }, { coefficient := 1, powers := [(14, 1), (31, 1), (49, 1)] }, { coefficient := 1, powers := [(14, 1), (37, 1), (40, 1)] }, { coefficient := 1, powers := [(19, 1), (25, 1), (55, 1)] }, { coefficient := 1, powers := [(19, 1), (31, 1), (43, 1)] }, { coefficient := 1, powers := [(19, 1), (34, 1), (40, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (64, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(41, 1)] }],
  [{ coefficient := 1, powers := [(42, 1)] }],
  [{ coefficient := 1, powers := [(43, 1)] }],
  [{ coefficient := 1, powers := [(56, 1)] }],
  [{ coefficient := 1, powers := [(57, 1)] }],
  [{ coefficient := 1, powers := [(58, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 55 → SparsePoly (Fin 65) := ![
  [{ coefficient := 1, powers := [(9, 1), (24, 1), (35, 1), (38, 1), (49, 1), (51, 1)] }, { coefficient := -1, powers := [(24, 1), (35, 1), (38, 1), (49, 1), (50, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (27, 1), (50, 1), (63, 1)] }, { coefficient := 1, powers := [(20, 1), (27, 1), (50, 1), (63, 1)] }, { coefficient := 1, powers := [(26, 1), (27, 1), (50, 1), (63, 1)] }, { coefficient := 1, powers := [(27, 1), (32, 1), (38, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (29, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (9, 1), (22, 1), (35, 1), (38, 1), (49, 1), (63, 1)] }, { coefficient := -1, powers := [(2, 1), (22, 1), (35, 1), (38, 1), (49, 1), (50, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (29, 1), (50, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (24, 1), (26, 1), (49, 1), (59, 1)] }, { coefficient := -1, powers := [(9, 1), (24, 1), (35, 1), (38, 1), (49, 1)] }, { coefficient := 1, powers := [(24, 1), (35, 1), (38, 1), (49, 1), (50, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (9, 1), (14, 1), (26, 1), (49, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (19, 1), (26, 1), (51, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (9, 1), (35, 1), (38, 1), (49, 1), (63, 1)] }, { coefficient := 1, powers := [(2, 1), (35, 1), (38, 1), (49, 1), (50, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (26, 1), (37, 1), (52, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(9, 1), (24, 1), (35, 1), (40, 1), (45, 1), (51, 1), (62, 1)] }, { coefficient := -1, powers := [(9, 1), (24, 1), (35, 1), (40, 1), (47, 1), (51, 1)] }, { coefficient := 1, powers := [(9, 1), (25, 1), (35, 1), (38, 1), (47, 1), (55, 1)] }, { coefficient := -1, powers := [(9, 1), (29, 1), (35, 1), (40, 1), (45, 1), (51, 1), (62, 1)] }, { coefficient := 1, powers := [(9, 1), (29, 1), (35, 1), (40, 1), (45, 1), (54, 1)] }, { coefficient := -1, powers := [(9, 1), (29, 1), (35, 1), (40, 1), (47, 1), (51, 1)] }, { coefficient := 1, powers := [(9, 1), (31, 1), (35, 1), (38, 1), (49, 1), (54, 1)] }, { coefficient := 1, powers := [(24, 1), (35, 1), (40, 1), (45, 1), (50, 1), (51, 1), (62, 1)] }, { coefficient := 1, powers := [(24, 1), (35, 1), (40, 1), (47, 1), (50, 1), (51, 1)] }, { coefficient := -1, powers := [(25, 1), (35, 1), (38, 1), (47, 1), (50, 1), (55, 1)] }, { coefficient := 1, powers := [(29, 1), (35, 1), (40, 1), (45, 1), (50, 1), (51, 1), (62, 1)] }, { coefficient := -1, powers := [(29, 1), (35, 1), (40, 1), (45, 1), (50, 1), (54, 1)] }, { coefficient := 1, powers := [(29, 1), (35, 1), (40, 1), (47, 1), (50, 1), (51, 1)] }, { coefficient := -1, powers := [(31, 1), (35, 1), (38, 1), (49, 1), (50, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(9, 1), (24, 1), (35, 1), (40, 1), (51, 1)] }, { coefficient := 1, powers := [(9, 1), (25, 1), (35, 1), (38, 1), (55, 1)] }, { coefficient := -1, powers := [(9, 1), (29, 1), (35, 1), (40, 1), (51, 1)] }, { coefficient := 1, powers := [(24, 1), (35, 1), (40, 1), (50, 1), (51, 1)] }, { coefficient := -1, powers := [(25, 1), (35, 1), (38, 1), (50, 1), (55, 1)] }, { coefficient := 1, powers := [(29, 1), (35, 1), (40, 1), (50, 1), (51, 1)] }],
  [{ coefficient := -1, powers := [(9, 1), (18, 1), (35, 1), (38, 1), (55, 1)] }, { coefficient := 1, powers := [(18, 1), (35, 1), (38, 1), (50, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (9, 1), (19, 1), (35, 1), (40, 1)] }, { coefficient := -1, powers := [(0, 1), (19, 1), (35, 1), (40, 1), (50, 1)] }, { coefficient := 1, powers := [(9, 1), (19, 1), (20, 1), (35, 1), (40, 1)] }, { coefficient := -1, powers := [(19, 1), (20, 1), (35, 1), (40, 1), (50, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (14, 1), (26, 1), (49, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (26, 1), (37, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(9, 1), (35, 1), (38, 1), (49, 1), (51, 1)] }, { coefficient := 1, powers := [(35, 1), (38, 1), (49, 1), (50, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (29, 1), (35, 1), (40, 1), (45, 1)] }, { coefficient := -1, powers := [(29, 1), (35, 1), (40, 1), (45, 1), (50, 1)] }],
  [{ coefficient := -1, powers := [(9, 1), (31, 1), (35, 1), (38, 1), (54, 1)] }, { coefficient := 1, powers := [(31, 1), (35, 1), (38, 1), (50, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (18, 1), (24, 1), (35, 1), (40, 1), (51, 1), (62, 1)] }, { coefficient := 2, powers := [(9, 1), (18, 1), (29, 1), (35, 1), (40, 1), (51, 1), (62, 1)] }, { coefficient := -1, powers := [(18, 1), (24, 1), (35, 1), (40, 1), (50, 1), (51, 1), (62, 1)] }, { coefficient := -2, powers := [(18, 1), (29, 1), (35, 1), (40, 1), (50, 1), (51, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(9, 1), (18, 1), (29, 1), (35, 1), (40, 1), (45, 1), (62, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (35, 1), (40, 1), (45, 1), (50, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (50, 1), (63, 1)] }, { coefficient := -1, powers := [(20, 1), (50, 1), (63, 1)] }, { coefficient := -1, powers := [(26, 1), (50, 1), (63, 1)] }, { coefficient := -1, powers := [(32, 1), (38, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (50, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(20, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (25, 1), (35, 1), (38, 1)] }, { coefficient := -1, powers := [(25, 1), (35, 1), (38, 1), (50, 1)] }],
  [{ coefficient := -1, powers := [(9, 1), (26, 1), (29, 1), (35, 1), (40, 1), (45, 1)] }, { coefficient := 1, powers := [(26, 1), (29, 1), (35, 1), (40, 1), (45, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (20, 1), (24, 1), (35, 1), (40, 1), (51, 1)] }, { coefficient := -1, powers := [(9, 1), (20, 1), (25, 1), (35, 1), (38, 1), (55, 1)] }, { coefficient := 1, powers := [(9, 1), (20, 1), (29, 1), (35, 1), (40, 1), (51, 1)] }, { coefficient := -1, powers := [(20, 1), (24, 1), (35, 1), (40, 1), (50, 1), (51, 1)] }, { coefficient := 1, powers := [(20, 1), (25, 1), (35, 1), (38, 1), (50, 1), (55, 1)] }, { coefficient := -1, powers := [(20, 1), (29, 1), (35, 1), (40, 1), (50, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (14, 1), (26, 1), (59, 1)] }, { coefficient := 1, powers := [(9, 1), (18, 1), (35, 1), (38, 1), (51, 1)] }, { coefficient := -1, powers := [(18, 1), (35, 1), (38, 1), (50, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (26, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (14, 1), (26, 1), (49, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(9, 1), (29, 1), (35, 1), (40, 1), (45, 1)] }, { coefficient := -1, powers := [(9, 1), (31, 1), (35, 1), (38, 1), (49, 1)] }, { coefficient := 1, powers := [(29, 1), (35, 1), (40, 1), (45, 1), (50, 1)] }, { coefficient := 1, powers := [(31, 1), (35, 1), (38, 1), (49, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (24, 1), (35, 1), (40, 1), (51, 1)] }, { coefficient := -1, powers := [(9, 1), (25, 1), (35, 1), (38, 1), (55, 1)] }, { coefficient := 1, powers := [(9, 1), (29, 1), (35, 1), (40, 1), (51, 1)] }, { coefficient := -1, powers := [(24, 1), (35, 1), (40, 1), (50, 1), (51, 1)] }, { coefficient := 1, powers := [(25, 1), (35, 1), (38, 1), (50, 1), (55, 1)] }, { coefficient := -1, powers := [(29, 1), (35, 1), (40, 1), (50, 1), (51, 1)] }],
  [{ coefficient := -1, powers := [(9, 1), (19, 1), (24, 1), (35, 1), (40, 1)] }, { coefficient := -1, powers := [(9, 1), (19, 1), (29, 1), (35, 1), (40, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (35, 1), (40, 1), (50, 1)] }, { coefficient := 1, powers := [(19, 1), (29, 1), (35, 1), (40, 1), (50, 1)] }],
  [{ coefficient := -1, powers := [(9, 1), (35, 1), (40, 1), (51, 1)] }, { coefficient := 1, powers := [(35, 1), (40, 1), (50, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (35, 1), (38, 1), (55, 1)] }, { coefficient := -1, powers := [(35, 1), (38, 1), (50, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (26, 1), (49, 1), (59, 1)] }, { coefficient := 1, powers := [(9, 1), (35, 1), (38, 1), (49, 1)] }, { coefficient := -1, powers := [(35, 1), (38, 1), (49, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (31, 1), (35, 1), (38, 1)] }, { coefficient := -1, powers := [(31, 1), (35, 1), (38, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (19, 1), (26, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (9, 1), (19, 1), (35, 1), (40, 1)] }, { coefficient := -1, powers := [(0, 1), (19, 1), (35, 1), (40, 1), (50, 1)] }, { coefficient := 1, powers := [(9, 1), (19, 1), (20, 1), (35, 1), (40, 1)] }, { coefficient := -1, powers := [(19, 1), (20, 1), (35, 1), (40, 1), (50, 1)] }],
  [{ coefficient := -1, powers := [(20, 1), (50, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(50, 1)] }],
  [{ coefficient := 1, powers := [(44, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (35, 1), (40, 1)] }, { coefficient := -1, powers := [(35, 1), (40, 1), (50, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(3, 1), (26, 1), (59, 1)] }, { coefficient := -1, powers := [(9, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(35, 1), (38, 1), (50, 1)] }],
  [{ coefficient := -1, powers := [(9, 1), (18, 1), (24, 1), (35, 1), (40, 1), (45, 1), (51, 1)] }, { coefficient := -1, powers := [(9, 1), (18, 1), (29, 1), (35, 1), (40, 1), (45, 1), (51, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (35, 1), (40, 1), (45, 1), (50, 1), (51, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (35, 1), (40, 1), (45, 1), (50, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1), (50, 1)] }, { coefficient := 1, powers := [(2, 1), (9, 1), (35, 1), (38, 1), (49, 1), (55, 1)] }, { coefficient := -1, powers := [(2, 1), (35, 1), (38, 1), (49, 1), (50, 1), (55, 1)] }, { coefficient := 1, powers := [(20, 1), (44, 1), (50, 1)] }, { coefficient := 1, powers := [(26, 1), (44, 1), (50, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1), (44, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (38, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (14, 1), (15, 1), (26, 1), (31, 1), (49, 1), (60, 1)] }, { coefficient := 1, powers := [(6, 1), (35, 1)] }, { coefficient := 1, powers := [(15, 1), (26, 1)] }, { coefficient := -1, powers := [(26, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (20, 1), (35, 1), (50, 1)] }, { coefficient := -1, powers := [(6, 1), (32, 1), (35, 1), (38, 1)] }, { coefficient := -1, powers := [(9, 1), (19, 1), (20, 1), (24, 1), (35, 1), (40, 1), (51, 1)] }, { coefficient := 1, powers := [(9, 1), (19, 1), (20, 1), (25, 1), (35, 1), (38, 1), (55, 1)] }, { coefficient := -1, powers := [(9, 1), (19, 1), (20, 1), (29, 1), (35, 1), (40, 1), (51, 1)] }, { coefficient := -1, powers := [(9, 1), (19, 1), (24, 1), (26, 1), (35, 1), (40, 1), (51, 1)] }, { coefficient := 1, powers := [(9, 1), (19, 1), (25, 1), (26, 1), (35, 1), (38, 1), (55, 1)] }, { coefficient := -1, powers := [(9, 1), (19, 1), (26, 1), (29, 1), (35, 1), (40, 1), (51, 1)] }, { coefficient := 1, powers := [(15, 1), (20, 1), (26, 1), (50, 1)] }, { coefficient := -1, powers := [(15, 1), (26, 1), (32, 1), (38, 1)] }, { coefficient := 1, powers := [(19, 1), (20, 1), (24, 1), (35, 1), (40, 1), (50, 1), (51, 1)] }, { coefficient := -1, powers := [(19, 1), (20, 1), (25, 1), (35, 1), (38, 1), (50, 1), (55, 1)] }, { coefficient := 1, powers := [(19, 1), (20, 1), (29, 1), (35, 1), (40, 1), (50, 1), (51, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (26, 1), (35, 1), (40, 1), (50, 1), (51, 1)] }, { coefficient := -1, powers := [(19, 1), (25, 1), (26, 1), (35, 1), (38, 1), (50, 1), (55, 1)] }, { coefficient := 1, powers := [(19, 1), (26, 1), (29, 1), (35, 1), (40, 1), (50, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (8, 1), (26, 1), (37, 1), (59, 1)] }, { coefficient := 1, powers := [(8, 1), (9, 1), (35, 1), (37, 1), (38, 1)] }, { coefficient := -1, powers := [(8, 1), (35, 1), (37, 1), (38, 1), (50, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (2, 1), (41, 1), (64, 1)] }, { coefficient := 1, powers := [(0, 1), (11, 1), (22, 1), (50, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (13, 1), (24, 1), (64, 1)] }, { coefficient := 1, powers := [(0, 1), (18, 1), (24, 1), (50, 1), (64, 1)] }, { coefficient := 1, powers := [(0, 1), (20, 1), (42, 1), (50, 1)] }, { coefficient := -1, powers := [(0, 1), (32, 1), (38, 1), (42, 1)] }, { coefficient := 1, powers := [(0, 1), (41, 1)] }, { coefficient := 1, powers := [(3, 1), (18, 1), (21, 1), (26, 1), (37, 1), (52, 1), (55, 1)] }, { coefficient := 1, powers := [(3, 1), (32, 1)] }, { coefficient := 1, powers := [(11, 1), (20, 1), (22, 1), (50, 1), (63, 1)] }, { coefficient := 1, powers := [(11, 1), (22, 1), (26, 1), (50, 1), (63, 1)] }, { coefficient := 1, powers := [(11, 1), (22, 1), (32, 1), (38, 1), (63, 1)] }, { coefficient := -1, powers := [(32, 1), (38, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (3, 1), (9, 1), (19, 1), (34, 1), (35, 1), (40, 1)] }, { coefficient := 1, powers := [(0, 1), (3, 1), (19, 1), (34, 1), (35, 1), (40, 1), (50, 1)] }, { coefficient := -1, powers := [(0, 1), (9, 1), (19, 1), (24, 1), (35, 1), (40, 1), (51, 1)] }, { coefficient := 1, powers := [(0, 1), (19, 1), (24, 1), (35, 1), (40, 1), (50, 1), (51, 1)] }, { coefficient := -1, powers := [(3, 1), (9, 1), (19, 1), (20, 1), (34, 1), (35, 1), (40, 1)] }, { coefficient := 1, powers := [(3, 1), (19, 1), (20, 1), (34, 1), (35, 1), (40, 1), (50, 1)] }, { coefficient := 1, powers := [(9, 1), (14, 1), (20, 1), (29, 1), (35, 1), (40, 1), (45, 1)] }, { coefficient := 1, powers := [(9, 1), (14, 1), (20, 1), (31, 1), (35, 1), (38, 1), (49, 1)] }, { coefficient := 1, powers := [(9, 1), (14, 1), (26, 1), (29, 1), (35, 1), (40, 1), (45, 1)] }, { coefficient := 1, powers := [(9, 1), (19, 1), (20, 1), (29, 1), (35, 1), (40, 1), (51, 1)] }, { coefficient := -1, powers := [(14, 1), (20, 1), (29, 1), (35, 1), (40, 1), (45, 1), (50, 1)] }, { coefficient := -1, powers := [(14, 1), (20, 1), (31, 1), (35, 1), (38, 1), (49, 1), (50, 1)] }, { coefficient := -1, powers := [(14, 1), (26, 1), (29, 1), (35, 1), (40, 1), (45, 1), (50, 1)] }, { coefficient := -1, powers := [(19, 1), (20, 1), (29, 1), (35, 1), (40, 1), (50, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (3, 1), (26, 1), (43, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (9, 1), (35, 1), (38, 1), (43, 1)] }, { coefficient := -1, powers := [(2, 1), (35, 1), (38, 1), (43, 1), (50, 1)] }, { coefficient := 1, powers := [(3, 1), (5, 1), (26, 1), (34, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (9, 1), (34, 1), (35, 1), (38, 1)] }, { coefficient := -1, powers := [(5, 1), (34, 1), (35, 1), (38, 1), (50, 1)] }, { coefficient := -1, powers := [(9, 1), (18, 1), (25, 1), (35, 1), (38, 1), (51, 1)] }, { coefficient := 1, powers := [(18, 1), (25, 1), (35, 1), (38, 1), (50, 1), (51, 1)] }]
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
    ¬ ∀ index : Fin 55,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component24.SelectedLeafB7_0_0.selectedHasNoCommonZero

end Krenn.Component24.SelectedLeafB7_0_0
