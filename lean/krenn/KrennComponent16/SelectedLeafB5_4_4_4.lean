import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component16.SelectedLeafB5_4_4_4

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "55284e59595c252edecb407c0edde891c6a90517e141038e644ddae2c5fb7008"
def certificateSHA256 : String := "e51bb01e8b3da7c80f169978d5138be491061abce6212b10d275f9afa0728c07"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 40 → Fin 674 := ![
  6,
  9,
  12,
  13,
  23,
  31,
  142,
  170,
  171,
  302,
  316,
  366,
  407,
  433,
  435,
  438,
  440,
  448,
  454,
  455,
  478,
  481,
  503,
  571,
  572,
  584,
  585,
  610,
  620,
  649,
  653,
  661,
  662,
  664,
  666,
  667,
  669,
  670,
  671,
  673
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 40 → SparsePoly (Fin 67) := ![
  [{ coefficient := 1, powers := [(6, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (26, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(30, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (55, 1)] }, { coefficient := 1, powers := [(21, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (45, 1)] }, { coefficient := 1, powers := [(29, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (54, 1)] }, { coefficient := 1, powers := [(31, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (61, 1)] }, { coefficient := 1, powers := [(13, 1), (50, 1)] }, { coefficient := 1, powers := [(20, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (55, 1)] }, { coefficient := 1, powers := [(31, 1), (43, 1)] }, { coefficient := 1, powers := [(34, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (25, 1), (60, 1)] }, { coefficient := 1, powers := [(25, 1)] }, { coefficient := 1, powers := [(29, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (26, 1), (42, 1)] }, { coefficient := 1, powers := [(19, 1), (26, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (29, 1), (42, 1)] }, { coefficient := 1, powers := [(19, 1), (29, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (30, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (49, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (60, 1)] }, { coefficient := 1, powers := [(19, 1), (25, 1)] }, { coefficient := 1, powers := [(19, 1), (29, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (53, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (53, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (57, 1)] }, { coefficient := 1, powers := [(19, 1), (30, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1)] }, { coefficient := 1, powers := [(13, 1), (31, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (61, 1)] }, { coefficient := 1, powers := [(13, 1), (27, 1), (48, 1)] }, { coefficient := 1, powers := [(13, 1), (58, 1)] }, { coefficient := 1, powers := [(20, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (42, 1)] }, { coefficient := 1, powers := [(19, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (53, 1)] }, { coefficient := 1, powers := [(19, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(30, 1), (42, 1)] }, { coefficient := 1, powers := [(30, 1), (47, 1)] }, { coefficient := 1, powers := [(30, 1), (53, 1)] }, { coefficient := 1, powers := [(30, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1)] }, { coefficient := 1, powers := [(19, 1), (29, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (39, 1), (61, 1)] }, { coefficient := 1, powers := [(13, 1), (30, 1), (48, 1)] }, { coefficient := 1, powers := [(13, 1), (37, 1), (39, 1)] }, { coefficient := 1, powers := [(20, 1), (34, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (31, 1), (61, 1)] }, { coefficient := 1, powers := [(3, 1), (34, 1), (58, 1)] }, { coefficient := 1, powers := [(3, 1), (37, 1), (55, 1)] }, { coefficient := 1, powers := [(24, 1), (45, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (45, 1), (54, 1)] }, { coefficient := 1, powers := [(25, 1), (58, 1)] }, { coefficient := 1, powers := [(31, 1), (50, 1)] }, { coefficient := 1, powers := [(37, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(30, 1), (42, 1), (45, 1)] }, { coefficient := 1, powers := [(30, 1), (45, 1), (53, 1)] }, { coefficient := 1, powers := [(30, 1), (48, 1)] }, { coefficient := 1, powers := [(37, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1)] }, { coefficient := 1, powers := [(6, 1), (60, 1)] }, { coefficient := 1, powers := [(26, 1), (42, 1)] }, { coefficient := 1, powers := [(26, 1), (47, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (53, 1)] }, { coefficient := 1, powers := [(3, 1), (60, 1)] }, { coefficient := 1, powers := [(21, 1), (53, 1)] }, { coefficient := 1, powers := [(21, 1), (57, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (38, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1)] }, { coefficient := 1, powers := [(3, 1), (26, 1), (60, 1)] }, { coefficient := 1, powers := [(6, 1), (21, 1), (60, 1)] }, { coefficient := 1, powers := [(21, 1)] }, { coefficient := 1, powers := [(26, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (40, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (49, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (25, 1), (60, 1)] }, { coefficient := 1, powers := [(19, 1), (25, 1), (54, 1)] }, { coefficient := 1, powers := [(19, 1), (31, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (39, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (42, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (47, 1), (53, 1)] }, { coefficient := 1, powers := [(42, 1)] }, { coefficient := 1, powers := [(47, 1)] }, { coefficient := 1, powers := [(53, 1)] }, { coefficient := 1, powers := [(57, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (39, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (42, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (47, 1), (53, 1)] }, { coefficient := 1, powers := [(19, 1), (30, 1), (42, 1)] }, { coefficient := 1, powers := [(19, 1), (30, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (30, 1), (53, 1)] }, { coefficient := 1, powers := [(19, 1), (30, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (40, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (43, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (50, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (37, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (25, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (50, 1)] }, { coefficient := 1, powers := [(8, 1), (37, 1), (43, 1)] }, { coefficient := 1, powers := [(13, 1), (25, 1), (58, 1)] }, { coefficient := 1, powers := [(13, 1), (31, 1), (50, 1)] }, { coefficient := 1, powers := [(13, 1), (37, 1), (40, 1)] }, { coefficient := 1, powers := [(20, 1), (25, 1), (55, 1)] }, { coefficient := 1, powers := [(20, 1), (31, 1), (43, 1)] }, { coefficient := 1, powers := [(20, 1), (34, 1), (40, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(42, 1)] }],
  [{ coefficient := 1, powers := [(43, 1)] }],
  [{ coefficient := 1, powers := [(57, 1)] }],
  [{ coefficient := 1, powers := [(58, 1)] }],
  [{ coefficient := 1, powers := [(26, 1), (66, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(31, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 40 → SparsePoly (Fin 67) := ![
  [{ coefficient := 2, powers := [(3, 1), (19, 1), (25, 1), (54, 1), (60, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (26, 1), (37, 1), (39, 1), (40, 1), (60, 1), (66, 1)] }, { coefficient := -2, powers := [(26, 2), (37, 1), (39, 1), (40, 1), (60, 1), (66, 1)] }],
  [{ coefficient := -2, powers := [(3, 1), (25, 1), (54, 1), (60, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (25, 1), (26, 1), (27, 1), (39, 1), (60, 1)] }, { coefficient := 2, powers := [(0, 1), (26, 1), (30, 1), (40, 1), (60, 1)] }, { coefficient := -2, powers := [(25, 1), (26, 2), (27, 1), (39, 1), (60, 1)] }, { coefficient := -2, powers := [(26, 2), (30, 1), (40, 1), (60, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (19, 1), (26, 1), (39, 1), (50, 1), (60, 1)] }, { coefficient := -2, powers := [(3, 1), (5, 1), (45, 1), (60, 2)] }, { coefficient := 2, powers := [(3, 1), (19, 1), (50, 1), (60, 1)] }, { coefficient := -2, powers := [(19, 1), (26, 2), (39, 1), (50, 1), (60, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (5, 1), (26, 1), (45, 1), (53, 1), (60, 1)] }, { coefficient := 2, powers := [(0, 1), (5, 1), (26, 1), (48, 1), (60, 1)] }, { coefficient := -2, powers := [(5, 1), (26, 2), (45, 1), (53, 1), (60, 1)] }, { coefficient := -2, powers := [(5, 1), (26, 2), (48, 1), (60, 1)] }],
  [{ coefficient := 2, powers := [(3, 1), (5, 1), (37, 1), (53, 1), (60, 1)] }],
  [{ coefficient := 2, powers := [(3, 1), (13, 1), (54, 1), (60, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (13, 1), (26, 1), (39, 1), (45, 1), (60, 1)] }, { coefficient := 2, powers := [(3, 1), (13, 1), (45, 1), (60, 1)] }, { coefficient := 2, powers := [(3, 1), (19, 1), (61, 1)] }, { coefficient := -2, powers := [(13, 1), (26, 2), (39, 1), (45, 1), (60, 1)] }],
  [{ coefficient := -2, powers := [(3, 1), (29, 1), (54, 1), (60, 1)] }],
  [{ coefficient := -2, powers := [(3, 1), (20, 1), (60, 1)] }],
  [{ coefficient := -2, powers := [(3, 1), (19, 1), (54, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (24, 1), (53, 1), (63, 1)] }, { coefficient := 1, powers := [(0, 1), (29, 1), (53, 1), (63, 1)] }, { coefficient := -1, powers := [(24, 1), (26, 1), (53, 1), (63, 1)] }, { coefficient := -2, powers := [(24, 1), (63, 1)] }, { coefficient := -1, powers := [(26, 1), (29, 1), (53, 1), (63, 1)] }, { coefficient := -2, powers := [(29, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (26, 1), (53, 1), (63, 1)] }, { coefficient := 1, powers := [(0, 1), (63, 1)] }, { coefficient := 1, powers := [(26, 2), (53, 1), (63, 1)] }, { coefficient := 1, powers := [(26, 1), (63, 1)] }],
  [{ coefficient := 2, powers := [(3, 1), (54, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (26, 1), (53, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (63, 1)] }, { coefficient := -1, powers := [(26, 2), (53, 1), (63, 1)] }, { coefficient := -1, powers := [(26, 1), (63, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (26, 1), (39, 1), (50, 1), (60, 1)] }, { coefficient := -2, powers := [(3, 1), (50, 1), (60, 1)] }, { coefficient := 2, powers := [(26, 2), (39, 1), (50, 1), (60, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (25, 1), (26, 1), (39, 1), (60, 1)] }, { coefficient := 2, powers := [(25, 1), (26, 2), (39, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (24, 1), (26, 1), (53, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (29, 1), (63, 1)] }, { coefficient := 1, powers := [(24, 1), (26, 2), (53, 1), (63, 1)] }, { coefficient := 2, powers := [(24, 1), (26, 1), (63, 1)] }, { coefficient := 1, powers := [(26, 1), (29, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(0, 2), (19, 1), (26, 1), (53, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 2), (19, 1), (63, 1)] }, { coefficient := -2, powers := [(0, 1), (19, 1), (21, 1), (63, 1)] }, { coefficient := 1, powers := [(0, 1), (19, 1), (26, 2), (53, 1), (63, 1)] }, { coefficient := -3, powers := [(0, 1), (19, 1), (26, 1), (63, 1)] }, { coefficient := -2, powers := [(19, 1), (21, 1), (26, 1), (63, 1)] }, { coefficient := 2, powers := [(19, 1), (26, 2), (63, 1)] }],
  [{ coefficient := 2, powers := [(63, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (26, 1), (40, 1), (60, 1)] }, { coefficient := 2, powers := [(26, 2), (40, 1), (60, 1)] }],
  [{ coefficient := 2, powers := [(3, 1), (5, 1), (60, 2)] }],
  [{ coefficient := -2, powers := [(0, 1), (13, 1), (26, 1), (39, 1), (60, 1)] }, { coefficient := -2, powers := [(3, 1), (13, 1), (60, 1)] }, { coefficient := 2, powers := [(13, 1), (26, 2), (39, 1), (60, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (5, 1), (26, 1), (55, 1), (60, 1)] }, { coefficient := 2, powers := [(5, 1), (26, 2), (55, 1), (60, 1)] }],
  [{ coefficient := 2, powers := [(21, 1), (62, 1)] }],
  [{ coefficient := -2, powers := [(3, 1), (5, 1), (37, 1), (55, 1), (60, 1)] }, { coefficient := 2, powers := [(26, 1), (62, 1)] }, { coefficient := 2, powers := [] }],
  [{ coefficient := -2, powers := [(62, 1)] }],
  [{ coefficient := -2, powers := [(3, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (2, 1), (26, 1), (53, 1), (63, 1)] }, { coefficient := -2, powers := [(0, 1), (26, 1), (53, 1)] }, { coefficient := -1, powers := [(0, 1)] }, { coefficient := -1, powers := [(2, 1), (26, 2), (53, 1), (63, 1)] }, { coefficient := -2, powers := [(2, 1), (26, 1), (63, 1)] }, { coefficient := -2, powers := [(21, 1), (26, 1), (62, 1)] }, { coefficient := -2, powers := [(21, 1)] }, { coefficient := 2, powers := [(26, 2), (53, 1)] }, { coefficient := 1, powers := [(26, 1)] }],
  [{ coefficient := 1, powers := [(0, 2), (26, 1), (53, 1), (63, 1)] }, { coefficient := 1, powers := [(0, 2), (63, 1)] }, { coefficient := 2, powers := [(0, 1), (21, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (26, 2), (53, 1), (63, 1)] }, { coefficient := 3, powers := [(0, 1), (26, 1), (63, 1)] }, { coefficient := 2, powers := [(21, 1), (26, 1), (63, 1)] }, { coefficient := -2, powers := [(26, 2), (63, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (26, 1), (39, 1), (60, 1)] }, { coefficient := 2, powers := [(3, 1), (60, 1)] }, { coefficient := -2, powers := [(26, 2), (39, 1), (60, 1)] }],
  [{ coefficient := 2, powers := [(21, 1), (26, 1), (39, 1), (60, 1)] }, { coefficient := 2, powers := [(21, 1), (26, 1), (47, 1), (53, 1)] }, { coefficient := -2, powers := [(21, 1), (47, 1)] }, { coefficient := -2, powers := [(26, 1), (53, 1)] }, { coefficient := 2, powers := [(38, 1), (60, 1)] }, { coefficient := 2, powers := [] }],
  [{ coefficient := -2, powers := [(0, 2), (26, 1), (39, 1), (53, 1), (60, 1)] }, { coefficient := -2, powers := [(0, 2), (26, 1), (47, 1), (53, 2)] }, { coefficient := -1, powers := [(0, 2), (39, 1), (60, 1)] }, { coefficient := -1, powers := [(0, 2), (47, 1), (53, 1)] }, { coefficient := -2, powers := [(0, 1), (21, 1), (39, 1), (60, 1)] }, { coefficient := -2, powers := [(0, 1), (21, 1), (47, 1), (53, 1)] }, { coefficient := 2, powers := [(0, 1), (26, 2), (39, 1), (53, 1), (60, 1)] }, { coefficient := 2, powers := [(0, 1), (26, 2), (47, 1), (53, 2)] }, { coefficient := -1, powers := [(0, 1), (26, 1), (39, 1), (60, 1)] }, { coefficient := -1, powers := [(0, 1), (26, 1), (47, 1), (53, 1)] }, { coefficient := -2, powers := [(0, 1), (26, 1), (53, 2)] }, { coefficient := -1, powers := [(0, 1), (47, 1)] }, { coefficient := 1, powers := [(0, 1), (53, 1)] }, { coefficient := -2, powers := [(21, 1), (26, 1), (39, 1), (60, 1)] }, { coefficient := -2, powers := [(21, 1), (26, 1), (47, 1), (53, 1)] }, { coefficient := 2, powers := [(26, 2), (39, 1), (60, 1)] }, { coefficient := 2, powers := [(26, 2), (47, 1), (53, 1)] }, { coefficient := 2, powers := [(26, 2), (53, 2)] }, { coefficient := 1, powers := [(26, 1), (47, 1)] }, { coefficient := 3, powers := [(26, 1), (53, 1)] }, { coefficient := -2, powers := [(38, 1), (60, 1)] }, { coefficient := -2, powers := [] }],
  [{ coefficient := -2, powers := [(0, 2), (2, 1), (26, 1), (53, 1), (57, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 2), (2, 1), (57, 1), (63, 1)] }, { coefficient := 2, powers := [(0, 2), (26, 1), (53, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 2), (57, 1)] }, { coefficient := -2, powers := [(0, 1), (2, 1), (21, 1), (57, 1), (63, 1)] }, { coefficient := 2, powers := [(0, 1), (2, 1), (26, 2), (53, 1), (57, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (2, 1), (26, 1), (53, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (2, 1), (26, 1), (57, 1), (63, 1)] }, { coefficient := 2, powers := [(0, 1), (5, 1), (26, 1), (30, 1), (45, 1), (55, 1), (60, 1)] }, { coefficient := 2, powers := [(0, 1), (21, 1), (26, 1), (57, 1), (62, 1)] }, { coefficient := 2, powers := [(0, 1), (21, 1), (57, 1)] }, { coefficient := -2, powers := [(0, 1), (26, 2), (53, 1), (57, 1)] }, { coefficient := 2, powers := [(0, 1), (26, 1), (53, 1)] }, { coefficient := -1, powers := [(0, 1), (26, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1)] }, { coefficient := -2, powers := [(2, 1), (21, 1), (26, 1), (57, 1), (63, 1)] }, { coefficient := 1, powers := [(2, 1), (26, 2), (53, 1), (63, 1)] }, { coefficient := 2, powers := [(2, 1), (26, 2), (57, 1), (63, 1)] }, { coefficient := 2, powers := [(2, 1), (26, 1), (63, 1)] }, { coefficient := -2, powers := [(5, 1), (26, 2), (30, 1), (45, 1), (55, 1), (60, 1)] }, { coefficient := 2, powers := [(21, 1)] }, { coefficient := -2, powers := [(26, 2), (53, 1)] }, { coefficient := -1, powers := [(26, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (2, 1), (26, 1), (39, 1), (58, 1), (60, 1)] }, { coefficient := -2, powers := [(0, 1), (8, 1), (26, 1), (37, 1), (39, 1), (60, 1)] }, { coefficient := -2, powers := [(2, 1), (3, 1), (58, 1), (60, 1)] }, { coefficient := 2, powers := [(2, 1), (26, 2), (39, 1), (58, 1), (60, 1)] }, { coefficient := -2, powers := [(3, 1), (8, 1), (37, 1), (60, 1)] }, { coefficient := 2, powers := [(3, 1), (20, 1), (29, 1), (54, 1), (60, 1)] }, { coefficient := 2, powers := [(8, 1), (26, 2), (37, 1), (39, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (2, 1), (26, 1), (53, 1), (63, 1)] }, { coefficient := 1, powers := [(0, 1), (19, 1), (24, 1), (63, 1)] }, { coefficient := 1, powers := [(0, 1), (19, 1), (29, 1), (63, 1)] }, { coefficient := 2, powers := [(0, 1), (26, 1), (53, 1)] }, { coefficient := 1, powers := [(0, 1)] }, { coefficient := 1, powers := [(2, 1), (26, 2), (53, 1), (63, 1)] }, { coefficient := 2, powers := [(2, 1), (26, 1), (63, 1)] }, { coefficient := 2, powers := [(3, 1), (5, 1), (21, 1), (37, 1), (55, 1), (60, 1)] }, { coefficient := -1, powers := [(19, 1), (24, 1), (26, 1), (63, 1)] }, { coefficient := -1, powers := [(19, 1), (26, 1), (29, 1), (63, 1)] }, { coefficient := -2, powers := [(26, 2), (53, 1)] }, { coefficient := -1, powers := [(26, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (5, 1), (26, 1), (34, 1), (39, 1), (60, 1)] }, { coefficient := 2, powers := [(0, 1), (13, 1), (25, 1), (26, 1), (39, 1), (60, 1)] }, { coefficient := -2, powers := [(3, 2), (5, 1), (34, 1), (60, 2)] }, { coefficient := -2, powers := [(3, 1), (5, 1), (34, 1), (60, 1)] }, { coefficient := 2, powers := [(5, 1), (26, 2), (34, 1), (39, 1), (60, 1)] }, { coefficient := -2, powers := [(13, 1), (25, 1), (26, 2), (39, 1), (60, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (13, 1), (26, 1), (37, 1), (39, 1), (40, 1), (60, 1)] }, { coefficient := 2, powers := [(13, 1), (26, 2), (37, 1), (39, 1), (40, 1), (60, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (5, 1), (26, 1), (39, 1), (60, 1), (61, 1)] }, { coefficient := -2, powers := [(0, 1), (13, 1), (26, 1), (39, 1), (45, 1), (49, 1), (60, 1)] }, { coefficient := 2, powers := [(0, 1), (13, 1), (26, 1), (39, 1), (50, 1), (60, 1)] }, { coefficient := -2, powers := [(0, 1), (20, 1), (26, 1), (39, 1), (43, 1), (60, 1)] }, { coefficient := -2, powers := [(3, 2), (5, 1), (60, 2), (61, 1)] }, { coefficient := -2, powers := [(3, 1), (13, 1), (45, 1), (49, 1), (60, 1)] }, { coefficient := 2, powers := [(3, 1), (13, 1), (50, 1), (60, 1)] }, { coefficient := 2, powers := [(5, 1), (26, 2), (39, 1), (60, 1), (61, 1)] }, { coefficient := 2, powers := [(13, 1), (26, 2), (39, 1), (45, 1), (49, 1), (60, 1)] }, { coefficient := -2, powers := [(13, 1), (26, 2), (39, 1), (50, 1), (60, 1)] }, { coefficient := 2, powers := [(20, 1), (26, 2), (39, 1), (43, 1), (60, 1)] }]
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
    ¬ ∀ index : Fin 40,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((2 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (2 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (2 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component16.SelectedLeafB5_4_4_4.selectedHasNoCommonZero

end Krenn.Component16.SelectedLeafB5_4_4_4
