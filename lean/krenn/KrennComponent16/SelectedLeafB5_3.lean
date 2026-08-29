import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component16.SelectedLeafB5_3

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "939ffe326df1a5607d94c3616e8b565c8d63550e2fa96ffdf9ab692d0eacff99"
def certificateSHA256 : String := "49a16d0bc31f77b33a4700397d37c7607cc3b6e8be28bd9e185ae4a9e1182bbf"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 50 → Fin 668 := ![
  6,
  7,
  13,
  15,
  23,
  24,
  25,
  30,
  32,
  33,
  50,
  147,
  162,
  170,
  173,
  247,
  299,
  300,
  301,
  302,
  314,
  316,
  325,
  327,
  355,
  407,
  408,
  428,
  436,
  440,
  448,
  468,
  478,
  481,
  523,
  571,
  572,
  584,
  585,
  608,
  609,
  610,
  654,
  660,
  661,
  662,
  663,
  664,
  666,
  667
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 50 → SparsePoly (Fin 66) := ![
  [{ coefficient := 1, powers := [(6, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (34, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(26, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(28, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(30, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(34, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(43, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (34, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (61, 1)] }, { coefficient := 1, powers := [(7, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (47, 1)] }, { coefficient := 1, powers := [(13, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (45, 1)] }, { coefficient := 1, powers := [(29, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1), (57, 1)] }, { coefficient := 1, powers := [(43, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (21, 1), (57, 1)] }, { coefficient := 1, powers := [(13, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (50, 1)] }, { coefficient := 1, powers := [(22, 1), (45, 1)] }, { coefficient := 1, powers := [(26, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (47, 1)] }, { coefficient := 1, powers := [(4, 1), (36, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (53, 1)] }, { coefficient := 1, powers := [(7, 1), (33, 1)] }, { coefficient := 1, powers := [(11, 1), (28, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (61, 1)] }, { coefficient := 1, powers := [(13, 1), (50, 1)] }, { coefficient := 1, powers := [(20, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (48, 1)] }, { coefficient := 1, powers := [(20, 1), (42, 1)] }, { coefficient := 1, powers := [(20, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (55, 1)] }, { coefficient := 1, powers := [(31, 1), (43, 1)] }, { coefficient := 1, powers := [(34, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (50, 1), (53, 1)] }, { coefficient := 1, powers := [(22, 1), (45, 1), (53, 1)] }, { coefficient := 1, powers := [(50, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (39, 1), (61, 1)] }, { coefficient := 1, powers := [(4, 1), (28, 1), (61, 1)] }, { coefficient := 1, powers := [(7, 1), (23, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (34, 1), (57, 1)] }, { coefficient := 1, powers := [(7, 1), (34, 1), (47, 1)] }, { coefficient := 1, powers := [(16, 1), (34, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (26, 1), (42, 1)] }, { coefficient := 1, powers := [(19, 1), (26, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (26, 1), (48, 1)] }, { coefficient := 1, powers := [(20, 1), (26, 1), (42, 1)] }, { coefficient := 1, powers := [(20, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (48, 1)] }, { coefficient := 1, powers := [(26, 1), (42, 1), (45, 1)] }, { coefficient := 1, powers := [(26, 1), (48, 1)] }, { coefficient := 1, powers := [(45, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (50, 1)] }, { coefficient := 1, powers := [(5, 1), (37, 1)] }, { coefficient := 1, powers := [(19, 1), (29, 1), (50, 1)] }, { coefficient := 1, powers := [(20, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1)] }, { coefficient := 1, powers := [(13, 1), (31, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (61, 1)] }, { coefficient := 1, powers := [(13, 1), (27, 1), (48, 1)] }, { coefficient := 1, powers := [(13, 1), (58, 1)] }, { coefficient := 1, powers := [(20, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (48, 1), (53, 1)] }, { coefficient := 1, powers := [(42, 1), (45, 1)] }, { coefficient := 1, powers := [(45, 1), (53, 1)] }, { coefficient := 1, powers := [(48, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1)] }, { coefficient := 1, powers := [(19, 1), (29, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (39, 1), (61, 1)] }, { coefficient := 1, powers := [(13, 1), (30, 1), (48, 1)] }, { coefficient := 1, powers := [(13, 1), (37, 1), (39, 1)] }, { coefficient := 1, powers := [(20, 1), (34, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (23, 1), (60, 1)] }, { coefficient := 1, powers := [(6, 1), (33, 1), (47, 1)] }, { coefficient := 1, powers := [(6, 1), (36, 1), (42, 1)] }, { coefficient := 1, powers := [(23, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (45, 1), (54, 1)] }, { coefficient := 1, powers := [(25, 1), (58, 1)] }, { coefficient := 1, powers := [(31, 1), (50, 1)] }, { coefficient := 1, powers := [(37, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(30, 1), (42, 1), (45, 1)] }, { coefficient := 1, powers := [(30, 1), (45, 1), (53, 1)] }, { coefficient := 1, powers := [(30, 1), (48, 1)] }, { coefficient := 1, powers := [(37, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1)] }, { coefficient := 1, powers := [(6, 1), (60, 1)] }, { coefficient := 1, powers := [(26, 1), (42, 1)] }, { coefficient := 1, powers := [(26, 1), (47, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (53, 1)] }, { coefficient := 1, powers := [(3, 1), (60, 1)] }, { coefficient := 1, powers := [(21, 1), (53, 1)] }, { coefficient := 1, powers := [(21, 1), (57, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(4, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (60, 1)] }, { coefficient := 1, powers := [(11, 1), (47, 1)] }, { coefficient := 1, powers := [(11, 1), (57, 1)] }, { coefficient := 1, powers := [(16, 1), (42, 1)] }, { coefficient := 1, powers := [(16, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (53, 1)] }, { coefficient := 1, powers := [(23, 1), (57, 1)] }, { coefficient := 1, powers := [(28, 1), (42, 1)] }, { coefficient := 1, powers := [(28, 1), (47, 1)] }, { coefficient := 1, powers := [(33, 1), (39, 1)] }, { coefficient := 1, powers := [(36, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (38, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1)] }, { coefficient := 1, powers := [(3, 1), (26, 1), (60, 1)] }, { coefficient := 1, powers := [(6, 1), (21, 1), (60, 1)] }, { coefficient := 1, powers := [(21, 1)] }, { coefficient := 1, powers := [(26, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (42, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (48, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (37, 1), (42, 1)] }, { coefficient := 1, powers := [(19, 1), (30, 1), (58, 1)] }, { coefficient := 1, powers := [(19, 1), (31, 1), (48, 1)] }, { coefficient := 1, powers := [(20, 1), (30, 1), (54, 1)] }, { coefficient := 1, powers := [(20, 1), (31, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (39, 1), (60, 1)] }, { coefficient := 1, powers := [(1, 1), (42, 1), (57, 1)] }, { coefficient := 1, powers := [(1, 1), (47, 1), (53, 1)] }, { coefficient := 1, powers := [(4, 1), (28, 1), (60, 1)] }, { coefficient := 1, powers := [(4, 1), (33, 1), (57, 1)] }, { coefficient := 1, powers := [(4, 1), (36, 1), (53, 1)] }, { coefficient := 1, powers := [(7, 1), (23, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (33, 1), (47, 1)] }, { coefficient := 1, powers := [(7, 1), (36, 1), (42, 1)] }, { coefficient := 1, powers := [(11, 1), (23, 1), (57, 1)] }, { coefficient := 1, powers := [(11, 1), (28, 1), (47, 1)] }, { coefficient := 1, powers := [(11, 1), (36, 1), (39, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1), (53, 1)] }, { coefficient := 1, powers := [(16, 1), (28, 1), (42, 1)] }, { coefficient := 1, powers := [(16, 1), (33, 1), (39, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (40, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (43, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (50, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (37, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (25, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (50, 1)] }, { coefficient := 1, powers := [(8, 1), (37, 1), (43, 1)] }, { coefficient := 1, powers := [(13, 1), (25, 1), (58, 1)] }, { coefficient := 1, powers := [(13, 1), (31, 1), (50, 1)] }, { coefficient := 1, powers := [(13, 1), (37, 1), (40, 1)] }, { coefficient := 1, powers := [(20, 1), (25, 1), (55, 1)] }, { coefficient := 1, powers := [(20, 1), (31, 1), (43, 1)] }, { coefficient := 1, powers := [(20, 1), (34, 1), (40, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(42, 1), (64, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(43, 1), (65, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 50 → SparsePoly (Fin 66) := ![
  [{ coefficient := 2, powers := [(2, 1), (11, 1), (23, 1), (40, 1), (53, 1), (60, 1)] }, { coefficient := 2, powers := [(2, 1), (11, 1), (33, 1), (40, 1), (47, 1), (53, 1)] }, { coefficient := 2, powers := [(2, 1), (11, 1), (36, 1), (40, 1), (42, 1), (53, 1)] }],
  [{ coefficient := 2, powers := [(5, 1), (23, 1), (58, 1), (60, 1)] }, { coefficient := -2, powers := [(5, 1), (33, 1), (47, 1), (58, 1)] }, { coefficient := 2, powers := [(5, 1), (36, 1), (42, 1), (58, 1)] }],
  [{ coefficient := 2, powers := [(2, 1), (11, 1), (30, 1), (33, 1), (40, 1), (63, 1)] }, { coefficient := -2, powers := [(25, 1), (27, 1)] }],
  [{ coefficient := 2, powers := [(2, 1), (23, 1), (40, 1), (42, 1), (61, 1), (65, 1)] }, { coefficient := 2, powers := [(2, 1), (33, 1), (39, 1), (40, 1), (61, 1), (65, 1)] }, { coefficient := 2, powers := [(5, 1), (33, 1), (34, 1), (39, 1), (58, 1), (65, 1)] }],
  [{ coefficient := -2, powers := [(19, 1), (50, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (13, 1), (25, 1), (53, 1), (58, 1), (62, 1), (65, 1)] }, { coefficient := -2, powers := [(2, 1), (43, 1), (48, 1), (53, 1), (54, 1), (64, 1), (65, 1)] }, { coefficient := -2, powers := [(2, 1), (50, 1), (53, 1), (55, 1), (65, 1)] }, { coefficient := -2, powers := [(13, 1), (19, 1), (24, 1), (25, 1), (42, 1), (58, 1), (63, 1), (65, 1)] }, { coefficient := -2, powers := [(13, 1), (19, 1), (24, 1), (25, 1), (47, 1), (58, 1), (63, 1), (65, 1)] }, { coefficient := -2, powers := [(13, 1), (19, 1), (25, 1), (29, 1), (42, 1), (58, 1), (63, 1), (65, 1)] }, { coefficient := -2, powers := [(13, 1), (19, 1), (25, 1), (29, 1), (47, 1), (58, 1), (63, 1), (65, 1)] }, { coefficient := 2, powers := [(13, 1), (21, 1), (25, 1), (42, 1), (58, 1), (62, 1), (65, 1)] }, { coefficient := 2, powers := [(13, 1), (21, 1), (25, 1), (47, 1), (58, 1), (62, 1), (65, 1)] }, { coefficient := 2, powers := [(13, 1), (21, 1), (25, 1), (53, 1), (58, 1), (62, 1), (65, 1)] }, { coefficient := 2, powers := [(13, 1), (21, 1), (25, 1), (57, 1), (58, 1), (62, 1), (65, 1)] }, { coefficient := -4, powers := [(13, 1), (31, 1), (50, 1), (53, 1), (65, 1)] }, { coefficient := -4, powers := [(20, 1), (25, 1), (53, 1), (55, 1), (65, 1)] }, { coefficient := 2, powers := [(20, 1), (31, 1), (43, 1), (53, 2), (64, 1), (65, 1)] }, { coefficient := -2, powers := [(20, 1), (31, 1), (43, 1), (53, 1), (65, 1)] }],
  [{ coefficient := -2, powers := [(2, 1), (11, 1), (40, 1), (42, 1), (61, 1), (65, 1)] }, { coefficient := -4, powers := [(2, 1), (11, 1), (40, 1), (47, 1), (61, 1), (65, 1)] }, { coefficient := -2, powers := [(2, 1), (16, 1), (40, 1), (53, 1), (61, 1), (65, 1)] }, { coefficient := -2, powers := [(5, 1), (7, 1), (34, 1), (58, 1), (60, 1), (65, 1)] }, { coefficient := 1, powers := [(5, 1), (11, 1), (21, 1), (34, 1), (42, 1), (57, 1), (58, 1), (65, 1)] }, { coefficient := 1, powers := [(5, 1), (11, 1), (21, 1), (34, 1), (47, 1), (57, 1), (58, 1), (65, 1)] }, { coefficient := -1, powers := [(5, 1), (11, 1), (34, 1), (42, 1), (58, 1), (65, 1)] }, { coefficient := -3, powers := [(5, 1), (11, 1), (34, 1), (47, 1), (58, 1), (65, 1)] }, { coefficient := -2, powers := [(5, 1), (11, 1), (34, 1), (57, 1), (58, 1), (65, 1)] }, { coefficient := -2, powers := [(5, 1), (16, 1), (34, 1), (53, 1), (58, 1), (65, 1)] }],
  [{ coefficient := -2, powers := [(2, 1), (11, 1), (13, 1), (33, 1), (40, 1), (42, 1), (45, 1), (63, 1), (65, 1)] }, { coefficient := -2, powers := [(2, 1), (11, 1), (13, 1), (33, 1), (40, 1), (45, 1), (53, 1), (63, 1), (65, 1)] }, { coefficient := -2, powers := [(2, 1), (11, 1), (13, 1), (33, 1), (40, 1), (48, 1), (63, 1), (65, 1)] }, { coefficient := -2, powers := [(19, 1), (43, 1), (58, 1), (64, 1), (65, 1)] }, { coefficient := -2, powers := [(20, 1), (43, 1), (54, 1), (64, 1), (65, 1)] }],
  [{ coefficient := 2, powers := [(2, 1), (11, 1), (20, 1), (33, 1), (40, 1), (63, 1)] }, { coefficient := 1, powers := [(5, 1), (11, 1), (21, 1), (33, 1), (57, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (11, 1), (21, 1), (36, 1), (57, 1), (58, 1)] }, { coefficient := -1, powers := [(5, 1), (11, 1), (33, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (11, 1), (36, 1), (58, 1)] }, { coefficient := -2, powers := [(5, 1), (16, 1), (33, 1), (58, 1)] }],
  [{ coefficient := -2, powers := [(2, 1), (26, 1), (42, 1), (43, 1), (53, 1), (54, 1), (64, 1), (65, 1)] }, { coefficient := 2, powers := [(2, 1), (42, 1), (43, 1), (54, 1), (64, 1), (65, 1)] }, { coefficient := -2, powers := [(13, 1), (25, 1), (54, 1), (65, 1)] }, { coefficient := 2, powers := [(19, 1), (25, 1), (55, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (11, 1), (23, 1), (58, 1), (60, 1)] }],
  [{ coefficient := -2, powers := [(2, 1), (28, 1), (40, 1), (60, 1)] }, { coefficient := 2, powers := [(2, 1), (33, 1), (40, 1), (57, 1)] }, { coefficient := 2, powers := [(2, 1), (36, 1), (40, 1), (42, 1)] }],
  [{ coefficient := 2, powers := [(21, 1), (25, 1), (58, 1)] }],
  [{ coefficient := -2, powers := [(19, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (11, 1), (23, 1), (34, 1), (53, 1), (58, 1), (65, 1)] }],
  [{ coefficient := -2, powers := [(25, 1), (58, 1)] }],
  [{ coefficient := 2, powers := [(2, 1), (53, 1), (55, 1)] }, { coefficient := 4, powers := [(13, 1), (31, 1), (53, 1)] }],
  [{ coefficient := -2, powers := [(2, 1), (40, 1), (42, 1), (61, 1)] }, { coefficient := 2, powers := [(2, 1), (40, 1), (53, 1), (61, 1)] }, { coefficient := 2, powers := [(5, 1), (34, 1), (53, 1), (58, 1)] }],
  [{ coefficient := 2, powers := [(2, 1), (40, 1), (47, 1), (61, 1)] }, { coefficient := -2, powers := [(2, 1), (40, 1), (57, 1), (61, 1)] }, { coefficient := 2, powers := [(5, 1), (34, 1), (47, 1), (58, 1)] }],
  [{ coefficient := 2, powers := [(31, 1)] }],
  [{ coefficient := 4, powers := [(25, 1), (26, 1), (55, 1)] }, { coefficient := -2, powers := [(26, 1), (31, 1), (43, 1), (53, 1), (64, 1)] }, { coefficient := 2, powers := [(26, 1), (31, 1), (43, 1)] }, { coefficient := -2, powers := [(31, 1), (43, 1), (64, 1)] }],
  [{ coefficient := 2, powers := [(20, 1)] }],
  [{ coefficient := -2, powers := [(2, 1), (55, 1)] }, { coefficient := -4, powers := [(13, 1), (31, 1)] }],
  [{ coefficient := 2, powers := [(2, 1), (40, 1), (60, 1)] }],
  [{ coefficient := 2, powers := [(5, 1), (33, 1), (58, 1)] }],
  [{ coefficient := 2, powers := [(13, 1), (24, 1), (25, 1), (58, 1), (63, 1)] }, { coefficient := 2, powers := [(13, 1), (25, 1), (29, 1), (58, 1), (63, 1)] }],
  [{ coefficient := -4, powers := [(25, 1), (55, 1)] }, { coefficient := 2, powers := [(31, 1), (43, 1), (53, 1), (64, 1)] }, { coefficient := -2, powers := [(31, 1), (43, 1)] }],
  [{ coefficient := 2, powers := [(2, 1), (43, 1), (53, 1), (54, 1), (64, 1)] }],
  [{ coefficient := 2, powers := [(55, 1)] }],
  [{ coefficient := 2, powers := [(50, 1)] }],
  [{ coefficient := 2, powers := [(25, 1)] }],
  [{ coefficient := -2, powers := [(2, 1), (43, 1), (54, 1), (64, 1)] }],
  [{ coefficient := -2, powers := [(13, 1), (25, 1), (58, 1), (63, 1)] }],
  [{ coefficient := -2, powers := [(2, 1), (11, 1), (33, 1), (40, 1), (63, 1)] }],
  [{ coefficient := -2, powers := [(2, 1), (11, 1), (40, 1), (53, 1), (61, 1)] }],
  [{ coefficient := 2, powers := [(13, 1)] }],
  [{ coefficient := 2, powers := [(2, 1), (11, 1), (13, 1), (33, 1), (40, 1), (63, 1)] }],
  [{ coefficient := -2, powers := [(13, 1), (21, 1), (25, 1), (58, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (11, 1), (23, 1), (34, 1), (57, 1), (58, 1)] }, { coefficient := -2, powers := [(13, 1), (25, 1), (26, 1), (58, 1), (62, 1)] }],
  [{ coefficient := 2, powers := [(2, 1), (28, 1), (40, 1), (61, 1)] }, { coefficient := 2, powers := [(5, 1), (28, 1), (34, 1), (58, 1)] }],
  [{ coefficient := 2, powers := [(2, 1), (11, 1), (40, 1), (61, 1)] }, { coefficient := -1, powers := [(5, 1), (11, 1), (21, 1), (34, 1), (57, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (11, 1), (34, 1), (58, 1)] }],
  [{ coefficient := 2, powers := [(13, 1), (25, 1), (58, 1), (62, 1)] }],
  [{ coefficient := 2, powers := [(43, 1), (64, 1)] }],
  [{ coefficient := -2, powers := [(2, 1), (40, 1), (61, 1)] }, { coefficient := -2, powers := [(5, 1), (34, 1), (58, 1)] }],
  [{ coefficient := -2, powers := [] }],
  [{ coefficient := 2, powers := [(13, 1), (21, 1), (25, 1), (47, 1), (58, 1)] }, { coefficient := -2, powers := [(13, 1), (25, 1), (38, 1), (58, 1), (60, 1)] }, { coefficient := -2, powers := [(13, 1), (25, 1), (58, 1)] }],
  [{ coefficient := 2, powers := [(2, 1), (40, 1), (42, 1), (47, 1), (61, 1)] }, { coefficient := 2, powers := [(2, 1), (40, 1), (42, 1), (57, 1), (61, 1)] }, { coefficient := -2, powers := [(2, 1), (40, 1), (47, 1), (53, 1), (61, 1)] }, { coefficient := 2, powers := [(2, 1), (40, 1), (53, 1), (57, 1), (61, 1)] }, { coefficient := 2, powers := [(5, 1), (34, 1), (39, 1), (58, 1), (60, 1)] }, { coefficient := 2, powers := [(5, 1), (34, 1), (42, 1), (57, 1), (58, 1)] }, { coefficient := -2, powers := [(5, 1), (34, 1), (47, 1), (53, 1), (58, 1)] }],
  [{ coefficient := 2, powers := [(2, 1), (11, 1), (33, 1), (39, 1), (40, 1), (61, 1)] }, { coefficient := 2, powers := [(13, 1), (25, 1), (38, 1), (58, 1), (60, 1)] }, { coefficient := 2, powers := [(13, 1), (25, 1), (58, 1)] }],
  [{ coefficient := -2, powers := [(2, 1), (43, 1), (58, 1)] }, { coefficient := -2, powers := [(8, 1), (37, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (5, 1), (11, 1), (23, 1), (34, 1), (53, 1), (57, 1), (58, 1)] }, { coefficient := -2, powers := [(0, 1), (13, 1), (25, 1), (26, 1), (53, 1), (58, 1), (62, 1)] }, { coefficient := 2, powers := [(2, 1), (11, 1), (13, 1), (30, 1), (33, 1), (40, 1), (42, 1), (45, 1), (63, 1)] }, { coefficient := 2, powers := [(2, 1), (11, 1), (13, 1), (30, 1), (33, 1), (40, 1), (45, 1), (53, 1), (63, 1)] }, { coefficient := 2, powers := [(2, 1), (11, 1), (13, 1), (30, 1), (33, 1), (40, 1), (48, 1), (63, 1)] }, { coefficient := 2, powers := [(2, 1), (11, 1), (28, 1), (40, 1), (42, 1), (61, 1)] }, { coefficient := 4, powers := [(2, 1), (11, 1), (28, 1), (40, 1), (47, 1), (61, 1)] }, { coefficient := -2, powers := [(2, 1), (16, 1), (23, 1), (40, 1), (42, 1), (61, 1)] }, { coefficient := 2, powers := [(2, 1), (16, 1), (28, 1), (40, 1), (53, 1), (61, 1)] }, { coefficient := -2, powers := [(2, 1), (16, 1), (33, 1), (39, 1), (40, 1), (61, 1)] }, { coefficient := 2, powers := [(2, 1), (26, 1), (42, 1), (43, 1), (45, 1), (53, 1), (54, 1), (64, 1)] }, { coefficient := 2, powers := [(2, 1), (26, 1), (43, 1), (48, 1), (53, 1), (54, 1), (64, 1)] }, { coefficient := 2, powers := [(2, 1), (26, 1), (50, 1), (53, 1), (55, 1)] }, { coefficient := -2, powers := [(2, 1), (42, 1), (43, 1), (45, 1), (54, 1), (64, 1)] }, { coefficient := 2, powers := [(5, 1), (7, 1), (28, 1), (34, 1), (58, 1), (60, 1)] }, { coefficient := -1, powers := [(5, 1), (11, 1), (21, 1), (28, 1), (34, 1), (42, 1), (57, 1), (58, 1)] }, { coefficient := -1, powers := [(5, 1), (11, 1), (21, 1), (28, 1), (34, 1), (47, 1), (57, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (11, 1), (23, 1), (34, 1), (53, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (11, 1), (28, 1), (34, 1), (42, 1), (58, 1)] }, { coefficient := 3, powers := [(5, 1), (11, 1), (28, 1), (34, 1), (47, 1), (58, 1)] }, { coefficient := 2, powers := [(5, 1), (11, 1), (28, 1), (34, 1), (57, 1), (58, 1)] }, { coefficient := 2, powers := [(5, 1), (16, 1), (28, 1), (34, 1), (53, 1), (58, 1)] }, { coefficient := -2, powers := [(5, 1), (16, 1), (33, 1), (34, 1), (39, 1), (58, 1)] }, { coefficient := 2, powers := [(13, 1), (19, 1), (24, 1), (25, 1), (26, 1), (42, 1), (58, 1), (63, 1)] }, { coefficient := 2, powers := [(13, 1), (19, 1), (24, 1), (25, 1), (26, 1), (47, 1), (58, 1), (63, 1)] }, { coefficient := 2, powers := [(13, 1), (19, 1), (25, 1), (26, 1), (29, 1), (42, 1), (58, 1), (63, 1)] }, { coefficient := 2, powers := [(13, 1), (19, 1), (25, 1), (26, 1), (29, 1), (47, 1), (58, 1), (63, 1)] }, { coefficient := -2, powers := [(13, 1), (21, 1), (25, 1), (26, 1), (42, 1), (58, 1), (62, 1)] }, { coefficient := -2, powers := [(13, 1), (21, 1), (25, 1), (26, 1), (47, 1), (58, 1), (62, 1)] }, { coefficient := -2, powers := [(13, 1), (21, 1), (25, 1), (26, 1), (53, 1), (58, 1), (62, 1)] }, { coefficient := -2, powers := [(13, 1), (21, 1), (25, 1), (26, 1), (57, 1), (58, 1), (62, 1)] }, { coefficient := 2, powers := [(13, 1), (25, 1), (45, 1), (54, 1)] }, { coefficient := 4, powers := [(13, 1), (26, 1), (31, 1), (50, 1), (53, 1)] }, { coefficient := -2, powers := [(19, 1), (25, 1), (45, 1), (55, 1)] }, { coefficient := 2, powers := [(19, 1), (30, 1), (43, 1), (58, 1), (64, 1)] }, { coefficient := 4, powers := [(20, 1), (25, 1), (26, 1), (53, 1), (55, 1)] }, { coefficient := -2, powers := [(20, 1), (26, 1), (31, 1), (43, 1), (53, 2), (64, 1)] }, { coefficient := 2, powers := [(20, 1), (26, 1), (31, 1), (43, 1), (53, 1)] }, { coefficient := 2, powers := [(20, 1), (30, 1), (43, 1), (54, 1), (64, 1)] }]
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
    (values : Fin 66 → R) :
    ¬ ∀ index : Fin 50,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((2 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (2 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (2 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component16.SelectedLeafB5_3.selectedHasNoCommonZero

end Krenn.Component16.SelectedLeafB5_3
