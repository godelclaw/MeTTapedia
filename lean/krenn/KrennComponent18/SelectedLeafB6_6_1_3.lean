import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component18.SelectedLeafB6_6_1_3

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "9645efd7473315312bb315134846875f97c03d4071404e0985093074dd9a6b39"
def certificateSHA256 : String := "c6830726358036797c61ca89ee233d0c1c06c40a941860f5ab8648cdb64989ab"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 42 → Fin 670 := ![
  10,
  19,
  23,
  145,
  148,
  149,
  151,
  246,
  294,
  301,
  318,
  319,
  323,
  409,
  424,
  437,
  443,
  450,
  458,
  463,
  501,
  502,
  505,
  506,
  523,
  580,
  604,
  605,
  606,
  607,
  608,
  609,
  645,
  656,
  657,
  658,
  660,
  663,
  665,
  666,
  667,
  669
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 42 → SparsePoly (Fin 68) := ![
  [{ coefficient := 1, powers := [(13, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(30, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (25, 1)] }, { coefficient := 1, powers := [(15, 1), (19, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (26, 1)] }, { coefficient := 1, powers := [(15, 1), (19, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (31, 1)] }, { coefficient := 1, powers := [(15, 1), (23, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (19, 1), (56, 1)] }, { coefficient := 1, powers := [(13, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1)] }, { coefficient := 1, powers := [(19, 1), (45, 1)] }, { coefficient := 1, powers := [(25, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (60, 1)] }, { coefficient := 1, powers := [(13, 1), (49, 1)] }, { coefficient := 1, powers := [(18, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (54, 1)] }, { coefficient := 1, powers := [(31, 1), (43, 1)] }, { coefficient := 1, powers := [(34, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(30, 1), (53, 1)] }, { coefficient := 1, powers := [(31, 1), (42, 1)] }, { coefficient := 1, powers := [(31, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1), (52, 1)] }, { coefficient := 1, powers := [(19, 1), (45, 1), (52, 1)] }, { coefficient := 1, powers := [(45, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (25, 1), (47, 1)] }, { coefficient := 1, powers := [(18, 1), (25, 1), (42, 1)] }, { coefficient := 1, powers := [(18, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1)] }, { coefficient := 1, powers := [(25, 1), (42, 1), (45, 1)] }, { coefficient := 1, powers := [(25, 1), (47, 1)] }, { coefficient := 1, powers := [(45, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1)] }, { coefficient := 1, powers := [(13, 1), (31, 1)] }, { coefficient := 1, powers := [(17, 1), (23, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (60, 1)] }, { coefficient := 1, powers := [(13, 1), (26, 1), (47, 1)] }, { coefficient := 1, powers := [(13, 1), (57, 1)] }, { coefficient := 1, powers := [(18, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(30, 1), (42, 1)] }, { coefficient := 1, powers := [(30, 1), (46, 1)] }, { coefficient := 1, powers := [(30, 1), (52, 1)] }, { coefficient := 1, powers := [(30, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1), (53, 1)] }, { coefficient := 1, powers := [(19, 1), (45, 1), (53, 1)] }, { coefficient := 1, powers := [(19, 1), (57, 1)] }, { coefficient := 1, powers := [(26, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1), (52, 1)] }, { coefficient := 1, powers := [(42, 1), (45, 1)] }, { coefficient := 1, powers := [(45, 1), (52, 1)] }, { coefficient := 1, powers := [(47, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (25, 1), (59, 1)] }, { coefficient := 1, powers := [(11, 1), (25, 1), (46, 1)] }, { coefficient := 1, powers := [(15, 1), (25, 1), (42, 1)] }, { coefficient := 1, powers := [(15, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (26, 1), (59, 1)] }, { coefficient := 1, powers := [(11, 1), (26, 1), (46, 1)] }, { coefficient := 1, powers := [(15, 1), (26, 1), (42, 1)] }, { coefficient := 1, powers := [(15, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (31, 1), (59, 1)] }, { coefficient := 1, powers := [(11, 1), (31, 1), (46, 1)] }, { coefficient := 1, powers := [(15, 1), (30, 1), (53, 1)] }, { coefficient := 1, powers := [(15, 1), (31, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (31, 1), (60, 1)] }, { coefficient := 1, powers := [(4, 1), (34, 1), (57, 1)] }, { coefficient := 1, powers := [(4, 1), (37, 1), (54, 1)] }, { coefficient := 1, powers := [(16, 1), (30, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (23, 1), (59, 1)] }, { coefficient := 1, powers := [(11, 1), (23, 1), (56, 1)] }, { coefficient := 1, powers := [(11, 1), (30, 1)] }, { coefficient := 1, powers := [(15, 1), (23, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1)] }, { coefficient := 1, powers := [(6, 1), (59, 1)] }, { coefficient := 1, powers := [(25, 1), (42, 1)] }, { coefficient := 1, powers := [(25, 1), (46, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1), (46, 1)] }, { coefficient := 1, powers := [(4, 1), (27, 1), (59, 1)] }, { coefficient := 1, powers := [(4, 1), (36, 1)] }, { coefficient := 1, powers := [(11, 1), (27, 1), (46, 1)] }, { coefficient := 1, powers := [(15, 1), (22, 1)] }, { coefficient := 1, powers := [(15, 1), (27, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (52, 1)] }, { coefficient := 1, powers := [(7, 1), (21, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (33, 1)] }, { coefficient := 1, powers := [(11, 1), (21, 1), (56, 1)] }, { coefficient := 1, powers := [(11, 1), (28, 1)] }, { coefficient := 1, powers := [(15, 1), (21, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (59, 1)] }, { coefficient := 1, powers := [(11, 1), (46, 1)] }, { coefficient := 1, powers := [(11, 1), (56, 1)] }, { coefficient := 1, powers := [(15, 1), (42, 1)] }, { coefficient := 1, powers := [(15, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (52, 1)] }, { coefficient := 1, powers := [(22, 1), (56, 1)] }, { coefficient := 1, powers := [(28, 1), (42, 1)] }, { coefficient := 1, powers := [(28, 1), (46, 1)] }, { coefficient := 1, powers := [(33, 1), (39, 1)] }, { coefficient := 1, powers := [(36, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (38, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1)] }, { coefficient := 1, powers := [(3, 1), (25, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (19, 1), (59, 1)] }, { coefficient := 1, powers := [(19, 1)] }, { coefficient := 1, powers := [(25, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (47, 1), (53, 1)] }, { coefficient := 1, powers := [(26, 1), (42, 1), (45, 1)] }, { coefficient := 1, powers := [(26, 1), (47, 1)] }, { coefficient := 1, powers := [(45, 1), (53, 1)] }, { coefficient := 1, powers := [(57, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (39, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (42, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(42, 1)] }, { coefficient := 1, powers := [(46, 1)] }, { coefficient := 1, powers := [(52, 1)] }, { coefficient := 1, powers := [(56, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (39, 1), (59, 1)] }, { coefficient := 1, powers := [(1, 1), (42, 1), (56, 1)] }, { coefficient := 1, powers := [(1, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(4, 1), (28, 1), (59, 1)] }, { coefficient := 1, powers := [(4, 1), (33, 1), (56, 1)] }, { coefficient := 1, powers := [(4, 1), (36, 1), (52, 1)] }, { coefficient := 1, powers := [(7, 1), (22, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (33, 1), (46, 1)] }, { coefficient := 1, powers := [(7, 1), (36, 1), (42, 1)] }, { coefficient := 1, powers := [(11, 1), (22, 1), (56, 1)] }, { coefficient := 1, powers := [(11, 1), (28, 1), (46, 1)] }, { coefficient := 1, powers := [(11, 1), (36, 1), (39, 1)] }, { coefficient := 1, powers := [(15, 1), (22, 1), (52, 1)] }, { coefficient := 1, powers := [(15, 1), (28, 1), (42, 1)] }, { coefficient := 1, powers := [(15, 1), (33, 1), (39, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (40, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (43, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (49, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (37, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (49, 1)] }, { coefficient := 1, powers := [(8, 1), (37, 1), (43, 1)] }, { coefficient := 1, powers := [(13, 1), (24, 1), (57, 1)] }, { coefficient := 1, powers := [(13, 1), (31, 1), (49, 1)] }, { coefficient := 1, powers := [(13, 1), (37, 1), (40, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (54, 1)] }, { coefficient := 1, powers := [(18, 1), (31, 1), (43, 1)] }, { coefficient := 1, powers := [(18, 1), (34, 1), (40, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (61, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(43, 1)] }],
  [{ coefficient := 1, powers := [(56, 1)] }],
  [{ coefficient := 1, powers := [(57, 1), (65, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(25, 1)] }],
  [{ coefficient := 1, powers := [(31, 1), (67, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 42 → SparsePoly (Fin 68) := ![
  [{ coefficient := -1, powers := [(4, 1), (24, 1), (26, 1), (36, 1), (42, 1)] }, { coefficient := -1, powers := [(4, 1), (24, 1), (26, 1), (36, 1), (46, 1)] }, { coefficient := -1, powers := [(4, 1), (24, 1), (26, 1), (36, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (17, 1), (36, 1), (42, 1), (49, 1)] }, { coefficient := -1, powers := [(4, 1), (17, 1), (36, 1), (46, 1), (49, 1)] }, { coefficient := -1, powers := [(4, 1), (17, 1), (36, 1), (49, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (16, 1), (36, 1), (42, 1)] }, { coefficient := -1, powers := [(5, 1), (16, 1), (36, 1), (46, 1)] }, { coefficient := -1, powers := [(5, 1), (16, 1), (36, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (31, 1), (36, 1), (42, 1)] }, { coefficient := -1, powers := [(5, 1), (31, 1), (36, 1), (46, 1)] }, { coefficient := -1, powers := [(5, 1), (31, 1), (36, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(28, 1), (30, 1), (46, 1), (53, 1), (67, 1)] }, { coefficient := -1, powers := [(30, 1), (36, 1), (39, 1), (53, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(28, 1), (30, 1), (46, 1), (67, 1)] }, { coefficient := 1, powers := [(30, 1), (36, 1), (39, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(28, 1), (46, 1), (67, 1)] }, { coefficient := 1, powers := [(36, 1), (39, 1), (67, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (31, 1), (36, 1), (42, 1), (49, 1)] }, { coefficient := -1, powers := [(4, 1), (31, 1), (36, 1), (46, 1), (49, 1)] }, { coefficient := -1, powers := [(4, 1), (31, 1), (36, 1), (49, 1), (52, 1)] }, { coefficient := 1, powers := [(4, 1), (36, 1), (37, 1), (40, 1), (42, 1)] }, { coefficient := 1, powers := [(4, 1), (36, 1), (37, 1), (40, 1), (46, 1)] }, { coefficient := 1, powers := [(4, 1), (36, 1), (37, 1), (40, 1), (52, 1)] }, { coefficient := -1, powers := [(7, 1), (31, 1), (36, 1), (42, 1), (49, 1)] }, { coefficient := -1, powers := [(7, 1), (31, 1), (36, 1), (46, 1), (49, 1)] }, { coefficient := -1, powers := [(7, 1), (31, 1), (36, 1), (49, 1), (52, 1)] }],
  [{ coefficient := 2, powers := [(7, 1), (26, 1), (33, 1), (46, 2), (52, 1), (65, 1)] }, { coefficient := 1, powers := [(7, 1), (26, 1), (36, 1), (42, 1), (46, 1), (52, 1), (65, 1)] }, { coefficient := -2, powers := [(7, 1), (33, 1), (46, 2), (53, 1), (65, 1)] }, { coefficient := -1, powers := [(7, 1), (36, 1), (42, 1), (46, 1), (53, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (31, 1), (36, 1), (42, 1)] }, { coefficient := 1, powers := [(4, 1), (31, 1), (36, 1), (46, 1)] }, { coefficient := 1, powers := [(4, 1), (31, 1), (36, 1), (52, 1)] }, { coefficient := 1, powers := [(7, 1), (31, 1), (36, 1), (42, 1)] }, { coefficient := 1, powers := [(7, 1), (31, 1), (36, 1), (46, 1)] }, { coefficient := 1, powers := [(7, 1), (31, 1), (36, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (18, 1), (36, 1), (42, 1)] }, { coefficient := 1, powers := [(4, 1), (18, 1), (36, 1), (46, 1)] }, { coefficient := 1, powers := [(4, 1), (18, 1), (36, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (42, 1), (67, 1)] }, { coefficient := 1, powers := [(1, 1), (46, 1), (67, 1)] }, { coefficient := 1, powers := [(1, 1), (52, 1), (67, 1)] }, { coefficient := 1, powers := [(15, 1), (21, 1), (46, 1), (67, 1)] }, { coefficient := 1, powers := [(15, 1), (22, 1), (67, 1)] }, { coefficient := -1, powers := [(15, 1), (27, 1), (42, 1), (67, 1)] }, { coefficient := -1, powers := [(15, 1), (27, 1), (46, 1), (67, 1)] }, { coefficient := -1, powers := [(15, 1), (28, 1), (67, 1)] }, { coefficient := -2, powers := [(15, 1), (33, 1), (38, 1), (46, 1), (67, 1)] }, { coefficient := -1, powers := [(15, 1), (36, 1), (38, 1), (42, 1), (67, 1)] }],
  [{ coefficient := -2, powers := [(7, 1), (26, 1), (33, 1), (46, 2), (65, 1)] }, { coefficient := -1, powers := [(7, 1), (26, 1), (36, 1), (42, 1), (46, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (24, 1), (36, 1), (42, 1), (54, 1)] }, { coefficient := -1, powers := [(4, 1), (24, 1), (36, 1), (46, 1), (54, 1)] }, { coefficient := -1, powers := [(4, 1), (24, 1), (36, 1), (52, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(1, 1), (26, 1), (42, 1), (52, 1), (61, 1), (65, 1)] }, { coefficient := -1, powers := [(1, 1), (26, 1), (46, 1), (52, 1), (61, 1), (65, 1)] }, { coefficient := -1, powers := [(1, 1), (26, 1), (52, 2), (61, 1), (65, 1)] }, { coefficient := 1, powers := [(1, 1), (42, 1), (53, 1), (61, 1), (65, 1)] }, { coefficient := 1, powers := [(1, 1), (46, 1), (53, 1), (61, 1), (65, 1)] }, { coefficient := 1, powers := [(1, 1), (52, 1), (53, 1), (61, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (36, 1), (42, 1), (49, 1)] }, { coefficient := 1, powers := [(4, 1), (36, 1), (46, 1), (49, 1)] }, { coefficient := 1, powers := [(4, 1), (36, 1), (49, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (24, 1), (36, 1), (42, 1)] }, { coefficient := 1, powers := [(4, 1), (24, 1), (36, 1), (46, 1)] }, { coefficient := 1, powers := [(4, 1), (24, 1), (36, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(1, 1), (53, 1), (67, 1)] }],
  [{ coefficient := 2, powers := [(7, 1), (33, 1), (46, 2), (65, 1)] }, { coefficient := 1, powers := [(7, 1), (36, 1), (42, 1), (46, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (26, 1), (42, 1), (61, 1), (65, 1)] }, { coefficient := 1, powers := [(1, 1), (26, 1), (46, 1), (61, 1), (65, 1)] }, { coefficient := 1, powers := [(1, 1), (26, 1), (52, 1), (61, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(21, 1), (42, 1), (46, 1)] }, { coefficient := -1, powers := [(21, 1), (46, 2)] }, { coefficient := -1, powers := [(22, 1), (52, 1)] }, { coefficient := 1, powers := [(27, 1), (42, 2)] }, { coefficient := 2, powers := [(27, 1), (42, 1), (46, 1)] }, { coefficient := 1, powers := [(27, 1), (46, 2)] }, { coefficient := 2, powers := [(33, 1), (38, 1), (42, 1), (46, 1)] }, { coefficient := 2, powers := [(33, 1), (38, 1), (46, 2)] }, { coefficient := 2, powers := [(33, 1), (38, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(36, 1), (38, 1), (42, 2)] }, { coefficient := 1, powers := [(36, 1), (38, 1), (42, 1), (46, 1)] }, { coefficient := 1, powers := [(36, 1), (38, 1), (42, 1), (52, 1)] }, { coefficient := -1, powers := [(36, 1), (39, 1)] }],
  [{ coefficient := -1, powers := [(23, 1), (28, 1), (46, 1), (67, 1)] }, { coefficient := -1, powers := [(23, 1), (36, 1), (39, 1), (67, 1)] }],
  [{ coefficient := -1, powers := [(21, 1), (46, 1), (67, 1)] }, { coefficient := -1, powers := [(22, 1), (67, 1)] }, { coefficient := 1, powers := [(27, 1), (42, 1), (67, 1)] }, { coefficient := 1, powers := [(27, 1), (46, 1), (67, 1)] }, { coefficient := 1, powers := [(28, 1), (67, 1)] }, { coefficient := 2, powers := [(33, 1), (38, 1), (46, 1), (67, 1)] }, { coefficient := 1, powers := [(36, 1), (38, 1), (42, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (36, 1), (42, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1), (46, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(26, 1), (28, 1), (46, 1), (67, 1)] }, { coefficient := -1, powers := [(26, 1), (36, 1), (39, 1), (67, 1)] }],
  [{ coefficient := -2, powers := [(7, 1), (19, 1), (33, 1), (46, 1), (61, 1)] }, { coefficient := -1, powers := [(7, 1), (19, 1), (36, 1), (42, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(42, 1)] }, { coefficient := -1, powers := [(46, 1)] }],
  [{ coefficient := -1, powers := [(46, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (31, 1), (46, 1), (67, 1)] }, { coefficient := 1, powers := [(22, 1), (31, 1), (67, 1)] }, { coefficient := 1, powers := [(23, 1), (26, 1), (28, 1), (46, 1), (67, 1)] }, { coefficient := 1, powers := [(23, 1), (26, 1), (36, 1), (39, 1), (67, 1)] }, { coefficient := -1, powers := [(27, 1), (31, 1), (42, 1), (67, 1)] }, { coefficient := -1, powers := [(27, 1), (31, 1), (46, 1), (67, 1)] }, { coefficient := 1, powers := [(27, 1), (42, 1)] }, { coefficient := 1, powers := [(27, 1), (46, 1)] }, { coefficient := -1, powers := [(28, 1), (31, 1), (67, 1)] }, { coefficient := 1, powers := [(28, 1)] }, { coefficient := -2, powers := [(31, 1), (33, 1), (38, 1), (46, 1), (67, 1)] }, { coefficient := -1, powers := [(31, 1), (36, 1), (38, 1), (42, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(15, 1)] }],
  [{ coefficient := 2, powers := [(7, 1), (33, 1), (46, 1), (61, 1)] }, { coefficient := 1, powers := [(7, 1), (36, 1), (42, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(1, 1), (42, 1), (61, 1), (65, 1)] }, { coefficient := -1, powers := [(1, 1), (46, 1), (61, 1), (65, 1)] }, { coefficient := -1, powers := [(1, 1), (52, 1), (61, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(4, 1), (36, 1), (42, 1)] }, { coefficient := -1, powers := [(4, 1), (36, 1), (46, 1)] }, { coefficient := -1, powers := [(4, 1), (36, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(1, 1), (39, 1), (59, 1)] }, { coefficient := 1, powers := [(1, 1), (42, 2)] }, { coefficient := 1, powers := [(1, 1), (42, 1), (46, 1)] }, { coefficient := 1, powers := [(1, 1), (42, 1), (52, 1)] }, { coefficient := -1, powers := [(1, 1), (46, 1), (52, 1)] }, { coefficient := 2, powers := [(7, 1), (19, 1), (33, 1), (46, 2)] }, { coefficient := 1, powers := [(7, 1), (19, 1), (36, 1), (42, 1), (46, 1)] }, { coefficient := -2, powers := [(7, 1), (33, 1), (38, 1), (46, 1), (59, 1)] }, { coefficient := -2, powers := [(7, 1), (33, 1), (46, 1)] }, { coefficient := -1, powers := [(7, 1), (36, 1), (38, 1), (42, 1), (59, 1)] }, { coefficient := -1, powers := [(7, 1), (36, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (36, 1), (40, 1), (42, 1), (60, 1)] }, { coefficient := 1, powers := [(4, 1), (36, 1), (40, 1), (46, 1), (60, 1)] }, { coefficient := 1, powers := [(4, 1), (36, 1), (40, 1), (52, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (4, 1), (36, 1), (42, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (4, 1), (36, 1), (46, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (4, 1), (36, 1), (52, 1), (57, 1)] }, { coefficient := 1, powers := [(4, 1), (8, 1), (36, 1), (37, 1), (42, 1)] }, { coefficient := 1, powers := [(4, 1), (8, 1), (36, 1), (37, 1), (46, 1)] }, { coefficient := 1, powers := [(4, 1), (8, 1), (36, 1), (37, 1), (52, 1)] }, { coefficient := -1, powers := [(4, 1), (18, 1), (31, 1), (36, 1), (42, 1)] }, { coefficient := -1, powers := [(4, 1), (18, 1), (31, 1), (36, 1), (46, 1)] }, { coefficient := -1, powers := [(4, 1), (18, 1), (31, 1), (36, 1), (52, 1)] }, { coefficient := -1, powers := [(7, 1), (18, 1), (31, 1), (36, 1), (42, 1)] }, { coefficient := -1, powers := [(7, 1), (18, 1), (31, 1), (36, 1), (46, 1)] }, { coefficient := -1, powers := [(7, 1), (18, 1), (31, 1), (36, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (1, 1), (42, 1), (61, 1)] }, { coefficient := 1, powers := [(1, 1), (30, 1), (53, 1), (67, 1)] }, { coefficient := 1, powers := [(1, 1), (42, 1)] }, { coefficient := -1, powers := [(1, 1), (61, 1)] }, { coefficient := 1, powers := [(4, 1), (13, 1), (19, 1), (31, 1), (36, 1), (42, 1), (49, 1)] }, { coefficient := 1, powers := [(4, 1), (13, 1), (19, 1), (31, 1), (36, 1), (46, 1), (49, 1)] }, { coefficient := 1, powers := [(4, 1), (13, 1), (19, 1), (31, 1), (36, 1), (49, 1), (52, 1)] }, { coefficient := -1, powers := [(4, 1), (13, 1), (19, 1), (36, 1), (37, 1), (40, 1), (42, 1)] }, { coefficient := -1, powers := [(4, 1), (13, 1), (19, 1), (36, 1), (37, 1), (40, 1), (46, 1)] }, { coefficient := -1, powers := [(4, 1), (13, 1), (19, 1), (36, 1), (37, 1), (40, 1), (52, 1)] }, { coefficient := 1, powers := [(4, 1), (33, 1)] }, { coefficient := 1, powers := [(7, 1), (13, 1), (19, 1), (31, 1), (36, 1), (42, 1), (49, 1)] }, { coefficient := 1, powers := [(7, 1), (13, 1), (19, 1), (31, 1), (36, 1), (46, 1), (49, 1)] }, { coefficient := 1, powers := [(7, 1), (13, 1), (19, 1), (31, 1), (36, 1), (49, 1), (52, 1)] }, { coefficient := -1, powers := [(11, 1), (21, 1), (31, 1), (46, 1), (67, 1)] }, { coefficient := 1, powers := [(11, 1), (21, 1), (46, 1)] }, { coefficient := -1, powers := [(11, 1), (22, 1), (31, 1), (67, 1)] }, { coefficient := 1, powers := [(11, 1), (22, 1)] }, { coefficient := 1, powers := [(11, 1), (27, 1), (31, 1), (42, 1), (67, 1)] }, { coefficient := 1, powers := [(11, 1), (27, 1), (31, 1), (46, 1), (67, 1)] }, { coefficient := -1, powers := [(11, 1), (27, 1), (42, 1)] }, { coefficient := -1, powers := [(11, 1), (27, 1), (46, 1)] }, { coefficient := 1, powers := [(11, 1), (28, 1), (31, 1), (67, 1)] }, { coefficient := -1, powers := [(11, 1), (28, 1)] }, { coefficient := 2, powers := [(11, 1), (31, 1), (33, 1), (38, 1), (46, 1), (67, 1)] }, { coefficient := 1, powers := [(11, 1), (31, 1), (36, 1), (38, 1), (42, 1), (67, 1)] }, { coefficient := -1, powers := [(15, 1), (22, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (1, 1), (42, 2), (61, 1)] }, { coefficient := 1, powers := [(0, 1), (1, 1), (42, 1), (46, 1), (61, 1)] }, { coefficient := 1, powers := [(0, 1), (1, 1), (42, 1), (52, 1), (61, 1)] }, { coefficient := 1, powers := [(1, 1), (42, 1), (61, 1)] }, { coefficient := 1, powers := [(1, 1), (46, 1), (61, 1)] }, { coefficient := 1, powers := [(1, 1), (52, 1), (61, 1)] }, { coefficient := -2, powers := [(7, 1), (19, 1), (33, 1), (46, 2)] }, { coefficient := -1, powers := [(7, 1), (19, 1), (36, 1), (42, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (26, 1), (42, 2), (45, 1), (52, 1), (61, 1), (65, 1)] }, { coefficient := 1, powers := [(1, 1), (26, 1), (42, 1), (45, 1), (46, 1), (52, 1), (61, 1), (65, 1)] }, { coefficient := 1, powers := [(1, 1), (26, 1), (42, 1), (45, 1), (52, 2), (61, 1), (65, 1)] }, { coefficient := 1, powers := [(1, 1), (26, 1), (42, 1), (47, 1), (52, 1), (61, 1), (65, 1)] }, { coefficient := 1, powers := [(1, 1), (26, 1), (46, 1), (47, 1), (52, 1), (61, 1), (65, 1)] }, { coefficient := 1, powers := [(1, 1), (26, 1), (47, 1), (52, 2), (61, 1), (65, 1)] }, { coefficient := -1, powers := [(1, 1), (42, 2), (45, 1), (53, 1), (61, 1), (65, 1)] }, { coefficient := -1, powers := [(1, 1), (42, 1), (45, 1), (46, 1), (53, 1), (61, 1), (65, 1)] }, { coefficient := -1, powers := [(1, 1), (42, 1), (45, 1), (52, 1), (53, 1), (61, 1), (65, 1)] }, { coefficient := -1, powers := [(1, 1), (42, 1), (47, 1), (53, 1), (61, 1), (65, 1)] }, { coefficient := -1, powers := [(1, 1), (46, 1), (47, 1), (53, 1), (61, 1), (65, 1)] }, { coefficient := -1, powers := [(1, 1), (47, 1), (52, 1), (53, 1), (61, 1), (65, 1)] }, { coefficient := -2, powers := [(3, 1), (7, 1), (33, 1), (46, 1), (59, 1), (61, 1)] }, { coefficient := -1, powers := [(3, 1), (7, 1), (36, 1), (42, 1), (59, 1), (61, 1)] }, { coefficient := 1, powers := [(4, 1), (17, 1), (24, 1), (36, 1), (42, 1), (47, 1), (54, 1)] }, { coefficient := 1, powers := [(4, 1), (17, 1), (24, 1), (36, 1), (46, 1), (47, 1), (54, 1)] }, { coefficient := 1, powers := [(4, 1), (17, 1), (24, 1), (36, 1), (47, 1), (52, 1), (54, 1)] }, { coefficient := 1, powers := [(4, 1), (18, 1), (24, 1), (36, 1), (42, 2), (54, 1)] }, { coefficient := 1, powers := [(4, 1), (18, 1), (24, 1), (36, 1), (42, 1), (46, 1), (54, 1)] }, { coefficient := 1, powers := [(4, 1), (18, 1), (24, 1), (36, 1), (42, 1), (52, 1), (54, 1)] }, { coefficient := 1, powers := [(4, 1), (21, 1), (42, 1), (46, 1), (59, 1)] }, { coefficient := 1, powers := [(4, 1), (21, 1), (46, 2), (59, 1)] }, { coefficient := 1, powers := [(4, 1), (22, 1), (52, 1), (59, 1)] }, { coefficient := -1, powers := [(4, 1), (27, 1), (42, 2), (59, 1)] }, { coefficient := -2, powers := [(4, 1), (27, 1), (42, 1), (46, 1), (59, 1)] }, { coefficient := -1, powers := [(4, 1), (27, 1), (46, 2), (59, 1)] }, { coefficient := -2, powers := [(4, 1), (33, 1), (38, 1), (42, 1), (46, 1), (59, 1)] }, { coefficient := -2, powers := [(4, 1), (33, 1), (38, 1), (46, 2), (59, 1)] }, { coefficient := -2, powers := [(4, 1), (33, 1), (38, 1), (46, 1), (52, 1), (59, 1)] }, { coefficient := -1, powers := [(4, 1), (36, 1), (38, 1), (42, 2), (59, 1)] }, { coefficient := -1, powers := [(4, 1), (36, 1), (38, 1), (42, 1), (46, 1), (59, 1)] }, { coefficient := -1, powers := [(4, 1), (36, 1), (38, 1), (42, 1), (52, 1), (59, 1)] }, { coefficient := 1, powers := [(4, 1), (36, 1), (39, 1), (59, 1)] }, { coefficient := 2, powers := [(7, 1), (19, 1), (33, 1), (42, 1), (46, 1), (61, 1)] }, { coefficient := 2, powers := [(7, 1), (19, 1), (33, 1), (46, 2), (61, 1)] }, { coefficient := 1, powers := [(7, 1), (19, 1), (36, 1), (42, 2), (61, 1)] }, { coefficient := 1, powers := [(7, 1), (19, 1), (36, 1), (42, 1), (46, 1), (61, 1)] }, { coefficient := -2, powers := [(7, 1), (26, 1), (33, 1), (45, 1), (46, 2), (52, 1), (65, 1)] }, { coefficient := -1, powers := [(7, 1), (26, 1), (36, 1), (42, 1), (45, 1), (46, 1), (52, 1), (65, 1)] }, { coefficient := 2, powers := [(7, 1), (33, 1), (45, 1), (46, 2), (53, 1), (65, 1)] }, { coefficient := -2, powers := [(7, 1), (33, 1), (46, 1), (61, 1)] }, { coefficient := 1, powers := [(7, 1), (36, 1), (42, 1), (45, 1), (46, 1), (53, 1), (65, 1)] }, { coefficient := -1, powers := [(7, 1), (36, 1), (42, 1), (61, 1)] }, { coefficient := 1, powers := [(11, 1), (21, 1), (42, 1), (46, 2)] }, { coefficient := 1, powers := [(11, 1), (21, 1), (46, 3)] }, { coefficient := 1, powers := [(11, 1), (22, 1), (46, 1), (52, 1)] }, { coefficient := -1, powers := [(11, 1), (27, 1), (42, 2), (46, 1)] }, { coefficient := -2, powers := [(11, 1), (27, 1), (42, 1), (46, 2)] }, { coefficient := -1, powers := [(11, 1), (27, 1), (46, 3)] }, { coefficient := 1, powers := [(11, 1), (28, 1), (30, 1), (46, 1), (53, 1), (67, 1)] }, { coefficient := 1, powers := [(11, 1), (30, 1), (36, 1), (39, 1), (53, 1), (67, 1)] }, { coefficient := -2, powers := [(11, 1), (33, 1), (38, 1), (42, 1), (46, 2)] }, { coefficient := -2, powers := [(11, 1), (33, 1), (38, 1), (46, 3)] }, { coefficient := -2, powers := [(11, 1), (33, 1), (38, 1), (46, 2), (52, 1)] }, { coefficient := -1, powers := [(11, 1), (36, 1), (38, 1), (42, 2), (46, 1)] }, { coefficient := -1, powers := [(11, 1), (36, 1), (38, 1), (42, 1), (46, 2)] }, { coefficient := -1, powers := [(11, 1), (36, 1), (38, 1), (42, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(11, 1), (36, 1), (39, 1), (46, 1)] }, { coefficient := 1, powers := [(15, 1), (21, 1), (42, 2), (46, 1)] }, { coefficient := 1, powers := [(15, 1), (21, 1), (42, 1), (46, 2)] }, { coefficient := 1, powers := [(15, 1), (22, 1), (42, 1), (52, 1)] }, { coefficient := -1, powers := [(15, 1), (27, 1), (42, 3)] }, { coefficient := -2, powers := [(15, 1), (27, 1), (42, 2), (46, 1)] }, { coefficient := -1, powers := [(15, 1), (27, 1), (42, 1), (46, 2)] }, { coefficient := -2, powers := [(15, 1), (33, 1), (38, 1), (42, 2), (46, 1)] }, { coefficient := -2, powers := [(15, 1), (33, 1), (38, 1), (42, 1), (46, 2)] }, { coefficient := -2, powers := [(15, 1), (33, 1), (38, 1), (42, 1), (46, 1), (52, 1)] }, { coefficient := -1, powers := [(15, 1), (36, 1), (38, 1), (42, 3)] }, { coefficient := -1, powers := [(15, 1), (36, 1), (38, 1), (42, 2), (46, 1)] }, { coefficient := -1, powers := [(15, 1), (36, 1), (38, 1), (42, 2), (52, 1)] }, { coefficient := 1, powers := [(15, 1), (36, 1), (39, 1), (42, 1)] }],
  [{ coefficient := -1, powers := [(1, 1), (42, 2)] }, { coefficient := -2, powers := [(1, 1), (42, 1), (46, 1)] }, { coefficient := -1, powers := [(1, 1), (42, 1), (52, 1)] }, { coefficient := -1, powers := [(1, 1), (46, 2)] }, { coefficient := -1, powers := [(1, 1), (46, 1), (52, 1)] }, { coefficient := -1, powers := [(7, 1), (21, 1), (46, 1), (59, 1)] }, { coefficient := -1, powers := [(7, 1), (22, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (27, 1), (42, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (27, 1), (46, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (28, 1), (59, 1)] }, { coefficient := 2, powers := [(7, 1), (33, 1), (38, 1), (46, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (36, 1), (38, 1), (42, 1), (59, 1)] }, { coefficient := -1, powers := [(11, 1), (28, 1), (46, 1)] }, { coefficient := -1, powers := [(11, 1), (36, 1), (39, 1)] }, { coefficient := -1, powers := [(15, 1), (21, 1), (42, 1), (46, 1)] }, { coefficient := -1, powers := [(15, 1), (21, 1), (46, 2)] }, { coefficient := -1, powers := [(15, 1), (21, 1), (46, 1), (52, 1)] }, { coefficient := -1, powers := [(15, 1), (22, 1), (42, 1)] }, { coefficient := -1, powers := [(15, 1), (22, 1), (46, 1)] }, { coefficient := -1, powers := [(15, 1), (22, 1), (52, 1)] }, { coefficient := 1, powers := [(15, 1), (27, 1), (42, 2)] }, { coefficient := 2, powers := [(15, 1), (27, 1), (42, 1), (46, 1)] }, { coefficient := 1, powers := [(15, 1), (27, 1), (42, 1), (52, 1)] }, { coefficient := 1, powers := [(15, 1), (27, 1), (46, 2)] }, { coefficient := 1, powers := [(15, 1), (27, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(15, 1), (28, 1), (42, 1)] }, { coefficient := 1, powers := [(15, 1), (28, 1), (46, 1)] }, { coefficient := 1, powers := [(15, 1), (28, 1), (52, 1)] }, { coefficient := 2, powers := [(15, 1), (33, 1), (38, 1), (42, 1), (46, 1)] }, { coefficient := 2, powers := [(15, 1), (33, 1), (38, 1), (46, 2)] }, { coefficient := 2, powers := [(15, 1), (33, 1), (38, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(15, 1), (36, 1), (38, 1), (42, 2)] }, { coefficient := 1, powers := [(15, 1), (36, 1), (38, 1), (42, 1), (46, 1)] }, { coefficient := 1, powers := [(15, 1), (36, 1), (38, 1), (42, 1), (52, 1)] }]
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
    (values : Fin 68 → R) :
    ¬ ∀ index : Fin 42,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component18.SelectedLeafB6_6_1_3.selectedHasNoCommonZero

end Krenn.Component18.SelectedLeafB6_6_1_3
