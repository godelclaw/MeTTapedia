import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component25.SelectedLeafB5_7_7

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "d437b685d0f6364223c4b7041becf639f2c6ac1bf43276a2ae6737c4089fe50f"
def certificateSHA256 : String := "2ae523bd3ac3bb00b776f7d4968952988655dfbac2b1fe1fa40bdda71e23c2fb"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 44 → Fin 665 := ![
  2,
  14,
  15,
  16,
  17,
  21,
  142,
  152,
  162,
  167,
  168,
  170,
  171,
  173,
  175,
  251,
  294,
  300,
  307,
  311,
  312,
  319,
  388,
  411,
  429,
  430,
  433,
  435,
  438,
  439,
  450,
  501,
  579,
  580,
  588,
  648,
  655,
  656,
  658,
  659,
  660,
  662,
  663,
  664
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 44 → SparsePoly (Fin 69) := ![
  [{ coefficient := 1, powers := [(9, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (54, 1)] }, { coefficient := 1, powers := [(18, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (29, 1)] }, { coefficient := 1, powers := [(29, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (18, 1)] }, { coefficient := 1, powers := [(16, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (46, 1)] }, { coefficient := -1, powers := [(28, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (54, 1)] }, { coefficient := 1, powers := [(29, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (43, 1)] }, { coefficient := 1, powers := [(27, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (53, 1)] }, { coefficient := -1, powers := [(28, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (40, 1)] }, { coefficient := 1, powers := [(29, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(57, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (22, 1), (53, 1)] }, { coefficient := 1, powers := [(28, 1), (42, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (50, 1)] }, { coefficient := 1, powers := [(18, 1), (50, 1)] }, { coefficient := 1, powers := [(24, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (60, 1)] }, { coefficient := 1, powers := [(12, 1), (57, 1)] }, { coefficient := 1, powers := [(17, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (22, 1)] }, { coefficient := 1, powers := [(22, 1), (55, 1)] }, { coefficient := 1, powers := [(27, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (52, 1)] }, { coefficient := 1, powers := [(23, 1), (56, 1)] }, { coefficient := 1, powers := [(28, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (57, 1)] }, { coefficient := 1, powers := [(29, 1), (48, 1)] }, { coefficient := 1, powers := [(35, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1), (50, 1)] }, { coefficient := 1, powers := [(24, 1), (45, 1), (50, 1)] }, { coefficient := 1, powers := [(50, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (18, 1), (56, 1)] }, { coefficient := 1, powers := [(12, 1)] }, { coefficient := 1, powers := [(16, 1), (18, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(28, 1), (43, 1), (54, 1)] }, { coefficient := 1, powers := [(28, 1), (50, 1), (57, 1)] }, { coefficient := 1, powers := [(29, 1), (46, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (47, 1)] }, { coefficient := 1, powers := [(5, 1), (27, 1), (59, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (48, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1), (48, 1)] }, { coefficient := 1, powers := [(17, 1), (23, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (52, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1), (52, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1), (56, 1)] }, { coefficient := 1, powers := [(16, 1), (28, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1)] }, { coefficient := 1, powers := [(12, 1), (29, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (59, 1)] }, { coefficient := 1, powers := [(16, 1), (19, 1), (52, 1)] }, { coefficient := 1, powers := [(16, 1), (19, 1), (56, 1)] }, { coefficient := 1, powers := [(16, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (60, 1)] }, { coefficient := 1, powers := [(12, 1), (48, 1)] }, { coefficient := 1, powers := [(17, 1), (19, 1), (53, 1)] }, { coefficient := 1, powers := [(17, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (54, 1)] }, { coefficient := 1, powers := [(29, 1), (41, 1)] }, { coefficient := 1, powers := [(29, 1), (47, 1), (50, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (32, 1), (56, 1)] }, { coefficient := 1, powers := [(22, 1), (50, 1), (56, 1)] }, { coefficient := 1, powers := [(22, 1), (53, 1)] }, { coefficient := 1, powers := [(28, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (52, 1)] }, { coefficient := 1, powers := [(3, 1), (59, 1)] }, { coefficient := 1, powers := [(18, 1), (52, 1)] }, { coefficient := 1, powers := [(18, 1), (56, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (38, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (41, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (48, 1), (54, 1)] }, { coefficient := 1, powers := [(19, 1), (43, 1), (54, 1)] }, { coefficient := 1, powers := [(19, 1), (50, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (40, 1)] }, { coefficient := 1, powers := [(16, 1), (28, 1), (57, 1)] }, { coefficient := 1, powers := [(16, 1), (29, 1), (46, 1)] }, { coefficient := 1, powers := [(17, 1), (29, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (41, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (47, 1), (53, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (56, 1)] }, { coefficient := 1, powers := [(12, 1), (23, 1), (56, 1)] }, { coefficient := 1, powers := [(12, 1), (28, 1), (47, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1), (53, 1)] }, { coefficient := 1, powers := [(16, 1), (28, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (41, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (48, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (23, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (48, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(12, 1), (23, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1), (29, 1), (48, 1)] }, { coefficient := 1, powers := [(12, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(17, 1), (23, 1), (54, 1)] }, { coefficient := 1, powers := [(17, 1), (29, 1), (41, 1)] }, { coefficient := 1, powers := [(17, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (61, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(39, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(40, 1), (64, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(55, 1), (66, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(56, 1), (67, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(57, 1), (68, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 44 → SparsePoly (Fin 69) := ![
  [{ coefficient := -2, powers := [(3, 1), (12, 1), (29, 1), (48, 1), (59, 1), (63, 1), (68, 1)] }, { coefficient := 1, powers := [(3, 1), (17, 1), (29, 1), (41, 1), (45, 1), (59, 1), (63, 1), (64, 1), (68, 1)] }, { coefficient := -1, powers := [(3, 1), (17, 1), (29, 1), (41, 1), (59, 1), (63, 1), (68, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (22, 1), (48, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (22, 1), (52, 1), (62, 1), (68, 1)] }, { coefficient := 1, powers := [(0, 1), (22, 1), (56, 1), (62, 1), (68, 1)] }, { coefficient := 1, powers := [(0, 1), (28, 1), (62, 1), (68, 1)] }, { coefficient := -1, powers := [(3, 1), (19, 1), (27, 1), (52, 1), (53, 1), (57, 1), (59, 1), (67, 1), (68, 1)] }, { coefficient := -1, powers := [(3, 1), (19, 1), (27, 1), (53, 1), (56, 1), (57, 1), (59, 1), (67, 1), (68, 1)] }, { coefficient := 1, powers := [(3, 1), (23, 1), (24, 1), (52, 1), (53, 1), (57, 1), (59, 1), (67, 1), (68, 1)] }, { coefficient := 1, powers := [(3, 1), (23, 1), (24, 1), (53, 1), (57, 1), (59, 1), (68, 1)] }, { coefficient := -1, powers := [(3, 1), (23, 1), (43, 1), (54, 1), (59, 1), (68, 1)] }, { coefficient := -1, powers := [(3, 1), (28, 1), (41, 1), (57, 1), (59, 1), (67, 1), (68, 1)] }, { coefficient := 1, powers := [(3, 1), (28, 1), (41, 1), (59, 1), (64, 1)] }, { coefficient := 1, powers := [(3, 1), (29, 1), (41, 1), (46, 1), (59, 1), (64, 1), (68, 1)] }],
  [{ coefficient := 2, powers := [(2, 1), (3, 1), (40, 1), (48, 1), (54, 1), (59, 1), (68, 1)] }, { coefficient := -1, powers := [(3, 1), (12, 1), (23, 1), (52, 1), (56, 1), (57, 1), (59, 1), (67, 1), (68, 1)] }, { coefficient := -1, powers := [(3, 1), (12, 1), (23, 1), (56, 1), (57, 1), (59, 1), (68, 1)] }, { coefficient := 2, powers := [(3, 1), (17, 1), (23, 1), (40, 1), (54, 1), (59, 1), (68, 1)] }, { coefficient := 2, powers := [(5, 1), (22, 1), (45, 1), (50, 1), (57, 1), (59, 1), (68, 1)] }, { coefficient := -1, powers := [(52, 1), (68, 1)] }, { coefficient := -1, powers := [(56, 1), (68, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (3, 1), (43, 1), (54, 1), (59, 1), (61, 1), (68, 1)] }, { coefficient := 1, powers := [(2, 1), (3, 1), (50, 1), (59, 1), (61, 1)] }, { coefficient := 1, powers := [(3, 1), (17, 1), (29, 1), (53, 1), (59, 1), (68, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (17, 1), (50, 1), (59, 1)] }],
  [{ coefficient := -2, powers := [(2, 1), (3, 1), (40, 1), (48, 1), (59, 1)] }, { coefficient := -2, powers := [(3, 1), (17, 1), (23, 1), (40, 1), (59, 1)] }],
  [{ coefficient := 2, powers := [(3, 1), (12, 1), (48, 1), (59, 1), (63, 1)] }, { coefficient := -1, powers := [(3, 1), (17, 1), (41, 1), (45, 1), (59, 1), (63, 1), (64, 1)] }, { coefficient := 1, powers := [(3, 1), (17, 1), (41, 1), (59, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (23, 1), (52, 1), (53, 1), (57, 1), (59, 1), (67, 1)] }, { coefficient := -1, powers := [(3, 1), (23, 1), (53, 1), (57, 1), (59, 1)] }],
  [{ coefficient := 2, powers := [(5, 1), (54, 1), (57, 1), (59, 1), (67, 1), (68, 1)] }],
  [{ coefficient := -2, powers := [(5, 1), (46, 1), (57, 1), (59, 1), (67, 1), (68, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (16, 1), (54, 1), (59, 1)] }],
  [{ coefficient := -2, powers := [(5, 1), (42, 1), (57, 1), (59, 1), (66, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (17, 1), (41, 1), (59, 1), (64, 1)] }],
  [{ coefficient := 2, powers := [(2, 1), (3, 1), (48, 1), (54, 1), (59, 1), (68, 1)] }, { coefficient := 2, powers := [(3, 1), (17, 1), (23, 1), (54, 1), (59, 1), (68, 1)] }],
  [{ coefficient := -2, powers := [(5, 1), (57, 1), (59, 1), (66, 1), (67, 1)] }],
  [{ coefficient := -2, powers := [(5, 1), (22, 1), (45, 1), (57, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (23, 1), (59, 1)] }],
  [{ coefficient := 2, powers := [(5, 1), (53, 1), (57, 1), (59, 1), (66, 1), (67, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (12, 1), (57, 1), (59, 1), (67, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (12, 1), (59, 1)] }],
  [{ coefficient := 2, powers := [(5, 1), (22, 1), (57, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (23, 1), (52, 1), (57, 1), (59, 1), (67, 1)] }, { coefficient := 1, powers := [(3, 1), (23, 1), (57, 1), (59, 1)] }],
  [{ coefficient := 2, powers := [(5, 1), (57, 1), (59, 1), (67, 1), (68, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (53, 1), (57, 1), (59, 1), (67, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (54, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (48, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (27, 1), (53, 1), (57, 1), (59, 1), (67, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (29, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (17, 1), (59, 1)] }],
  [{ coefficient := -2, powers := [(5, 1), (57, 1), (59, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [] }],
  [{ coefficient := -1, powers := [(2, 1), (3, 1), (59, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (41, 1), (59, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (57, 1), (59, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (3, 1), (38, 1), (59, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (3, 1), (41, 1), (57, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (3, 1), (48, 1), (54, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (52, 1)] }],
  [{ coefficient := -2, powers := [(3, 1), (12, 1), (29, 1), (48, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (17, 1), (29, 1), (41, 1), (45, 1), (59, 1), (64, 1)] }, { coefficient := -1, powers := [(3, 1), (17, 1), (29, 1), (41, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (3, 1), (41, 1), (57, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (8, 1), (35, 1), (41, 1), (59, 1)] }],
  [{ coefficient := -2, powers := [(5, 1), (22, 1), (53, 1), (57, 1), (59, 1), (67, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (3, 1), (41, 1), (57, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (5, 1), (32, 1), (57, 1), (59, 1)] }, { coefficient := 2, powers := [(5, 1), (22, 1), (50, 1), (57, 1), (59, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (2, 1), (3, 1), (40, 1), (48, 1), (54, 1), (59, 1)] }, { coefficient := -2, powers := [(0, 1), (3, 1), (17, 1), (23, 1), (40, 1), (54, 1), (59, 1)] }, { coefficient := -1, powers := [(0, 1), (16, 1), (22, 1), (52, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 1), (16, 1), (22, 1), (56, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 1), (16, 1), (28, 1), (62, 1)] }, { coefficient := -2, powers := [(2, 1), (3, 1), (18, 1), (40, 1), (48, 1), (54, 1), (59, 1)] }, { coefficient := -1, powers := [(2, 1), (3, 1), (19, 1), (43, 1), (54, 1), (59, 1), (61, 1)] }, { coefficient := -2, powers := [(2, 1), (3, 1), (48, 1), (54, 1), (59, 1)] }, { coefficient := 2, powers := [(3, 1), (9, 1), (12, 1), (29, 1), (48, 1), (59, 1), (63, 1)] }, { coefficient := -1, powers := [(3, 1), (9, 1), (17, 1), (29, 1), (41, 1), (45, 1), (59, 1), (63, 1), (64, 1)] }, { coefficient := 1, powers := [(3, 1), (9, 1), (17, 1), (29, 1), (41, 1), (59, 1), (63, 1)] }, { coefficient := 1, powers := [(3, 1), (12, 1), (18, 1), (23, 1), (52, 1), (56, 1), (57, 1), (59, 1), (67, 1)] }, { coefficient := 1, powers := [(3, 1), (12, 1), (18, 1), (23, 1), (56, 1), (57, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (16, 1), (19, 1), (27, 1), (52, 1), (53, 1), (57, 1), (59, 1), (67, 1)] }, { coefficient := 1, powers := [(3, 1), (16, 1), (19, 1), (27, 1), (53, 1), (56, 1), (57, 1), (59, 1), (67, 1)] }, { coefficient := -1, powers := [(3, 1), (16, 1), (23, 1), (24, 1), (52, 1), (53, 1), (57, 1), (59, 1), (67, 1)] }, { coefficient := -1, powers := [(3, 1), (16, 1), (23, 1), (24, 1), (53, 1), (57, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (16, 1), (23, 1), (43, 1), (54, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (16, 1), (28, 1), (41, 1), (57, 1), (59, 1), (67, 1)] }, { coefficient := -1, powers := [(3, 1), (16, 1), (29, 1), (41, 1), (46, 1), (59, 1), (64, 1)] }, { coefficient := -2, powers := [(3, 1), (17, 1), (18, 1), (23, 1), (40, 1), (54, 1), (59, 1)] }, { coefficient := -1, powers := [(3, 1), (17, 1), (19, 1), (29, 1), (53, 1), (59, 1)] }, { coefficient := -2, powers := [(3, 1), (17, 1), (23, 1), (54, 1), (59, 1)] }, { coefficient := -2, powers := [(5, 1), (18, 1), (22, 1), (45, 1), (50, 1), (57, 1), (59, 1)] }, { coefficient := -2, powers := [(5, 1), (28, 1), (50, 1), (57, 1), (59, 1), (67, 1)] }, { coefficient := 1, powers := [(18, 1), (52, 1)] }, { coefficient := 1, powers := [(18, 1), (56, 1)] }]
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
    (values : Fin 69 → R) :
    ¬ ∀ index : Fin 44,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component25.SelectedLeafB5_7_7.selectedHasNoCommonZero

end Krenn.Component25.SelectedLeafB5_7_7
