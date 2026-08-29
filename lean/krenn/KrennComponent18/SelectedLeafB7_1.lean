import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component18.SelectedLeafB7_1

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "d04e97381169369803e01c0e64b96a81151f7faf7cb6e6989d12c405b759c84f"
def certificateSHA256 : String := "79c017e0d4b858f32fdcd92c0213466c95d53440e0aa6bfbbba29bd155db2d07"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 45 → Fin 664 := ![
  1,
  10,
  12,
  16,
  17,
  19,
  20,
  25,
  167,
  168,
  169,
  295,
  300,
  301,
  302,
  313,
  318,
  327,
  408,
  409,
  424,
  433,
  437,
  443,
  449,
  452,
  463,
  478,
  515,
  562,
  580,
  584,
  585,
  602,
  603,
  609,
  645,
  649,
  655,
  657,
  658,
  660,
  661,
  662,
  663
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 45 → SparsePoly (Fin 65) := ![
  [{ coefficient := 1, powers := [(6, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(43, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (45, 1)] }, { coefficient := 1, powers := [(29, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (53, 1)] }, { coefficient := 1, powers := [(31, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1), (56, 1)] }, { coefficient := 1, powers := [(43, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (49, 1)] }, { coefficient := 1, powers := [(20, 1), (45, 1)] }, { coefficient := 1, powers := [(25, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (44, 1)] }, { coefficient := 1, powers := [(17, 1), (23, 1), (55, 1)] }, { coefficient := 1, powers := [(17, 1), (29, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (60, 1)] }, { coefficient := 1, powers := [(13, 1), (49, 1)] }, { coefficient := 1, powers := [(18, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (58, 1)] }, { coefficient := 1, powers := [(9, 1), (55, 1)] }, { coefficient := 1, powers := [(14, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (42, 1)] }, { coefficient := 1, powers := [(14, 1), (52, 1)] }, { coefficient := 1, powers := [(35, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (54, 1)] }, { coefficient := 1, powers := [(31, 1), (43, 1)] }, { coefficient := 1, powers := [(34, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (49, 1), (52, 1)] }, { coefficient := 1, powers := [(20, 1), (45, 1), (52, 1)] }, { coefficient := 1, powers := [(49, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (25, 1), (42, 1)] }, { coefficient := 1, powers := [(17, 1), (25, 1), (46, 1)] }, { coefficient := 1, powers := [(17, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (25, 1), (47, 1)] }, { coefficient := 1, powers := [(18, 1), (25, 1), (42, 1)] }, { coefficient := 1, powers := [(18, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1)] }, { coefficient := 1, powers := [(25, 1), (42, 1), (45, 1)] }, { coefficient := 1, powers := [(25, 1), (47, 1)] }, { coefficient := 1, powers := [(45, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (49, 1)] }, { coefficient := 1, powers := [(5, 1), (37, 1)] }, { coefficient := 1, powers := [(17, 1), (29, 1), (49, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1)] }, { coefficient := 1, powers := [(13, 1), (31, 1)] }, { coefficient := 1, powers := [(17, 1), (23, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (60, 1)] }, { coefficient := 1, powers := [(13, 1), (26, 1), (47, 1)] }, { coefficient := 1, powers := [(13, 1), (57, 1)] }, { coefficient := 1, powers := [(18, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (42, 1)] }, { coefficient := 1, powers := [(17, 1), (46, 1)] }, { coefficient := 1, powers := [(17, 1), (52, 1)] }, { coefficient := 1, powers := [(17, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (39, 1), (58, 1)] }, { coefficient := 1, powers := [(9, 1), (35, 1), (39, 1)] }, { coefficient := 1, powers := [(14, 1), (32, 1), (39, 1)] }, { coefficient := 1, powers := [(14, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1), (52, 1)] }, { coefficient := 1, powers := [(42, 1), (45, 1)] }, { coefficient := 1, powers := [(45, 1), (52, 1)] }, { coefficient := 1, powers := [(47, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1)] }, { coefficient := 1, powers := [(17, 1), (23, 1)] }, { coefficient := 1, powers := [(17, 1), (29, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (24, 1), (60, 1)] }, { coefficient := 1, powers := [(6, 1), (34, 1), (49, 1)] }, { coefficient := 1, powers := [(6, 1), (37, 1), (43, 1)] }, { coefficient := 1, powers := [(29, 1), (43, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (45, 1), (53, 1)] }, { coefficient := 1, powers := [(24, 1), (57, 1)] }, { coefficient := 1, powers := [(31, 1), (49, 1)] }, { coefficient := 1, powers := [(37, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1)] }, { coefficient := 1, powers := [(6, 1), (59, 1)] }, { coefficient := 1, powers := [(25, 1), (42, 1)] }, { coefficient := 1, powers := [(25, 1), (46, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (40, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (43, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (49, 1), (54, 1)] }, { coefficient := 1, powers := [(20, 1), (45, 1), (54, 1)] }, { coefficient := 1, powers := [(26, 1), (43, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1), (55, 1)] }, { coefficient := 1, powers := [(6, 1), (35, 1), (42, 1)] }, { coefficient := 1, powers := [(14, 1), (25, 1), (42, 1)] }, { coefficient := 1, powers := [(14, 1)] }, { coefficient := 1, powers := [(55, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1)] }, { coefficient := 1, powers := [(3, 1), (35, 1)] }, { coefficient := 1, powers := [(14, 1), (19, 1)] }, { coefficient := 1, powers := [(19, 1), (55, 1)] }, { coefficient := 1, powers := [(25, 1), (44, 1)] }, { coefficient := 1, powers := [(35, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (50, 1)] }, { coefficient := 1, powers := [(6, 1), (32, 1)] }, { coefficient := 1, powers := [(9, 1), (25, 1)] }, { coefficient := 1, powers := [(19, 1), (50, 1)] }, { coefficient := 1, powers := [(25, 1), (41, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (47, 1), (53, 1)] }, { coefficient := 1, powers := [(26, 1), (42, 1), (45, 1)] }, { coefficient := 1, powers := [(26, 1), (47, 1)] }, { coefficient := 1, powers := [(45, 1), (53, 1)] }, { coefficient := 1, powers := [(57, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (39, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (42, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(42, 1)] }, { coefficient := 1, powers := [(46, 1)] }, { coefficient := 1, powers := [(52, 1)] }, { coefficient := 1, powers := [(56, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (39, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (42, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(17, 1), (30, 1), (42, 1)] }, { coefficient := 1, powers := [(17, 1), (30, 1), (46, 1)] }, { coefficient := 1, powers := [(17, 1), (30, 1), (52, 1)] }, { coefficient := 1, powers := [(17, 1), (30, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (38, 1), (58, 1)] }, { coefficient := 1, powers := [(0, 1), (41, 1), (55, 1)] }, { coefficient := 1, powers := [(0, 1), (44, 1), (50, 1)] }, { coefficient := 1, powers := [(3, 1), (25, 1), (58, 1)] }, { coefficient := 1, powers := [(3, 1), (32, 1), (55, 1)] }, { coefficient := 1, powers := [(3, 1), (35, 1), (50, 1)] }, { coefficient := 1, powers := [(6, 1), (19, 1), (58, 1)] }, { coefficient := 1, powers := [(6, 1), (32, 1), (44, 1)] }, { coefficient := 1, powers := [(6, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(9, 1), (19, 1), (55, 1)] }, { coefficient := 1, powers := [(9, 1), (25, 1), (44, 1)] }, { coefficient := 1, powers := [(9, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(14, 1), (19, 1), (50, 1)] }, { coefficient := 1, powers := [(14, 1), (25, 1), (41, 1)] }, { coefficient := 1, powers := [(14, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (40, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (43, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (49, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (37, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (49, 1)] }, { coefficient := 1, powers := [(8, 1), (37, 1), (43, 1)] }, { coefficient := 1, powers := [(13, 1), (24, 1), (57, 1)] }, { coefficient := 1, powers := [(13, 1), (31, 1), (49, 1)] }, { coefficient := 1, powers := [(13, 1), (37, 1), (40, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (54, 1)] }, { coefficient := 1, powers := [(18, 1), (31, 1), (43, 1)] }, { coefficient := 1, powers := [(18, 1), (34, 1), (40, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (61, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(41, 1)] }],
  [{ coefficient := 1, powers := [(42, 1)] }],
  [{ coefficient := 1, powers := [(43, 1), (64, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 45 → SparsePoly (Fin 65) := ![
  [{ coefficient := 1, powers := [(0, 1), (8, 1), (24, 1), (43, 1), (52, 1), (59, 1), (64, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (43, 1), (59, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (6, 1), (24, 1), (26, 1), (52, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (24, 1), (26, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(0, 3), (39, 1), (50, 1), (59, 1), (64, 1)] }, { coefficient := -1, powers := [(0, 2), (3, 1), (32, 1), (39, 1), (59, 1), (64, 1)] }, { coefficient := -1, powers := [(0, 2), (6, 1), (32, 1), (39, 1), (59, 1), (64, 1)] }, { coefficient := -1, powers := [(0, 2), (9, 1), (25, 1), (39, 1), (59, 1), (64, 1)] }, { coefficient := -1, powers := [(0, 2), (19, 1), (39, 1), (50, 1), (59, 1), (64, 1)] }, { coefficient := -1, powers := [(0, 2), (32, 1), (38, 1), (39, 1), (59, 1), (64, 1)] }, { coefficient := 1, powers := [(0, 2), (38, 1), (50, 1), (52, 1), (59, 1), (64, 1)] }, { coefficient := -1, powers := [(0, 2), (38, 1), (51, 1), (59, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(0, 2), (6, 1), (29, 1), (32, 1), (39, 1), (59, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(0, 2), (6, 1), (23, 1), (32, 1), (39, 1), (59, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (6, 1), (17, 1), (49, 1), (52, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (17, 1), (49, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(0, 2), (2, 1), (6, 1), (26, 1), (43, 1), (47, 1), (52, 2), (59, 1), (61, 1), (64, 1)] }, { coefficient := 1, powers := [(0, 2), (2, 1), (6, 1), (43, 1), (47, 1), (52, 1), (53, 1), (59, 1), (61, 1), (64, 1)] }, { coefficient := 1, powers := [(0, 2), (3, 1), (39, 1), (58, 1), (59, 1), (64, 1)] }, { coefficient := 1, powers := [(0, 2), (9, 1), (39, 1), (44, 1), (59, 1), (64, 1)] }, { coefficient := -1, powers := [(0, 2), (17, 1), (23, 1), (39, 1), (46, 1), (59, 1), (63, 1), (64, 1)] }, { coefficient := -1, powers := [(0, 2), (17, 1), (29, 1), (39, 1), (46, 1), (59, 1), (63, 1), (64, 1)] }, { coefficient := -1, powers := [(0, 2), (39, 1), (44, 1), (50, 1), (59, 1), (64, 1)] }, { coefficient := 1, powers := [(0, 1), (2, 1), (6, 1), (26, 1), (43, 1), (47, 1), (52, 2), (59, 1), (64, 1)] }, { coefficient := -1, powers := [(0, 1), (2, 1), (6, 1), (26, 1), (43, 1), (47, 1), (52, 1), (59, 1), (61, 1), (64, 1)] }, { coefficient := -1, powers := [(0, 1), (2, 1), (6, 1), (43, 1), (47, 1), (52, 1), (53, 1), (59, 1), (64, 1)] }, { coefficient := 1, powers := [(0, 1), (2, 1), (6, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1), (64, 1)] }, { coefficient := 1, powers := [(0, 1), (2, 1), (6, 1), (49, 1), (52, 2), (54, 1), (59, 1), (64, 1)] }, { coefficient := -1, powers := [(0, 1), (2, 1), (6, 1), (49, 1), (52, 1), (54, 1), (59, 1), (61, 1), (64, 1)] }, { coefficient := 1, powers := [(0, 1), (5, 1), (6, 1), (26, 1), (34, 1), (47, 1), (52, 2), (59, 1), (64, 1)] }, { coefficient := -1, powers := [(0, 1), (5, 1), (6, 1), (34, 1), (47, 1), (52, 1), (53, 1), (59, 1), (64, 1)] }, { coefficient := 1, powers := [(0, 1), (6, 1), (8, 1), (34, 1), (43, 1), (49, 1), (52, 2), (59, 1), (64, 2)] }, { coefficient := -1, powers := [(0, 1), (6, 1), (13, 1), (24, 1), (26, 1), (47, 1), (52, 2), (59, 1), (64, 1)] }, { coefficient := 1, powers := [(0, 1), (6, 1), (13, 1), (24, 1), (47, 1), (52, 1), (53, 1), (59, 1), (64, 1)] }, { coefficient := 2, powers := [(0, 1), (6, 1), (13, 1), (31, 1), (49, 1), (52, 2), (59, 1), (64, 1)] }, { coefficient := 1, powers := [(0, 1), (6, 1), (17, 1), (23, 1), (46, 1), (52, 1), (59, 1), (63, 1), (64, 1)] }, { coefficient := -2, powers := [(0, 1), (6, 1), (17, 1), (24, 1), (47, 1), (52, 1), (54, 1), (59, 1), (64, 1)] }, { coefficient := 1, powers := [(0, 1), (6, 1), (17, 1), (29, 1), (46, 1), (52, 1), (59, 1), (63, 1), (64, 1)] }, { coefficient := -1, powers := [(0, 1), (6, 1), (17, 1), (31, 1), (43, 1), (47, 1), (52, 1), (59, 1), (64, 1)] }, { coefficient := 1, powers := [(0, 1), (17, 1), (23, 1), (46, 1), (52, 1), (63, 1), (64, 1)] }, { coefficient := 1, powers := [(0, 1), (17, 1), (29, 1), (46, 1), (52, 1), (63, 1), (64, 1)] }, { coefficient := 1, powers := [(0, 1), (38, 1), (46, 1), (52, 1), (59, 1), (64, 1)] }, { coefficient := 1, powers := [(2, 1), (6, 1), (26, 1), (43, 1), (47, 1), (52, 1), (59, 1), (64, 1)] }, { coefficient := -1, powers := [(2, 1), (6, 1), (43, 1), (47, 1), (53, 1), (59, 1), (64, 1)] }, { coefficient := 1, powers := [(2, 1), (6, 1), (49, 1), (52, 1), (54, 1), (59, 1), (64, 1)] }, { coefficient := -1, powers := [(2, 1), (6, 1), (49, 1), (54, 1), (59, 1), (61, 1), (64, 1)] }, { coefficient := 1, powers := [(5, 1), (6, 1), (26, 1), (34, 1), (47, 1), (52, 1), (59, 1), (64, 1)] }, { coefficient := -1, powers := [(5, 1), (6, 1), (34, 1), (47, 1), (53, 1), (59, 1), (64, 1)] }, { coefficient := 1, powers := [(6, 1), (8, 1), (34, 1), (43, 1), (49, 1), (52, 1), (59, 1), (64, 2)] }, { coefficient := -1, powers := [(6, 1), (13, 1), (24, 1), (26, 1), (47, 1), (52, 1), (59, 1), (64, 1)] }, { coefficient := 1, powers := [(6, 1), (13, 1), (24, 1), (47, 1), (53, 1), (59, 1), (64, 1)] }, { coefficient := 2, powers := [(6, 1), (13, 1), (31, 1), (49, 1), (52, 1), (59, 1), (64, 1)] }, { coefficient := -2, powers := [(6, 1), (17, 1), (24, 1), (47, 1), (54, 1), (59, 1), (64, 1)] }, { coefficient := -1, powers := [(6, 1), (17, 1), (31, 1), (43, 1), (47, 1), (59, 1), (64, 1)] }, { coefficient := -1, powers := [(46, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (2, 1), (6, 1), (26, 1), (52, 1), (59, 1), (61, 1)] }, { coefficient := -1, powers := [(0, 1), (6, 1), (13, 1), (31, 1), (48, 1), (52, 1), (59, 1), (64, 1)] }, { coefficient := -1, powers := [(0, 1), (6, 1), (17, 1), (24, 1), (52, 1), (54, 1), (59, 1), (64, 1)] }, { coefficient := 1, powers := [(0, 1), (8, 1), (29, 1), (43, 1), (52, 1), (59, 1), (64, 1)] }, { coefficient := 1, powers := [(2, 1), (6, 1), (26, 1), (59, 1), (61, 1)] }, { coefficient := -1, powers := [(6, 1), (13, 1), (31, 1), (48, 1), (59, 1), (64, 1)] }, { coefficient := -1, powers := [(6, 1), (17, 1), (24, 1), (54, 1), (59, 1), (64, 1)] }, { coefficient := 1, powers := [(8, 1), (29, 1), (43, 1), (59, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (6, 1), (17, 1), (52, 1), (54, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (17, 1), (54, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (6, 1), (13, 1), (45, 1), (52, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (13, 1), (45, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (61, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (2, 1), (6, 1), (52, 2), (54, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (2, 1), (6, 1), (52, 1), (54, 1), (59, 1), (61, 1)] }, { coefficient := -1, powers := [(0, 1), (6, 1), (8, 1), (34, 1), (43, 1), (52, 2), (59, 1), (64, 1)] }, { coefficient := -2, powers := [(0, 1), (6, 1), (13, 1), (31, 1), (52, 2), (59, 1)] }, { coefficient := -1, powers := [(2, 1), (6, 1), (52, 1), (54, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (6, 1), (54, 1), (59, 1), (61, 1)] }, { coefficient := -1, powers := [(6, 1), (8, 1), (34, 1), (43, 1), (52, 1), (59, 1), (64, 1)] }, { coefficient := -2, powers := [(6, 1), (13, 1), (31, 1), (52, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(0, 2), (6, 1), (32, 1), (39, 1), (59, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (6, 1), (31, 1), (52, 1), (59, 1)] }, { coefficient := -1, powers := [(6, 1), (31, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(0, 2), (19, 1), (39, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(0, 2), (38, 1), (50, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (6, 1), (18, 1), (52, 1), (59, 1)] }, { coefficient := -1, powers := [(6, 1), (18, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (2, 1), (6, 1), (52, 1), (54, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (6, 1), (8, 1), (34, 1), (43, 1), (52, 1), (59, 1), (64, 1)] }, { coefficient := 2, powers := [(0, 1), (6, 1), (13, 1), (31, 1), (52, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (6, 1), (54, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (8, 1), (34, 1), (43, 1), (59, 1), (64, 1)] }, { coefficient := 2, powers := [(6, 1), (13, 1), (31, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(0, 2), (23, 1), (39, 1), (59, 1), (63, 1)] }, { coefficient := 1, powers := [(0, 2), (29, 1), (39, 1), (59, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (6, 1), (23, 1), (52, 1), (59, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (6, 1), (29, 1), (52, 1), (59, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (23, 1), (52, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (29, 1), (52, 1), (63, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (6, 1), (24, 1), (52, 1), (54, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (6, 1), (31, 1), (43, 1), (52, 1), (59, 1)] }, { coefficient := 2, powers := [(6, 1), (24, 1), (54, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (31, 1), (43, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(0, 2), (2, 1), (6, 1), (26, 1), (43, 1), (52, 2), (59, 1), (61, 1)] }, { coefficient := -1, powers := [(0, 2), (2, 1), (6, 1), (43, 1), (52, 1), (53, 1), (59, 1), (61, 1)] }, { coefficient := -1, powers := [(0, 1), (2, 1), (6, 1), (26, 1), (43, 1), (52, 2), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (2, 1), (6, 1), (26, 1), (43, 1), (52, 1), (59, 1), (61, 1)] }, { coefficient := 1, powers := [(0, 1), (2, 1), (6, 1), (43, 1), (52, 1), (53, 1), (59, 1)] }, { coefficient := -1, powers := [(0, 1), (2, 1), (6, 1), (43, 1), (53, 1), (59, 1), (61, 1)] }, { coefficient := -1, powers := [(0, 1), (5, 1), (6, 1), (26, 1), (34, 1), (52, 2), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (5, 1), (6, 1), (34, 1), (52, 1), (53, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (6, 1), (13, 1), (24, 1), (26, 1), (52, 2), (59, 1)] }, { coefficient := -1, powers := [(0, 1), (6, 1), (13, 1), (24, 1), (52, 1), (53, 1), (59, 1)] }, { coefficient := -1, powers := [(2, 1), (6, 1), (26, 1), (43, 1), (52, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (6, 1), (43, 1), (53, 1), (59, 1)] }, { coefficient := -1, powers := [(5, 1), (6, 1), (26, 1), (34, 1), (52, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (6, 1), (34, 1), (53, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (13, 1), (24, 1), (26, 1), (52, 1), (59, 1)] }, { coefficient := -1, powers := [(6, 1), (13, 1), (24, 1), (53, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (6, 1), (52, 1), (54, 1), (59, 1)] }, { coefficient := -1, powers := [(6, 1), (54, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (6, 1), (49, 1), (52, 1), (59, 1)] }, { coefficient := -1, powers := [(6, 1), (49, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (6, 1), (24, 1), (52, 1), (59, 1)] }, { coefficient := -1, powers := [(6, 1), (24, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(0, 2), (30, 1), (38, 1), (59, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 2), (30, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(0, 2), (38, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(0, 2), (2, 1), (6, 1), (26, 1), (43, 1), (52, 1), (59, 1), (61, 1)] }, { coefficient := 1, powers := [(0, 1), (2, 1), (6, 1), (26, 1), (43, 1), (52, 1), (59, 1)] }, { coefficient := -1, powers := [(0, 1), (2, 1), (6, 1), (26, 1), (43, 1), (59, 1), (61, 1)] }, { coefficient := 1, powers := [(0, 1), (5, 1), (6, 1), (26, 1), (34, 1), (52, 1), (59, 1)] }, { coefficient := -1, powers := [(0, 1), (6, 1), (13, 1), (24, 1), (26, 1), (52, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (6, 1), (26, 1), (43, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (6, 1), (26, 1), (34, 1), (59, 1)] }, { coefficient := -1, powers := [(6, 1), (13, 1), (24, 1), (26, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(0, 2), (39, 1), (59, 1), (63, 1)] }, { coefficient := 1, powers := [(0, 1), (6, 1), (52, 1), (59, 1), (63, 1)] }, { coefficient := 1, powers := [(0, 1), (52, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (8, 1), (43, 1), (52, 1), (59, 1), (64, 1)] }, { coefficient := -1, powers := [(8, 1), (43, 1), (59, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (6, 1), (13, 1), (52, 1), (59, 1)] }, { coefficient := -1, powers := [(6, 1), (13, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (38, 1), (52, 1), (59, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := -1, powers := [(0, 1), (2, 1), (6, 1), (52, 1), (59, 1), (61, 1)] }, { coefficient := -1, powers := [(2, 1), (6, 1), (59, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(0, 2), (3, 1), (32, 1), (39, 1), (59, 1)] }, { coefficient := -1, powers := [(0, 2), (19, 1), (39, 1), (50, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(0, 2), (39, 1), (50, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(0, 2), (14, 1), (39, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(0, 2), (2, 1), (6, 1), (43, 1), (52, 1), (59, 1), (61, 1)] }, { coefficient := -1, powers := [(0, 1), (2, 1), (6, 1), (43, 1), (52, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (2, 1), (6, 1), (43, 1), (59, 1), (61, 1)] }, { coefficient := -1, powers := [(0, 1), (5, 1), (6, 1), (34, 1), (52, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (6, 1), (13, 1), (24, 1), (52, 1), (59, 1)] }, { coefficient := -1, powers := [(2, 1), (6, 1), (43, 1), (59, 1)] }, { coefficient := -1, powers := [(5, 1), (6, 1), (34, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (13, 1), (24, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(0, 1)] }],
  [{ coefficient := 1, powers := [(0, 2), (38, 1), (59, 1), (63, 1)] }, { coefficient := 1, powers := [(0, 2), (63, 1)] }],
  [{ coefficient := -1, powers := [(0, 2), (39, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (6, 1), (52, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (2, 1), (6, 1), (40, 1), (52, 1), (59, 1), (60, 1)] }, { coefficient := -1, powers := [(0, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (6, 1), (40, 1), (59, 1), (60, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(0, 2), (6, 1), (32, 1), (39, 1), (44, 1), (59, 1)] }, { coefficient := -1, powers := [(0, 2), (38, 1), (46, 1), (52, 1), (59, 1)] }, { coefficient := -1, powers := [(0, 2), (46, 1), (52, 1)] }, { coefficient := -1, powers := [(0, 1), (6, 1), (38, 1), (52, 1), (59, 2)] }, { coefficient := -1, powers := [(0, 1), (6, 1), (52, 1), (59, 1)] }, { coefficient := -1, powers := [(0, 1), (38, 1), (52, 1), (59, 1)] }, { coefficient := -1, powers := [(0, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(0, 3), (39, 1), (55, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 2), (6, 1), (35, 1), (39, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(0, 3), (2, 1), (6, 1), (43, 1), (52, 1), (57, 1), (59, 1), (61, 1)] }, { coefficient := -1, powers := [(0, 3), (3, 1), (32, 1), (39, 1), (55, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 3), (19, 1), (39, 1), (50, 1), (55, 1), (59, 1)] }, { coefficient := -1, powers := [(0, 2), (2, 1), (6, 1), (25, 1), (26, 1), (43, 1), (45, 1), (52, 2), (59, 1), (61, 1)] }, { coefficient := 1, powers := [(0, 2), (2, 1), (6, 1), (25, 1), (43, 1), (45, 1), (52, 1), (53, 1), (59, 1), (61, 1)] }, { coefficient := 1, powers := [(0, 2), (2, 1), (6, 1), (43, 1), (52, 1), (57, 1), (59, 1)] }, { coefficient := -1, powers := [(0, 2), (2, 1), (6, 1), (43, 1), (57, 1), (59, 1), (61, 1)] }, { coefficient := -1, powers := [(0, 2), (2, 1), (38, 1), (56, 1), (59, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 2), (2, 1), (56, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 2), (3, 1), (6, 1), (32, 1), (35, 1), (39, 1), (59, 1)] }, { coefficient := -1, powers := [(0, 2), (3, 1), (14, 1), (25, 1), (32, 1), (39, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 2), (5, 1), (6, 1), (34, 1), (52, 1), (57, 1), (59, 1)] }, { coefficient := -1, powers := [(0, 2), (6, 1), (13, 1), (24, 1), (52, 1), (57, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 2), (6, 1), (19, 1), (35, 1), (39, 1), (50, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 2), (14, 1), (19, 1), (25, 1), (39, 1), (50, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 2), (14, 1), (38, 1), (50, 1), (59, 1)] }, { coefficient := -1, powers := [(0, 2), (17, 1), (23, 1), (25, 1), (39, 1), (59, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 2), (17, 1), (25, 1), (29, 1), (39, 1), (59, 1), (63, 1)] }, { coefficient := 1, powers := [(0, 2), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (2, 1), (6, 1), (25, 1), (26, 1), (43, 1), (45, 1), (52, 2), (59, 1)] }, { coefficient := -1, powers := [(0, 1), (2, 1), (6, 1), (25, 1), (26, 1), (43, 1), (45, 1), (52, 1), (59, 1), (61, 1)] }, { coefficient := -1, powers := [(0, 1), (2, 1), (6, 1), (25, 1), (43, 1), (45, 1), (52, 1), (53, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (2, 1), (6, 1), (25, 1), (43, 1), (45, 1), (53, 1), (59, 1), (61, 1)] }, { coefficient := 1, powers := [(0, 1), (2, 1), (6, 1), (43, 1), (57, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (5, 1), (6, 1), (25, 1), (26, 1), (34, 1), (45, 1), (52, 2), (59, 1)] }, { coefficient := -1, powers := [(0, 1), (5, 1), (6, 1), (25, 1), (34, 1), (45, 1), (52, 1), (53, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (5, 1), (6, 1), (34, 1), (57, 1), (59, 1)] }, { coefficient := -1, powers := [(0, 1), (6, 1), (13, 1), (24, 1), (25, 1), (26, 1), (45, 1), (52, 2), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (6, 1), (13, 1), (24, 1), (25, 1), (45, 1), (52, 1), (53, 1), (59, 1)] }, { coefficient := -1, powers := [(0, 1), (6, 1), (13, 1), (24, 1), (57, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (6, 1), (17, 1), (23, 1), (25, 1), (52, 1), (59, 1), (63, 1)] }, { coefficient := 1, powers := [(0, 1), (6, 1), (17, 1), (25, 1), (29, 1), (52, 1), (59, 1), (63, 1)] }, { coefficient := -2, powers := [(0, 1), (6, 1), (18, 1), (24, 1), (25, 1), (52, 1), (54, 1), (59, 1)] }, { coefficient := -1, powers := [(0, 1), (6, 1), (18, 1), (25, 1), (31, 1), (43, 1), (52, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (17, 1), (23, 1), (25, 1), (52, 1), (63, 1)] }, { coefficient := 1, powers := [(0, 1), (17, 1), (25, 1), (29, 1), (52, 1), (63, 1)] }, { coefficient := 1, powers := [(0, 1), (25, 1), (38, 1), (52, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1)] }, { coefficient := 1, powers := [(2, 1), (6, 1), (25, 1), (26, 1), (43, 1), (45, 1), (52, 1), (59, 1)] }, { coefficient := -1, powers := [(2, 1), (6, 1), (25, 1), (43, 1), (45, 1), (53, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (6, 1), (25, 1), (26, 1), (34, 1), (45, 1), (52, 1), (59, 1)] }, { coefficient := -1, powers := [(5, 1), (6, 1), (25, 1), (34, 1), (45, 1), (53, 1), (59, 1)] }, { coefficient := -1, powers := [(6, 1), (13, 1), (24, 1), (25, 1), (26, 1), (45, 1), (52, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (13, 1), (24, 1), (25, 1), (45, 1), (53, 1), (59, 1)] }, { coefficient := -2, powers := [(6, 1), (18, 1), (24, 1), (25, 1), (54, 1), (59, 1)] }, { coefficient := -1, powers := [(6, 1), (18, 1), (25, 1), (31, 1), (43, 1), (59, 1)] }, { coefficient := -1, powers := [(25, 1)] }],
  [{ coefficient := 1, powers := [(0, 3), (14, 1), (39, 1), (50, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 2), (2, 1), (6, 1), (25, 1), (26, 1), (43, 1), (47, 1), (52, 2), (59, 1), (61, 1)] }, { coefficient := -1, powers := [(0, 2), (2, 1), (6, 1), (25, 1), (43, 1), (47, 1), (52, 1), (53, 1), (59, 1), (61, 1)] }, { coefficient := 1, powers := [(0, 2), (3, 1), (14, 1), (32, 1), (39, 1), (59, 1)] }, { coefficient := -1, powers := [(0, 2), (3, 1), (25, 1), (39, 1), (58, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 2), (6, 1), (14, 1), (32, 1), (39, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 2), (9, 1), (14, 1), (25, 1), (39, 1), (59, 1)] }, { coefficient := -1, powers := [(0, 2), (9, 1), (25, 1), (39, 1), (44, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 2), (14, 1), (19, 1), (39, 1), (50, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 2), (14, 1), (32, 1), (38, 1), (39, 1), (59, 1)] }, { coefficient := -1, powers := [(0, 2), (14, 1), (38, 1), (50, 1), (52, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 2), (14, 1), (38, 1), (51, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 2), (17, 1), (23, 1), (25, 1), (39, 1), (46, 1), (59, 1), (63, 1)] }, { coefficient := 1, powers := [(0, 2), (17, 1), (25, 1), (29, 1), (39, 1), (46, 1), (59, 1), (63, 1)] }, { coefficient := 1, powers := [(0, 2), (25, 1), (39, 1), (44, 1), (50, 1), (59, 1)] }, { coefficient := -1, powers := [(0, 2), (56, 1), (61, 1)] }, { coefficient := -1, powers := [(0, 1), (2, 1), (6, 1), (25, 1), (26, 1), (43, 1), (47, 1), (52, 2), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (2, 1), (6, 1), (25, 1), (26, 1), (43, 1), (47, 1), (52, 1), (59, 1), (61, 1)] }, { coefficient := 1, powers := [(0, 1), (2, 1), (6, 1), (25, 1), (43, 1), (47, 1), (52, 1), (53, 1), (59, 1)] }, { coefficient := -1, powers := [(0, 1), (2, 1), (6, 1), (25, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] }, { coefficient := -1, powers := [(0, 1), (2, 1), (6, 1), (25, 1), (49, 1), (52, 2), (54, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (2, 1), (6, 1), (25, 1), (49, 1), (52, 1), (54, 1), (59, 1), (61, 1)] }, { coefficient := -1, powers := [(0, 1), (5, 1), (6, 1), (25, 1), (26, 1), (34, 1), (47, 1), (52, 2), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (5, 1), (6, 1), (25, 1), (34, 1), (47, 1), (52, 1), (53, 1), (59, 1)] }, { coefficient := -1, powers := [(0, 1), (6, 1), (8, 1), (25, 1), (34, 1), (43, 1), (49, 1), (52, 2), (59, 1), (64, 1)] }, { coefficient := 1, powers := [(0, 1), (6, 1), (8, 1), (37, 1), (43, 1), (52, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (6, 1), (13, 1), (24, 1), (25, 1), (26, 1), (47, 1), (52, 2), (59, 1)] }, { coefficient := -1, powers := [(0, 1), (6, 1), (13, 1), (24, 1), (25, 1), (47, 1), (52, 1), (53, 1), (59, 1)] }, { coefficient := -2, powers := [(0, 1), (6, 1), (13, 1), (25, 1), (31, 1), (49, 1), (52, 2), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (6, 1), (13, 1), (31, 1), (45, 1), (48, 1), (52, 1), (59, 1)] }, { coefficient := -1, powers := [(0, 1), (6, 1), (17, 1), (23, 1), (25, 1), (46, 1), (52, 1), (59, 1), (63, 1)] }, { coefficient := 2, powers := [(0, 1), (6, 1), (17, 1), (24, 1), (25, 1), (47, 1), (52, 1), (54, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (6, 1), (17, 1), (24, 1), (45, 1), (52, 1), (54, 1), (59, 1)] }, { coefficient := -1, powers := [(0, 1), (6, 1), (17, 1), (25, 1), (29, 1), (46, 1), (52, 1), (59, 1), (63, 1)] }, { coefficient := 1, powers := [(0, 1), (6, 1), (17, 1), (25, 1), (31, 1), (43, 1), (47, 1), (52, 1), (59, 1)] }, { coefficient := -1, powers := [(0, 1), (17, 1), (23, 1), (25, 1), (46, 1), (52, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (17, 1), (25, 1), (29, 1), (46, 1), (52, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (25, 1), (38, 1), (46, 1), (52, 1), (59, 1)] }, { coefficient := -1, powers := [(0, 1), (61, 1)] }, { coefficient := -1, powers := [(2, 1), (6, 1), (25, 1), (26, 1), (43, 1), (47, 1), (52, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (6, 1), (25, 1), (43, 1), (47, 1), (53, 1), (59, 1)] }, { coefficient := -1, powers := [(2, 1), (6, 1), (25, 1), (49, 1), (52, 1), (54, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (6, 1), (25, 1), (49, 1), (54, 1), (59, 1), (61, 1)] }, { coefficient := -1, powers := [(5, 1), (6, 1), (25, 1), (26, 1), (34, 1), (47, 1), (52, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (6, 1), (25, 1), (34, 1), (47, 1), (53, 1), (59, 1)] }, { coefficient := -1, powers := [(6, 1), (8, 1), (25, 1), (34, 1), (43, 1), (49, 1), (52, 1), (59, 1), (64, 1)] }, { coefficient := 1, powers := [(6, 1), (8, 1), (37, 1), (43, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (13, 1), (24, 1), (25, 1), (26, 1), (47, 1), (52, 1), (59, 1)] }, { coefficient := -1, powers := [(6, 1), (13, 1), (24, 1), (25, 1), (47, 1), (53, 1), (59, 1)] }, { coefficient := -2, powers := [(6, 1), (13, 1), (25, 1), (31, 1), (49, 1), (52, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (13, 1), (31, 1), (45, 1), (48, 1), (59, 1)] }, { coefficient := 2, powers := [(6, 1), (17, 1), (24, 1), (25, 1), (47, 1), (54, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (17, 1), (24, 1), (45, 1), (54, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (17, 1), (25, 1), (31, 1), (43, 1), (47, 1), (59, 1)] }, { coefficient := 1, powers := [(25, 1), (46, 1)] }]
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
    (values : Fin 65 → R) :
    ¬ ∀ index : Fin 45,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((2 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (2 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (2 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component18.SelectedLeafB7_1.selectedHasNoCommonZero

end Krenn.Component18.SelectedLeafB7_1
