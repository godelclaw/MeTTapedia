import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component18.SelectedLeafB4_5

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "cd8a9993dda0ed713264da64b3f6516d6c2a97596b7fb0288a371b3811d0b96d"
def certificateSHA256 : String := "1eb37b339cfeae25680ed8f7309b54dec2c131f1fcf838bf6977c721bc77c4b9"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 36 → Fin 664 := ![
  1,
  10,
  12,
  19,
  20,
  25,
  167,
  168,
  294,
  295,
  301,
  302,
  303,
  318,
  327,
  409,
  424,
  433,
  437,
  438,
  443,
  463,
  498,
  515,
  562,
  585,
  602,
  603,
  609,
  610,
  629,
  655,
  657,
  660,
  662,
  663
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 36 → SparsePoly (Fin 64) := ![
  [{ coefficient := 1, powers := [(6, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(43, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (45, 1)] }, { coefficient := 1, powers := [(29, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (53, 1)] }, { coefficient := 1, powers := [(31, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1)] }, { coefficient := 1, powers := [(19, 1), (45, 1)] }, { coefficient := 1, powers := [(25, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (49, 1)] }, { coefficient := 1, powers := [(20, 1), (45, 1)] }, { coefficient := 1, powers := [(25, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (60, 1)] }, { coefficient := 1, powers := [(13, 1), (49, 1)] }, { coefficient := 1, powers := [(18, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (58, 1)] }, { coefficient := 1, powers := [(9, 1), (55, 1)] }, { coefficient := 1, powers := [(14, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (29, 1)] }, { coefficient := 1, powers := [(23, 1), (50, 1)] }, { coefficient := 1, powers := [(29, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (54, 1)] }, { coefficient := 1, powers := [(31, 1), (43, 1)] }, { coefficient := 1, powers := [(34, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (49, 1), (52, 1)] }, { coefficient := 1, powers := [(20, 1), (45, 1), (52, 1)] }, { coefficient := 1, powers := [(49, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (25, 1), (47, 1)] }, { coefficient := 1, powers := [(18, 1), (25, 1), (42, 1)] }, { coefficient := 1, powers := [(18, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1)] }, { coefficient := 1, powers := [(25, 1), (42, 1), (45, 1)] }, { coefficient := 1, powers := [(25, 1), (47, 1)] }, { coefficient := 1, powers := [(45, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (49, 1)] }, { coefficient := 1, powers := [(5, 1), (37, 1)] }, { coefficient := 1, powers := [(17, 1), (29, 1), (49, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1)] }, { coefficient := 1, powers := [(13, 1), (31, 1)] }, { coefficient := 1, powers := [(17, 1), (23, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (37, 1)] }, { coefficient := 1, powers := [(23, 1), (45, 1)] }, { coefficient := 1, powers := [(29, 1), (45, 1)] }, { coefficient := 1, powers := [(37, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (60, 1)] }, { coefficient := 1, powers := [(13, 1), (26, 1), (47, 1)] }, { coefficient := 1, powers := [(13, 1), (57, 1)] }, { coefficient := 1, powers := [(18, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1), (52, 1)] }, { coefficient := 1, powers := [(42, 1), (45, 1)] }, { coefficient := 1, powers := [(45, 1), (52, 1)] }, { coefficient := 1, powers := [(47, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (37, 1), (51, 1)] }, { coefficient := 1, powers := [(9, 1), (30, 1), (45, 1)] }, { coefficient := 1, powers := [(23, 1), (45, 1), (51, 1)] }, { coefficient := 1, powers := [(30, 1), (41, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (24, 1), (60, 1)] }, { coefficient := 1, powers := [(6, 1), (34, 1), (49, 1)] }, { coefficient := 1, powers := [(6, 1), (37, 1), (43, 1)] }, { coefficient := 1, powers := [(29, 1), (43, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (45, 1), (53, 1)] }, { coefficient := 1, powers := [(24, 1), (57, 1)] }, { coefficient := 1, powers := [(31, 1), (49, 1)] }, { coefficient := 1, powers := [(37, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1), (55, 1)] }, { coefficient := 1, powers := [(6, 1), (35, 1), (42, 1)] }, { coefficient := 1, powers := [(14, 1), (25, 1), (42, 1)] }, { coefficient := 1, powers := [(14, 1)] }, { coefficient := 1, powers := [(55, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1)] }, { coefficient := 1, powers := [(3, 1), (35, 1)] }, { coefficient := 1, powers := [(14, 1), (19, 1)] }, { coefficient := 1, powers := [(19, 1), (55, 1)] }, { coefficient := 1, powers := [(25, 1), (44, 1)] }, { coefficient := 1, powers := [(35, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (50, 1)] }, { coefficient := 1, powers := [(6, 1), (32, 1)] }, { coefficient := 1, powers := [(9, 1), (25, 1)] }, { coefficient := 1, powers := [(19, 1), (50, 1)] }, { coefficient := 1, powers := [(25, 1), (41, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (47, 1), (53, 1)] }, { coefficient := 1, powers := [(26, 1), (42, 1), (45, 1)] }, { coefficient := 1, powers := [(26, 1), (47, 1)] }, { coefficient := 1, powers := [(45, 1), (53, 1)] }, { coefficient := 1, powers := [(57, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1), (51, 1)] }, { coefficient := 1, powers := [(3, 1), (35, 1), (51, 1)] }, { coefficient := 1, powers := [(3, 1), (58, 1)] }, { coefficient := 1, powers := [(9, 1), (44, 1)] }, { coefficient := 1, powers := [(14, 1), (19, 1), (51, 1)] }, { coefficient := 1, powers := [(14, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (37, 1), (50, 1)] }, { coefficient := 1, powers := [(6, 1), (37, 1), (41, 1)] }, { coefficient := 1, powers := [(9, 1), (29, 1), (45, 1)] }, { coefficient := 1, powers := [(9, 1), (37, 1), (38, 1)] }, { coefficient := 1, powers := [(23, 1), (45, 1), (50, 1)] }, { coefficient := 1, powers := [(29, 1), (41, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (38, 1), (58, 1)] }, { coefficient := 1, powers := [(0, 1), (41, 1), (55, 1)] }, { coefficient := 1, powers := [(0, 1), (44, 1), (50, 1)] }, { coefficient := 1, powers := [(3, 1), (25, 1), (58, 1)] }, { coefficient := 1, powers := [(3, 1), (32, 1), (55, 1)] }, { coefficient := 1, powers := [(3, 1), (35, 1), (50, 1)] }, { coefficient := 1, powers := [(6, 1), (19, 1), (58, 1)] }, { coefficient := 1, powers := [(6, 1), (32, 1), (44, 1)] }, { coefficient := 1, powers := [(6, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(9, 1), (19, 1), (55, 1)] }, { coefficient := 1, powers := [(9, 1), (25, 1), (44, 1)] }, { coefficient := 1, powers := [(9, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(14, 1), (19, 1), (50, 1)] }, { coefficient := 1, powers := [(14, 1), (25, 1), (41, 1)] }, { coefficient := 1, powers := [(14, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (40, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (43, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (49, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (37, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (49, 1)] }, { coefficient := 1, powers := [(8, 1), (37, 1), (43, 1)] }, { coefficient := 1, powers := [(13, 1), (24, 1), (57, 1)] }, { coefficient := 1, powers := [(13, 1), (31, 1), (49, 1)] }, { coefficient := 1, powers := [(13, 1), (37, 1), (40, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (54, 1)] }, { coefficient := 1, powers := [(18, 1), (31, 1), (43, 1)] }, { coefficient := 1, powers := [(18, 1), (34, 1), (40, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(42, 1)] }],
  [{ coefficient := 1, powers := [(43, 1), (63, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 36 → SparsePoly (Fin 64) := ![
  [{ coefficient := -1, powers := [(8, 1), (24, 1), (32, 1), (43, 1), (44, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(24, 1), (26, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (8, 1), (19, 1), (37, 1), (43, 1), (51, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (8, 1), (37, 1), (43, 1), (50, 1), (63, 1)] }, { coefficient := -1, powers := [(3, 1), (8, 1), (32, 1), (37, 1), (43, 1), (63, 1)] }, { coefficient := -1, powers := [(6, 1), (8, 1), (32, 1), (37, 1), (43, 1), (63, 1)] }, { coefficient := -1, powers := [(8, 1), (9, 1), (25, 1), (37, 1), (43, 1), (63, 1)] }, { coefficient := -1, powers := [(8, 1), (19, 1), (37, 1), (43, 1), (50, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(17, 1), (49, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (8, 1), (37, 1), (43, 1), (44, 1), (51, 1), (63, 1)] }, { coefficient := 1, powers := [(3, 1), (8, 1), (37, 1), (43, 1), (58, 1), (63, 1)] }, { coefficient := -1, powers := [(5, 1), (26, 1), (34, 1), (47, 1), (52, 1), (63, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (47, 1), (53, 1), (63, 1)] }, { coefficient := -1, powers := [(6, 1), (8, 1), (32, 1), (34, 1), (43, 1), (44, 1), (49, 1), (52, 1), (63, 2)] }, { coefficient := -1, powers := [(8, 1), (37, 1), (43, 1), (44, 1), (50, 1), (63, 1)] }, { coefficient := 1, powers := [(13, 1), (24, 1), (26, 1), (47, 1), (52, 1), (63, 1)] }, { coefficient := -1, powers := [(13, 1), (24, 1), (47, 1), (53, 1), (63, 1)] }, { coefficient := -2, powers := [(13, 1), (31, 1), (49, 1), (52, 1), (63, 1)] }, { coefficient := 2, powers := [(17, 1), (24, 1), (47, 1), (54, 1), (63, 1)] }, { coefficient := 1, powers := [(17, 1), (31, 1), (43, 1), (47, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (8, 1), (9, 1), (30, 1), (35, 1), (43, 1), (63, 1)] }, { coefficient := 1, powers := [(0, 1), (8, 1), (29, 1), (35, 1), (43, 1), (51, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (8, 1), (30, 1), (35, 1), (41, 1), (43, 1), (63, 1)] }, { coefficient := 1, powers := [(8, 1), (9, 1), (23, 1), (35, 1), (43, 1), (63, 1)] }, { coefficient := 1, powers := [(8, 1), (9, 1), (29, 1), (35, 1), (43, 1), (63, 1)] }, { coefficient := 1, powers := [(8, 1), (19, 1), (23, 1), (43, 1), (58, 1), (63, 1)] }, { coefficient := 1, powers := [(8, 1), (19, 1), (29, 1), (43, 1), (58, 1), (63, 1)] }, { coefficient := 1, powers := [(8, 1), (23, 1), (25, 1), (43, 1), (58, 1), (63, 1)] }, { coefficient := 1, powers := [(8, 1), (23, 1), (35, 1), (43, 1), (50, 1), (63, 1)] }, { coefficient := 1, powers := [(8, 1), (25, 1), (29, 1), (43, 1), (58, 1), (63, 1)] }, { coefficient := -1, powers := [(8, 1), (29, 1), (32, 1), (43, 1), (44, 1), (63, 1)] }, { coefficient := 1, powers := [(8, 1), (29, 1), (35, 1), (43, 1), (50, 1), (63, 1)] }, { coefficient := 1, powers := [(13, 1), (31, 1), (48, 1), (63, 1)] }, { coefficient := 1, powers := [(17, 1), (24, 1), (54, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(17, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(13, 1), (45, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (23, 1), (43, 1), (58, 1)] }, { coefficient := -1, powers := [(8, 1), (29, 1), (43, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (8, 1), (32, 1), (34, 1), (43, 1), (44, 1), (52, 1), (63, 1)] }, { coefficient := 2, powers := [(13, 1), (31, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(31, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (19, 1), (37, 1), (43, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (35, 1), (43, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(18, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (8, 1), (32, 1), (34, 1), (43, 1), (44, 1), (63, 1)] }, { coefficient := -2, powers := [(13, 1), (31, 1)] }],
  [{ coefficient := -2, powers := [(24, 1), (54, 1)] }, { coefficient := -1, powers := [(31, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (26, 1), (34, 1), (52, 1)] }, { coefficient := -1, powers := [(5, 1), (34, 1), (53, 1)] }, { coefficient := -1, powers := [(13, 1), (24, 1), (26, 1), (52, 1)] }, { coefficient := 1, powers := [(13, 1), (24, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(54, 1)] }],
  [{ coefficient := 1, powers := [(49, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (8, 1), (35, 1), (43, 1), (51, 1)] }, { coefficient := 1, powers := [(0, 1), (8, 1), (43, 1), (58, 1)] }, { coefficient := -1, powers := [(8, 1), (9, 1), (35, 1), (43, 1)] }, { coefficient := -1, powers := [(8, 1), (35, 1), (43, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(24, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (26, 1), (34, 1)] }, { coefficient := 1, powers := [(13, 1), (24, 1), (26, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (8, 1), (35, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (32, 1), (43, 1), (44, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(13, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (8, 1), (19, 1), (37, 1), (43, 1), (51, 1)] }, { coefficient := 1, powers := [(0, 1), (8, 1), (37, 1), (41, 1), (43, 1)] }, { coefficient := 1, powers := [(3, 1), (8, 1), (32, 1), (37, 1), (43, 1)] }, { coefficient := -1, powers := [(8, 1), (9, 1), (19, 1), (37, 1), (43, 1)] }, { coefficient := -1, powers := [(8, 1), (19, 1), (37, 1), (43, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (8, 1), (37, 1), (43, 1), (51, 1)] }, { coefficient := 1, powers := [(8, 1), (9, 1), (37, 1), (43, 1)] }, { coefficient := 1, powers := [(8, 1), (37, 1), (43, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (14, 1), (37, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (34, 1)] }, { coefficient := -1, powers := [(13, 1), (24, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (8, 1), (37, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (35, 1), (43, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (37, 1), (43, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(40, 1), (60, 1)] }, { coefficient := 1, powers := [(43, 1), (57, 1)] }, { coefficient := -1, powers := [(49, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(0, 2), (8, 1), (19, 1), (37, 1), (43, 1), (51, 1), (55, 1)] }, { coefficient := -1, powers := [(0, 2), (8, 1), (37, 1), (41, 1), (43, 1), (55, 1)] }, { coefficient := -1, powers := [(0, 1), (3, 1), (8, 1), (32, 1), (37, 1), (43, 1), (55, 1)] }, { coefficient := -1, powers := [(0, 1), (5, 1), (34, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (6, 1), (8, 1), (19, 1), (35, 1), (37, 1), (43, 1), (51, 1)] }, { coefficient := -1, powers := [(0, 1), (6, 1), (8, 1), (35, 1), (37, 1), (41, 1), (43, 1)] }, { coefficient := 1, powers := [(0, 1), (8, 1), (9, 1), (19, 1), (37, 1), (43, 1), (55, 1)] }, { coefficient := 1, powers := [(0, 1), (8, 1), (14, 1), (19, 1), (25, 1), (37, 1), (43, 1), (51, 1)] }, { coefficient := -1, powers := [(0, 1), (8, 1), (14, 1), (25, 1), (37, 1), (41, 1), (43, 1)] }, { coefficient := 1, powers := [(0, 1), (8, 1), (19, 1), (37, 1), (43, 1), (50, 1), (55, 1)] }, { coefficient := 1, powers := [(0, 1), (13, 1), (24, 1), (57, 1)] }, { coefficient := -1, powers := [(3, 1), (6, 1), (8, 1), (32, 1), (35, 1), (37, 1), (43, 1)] }, { coefficient := -1, powers := [(3, 1), (8, 1), (14, 1), (25, 1), (32, 1), (37, 1), (43, 1)] }, { coefficient := -1, powers := [(5, 1), (25, 1), (26, 1), (34, 1), (45, 1), (52, 1)] }, { coefficient := 1, powers := [(5, 1), (25, 1), (34, 1), (45, 1), (53, 1)] }, { coefficient := 1, powers := [(6, 1), (8, 1), (9, 1), (19, 1), (35, 1), (37, 1), (43, 1)] }, { coefficient := 1, powers := [(6, 1), (8, 1), (19, 1), (35, 1), (37, 1), (43, 1), (50, 1)] }, { coefficient := 1, powers := [(8, 1), (9, 1), (14, 1), (19, 1), (25, 1), (37, 1), (43, 1)] }, { coefficient := 1, powers := [(8, 1), (14, 1), (19, 1), (25, 1), (37, 1), (43, 1), (50, 1)] }, { coefficient := 1, powers := [(13, 1), (24, 1), (25, 1), (26, 1), (45, 1), (52, 1)] }, { coefficient := -1, powers := [(13, 1), (24, 1), (25, 1), (45, 1), (53, 1)] }, { coefficient := 2, powers := [(18, 1), (24, 1), (25, 1), (54, 1)] }, { coefficient := 1, powers := [(18, 1), (25, 1), (31, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (8, 1), (9, 1), (30, 1), (35, 1), (43, 1), (45, 1)] }, { coefficient := -1, powers := [(0, 1), (8, 1), (14, 1), (19, 1), (37, 1), (43, 1), (51, 1)] }, { coefficient := 1, powers := [(0, 1), (8, 1), (14, 1), (37, 1), (43, 1), (50, 1)] }, { coefficient := 1, powers := [(0, 1), (8, 1), (25, 1), (37, 1), (43, 1), (44, 1), (51, 1)] }, { coefficient := -1, powers := [(0, 1), (8, 1), (29, 1), (35, 1), (43, 1), (45, 1), (51, 1)] }, { coefficient := 1, powers := [(0, 1), (8, 1), (30, 1), (35, 1), (41, 1), (43, 1), (45, 1)] }, { coefficient := 1, powers := [(3, 1), (8, 1), (14, 1), (32, 1), (37, 1), (43, 1)] }, { coefficient := -1, powers := [(3, 1), (8, 1), (25, 1), (37, 1), (43, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (25, 1), (26, 1), (34, 1), (47, 1), (52, 1)] }, { coefficient := -1, powers := [(5, 1), (25, 1), (34, 1), (47, 1), (53, 1)] }, { coefficient := 1, powers := [(6, 1), (8, 1), (14, 1), (32, 1), (37, 1), (43, 1)] }, { coefficient := 1, powers := [(6, 1), (8, 1), (25, 1), (32, 1), (34, 1), (43, 1), (44, 1), (49, 1), (52, 1), (63, 1)] }, { coefficient := -1, powers := [(6, 1), (8, 1), (32, 1), (37, 1), (43, 1), (44, 1)] }, { coefficient := 1, powers := [(8, 1), (9, 1), (14, 1), (25, 1), (37, 1), (43, 1)] }, { coefficient := -1, powers := [(8, 1), (9, 1), (23, 1), (35, 1), (43, 1), (45, 1)] }, { coefficient := -1, powers := [(8, 1), (9, 1), (29, 1), (35, 1), (43, 1), (45, 1)] }, { coefficient := 1, powers := [(8, 1), (14, 1), (19, 1), (37, 1), (43, 1), (50, 1)] }, { coefficient := -1, powers := [(8, 1), (19, 1), (23, 1), (43, 1), (45, 1), (58, 1)] }, { coefficient := -1, powers := [(8, 1), (19, 1), (29, 1), (43, 1), (45, 1), (58, 1)] }, { coefficient := -1, powers := [(8, 1), (23, 1), (25, 1), (43, 1), (45, 1), (58, 1)] }, { coefficient := -1, powers := [(8, 1), (23, 1), (35, 1), (43, 1), (45, 1), (50, 1)] }, { coefficient := -1, powers := [(8, 1), (25, 1), (29, 1), (43, 1), (45, 1), (58, 1)] }, { coefficient := 1, powers := [(8, 1), (25, 1), (37, 1), (43, 1), (44, 1), (50, 1)] }, { coefficient := -1, powers := [(8, 1), (29, 1), (35, 1), (43, 1), (45, 1), (50, 1)] }, { coefficient := -1, powers := [(13, 1), (24, 1), (25, 1), (26, 1), (47, 1), (52, 1)] }, { coefficient := 1, powers := [(13, 1), (24, 1), (25, 1), (47, 1), (53, 1)] }, { coefficient := 2, powers := [(13, 1), (25, 1), (31, 1), (49, 1), (52, 1)] }, { coefficient := -1, powers := [(13, 1), (31, 1), (45, 1), (48, 1)] }, { coefficient := -2, powers := [(17, 1), (24, 1), (25, 1), (47, 1), (54, 1)] }, { coefficient := -1, powers := [(17, 1), (24, 1), (45, 1), (54, 1)] }, { coefficient := -1, powers := [(17, 1), (25, 1), (31, 1), (43, 1), (47, 1)] }]
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
    (values : Fin 64 → R) :
    ¬ ∀ index : Fin 36,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component18.SelectedLeafB4_5.selectedHasNoCommonZero

end Krenn.Component18.SelectedLeafB4_5
