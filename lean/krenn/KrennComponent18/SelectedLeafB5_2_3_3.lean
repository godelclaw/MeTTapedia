import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component18.SelectedLeafB5_2_3_3

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "78f90cc435a01b6dcbdafee13e984e03433e68b41f85185655f47641cf863fbc"
def certificateSHA256 : String := "036abaa4b70e5ed6d34e2e477b09dc1443c962ebb3c4dbd09bdaa931ec1ace60"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 42 → Fin 670 := ![
  10,
  16,
  19,
  142,
  246,
  294,
  295,
  300,
  301,
  302,
  303,
  317,
  318,
  323,
  409,
  424,
  437,
  438,
  443,
  457,
  458,
  463,
  498,
  519,
  584,
  585,
  591,
  602,
  603,
  610,
  629,
  655,
  657,
  658,
  660,
  661,
  662,
  663,
  664,
  665,
  666,
  667
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 42 → SparsePoly (Fin 68) := ![
  [{ coefficient := 1, powers := [(13, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (54, 1)] }, { coefficient := 1, powers := [(19, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (19, 1), (56, 1)] }, { coefficient := 1, powers := [(13, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1)] }, { coefficient := 1, powers := [(19, 1), (45, 1)] }, { coefficient := 1, powers := [(25, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (49, 1)] }, { coefficient := 1, powers := [(20, 1), (45, 1)] }, { coefficient := 1, powers := [(25, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (44, 1)] }, { coefficient := 1, powers := [(17, 1), (23, 1), (55, 1)] }, { coefficient := 1, powers := [(17, 1), (29, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (60, 1)] }, { coefficient := 1, powers := [(13, 1), (49, 1)] }, { coefficient := 1, powers := [(18, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (58, 1)] }, { coefficient := 1, powers := [(9, 1), (55, 1)] }, { coefficient := 1, powers := [(14, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (29, 1)] }, { coefficient := 1, powers := [(23, 1), (50, 1)] }, { coefficient := 1, powers := [(29, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (52, 1)] }, { coefficient := 1, powers := [(24, 1), (56, 1)] }, { coefficient := 1, powers := [(30, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (54, 1)] }, { coefficient := 1, powers := [(31, 1), (43, 1)] }, { coefficient := 1, powers := [(34, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1), (52, 1)] }, { coefficient := 1, powers := [(19, 1), (45, 1), (52, 1)] }, { coefficient := 1, powers := [(45, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (25, 1), (47, 1)] }, { coefficient := 1, powers := [(18, 1), (25, 1), (42, 1)] }, { coefficient := 1, powers := [(18, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1)] }, { coefficient := 1, powers := [(25, 1), (42, 1), (45, 1)] }, { coefficient := 1, powers := [(25, 1), (47, 1)] }, { coefficient := 1, powers := [(45, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1)] }, { coefficient := 1, powers := [(13, 1), (31, 1)] }, { coefficient := 1, powers := [(17, 1), (23, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (37, 1)] }, { coefficient := 1, powers := [(23, 1), (45, 1)] }, { coefficient := 1, powers := [(29, 1), (45, 1)] }, { coefficient := 1, powers := [(37, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (60, 1)] }, { coefficient := 1, powers := [(13, 1), (26, 1), (47, 1)] }, { coefficient := 1, powers := [(13, 1), (57, 1)] }, { coefficient := 1, powers := [(18, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1), (51, 1)] }, { coefficient := 1, powers := [(9, 1), (45, 1)] }, { coefficient := 1, powers := [(19, 1), (45, 1), (51, 1)] }, { coefficient := 1, powers := [(41, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1), (53, 1)] }, { coefficient := 1, powers := [(19, 1), (45, 1), (53, 1)] }, { coefficient := 1, powers := [(19, 1), (57, 1)] }, { coefficient := 1, powers := [(26, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1), (52, 1)] }, { coefficient := 1, powers := [(42, 1), (45, 1)] }, { coefficient := 1, powers := [(45, 1), (52, 1)] }, { coefficient := 1, powers := [(47, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (37, 1), (51, 1)] }, { coefficient := 1, powers := [(9, 1), (30, 1), (45, 1)] }, { coefficient := 1, powers := [(23, 1), (45, 1), (51, 1)] }, { coefficient := 1, powers := [(30, 1), (41, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (37, 1), (42, 1)] }, { coefficient := 1, powers := [(29, 1), (42, 1), (45, 1)] }, { coefficient := 1, powers := [(29, 1), (47, 1)] }, { coefficient := 1, powers := [(30, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (40, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (43, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (49, 1), (54, 1)] }, { coefficient := 1, powers := [(20, 1), (45, 1), (54, 1)] }, { coefficient := 1, powers := [(26, 1), (43, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1), (55, 1)] }, { coefficient := 1, powers := [(6, 1), (35, 1), (42, 1)] }, { coefficient := 1, powers := [(14, 1), (25, 1), (42, 1)] }, { coefficient := 1, powers := [(14, 1)] }, { coefficient := 1, powers := [(55, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (43, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (56, 1)] }, { coefficient := 1, powers := [(13, 1), (24, 1), (56, 1)] }, { coefficient := 1, powers := [(13, 1), (30, 1), (48, 1)] }, { coefficient := 1, powers := [(17, 1), (30, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1)] }, { coefficient := 1, powers := [(3, 1), (35, 1)] }, { coefficient := 1, powers := [(14, 1), (19, 1)] }, { coefficient := 1, powers := [(19, 1), (55, 1)] }, { coefficient := 1, powers := [(25, 1), (44, 1)] }, { coefficient := 1, powers := [(35, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (50, 1)] }, { coefficient := 1, powers := [(6, 1), (32, 1)] }, { coefficient := 1, powers := [(9, 1), (25, 1)] }, { coefficient := 1, powers := [(19, 1), (50, 1)] }, { coefficient := 1, powers := [(25, 1), (41, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1), (51, 1)] }, { coefficient := 1, powers := [(3, 1), (35, 1), (51, 1)] }, { coefficient := 1, powers := [(3, 1), (58, 1)] }, { coefficient := 1, powers := [(9, 1), (44, 1)] }, { coefficient := 1, powers := [(14, 1), (19, 1), (51, 1)] }, { coefficient := 1, powers := [(14, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (37, 1), (50, 1)] }, { coefficient := 1, powers := [(6, 1), (37, 1), (41, 1)] }, { coefficient := 1, powers := [(9, 1), (29, 1), (45, 1)] }, { coefficient := 1, powers := [(9, 1), (37, 1), (38, 1)] }, { coefficient := 1, powers := [(23, 1), (45, 1), (50, 1)] }, { coefficient := 1, powers := [(29, 1), (41, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (38, 1), (58, 1)] }, { coefficient := 1, powers := [(0, 1), (41, 1), (55, 1)] }, { coefficient := 1, powers := [(0, 1), (44, 1), (50, 1)] }, { coefficient := 1, powers := [(3, 1), (25, 1), (58, 1)] }, { coefficient := 1, powers := [(3, 1), (32, 1), (55, 1)] }, { coefficient := 1, powers := [(3, 1), (35, 1), (50, 1)] }, { coefficient := 1, powers := [(6, 1), (19, 1), (58, 1)] }, { coefficient := 1, powers := [(6, 1), (32, 1), (44, 1)] }, { coefficient := 1, powers := [(6, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(9, 1), (19, 1), (55, 1)] }, { coefficient := 1, powers := [(9, 1), (25, 1), (44, 1)] }, { coefficient := 1, powers := [(9, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(14, 1), (19, 1), (50, 1)] }, { coefficient := 1, powers := [(14, 1), (25, 1), (41, 1)] }, { coefficient := 1, powers := [(14, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (40, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (43, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (49, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (37, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (49, 1)] }, { coefficient := 1, powers := [(8, 1), (37, 1), (43, 1)] }, { coefficient := 1, powers := [(13, 1), (24, 1), (57, 1)] }, { coefficient := 1, powers := [(13, 1), (31, 1), (49, 1)] }, { coefficient := 1, powers := [(13, 1), (37, 1), (40, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (54, 1)] }, { coefficient := 1, powers := [(18, 1), (31, 1), (43, 1)] }, { coefficient := 1, powers := [(18, 1), (34, 1), (40, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (61, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(41, 1)] }],
  [{ coefficient := 1, powers := [(42, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(43, 1)] }],
  [{ coefficient := 1, powers := [(55, 1)] }],
  [{ coefficient := 1, powers := [(56, 1), (64, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(57, 1), (65, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(25, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 42 → SparsePoly (Fin 68) := ![
  [{ coefficient := -1, powers := [(24, 1), (26, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (5, 1), (9, 1), (29, 1), (37, 1), (54, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 1), (9, 1), (13, 1), (29, 1), (37, 1), (40, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(17, 1), (49, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (49, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(24, 1), (57, 1)] }, { coefficient := -1, powers := [(30, 1), (48, 1), (57, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (5, 1), (29, 1), (35, 1), (51, 1), (52, 1), (54, 1)] }, { coefficient := 1, powers := [(0, 1), (5, 1), (30, 1), (35, 1), (50, 1), (52, 1), (54, 1)] }, { coefficient := 1, powers := [(0, 1), (5, 1), (30, 1), (35, 1), (51, 1), (54, 1)] }, { coefficient := -1, powers := [(0, 1), (13, 1), (29, 1), (35, 1), (40, 1), (51, 1), (52, 1)] }, { coefficient := 1, powers := [(0, 1), (13, 1), (30, 1), (35, 1), (40, 1), (50, 1), (52, 1)] }, { coefficient := 1, powers := [(0, 1), (13, 1), (30, 1), (35, 1), (40, 1), (51, 1)] }, { coefficient := 1, powers := [(2, 1), (19, 1), (20, 1), (52, 1), (54, 1), (61, 2)] }, { coefficient := 1, powers := [(2, 1), (20, 1), (52, 1), (54, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (9, 1), (23, 1), (35, 1), (52, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (9, 1), (29, 1), (35, 1), (52, 1), (54, 1)] }, { coefficient := -1, powers := [(5, 1), (14, 1), (30, 1), (32, 1), (52, 1), (54, 1), (63, 1)] }, { coefficient := -1, powers := [(5, 1), (19, 1), (23, 1), (52, 1), (54, 1), (58, 1)] }, { coefficient := -1, powers := [(5, 1), (19, 1), (29, 1), (52, 1), (54, 1), (58, 1)] }, { coefficient := 2, powers := [(5, 1), (19, 1), (30, 1), (35, 1), (50, 1), (52, 1), (54, 1)] }, { coefficient := -1, powers := [(5, 1), (23, 1), (35, 1), (50, 1), (52, 1), (54, 1)] }, { coefficient := -1, powers := [(5, 1), (23, 1), (35, 1), (51, 1), (54, 1)] }, { coefficient := -1, powers := [(5, 1), (23, 1), (54, 1), (58, 1)] }, { coefficient := -1, powers := [(5, 1), (29, 1), (35, 1), (50, 1), (52, 1), (54, 1)] }, { coefficient := -1, powers := [(5, 1), (29, 1), (35, 1), (51, 1), (54, 1)] }, { coefficient := -1, powers := [(5, 1), (29, 1), (54, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (32, 1), (44, 1), (52, 1), (54, 1), (63, 1)] }, { coefficient := 1, powers := [(9, 1), (13, 1), (23, 1), (35, 1), (40, 1), (52, 1)] }, { coefficient := 1, powers := [(9, 1), (13, 1), (29, 1), (35, 1), (40, 1), (52, 1)] }, { coefficient := -1, powers := [(13, 1), (14, 1), (30, 1), (32, 1), (40, 1), (52, 1), (63, 1)] }, { coefficient := -1, powers := [(13, 1), (19, 1), (23, 1), (40, 1), (52, 1), (58, 1)] }, { coefficient := -1, powers := [(13, 1), (19, 1), (29, 1), (40, 1), (52, 1), (58, 1)] }, { coefficient := 2, powers := [(13, 1), (19, 1), (30, 1), (35, 1), (40, 1), (50, 1), (52, 1)] }, { coefficient := -1, powers := [(13, 1), (20, 1), (31, 1), (52, 1), (61, 1)] }, { coefficient := -1, powers := [(13, 1), (23, 1), (35, 1), (40, 1), (50, 1), (52, 1)] }, { coefficient := -1, powers := [(13, 1), (23, 1), (35, 1), (40, 1), (51, 1)] }, { coefficient := -1, powers := [(13, 1), (23, 1), (40, 1), (58, 1)] }, { coefficient := -1, powers := [(13, 1), (24, 1), (26, 1), (52, 2), (57, 1), (65, 1)] }, { coefficient := 1, powers := [(13, 1), (24, 1), (52, 1), (53, 1), (57, 1), (65, 1)] }, { coefficient := -1, powers := [(13, 1), (29, 1), (35, 1), (40, 1), (50, 1), (52, 1)] }, { coefficient := -1, powers := [(13, 1), (29, 1), (35, 1), (40, 1), (51, 1)] }, { coefficient := -1, powers := [(13, 1), (29, 1), (40, 1), (58, 1)] }, { coefficient := 1, powers := [(13, 1), (30, 1), (32, 1), (40, 1), (44, 1), (52, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (19, 1), (54, 1), (61, 2)] }, { coefficient := -1, powers := [(13, 1), (31, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (5, 1), (9, 1), (37, 1), (54, 1), (62, 1)] }, { coefficient := 1, powers := [(0, 1), (9, 1), (13, 1), (37, 1), (40, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(31, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (19, 1), (37, 1), (54, 1)] }, { coefficient := 1, powers := [(13, 1), (19, 1), (37, 1), (40, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (35, 1), (45, 1), (54, 1)] }, { coefficient := -1, powers := [(13, 1), (35, 1), (40, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (19, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(18, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (5, 1), (29, 1), (35, 1), (51, 1), (54, 1)] }, { coefficient := -1, powers := [(0, 1), (5, 1), (30, 1), (35, 1), (50, 1), (54, 1)] }, { coefficient := 1, powers := [(0, 1), (13, 1), (29, 1), (35, 1), (40, 1), (51, 1)] }, { coefficient := -1, powers := [(0, 1), (13, 1), (30, 1), (35, 1), (40, 1), (50, 1)] }, { coefficient := -1, powers := [(2, 1), (19, 1), (20, 1), (54, 1), (61, 2)] }, { coefficient := -1, powers := [(2, 1), (20, 1), (54, 1), (61, 1)] }, { coefficient := -1, powers := [(5, 1), (9, 1), (23, 1), (35, 1), (54, 1)] }, { coefficient := -1, powers := [(5, 1), (9, 1), (29, 1), (35, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (14, 1), (30, 1), (32, 1), (54, 1), (63, 1)] }, { coefficient := 1, powers := [(5, 1), (19, 1), (23, 1), (54, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (19, 1), (29, 1), (54, 1), (58, 1)] }, { coefficient := -2, powers := [(5, 1), (19, 1), (30, 1), (35, 1), (50, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (23, 1), (35, 1), (50, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (35, 1), (50, 1), (54, 1)] }, { coefficient := -1, powers := [(5, 1), (30, 1), (32, 1), (44, 1), (54, 1), (63, 1)] }, { coefficient := -1, powers := [(9, 1), (13, 1), (23, 1), (35, 1), (40, 1)] }, { coefficient := -1, powers := [(9, 1), (13, 1), (29, 1), (35, 1), (40, 1)] }, { coefficient := 1, powers := [(13, 1), (14, 1), (30, 1), (32, 1), (40, 1), (63, 1)] }, { coefficient := 1, powers := [(13, 1), (19, 1), (23, 1), (40, 1), (58, 1)] }, { coefficient := 1, powers := [(13, 1), (19, 1), (29, 1), (40, 1), (58, 1)] }, { coefficient := -2, powers := [(13, 1), (19, 1), (30, 1), (35, 1), (40, 1), (50, 1)] }, { coefficient := 1, powers := [(13, 1), (20, 1), (31, 1), (61, 1)] }, { coefficient := 1, powers := [(13, 1), (23, 1), (35, 1), (40, 1), (50, 1)] }, { coefficient := 1, powers := [(13, 1), (24, 1), (26, 1), (52, 1), (57, 1), (65, 1)] }, { coefficient := 1, powers := [(13, 1), (29, 1), (35, 1), (40, 1), (50, 1)] }, { coefficient := -1, powers := [(13, 1), (30, 1), (32, 1), (40, 1), (44, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(24, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (5, 1), (29, 1), (35, 1), (50, 1), (52, 1), (54, 1)] }, { coefficient := 1, powers := [(0, 1), (13, 1), (29, 1), (35, 1), (40, 1), (50, 1), (52, 1)] }, { coefficient := -1, powers := [(5, 1), (14, 1), (29, 1), (32, 1), (52, 1), (54, 1), (63, 1)] }, { coefficient := 2, powers := [(5, 1), (19, 1), (29, 1), (35, 1), (50, 1), (52, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (32, 1), (44, 1), (52, 1), (54, 1), (63, 1)] }, { coefficient := -1, powers := [(13, 1), (14, 1), (29, 1), (32, 1), (40, 1), (52, 1), (63, 1)] }, { coefficient := 2, powers := [(13, 1), (19, 1), (29, 1), (35, 1), (40, 1), (50, 1), (52, 1)] }, { coefficient := 1, powers := [(13, 1), (29, 1), (32, 1), (40, 1), (44, 1), (52, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(49, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (5, 1), (35, 1), (51, 1), (54, 1)] }, { coefficient := 1, powers := [(0, 1), (5, 1), (54, 1), (58, 1)] }, { coefficient := -1, powers := [(0, 1), (13, 1), (35, 1), (40, 1), (51, 1)] }, { coefficient := 1, powers := [(0, 1), (13, 1), (40, 1), (58, 1)] }, { coefficient := -1, powers := [(5, 1), (35, 1), (50, 1), (54, 1)] }, { coefficient := -1, powers := [(13, 1), (35, 1), (40, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(24, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (5, 1), (30, 1), (35, 1), (54, 1)] }, { coefficient := -1, powers := [(0, 1), (13, 1), (30, 1), (35, 1), (40, 1)] }, { coefficient := 1, powers := [(5, 1), (23, 1), (35, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (35, 1), (54, 1)] }, { coefficient := 1, powers := [(13, 1), (23, 1), (35, 1), (40, 1)] }, { coefficient := 1, powers := [(13, 1), (29, 1), (35, 1), (40, 1)] }],
  [{ coefficient := -1, powers := [(13, 1), (24, 1), (52, 1), (57, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (5, 1), (29, 1), (35, 1), (50, 1), (54, 1)] }, { coefficient := -1, powers := [(0, 1), (13, 1), (29, 1), (35, 1), (40, 1), (50, 1)] }, { coefficient := 1, powers := [(5, 1), (14, 1), (29, 1), (32, 1), (54, 1), (63, 1)] }, { coefficient := -2, powers := [(5, 1), (19, 1), (29, 1), (35, 1), (50, 1), (54, 1)] }, { coefficient := -1, powers := [(5, 1), (29, 1), (32, 1), (44, 1), (54, 1), (63, 1)] }, { coefficient := 1, powers := [(13, 1), (14, 1), (29, 1), (32, 1), (40, 1), (63, 1)] }, { coefficient := -2, powers := [(13, 1), (19, 1), (29, 1), (35, 1), (40, 1), (50, 1)] }, { coefficient := -1, powers := [(13, 1), (29, 1), (32, 1), (40, 1), (44, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (5, 1), (35, 1), (54, 1)] }, { coefficient := 1, powers := [(0, 1), (13, 1), (35, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (5, 1), (35, 1), (50, 1), (54, 1)] }, { coefficient := 1, powers := [(0, 1), (13, 1), (35, 1), (40, 1), (50, 1)] }, { coefficient := -1, powers := [(5, 1), (14, 1), (32, 1), (54, 1), (63, 1)] }, { coefficient := 2, powers := [(5, 1), (19, 1), (35, 1), (50, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (44, 1), (54, 1), (63, 1)] }, { coefficient := -1, powers := [(13, 1), (14, 1), (32, 1), (40, 1), (63, 1)] }, { coefficient := 2, powers := [(13, 1), (19, 1), (35, 1), (40, 1), (50, 1)] }, { coefficient := 1, powers := [(13, 1), (32, 1), (40, 1), (44, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (5, 1), (37, 1), (50, 1), (54, 1)] }, { coefficient := -1, powers := [(0, 1), (13, 1), (37, 1), (40, 1), (50, 1)] }, { coefficient := -2, powers := [(5, 1), (19, 1), (37, 1), (50, 1), (54, 1)] }, { coefficient := -2, powers := [(13, 1), (19, 1), (37, 1), (40, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(57, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (5, 1), (37, 1), (51, 1), (54, 1)] }, { coefficient := 1, powers := [(0, 1), (13, 1), (37, 1), (40, 1), (51, 1)] }, { coefficient := 1, powers := [(5, 1), (37, 1), (50, 1), (54, 1)] }, { coefficient := 1, powers := [(13, 1), (37, 1), (40, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (14, 1), (37, 1), (54, 1)] }, { coefficient := 1, powers := [(13, 1), (14, 1), (37, 1), (40, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (5, 1), (37, 1), (54, 1)] }, { coefficient := -1, powers := [(0, 1), (13, 1), (37, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (35, 1), (54, 1)] }, { coefficient := 1, powers := [(13, 1), (35, 1), (40, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (37, 1), (54, 1)] }, { coefficient := -1, powers := [(13, 1), (37, 1), (40, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(2, 1), (19, 1), (49, 1), (54, 1), (61, 1)] }, { coefficient := -1, powers := [(2, 1), (40, 1), (60, 1)] }, { coefficient := 1, powers := [(13, 1), (31, 1), (49, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (5, 1), (9, 1), (37, 1), (44, 1), (54, 1)] }, { coefficient := -1, powers := [(0, 1), (9, 1), (13, 1), (37, 1), (40, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (5, 1), (14, 1), (37, 1), (54, 1)] }, { coefficient := 1, powers := [(0, 1), (13, 1), (14, 1), (37, 1), (40, 1)] }, { coefficient := -1, powers := [(5, 1), (23, 1), (35, 1), (45, 1), (54, 1)] }, { coefficient := -1, powers := [(5, 1), (29, 1), (35, 1), (45, 1), (54, 1)] }, { coefficient := -1, powers := [(13, 1), (23, 1), (35, 1), (40, 1), (45, 1)] }, { coefficient := -1, powers := [(13, 1), (29, 1), (35, 1), (40, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (6, 1), (14, 1), (32, 1), (37, 1), (54, 1)] }, { coefficient := -1, powers := [(5, 1), (6, 1), (32, 1), (37, 1), (44, 1), (54, 1)] }, { coefficient := 1, powers := [(6, 1), (13, 1), (14, 1), (32, 1), (37, 1), (40, 1)] }, { coefficient := -1, powers := [(6, 1), (13, 1), (32, 1), (37, 1), (40, 1), (44, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (2, 1), (57, 1), (61, 1)] }, { coefficient := -1, powers := [(2, 1), (26, 1), (45, 1), (61, 1)] }, { coefficient := -1, powers := [(2, 1), (56, 1), (57, 1), (64, 1)] }, { coefficient := 1, powers := [(2, 1), (57, 1)] }, { coefficient := 1, powers := [(8, 1), (37, 1)] }, { coefficient := -1, powers := [(17, 1), (30, 1), (57, 1), (64, 1)] }, { coefficient := -1, powers := [(18, 1), (31, 1)] }],
  [{ coefficient := 1, powers := [(0, 2), (5, 1), (37, 1), (42, 1), (50, 1), (54, 1)] }, { coefficient := 1, powers := [(0, 2), (13, 1), (37, 1), (40, 1), (42, 1), (50, 1)] }, { coefficient := -1, powers := [(0, 1), (5, 1), (9, 1), (17, 1), (23, 1), (37, 1), (54, 1), (62, 1)] }, { coefficient := 2, powers := [(0, 1), (5, 1), (19, 1), (37, 1), (42, 1), (50, 1), (54, 1)] }, { coefficient := -1, powers := [(0, 1), (5, 1), (19, 1), (37, 1), (51, 1), (54, 1)] }, { coefficient := 1, powers := [(0, 1), (5, 1), (37, 1), (41, 1), (54, 1)] }, { coefficient := 1, powers := [(0, 1), (5, 1), (37, 1), (50, 1), (54, 1)] }, { coefficient := -1, powers := [(0, 1), (9, 1), (13, 1), (17, 1), (23, 1), (37, 1), (40, 1), (62, 1)] }, { coefficient := 2, powers := [(0, 1), (13, 1), (19, 1), (37, 1), (40, 1), (42, 1), (50, 1)] }, { coefficient := -1, powers := [(0, 1), (13, 1), (19, 1), (37, 1), (40, 1), (51, 1)] }, { coefficient := 1, powers := [(0, 1), (13, 1), (37, 1), (40, 1), (41, 1)] }, { coefficient := 1, powers := [(0, 1), (13, 1), (37, 1), (40, 1), (50, 1)] }, { coefficient := 1, powers := [(3, 1), (5, 1), (32, 1), (37, 1), (54, 1)] }, { coefficient := 1, powers := [(3, 1), (13, 1), (32, 1), (37, 1), (40, 1)] }, { coefficient := 1, powers := [(5, 1), (19, 1), (37, 1), (50, 1), (54, 1)] }, { coefficient := 1, powers := [(13, 1), (19, 1), (37, 1), (40, 1), (50, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (34, 1), (57, 1)] }, { coefficient := 1, powers := [(13, 1), (19, 1), (30, 1), (48, 1), (57, 1)] }, { coefficient := -1, powers := [(13, 1), (24, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (19, 1), (24, 1), (52, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (5, 1), (14, 1), (37, 1), (42, 1), (50, 1), (54, 1)] }, { coefficient := -1, powers := [(0, 1), (5, 1), (29, 1), (35, 1), (42, 1), (45, 1), (50, 1), (52, 1), (54, 1)] }, { coefficient := 1, powers := [(0, 1), (5, 1), (29, 1), (35, 1), (45, 1), (51, 1), (52, 1), (54, 1)] }, { coefficient := -1, powers := [(0, 1), (5, 1), (29, 1), (35, 1), (47, 1), (50, 1), (52, 1), (54, 1)] }, { coefficient := -1, powers := [(0, 1), (5, 1), (30, 1), (35, 1), (45, 1), (50, 1), (52, 1), (54, 1)] }, { coefficient := -1, powers := [(0, 1), (5, 1), (30, 1), (35, 1), (45, 1), (51, 1), (54, 1)] }, { coefficient := -1, powers := [(0, 1), (5, 1), (37, 1), (44, 1), (51, 1), (54, 1)] }, { coefficient := 1, powers := [(0, 1), (13, 1), (14, 1), (37, 1), (40, 1), (42, 1), (50, 1)] }, { coefficient := -1, powers := [(0, 1), (13, 1), (29, 1), (35, 1), (40, 1), (42, 1), (45, 1), (50, 1), (52, 1)] }, { coefficient := 1, powers := [(0, 1), (13, 1), (29, 1), (35, 1), (40, 1), (45, 1), (51, 1), (52, 1)] }, { coefficient := -1, powers := [(0, 1), (13, 1), (29, 1), (35, 1), (40, 1), (47, 1), (50, 1), (52, 1)] }, { coefficient := -1, powers := [(0, 1), (13, 1), (30, 1), (35, 1), (40, 1), (45, 1), (50, 1), (52, 1)] }, { coefficient := -1, powers := [(0, 1), (13, 1), (30, 1), (35, 1), (40, 1), (45, 1), (51, 1)] }, { coefficient := -1, powers := [(0, 1), (13, 1), (37, 1), (40, 1), (44, 1), (51, 1)] }, { coefficient := -1, powers := [(2, 1), (19, 1), (20, 1), (45, 1), (52, 1), (54, 1), (61, 2)] }, { coefficient := -1, powers := [(2, 1), (19, 1), (49, 1), (54, 1), (61, 2)] }, { coefficient := -1, powers := [(2, 1), (20, 1), (45, 1), (52, 1), (54, 1), (61, 1)] }, { coefficient := 1, powers := [(3, 1), (5, 1), (37, 1), (54, 1), (58, 1)] }, { coefficient := 1, powers := [(3, 1), (13, 1), (37, 1), (40, 1), (58, 1)] }, { coefficient := -1, powers := [(5, 1), (9, 1), (14, 1), (37, 1), (54, 1)] }, { coefficient := -1, powers := [(5, 1), (9, 1), (23, 1), (35, 1), (45, 1), (52, 1), (54, 1)] }, { coefficient := -1, powers := [(5, 1), (9, 1), (29, 1), (35, 1), (45, 1), (52, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (9, 1), (37, 1), (44, 1), (54, 1)] }, { coefficient := 2, powers := [(5, 1), (14, 1), (19, 1), (37, 1), (42, 1), (50, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (14, 1), (29, 1), (32, 1), (42, 1), (45, 1), (52, 1), (54, 1), (63, 1)] }, { coefficient := 1, powers := [(5, 1), (14, 1), (29, 1), (32, 1), (47, 1), (52, 1), (54, 1), (63, 1)] }, { coefficient := 1, powers := [(5, 1), (14, 1), (30, 1), (32, 1), (45, 1), (52, 1), (54, 1), (63, 1)] }, { coefficient := 1, powers := [(5, 1), (19, 1), (23, 1), (45, 1), (52, 1), (54, 1), (58, 1)] }, { coefficient := -2, powers := [(5, 1), (19, 1), (29, 1), (35, 1), (42, 1), (45, 1), (50, 1), (52, 1), (54, 1)] }, { coefficient := -2, powers := [(5, 1), (19, 1), (29, 1), (35, 1), (47, 1), (50, 1), (52, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (19, 1), (29, 1), (45, 1), (52, 1), (54, 1), (58, 1)] }, { coefficient := -2, powers := [(5, 1), (19, 1), (30, 1), (35, 1), (45, 1), (50, 1), (52, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (23, 1), (35, 1), (45, 1), (50, 1), (52, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (23, 1), (35, 1), (45, 1), (51, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (23, 1), (45, 1), (54, 1), (58, 1)] }, { coefficient := -1, powers := [(5, 1), (29, 1), (32, 1), (42, 1), (44, 1), (45, 1), (52, 1), (54, 1), (63, 1)] }, { coefficient := -1, powers := [(5, 1), (29, 1), (32, 1), (44, 1), (47, 1), (52, 1), (54, 1), (63, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (35, 1), (45, 1), (50, 1), (52, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (35, 1), (45, 1), (51, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (45, 1), (54, 1), (58, 1)] }, { coefficient := -1, powers := [(5, 1), (30, 1), (32, 1), (44, 1), (45, 1), (52, 1), (54, 1), (63, 1)] }, { coefficient := -1, powers := [(5, 1), (37, 1), (44, 1), (50, 1), (54, 1)] }, { coefficient := -1, powers := [(9, 1), (13, 1), (14, 1), (37, 1), (40, 1)] }, { coefficient := -1, powers := [(9, 1), (13, 1), (23, 1), (35, 1), (40, 1), (45, 1), (52, 1)] }, { coefficient := -1, powers := [(9, 1), (13, 1), (29, 1), (35, 1), (40, 1), (45, 1), (52, 1)] }, { coefficient := 1, powers := [(9, 1), (13, 1), (37, 1), (40, 1), (44, 1)] }, { coefficient := 2, powers := [(13, 1), (14, 1), (19, 1), (37, 1), (40, 1), (42, 1), (50, 1)] }, { coefficient := 1, powers := [(13, 1), (14, 1), (29, 1), (32, 1), (40, 1), (42, 1), (45, 1), (52, 1), (63, 1)] }, { coefficient := 1, powers := [(13, 1), (14, 1), (29, 1), (32, 1), (40, 1), (47, 1), (52, 1), (63, 1)] }, { coefficient := 1, powers := [(13, 1), (14, 1), (30, 1), (32, 1), (40, 1), (45, 1), (52, 1), (63, 1)] }, { coefficient := 1, powers := [(13, 1), (19, 1), (23, 1), (40, 1), (45, 1), (52, 1), (58, 1)] }, { coefficient := -2, powers := [(13, 1), (19, 1), (29, 1), (35, 1), (40, 1), (42, 1), (45, 1), (50, 1), (52, 1)] }, { coefficient := -2, powers := [(13, 1), (19, 1), (29, 1), (35, 1), (40, 1), (47, 1), (50, 1), (52, 1)] }, { coefficient := 1, powers := [(13, 1), (19, 1), (29, 1), (40, 1), (45, 1), (52, 1), (58, 1)] }, { coefficient := -2, powers := [(13, 1), (19, 1), (30, 1), (35, 1), (40, 1), (45, 1), (50, 1), (52, 1)] }, { coefficient := 1, powers := [(13, 1), (20, 1), (31, 1), (45, 1), (52, 1), (61, 1)] }, { coefficient := 1, powers := [(13, 1), (23, 1), (35, 1), (40, 1), (45, 1), (50, 1), (52, 1)] }, { coefficient := 1, powers := [(13, 1), (23, 1), (35, 1), (40, 1), (45, 1), (51, 1)] }, { coefficient := 1, powers := [(13, 1), (23, 1), (40, 1), (45, 1), (58, 1)] }, { coefficient := 1, powers := [(13, 1), (24, 1), (26, 1), (45, 1), (52, 2), (57, 1), (65, 1)] }, { coefficient := -1, powers := [(13, 1), (24, 1), (45, 1), (52, 1), (53, 1), (57, 1), (65, 1)] }, { coefficient := -1, powers := [(13, 1), (29, 1), (32, 1), (40, 1), (42, 1), (44, 1), (45, 1), (52, 1), (63, 1)] }, { coefficient := -1, powers := [(13, 1), (29, 1), (32, 1), (40, 1), (44, 1), (47, 1), (52, 1), (63, 1)] }, { coefficient := 1, powers := [(13, 1), (29, 1), (35, 1), (40, 1), (45, 1), (50, 1), (52, 1)] }, { coefficient := 1, powers := [(13, 1), (29, 1), (35, 1), (40, 1), (45, 1), (51, 1)] }, { coefficient := 1, powers := [(13, 1), (29, 1), (40, 1), (45, 1), (58, 1)] }, { coefficient := -1, powers := [(13, 1), (30, 1), (32, 1), (40, 1), (44, 1), (45, 1), (52, 1), (63, 1)] }, { coefficient := 1, powers := [(13, 1), (31, 1), (49, 1), (61, 1)] }, { coefficient := -1, powers := [(13, 1), (37, 1), (40, 1), (44, 1), (50, 1)] }, { coefficient := 1, powers := [(17, 1), (24, 1), (47, 1), (54, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (42, 1), (54, 1)] }]
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

#print axioms Krenn.Component18.SelectedLeafB5_2_3_3.selectedHasNoCommonZero

end Krenn.Component18.SelectedLeafB5_2_3_3
