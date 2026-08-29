import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component18.SelectedLeafB5_2_2_7

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "d96f0ae9bb6f806e6f9c2b6b3fabd41a5255582a534946a321f839a0797d7459"
def certificateSHA256 : String := "5adbf027cb4cd63f2a6324dec95f710a81a7746be18eb1acfeb29b3faa2b82e6"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 60 → Fin 670 := ![
  0,
  1,
  5,
  7,
  9,
  10,
  13,
  16,
  19,
  142,
  147,
  162,
  163,
  164,
  167,
  168,
  170,
  272,
  294,
  295,
  300,
  301,
  302,
  314,
  315,
  318,
  319,
  322,
  323,
  327,
  403,
  409,
  412,
  424,
  433,
  435,
  437,
  438,
  443,
  449,
  463,
  478,
  479,
  491,
  580,
  590,
  602,
  603,
  610,
  655,
  657,
  658,
  660,
  661,
  663,
  664,
  666,
  667,
  668,
  669
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 60 → SparsePoly (Fin 68) := ![
  [{ coefficient := 1, powers := [(3, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (54, 1)] }, { coefficient := 1, powers := [(19, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (34, 1)] }, { coefficient := 1, powers := [(34, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (19, 1)] }, { coefficient := 1, powers := [(17, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (45, 1)] }, { coefficient := 1, powers := [(18, 1), (19, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (49, 1)] }, { coefficient := 1, powers := [(18, 1), (20, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (45, 1)] }, { coefficient := 1, powers := [(29, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (53, 1)] }, { coefficient := 1, powers := [(31, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1), (54, 1)] }, { coefficient := 1, powers := [(54, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (27, 1), (49, 1)] }, { coefficient := 1, powers := [(18, 1), (21, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1)] }, { coefficient := 1, powers := [(19, 1), (45, 1)] }, { coefficient := 1, powers := [(25, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (49, 1)] }, { coefficient := 1, powers := [(20, 1), (45, 1)] }, { coefficient := 1, powers := [(25, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (44, 1)] }, { coefficient := 1, powers := [(17, 1), (23, 1), (55, 1)] }, { coefficient := 1, powers := [(17, 1), (29, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (60, 1)] }, { coefficient := 1, powers := [(13, 1), (49, 1)] }, { coefficient := 1, powers := [(18, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (58, 1)] }, { coefficient := 1, powers := [(9, 1), (55, 1)] }, { coefficient := 1, powers := [(14, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (22, 1)] }, { coefficient := 1, powers := [(17, 1), (27, 1), (42, 1)] }, { coefficient := 1, powers := [(17, 1), (27, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (47, 1)] }, { coefficient := 1, powers := [(18, 1), (42, 1)] }, { coefficient := 1, powers := [(18, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (54, 1)] }, { coefficient := 1, powers := [(31, 1), (43, 1)] }, { coefficient := 1, powers := [(34, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(30, 1), (53, 1)] }, { coefficient := 1, powers := [(31, 1), (42, 1)] }, { coefficient := 1, powers := [(31, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1), (54, 1)] }, { coefficient := 1, powers := [(3, 1), (35, 1), (54, 1)] }, { coefficient := 1, powers := [(14, 1), (19, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1), (52, 1)] }, { coefficient := 1, powers := [(19, 1), (45, 1), (52, 1)] }, { coefficient := 1, powers := [(45, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (49, 1), (52, 1)] }, { coefficient := 1, powers := [(20, 1), (45, 1), (52, 1)] }, { coefficient := 1, powers := [(49, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (19, 1), (52, 1)] }, { coefficient := 1, powers := [(17, 1), (19, 1), (56, 1)] }, { coefficient := 1, powers := [(17, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (25, 1), (47, 1)] }, { coefficient := 1, powers := [(18, 1), (25, 1), (42, 1)] }, { coefficient := 1, powers := [(18, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (48, 1), (52, 1)] }, { coefficient := 1, powers := [(21, 1), (48, 1), (56, 1)] }, { coefficient := 1, powers := [(28, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1)] }, { coefficient := 1, powers := [(25, 1), (42, 1), (45, 1)] }, { coefficient := 1, powers := [(25, 1), (47, 1)] }, { coefficient := 1, powers := [(45, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (49, 1)] }, { coefficient := 1, powers := [(5, 1), (37, 1)] }, { coefficient := 1, powers := [(17, 1), (29, 1), (49, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (52, 1)] }, { coefficient := 1, powers := [(17, 1), (23, 1), (52, 1)] }, { coefficient := 1, powers := [(17, 1), (23, 1), (56, 1)] }, { coefficient := 1, powers := [(17, 1), (30, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1)] }, { coefficient := 1, powers := [(13, 1), (31, 1)] }, { coefficient := 1, powers := [(17, 1), (23, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (37, 1)] }, { coefficient := 1, powers := [(23, 1), (45, 1)] }, { coefficient := 1, powers := [(29, 1), (45, 1)] }, { coefficient := 1, powers := [(37, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (60, 1)] }, { coefficient := 1, powers := [(13, 1), (26, 1), (47, 1)] }, { coefficient := 1, powers := [(13, 1), (57, 1)] }, { coefficient := 1, powers := [(18, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (42, 1)] }, { coefficient := 1, powers := [(17, 1), (46, 1)] }, { coefficient := 1, powers := [(17, 1), (52, 1)] }, { coefficient := 1, powers := [(17, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1), (52, 1)] }, { coefficient := 1, powers := [(42, 1), (45, 1)] }, { coefficient := 1, powers := [(45, 1), (52, 1)] }, { coefficient := 1, powers := [(47, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1)] }, { coefficient := 1, powers := [(17, 1), (23, 1)] }, { coefficient := 1, powers := [(17, 1), (29, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (60, 1)] }, { coefficient := 1, powers := [(13, 1), (29, 1), (45, 1)] }, { coefficient := 1, powers := [(13, 1), (37, 1), (38, 1)] }, { coefficient := 1, powers := [(18, 1), (34, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (29, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (23, 1), (59, 1)] }, { coefficient := 1, powers := [(23, 1)] }, { coefficient := 1, powers := [(29, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1)] }, { coefficient := 1, powers := [(6, 1), (59, 1)] }, { coefficient := 1, powers := [(25, 1), (42, 1)] }, { coefficient := 1, powers := [(25, 1), (46, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (41, 1), (55, 1)] }, { coefficient := 1, powers := [(2, 1), (44, 1), (50, 1)] }, { coefficient := 1, powers := [(12, 1), (23, 1), (55, 1)] }, { coefficient := 1, powers := [(12, 1), (29, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1)] }, { coefficient := 1, powers := [(3, 1), (35, 1)] }, { coefficient := 1, powers := [(14, 1), (19, 1)] }, { coefficient := 1, powers := [(19, 1), (55, 1)] }, { coefficient := 1, powers := [(25, 1), (44, 1)] }, { coefficient := 1, powers := [(35, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (50, 1)] }, { coefficient := 1, powers := [(6, 1), (32, 1)] }, { coefficient := 1, powers := [(9, 1), (25, 1)] }, { coefficient := 1, powers := [(19, 1), (50, 1)] }, { coefficient := 1, powers := [(25, 1), (41, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1), (51, 1)] }, { coefficient := 1, powers := [(3, 1), (35, 1), (51, 1)] }, { coefficient := 1, powers := [(3, 1), (58, 1)] }, { coefficient := 1, powers := [(9, 1), (44, 1)] }, { coefficient := 1, powers := [(14, 1), (19, 1), (51, 1)] }, { coefficient := 1, powers := [(14, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (38, 1), (58, 1)] }, { coefficient := 1, powers := [(0, 1), (41, 1), (55, 1)] }, { coefficient := 1, powers := [(0, 1), (44, 1), (50, 1)] }, { coefficient := 1, powers := [(3, 1), (25, 1), (58, 1)] }, { coefficient := 1, powers := [(3, 1), (32, 1), (55, 1)] }, { coefficient := 1, powers := [(3, 1), (35, 1), (50, 1)] }, { coefficient := 1, powers := [(6, 1), (19, 1), (58, 1)] }, { coefficient := 1, powers := [(6, 1), (32, 1), (44, 1)] }, { coefficient := 1, powers := [(6, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(9, 1), (19, 1), (55, 1)] }, { coefficient := 1, powers := [(9, 1), (25, 1), (44, 1)] }, { coefficient := 1, powers := [(9, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(14, 1), (19, 1), (50, 1)] }, { coefficient := 1, powers := [(14, 1), (25, 1), (41, 1)] }, { coefficient := 1, powers := [(14, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (40, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (43, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (49, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (37, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (49, 1)] }, { coefficient := 1, powers := [(8, 1), (37, 1), (43, 1)] }, { coefficient := 1, powers := [(13, 1), (24, 1), (57, 1)] }, { coefficient := 1, powers := [(13, 1), (31, 1), (49, 1)] }, { coefficient := 1, powers := [(13, 1), (37, 1), (40, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (54, 1)] }, { coefficient := 1, powers := [(18, 1), (31, 1), (43, 1)] }, { coefficient := 1, powers := [(18, 1), (34, 1), (40, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (61, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(41, 1)] }],
  [{ coefficient := 1, powers := [(43, 1)] }],
  [{ coefficient := 1, powers := [(55, 1)] }],
  [{ coefficient := 1, powers := [(57, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (65, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(28, 1), (66, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(31, 1), (67, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 60 → SparsePoly (Fin 68) := ![
  [{ coefficient := 1, powers := [(17, 1), (29, 1), (40, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (23, 1), (40, 1), (59, 1)] }],
  [{ coefficient := -2, powers := [(18, 1), (19, 1), (24, 1), (29, 1), (54, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (37, 1), (40, 1), (59, 1), (65, 1)] }, { coefficient := -1, powers := [(31, 1), (49, 1), (65, 1)] }, { coefficient := 1, powers := [(37, 1), (40, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(23, 1), (40, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(24, 1), (26, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (18, 1), (24, 1), (50, 1)] }, { coefficient := 2, powers := [(6, 1), (18, 1), (24, 1), (32, 1)] }, { coefficient := 2, powers := [(9, 1), (18, 1), (24, 1), (25, 1)] }, { coefficient := 4, powers := [(18, 1), (19, 1), (24, 1), (50, 1)] }],
  [{ coefficient := 2, powers := [(6, 1), (18, 1), (24, 1), (29, 1), (32, 1), (54, 1), (62, 1)] }, { coefficient := -2, powers := [(9, 1), (18, 1), (24, 1), (25, 1), (29, 1), (54, 1), (62, 1)] }, { coefficient := 2, powers := [(18, 1), (19, 1), (24, 1), (29, 1), (50, 1), (54, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(17, 1), (49, 1)] }],
  [{ coefficient := -2, powers := [(18, 1), (24, 1), (38, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (40, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (30, 1), (45, 1), (54, 1), (61, 1)] }, { coefficient := 1, powers := [(22, 1), (25, 1), (30, 1), (49, 1), (54, 1), (61, 1), (66, 1)] }, { coefficient := 1, powers := [(23, 1), (49, 1), (52, 1), (54, 1)] }, { coefficient := 1, powers := [(23, 1), (49, 1), (54, 1), (56, 1)] }, { coefficient := -1, powers := [(23, 1), (49, 1), (54, 1), (61, 1)] }, { coefficient := 1, powers := [(24, 1), (25, 1), (45, 1), (46, 1), (54, 1), (61, 1)] }, { coefficient := 1, powers := [(24, 1), (25, 1), (45, 1), (54, 1), (56, 1), (61, 1)] }, { coefficient := -1, powers := [(24, 1), (25, 1), (47, 1), (52, 1), (54, 1)] }, { coefficient := -1, powers := [(24, 1), (45, 1), (54, 1), (61, 1)] }, { coefficient := 1, powers := [(25, 1), (34, 1), (40, 1), (45, 1), (46, 1), (61, 1)] }, { coefficient := 1, powers := [(25, 1), (34, 1), (40, 1), (45, 1), (56, 1), (61, 1)] }, { coefficient := -1, powers := [(25, 1), (34, 1), (40, 1), (47, 1), (52, 1)] }, { coefficient := 1, powers := [(30, 1), (49, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (22, 1), (25, 1), (30, 1), (54, 1), (61, 1), (66, 1)] }, { coefficient := -1, powers := [(20, 1), (23, 1), (54, 1), (61, 1)] }, { coefficient := 1, powers := [(20, 1), (30, 1), (54, 1)] }, { coefficient := -1, powers := [(24, 1), (25, 1), (42, 1), (54, 1)] }, { coefficient := -1, powers := [(24, 1), (25, 1), (52, 1), (54, 1)] }, { coefficient := -1, powers := [(25, 1), (34, 1), (40, 1), (42, 1)] }, { coefficient := -1, powers := [(25, 1), (34, 1), (40, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(19, 1), (22, 1), (25, 1), (30, 1), (54, 1), (61, 1), (66, 1)] }, { coefficient := 1, powers := [(19, 1), (23, 1), (54, 1), (61, 1)] }, { coefficient := -1, powers := [(19, 1), (30, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(17, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (25, 1), (30, 1), (54, 1), (67, 1)] }],
  [{ coefficient := -1, powers := [(18, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (30, 1), (52, 1), (54, 1), (66, 1)] }, { coefficient := 1, powers := [(25, 1), (30, 1), (54, 1), (56, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(17, 1), (20, 1), (30, 1), (54, 1), (61, 1)] }, { coefficient := -1, powers := [(17, 1), (24, 1), (25, 1), (42, 1), (52, 1), (54, 1)] }, { coefficient := -1, powers := [(17, 1), (24, 1), (25, 1), (46, 1), (54, 1), (61, 1)] }, { coefficient := -1, powers := [(17, 1), (24, 1), (25, 1), (54, 1), (56, 1), (61, 1)] }, { coefficient := 1, powers := [(17, 1), (24, 1), (54, 1), (61, 1)] }, { coefficient := -1, powers := [(17, 1), (25, 1), (34, 1), (40, 1), (42, 1), (52, 1)] }, { coefficient := -1, powers := [(17, 1), (25, 1), (34, 1), (40, 1), (46, 1), (61, 1)] }, { coefficient := -1, powers := [(17, 1), (25, 1), (34, 1), (40, 1), (56, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (52, 1), (54, 1)] }, { coefficient := -1, powers := [(17, 1), (22, 1), (25, 1), (30, 1), (54, 1), (61, 1), (66, 1)] }, { coefficient := 1, powers := [(17, 1), (23, 1), (54, 1), (61, 1)] }],
  [{ coefficient := -2, powers := [(6, 1), (18, 1), (24, 1), (32, 1), (54, 1), (62, 1)] }, { coefficient := 2, powers := [(9, 1), (18, 1), (24, 1), (25, 1), (54, 1), (62, 1)] }, { coefficient := -2, powers := [(18, 1), (19, 1), (24, 1), (50, 1), (54, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(31, 1)] }],
  [{ coefficient := -2, powers := [(18, 1), (19, 1), (24, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (30, 1), (49, 1), (54, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (24, 1), (25, 1), (52, 1), (54, 1)] }, { coefficient := 1, powers := [(19, 1), (25, 1), (34, 1), (40, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (18, 1), (46, 1)] }, { coefficient := 1, powers := [(18, 1), (25, 1), (46, 1)] }, { coefficient := 1, powers := [(18, 1)] }],
  [{ coefficient := -1, powers := [(18, 1), (24, 1), (25, 1), (54, 1), (67, 1)] }],
  [{ coefficient := 2, powers := [(9, 1), (18, 1), (24, 1)] }, { coefficient := 2, powers := [(18, 1), (24, 1), (25, 1), (51, 1)] }, { coefficient := -2, powers := [(18, 1), (24, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (24, 1), (25, 1), (42, 1), (54, 1)] }, { coefficient := 1, powers := [(17, 1), (25, 1), (34, 1), (40, 1), (42, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(23, 1), (49, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (54, 1)] }, { coefficient := 1, powers := [(34, 1), (40, 1)] }],
  [{ coefficient := -1, powers := [(18, 1), (25, 1), (30, 1), (54, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (24, 1), (25, 1), (52, 1), (54, 1)] }, { coefficient := 1, powers := [(17, 1), (25, 1), (34, 1), (40, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(54, 1)] }],
  [{ coefficient := -1, powers := [(25, 1), (49, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(49, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (40, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(24, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (25, 1), (45, 1), (54, 1)] }, { coefficient := -1, powers := [(25, 1), (27, 1), (30, 1), (49, 1), (54, 1), (66, 1)] }, { coefficient := 1, powers := [(25, 1), (34, 1), (40, 1), (45, 1)] }],
  [{ coefficient := -1, powers := [(17, 1), (24, 1), (25, 1), (54, 1)] }, { coefficient := -1, powers := [(17, 1), (25, 1), (34, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(40, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(40, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(17, 1), (40, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(18, 1), (34, 1), (40, 1)] }],
  [{ coefficient := 2, powers := [(18, 1), (19, 1), (24, 1), (54, 1), (62, 1)] }],
  [{ coefficient := -2, powers := [(9, 1), (18, 1), (24, 1), (54, 1)] }],
  [{ coefficient := -2, powers := [(14, 1), (18, 1), (24, 1), (54, 1)] }],
  [{ coefficient := -2, powers := [(18, 1), (24, 1), (25, 1), (54, 1)] }],
  [{ coefficient := 2, powers := [(18, 1), (24, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(17, 1), (20, 1), (30, 1), (45, 1), (54, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (25, 1), (30, 1), (49, 1), (54, 1), (66, 1)] }, { coefficient := -1, powers := [(17, 1), (23, 1), (49, 1), (54, 1)] }, { coefficient := 1, powers := [(17, 1), (24, 1), (25, 1), (45, 1), (46, 1), (54, 1)] }, { coefficient := 1, powers := [(17, 1), (24, 1), (25, 1), (45, 1), (54, 1), (56, 1)] }, { coefficient := -1, powers := [(17, 1), (24, 1), (45, 1), (54, 1)] }, { coefficient := 1, powers := [(17, 1), (25, 1), (34, 1), (40, 1), (45, 1), (46, 1)] }, { coefficient := 1, powers := [(17, 1), (25, 1), (34, 1), (40, 1), (45, 1), (56, 1)] }],
  [{ coefficient := 2, powers := [(6, 1), (18, 1), (24, 1), (32, 1), (44, 1), (54, 1)] }, { coefficient := -2, powers := [(9, 1), (18, 1), (24, 1), (25, 1), (44, 1), (54, 1)] }, { coefficient := -2, powers := [(18, 1), (19, 1), (24, 1), (38, 1), (54, 1), (58, 1)] }],
  [{ coefficient := -2, powers := [(6, 1), (18, 1), (24, 1), (35, 1), (54, 1)] }, { coefficient := 2, powers := [(14, 1), (18, 1), (24, 1), (25, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (18, 1), (31, 1), (46, 1)] }, { coefficient := 1, powers := [(8, 1), (37, 1)] }, { coefficient := -1, powers := [(18, 1), (25, 1), (31, 1), (46, 1)] }, { coefficient := -1, powers := [(18, 1), (31, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (18, 1), (24, 1), (41, 1), (54, 1)] }, { coefficient := -2, powers := [(2, 1), (18, 1), (19, 1), (24, 1), (41, 1), (54, 1), (62, 1)] }, { coefficient := -2, powers := [(3, 1), (18, 1), (24, 1), (32, 1), (54, 1)] }, { coefficient := 2, powers := [(6, 1), (17, 1), (18, 1), (23, 1), (24, 1), (32, 1), (54, 1), (62, 1)] }, { coefficient := -2, powers := [(9, 1), (17, 1), (18, 1), (23, 1), (24, 1), (25, 1), (54, 1), (62, 1)] }, { coefficient := 2, powers := [(9, 1), (18, 1), (19, 1), (24, 1), (54, 1)] }, { coefficient := -2, powers := [(12, 1), (18, 1), (19, 1), (23, 1), (24, 1), (54, 1), (62, 1)] }, { coefficient := 2, powers := [(17, 1), (18, 1), (19, 1), (23, 1), (24, 1), (50, 1), (54, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (43, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (13, 1), (37, 1), (40, 1), (59, 1)] }, { coefficient := 1, powers := [(13, 1), (31, 1), (49, 1)] }, { coefficient := -1, powers := [(13, 1), (37, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (25, 1), (30, 1), (48, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (24, 1), (25, 1), (42, 1), (54, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (25, 1), (46, 1), (54, 1)] }, { coefficient := -1, powers := [(18, 1), (25, 1), (30, 1), (48, 1), (54, 1)] }]
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
    ¬ ∀ index : Fin 60,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component18.SelectedLeafB5_2_2_7.selectedHasNoCommonZero

end Krenn.Component18.SelectedLeafB5_2_2_7
