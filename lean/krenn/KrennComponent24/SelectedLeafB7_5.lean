import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component24.SelectedLeafB7_5

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "a7efea2076ef8bd1a19f7a8d9750bf9c0bc88924f75784cead682acbefce9d1a"
def certificateSHA256 : String := "ddf57c0aaa93a48e603705903684ae88d31a13e9887ce6a3383e1ca5b8ecc4c0"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 62 → Fin 670 := ![
  2,
  8,
  9,
  13,
  14,
  15,
  16,
  17,
  91,
  129,
  149,
  151,
  152,
  153,
  154,
  160,
  161,
  162,
  164,
  166,
  196,
  266,
  282,
  299,
  300,
  301,
  305,
  306,
  307,
  316,
  319,
  321,
  323,
  330,
  417,
  430,
  434,
  441,
  442,
  448,
  452,
  457,
  462,
  486,
  490,
  547,
  584,
  589,
  590,
  596,
  597,
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
  669
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 62 → SparsePoly (Fin 67) := ![
  [{ coefficient := 1, powers := [(8, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(15, 1), (21, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (55, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(15, 1), (21, 1)] }, { coefficient := 1, powers := [(21, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(15, 1), (51, 1)] }, { coefficient := 1, powers := [(51, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(15, 1), (54, 1)] }, { coefficient := 1, powers := [(35, 1), (39, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (20, 1)] }, { coefficient := 1, powers := [(18, 1), (26, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (45, 1)] }, { coefficient := 1, powers := [(19, 1), (20, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (58, 1)] }, { coefficient := 1, powers := [(31, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (45, 1)] }, { coefficient := 1, powers := [(29, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (54, 1)] }, { coefficient := -1, powers := [(30, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(31, 1), (42, 1)] }, { coefficient := 1, powers := [(31, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1), (58, 1)] }, { coefficient := 1, powers := [(58, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (24, 1), (60, 1)] }, { coefficient := 1, powers := [(18, 1), (31, 1)] }],
  [{ coefficient := 1, powers := [(15, 1), (21, 1), (54, 1)] }, { coefficient := 1, powers := [(15, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (26, 1), (49, 1)] }, { coefficient := 1, powers := [(19, 1), (21, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1)] }, { coefficient := 1, powers := [(20, 1), (45, 1)] }, { coefficient := 1, powers := [(26, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (49, 1)] }, { coefficient := 1, powers := [(21, 1), (45, 1)] }, { coefficient := 1, powers := [(26, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (51, 1)] }, { coefficient := 1, powers := [(20, 1), (51, 1)] }, { coefficient := 1, powers := [(26, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (44, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (56, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (59, 1)] }, { coefficient := 1, powers := [(9, 1), (56, 1)] }, { coefficient := 1, powers := [(15, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (61, 1)] }, { coefficient := 1, powers := [(14, 1), (58, 1)] }, { coefficient := 1, powers := [(19, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (46, 1)] }, { coefficient := 1, powers := [(14, 1), (57, 1)] }, { coefficient := 1, powers := [(18, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(15, 1), (42, 1)] }, { coefficient := 1, powers := [(15, 1), (53, 1)] }, { coefficient := 1, powers := [(35, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (42, 1)] }, { coefficient := 1, powers := [(19, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (58, 1)] }, { coefficient := 1, powers := [(31, 1), (49, 1)] }, { coefficient := 1, powers := [(37, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1), (51, 1)] }, { coefficient := 1, powers := [(26, 1), (46, 1), (51, 1)] }, { coefficient := 1, powers := [(51, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (20, 1), (57, 1)] }, { coefficient := 1, powers := [(14, 1)] }, { coefficient := 1, powers := [(18, 1), (20, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (26, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (26, 1), (42, 1)] }, { coefficient := 1, powers := [(19, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (45, 1), (54, 1)] }, { coefficient := 1, powers := [(30, 1), (43, 1), (45, 1)] }, { coefficient := 1, powers := [(30, 1), (49, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1)] }, { coefficient := 1, powers := [(26, 1), (42, 1), (45, 1)] }, { coefficient := 1, powers := [(26, 1), (47, 1)] }, { coefficient := 1, powers := [(45, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (48, 1)] }, { coefficient := 1, powers := [(6, 1), (21, 1), (60, 1)] }, { coefficient := 1, powers := [(21, 1)] }, { coefficient := 1, powers := [(26, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (45, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (45, 1)] }, { coefficient := 1, powers := [(18, 1), (37, 1), (38, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (49, 1)] }, { coefficient := 1, powers := [(5, 1), (37, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (49, 1)] }, { coefficient := 1, powers := [(19, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1)] }, { coefficient := 1, powers := [(14, 1), (31, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (61, 1)] }, { coefficient := 1, powers := [(14, 1), (49, 1)] }, { coefficient := 1, powers := [(19, 1), (21, 1), (54, 1)] }, { coefficient := 1, powers := [(19, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (48, 1), (51, 1)] }, { coefficient := 1, powers := [(21, 1), (51, 1)] }, { coefficient := 1, powers := [(26, 1), (43, 1)] }, { coefficient := 1, powers := [(26, 1), (48, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (49, 1), (54, 1)] }, { coefficient := 1, powers := [(21, 1), (45, 1), (54, 1)] }, { coefficient := 1, powers := [(43, 1), (45, 1)] }, { coefficient := 1, powers := [(49, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (37, 1), (42, 1)] }, { coefficient := 1, powers := [(29, 1), (42, 1), (45, 1)] }, { coefficient := 1, powers := [(29, 1), (47, 1)] }, { coefficient := 1, powers := [(30, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1)] }, { coefficient := 1, powers := [(6, 1), (60, 1)] }, { coefficient := 1, powers := [(26, 1), (42, 1)] }, { coefficient := 1, powers := [(26, 1), (46, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1), (56, 1)] }, { coefficient := 1, powers := [(6, 1), (35, 1), (42, 1)] }, { coefficient := 1, powers := [(15, 1), (26, 1), (42, 1)] }, { coefficient := 1, powers := [(15, 1)] }, { coefficient := 1, powers := [(56, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1), (56, 1)] }, { coefficient := 1, powers := [(6, 1), (35, 1), (43, 1)] }, { coefficient := 1, powers := [(15, 1), (21, 1), (51, 1)] }, { coefficient := 1, powers := [(15, 1), (26, 1), (43, 1)] }, { coefficient := 1, powers := [(21, 1), (51, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (41, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (44, 1), (50, 1)] }, { coefficient := 1, powers := [(13, 1), (24, 1), (56, 1)] }, { coefficient := 1, powers := [(13, 1), (29, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (41, 1), (58, 1)] }, { coefficient := 1, powers := [(8, 1), (37, 1), (41, 1)] }, { coefficient := 1, powers := [(13, 1), (24, 1), (58, 1)] }, { coefficient := 1, powers := [(13, 1), (31, 1), (45, 1)] }, { coefficient := 1, powers := [(19, 1), (31, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1)] }, { coefficient := 1, powers := [(3, 1), (35, 1)] }, { coefficient := 1, powers := [(15, 1), (20, 1)] }, { coefficient := 1, powers := [(20, 1), (56, 1)] }, { coefficient := 1, powers := [(26, 1), (44, 1)] }, { coefficient := 1, powers := [(35, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (50, 1)] }, { coefficient := 1, powers := [(6, 1), (32, 1)] }, { coefficient := 1, powers := [(9, 1), (26, 1)] }, { coefficient := 1, powers := [(20, 1), (50, 1)] }, { coefficient := 1, powers := [(26, 1), (41, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (45, 1), (51, 1)] }, { coefficient := 1, powers := [(14, 1), (29, 1), (45, 1)] }, { coefficient := 1, powers := [(14, 1), (37, 1), (38, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (51, 1)] }, { coefficient := 1, powers := [(19, 1), (34, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (38, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (41, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (44, 1), (50, 1)] }, { coefficient := 1, powers := [(3, 1), (26, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (32, 1), (56, 1)] }, { coefficient := 1, powers := [(3, 1), (35, 1), (50, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (32, 1), (44, 1)] }, { coefficient := 1, powers := [(6, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(9, 1), (20, 1), (56, 1)] }, { coefficient := 1, powers := [(9, 1), (26, 1), (44, 1)] }, { coefficient := 1, powers := [(9, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(15, 1), (20, 1), (50, 1)] }, { coefficient := 1, powers := [(15, 1), (26, 1), (41, 1)] }, { coefficient := 1, powers := [(15, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (40, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (43, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (49, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (37, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (25, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (49, 1)] }, { coefficient := 1, powers := [(8, 1), (37, 1), (43, 1)] }, { coefficient := 1, powers := [(14, 1), (25, 1), (58, 1)] }, { coefficient := 1, powers := [(14, 1), (31, 1), (49, 1)] }, { coefficient := 1, powers := [(14, 1), (37, 1), (40, 1)] }, { coefficient := 1, powers := [(19, 1), (25, 1), (55, 1)] }, { coefficient := 1, powers := [(19, 1), (31, 1), (43, 1)] }, { coefficient := 1, powers := [(19, 1), (34, 1), (40, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (64, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(41, 1), (65, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(42, 1)] }],
  [{ coefficient := 1, powers := [(43, 1), (66, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 62 → SparsePoly (Fin 67) := ![
  [{ coefficient := 1, powers := [(9, 1), (24, 1), (35, 1), (38, 1), (49, 1), (51, 1)] }, { coefficient := -1, powers := [(24, 1), (35, 1), (38, 1), (49, 1), (50, 1), (51, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (29, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (24, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (9, 1), (22, 1), (35, 1), (38, 1), (49, 1), (63, 1)] }, { coefficient := -1, powers := [(2, 1), (22, 1), (35, 1), (38, 1), (49, 1), (50, 1), (63, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (29, 1), (50, 1), (64, 1)] }, { coefficient := 1, powers := [(20, 1), (29, 1), (50, 1), (64, 1)] }, { coefficient := 1, powers := [(26, 1), (29, 1), (41, 1), (64, 1)] }, { coefficient := 1, powers := [(26, 1), (29, 1), (50, 1), (64, 1)] }, { coefficient := 1, powers := [(29, 1), (32, 1), (38, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(9, 1), (24, 1), (35, 1), (38, 1), (49, 1)] }, { coefficient := 1, powers := [(24, 1), (35, 1), (38, 1), (49, 1), (50, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (24, 1), (50, 1), (64, 1)] }, { coefficient := 1, powers := [(20, 1), (24, 1), (50, 1), (64, 1)] }, { coefficient := 1, powers := [(24, 1), (26, 1), (41, 1), (64, 1)] }, { coefficient := 1, powers := [(24, 1), (26, 1), (50, 1), (64, 1)] }, { coefficient := 1, powers := [(24, 1), (32, 1), (38, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(9, 1), (25, 1), (35, 1), (38, 1), (51, 1)] }, { coefficient := 1, powers := [(25, 1), (35, 1), (38, 1), (50, 1), (51, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (41, 1), (51, 1), (66, 1)] }, { coefficient := 1, powers := [(3, 1), (32, 1), (51, 1), (66, 1)] }, { coefficient := -1, powers := [(32, 1), (38, 1), (51, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (9, 1), (35, 1), (38, 1), (49, 1), (63, 1)] }, { coefficient := 1, powers := [(2, 1), (35, 1), (38, 1), (49, 1), (50, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (41, 1), (51, 1), (53, 1), (66, 1)] }, { coefficient := -1, powers := [(3, 1), (32, 1), (51, 1), (53, 1), (66, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1), (51, 1), (53, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (21, 1), (41, 1), (53, 1), (66, 1)] }, { coefficient := 1, powers := [(3, 1), (21, 1), (32, 1), (53, 1), (66, 1)] }, { coefficient := -1, powers := [(21, 1), (32, 1), (38, 1), (53, 1), (66, 1)] }, { coefficient := -1, powers := [(21, 1), (41, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (21, 1), (41, 1), (66, 1)] }, { coefficient := 1, powers := [(3, 1), (21, 1), (32, 1), (66, 1)] }, { coefficient := -1, powers := [(21, 1), (32, 1), (38, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (25, 1), (35, 1), (38, 1), (47, 1), (55, 1)] }, { coefficient := -1, powers := [(9, 1), (29, 1), (35, 1), (40, 1), (45, 1), (51, 1), (62, 1)] }, { coefficient := 1, powers := [(9, 1), (31, 1), (35, 1), (38, 1), (43, 1), (47, 1)] }, { coefficient := -1, powers := [(9, 1), (31, 1), (35, 1), (38, 1), (49, 1), (51, 1), (62, 1)] }, { coefficient := -1, powers := [(25, 1), (35, 1), (38, 1), (47, 1), (50, 1), (55, 1)] }, { coefficient := 1, powers := [(29, 1), (35, 1), (40, 1), (45, 1), (50, 1), (51, 1), (62, 1)] }, { coefficient := -1, powers := [(31, 1), (35, 1), (38, 1), (43, 1), (47, 1), (50, 1)] }, { coefficient := 1, powers := [(31, 1), (35, 1), (38, 1), (49, 1), (50, 1), (51, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (25, 1), (35, 1), (38, 1), (55, 1)] }, { coefficient := 1, powers := [(9, 1), (31, 1), (35, 1), (38, 1), (43, 1)] }, { coefficient := -1, powers := [(25, 1), (35, 1), (38, 1), (50, 1), (55, 1)] }, { coefficient := -1, powers := [(31, 1), (35, 1), (38, 1), (43, 1), (50, 1)] }],
  [{ coefficient := -1, powers := [(9, 1), (13, 1), (35, 1), (38, 1), (43, 1), (65, 1)] }, { coefficient := 1, powers := [(13, 1), (35, 1), (38, 1), (43, 1), (50, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(9, 1), (14, 1), (20, 1), (35, 1), (40, 1), (54, 1), (66, 1)] }, { coefficient := -1, powers := [(9, 1), (18, 1), (35, 1), (38, 1), (55, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1), (35, 1), (40, 1), (50, 1), (54, 1), (66, 1)] }, { coefficient := 1, powers := [(18, 1), (35, 1), (38, 1), (50, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (14, 1), (20, 1), (35, 1), (40, 1), (49, 1), (66, 1)] }, { coefficient := -1, powers := [(14, 1), (20, 1), (35, 1), (40, 1), (49, 1), (50, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(9, 1), (14, 1), (20, 1), (35, 1), (38, 1), (49, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1), (35, 1), (38, 1), (49, 1), (50, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (9, 1), (35, 1), (38, 1), (41, 1), (43, 1), (65, 1)] }, { coefficient := 1, powers := [(2, 1), (9, 1), (35, 1), (38, 1), (43, 1)] }, { coefficient := 1, powers := [(2, 1), (35, 1), (38, 1), (41, 1), (43, 1), (50, 1), (65, 1)] }, { coefficient := -1, powers := [(2, 1), (35, 1), (38, 1), (43, 1), (50, 1)] }, { coefficient := 1, powers := [(5, 1), (9, 1), (34, 1), (35, 1), (38, 1)] }, { coefficient := -1, powers := [(5, 1), (34, 1), (35, 1), (38, 1), (50, 1)] }],
  [{ coefficient := -1, powers := [(9, 1), (35, 1), (38, 1), (49, 1), (51, 1)] }, { coefficient := 1, powers := [(35, 1), (38, 1), (49, 1), (50, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (41, 1), (66, 1)] }, { coefficient := -1, powers := [(3, 1), (32, 1), (66, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(9, 1), (31, 1), (35, 1), (38, 1), (54, 1)] }, { coefficient := 1, powers := [(31, 1), (35, 1), (38, 1), (50, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(9, 1), (14, 1), (30, 1), (35, 1), (40, 1)] }, { coefficient := 1, powers := [(9, 1), (18, 1), (29, 1), (35, 1), (40, 1), (51, 1), (62, 1)] }, { coefficient := 1, powers := [(14, 1), (30, 1), (35, 1), (40, 1), (50, 1)] }, { coefficient := -1, powers := [(18, 1), (29, 1), (35, 1), (40, 1), (50, 1), (51, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (18, 1), (31, 1), (35, 1), (38, 1), (54, 1)] }, { coefficient := -1, powers := [(18, 1), (31, 1), (35, 1), (38, 1), (50, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (18, 1), (31, 1), (35, 1), (38, 1), (49, 1), (62, 1)] }, { coefficient := -1, powers := [(18, 1), (31, 1), (35, 1), (38, 1), (49, 1), (50, 1), (62, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (50, 1), (64, 1)] }, { coefficient := -1, powers := [(20, 1), (50, 1), (64, 1)] }, { coefficient := -1, powers := [(26, 1), (41, 1), (64, 1)] }, { coefficient := -1, powers := [(26, 1), (50, 1), (64, 1)] }, { coefficient := -1, powers := [(32, 1), (38, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(20, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (25, 1), (35, 1), (38, 1)] }, { coefficient := -1, powers := [(25, 1), (35, 1), (38, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (20, 1), (31, 1), (35, 1), (38, 1), (49, 1)] }, { coefficient := -1, powers := [(20, 1), (31, 1), (35, 1), (38, 1), (49, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (21, 1), (41, 1), (51, 1), (66, 1)] }, { coefficient := -1, powers := [(3, 1), (21, 1), (32, 1), (51, 1), (66, 1)] }, { coefficient := 1, powers := [(21, 1), (32, 1), (38, 1), (51, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(9, 1), (20, 1), (25, 1), (35, 1), (38, 1), (55, 1)] }, { coefficient := -1, powers := [(9, 1), (20, 1), (31, 1), (35, 1), (38, 1), (43, 1)] }, { coefficient := 1, powers := [(20, 1), (25, 1), (35, 1), (38, 1), (50, 1), (55, 1)] }, { coefficient := 1, powers := [(20, 1), (31, 1), (35, 1), (38, 1), (43, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (18, 1), (35, 1), (38, 1), (51, 1)] }, { coefficient := -1, powers := [(18, 1), (35, 1), (38, 1), (50, 1), (51, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (21, 1), (59, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(9, 1), (31, 1), (35, 1), (38, 1), (49, 1)] }, { coefficient := 1, powers := [(31, 1), (35, 1), (38, 1), (49, 1), (50, 1)] }],
  [{ coefficient := -1, powers := [(9, 1), (25, 1), (35, 1), (38, 1), (55, 1)] }, { coefficient := -1, powers := [(9, 1), (31, 1), (35, 1), (38, 1), (43, 1)] }, { coefficient := 1, powers := [(25, 1), (35, 1), (38, 1), (50, 1), (55, 1)] }, { coefficient := 1, powers := [(31, 1), (35, 1), (38, 1), (43, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (14, 1), (20, 1), (35, 1), (40, 1), (66, 1)] }, { coefficient := -1, powers := [(14, 1), (20, 1), (35, 1), (40, 1), (50, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(9, 1), (14, 1), (29, 1), (35, 1), (40, 1)] }, { coefficient := 1, powers := [(14, 1), (29, 1), (35, 1), (40, 1), (50, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (51, 1), (59, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(9, 1), (35, 1), (40, 1), (51, 1)] }, { coefficient := 1, powers := [(35, 1), (40, 1), (50, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (35, 1), (38, 1), (55, 1)] }, { coefficient := -1, powers := [(35, 1), (38, 1), (50, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (35, 1), (38, 1), (49, 1)] }, { coefficient := -1, powers := [(35, 1), (38, 1), (49, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (31, 1), (35, 1), (38, 1)] }, { coefficient := -1, powers := [(31, 1), (35, 1), (38, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (59, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(9, 1), (18, 1), (31, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(18, 1), (31, 1), (35, 1), (38, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (9, 1), (14, 1), (35, 1), (40, 1)] }, { coefficient := -1, powers := [(0, 1), (14, 1), (35, 1), (40, 1), (50, 1)] }, { coefficient := 1, powers := [(9, 1), (14, 1), (26, 1), (35, 1), (40, 1)] }, { coefficient := -1, powers := [(14, 1), (26, 1), (35, 1), (40, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (21, 1), (51, 1), (59, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (41, 1), (43, 1), (66, 1)] }, { coefficient := 1, powers := [(3, 1), (32, 1), (43, 1), (66, 1)] }, { coefficient := -1, powers := [(20, 1), (50, 1)] }, { coefficient := -1, powers := [(32, 1), (38, 1), (43, 1), (66, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(41, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (35, 1), (38, 1), (43, 1), (65, 1)] }, { coefficient := -1, powers := [(35, 1), (38, 1), (43, 1), (50, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(50, 1)] }],
  [{ coefficient := 1, powers := [(44, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (35, 1), (40, 1)] }, { coefficient := -1, powers := [(35, 1), (40, 1), (50, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(9, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(35, 1), (38, 1), (50, 1)] }],
  [{ coefficient := -1, powers := [(9, 1), (18, 1), (29, 1), (35, 1), (40, 1), (45, 1), (51, 1)] }, { coefficient := -1, powers := [(9, 1), (18, 1), (31, 1), (35, 1), (38, 1), (49, 1), (51, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (35, 1), (40, 1), (45, 1), (50, 1), (51, 1)] }, { coefficient := 1, powers := [(18, 1), (31, 1), (35, 1), (38, 1), (49, 1), (50, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (9, 1), (35, 1), (38, 1), (49, 1), (55, 1)] }, { coefficient := -1, powers := [(2, 1), (35, 1), (38, 1), (49, 1), (50, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (38, 1), (59, 1)] }, { coefficient := -1, powers := [(0, 1), (41, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (44, 1), (50, 1)] }, { coefficient := 1, powers := [(20, 1), (44, 1), (50, 1)] }, { coefficient := 1, powers := [(26, 1), (41, 1), (44, 1)] }, { coefficient := 1, powers := [(26, 1), (44, 1), (50, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1), (44, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (9, 1), (35, 1), (37, 1), (38, 1), (43, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (37, 1), (38, 1), (43, 1), (50, 1)] }, { coefficient := -1, powers := [(9, 1), (19, 1), (31, 1), (35, 1), (38, 1), (43, 1)] }, { coefficient := 1, powers := [(19, 1), (31, 1), (35, 1), (38, 1), (43, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(0, 2), (41, 1), (43, 1), (56, 1), (66, 1)] }, { coefficient := 1, powers := [(0, 1), (2, 1), (9, 1), (35, 1), (38, 1), (41, 1), (43, 1), (58, 1), (65, 1)] }, { coefficient := -1, powers := [(0, 1), (2, 1), (9, 1), (35, 1), (38, 1), (43, 1), (58, 1)] }, { coefficient := -1, powers := [(0, 1), (2, 1), (35, 1), (38, 1), (41, 1), (43, 1), (50, 1), (58, 1), (65, 1)] }, { coefficient := 1, powers := [(0, 1), (2, 1), (35, 1), (38, 1), (43, 1), (50, 1), (58, 1)] }, { coefficient := -1, powers := [(0, 1), (3, 1), (32, 1), (43, 1), (56, 1), (66, 1)] }, { coefficient := -1, powers := [(0, 1), (5, 1), (9, 1), (34, 1), (35, 1), (38, 1), (58, 1)] }, { coefficient := 1, powers := [(0, 1), (5, 1), (34, 1), (35, 1), (38, 1), (50, 1), (58, 1)] }, { coefficient := -1, powers := [(0, 1), (6, 1), (9, 1), (14, 1), (35, 1), (37, 1), (40, 1)] }, { coefficient := 1, powers := [(0, 1), (6, 1), (14, 1), (35, 1), (37, 1), (40, 1), (50, 1)] }, { coefficient := 1, powers := [(0, 1), (6, 1), (35, 1), (41, 1), (43, 1), (66, 1)] }, { coefficient := -1, powers := [(0, 1), (9, 1), (14, 1), (29, 1), (35, 1), (40, 1), (45, 1)] }, { coefficient := 1, powers := [(0, 1), (14, 1), (29, 1), (35, 1), (40, 1), (45, 1), (50, 1)] }, { coefficient := -1, powers := [(0, 1), (15, 1), (21, 1), (41, 1), (51, 1), (66, 1)] }, { coefficient := 1, powers := [(0, 1), (15, 1), (26, 1), (41, 1), (43, 1), (66, 1)] }, { coefficient := 1, powers := [(0, 1), (20, 1), (50, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (32, 1), (38, 1), (43, 1), (56, 1), (66, 1)] }, { coefficient := -1, powers := [(0, 1), (32, 1), (38, 1), (56, 1)] }, { coefficient := -1, powers := [(3, 1), (6, 1), (32, 1), (35, 1), (43, 1), (66, 1)] }, { coefficient := 1, powers := [(3, 1), (15, 1), (21, 1), (32, 1), (51, 1), (66, 1)] }, { coefficient := -1, powers := [(3, 1), (15, 1), (26, 1), (32, 1), (43, 1), (66, 1)] }, { coefficient := -1, powers := [(3, 1), (21, 1), (26, 1), (51, 1), (59, 1), (66, 1)] }, { coefficient := -1, powers := [(6, 1), (9, 1), (14, 1), (26, 1), (35, 1), (37, 1), (40, 1)] }, { coefficient := 1, powers := [(6, 1), (14, 1), (26, 1), (35, 1), (37, 1), (40, 1), (50, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1), (35, 1), (50, 1)] }, { coefficient := 1, powers := [(6, 1), (32, 1), (35, 1), (38, 1), (43, 1), (66, 1)] }, { coefficient := -1, powers := [(6, 1), (32, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(9, 1), (14, 1), (20, 1), (31, 1), (35, 1), (38, 1), (49, 1)] }, { coefficient := 1, powers := [(9, 1), (19, 1), (20, 1), (25, 1), (35, 1), (38, 1), (55, 1)] }, { coefficient := 1, powers := [(9, 1), (19, 1), (20, 1), (31, 1), (35, 1), (38, 1), (43, 1)] }, { coefficient := 1, powers := [(9, 1), (19, 1), (25, 1), (26, 1), (35, 1), (38, 1), (55, 1)] }, { coefficient := 1, powers := [(9, 1), (19, 1), (26, 1), (31, 1), (35, 1), (38, 1), (43, 1)] }, { coefficient := -1, powers := [(14, 1), (20, 1), (31, 1), (35, 1), (38, 1), (49, 1), (50, 1)] }, { coefficient := 1, powers := [(15, 1), (20, 1), (26, 1), (50, 1)] }, { coefficient := -1, powers := [(15, 1), (21, 1), (32, 1), (38, 1), (51, 1), (66, 1)] }, { coefficient := 1, powers := [(15, 1), (26, 1), (32, 1), (38, 1), (43, 1), (66, 1)] }, { coefficient := -1, powers := [(15, 1), (26, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [(19, 1), (20, 1), (25, 1), (35, 1), (38, 1), (50, 1), (55, 1)] }, { coefficient := -1, powers := [(19, 1), (20, 1), (31, 1), (35, 1), (38, 1), (43, 1), (50, 1)] }, { coefficient := -1, powers := [(19, 1), (25, 1), (26, 1), (35, 1), (38, 1), (50, 1), (55, 1)] }, { coefficient := -1, powers := [(19, 1), (26, 1), (31, 1), (35, 1), (38, 1), (43, 1), (50, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (26, 1), (59, 1)] }, { coefficient := -1, powers := [(3, 1), (32, 1), (56, 1)] }, { coefficient := -1, powers := [(6, 1), (35, 1), (41, 1)] }, { coefficient := -1, powers := [(9, 1), (14, 1), (20, 1), (30, 1), (35, 1), (40, 1), (45, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1), (30, 1), (35, 1), (40, 1), (45, 1), (50, 1)] }, { coefficient := -1, powers := [(15, 1), (26, 1), (41, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1), (56, 1)] }]
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
    (values : Fin 67 → R) :
    ¬ ∀ index : Fin 62,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component24.SelectedLeafB7_5.selectedHasNoCommonZero

end Krenn.Component24.SelectedLeafB7_5
