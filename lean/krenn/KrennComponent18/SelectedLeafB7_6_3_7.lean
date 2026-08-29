import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component18.SelectedLeafB7_6_3_7

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "76253fc3f9238586d561477b09d949139ac8b2ea923c233b8856f23ab292949d"
def certificateSHA256 : String := "5f60e2d50f36e52120dd6b7496fcf8ad54bd4d10979a01682eb8f378df3725e0"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 33 → Fin 670 := ![
  7,
  9,
  10,
  15,
  19,
  143,
  147,
  159,
  162,
  301,
  318,
  323,
  403,
  435,
  436,
  437,
  438,
  442,
  443,
  449,
  458,
  478,
  479,
  584,
  591,
  657,
  658,
  659,
  660,
  663,
  665,
  666,
  667
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 33 → SparsePoly (Fin 71) := ![
  [{ coefficient := 1, powers := [(13, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(15, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (54, 1)] }, { coefficient := 1, powers := [(15, 1), (21, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (34, 1)] }, { coefficient := 1, powers := [(34, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (46, 1)] }, { coefficient := 1, powers := [(13, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (19, 1)] }, { coefficient := 1, powers := [(17, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (60, 1)] }, { coefficient := 1, powers := [(13, 1), (49, 1)] }, { coefficient := 1, powers := [(18, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (54, 1)] }, { coefficient := 1, powers := [(31, 1), (43, 1)] }, { coefficient := 1, powers := [(34, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1), (52, 1)] }, { coefficient := 1, powers := [(19, 1), (45, 1), (52, 1)] }, { coefficient := 1, powers := [(45, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (19, 1), (52, 1)] }, { coefficient := 1, powers := [(17, 1), (19, 1), (56, 1)] }, { coefficient := 1, powers := [(17, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (52, 1)] }, { coefficient := 1, powers := [(17, 1), (23, 1), (52, 1)] }, { coefficient := 1, powers := [(17, 1), (23, 1), (56, 1)] }, { coefficient := 1, powers := [(17, 1), (30, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (53, 1)] }, { coefficient := 1, powers := [(8, 1), (23, 1), (59, 1)] }, { coefficient := 1, powers := [(17, 1), (23, 1), (53, 1)] }, { coefficient := 1, powers := [(17, 1), (31, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1)] }, { coefficient := 1, powers := [(13, 1), (31, 1)] }, { coefficient := 1, powers := [(17, 1), (23, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (37, 1)] }, { coefficient := 1, powers := [(23, 1), (45, 1)] }, { coefficient := 1, powers := [(29, 1), (45, 1)] }, { coefficient := 1, powers := [(37, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (59, 1)] }, { coefficient := 1, powers := [(17, 1), (26, 1), (42, 1)] }, { coefficient := 1, powers := [(17, 1), (26, 1), (46, 1)] }, { coefficient := 1, powers := [(17, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (60, 1)] }, { coefficient := 1, powers := [(13, 1), (26, 1), (47, 1)] }, { coefficient := 1, powers := [(13, 1), (57, 1)] }, { coefficient := 1, powers := [(18, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (42, 1)] }, { coefficient := 1, powers := [(17, 1), (46, 1)] }, { coefficient := 1, powers := [(17, 1), (52, 1)] }, { coefficient := 1, powers := [(17, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1), (53, 1)] }, { coefficient := 1, powers := [(19, 1), (45, 1), (53, 1)] }, { coefficient := 1, powers := [(19, 1), (57, 1)] }, { coefficient := 1, powers := [(26, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1)] }, { coefficient := 1, powers := [(17, 1), (23, 1)] }, { coefficient := 1, powers := [(17, 1), (29, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (60, 1)] }, { coefficient := 1, powers := [(13, 1), (29, 1), (45, 1)] }, { coefficient := 1, powers := [(13, 1), (37, 1), (38, 1)] }, { coefficient := 1, powers := [(18, 1), (34, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (40, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (43, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (49, 1), (54, 1)] }, { coefficient := 1, powers := [(20, 1), (45, 1), (54, 1)] }, { coefficient := 1, powers := [(26, 1), (43, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (43, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (56, 1)] }, { coefficient := 1, powers := [(13, 1), (24, 1), (56, 1)] }, { coefficient := 1, powers := [(13, 1), (30, 1), (48, 1)] }, { coefficient := 1, powers := [(17, 1), (30, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (40, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (43, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (49, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (37, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (49, 1)] }, { coefficient := 1, powers := [(8, 1), (37, 1), (43, 1)] }, { coefficient := 1, powers := [(13, 1), (24, 1), (57, 1)] }, { coefficient := 1, powers := [(13, 1), (31, 1), (49, 1)] }, { coefficient := 1, powers := [(13, 1), (37, 1), (40, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (54, 1)] }, { coefficient := 1, powers := [(18, 1), (31, 1), (43, 1)] }, { coefficient := 1, powers := [(18, 1), (34, 1), (40, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (61, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(43, 1)] }],
  [{ coefficient := 1, powers := [(56, 1), (66, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(57, 1), (67, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(25, 1), (68, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 33 → SparsePoly (Fin 71) := ![
  [{ coefficient := -1, powers := [(3, 1), (37, 1), (40, 1), (59, 1), (68, 1)] }, { coefficient := 1, powers := [(6, 1), (24, 1), (46, 1), (57, 1), (59, 1), (66, 1), (68, 1)] }, { coefficient := -1, powers := [(6, 1), (30, 1), (48, 1), (57, 1), (59, 1), (66, 1), (68, 1)] }, { coefficient := 1, powers := [(17, 1), (24, 1), (25, 1), (30, 1), (46, 1), (57, 1), (63, 1), (66, 1), (68, 1)] }, { coefficient := -1, powers := [(17, 1), (24, 1), (26, 1), (30, 1), (45, 1), (46, 1), (57, 1), (63, 1), (66, 1), (67, 1), (68, 1)] }, { coefficient := -1, powers := [(17, 1), (24, 1), (29, 1), (46, 1), (57, 1), (63, 1), (66, 1), (68, 1)] }, { coefficient := 1, powers := [(17, 1), (24, 1), (31, 1), (45, 1), (46, 1), (57, 1), (63, 1), (66, 1), (67, 1), (68, 1)] }, { coefficient := -1, powers := [(17, 1), (25, 1), (30, 2), (48, 1), (57, 1), (63, 1), (66, 1), (68, 1)] }, { coefficient := -1, powers := [(17, 1), (25, 1), (30, 1), (31, 1), (49, 1), (63, 1), (68, 1)] }, { coefficient := 1, powers := [(17, 1), (25, 1), (30, 1), (37, 1), (40, 1), (63, 1), (68, 1)] }, { coefficient := 1, powers := [(17, 1), (26, 1), (30, 2), (45, 1), (48, 1), (57, 1), (63, 1), (66, 1), (67, 1), (68, 1)] }, { coefficient := 1, powers := [(17, 1), (26, 1), (30, 1), (31, 1), (45, 1), (49, 1), (63, 1), (67, 1), (68, 1)] }, { coefficient := -1, powers := [(17, 1), (26, 1), (30, 1), (37, 1), (40, 1), (45, 1), (63, 1), (67, 1), (68, 1)] }, { coefficient := 1, powers := [(17, 1), (29, 1), (30, 1), (48, 1), (57, 1), (63, 1), (66, 1), (68, 1)] }, { coefficient := 1, powers := [(17, 1), (29, 1), (31, 1), (49, 1), (63, 1), (68, 1)] }, { coefficient := -1, powers := [(17, 1), (29, 1), (37, 1), (40, 1), (63, 1), (68, 1)] }, { coefficient := -1, powers := [(17, 1), (30, 1), (31, 1), (45, 1), (48, 1), (57, 1), (63, 1), (66, 1), (67, 1), (68, 1)] }, { coefficient := -1, powers := [(17, 1), (31, 2), (45, 1), (49, 1), (63, 1), (67, 1), (68, 1)] }, { coefficient := 1, powers := [(17, 1), (31, 1), (37, 1), (40, 1), (45, 1), (63, 1), (67, 1), (68, 1)] }, { coefficient := 1, powers := [(31, 1), (38, 1), (49, 1), (59, 1), (68, 1)] }, { coefficient := -1, powers := [(37, 1), (38, 1), (40, 1), (59, 1), (68, 1)] }],
  [{ coefficient := -1, powers := [(23, 1), (40, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(17, 1), (24, 1), (25, 1), (26, 1), (30, 1), (63, 1)] }, { coefficient := 1, powers := [(17, 1), (24, 1), (26, 2), (30, 1), (45, 1), (63, 1), (67, 1)] }, { coefficient := 1, powers := [(17, 1), (24, 1), (26, 1), (29, 1), (63, 1)] }, { coefficient := -1, powers := [(17, 1), (24, 1), (26, 1), (31, 1), (45, 1), (63, 1), (67, 1)] }, { coefficient := 1, powers := [(24, 1), (26, 1), (38, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (5, 1), (21, 1), (37, 1), (59, 1), (62, 1)] }, { coefficient := -1, powers := [(5, 1), (17, 1), (21, 1), (25, 1), (30, 1), (37, 1), (62, 1), (63, 1)] }, { coefficient := 1, powers := [(5, 1), (17, 1), (21, 1), (26, 1), (30, 1), (37, 1), (45, 1), (62, 1), (63, 1), (67, 1)] }, { coefficient := 1, powers := [(5, 1), (17, 1), (21, 1), (29, 1), (37, 1), (62, 1), (63, 1)] }, { coefficient := -1, powers := [(5, 1), (17, 1), (21, 1), (31, 1), (37, 1), (45, 1), (62, 1), (63, 1), (67, 1)] }, { coefficient := -1, powers := [(5, 1), (21, 1), (29, 1), (45, 1), (59, 1), (62, 1)] }, { coefficient := 1, powers := [(17, 1), (18, 1), (21, 1), (24, 1), (25, 1), (30, 1), (62, 1), (63, 1)] }, { coefficient := -1, powers := [(17, 1), (18, 1), (21, 1), (24, 1), (26, 1), (30, 1), (45, 1), (62, 1), (63, 1), (67, 1)] }, { coefficient := -1, powers := [(17, 1), (18, 1), (21, 1), (24, 1), (29, 1), (62, 1), (63, 1)] }, { coefficient := 1, powers := [(17, 1), (18, 1), (21, 1), (24, 1), (31, 1), (45, 1), (62, 1), (63, 1), (67, 1)] }, { coefficient := 1, powers := [(17, 1), (20, 1), (21, 1), (25, 1), (30, 1), (45, 1), (61, 1), (62, 1)] }, { coefficient := -1, powers := [(17, 1), (20, 1), (21, 1), (26, 1), (30, 1), (45, 2), (61, 1), (62, 1), (67, 1)] }, { coefficient := -1, powers := [(17, 1), (20, 1), (21, 1), (29, 1), (45, 1), (61, 1), (62, 1)] }, { coefficient := 1, powers := [(17, 1), (20, 1), (21, 1), (31, 1), (45, 2), (61, 1), (62, 1), (67, 1)] }, { coefficient := 1, powers := [(17, 1), (21, 1), (25, 1), (30, 1), (49, 1), (62, 1)] }, { coefficient := -1, powers := [(17, 1), (21, 1), (26, 1), (30, 1), (45, 1), (49, 1), (62, 1), (67, 1)] }, { coefficient := -1, powers := [(17, 1), (21, 1), (29, 1), (49, 1), (62, 1)] }, { coefficient := 1, powers := [(17, 1), (21, 1), (31, 1), (45, 1), (49, 1), (62, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (45, 1), (59, 1)] }, { coefficient := -1, powers := [(17, 2), (25, 1), (30, 1), (49, 1), (63, 1)] }, { coefficient := 1, powers := [(17, 2), (26, 1), (30, 1), (45, 1), (49, 1), (63, 1), (67, 1)] }, { coefficient := 1, powers := [(17, 2), (29, 1), (49, 1), (63, 1)] }, { coefficient := -1, powers := [(17, 2), (31, 1), (45, 1), (49, 1), (63, 1), (67, 1)] }, { coefficient := 1, powers := [(17, 1), (38, 1), (49, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (5, 1), (37, 1), (59, 1), (62, 1)] }, { coefficient := 1, powers := [(5, 1), (17, 1), (25, 1), (30, 1), (37, 1), (62, 1), (63, 1)] }, { coefficient := -1, powers := [(5, 1), (17, 1), (26, 1), (30, 1), (37, 1), (45, 1), (62, 1), (63, 1), (67, 1)] }, { coefficient := -1, powers := [(5, 1), (17, 1), (29, 1), (37, 1), (62, 1), (63, 1)] }, { coefficient := 1, powers := [(5, 1), (17, 1), (31, 1), (37, 1), (45, 1), (62, 1), (63, 1), (67, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (45, 1), (59, 1), (62, 1)] }, { coefficient := -1, powers := [(17, 1), (18, 1), (24, 1), (25, 1), (30, 1), (62, 1), (63, 1)] }, { coefficient := 1, powers := [(17, 1), (18, 1), (24, 1), (26, 1), (30, 1), (45, 1), (62, 1), (63, 1), (67, 1)] }, { coefficient := 1, powers := [(17, 1), (18, 1), (24, 1), (29, 1), (62, 1), (63, 1)] }, { coefficient := -1, powers := [(17, 1), (18, 1), (24, 1), (31, 1), (45, 1), (62, 1), (63, 1), (67, 1)] }, { coefficient := -1, powers := [(17, 1), (20, 1), (25, 1), (30, 1), (45, 1), (61, 1), (62, 1)] }, { coefficient := 1, powers := [(17, 1), (20, 1), (26, 1), (30, 1), (45, 2), (61, 1), (62, 1), (67, 1)] }, { coefficient := 1, powers := [(17, 1), (20, 1), (29, 1), (45, 1), (61, 1), (62, 1)] }, { coefficient := -1, powers := [(17, 1), (20, 1), (31, 1), (45, 2), (61, 1), (62, 1), (67, 1)] }, { coefficient := -1, powers := [(17, 1), (25, 1), (30, 1), (49, 1), (62, 1)] }, { coefficient := 1, powers := [(17, 1), (26, 1), (30, 1), (45, 1), (49, 1), (62, 1), (67, 1)] }, { coefficient := 1, powers := [(17, 1), (29, 1), (49, 1), (62, 1)] }, { coefficient := -1, powers := [(17, 1), (31, 1), (45, 1), (49, 1), (62, 1), (67, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (57, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (24, 1), (57, 1), (59, 1), (66, 1)] }, { coefficient := -1, powers := [(17, 1), (24, 1), (25, 1), (30, 1), (57, 1), (63, 1), (66, 1)] }, { coefficient := 1, powers := [(17, 1), (24, 1), (26, 1), (30, 1), (45, 1), (57, 1), (63, 1), (66, 1), (67, 1)] }, { coefficient := 1, powers := [(17, 1), (24, 1), (29, 1), (57, 1), (63, 1), (66, 1)] }, { coefficient := -1, powers := [(17, 1), (24, 1), (31, 1), (45, 1), (57, 1), (63, 1), (66, 1), (67, 1)] }],
  [{ coefficient := -1, powers := [(30, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (25, 1), (30, 1), (31, 1), (63, 1)] }, { coefficient := -1, powers := [(17, 1), (26, 1), (30, 1), (31, 1), (45, 1), (63, 1), (67, 1)] }, { coefficient := -1, powers := [(17, 1), (29, 1), (31, 1), (63, 1)] }, { coefficient := 1, powers := [(17, 1), (31, 2), (45, 1), (63, 1), (67, 1)] }, { coefficient := -1, powers := [(31, 1), (38, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (18, 1), (25, 1), (30, 1), (63, 1)] }, { coefficient := -1, powers := [(17, 1), (18, 1), (26, 1), (30, 1), (45, 1), (63, 1), (67, 1)] }, { coefficient := -1, powers := [(17, 1), (18, 1), (29, 1), (63, 1)] }, { coefficient := 1, powers := [(17, 1), (18, 1), (31, 1), (45, 1), (63, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(53, 1), (67, 1)] }],
  [{ coefficient := -1, powers := [(23, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (63, 1)] }, { coefficient := 1, powers := [(26, 1), (45, 1), (63, 1), (67, 1)] }],
  [{ coefficient := -1, powers := [(45, 1), (63, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (25, 1), (30, 1), (49, 1), (63, 1)] }, { coefficient := -1, powers := [(17, 1), (26, 1), (30, 1), (45, 1), (49, 1), (63, 1), (67, 1)] }, { coefficient := -1, powers := [(17, 1), (29, 1), (49, 1), (63, 1)] }, { coefficient := 1, powers := [(17, 1), (31, 1), (45, 1), (49, 1), (63, 1), (67, 1)] }, { coefficient := -1, powers := [(38, 1), (49, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (54, 1), (59, 1)] }, { coefficient := 1, powers := [(13, 1), (40, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (45, 1), (63, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (24, 1), (25, 1), (30, 1), (63, 1)] }, { coefficient := -1, powers := [(17, 1), (24, 1), (26, 1), (30, 1), (45, 1), (63, 1), (67, 1)] }, { coefficient := -1, powers := [(17, 1), (24, 1), (29, 1), (63, 1)] }, { coefficient := 1, powers := [(17, 1), (24, 1), (31, 1), (45, 1), (63, 1), (67, 1)] }, { coefficient := -1, powers := [(24, 1), (38, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(23, 1), (26, 1), (45, 1), (63, 1), (67, 1)] }],
  [{ coefficient := -1, powers := [(52, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(63, 1)] }],
  [{ coefficient := -1, powers := [(40, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (25, 1), (30, 1), (61, 1)] }, { coefficient := -1, powers := [(17, 1), (26, 1), (30, 1), (45, 1), (61, 1), (67, 1)] }, { coefficient := -1, powers := [(17, 1), (29, 1), (61, 1)] }, { coefficient := 1, powers := [(17, 1), (31, 1), (45, 1), (61, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (57, 1), (59, 1), (66, 1)] }, { coefficient := 1, powers := [(17, 1), (25, 1), (30, 1), (57, 1), (63, 1), (66, 1)] }, { coefficient := -1, powers := [(17, 1), (26, 1), (30, 1), (45, 1), (57, 1), (63, 1), (66, 1), (67, 1)] }, { coefficient := -1, powers := [(17, 1), (29, 1), (57, 1), (63, 1), (66, 1)] }, { coefficient := 1, powers := [(17, 1), (31, 1), (45, 1), (57, 1), (63, 1), (66, 1), (67, 1)] }],
  [{ coefficient := -1, powers := [(17, 1), (25, 1), (30, 1), (63, 1)] }, { coefficient := 1, powers := [(17, 1), (26, 1), (30, 1), (45, 1), (63, 1), (67, 1)] }, { coefficient := 1, powers := [(17, 1), (29, 1), (63, 1)] }, { coefficient := -1, powers := [(17, 1), (31, 1), (45, 1), (63, 1), (67, 1)] }, { coefficient := 1, powers := [(38, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(17, 1), (25, 1), (30, 1), (40, 1), (60, 1)] }, { coefficient := -1, powers := [(17, 1), (25, 1), (30, 1), (49, 1), (54, 1)] }, { coefficient := 1, powers := [(17, 1), (26, 1), (30, 1), (40, 1), (45, 1), (60, 1), (67, 1)] }, { coefficient := 1, powers := [(17, 1), (26, 1), (30, 1), (45, 1), (49, 1), (54, 1), (67, 1)] }, { coefficient := 1, powers := [(17, 1), (29, 1), (40, 1), (60, 1)] }, { coefficient := 1, powers := [(17, 1), (29, 1), (49, 1), (54, 1)] }, { coefficient := -1, powers := [(17, 1), (31, 1), (40, 1), (45, 1), (60, 1), (67, 1)] }, { coefficient := -1, powers := [(17, 1), (31, 1), (45, 1), (49, 1), (54, 1), (67, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (5, 1), (37, 1), (54, 1), (59, 1)] }, { coefficient := -1, powers := [(5, 1), (17, 1), (25, 1), (30, 1), (37, 1), (54, 1), (63, 1)] }, { coefficient := 1, powers := [(5, 1), (17, 1), (26, 1), (30, 1), (37, 1), (45, 1), (54, 1), (63, 1), (67, 1)] }, { coefficient := 1, powers := [(5, 1), (17, 1), (29, 1), (37, 1), (54, 1), (63, 1)] }, { coefficient := -1, powers := [(5, 1), (17, 1), (31, 1), (37, 1), (45, 1), (54, 1), (63, 1), (67, 1)] }, { coefficient := -1, powers := [(5, 1), (29, 1), (45, 1), (54, 1), (59, 1)] }, { coefficient := 1, powers := [(17, 1), (18, 1), (24, 1), (25, 1), (30, 1), (54, 1), (63, 1)] }, { coefficient := -1, powers := [(17, 1), (18, 1), (24, 1), (26, 1), (30, 1), (45, 1), (54, 1), (63, 1), (67, 1)] }, { coefficient := -1, powers := [(17, 1), (18, 1), (24, 1), (29, 1), (54, 1), (63, 1)] }, { coefficient := 1, powers := [(17, 1), (18, 1), (24, 1), (31, 1), (45, 1), (54, 1), (63, 1), (67, 1)] }, { coefficient := 1, powers := [(17, 1), (20, 1), (25, 1), (30, 1), (45, 1), (54, 1), (61, 1)] }, { coefficient := -1, powers := [(17, 1), (20, 1), (26, 1), (30, 1), (45, 2), (54, 1), (61, 1), (67, 1)] }, { coefficient := -1, powers := [(17, 1), (20, 1), (29, 1), (45, 1), (54, 1), (61, 1)] }, { coefficient := 1, powers := [(17, 1), (20, 1), (31, 1), (45, 2), (54, 1), (61, 1), (67, 1)] }, { coefficient := 1, powers := [(17, 1), (25, 1), (30, 1), (49, 1), (54, 1)] }, { coefficient := -1, powers := [(17, 1), (26, 1), (30, 1), (45, 1), (49, 1), (54, 1), (67, 1)] }, { coefficient := -1, powers := [(17, 1), (29, 1), (49, 1), (54, 1)] }, { coefficient := 1, powers := [(17, 1), (31, 1), (45, 1), (49, 1), (54, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (25, 1), (30, 1), (40, 1), (60, 1)] }, { coefficient := -1, powers := [(17, 1), (26, 1), (30, 1), (40, 1), (45, 1), (60, 1), (67, 1)] }, { coefficient := -1, powers := [(17, 1), (29, 1), (40, 1), (60, 1)] }, { coefficient := 1, powers := [(17, 1), (31, 1), (40, 1), (45, 1), (60, 1), (67, 1)] }, { coefficient := -1, powers := [(19, 1), (52, 1)] }, { coefficient := -1, powers := [(26, 1), (45, 1), (52, 1), (67, 1)] }, { coefficient := -1, powers := [(38, 1), (59, 1)] }, { coefficient := 1, powers := [(45, 1), (53, 1), (67, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(0, 1), (17, 1), (25, 1), (30, 1), (57, 1), (61, 1)] }, { coefficient := 1, powers := [(0, 1), (17, 1), (26, 1), (30, 1), (45, 1), (57, 1), (61, 1), (67, 1)] }, { coefficient := 1, powers := [(0, 1), (17, 1), (29, 1), (57, 1), (61, 1)] }, { coefficient := -1, powers := [(0, 1), (17, 1), (31, 1), (45, 1), (57, 1), (61, 1), (67, 1)] }, { coefficient := -1, powers := [(2, 1), (6, 1), (56, 1), (57, 1), (59, 1), (66, 1)] }, { coefficient := -1, powers := [(2, 1), (17, 1), (25, 1), (30, 1), (56, 1), (57, 1), (63, 1), (66, 1)] }, { coefficient := 1, powers := [(2, 1), (17, 1), (25, 1), (30, 1), (57, 1), (63, 1)] }, { coefficient := 1, powers := [(2, 1), (17, 1), (26, 1), (30, 1), (45, 1), (56, 1), (57, 1), (63, 1), (66, 1), (67, 1)] }, { coefficient := -1, powers := [(2, 1), (17, 1), (26, 1), (30, 1), (45, 1), (57, 1), (63, 1), (67, 1)] }, { coefficient := 1, powers := [(2, 1), (17, 1), (29, 1), (56, 1), (57, 1), (63, 1), (66, 1)] }, { coefficient := -1, powers := [(2, 1), (17, 1), (29, 1), (57, 1), (63, 1)] }, { coefficient := -1, powers := [(2, 1), (17, 1), (31, 1), (45, 1), (56, 1), (57, 1), (63, 1), (66, 1), (67, 1)] }, { coefficient := 1, powers := [(2, 1), (17, 1), (31, 1), (45, 1), (57, 1), (63, 1), (67, 1)] }, { coefficient := -1, powers := [(2, 1), (38, 1), (57, 1), (59, 1)] }, { coefficient := -1, powers := [(6, 1), (17, 1), (30, 1), (57, 1), (59, 1), (66, 1)] }, { coefficient := 1, powers := [(8, 1), (17, 1), (25, 1), (30, 1), (37, 1), (63, 1)] }, { coefficient := -1, powers := [(8, 1), (17, 1), (26, 1), (30, 1), (37, 1), (45, 1), (63, 1), (67, 1)] }, { coefficient := -1, powers := [(8, 1), (17, 1), (29, 1), (37, 1), (63, 1)] }, { coefficient := 1, powers := [(8, 1), (17, 1), (31, 1), (37, 1), (45, 1), (63, 1), (67, 1)] }, { coefficient := -1, powers := [(8, 1), (37, 1), (38, 1), (59, 1)] }, { coefficient := -1, powers := [(17, 2), (25, 1), (30, 2), (57, 1), (63, 1), (66, 1)] }, { coefficient := 1, powers := [(17, 2), (26, 1), (30, 2), (45, 1), (57, 1), (63, 1), (66, 1), (67, 1)] }, { coefficient := 1, powers := [(17, 2), (29, 1), (30, 1), (57, 1), (63, 1), (66, 1)] }, { coefficient := -1, powers := [(17, 2), (30, 1), (31, 1), (45, 1), (57, 1), (63, 1), (66, 1), (67, 1)] }, { coefficient := -1, powers := [(17, 1), (18, 1), (25, 1), (30, 1), (31, 1), (63, 1)] }, { coefficient := 1, powers := [(17, 1), (18, 1), (26, 1), (30, 1), (31, 1), (45, 1), (63, 1), (67, 1)] }, { coefficient := 1, powers := [(17, 1), (18, 1), (29, 1), (31, 1), (63, 1)] }, { coefficient := -1, powers := [(17, 1), (18, 1), (31, 2), (45, 1), (63, 1), (67, 1)] }, { coefficient := -1, powers := [(17, 1), (25, 1), (26, 1), (30, 1), (45, 1), (61, 1)] }, { coefficient := 1, powers := [(17, 1), (26, 2), (30, 1), (45, 2), (61, 1), (67, 1)] }, { coefficient := 1, powers := [(17, 1), (26, 1), (29, 1), (45, 1), (61, 1)] }, { coefficient := -1, powers := [(17, 1), (26, 1), (31, 1), (45, 2), (61, 1), (67, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (6, 1), (34, 1), (57, 1), (59, 1)] }, { coefficient := -1, powers := [(5, 1), (17, 1), (25, 1), (30, 1), (34, 1), (57, 1), (63, 1)] }, { coefficient := 1, powers := [(5, 1), (17, 1), (26, 1), (30, 1), (34, 1), (45, 1), (57, 1), (63, 1), (67, 1)] }, { coefficient := 1, powers := [(5, 1), (17, 1), (29, 1), (34, 1), (57, 1), (63, 1)] }, { coefficient := -1, powers := [(5, 1), (17, 1), (31, 1), (34, 1), (45, 1), (57, 1), (63, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (13, 1), (37, 1), (40, 1), (59, 1)] }, { coefficient := -1, powers := [(6, 1), (13, 1), (24, 1), (46, 1), (57, 1), (59, 1), (66, 1)] }, { coefficient := 1, powers := [(6, 1), (13, 1), (30, 1), (48, 1), (57, 1), (59, 1), (66, 1)] }, { coefficient := -1, powers := [(13, 1), (17, 1), (24, 1), (25, 1), (30, 1), (46, 1), (57, 1), (63, 1), (66, 1)] }, { coefficient := 1, powers := [(13, 1), (17, 1), (24, 1), (26, 1), (30, 1), (45, 1), (46, 1), (57, 1), (63, 1), (66, 1), (67, 1)] }, { coefficient := 1, powers := [(13, 1), (17, 1), (24, 1), (29, 1), (46, 1), (57, 1), (63, 1), (66, 1)] }, { coefficient := -1, powers := [(13, 1), (17, 1), (24, 1), (31, 1), (45, 1), (46, 1), (57, 1), (63, 1), (66, 1), (67, 1)] }, { coefficient := 1, powers := [(13, 1), (17, 1), (25, 1), (30, 2), (48, 1), (57, 1), (63, 1), (66, 1)] }, { coefficient := 1, powers := [(13, 1), (17, 1), (25, 1), (30, 1), (31, 1), (49, 1), (63, 1)] }, { coefficient := -1, powers := [(13, 1), (17, 1), (25, 1), (30, 1), (37, 1), (40, 1), (63, 1)] }, { coefficient := -1, powers := [(13, 1), (17, 1), (26, 1), (30, 2), (45, 1), (48, 1), (57, 1), (63, 1), (66, 1), (67, 1)] }, { coefficient := -1, powers := [(13, 1), (17, 1), (26, 1), (30, 1), (31, 1), (45, 1), (49, 1), (63, 1), (67, 1)] }, { coefficient := 1, powers := [(13, 1), (17, 1), (26, 1), (30, 1), (37, 1), (40, 1), (45, 1), (63, 1), (67, 1)] }, { coefficient := -1, powers := [(13, 1), (17, 1), (29, 1), (30, 1), (48, 1), (57, 1), (63, 1), (66, 1)] }, { coefficient := -1, powers := [(13, 1), (17, 1), (29, 1), (31, 1), (49, 1), (63, 1)] }, { coefficient := 1, powers := [(13, 1), (17, 1), (29, 1), (37, 1), (40, 1), (63, 1)] }, { coefficient := 1, powers := [(13, 1), (17, 1), (30, 1), (31, 1), (45, 1), (48, 1), (57, 1), (63, 1), (66, 1), (67, 1)] }, { coefficient := 1, powers := [(13, 1), (17, 1), (31, 2), (45, 1), (49, 1), (63, 1), (67, 1)] }, { coefficient := -1, powers := [(13, 1), (17, 1), (31, 1), (37, 1), (40, 1), (45, 1), (63, 1), (67, 1)] }, { coefficient := -1, powers := [(13, 1), (31, 1), (38, 1), (49, 1), (59, 1)] }, { coefficient := 1, powers := [(13, 1), (37, 1), (38, 1), (40, 1), (59, 1)] }]
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
    (values : Fin 71 → R) :
    ¬ ∀ index : Fin 33,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component18.SelectedLeafB7_6_3_7.selectedHasNoCommonZero

end Krenn.Component18.SelectedLeafB7_6_3_7
