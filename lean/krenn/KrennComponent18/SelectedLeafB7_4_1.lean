import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component18.SelectedLeafB7_4_1

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "0d336aad9250f07a2e01d5768a9fa6e1036a1db701a6ba6a5eea1f665d43c7fd"
def certificateSHA256 : String := "adac92d8295772a01ea8378edee2951840e421504c4460e59d94098268c0aa85"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 41 → Fin 667 := ![
  9,
  10,
  15,
  19,
  143,
  147,
  162,
  163,
  167,
  246,
  301,
  315,
  318,
  323,
  403,
  409,
  426,
  430,
  433,
  435,
  437,
  438,
  443,
  449,
  458,
  478,
  479,
  580,
  581,
  584,
  608,
  645,
  649,
  657,
  658,
  659,
  660,
  662,
  663,
  665,
  666
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 41 → SparsePoly (Fin 66) := ![
  [{ coefficient := 1, powers := [(13, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(15, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (54, 1)] }, { coefficient := 1, powers := [(15, 1), (21, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (34, 1)] }, { coefficient := 1, powers := [(34, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (19, 1)] }, { coefficient := 1, powers := [(17, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (45, 1)] }, { coefficient := 1, powers := [(18, 1), (19, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (45, 1)] }, { coefficient := 1, powers := [(29, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (19, 1), (56, 1)] }, { coefficient := 1, powers := [(13, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (60, 1)] }, { coefficient := 1, powers := [(13, 1), (49, 1)] }, { coefficient := 1, powers := [(18, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (47, 1)] }, { coefficient := 1, powers := [(18, 1), (42, 1)] }, { coefficient := 1, powers := [(18, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (54, 1)] }, { coefficient := 1, powers := [(31, 1), (43, 1)] }, { coefficient := 1, powers := [(34, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1), (52, 1)] }, { coefficient := 1, powers := [(19, 1), (45, 1), (52, 1)] }, { coefficient := 1, powers := [(45, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (19, 1), (52, 1)] }, { coefficient := 1, powers := [(17, 1), (19, 1), (56, 1)] }, { coefficient := 1, powers := [(17, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (25, 1), (47, 1)] }, { coefficient := 1, powers := [(18, 1), (25, 1), (42, 1)] }, { coefficient := 1, powers := [(18, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (53, 1)] }, { coefficient := 1, powers := [(3, 1), (26, 1), (59, 1)] }, { coefficient := 1, powers := [(19, 1), (53, 1)] }, { coefficient := 1, powers := [(26, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (46, 1)] }, { coefficient := 1, powers := [(17, 1), (29, 1), (42, 1)] }, { coefficient := 1, powers := [(17, 1), (29, 1), (46, 1)] }, { coefficient := 1, powers := [(17, 1), (30, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (49, 1)] }, { coefficient := 1, powers := [(5, 1), (37, 1)] }, { coefficient := 1, powers := [(17, 1), (29, 1), (49, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (52, 1)] }, { coefficient := 1, powers := [(17, 1), (23, 1), (52, 1)] }, { coefficient := 1, powers := [(17, 1), (23, 1), (56, 1)] }, { coefficient := 1, powers := [(17, 1), (30, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1)] }, { coefficient := 1, powers := [(13, 1), (31, 1)] }, { coefficient := 1, powers := [(17, 1), (23, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (37, 1)] }, { coefficient := 1, powers := [(23, 1), (45, 1)] }, { coefficient := 1, powers := [(29, 1), (45, 1)] }, { coefficient := 1, powers := [(37, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (60, 1)] }, { coefficient := 1, powers := [(13, 1), (26, 1), (47, 1)] }, { coefficient := 1, powers := [(13, 1), (57, 1)] }, { coefficient := 1, powers := [(18, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (42, 1)] }, { coefficient := 1, powers := [(17, 1), (46, 1)] }, { coefficient := 1, powers := [(17, 1), (52, 1)] }, { coefficient := 1, powers := [(17, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1), (53, 1)] }, { coefficient := 1, powers := [(19, 1), (45, 1), (53, 1)] }, { coefficient := 1, powers := [(19, 1), (57, 1)] }, { coefficient := 1, powers := [(26, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1)] }, { coefficient := 1, powers := [(17, 1), (23, 1)] }, { coefficient := 1, powers := [(17, 1), (29, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (60, 1)] }, { coefficient := 1, powers := [(13, 1), (29, 1), (45, 1)] }, { coefficient := 1, powers := [(13, 1), (37, 1), (38, 1)] }, { coefficient := 1, powers := [(18, 1), (34, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1)] }, { coefficient := 1, powers := [(6, 1), (59, 1)] }, { coefficient := 1, powers := [(25, 1), (42, 1)] }, { coefficient := 1, powers := [(25, 1), (46, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (52, 1)] }, { coefficient := 1, powers := [(3, 1), (59, 1)] }, { coefficient := 1, powers := [(19, 1), (52, 1)] }, { coefficient := 1, powers := [(19, 1), (56, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (40, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (43, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (49, 1), (54, 1)] }, { coefficient := 1, powers := [(20, 1), (45, 1), (54, 1)] }, { coefficient := 1, powers := [(26, 1), (43, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (38, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1)] }, { coefficient := 1, powers := [(3, 1), (25, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (19, 1), (59, 1)] }, { coefficient := 1, powers := [(19, 1)] }, { coefficient := 1, powers := [(25, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (39, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (42, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(42, 1)] }, { coefficient := 1, powers := [(46, 1)] }, { coefficient := 1, powers := [(52, 1)] }, { coefficient := 1, powers := [(56, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (39, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (42, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(17, 1), (30, 1), (42, 1)] }, { coefficient := 1, powers := [(17, 1), (30, 1), (46, 1)] }, { coefficient := 1, powers := [(17, 1), (30, 1), (52, 1)] }, { coefficient := 1, powers := [(17, 1), (30, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (40, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (43, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (49, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (37, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (49, 1)] }, { coefficient := 1, powers := [(8, 1), (37, 1), (43, 1)] }, { coefficient := 1, powers := [(13, 1), (24, 1), (57, 1)] }, { coefficient := 1, powers := [(13, 1), (31, 1), (49, 1)] }, { coefficient := 1, powers := [(13, 1), (37, 1), (40, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (54, 1)] }, { coefficient := 1, powers := [(18, 1), (31, 1), (43, 1)] }, { coefficient := 1, powers := [(18, 1), (34, 1), (40, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (61, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(42, 1)] }],
  [{ coefficient := 1, powers := [(43, 1)] }],
  [{ coefficient := 1, powers := [(56, 1)] }],
  [{ coefficient := 1, powers := [(57, 1), (65, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 41 → SparsePoly (Fin 66) := ![
  [{ coefficient := -2, powers := [(23, 1), (40, 1), (59, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (2, 1), (24, 1), (26, 1), (46, 1), (63, 1)] }, { coefficient := -2, powers := [(2, 1), (24, 1), (25, 1), (26, 1), (46, 1), (63, 1)] }, { coefficient := -2, powers := [(2, 1), (24, 1), (26, 1), (63, 1)] }, { coefficient := 2, powers := [(24, 1), (26, 1), (38, 1), (59, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (2, 1), (18, 1), (21, 1), (24, 1), (46, 1), (62, 1), (63, 1)] }, { coefficient := 2, powers := [(0, 1), (2, 1), (20, 1), (21, 1), (45, 1), (46, 1), (61, 1), (62, 1)] }, { coefficient := 4, powers := [(0, 1), (2, 1), (21, 1), (46, 1), (49, 1), (62, 1)] }, { coefficient := 2, powers := [(2, 1), (3, 1), (21, 1), (49, 1), (59, 1), (62, 1)] }, { coefficient := 2, powers := [(2, 1), (18, 1), (21, 1), (24, 1), (25, 1), (46, 1), (62, 1), (63, 1)] }, { coefficient := 2, powers := [(2, 1), (18, 1), (21, 1), (24, 1), (62, 1), (63, 1)] }, { coefficient := 2, powers := [(2, 1), (20, 1), (21, 1), (25, 1), (45, 1), (46, 1), (61, 1), (62, 1)] }, { coefficient := 2, powers := [(2, 1), (20, 1), (21, 1), (45, 1), (61, 1), (62, 1)] }, { coefficient := 4, powers := [(2, 1), (21, 1), (25, 1), (46, 1), (49, 1), (62, 1)] }, { coefficient := 4, powers := [(2, 1), (21, 1), (49, 1), (62, 1)] }, { coefficient := -2, powers := [(5, 1), (21, 1), (29, 1), (45, 1), (59, 1), (62, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (2, 1), (17, 1), (46, 1), (49, 1), (63, 1)] }, { coefficient := -2, powers := [(2, 1), (17, 1), (25, 1), (46, 1), (49, 1), (63, 1)] }, { coefficient := -2, powers := [(2, 1), (17, 1), (49, 1), (63, 1)] }, { coefficient := 2, powers := [(5, 1), (45, 1), (59, 1)] }, { coefficient := 2, powers := [(17, 1), (38, 1), (49, 1), (59, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (2, 1), (18, 1), (24, 1), (46, 1), (62, 1), (63, 1)] }, { coefficient := -2, powers := [(0, 1), (2, 1), (20, 1), (45, 1), (46, 1), (61, 1), (62, 1)] }, { coefficient := -4, powers := [(0, 1), (2, 1), (46, 1), (49, 1), (62, 1)] }, { coefficient := -2, powers := [(2, 1), (3, 1), (49, 1), (59, 1), (62, 1)] }, { coefficient := -2, powers := [(2, 1), (18, 1), (24, 1), (25, 1), (46, 1), (62, 1), (63, 1)] }, { coefficient := -2, powers := [(2, 1), (18, 1), (24, 1), (62, 1), (63, 1)] }, { coefficient := -2, powers := [(2, 1), (20, 1), (25, 1), (45, 1), (46, 1), (61, 1), (62, 1)] }, { coefficient := -2, powers := [(2, 1), (20, 1), (45, 1), (61, 1), (62, 1)] }, { coefficient := -4, powers := [(2, 1), (25, 1), (46, 1), (49, 1), (62, 1)] }, { coefficient := -4, powers := [(2, 1), (49, 1), (62, 1)] }, { coefficient := 2, powers := [(5, 1), (29, 1), (45, 1), (59, 1), (62, 1)] }],
  [{ coefficient := -2, powers := [(5, 1), (57, 1), (59, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (2, 1), (24, 1), (46, 1), (47, 1), (54, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (23, 1), (52, 2), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (29, 1), (52, 2), (63, 1)] }, { coefficient := 2, powers := [(2, 1), (24, 1), (25, 1), (46, 1), (47, 1), (54, 1), (63, 1)] }, { coefficient := 2, powers := [(2, 1), (24, 1), (47, 1), (54, 1), (63, 1)] }, { coefficient := 2, powers := [(3, 1), (24, 1), (47, 1), (54, 1), (59, 1)] }, { coefficient := -4, powers := [(23, 1), (52, 1), (63, 1)] }, { coefficient := -4, powers := [(29, 1), (52, 1), (63, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (2, 1), (24, 1), (46, 1), (54, 1), (63, 1)] }, { coefficient := 2, powers := [(2, 1), (24, 1), (25, 1), (46, 1), (54, 1), (63, 1)] }, { coefficient := 2, powers := [(2, 1), (24, 1), (54, 1), (63, 1)] }, { coefficient := 2, powers := [(3, 1), (24, 1), (54, 1), (59, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (2, 1), (17, 1), (46, 1), (54, 1), (63, 1)] }, { coefficient := -2, powers := [(2, 1), (17, 1), (25, 1), (46, 1), (54, 1), (63, 1)] }, { coefficient := -2, powers := [(2, 1), (17, 1), (54, 1), (63, 1)] }, { coefficient := -2, powers := [(3, 1), (17, 1), (54, 1), (59, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (2, 1), (31, 1), (46, 1), (49, 1), (63, 1)] }, { coefficient := 2, powers := [(0, 1), (2, 1), (37, 1), (40, 1), (46, 1), (63, 1)] }, { coefficient := -2, powers := [(2, 1), (25, 1), (31, 1), (46, 1), (49, 1), (63, 1)] }, { coefficient := 2, powers := [(2, 1), (25, 1), (37, 1), (40, 1), (46, 1), (63, 1)] }, { coefficient := -2, powers := [(2, 1), (31, 1), (49, 1), (63, 1)] }, { coefficient := 2, powers := [(2, 1), (37, 1), (40, 1), (63, 1)] }, { coefficient := -2, powers := [(3, 1), (37, 1), (40, 1), (59, 1)] }, { coefficient := 2, powers := [(31, 1), (38, 1), (49, 1), (59, 1)] }, { coefficient := -2, powers := [(37, 1), (38, 1), (40, 1), (59, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (2, 1), (31, 1), (46, 1), (63, 1)] }, { coefficient := 2, powers := [(2, 1), (25, 1), (31, 1), (46, 1), (63, 1)] }, { coefficient := 2, powers := [(2, 1), (31, 1), (63, 1)] }, { coefficient := -2, powers := [(31, 1), (38, 1), (59, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (2, 1), (19, 1), (24, 1), (46, 1), (54, 1), (63, 1)] }, { coefficient := -2, powers := [(2, 1), (19, 1), (24, 1), (25, 1), (46, 1), (54, 1), (63, 1)] }, { coefficient := -2, powers := [(2, 1), (19, 1), (24, 1), (54, 1), (63, 1)] }, { coefficient := -2, powers := [(3, 1), (19, 1), (24, 1), (54, 1), (59, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (2, 1), (18, 1), (46, 1), (63, 1)] }, { coefficient := 2, powers := [(2, 1), (18, 1), (25, 1), (46, 1), (63, 1)] }, { coefficient := 2, powers := [(2, 1), (18, 1), (63, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (26, 1), (46, 1), (52, 1), (65, 1)] }, { coefficient := -6, powers := [(26, 1), (46, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (23, 1), (52, 1), (63, 1)] }, { coefficient := 1, powers := [(0, 1), (29, 1), (52, 1), (63, 1)] }, { coefficient := 4, powers := [(23, 1), (63, 1)] }, { coefficient := 4, powers := [(29, 1), (63, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (2, 1), (24, 1), (46, 1), (54, 1), (63, 1)] }, { coefficient := -2, powers := [(2, 1), (24, 1), (25, 1), (46, 1), (54, 1), (63, 1)] }, { coefficient := -2, powers := [(2, 1), (24, 1), (54, 1), (63, 1)] }, { coefficient := -2, powers := [(3, 1), (24, 1), (54, 1), (59, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (45, 1), (46, 1), (52, 1), (65, 1)] }, { coefficient := -6, powers := [(45, 1), (46, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (25, 1), (52, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (63, 1)] }, { coefficient := -4, powers := [(25, 1), (63, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (2, 1), (46, 1), (54, 1), (63, 1)] }, { coefficient := 2, powers := [(2, 1), (25, 1), (46, 1), (54, 1), (63, 1)] }, { coefficient := 2, powers := [(2, 1), (54, 1), (63, 1)] }, { coefficient := 2, powers := [(3, 1), (54, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (25, 1), (52, 1), (63, 1)] }, { coefficient := 1, powers := [(0, 1), (63, 1)] }, { coefficient := 4, powers := [(25, 1), (63, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (2, 1), (46, 1), (49, 1), (63, 1)] }, { coefficient := 2, powers := [(2, 1), (25, 1), (46, 1), (49, 1), (63, 1)] }, { coefficient := 2, powers := [(2, 1), (49, 1), (63, 1)] }, { coefficient := -2, powers := [(38, 1), (49, 1), (59, 1)] }],
  [{ coefficient := -2, powers := [(5, 1), (54, 1), (59, 1)] }, { coefficient := 2, powers := [(13, 1), (40, 1), (59, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (2, 1), (24, 1), (46, 1), (63, 1)] }, { coefficient := 2, powers := [(2, 1), (24, 1), (25, 1), (46, 1), (63, 1)] }, { coefficient := 2, powers := [(2, 1), (24, 1), (63, 1)] }, { coefficient := -2, powers := [(24, 1), (38, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(0, 2), (25, 1), (30, 1), (52, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 2), (30, 1), (63, 1)] }, { coefficient := 2, powers := [(0, 1), (19, 1), (25, 1), (30, 1), (52, 1), (63, 1)] }, { coefficient := 1, powers := [(0, 1), (25, 1), (29, 1), (52, 1), (63, 1)] }, { coefficient := 2, powers := [(0, 1), (25, 1), (30, 1), (63, 1)] }, { coefficient := 1, powers := [(0, 1), (29, 1), (63, 1)] }, { coefficient := 6, powers := [(19, 1), (25, 1), (30, 1), (63, 1)] }, { coefficient := 4, powers := [(25, 1), (29, 1), (63, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (46, 1), (52, 1), (65, 1)] }, { coefficient := 6, powers := [(46, 1), (65, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (52, 1), (63, 1)] }, { coefficient := -4, powers := [(63, 1)] }],
  [{ coefficient := -2, powers := [(40, 1), (59, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (19, 1), (52, 1), (61, 1)] }, { coefficient := 2, powers := [(5, 1), (34, 1), (57, 1)] }, { coefficient := -6, powers := [(19, 1), (61, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (25, 1), (52, 1), (61, 1)] }, { coefficient := 2, powers := [(0, 1), (26, 1), (45, 1), (46, 1), (52, 1), (65, 1)] }, { coefficient := -6, powers := [(25, 1), (61, 1)] }, { coefficient := 6, powers := [(26, 1), (45, 1), (46, 1), (65, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (2, 1), (46, 1), (61, 1)] }, { coefficient := 2, powers := [(2, 1), (25, 1), (46, 1), (61, 1)] }, { coefficient := 2, powers := [(2, 1), (61, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (52, 1), (61, 1)] }, { coefficient := 6, powers := [(61, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (2, 1), (25, 1), (52, 1), (63, 1)] }, { coefficient := 2, powers := [(0, 1), (19, 1), (25, 1), (52, 1), (61, 1)] }, { coefficient := -1, powers := [(0, 1)] }, { coefficient := 4, powers := [(2, 1), (25, 1), (63, 1)] }, { coefficient := 6, powers := [(19, 1), (25, 1), (61, 1)] }, { coefficient := -2, powers := [(25, 1)] }],
  [{ coefficient := -1, powers := [(0, 2), (25, 1), (52, 1), (63, 1)] }, { coefficient := 1, powers := [(0, 2), (63, 1)] }, { coefficient := -2, powers := [(0, 1), (19, 1), (25, 1), (52, 1), (63, 1)] }, { coefficient := -2, powers := [(0, 1), (25, 1), (63, 1)] }, { coefficient := -6, powers := [(19, 1), (25, 1), (63, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (2, 1), (46, 1), (63, 1)] }, { coefficient := -2, powers := [(2, 1), (25, 1), (46, 1), (63, 1)] }, { coefficient := -2, powers := [(2, 1), (63, 1)] }, { coefficient := 2, powers := [(38, 1), (59, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (2, 1), (40, 1), (46, 1), (60, 1)] }, { coefficient := -2, powers := [(0, 1), (2, 1), (46, 1), (49, 1), (54, 1)] }, { coefficient := -2, powers := [(0, 1), (19, 1), (25, 1), (39, 1), (52, 1), (59, 1)] }, { coefficient := -2, powers := [(0, 1), (19, 1), (25, 1), (46, 1), (52, 2)] }, { coefficient := 2, powers := [(0, 1), (19, 1), (46, 1), (52, 1)] }, { coefficient := 2, powers := [(0, 1), (25, 1), (52, 2)] }, { coefficient := -2, powers := [(0, 1), (38, 1), (52, 1), (59, 1)] }, { coefficient := -2, powers := [(0, 1), (52, 1)] }, { coefficient := -2, powers := [(2, 1), (25, 1), (40, 1), (46, 1), (60, 1)] }, { coefficient := -2, powers := [(2, 1), (25, 1), (46, 1), (49, 1), (54, 1)] }, { coefficient := -2, powers := [(2, 1), (40, 1), (60, 1)] }, { coefficient := -2, powers := [(2, 1), (49, 1), (54, 1)] }, { coefficient := -6, powers := [(19, 1), (25, 1), (39, 1), (59, 1)] }, { coefficient := -6, powers := [(19, 1), (25, 1), (46, 1), (52, 1)] }, { coefficient := 6, powers := [(19, 1), (46, 1)] }, { coefficient := 6, powers := [(25, 1), (52, 1)] }, { coefficient := -6, powers := [(38, 1), (59, 1)] }, { coefficient := -6, powers := [] }],
  [{ coefficient := 2, powers := [(0, 1), (2, 1), (18, 1), (24, 1), (46, 1), (54, 1), (63, 1)] }, { coefficient := 2, powers := [(0, 1), (2, 1), (20, 1), (45, 1), (46, 1), (54, 1), (61, 1)] }, { coefficient := 4, powers := [(0, 1), (2, 1), (46, 1), (49, 1), (54, 1)] }, { coefficient := 2, powers := [(2, 1), (3, 1), (49, 1), (54, 1), (59, 1)] }, { coefficient := 2, powers := [(2, 1), (18, 1), (24, 1), (25, 1), (46, 1), (54, 1), (63, 1)] }, { coefficient := 2, powers := [(2, 1), (18, 1), (24, 1), (54, 1), (63, 1)] }, { coefficient := 2, powers := [(2, 1), (20, 1), (25, 1), (45, 1), (46, 1), (54, 1), (61, 1)] }, { coefficient := 2, powers := [(2, 1), (20, 1), (45, 1), (54, 1), (61, 1)] }, { coefficient := 4, powers := [(2, 1), (25, 1), (46, 1), (49, 1), (54, 1)] }, { coefficient := 4, powers := [(2, 1), (49, 1), (54, 1)] }, { coefficient := -2, powers := [(5, 1), (29, 1), (45, 1), (54, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(0, 2), (39, 1), (59, 1)] }, { coefficient := -1, powers := [(0, 2), (46, 1), (52, 1)] }, { coefficient := 2, powers := [(0, 1), (2, 1), (40, 1), (46, 1), (60, 1)] }, { coefficient := -2, powers := [(0, 1), (2, 1), (46, 1), (49, 1), (54, 1)] }, { coefficient := 2, powers := [(0, 1), (5, 1), (34, 1), (46, 1), (57, 1)] }, { coefficient := 2, powers := [(0, 1), (19, 1), (25, 1), (39, 1), (52, 1), (59, 1)] }, { coefficient := 2, powers := [(0, 1), (19, 1), (25, 1), (46, 1), (52, 2)] }, { coefficient := -2, powers := [(0, 1), (25, 1), (39, 1), (59, 1)] }, { coefficient := -2, powers := [(0, 1), (25, 1), (46, 1), (52, 1)] }, { coefficient := -2, powers := [(0, 1), (25, 1), (52, 2)] }, { coefficient := 2, powers := [(0, 1), (38, 1), (52, 1), (59, 1)] }, { coefficient := -1, powers := [(0, 1), (46, 1)] }, { coefficient := 1, powers := [(0, 1), (52, 1)] }, { coefficient := 2, powers := [(2, 1), (25, 1), (40, 1), (46, 1), (60, 1)] }, { coefficient := -2, powers := [(2, 1), (25, 1), (46, 1), (49, 1), (54, 1)] }, { coefficient := 2, powers := [(2, 1), (40, 1), (60, 1)] }, { coefficient := -2, powers := [(2, 1), (49, 1), (54, 1)] }, { coefficient := 2, powers := [(5, 1), (25, 1), (34, 1), (46, 1), (57, 1)] }, { coefficient := 2, powers := [(5, 1), (34, 1), (57, 1)] }, { coefficient := 6, powers := [(19, 1), (25, 1), (39, 1), (59, 1)] }, { coefficient := 6, powers := [(19, 1), (25, 1), (46, 1), (52, 1)] }, { coefficient := -2, powers := [(25, 1), (46, 1)] }, { coefficient := -8, powers := [(25, 1), (52, 1)] }, { coefficient := 4, powers := [(38, 1), (59, 1)] }, { coefficient := 2, powers := [] }],
  [{ coefficient := 2, powers := [(0, 1), (2, 1), (18, 1), (19, 1), (24, 1), (46, 1), (54, 1), (63, 1)] }, { coefficient := 2, powers := [(0, 1), (2, 1), (18, 1), (24, 1), (25, 1), (46, 1), (54, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (2, 1), (25, 1), (52, 1), (63, 1)] }, { coefficient := 1, powers := [(0, 1)] }, { coefficient := 2, powers := [(2, 1), (18, 1), (19, 1), (24, 1), (25, 1), (46, 1), (54, 1), (63, 1)] }, { coefficient := 2, powers := [(2, 1), (18, 1), (19, 1), (24, 1), (54, 1), (63, 1)] }, { coefficient := 2, powers := [(2, 1), (18, 1), (24, 1), (25, 2), (46, 1), (54, 1), (63, 1)] }, { coefficient := 2, powers := [(2, 1), (18, 1), (24, 1), (25, 1), (54, 1), (63, 1)] }, { coefficient := -4, powers := [(2, 1), (25, 1), (63, 1)] }, { coefficient := 2, powers := [(3, 1), (18, 1), (19, 1), (24, 1), (54, 1), (59, 1)] }, { coefficient := 2, powers := [(3, 1), (18, 1), (24, 1), (25, 1), (54, 1), (59, 1)] }, { coefficient := -2, powers := [(5, 1), (25, 1), (34, 1), (57, 1)] }, { coefficient := 2, powers := [(25, 1)] }],
  [{ coefficient := -2, powers := [(0, 2), (2, 1), (46, 1), (57, 1), (61, 1)] }, { coefficient := 2, powers := [(0, 1), (2, 2), (46, 1), (57, 1), (63, 1)] }, { coefficient := 2, powers := [(0, 1), (2, 1), (8, 1), (37, 1), (46, 1), (63, 1)] }, { coefficient := -2, powers := [(0, 1), (2, 1), (18, 1), (31, 1), (46, 1), (63, 1)] }, { coefficient := -2, powers := [(0, 1), (2, 1), (25, 1), (46, 1), (57, 1), (61, 1)] }, { coefficient := -2, powers := [(0, 1), (2, 1), (26, 1), (45, 1), (46, 1), (61, 1)] }, { coefficient := -2, powers := [(0, 1), (2, 1), (57, 1), (61, 1)] }, { coefficient := 2, powers := [(2, 2), (25, 1), (46, 1), (57, 1), (63, 1)] }, { coefficient := 2, powers := [(2, 2), (57, 1), (63, 1)] }, { coefficient := 2, powers := [(2, 1), (8, 1), (25, 1), (37, 1), (46, 1), (63, 1)] }, { coefficient := 2, powers := [(2, 1), (8, 1), (37, 1), (63, 1)] }, { coefficient := -2, powers := [(2, 1), (18, 1), (25, 1), (31, 1), (46, 1), (63, 1)] }, { coefficient := -2, powers := [(2, 1), (18, 1), (31, 1), (63, 1)] }, { coefficient := -2, powers := [(2, 1), (25, 1), (26, 1), (45, 1), (46, 1), (61, 1)] }, { coefficient := -2, powers := [(2, 1), (26, 1), (45, 1), (61, 1)] }, { coefficient := -2, powers := [(2, 1), (38, 1), (57, 1), (59, 1)] }, { coefficient := -2, powers := [(8, 1), (37, 1), (38, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(0, 2), (2, 1), (42, 1), (63, 1)] }, { coefficient := -2, powers := [(0, 2), (19, 1), (25, 1), (42, 1), (52, 1), (61, 1)] }, { coefficient := 1, powers := [(0, 2), (42, 1)] }, { coefficient := 2, powers := [(0, 1), (2, 1), (13, 1), (19, 1), (31, 1), (46, 1), (49, 1), (63, 1)] }, { coefficient := -2, powers := [(0, 1), (2, 1), (13, 1), (19, 1), (37, 1), (40, 1), (46, 1), (63, 1)] }, { coefficient := 2, powers := [(0, 1), (2, 1), (19, 1), (25, 1), (42, 1), (52, 1), (63, 1)] }, { coefficient := -2, powers := [(0, 1), (2, 1), (25, 1), (42, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (2, 1), (25, 1), (52, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (17, 1), (19, 1), (23, 1), (52, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (17, 1), (19, 1), (29, 1), (52, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (17, 1), (23, 1), (25, 1), (52, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (17, 1), (23, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (17, 1), (25, 1), (29, 1), (52, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (17, 1), (29, 1), (63, 1)] }, { coefficient := -6, powers := [(0, 1), (19, 1), (25, 1), (42, 1), (61, 1)] }, { coefficient := -2, powers := [(0, 1), (19, 1), (26, 1), (45, 1), (46, 1), (52, 1), (65, 1)] }, { coefficient := 2, powers := [(0, 1), (25, 1), (42, 1)] }, { coefficient := 1, powers := [(0, 1)] }, { coefficient := 2, powers := [(2, 1), (13, 1), (19, 1), (25, 1), (31, 1), (46, 1), (49, 1), (63, 1)] }, { coefficient := -2, powers := [(2, 1), (13, 1), (19, 1), (25, 1), (37, 1), (40, 1), (46, 1), (63, 1)] }, { coefficient := 2, powers := [(2, 1), (13, 1), (19, 1), (31, 1), (49, 1), (63, 1)] }, { coefficient := -2, powers := [(2, 1), (13, 1), (19, 1), (37, 1), (40, 1), (63, 1)] }, { coefficient := 6, powers := [(2, 1), (19, 1), (25, 1), (42, 1), (63, 1)] }, { coefficient := -4, powers := [(2, 1), (25, 1), (63, 1)] }, { coefficient := 2, powers := [(3, 1), (13, 1), (19, 1), (37, 1), (40, 1), (59, 1)] }, { coefficient := -2, powers := [(13, 1), (19, 1), (31, 1), (38, 1), (49, 1), (59, 1)] }, { coefficient := 2, powers := [(13, 1), (19, 1), (37, 1), (38, 1), (40, 1), (59, 1)] }, { coefficient := -4, powers := [(17, 1), (19, 1), (23, 1), (63, 1)] }, { coefficient := -4, powers := [(17, 1), (19, 1), (29, 1), (63, 1)] }, { coefficient := -4, powers := [(17, 1), (23, 1), (25, 1), (63, 1)] }, { coefficient := -4, powers := [(17, 1), (25, 1), (29, 1), (63, 1)] }, { coefficient := -6, powers := [(19, 1), (26, 1), (45, 1), (46, 1), (65, 1)] }, { coefficient := 2, powers := [(25, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (19, 1), (46, 1), (52, 1)] }, { coefficient := -6, powers := [(19, 1), (46, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
/-- Lean replays the exact selected-row integer certificate. -/
theorem constantIdentity :
    ∑ index, (multipliers index).toPoly *
      (selectedEquations index).toPoly = C (4 : ℤ) := by
  simp (config := { maxSteps := 1000000 })
    [Fin.sum_univ_succ, multipliers, selectedEquations,
    SparsePoly.toPoly, SparseTerm.toPoly]
  ring

/-- The selected rows have no common zero in a characteristic-zero ring. -/
theorem selectedHasNoCommonZero {R : Type*} [CommRing R] [Nontrivial R] [CharZero R]
    (values : Fin 66 → R) :
    ¬ ∀ index : Fin 41,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((4 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (4 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (4 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component18.SelectedLeafB7_4_1.selectedHasNoCommonZero

end Krenn.Component18.SelectedLeafB7_4_1
