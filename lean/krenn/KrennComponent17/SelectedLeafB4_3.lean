import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component17.SelectedLeafB4_3

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "dbee9ff2012b3e53927698bde4be9979205d0ccb5b8667c599e38c2c21eb4b61"
def certificateSHA256 : String := "eba24763e2774b0943cbcc1293df66079607a7b08e0dd527037253984ba34350"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 42 → Fin 608 := ![
  5,
  6,
  9,
  22,
  30,
  31,
  32,
  33,
  34,
  37,
  42,
  77,
  190,
  206,
  210,
  213,
  306,
  307,
  308,
  309,
  325,
  327,
  334,
  410,
  434,
  438,
  454,
  462,
  501,
  504,
  520,
  541,
  549,
  550,
  570,
  571,
  600,
  601,
  602,
  603,
  604,
  607
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 42 → SparsePoly (Fin 62) := ![
  [{ coefficient := 1, powers := [(3, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (34, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (31, 1)] }],
  [{ coefficient := 1, powers := [(15, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(26, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(26, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(41, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (32, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (32, 1)] }, { coefficient := 1, powers := [(32, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (19, 1)] }, { coefficient := 1, powers := [(17, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (43, 1)] }, { coefficient := 1, powers := [(27, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (41, 1), (54, 1)] }, { coefficient := 1, powers := [(41, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1)] }, { coefficient := 1, powers := [(19, 1), (43, 1)] }, { coefficient := 1, powers := [(24, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1)] }, { coefficient := 1, powers := [(20, 1), (43, 1)] }, { coefficient := 1, powers := [(24, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (44, 1)] }, { coefficient := 1, powers := [(4, 1), (34, 1)] }, { coefficient := 1, powers := [(15, 1), (21, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (50, 1)] }, { coefficient := 1, powers := [(7, 1), (31, 1)] }, { coefficient := 1, powers := [(11, 1), (26, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (52, 1)] }, { coefficient := 1, powers := [(29, 1), (41, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (36, 1), (58, 1)] }, { coefficient := 1, powers := [(3, 1), (24, 1), (58, 1)] }, { coefficient := 1, powers := [(6, 1), (19, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1), (50, 1)] }, { coefficient := 1, powers := [(20, 1), (43, 1), (50, 1)] }, { coefficient := 1, powers := [(47, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (19, 1), (50, 1)] }, { coefficient := 1, powers := [(17, 1), (19, 1), (54, 1)] }, { coefficient := 1, powers := [(17, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (52, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1)] }, { coefficient := 1, powers := [(13, 1), (29, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (57, 1)] }, { coefficient := 1, powers := [(17, 1), (20, 1), (50, 1)] }, { coefficient := 1, powers := [(17, 1), (20, 1), (54, 1)] }, { coefficient := 1, powers := [(17, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1), (51, 1)] }, { coefficient := 1, powers := [(19, 1), (43, 1), (51, 1)] }, { coefficient := 1, powers := [(19, 1), (55, 1)] }, { coefficient := 1, powers := [(25, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1), (50, 1)] }, { coefficient := 1, powers := [(20, 1), (50, 1)] }, { coefficient := 1, powers := [(20, 1), (54, 1)] }, { coefficient := 1, powers := [(46, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (26, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (50, 1)] }, { coefficient := 1, powers := [(17, 1), (26, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (21, 1), (57, 1)] }, { coefficient := 1, powers := [(6, 1), (31, 1), (44, 1)] }, { coefficient := 1, powers := [(6, 1), (34, 1), (40, 1)] }, { coefficient := 1, powers := [(21, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (21, 1), (57, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1), (44, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (40, 1)] }, { coefficient := 1, powers := [(17, 1), (21, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (43, 1), (51, 1)] }, { coefficient := 1, powers := [(23, 1), (55, 1)] }, { coefficient := 1, powers := [(29, 1), (47, 1)] }, { coefficient := 1, powers := [(35, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1)] }, { coefficient := 1, powers := [(6, 1), (57, 1)] }, { coefficient := 1, powers := [(24, 1), (40, 1)] }, { coefficient := 1, powers := [(24, 1), (44, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (50, 1)] }, { coefficient := 1, powers := [(3, 1), (57, 1)] }, { coefficient := 1, powers := [(19, 1), (50, 1)] }, { coefficient := 1, powers := [(19, 1), (54, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(21, 1), (50, 1)] }, { coefficient := 1, powers := [(21, 1), (54, 1)] }, { coefficient := 1, powers := [(26, 1), (40, 1)] }, { coefficient := 1, powers := [(26, 1), (44, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (36, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1)] }, { coefficient := 1, powers := [(3, 1), (24, 1), (57, 1)] }, { coefficient := 1, powers := [(6, 1), (19, 1), (57, 1)] }, { coefficient := 1, powers := [(19, 1)] }, { coefficient := 1, powers := [(24, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (37, 1), (57, 1)] }, { coefficient := 1, powers := [(1, 1), (40, 1), (54, 1)] }, { coefficient := 1, powers := [(1, 1), (44, 1), (50, 1)] }, { coefficient := 1, powers := [(4, 1), (26, 1), (57, 1)] }, { coefficient := 1, powers := [(4, 1), (31, 1), (54, 1)] }, { coefficient := 1, powers := [(4, 1), (34, 1), (50, 1)] }, { coefficient := 1, powers := [(7, 1), (21, 1), (57, 1)] }, { coefficient := 1, powers := [(7, 1), (31, 1), (44, 1)] }, { coefficient := 1, powers := [(7, 1), (34, 1), (40, 1)] }, { coefficient := 1, powers := [(11, 1), (21, 1), (54, 1)] }, { coefficient := 1, powers := [(11, 1), (26, 1), (44, 1)] }, { coefficient := 1, powers := [(11, 1), (34, 1), (37, 1)] }, { coefficient := 1, powers := [(15, 1), (21, 1), (50, 1)] }, { coefficient := 1, powers := [(15, 1), (26, 1), (40, 1)] }, { coefficient := 1, powers := [(15, 1), (31, 1), (37, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (41, 1), (55, 1)] }, { coefficient := 1, powers := [(2, 1), (47, 1), (52, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (52, 1)] }, { coefficient := 1, powers := [(8, 1), (23, 1), (58, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (47, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(13, 1), (23, 1), (55, 1)] }, { coefficient := 1, powers := [(13, 1), (29, 1), (47, 1)] }, { coefficient := 1, powers := [(13, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (52, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (41, 1)] }, { coefficient := 1, powers := [(18, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (59, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1)] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(41, 1), (61, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 42 → SparsePoly (Fin 62) := ![
  [{ coefficient := -1, powers := [(5, 1), (24, 1), (29, 1), (50, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (24, 1), (29, 1), (57, 1), (59, 1)] }, { coefficient := -1, powers := [(5, 1), (29, 1), (57, 1)] }],
  [{ coefficient := 2, powers := [(4, 1), (35, 1), (52, 1), (54, 1)] }, { coefficient := 2, powers := [(7, 1), (35, 1), (40, 1), (52, 1)] }, { coefficient := 2, powers := [(11, 1), (35, 1), (37, 1), (52, 1)] }],
  [{ coefficient := 2, powers := [(4, 1), (23, 1), (54, 1), (58, 1)] }, { coefficient := 2, powers := [(4, 1), (35, 1), (41, 1), (54, 1)] }, { coefficient := -2, powers := [(7, 1), (23, 1), (44, 1), (58, 1)] }, { coefficient := -2, powers := [(7, 1), (35, 1), (41, 1), (44, 1)] }, { coefficient := -2, powers := [(11, 1), (23, 1), (37, 1), (58, 1)] }, { coefficient := -2, powers := [(11, 1), (35, 1), (37, 1), (41, 1)] }],
  [{ coefficient := -2, powers := [(5, 1), (34, 1), (35, 1), (37, 1), (52, 1), (61, 1)] }, { coefficient := -2, powers := [(8, 1), (21, 1), (23, 1), (50, 1), (58, 1), (61, 1)] }, { coefficient := -2, powers := [(8, 1), (21, 1), (23, 1), (54, 1), (58, 1), (61, 1)] }, { coefficient := -2, powers := [(8, 1), (21, 1), (35, 1), (41, 1), (50, 1), (61, 1)] }, { coefficient := -2, powers := [(8, 1), (21, 1), (35, 1), (41, 1), (54, 1), (61, 1)] }, { coefficient := -2, powers := [(8, 1), (23, 1), (34, 1), (37, 1), (58, 1), (61, 1)] }, { coefficient := -2, powers := [(8, 1), (34, 1), (35, 1), (37, 1), (41, 1), (61, 1)] }],
  [{ coefficient := -2, powers := [(6, 1), (11, 1), (17, 1), (23, 1), (50, 1), (58, 1)] }, { coefficient := -2, powers := [(6, 1), (11, 1), (17, 1), (35, 1), (41, 1), (50, 1)] }, { coefficient := -2, powers := [(7, 1), (17, 1), (23, 1), (58, 1)] }, { coefficient := -2, powers := [(7, 1), (17, 1), (35, 1), (41, 1)] }],
  [{ coefficient := 2, powers := [(5, 1), (11, 1), (35, 1), (54, 1)] }],
  [{ coefficient := -2, powers := [(17, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (5, 1), (29, 1), (50, 1), (57, 1), (58, 1), (61, 1)] }, { coefficient := -1, powers := [(3, 1), (5, 1), (29, 1), (57, 1), (58, 1), (59, 1), (61, 1)] }, { coefficient := 1, powers := [(3, 1), (5, 1), (32, 1), (44, 1), (55, 1), (57, 1), (61, 1)] }, { coefficient := -1, powers := [(3, 1), (5, 1), (32, 1), (55, 1), (57, 1), (59, 1), (61, 1)] }, { coefficient := -2, powers := [(3, 1), (7, 1), (17, 1), (21, 1), (35, 1), (46, 1), (50, 1), (52, 1), (57, 1), (61, 1)] }, { coefficient := -2, powers := [(3, 1), (7, 1), (17, 1), (21, 1), (35, 1), (46, 1), (52, 1), (54, 1), (57, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (19, 1), (32, 1), (40, 1), (55, 1), (59, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (19, 1), (32, 1), (44, 1), (55, 1), (59, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (50, 1), (58, 1), (61, 1)] }, { coefficient := -1, powers := [(5, 1), (29, 1), (58, 1), (59, 1), (61, 1)] }, { coefficient := -1, powers := [(5, 1), (32, 1), (40, 1), (55, 1), (61, 1)] }, { coefficient := -1, powers := [(5, 1), (32, 1), (55, 1), (59, 1), (61, 1)] }, { coefficient := 2, powers := [(13, 1), (27, 1), (47, 1), (50, 1), (51, 1), (61, 1)] }, { coefficient := -2, powers := [(13, 1), (29, 1), (47, 1), (50, 1), (61, 1)] }],
  [{ coefficient := 2, powers := [(4, 1), (8, 1), (23, 1), (57, 1), (58, 1), (61, 1)] }, { coefficient := 2, powers := [(4, 1), (8, 1), (35, 1), (41, 1), (57, 1), (61, 1)] }, { coefficient := -2, powers := [(5, 1), (15, 1), (35, 1), (44, 1), (52, 1), (61, 1)] }, { coefficient := -2, powers := [(8, 1), (11, 1), (23, 1), (40, 1), (58, 1), (61, 1)] }, { coefficient := -2, powers := [(8, 1), (11, 1), (23, 1), (44, 1), (58, 1), (61, 1)] }, { coefficient := -2, powers := [(8, 1), (11, 1), (35, 1), (40, 1), (41, 1), (61, 1)] }, { coefficient := -2, powers := [(8, 1), (11, 1), (35, 1), (41, 1), (44, 1), (61, 1)] }, { coefficient := -2, powers := [(8, 1), (15, 1), (23, 1), (44, 1), (58, 1), (61, 1)] }, { coefficient := -2, powers := [(8, 1), (15, 1), (35, 1), (41, 1), (44, 1), (61, 1)] }],
  [{ coefficient := -2, powers := [(4, 1), (17, 1), (35, 1), (52, 1)] }],
  [{ coefficient := 2, powers := [(5, 1), (24, 1), (32, 1), (44, 1), (51, 1), (61, 1)] }, { coefficient := -2, powers := [(5, 1), (25, 1), (32, 1), (44, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (5, 1), (55, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (19, 1), (55, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (5, 1), (44, 1), (55, 1), (57, 1)] }, { coefficient := -1, powers := [(5, 1), (55, 1), (57, 1)] }],
  [{ coefficient := 2, powers := [(3, 1), (7, 1), (21, 1), (35, 1), (46, 1), (50, 1), (52, 1), (57, 1)] }, { coefficient := 2, powers := [(3, 1), (7, 1), (21, 1), (35, 1), (46, 1), (52, 1), (54, 1), (57, 1)] }],
  [{ coefficient := -2, powers := [(13, 1), (51, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (19, 1), (29, 1), (58, 1), (59, 1), (61, 1)] }],
  [{ coefficient := -2, powers := [(5, 1), (32, 1), (44, 1), (51, 1)] }],
  [{ coefficient := -2, powers := [(13, 1), (27, 1), (50, 1), (51, 1)] }, { coefficient := 2, powers := [(13, 1), (29, 1), (50, 1)] }],
  [{ coefficient := -2, powers := [(5, 1), (35, 1), (52, 1), (54, 1)] }, { coefficient := 2, powers := [(8, 1), (23, 1), (50, 1), (58, 1)] }, { coefficient := 2, powers := [(8, 1), (35, 1), (41, 1), (50, 1)] }],
  [{ coefficient := 2, powers := [(5, 1), (35, 1), (44, 1), (52, 1)] }, { coefficient := 2, powers := [(8, 1), (23, 1), (44, 1), (58, 1)] }, { coefficient := 2, powers := [(8, 1), (35, 1), (41, 1), (44, 1)] }],
  [{ coefficient := 2, powers := [(18, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (29, 1), (50, 1), (57, 1)] }, { coefficient := -1, powers := [(5, 1), (29, 1), (57, 1), (59, 1)] }],
  [{ coefficient := 2, powers := [(13, 1), (27, 1), (51, 1)] }, { coefficient := -2, powers := [(13, 1), (29, 1)] }],
  [{ coefficient := -2, powers := [(3, 1), (7, 1), (21, 1), (35, 1), (46, 1), (52, 1), (57, 1)] }, { coefficient := -2, powers := [(7, 1), (21, 1), (35, 1), (46, 1), (52, 1)] }],
  [{ coefficient := 2, powers := [(47, 1)] }],
  [{ coefficient := 2, powers := [(7, 1), (21, 1), (35, 1), (52, 1)] }],
  [{ coefficient := 2, powers := [(5, 1), (32, 1), (44, 1)] }],
  [{ coefficient := -2, powers := [(7, 1), (17, 1), (21, 1), (35, 1), (52, 1)] }],
  [{ coefficient := 2, powers := [(4, 1), (35, 1), (52, 1)] }],
  [{ coefficient := -2, powers := [(8, 1), (11, 1), (23, 1), (50, 1), (58, 1)] }, { coefficient := -2, powers := [(8, 1), (11, 1), (35, 1), (41, 1), (50, 1)] }],
  [{ coefficient := 2, powers := [(6, 1), (11, 1), (23, 1), (50, 1), (58, 1)] }, { coefficient := 2, powers := [(6, 1), (11, 1), (35, 1), (41, 1), (50, 1)] }, { coefficient := 2, powers := [(7, 1), (23, 1), (58, 1)] }, { coefficient := 2, powers := [(7, 1), (35, 1), (41, 1)] }],
  [{ coefficient := 2, powers := [(13, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (19, 1), (32, 1), (55, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (29, 1), (58, 1)] }, { coefficient := 2, powers := [(7, 1), (17, 1), (21, 1), (35, 1), (46, 1), (52, 1)] }],
  [{ coefficient := 2, powers := [(5, 1), (15, 1), (35, 1), (52, 1)] }, { coefficient := 2, powers := [(8, 1), (11, 1), (23, 1), (58, 1)] }, { coefficient := 2, powers := [(8, 1), (11, 1), (35, 1), (41, 1)] }, { coefficient := 2, powers := [(8, 1), (15, 1), (23, 1), (58, 1)] }, { coefficient := 2, powers := [(8, 1), (15, 1), (35, 1), (41, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (29, 1), (50, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (58, 1), (59, 1)] }, { coefficient := -1, powers := [(5, 1), (32, 1), (44, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (55, 1), (59, 1)] }],
  [{ coefficient := -2, powers := [(5, 1), (35, 1), (52, 1)] }, { coefficient := -2, powers := [(8, 1), (23, 1), (58, 1)] }, { coefficient := -2, powers := [(8, 1), (35, 1), (41, 1)] }],
  [{ coefficient := -2, powers := [] }],
  [{ coefficient := 1, powers := [(5, 1), (19, 1), (29, 1), (41, 1), (54, 1), (58, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (19, 1), (32, 1), (44, 1), (55, 1)] }, { coefficient := -1, powers := [(5, 1), (29, 1), (58, 1)] }, { coefficient := -1, powers := [(5, 1), (32, 1), (36, 1), (55, 1), (57, 1)] }, { coefficient := -1, powers := [(5, 1), (32, 1), (55, 1)] }],
  [{ coefficient := 2, powers := [(5, 1), (35, 1), (37, 1), (52, 1), (57, 1)] }, { coefficient := 2, powers := [(5, 1), (35, 1), (40, 1), (52, 1), (54, 1)] }, { coefficient := 2, powers := [(5, 1), (35, 1), (44, 1), (52, 1), (54, 1)] }, { coefficient := 2, powers := [(8, 1), (23, 1), (37, 1), (57, 1), (58, 1)] }, { coefficient := 2, powers := [(8, 1), (23, 1), (40, 1), (54, 1), (58, 1)] }, { coefficient := -2, powers := [(8, 1), (23, 1), (44, 1), (50, 1), (58, 1)] }, { coefficient := 2, powers := [(8, 1), (35, 1), (37, 1), (41, 1), (57, 1)] }, { coefficient := 2, powers := [(8, 1), (35, 1), (40, 1), (41, 1), (54, 1)] }, { coefficient := -2, powers := [(8, 1), (35, 1), (41, 1), (44, 1), (50, 1)] }],
  [{ coefficient := 2, powers := [(38, 1), (58, 1)] }, { coefficient := 2, powers := [(41, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (5, 1), (24, 1), (29, 1), (50, 1), (57, 1), (58, 1)] }, { coefficient := 1, powers := [(3, 1), (5, 1), (24, 1), (29, 1), (57, 1), (58, 1), (59, 1)] }, { coefficient := -1, powers := [(3, 1), (5, 1), (24, 1), (32, 1), (44, 1), (55, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (5, 1), (24, 1), (32, 1), (55, 1), (57, 1), (59, 1)] }, { coefficient := 2, powers := [(3, 1), (7, 1), (17, 1), (21, 1), (24, 1), (35, 1), (46, 1), (50, 1), (52, 1), (57, 1)] }, { coefficient := 2, powers := [(3, 1), (7, 1), (17, 1), (21, 1), (24, 1), (35, 1), (46, 1), (52, 1), (54, 1), (57, 1)] }, { coefficient := -2, powers := [(4, 1), (8, 1), (23, 1), (26, 1), (57, 1), (58, 1)] }, { coefficient := -2, powers := [(4, 1), (8, 1), (26, 1), (35, 1), (41, 1), (57, 1)] }, { coefficient := 2, powers := [(5, 1), (15, 1), (26, 1), (35, 1), (44, 1), (52, 1)] }, { coefficient := 2, powers := [(5, 1), (15, 1), (34, 1), (35, 1), (37, 1), (52, 1)] }, { coefficient := -1, powers := [(5, 1), (19, 1), (24, 1), (32, 1), (40, 1), (55, 1), (59, 1)] }, { coefficient := -1, powers := [(5, 1), (19, 1), (24, 1), (32, 1), (44, 1), (55, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (19, 1), (29, 1), (54, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (19, 1), (29, 1), (58, 1), (59, 1)] }, { coefficient := -1, powers := [(5, 1), (24, 1), (29, 1), (50, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (24, 1), (29, 1), (58, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (24, 1), (32, 1), (40, 1), (55, 1)] }, { coefficient := -2, powers := [(5, 1), (24, 1), (32, 1), (43, 1), (44, 1), (51, 1)] }, { coefficient := 1, powers := [(5, 1), (24, 1), (32, 1), (55, 1), (59, 1)] }, { coefficient := 2, powers := [(5, 1), (25, 1), (32, 1), (43, 1), (44, 1)] }, { coefficient := 2, powers := [(8, 1), (11, 1), (23, 1), (26, 1), (40, 1), (58, 1)] }, { coefficient := 2, powers := [(8, 1), (11, 1), (23, 1), (26, 1), (44, 1), (58, 1)] }, { coefficient := 2, powers := [(8, 1), (11, 1), (26, 1), (35, 1), (40, 1), (41, 1)] }, { coefficient := 2, powers := [(8, 1), (11, 1), (26, 1), (35, 1), (41, 1), (44, 1)] }, { coefficient := 2, powers := [(8, 1), (15, 1), (21, 1), (23, 1), (50, 1), (58, 1)] }, { coefficient := 2, powers := [(8, 1), (15, 1), (21, 1), (23, 1), (54, 1), (58, 1)] }, { coefficient := 2, powers := [(8, 1), (15, 1), (21, 1), (35, 1), (41, 1), (50, 1)] }, { coefficient := 2, powers := [(8, 1), (15, 1), (21, 1), (35, 1), (41, 1), (54, 1)] }, { coefficient := 2, powers := [(8, 1), (15, 1), (23, 1), (26, 1), (44, 1), (58, 1)] }, { coefficient := 2, powers := [(8, 1), (15, 1), (23, 1), (34, 1), (37, 1), (58, 1)] }, { coefficient := 2, powers := [(8, 1), (15, 1), (26, 1), (35, 1), (41, 1), (44, 1)] }, { coefficient := 2, powers := [(8, 1), (15, 1), (34, 1), (35, 1), (37, 1), (41, 1)] }, { coefficient := -2, powers := [(13, 1), (24, 1), (27, 1), (47, 1), (50, 1), (51, 1)] }, { coefficient := 2, powers := [(13, 1), (24, 1), (29, 1), (47, 1), (50, 1)] }]
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
    (values : Fin 62 → R) :
    ¬ ∀ index : Fin 42,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((2 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (2 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (2 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component17.SelectedLeafB4_3.selectedHasNoCommonZero

end Krenn.Component17.SelectedLeafB4_3
