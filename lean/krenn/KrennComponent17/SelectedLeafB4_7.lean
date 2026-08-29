import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component17.SelectedLeafB4_7

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "14d8817581d0e21b36e44ff1424637def4cc1f32973a78cea1fc74ad86e504b6"
def certificateSHA256 : String := "f38754b9f19f013a979849d08d886b83f90ea92393f70cdcb7eece2d106621de"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 52 → Fin 608 := ![
  6,
  9,
  20,
  22,
  30,
  31,
  32,
  33,
  34,
  37,
  39,
  77,
  89,
  183,
  190,
  206,
  210,
  250,
  307,
  308,
  309,
  312,
  314,
  325,
  326,
  328,
  332,
  334,
  360,
  410,
  434,
  438,
  455,
  462,
  501,
  504,
  520,
  541,
  549,
  550,
  553,
  567,
  568,
  570,
  599,
  600,
  601,
  603,
  604,
  605,
  606,
  607
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 52 → SparsePoly (Fin 63) := ![
  [{ coefficient := 1, powers := [(5, 1), (34, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (31, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(15, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(26, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(26, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(28, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (32, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (34, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (52, 1)] }, { coefficient := 1, powers := [(19, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (32, 1)] }, { coefficient := 1, powers := [(32, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (19, 1)] }, { coefficient := 1, powers := [(17, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (43, 1)] }, { coefficient := 1, powers := [(27, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (29, 1), (44, 1)] }, { coefficient := 1, powers := [(25, 1), (28, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1)] }, { coefficient := 1, powers := [(20, 1), (43, 1)] }, { coefficient := 1, powers := [(24, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (44, 1)] }, { coefficient := 1, powers := [(4, 1), (34, 1)] }, { coefficient := 1, powers := [(15, 1), (21, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (50, 1)] }, { coefficient := 1, powers := [(7, 1), (31, 1)] }, { coefficient := 1, powers := [(11, 1), (26, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (56, 1)] }, { coefficient := 1, powers := [(9, 1), (53, 1)] }, { coefficient := 1, powers := [(14, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (29, 1)] }, { coefficient := 1, powers := [(22, 1), (25, 1), (49, 1)] }, { coefficient := 1, powers := [(29, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (52, 1)] }, { coefficient := 1, powers := [(29, 1), (41, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(28, 1), (51, 1)] }, { coefficient := 1, powers := [(29, 1), (40, 1)] }, { coefficient := 1, powers := [(29, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (41, 1), (53, 1)] }, { coefficient := 1, powers := [(6, 1), (33, 1), (41, 1)] }, { coefficient := 1, powers := [(14, 1), (24, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(20, 1), (52, 1)] }, { coefficient := 1, powers := [(25, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1), (50, 1)] }, { coefficient := 1, powers := [(20, 1), (43, 1), (50, 1)] }, { coefficient := 1, powers := [(47, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (32, 1), (53, 1)] }, { coefficient := 1, powers := [(6, 1), (32, 1), (42, 1)] }, { coefficient := 1, powers := [(14, 1), (32, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (19, 1), (50, 1)] }, { coefficient := 1, powers := [(17, 1), (19, 1), (54, 1)] }, { coefficient := 1, powers := [(17, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (52, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1)] }, { coefficient := 1, powers := [(13, 1), (29, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (57, 1)] }, { coefficient := 1, powers := [(17, 1), (20, 1), (50, 1)] }, { coefficient := 1, powers := [(17, 1), (20, 1), (54, 1)] }, { coefficient := 1, powers := [(17, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1), (48, 1)] }, { coefficient := 1, powers := [(6, 1), (30, 1), (44, 1)] }, { coefficient := 1, powers := [(9, 1), (24, 1), (44, 1)] }, { coefficient := 1, powers := [(48, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1), (50, 1)] }, { coefficient := 1, powers := [(20, 1), (50, 1)] }, { coefficient := 1, powers := [(20, 1), (54, 1)] }, { coefficient := 1, powers := [(46, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (26, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (50, 1)] }, { coefficient := 1, powers := [(17, 1), (26, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (21, 1), (57, 1)] }, { coefficient := 1, powers := [(6, 1), (31, 1), (44, 1)] }, { coefficient := 1, powers := [(6, 1), (34, 1), (40, 1)] }, { coefficient := 1, powers := [(21, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (21, 1), (57, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1), (44, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (40, 1)] }, { coefficient := 1, powers := [(17, 1), (21, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (43, 1), (51, 1)] }, { coefficient := 1, powers := [(23, 1), (55, 1)] }, { coefficient := 1, powers := [(29, 1), (47, 1)] }, { coefficient := 1, powers := [(35, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1)] }, { coefficient := 1, powers := [(6, 1), (57, 1)] }, { coefficient := 1, powers := [(24, 1), (40, 1)] }, { coefficient := 1, powers := [(24, 1), (44, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (50, 1)] }, { coefficient := 1, powers := [(3, 1), (57, 1)] }, { coefficient := 1, powers := [(19, 1), (50, 1)] }, { coefficient := 1, powers := [(19, 1), (54, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (40, 1), (53, 1)] }, { coefficient := 1, powers := [(6, 1), (33, 1), (40, 1)] }, { coefficient := 1, powers := [(14, 1), (24, 1), (40, 1)] }, { coefficient := 1, powers := [(14, 1)] }, { coefficient := 1, powers := [(53, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1)] }, { coefficient := 1, powers := [(3, 1), (33, 1)] }, { coefficient := 1, powers := [(14, 1), (19, 1)] }, { coefficient := 1, powers := [(19, 1), (53, 1)] }, { coefficient := 1, powers := [(24, 1), (42, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (48, 1)] }, { coefficient := 1, powers := [(6, 1), (30, 1)] }, { coefficient := 1, powers := [(9, 1), (24, 1)] }, { coefficient := 1, powers := [(19, 1), (48, 1)] }, { coefficient := 1, powers := [(24, 1), (39, 1)] }, { coefficient := 1, powers := [(30, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (50, 1)] }, { coefficient := 1, powers := [(21, 1), (54, 1)] }, { coefficient := 1, powers := [(26, 1), (40, 1)] }, { coefficient := 1, powers := [(26, 1), (44, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (36, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (39, 1), (53, 1)] }, { coefficient := 1, powers := [(0, 1), (42, 1), (48, 1)] }, { coefficient := 1, powers := [(3, 1), (24, 1), (56, 1)] }, { coefficient := 1, powers := [(3, 1), (30, 1), (53, 1)] }, { coefficient := 1, powers := [(3, 1), (33, 1), (48, 1)] }, { coefficient := 1, powers := [(6, 1), (19, 1), (56, 1)] }, { coefficient := 1, powers := [(6, 1), (30, 1), (42, 1)] }, { coefficient := 1, powers := [(6, 1), (33, 1), (39, 1)] }, { coefficient := 1, powers := [(9, 1), (19, 1), (53, 1)] }, { coefficient := 1, powers := [(9, 1), (24, 1), (42, 1)] }, { coefficient := 1, powers := [(9, 1), (33, 1), (36, 1)] }, { coefficient := 1, powers := [(14, 1), (19, 1), (48, 1)] }, { coefficient := 1, powers := [(14, 1), (24, 1), (39, 1)] }, { coefficient := 1, powers := [(14, 1), (30, 1), (36, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1), (37, 1), (57, 1)] }, { coefficient := 1, powers := [(1, 1), (40, 1), (54, 1)] }, { coefficient := 1, powers := [(1, 1), (44, 1), (50, 1)] }, { coefficient := 1, powers := [(4, 1), (26, 1), (57, 1)] }, { coefficient := 1, powers := [(4, 1), (31, 1), (54, 1)] }, { coefficient := 1, powers := [(4, 1), (34, 1), (50, 1)] }, { coefficient := 1, powers := [(7, 1), (21, 1), (57, 1)] }, { coefficient := 1, powers := [(7, 1), (31, 1), (44, 1)] }, { coefficient := 1, powers := [(7, 1), (34, 1), (40, 1)] }, { coefficient := 1, powers := [(11, 1), (21, 1), (54, 1)] }, { coefficient := 1, powers := [(11, 1), (26, 1), (44, 1)] }, { coefficient := 1, powers := [(11, 1), (34, 1), (37, 1)] }, { coefficient := 1, powers := [(15, 1), (21, 1), (50, 1)] }, { coefficient := 1, powers := [(15, 1), (26, 1), (40, 1)] }, { coefficient := 1, powers := [(15, 1), (31, 1), (37, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (41, 1), (55, 1)] }, { coefficient := 1, powers := [(2, 1), (47, 1), (52, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (52, 1)] }, { coefficient := 1, powers := [(8, 1), (23, 1), (58, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (47, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(13, 1), (23, 1), (55, 1)] }, { coefficient := 1, powers := [(13, 1), (29, 1), (47, 1)] }, { coefficient := 1, powers := [(13, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (52, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (41, 1)] }, { coefficient := 1, powers := [(18, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1)] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(39, 1), (60, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(40, 1), (61, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(41, 1), (62, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 52 → SparsePoly (Fin 63) := ![
  [{ coefficient := 1, powers := [(4, 1), (35, 1), (52, 1), (54, 1)] }, { coefficient := 1, powers := [(7, 1), (35, 1), (40, 1), (52, 1)] }, { coefficient := 1, powers := [(11, 1), (35, 1), (37, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (23, 1), (54, 1), (58, 1)] }, { coefficient := 1, powers := [(4, 1), (35, 1), (41, 1), (54, 1)] }, { coefficient := -1, powers := [(7, 1), (23, 1), (44, 1), (58, 1)] }, { coefficient := -1, powers := [(7, 1), (35, 1), (41, 1), (44, 1)] }, { coefficient := -1, powers := [(11, 1), (23, 1), (37, 1), (58, 1)] }, { coefficient := -1, powers := [(11, 1), (35, 1), (37, 1), (41, 1)] }],
  [{ coefficient := 2, powers := [(0, 2), (5, 1), (9, 1), (32, 1), (40, 1), (44, 1), (55, 1), (61, 1), (62, 1)] }, { coefficient := 2, powers := [(0, 1), (5, 1), (6, 1), (9, 1), (32, 1), (40, 1), (55, 1), (57, 1), (61, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 1), (5, 1), (19, 1), (32, 1), (40, 1), (44, 1), (48, 1), (55, 1), (61, 1), (62, 1)] }, { coefficient := 1, powers := [(0, 1), (5, 1), (32, 1), (48, 1), (55, 1), (62, 1)] }, { coefficient := -1, powers := [(5, 1), (6, 1), (19, 1), (32, 1), (40, 1), (48, 1), (55, 1), (57, 1), (61, 1), (62, 1)] }, { coefficient := -1, powers := [(5, 1), (19, 1), (32, 1), (48, 1), (55, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (34, 1), (35, 1), (37, 1), (52, 1), (62, 1)] }, { coefficient := -1, powers := [(8, 1), (23, 1), (34, 1), (37, 1), (58, 1), (62, 1)] }, { coefficient := -1, powers := [(8, 1), (34, 1), (35, 1), (37, 1), (41, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (11, 1), (17, 1), (23, 1), (50, 1), (58, 1)] }, { coefficient := -1, powers := [(6, 1), (11, 1), (17, 1), (35, 1), (41, 1), (50, 1)] }, { coefficient := -1, powers := [(7, 1), (17, 1), (23, 1), (58, 1)] }, { coefficient := -1, powers := [(7, 1), (17, 1), (35, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (11, 1), (35, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (19, 1), (46, 1), (49, 1), (58, 1), (60, 1), (62, 1)] }, { coefficient := 1, powers := [(5, 1), (20, 1), (49, 1), (58, 1), (60, 1), (62, 1)] }, { coefficient := -1, powers := [(17, 1), (47, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (5, 1), (9, 1), (14, 1), (32, 1), (40, 1), (44, 1), (55, 1), (61, 1), (62, 1)] }, { coefficient := 2, powers := [(0, 1), (5, 1), (9, 1), (14, 1), (32, 1), (40, 1), (55, 1), (62, 1)] }, { coefficient := 1, powers := [(3, 1), (5, 1), (32, 1), (55, 1), (56, 1), (62, 1)] }, { coefficient := -1, powers := [(3, 1), (7, 1), (17, 1), (21, 1), (35, 1), (46, 1), (50, 1), (52, 1), (57, 1), (62, 1)] }, { coefficient := -1, powers := [(3, 1), (7, 1), (17, 1), (21, 1), (35, 1), (46, 1), (52, 1), (54, 1), (57, 1), (62, 1)] }, { coefficient := 1, powers := [(5, 1), (9, 1), (14, 1), (32, 1), (55, 1), (62, 1)] }, { coefficient := 1, powers := [(5, 1), (9, 1), (32, 1), (42, 1), (55, 1), (62, 1)] }, { coefficient := -1, powers := [(5, 1), (14, 1), (19, 1), (32, 1), (40, 1), (44, 1), (48, 1), (55, 1), (61, 1), (62, 1)] }, { coefficient := -1, powers := [(5, 1), (14, 1), (19, 1), (32, 1), (40, 1), (48, 1), (55, 1), (62, 1)] }, { coefficient := -1, powers := [(5, 1), (32, 1), (33, 1), (36, 1), (39, 1), (44, 1), (55, 1), (62, 1)] }, { coefficient := -1, powers := [(5, 1), (32, 1), (42, 1), (48, 1), (55, 1), (62, 1)] }, { coefficient := 1, powers := [(13, 1), (27, 1), (47, 1), (50, 1), (51, 1), (62, 1)] }, { coefficient := -1, powers := [(13, 1), (29, 1), (47, 1), (50, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (8, 1), (23, 1), (57, 1), (58, 1), (62, 1)] }, { coefficient := 1, powers := [(4, 1), (8, 1), (35, 1), (41, 1), (57, 1), (62, 1)] }, { coefficient := -1, powers := [(5, 1), (15, 1), (35, 1), (44, 1), (52, 1), (62, 1)] }, { coefficient := -1, powers := [(8, 1), (11, 1), (23, 1), (40, 1), (58, 1), (62, 1)] }, { coefficient := -1, powers := [(8, 1), (11, 1), (23, 1), (44, 1), (58, 1), (62, 1)] }, { coefficient := -1, powers := [(8, 1), (11, 1), (35, 1), (40, 1), (41, 1), (62, 1)] }, { coefficient := -1, powers := [(8, 1), (11, 1), (35, 1), (41, 1), (44, 1), (62, 1)] }, { coefficient := -1, powers := [(8, 1), (15, 1), (23, 1), (44, 1), (58, 1), (62, 1)] }, { coefficient := -1, powers := [(8, 1), (15, 1), (35, 1), (41, 1), (44, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (17, 1), (35, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (9, 1), (51, 1), (58, 1), (60, 1), (61, 1), (62, 1)] }, { coefficient := -1, powers := [(5, 1), (25, 1), (49, 1), (58, 1), (60, 1), (61, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (19, 1), (33, 1), (48, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (33, 1), (36, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (23, 1), (50, 1), (58, 1), (60, 1)] }, { coefficient := 1, powers := [(4, 1), (23, 1), (54, 1), (58, 1), (60, 1)] }, { coefficient := 1, powers := [(4, 1), (35, 1), (41, 1), (50, 1), (60, 1)] }, { coefficient := 1, powers := [(4, 1), (35, 1), (41, 1), (54, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (22, 1), (46, 1), (49, 1), (58, 1), (60, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (5, 1), (55, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (9, 1), (33, 1), (55, 1)] }, { coefficient := -1, powers := [(5, 1), (19, 1), (33, 1), (44, 1), (48, 1), (55, 1)] }, { coefficient := -1, powers := [(5, 1), (30, 1), (33, 1), (36, 1), (44, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (7, 1), (21, 1), (35, 1), (46, 1), (50, 1), (52, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (7, 1), (21, 1), (35, 1), (46, 1), (52, 1), (54, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [(13, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (58, 1), (60, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(13, 1), (27, 1), (50, 1), (51, 1)] }, { coefficient := 1, powers := [(13, 1), (29, 1), (50, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (35, 1), (52, 1), (54, 1)] }, { coefficient := -1, powers := [(8, 1), (23, 1), (54, 1), (58, 1)] }, { coefficient := -1, powers := [(8, 1), (35, 1), (41, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (35, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(8, 1), (23, 1), (44, 1), (58, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (41, 1), (44, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (5, 1), (32, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (19, 1), (32, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (58, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(18, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (9, 1), (58, 1), (60, 1), (61, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (5, 1), (9, 1), (32, 1), (40, 1), (55, 1), (62, 1)] }, { coefficient := -1, powers := [(5, 1), (9, 1), (32, 1), (55, 1), (62, 1)] }, { coefficient := 1, powers := [(5, 1), (19, 1), (32, 1), (40, 1), (48, 1), (55, 1), (62, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (39, 1), (55, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (22, 1), (49, 1), (58, 1), (60, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (27, 1), (51, 1)] }, { coefficient := -1, powers := [(13, 1), (29, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (30, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (7, 1), (21, 1), (35, 1), (46, 1), (52, 1), (57, 1)] }, { coefficient := -1, powers := [(7, 1), (21, 1), (35, 1), (46, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(47, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (21, 1), (35, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (32, 1), (33, 1), (36, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (17, 1), (21, 1), (35, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (35, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (11, 1), (23, 1), (50, 1), (58, 1)] }, { coefficient := -1, powers := [(8, 1), (11, 1), (35, 1), (41, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (11, 1), (23, 1), (50, 1), (58, 1)] }, { coefficient := 1, powers := [(6, 1), (11, 1), (35, 1), (41, 1), (50, 1)] }, { coefficient := 1, powers := [(7, 1), (23, 1), (58, 1)] }, { coefficient := 1, powers := [(7, 1), (35, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(13, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (5, 1), (9, 1), (14, 1), (32, 1), (40, 1), (55, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (14, 1), (19, 1), (32, 1), (40, 1), (48, 1), (55, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (17, 1), (21, 1), (35, 1), (46, 1), (52, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (5, 1), (9, 1), (32, 1), (40, 1), (55, 1), (61, 1)] }, { coefficient := -1, powers := [(5, 1), (19, 1), (32, 1), (40, 1), (48, 1), (55, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (32, 1), (48, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (32, 1), (33, 1), (36, 1), (44, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (15, 1), (35, 1), (52, 1)] }, { coefficient := 1, powers := [(8, 1), (11, 1), (23, 1), (58, 1)] }, { coefficient := 1, powers := [(8, 1), (11, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(8, 1), (15, 1), (23, 1), (58, 1)] }, { coefficient := 1, powers := [(8, 1), (15, 1), (35, 1), (41, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (32, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (35, 1), (52, 1)] }, { coefficient := -1, powers := [(8, 1), (23, 1), (58, 1)] }, { coefficient := -1, powers := [(8, 1), (35, 1), (41, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(5, 1), (35, 1), (37, 1), (52, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (40, 1), (52, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (44, 1), (52, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (23, 1), (37, 1), (57, 1), (58, 1)] }, { coefficient := 1, powers := [(8, 1), (23, 1), (40, 1), (54, 1), (58, 1)] }, { coefficient := 1, powers := [(8, 1), (23, 1), (44, 1), (54, 1), (58, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (37, 1), (41, 1), (57, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (40, 1), (41, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (41, 1), (44, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(38, 1), (58, 1)] }, { coefficient := 1, powers := [(41, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (8, 1), (23, 1), (34, 1), (50, 1), (58, 1)] }, { coefficient := -1, powers := [(4, 1), (8, 1), (23, 1), (34, 1), (54, 1), (58, 1)] }, { coefficient := -1, powers := [(4, 1), (8, 1), (34, 1), (35, 1), (41, 1), (50, 1)] }, { coefficient := -1, powers := [(4, 1), (8, 1), (34, 1), (35, 1), (41, 1), (54, 1)] }, { coefficient := -1, powers := [(5, 1), (29, 1), (58, 1)] }],
  [{ coefficient := -2, powers := [(0, 2), (5, 1), (9, 1), (32, 1), (40, 1), (53, 1), (55, 1)] }, { coefficient := -2, powers := [(0, 1), (5, 1), (6, 1), (9, 1), (32, 1), (33, 1), (40, 1), (55, 1)] }, { coefficient := -2, powers := [(0, 1), (5, 1), (9, 1), (32, 1), (53, 1), (55, 1)] }, { coefficient := 1, powers := [(0, 1), (5, 1), (19, 1), (32, 1), (40, 1), (48, 1), (53, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (6, 1), (19, 1), (32, 1), (33, 1), (40, 1), (48, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (9, 1), (29, 1), (58, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (19, 1), (32, 1), (48, 1), (53, 1), (55, 1)] }],
  [{ coefficient := -2, powers := [(0, 2), (5, 1), (9, 1), (14, 1), (32, 1), (40, 1), (44, 1), (55, 1), (61, 1)] }, { coefficient := 2, powers := [(0, 2), (5, 1), (9, 1), (32, 1), (40, 1), (53, 1), (55, 1)] }, { coefficient := -2, powers := [(0, 1), (5, 1), (6, 1), (9, 1), (14, 1), (32, 1), (40, 1), (55, 1), (57, 1), (61, 1)] }, { coefficient := 2, powers := [(0, 1), (5, 1), (6, 1), (9, 1), (32, 1), (33, 1), (40, 1), (55, 1)] }, { coefficient := -2, powers := [(0, 1), (5, 1), (9, 1), (14, 1), (24, 1), (32, 1), (40, 1), (44, 1), (55, 1), (61, 1)] }, { coefficient := 1, powers := [(0, 1), (5, 1), (9, 1), (32, 1), (53, 1), (55, 1)] }, { coefficient := 1, powers := [(0, 1), (5, 1), (14, 1), (19, 1), (32, 1), (40, 1), (44, 1), (48, 1), (55, 1), (61, 1)] }, { coefficient := -1, powers := [(0, 1), (5, 1), (14, 1), (32, 1), (48, 1), (55, 1)] }, { coefficient := -1, powers := [(0, 1), (5, 1), (19, 1), (32, 1), (40, 1), (48, 1), (53, 1), (55, 1)] }, { coefficient := -1, powers := [(0, 1), (5, 1), (32, 1), (39, 1), (53, 1), (55, 1)] }, { coefficient := -1, powers := [(3, 1), (5, 1), (24, 1), (32, 1), (55, 1), (56, 1)] }, { coefficient := 1, powers := [(3, 1), (7, 1), (17, 1), (21, 1), (24, 1), (35, 1), (46, 1), (50, 1), (52, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (7, 1), (17, 1), (21, 1), (24, 1), (35, 1), (46, 1), (52, 1), (54, 1), (57, 1)] }, { coefficient := -1, powers := [(4, 1), (8, 1), (23, 1), (26, 1), (57, 1), (58, 1)] }, { coefficient := -1, powers := [(4, 1), (8, 1), (26, 1), (35, 1), (41, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (6, 1), (9, 1), (32, 1), (33, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (6, 1), (14, 1), (19, 1), (32, 1), (40, 1), (48, 1), (55, 1), (57, 1), (61, 1)] }, { coefficient := -1, powers := [(5, 1), (6, 1), (19, 1), (32, 1), (33, 1), (40, 1), (48, 1), (55, 1)] }, { coefficient := -1, powers := [(5, 1), (6, 1), (32, 1), (33, 1), (39, 1), (55, 1)] }, { coefficient := -1, powers := [(5, 1), (9, 1), (24, 1), (32, 1), (42, 1), (55, 1)] }, { coefficient := -1, powers := [(5, 1), (9, 1), (28, 1), (51, 1), (58, 1), (60, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (14, 1), (19, 1), (24, 1), (32, 1), (40, 1), (44, 1), (48, 1), (55, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (14, 1), (19, 1), (32, 1), (48, 1), (55, 1)] }, { coefficient := -1, powers := [(5, 1), (14, 1), (24, 1), (32, 1), (39, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (15, 1), (26, 1), (35, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(5, 1), (15, 1), (34, 1), (35, 1), (37, 1), (52, 1)] }, { coefficient := 1, powers := [(5, 1), (22, 1), (25, 1), (49, 1), (58, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (24, 1), (32, 1), (33, 1), (36, 1), (39, 1), (44, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (24, 1), (32, 1), (42, 1), (48, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (25, 1), (28, 1), (49, 1), (58, 1), (60, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (11, 1), (23, 1), (26, 1), (40, 1), (58, 1)] }, { coefficient := 1, powers := [(8, 1), (11, 1), (23, 1), (26, 1), (44, 1), (58, 1)] }, { coefficient := 1, powers := [(8, 1), (11, 1), (26, 1), (35, 1), (40, 1), (41, 1)] }, { coefficient := 1, powers := [(8, 1), (11, 1), (26, 1), (35, 1), (41, 1), (44, 1)] }, { coefficient := 1, powers := [(8, 1), (15, 1), (23, 1), (26, 1), (44, 1), (58, 1)] }, { coefficient := 1, powers := [(8, 1), (15, 1), (23, 1), (34, 1), (37, 1), (58, 1)] }, { coefficient := 1, powers := [(8, 1), (15, 1), (26, 1), (35, 1), (41, 1), (44, 1)] }, { coefficient := 1, powers := [(8, 1), (15, 1), (34, 1), (35, 1), (37, 1), (41, 1)] }, { coefficient := -1, powers := [(13, 1), (24, 1), (27, 1), (47, 1), (50, 1), (51, 1)] }, { coefficient := 1, powers := [(13, 1), (24, 1), (29, 1), (47, 1), (50, 1)] }]
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
    (values : Fin 63 → R) :
    ¬ ∀ index : Fin 52,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component17.SelectedLeafB4_7.selectedHasNoCommonZero

end Krenn.Component17.SelectedLeafB4_7
