import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component12.SelectedLeafB4_7

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "1d63d26bb5f9636a29ec4d29d7eb7e677f89e5a568539c9cdef9c492411b3804"
def certificateSHA256 : String := "108ca2375bf11be9b929664679ab850f0bf1eae76e89ac15bb46083f331a6d8b"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 38 → Fin 619 := ![
  8,
  11,
  23,
  27,
  34,
  35,
  41,
  44,
  192,
  211,
  213,
  216,
  218,
  266,
  309,
  333,
  334,
  339,
  342,
  350,
  351,
  352,
  357,
  359,
  462,
  464,
  473,
  498,
  549,
  562,
  571,
  580,
  612,
  613,
  615,
  616,
  617,
  618
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 38 → SparsePoly (Fin 63) := ![
  [{ coefficient := 1, powers := [(3, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (18, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(40, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (52, 1)] }, { coefficient := 1, powers := [(18, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (39, 1)] }, { coefficient := 1, powers := [(17, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (42, 1)] }, { coefficient := 1, powers := [(26, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (40, 1), (54, 1)] }, { coefficient := 1, powers := [(40, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(52, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (28, 1), (44, 1)] }, { coefficient := 1, powers := [(24, 1), (27, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (23, 1), (39, 1)] }, { coefficient := 1, powers := [(17, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1)] }, { coefficient := 1, powers := [(18, 1), (42, 1)] }, { coefficient := 1, powers := [(23, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (42, 1)] }, { coefficient := 1, powers := [(23, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (52, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1)] }, { coefficient := 1, powers := [(12, 1), (28, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (28, 1)] }, { coefficient := 1, powers := [(21, 1), (24, 1), (49, 1)] }, { coefficient := 1, powers := [(28, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (52, 1)] }, { coefficient := 1, powers := [(28, 1), (40, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (51, 1)] }, { coefficient := 1, powers := [(28, 1), (39, 1)] }, { coefficient := 1, powers := [(28, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (35, 1), (58, 1)] }, { coefficient := 1, powers := [(3, 1), (23, 1), (58, 1)] }, { coefficient := 1, powers := [(6, 1), (18, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(19, 1), (52, 1)] }, { coefficient := 1, powers := [(24, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1), (50, 1)] }, { coefficient := 1, powers := [(19, 1), (42, 1), (50, 1)] }, { coefficient := 1, powers := [(47, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (34, 1)] }, { coefficient := 1, powers := [(21, 1), (42, 1)] }, { coefficient := 1, powers := [(26, 1), (42, 1)] }, { coefficient := 1, powers := [(34, 1), (35, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (58, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (45, 1)] }, { coefficient := 1, powers := [(12, 1), (55, 1)] }, { coefficient := 1, powers := [(17, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1), (51, 1)] }, { coefficient := 1, powers := [(18, 1), (42, 1), (51, 1)] }, { coefficient := 1, powers := [(18, 1), (55, 1)] }, { coefficient := 1, powers := [(24, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (28, 1), (58, 1)] }, { coefficient := 1, powers := [(3, 1), (31, 1), (55, 1)] }, { coefficient := 1, powers := [(3, 1), (34, 1), (52, 1)] }, { coefficient := 1, powers := [(21, 1), (42, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (42, 1), (51, 1)] }, { coefficient := 1, powers := [(22, 1), (55, 1)] }, { coefficient := 1, powers := [(28, 1), (47, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (50, 1)] }, { coefficient := 1, powers := [(3, 1), (57, 1)] }, { coefficient := 1, powers := [(18, 1), (50, 1)] }, { coefficient := 1, powers := [(18, 1), (54, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (39, 1), (55, 1)] }, { coefficient := 1, powers := [(2, 1), (45, 1), (51, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (39, 1)] }, { coefficient := 1, powers := [(17, 1), (27, 1), (51, 1)] }, { coefficient := 1, powers := [(17, 1), (28, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (35, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1)] }, { coefficient := 1, powers := [(3, 1), (23, 1), (57, 1)] }, { coefficient := 1, powers := [(6, 1), (18, 1), (57, 1)] }, { coefficient := 1, powers := [(18, 1)] }, { coefficient := 1, powers := [(23, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (37, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (40, 1), (55, 1)] }, { coefficient := 1, powers := [(2, 1), (47, 1), (52, 1)] }, { coefficient := 1, powers := [(5, 1), (28, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (52, 1)] }, { coefficient := 1, powers := [(8, 1), (22, 1), (58, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1), (47, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (40, 1)] }, { coefficient := 1, powers := [(12, 1), (22, 1), (55, 1)] }, { coefficient := 1, powers := [(12, 1), (28, 1), (47, 1)] }, { coefficient := 1, powers := [(12, 1), (34, 1), (37, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (52, 1)] }, { coefficient := 1, powers := [(17, 1), (28, 1), (40, 1)] }, { coefficient := 1, powers := [(17, 1), (31, 1), (37, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (59, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(38, 1), (60, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(39, 1), (61, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(40, 1), (62, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 38 → SparsePoly (Fin 63) := ![
  [{ coefficient := 1, powers := [(0, 1), (5, 1), (12, 1), (22, 1), (28, 1), (55, 1), (57, 1), (59, 1)] }, { coefficient := -1, powers := [(0, 1), (5, 1), (28, 1), (57, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (12, 1), (18, 1), (22, 1), (28, 1), (55, 1), (57, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (12, 1), (22, 1), (23, 1), (28, 1), (50, 1), (55, 1), (57, 1)] }, { coefficient := -1, powers := [(5, 1), (12, 1), (22, 1), (23, 1), (28, 1), (55, 1), (57, 1), (59, 1)] }, { coefficient := -1, powers := [(5, 1), (18, 1), (28, 1), (57, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (28, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (12, 1), (22, 1), (31, 1), (35, 1), (50, 1), (55, 2)] }, { coefficient := 1, powers := [(0, 1), (12, 1), (22, 1), (31, 1), (35, 1), (55, 2), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (31, 1), (35, 1), (50, 1), (55, 1)] }, { coefficient := -1, powers := [(0, 1), (31, 1), (35, 1), (55, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (12, 1), (22, 1), (31, 1), (55, 2)] }, { coefficient := -1, powers := [(3, 1), (31, 1), (55, 1)] }, { coefficient := -1, powers := [(6, 1), (12, 1), (18, 1), (22, 1), (31, 1), (50, 1), (55, 2)] }, { coefficient := 1, powers := [(6, 1), (12, 1), (18, 1), (22, 1), (31, 1), (55, 2), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (18, 1), (31, 1), (50, 1), (55, 1)] }, { coefficient := -1, powers := [(6, 1), (18, 1), (31, 1), (55, 1), (59, 1)] }],
  [{ coefficient := 2, powers := [(12, 1), (22, 2), (24, 1), (55, 1)] }, { coefficient := 2, powers := [(12, 1), (22, 1), (24, 1), (34, 1), (37, 1)] }, { coefficient := -2, powers := [(22, 1), (24, 1)] }],
  [{ coefficient := 2, powers := [(12, 1), (22, 2), (44, 1), (52, 1), (55, 1)] }, { coefficient := 2, powers := [(12, 1), (22, 1), (34, 1), (37, 1), (44, 1), (52, 1)] }, { coefficient := -2, powers := [(22, 1), (44, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (12, 1), (22, 1), (42, 1), (55, 1), (57, 1)] }, { coefficient := -2, powers := [(5, 1), (18, 1), (46, 1), (49, 1), (58, 1), (60, 1), (62, 1)] }, { coefficient := 2, powers := [(5, 1), (19, 1), (49, 1), (58, 1), (60, 1), (62, 1)] }, { coefficient := 1, powers := [(5, 1), (42, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (5, 1), (12, 1), (22, 1), (28, 1), (50, 1), (55, 1), (57, 1), (58, 1), (62, 1)] }, { coefficient := 1, powers := [(3, 1), (5, 1), (12, 1), (22, 1), (28, 1), (55, 1), (57, 1), (58, 1), (59, 1), (62, 1)] }, { coefficient := -1, powers := [(3, 1), (5, 1), (12, 1), (22, 1), (31, 1), (50, 1), (55, 2), (57, 1), (62, 1)] }, { coefficient := 1, powers := [(3, 1), (5, 1), (12, 1), (22, 1), (31, 1), (55, 2), (57, 1), (59, 1), (62, 1)] }, { coefficient := 1, powers := [(3, 1), (5, 1), (31, 1), (50, 1), (55, 1), (57, 1), (62, 1)] }, { coefficient := -1, powers := [(3, 1), (5, 1), (31, 1), (55, 1), (57, 1), (59, 1), (62, 1)] }, { coefficient := -1, powers := [(5, 1), (12, 1), (22, 1), (28, 1), (50, 1), (55, 1), (58, 1), (62, 1)] }, { coefficient := 1, powers := [(5, 1), (12, 1), (22, 1), (28, 1), (55, 1), (58, 1), (59, 1), (62, 1)] }, { coefficient := -1, powers := [(5, 1), (12, 1), (22, 1), (31, 1), (50, 1), (55, 2), (62, 1)] }, { coefficient := 1, powers := [(5, 1), (12, 1), (22, 1), (31, 1), (55, 2), (59, 1), (62, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (50, 1), (55, 1), (62, 1)] }, { coefficient := -1, powers := [(5, 1), (31, 1), (55, 1), (59, 1), (62, 1)] }, { coefficient := -2, powers := [(12, 1), (17, 1), (22, 1), (28, 1), (37, 1), (50, 1), (58, 1), (62, 1)] }, { coefficient := 2, powers := [(12, 1), (17, 1), (22, 1), (28, 1), (40, 1), (50, 1), (55, 1), (62, 1)] }, { coefficient := 2, powers := [(12, 1), (26, 1), (47, 1), (50, 1), (51, 1), (62, 1)] }, { coefficient := -2, powers := [(12, 1), (28, 1), (47, 1), (50, 1), (62, 1)] }, { coefficient := -2, powers := [(17, 1), (28, 1), (40, 1), (50, 1), (62, 1)] }],
  [{ coefficient := 2, powers := [(5, 1), (9, 1), (51, 1), (58, 1), (60, 1), (61, 1), (62, 1)] }, { coefficient := -2, powers := [(5, 1), (24, 1), (49, 1), (58, 1), (60, 1), (61, 1), (62, 1)] }, { coefficient := -2, powers := [(12, 1), (17, 1), (22, 1), (37, 1), (51, 1), (58, 1), (61, 1), (62, 1)] }, { coefficient := 2, powers := [(12, 1), (17, 1), (22, 1), (40, 1), (51, 1), (55, 1), (61, 1), (62, 1)] }, { coefficient := -2, powers := [(17, 1), (40, 1), (51, 1), (61, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (5, 1), (12, 1), (22, 1), (26, 1), (52, 1), (55, 1), (57, 1), (59, 1), (62, 1)] }, { coefficient := 1, powers := [(0, 1), (5, 1), (26, 1), (52, 1), (57, 1), (59, 1), (62, 1)] }, { coefficient := 1, powers := [(3, 1), (5, 1), (12, 1), (22, 1), (23, 1), (31, 1), (51, 1), (55, 1), (57, 1), (59, 1), (62, 1)] }, { coefficient := -1, powers := [(3, 1), (5, 1), (12, 1), (22, 1), (24, 1), (31, 1), (55, 1), (57, 1), (59, 1), (62, 1)] }, { coefficient := -1, powers := [(3, 1), (5, 1), (23, 1), (31, 1), (51, 1), (57, 1), (59, 1), (62, 1)] }, { coefficient := 1, powers := [(3, 1), (5, 1), (24, 1), (31, 1), (57, 1), (59, 1), (62, 1)] }, { coefficient := -1, powers := [(5, 1), (12, 1), (18, 1), (22, 1), (26, 1), (52, 1), (55, 1), (57, 1), (59, 1), (62, 1)] }, { coefficient := 1, powers := [(5, 1), (18, 1), (26, 1), (52, 1), (57, 1), (59, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (12, 1), (22, 1), (34, 1), (35, 1), (55, 1), (57, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (12, 1), (22, 1), (34, 1), (40, 1), (50, 1), (55, 1), (62, 1)] }, { coefficient := 1, powers := [(5, 1), (12, 1), (22, 1), (34, 1), (40, 1), (54, 1), (55, 1), (62, 1)] }, { coefficient := 2, powers := [(5, 1), (21, 1), (46, 1), (49, 1), (58, 1), (60, 1), (62, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (35, 1), (57, 1), (59, 1)] }, { coefficient := -1, powers := [(5, 1), (34, 1), (40, 1), (50, 1), (62, 1)] }, { coefficient := -1, powers := [(5, 1), (34, 1), (40, 1), (54, 1), (62, 1)] }, { coefficient := -2, powers := [(12, 1), (17, 1), (22, 2), (44, 1), (55, 1)] }, { coefficient := -2, powers := [(12, 1), (17, 1), (22, 1), (34, 1), (37, 1), (44, 1)] }, { coefficient := 2, powers := [(17, 1), (22, 1), (44, 1)] }],
  [{ coefficient := 2, powers := [(12, 1), (22, 1), (23, 1), (28, 1), (37, 1), (58, 1)] }, { coefficient := -2, powers := [(12, 1), (22, 1), (23, 1), (28, 1), (40, 1), (55, 1)] }, { coefficient := 2, powers := [(23, 1), (28, 1), (40, 1)] }],
  [{ coefficient := -2, powers := [(12, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (12, 1), (18, 1), (22, 1), (28, 1), (55, 1), (58, 1), (59, 1), (62, 1)] }, { coefficient := 1, powers := [(5, 1), (12, 1), (18, 1), (22, 1), (31, 1), (55, 2), (59, 1), (62, 1)] }, { coefficient := -1, powers := [(5, 1), (12, 1), (22, 1), (34, 1), (52, 1), (55, 1), (62, 1)] }, { coefficient := -1, powers := [(5, 1), (18, 1), (31, 1), (55, 1), (59, 1), (62, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (52, 1), (62, 1)] }],
  [{ coefficient := 2, powers := [(12, 1), (17, 1), (22, 2), (55, 1)] }, { coefficient := 2, powers := [(12, 1), (17, 1), (22, 1), (34, 1), (37, 1)] }, { coefficient := -2, powers := [(17, 1), (22, 1)] }],
  [{ coefficient := 2, powers := [(5, 1), (58, 1), (60, 1), (61, 1)] }],
  [{ coefficient := -2, powers := [(12, 1), (22, 1), (28, 1), (37, 1), (58, 1)] }, { coefficient := 2, powers := [(12, 1), (22, 1), (28, 1), (40, 1), (55, 1)] }, { coefficient := -2, powers := [(28, 1), (40, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (5, 1), (12, 1), (22, 1), (31, 1), (51, 1), (55, 1), (57, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (5, 1), (31, 1), (51, 1), (57, 1), (59, 1)] }],
  [{ coefficient := -2, powers := [(12, 1), (26, 1), (50, 1), (51, 1)] }, { coefficient := 2, powers := [(12, 1), (28, 1), (50, 1)] }],
  [{ coefficient := -2, powers := [(12, 1), (22, 1), (47, 1), (55, 1)] }, { coefficient := 2, powers := [(47, 1)] }],
  [{ coefficient := 2, powers := [(5, 1), (58, 1), (60, 1)] }],
  [{ coefficient := -2, powers := [(12, 1), (17, 1), (22, 1), (55, 1)] }, { coefficient := 2, powers := [(17, 1)] }],
  [{ coefficient := -2, powers := [(5, 1), (9, 1), (58, 1), (60, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (12, 1), (22, 1), (28, 1), (50, 1), (55, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (12, 1), (22, 1), (28, 1), (55, 1), (57, 1), (59, 1)] }],
  [{ coefficient := -2, powers := [(5, 1), (21, 1), (49, 1), (58, 1), (60, 1), (62, 1)] }],
  [{ coefficient := 2, powers := [(12, 1), (26, 1), (51, 1)] }, { coefficient := -2, powers := [(12, 1), (28, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (5, 1), (12, 1), (22, 1), (52, 1), (55, 1), (57, 1), (59, 1)] }, { coefficient := -1, powers := [(0, 1), (5, 1), (52, 1), (57, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (12, 1), (18, 1), (22, 1), (52, 1), (55, 1), (57, 1), (59, 1)] }, { coefficient := -1, powers := [(5, 1), (18, 1), (52, 1), (57, 1), (59, 1)] }],
  [{ coefficient := -2, powers := [(12, 1), (22, 2), (55, 1)] }, { coefficient := -2, powers := [(12, 1), (22, 1), (34, 1), (37, 1)] }, { coefficient := 2, powers := [(22, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (5, 1), (12, 1), (22, 1), (31, 1), (55, 1), (57, 1), (59, 1)] }, { coefficient := -1, powers := [(3, 1), (5, 1), (31, 1), (57, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (5, 1), (12, 1), (22, 1), (55, 1), (57, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (5, 1), (57, 1), (59, 1)] }, { coefficient := -1, powers := [(5, 1), (12, 1), (18, 1), (22, 1), (55, 1), (57, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (12, 1), (22, 1), (55, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (18, 1), (57, 1), (59, 1)] }, { coefficient := -1, powers := [(5, 1), (57, 1)] }],
  [{ coefficient := 2, powers := [(12, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (12, 1), (22, 1), (28, 1), (55, 1), (58, 1)] }, { coefficient := -1, powers := [(5, 1), (12, 1), (22, 1), (31, 1), (55, 2)] }, { coefficient := -1, powers := [(5, 1), (12, 1), (22, 1), (34, 1), (40, 1), (52, 1), (55, 1), (62, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (40, 1), (52, 1), (62, 1)] }],
  [{ coefficient := 2, powers := [(12, 1), (22, 1), (37, 1), (58, 1), (61, 1)] }, { coefficient := -2, powers := [(12, 1), (22, 1), (40, 1), (55, 1), (61, 1)] }, { coefficient := 2, powers := [(40, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (12, 1), (22, 1), (28, 1), (50, 1), (55, 1), (58, 1)] }, { coefficient := -1, powers := [(5, 1), (12, 1), (22, 1), (28, 1), (55, 1), (58, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (12, 1), (22, 1), (31, 1), (50, 1), (55, 2)] }, { coefficient := -1, powers := [(5, 1), (12, 1), (22, 1), (31, 1), (55, 2), (59, 1)] }, { coefficient := -1, powers := [(5, 1), (31, 1), (50, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (55, 1), (59, 1)] }],
  [{ coefficient := 2, powers := [(12, 1), (22, 1), (55, 1)] }, { coefficient := -2, powers := [] }],
  [{ coefficient := 1, powers := [(3, 1), (5, 1), (12, 1), (22, 1), (31, 1), (55, 2), (57, 1)] }, { coefficient := -1, powers := [(3, 1), (5, 1), (31, 1), (55, 1), (57, 1)] }, { coefficient := -1, powers := [(5, 1), (12, 1), (18, 1), (22, 1), (28, 1), (40, 1), (54, 1), (55, 1), (58, 1), (62, 1)] }, { coefficient := -1, powers := [(5, 1), (12, 1), (18, 1), (22, 1), (31, 1), (40, 1), (54, 1), (55, 2), (62, 1)] }, { coefficient := 1, powers := [(5, 1), (12, 1), (22, 1), (28, 1), (55, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (12, 1), (22, 1), (31, 1), (55, 2)] }, { coefficient := 1, powers := [(5, 1), (18, 1), (31, 1), (40, 1), (54, 1), (55, 1), (62, 1)] }, { coefficient := -1, powers := [(5, 1), (31, 1), (55, 1)] }],
  [{ coefficient := -2, powers := [(12, 1), (22, 1), (37, 1), (39, 1), (55, 1), (58, 1), (61, 1)] }, { coefficient := -2, powers := [(12, 1), (22, 1), (37, 1), (45, 1), (51, 1), (58, 1), (61, 1)] }, { coefficient := -2, powers := [(12, 1), (22, 1), (37, 1), (55, 1), (58, 1)] }, { coefficient := 2, powers := [(12, 1), (22, 1), (39, 1), (40, 1), (55, 2), (61, 1)] }, { coefficient := 2, powers := [(12, 1), (22, 1), (40, 1), (45, 1), (51, 1), (55, 1), (61, 1)] }, { coefficient := -2, powers := [(12, 1), (22, 1), (40, 1), (55, 2)] }, { coefficient := 2, powers := [(37, 1), (58, 1)] }, { coefficient := -2, powers := [(39, 1), (40, 1), (55, 1), (61, 1)] }, { coefficient := -2, powers := [(40, 1), (45, 1), (51, 1), (61, 1)] }, { coefficient := 2, powers := [(40, 1), (55, 1)] }],
  [{ coefficient := -2, powers := [(5, 1), (28, 1), (58, 1)] }],
  [{ coefficient := 2, powers := [(5, 1), (9, 1), (28, 1), (58, 1), (60, 1)] }, { coefficient := -2, powers := [(8, 1), (12, 1), (22, 1), (34, 1), (37, 1), (58, 1)] }, { coefficient := 2, powers := [(8, 1), (12, 1), (22, 1), (34, 1), (40, 1), (55, 1)] }, { coefficient := -2, powers := [(8, 1), (34, 1), (40, 1)] }, { coefficient := -2, powers := [(12, 1), (17, 1), (22, 1), (28, 1), (37, 1), (58, 1)] }, { coefficient := 2, powers := [(12, 1), (17, 1), (22, 1), (28, 1), (40, 1), (55, 1)] }, { coefficient := -2, powers := [(17, 1), (28, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (5, 1), (12, 1), (22, 1), (26, 1), (42, 1), (52, 1), (55, 1), (57, 1), (59, 1)] }, { coefficient := -1, powers := [(0, 1), (5, 1), (26, 1), (42, 1), (52, 1), (57, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (5, 1), (12, 1), (22, 1), (23, 1), (28, 1), (50, 1), (55, 1), (57, 1), (58, 1)] }, { coefficient := -1, powers := [(3, 1), (5, 1), (12, 1), (22, 1), (23, 1), (28, 1), (55, 1), (57, 1), (58, 1), (59, 1)] }, { coefficient := -1, powers := [(3, 1), (5, 1), (12, 1), (22, 1), (23, 1), (31, 1), (42, 1), (51, 1), (55, 1), (57, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (5, 1), (12, 1), (22, 1), (23, 1), (31, 1), (50, 1), (55, 2), (57, 1)] }, { coefficient := -1, powers := [(3, 1), (5, 1), (12, 1), (22, 1), (23, 1), (31, 1), (55, 2), (57, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (5, 1), (12, 1), (22, 1), (24, 1), (31, 1), (42, 1), (55, 1), (57, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (5, 1), (12, 1), (22, 1), (34, 1), (52, 1), (55, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (5, 1), (23, 1), (31, 1), (42, 1), (51, 1), (57, 1), (59, 1)] }, { coefficient := -1, powers := [(3, 1), (5, 1), (23, 1), (31, 1), (50, 1), (55, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (5, 1), (23, 1), (31, 1), (55, 1), (57, 1), (59, 1)] }, { coefficient := -1, powers := [(3, 1), (5, 1), (24, 1), (31, 1), (42, 1), (57, 1), (59, 1)] }, { coefficient := -1, powers := [(3, 1), (5, 1), (34, 1), (52, 1), (57, 1)] }, { coefficient := -2, powers := [(5, 1), (9, 1), (27, 1), (51, 1), (58, 1), (60, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (12, 1), (18, 1), (22, 1), (26, 1), (42, 1), (52, 1), (55, 1), (57, 1), (59, 1)] }, { coefficient := -1, powers := [(5, 1), (12, 1), (18, 1), (22, 1), (28, 1), (54, 1), (55, 1), (58, 1)] }, { coefficient := -1, powers := [(5, 1), (12, 1), (18, 1), (22, 1), (28, 1), (55, 1), (58, 1), (59, 1)] }, { coefficient := -1, powers := [(5, 1), (12, 1), (18, 1), (22, 1), (31, 1), (54, 1), (55, 2)] }, { coefficient := -1, powers := [(5, 1), (12, 1), (18, 1), (22, 1), (31, 1), (55, 2), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (12, 1), (22, 1), (23, 1), (28, 1), (50, 1), (55, 1), (58, 1)] }, { coefficient := -1, powers := [(5, 1), (12, 1), (22, 1), (23, 1), (28, 1), (55, 1), (58, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (12, 1), (22, 1), (23, 1), (31, 1), (50, 1), (55, 2)] }, { coefficient := -1, powers := [(5, 1), (12, 1), (22, 1), (23, 1), (31, 1), (55, 2), (59, 1)] }, { coefficient := 2, powers := [(5, 1), (12, 1), (22, 1), (34, 1), (52, 1), (55, 1)] }, { coefficient := -1, powers := [(5, 1), (18, 1), (26, 1), (42, 1), (52, 1), (57, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (18, 1), (31, 1), (54, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (18, 1), (31, 1), (55, 1), (59, 1)] }, { coefficient := 2, powers := [(5, 1), (21, 1), (24, 1), (49, 1), (58, 1), (60, 1)] }, { coefficient := -1, powers := [(5, 1), (23, 1), (31, 1), (50, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (23, 1), (31, 1), (55, 1), (59, 1)] }, { coefficient := 2, powers := [(5, 1), (24, 1), (27, 1), (49, 1), (58, 1), (60, 1), (61, 1)] }, { coefficient := -2, powers := [(5, 1), (34, 1), (52, 1)] }, { coefficient := 2, powers := [(12, 1), (17, 1), (22, 1), (23, 1), (28, 1), (37, 1), (50, 1), (58, 1)] }, { coefficient := -2, powers := [(12, 1), (17, 1), (22, 1), (23, 1), (28, 1), (40, 1), (50, 1), (55, 1)] }, { coefficient := 2, powers := [(12, 1), (17, 1), (22, 1), (27, 1), (37, 1), (51, 1), (58, 1), (61, 1)] }, { coefficient := -2, powers := [(12, 1), (17, 1), (22, 1), (27, 1), (40, 1), (51, 1), (55, 1), (61, 1)] }, { coefficient := -2, powers := [(12, 1), (23, 1), (26, 1), (47, 1), (50, 1), (51, 1)] }, { coefficient := 2, powers := [(12, 1), (23, 1), (28, 1), (47, 1), (50, 1)] }, { coefficient := 2, powers := [(17, 1), (23, 1), (28, 1), (40, 1), (50, 1)] }, { coefficient := 2, powers := [(17, 1), (27, 1), (40, 1), (51, 1), (61, 1)] }]
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
    (values : Fin 63 → R) :
    ¬ ∀ index : Fin 38,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((2 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (2 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (2 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component12.SelectedLeafB4_7.selectedHasNoCommonZero

end Krenn.Component12.SelectedLeafB4_7
