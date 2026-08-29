import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component65.SelectedLeafB6_2_1

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "968fe279f737778982763a0813f70a3652b3614d5e3264cade12aa892e9f4e70"
def certificateSHA256 : String := "ad90df3fb0ca7453ec4b1f96b09c7595b79bac48470fa1b773240efd6fdc38ad"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 36 → Fin 671 := ![
  12,
  19,
  24,
  26,
  29,
  175,
  176,
  178,
  254,
  301,
  309,
  310,
  312,
  315,
  376,
  378,
  414,
  416,
  420,
  421,
  423,
  434,
  444,
  528,
  540,
  582,
  610,
  645,
  661,
  662,
  663,
  664,
  666,
  667,
  669,
  670
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 36 → SparsePoly (Fin 65) := ![
  [{ coefficient := 1, powers := [(5, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (20, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(28, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (24, 1)] }, { coefficient := 1, powers := [(16, 1), (19, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (25, 1)] }, { coefficient := 1, powers := [(16, 1), (19, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (42, 1)] }, { coefficient := 1, powers := [(17, 1), (19, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (19, 1), (56, 1)] }, { coefficient := 1, powers := [(13, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1)] }, { coefficient := 1, powers := [(19, 1), (42, 1)] }, { coefficient := 1, powers := [(24, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (47, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1)] }, { coefficient := 1, powers := [(13, 1), (28, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (45, 1)] }, { coefficient := 1, powers := [(17, 1), (39, 1)] }, { coefficient := 1, powers := [(17, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1), (51, 1)] }, { coefficient := 1, powers := [(19, 1), (42, 1), (51, 1)] }, { coefficient := 1, powers := [(42, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (19, 1), (57, 1)] }, { coefficient := 1, powers := [(11, 1), (25, 1), (42, 1)] }, { coefficient := 1, powers := [(17, 1), (19, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (24, 1), (45, 1)] }, { coefficient := 1, powers := [(17, 1), (24, 1), (39, 1)] }, { coefficient := 1, powers := [(17, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (53, 1)] }, { coefficient := 1, powers := [(3, 1), (25, 1), (59, 1)] }, { coefficient := 1, powers := [(19, 1), (53, 1)] }, { coefficient := 1, powers := [(25, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (45, 1)] }, { coefficient := 1, powers := [(11, 1), (26, 1), (45, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1)] }, { coefficient := 1, powers := [(17, 1), (26, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (60, 1)] }, { coefficient := 1, powers := [(13, 1), (47, 1)] }, { coefficient := 1, powers := [(18, 1), (20, 1), (52, 1)] }, { coefficient := 1, powers := [(18, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (60, 1)] }, { coefficient := 1, powers := [(13, 1), (25, 1), (45, 1)] }, { coefficient := 1, powers := [(13, 1), (57, 1)] }, { coefficient := 1, powers := [(18, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (54, 1)] }, { coefficient := 1, powers := [(28, 1), (40, 1)] }, { coefficient := 1, powers := [(28, 1), (46, 1), (49, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1), (53, 1)] }, { coefficient := 1, powers := [(19, 1), (42, 1), (53, 1)] }, { coefficient := 1, powers := [(19, 1), (57, 1)] }, { coefficient := 1, powers := [(25, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1), (51, 1)] }, { coefficient := 1, powers := [(39, 1), (42, 1)] }, { coefficient := 1, powers := [(42, 1), (51, 1)] }, { coefficient := 1, powers := [(45, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (25, 1), (45, 1)] }, { coefficient := 1, powers := [(11, 1), (57, 1)] }, { coefficient := 1, powers := [(17, 1), (25, 1), (39, 1)] }, { coefficient := 1, powers := [(17, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (42, 1), (53, 1)] }, { coefficient := 1, powers := [(23, 1), (57, 1)] }, { coefficient := 1, powers := [(28, 1), (47, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (51, 1)] }, { coefficient := 1, powers := [(3, 1), (59, 1)] }, { coefficient := 1, powers := [(19, 1), (51, 1)] }, { coefficient := 1, powers := [(19, 1), (56, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (39, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (45, 1), (53, 1)] }, { coefficient := 1, powers := [(25, 1), (39, 1), (42, 1)] }, { coefficient := 1, powers := [(25, 1), (45, 1)] }, { coefficient := 1, powers := [(42, 1), (53, 1)] }, { coefficient := 1, powers := [(57, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (36, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (44, 1), (51, 1)] }, { coefficient := 1, powers := [(39, 1)] }, { coefficient := 1, powers := [(44, 1)] }, { coefficient := 1, powers := [(51, 1)] }, { coefficient := 1, powers := [(56, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (37, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (47, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (28, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (23, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1), (47, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (40, 1)] }, { coefficient := 1, powers := [(13, 1), (23, 1), (57, 1)] }, { coefficient := 1, powers := [(13, 1), (28, 1), (47, 1)] }, { coefficient := 1, powers := [(13, 1), (34, 1), (37, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (54, 1)] }, { coefficient := 1, powers := [(18, 1), (28, 1), (40, 1)] }, { coefficient := 1, powers := [(18, 1), (31, 1), (37, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (61, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(39, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(40, 1)] }],
  [{ coefficient := 1, powers := [(56, 1)] }],
  [{ coefficient := 1, powers := [(57, 1), (64, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 36 → SparsePoly (Fin 65) := ![
  [{ coefficient := 1, powers := [(0, 2), (31, 1), (36, 1), (57, 2), (64, 1)] }, { coefficient := 2, powers := [(0, 2), (34, 1), (36, 1), (54, 1), (57, 1), (64, 1)] }, { coefficient := -1, powers := [(0, 1), (3, 1), (31, 1), (39, 1), (57, 2), (64, 1)] }, { coefficient := -1, powers := [(0, 1), (3, 1), (31, 1), (44, 1), (57, 2), (64, 1)] }, { coefficient := -2, powers := [(0, 1), (3, 1), (31, 1), (57, 1), (61, 1)] }, { coefficient := -2, powers := [(0, 1), (3, 1), (34, 1), (39, 1), (54, 1), (57, 1), (64, 1)] }, { coefficient := -2, powers := [(0, 1), (3, 1), (34, 1), (44, 1), (54, 1), (57, 1), (64, 1)] }, { coefficient := -4, powers := [(0, 1), (3, 1), (34, 1), (54, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(0, 2), (23, 1), (36, 1), (45, 1), (57, 1), (59, 1), (64, 1)] }, { coefficient := 1, powers := [(0, 1), (3, 1), (23, 1), (39, 1), (45, 1), (57, 1), (59, 1), (64, 1)] }, { coefficient := 1, powers := [(0, 1), (3, 1), (23, 1), (44, 1), (45, 1), (57, 1), (59, 1), (64, 1)] }, { coefficient := 2, powers := [(0, 1), (3, 1), (23, 1), (45, 1), (59, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(0, 2), (28, 1), (36, 1), (52, 1), (57, 1), (59, 1), (64, 1)] }, { coefficient := 1, powers := [(0, 1), (3, 1), (28, 1), (39, 1), (52, 1), (57, 1), (59, 1), (64, 1)] }, { coefficient := 1, powers := [(0, 1), (3, 1), (28, 1), (44, 1), (52, 1), (57, 1), (59, 1), (64, 1)] }, { coefficient := 2, powers := [(0, 1), (3, 1), (28, 1), (52, 1), (59, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(0, 2), (13, 1), (36, 1), (53, 1), (57, 1), (59, 1), (64, 1)] }, { coefficient := 1, powers := [(0, 1), (3, 1), (13, 1), (39, 1), (53, 1), (57, 1), (59, 1), (64, 1)] }, { coefficient := 1, powers := [(0, 1), (3, 1), (13, 1), (44, 1), (53, 1), (57, 1), (59, 1), (64, 1)] }, { coefficient := 2, powers := [(0, 1), (3, 1), (13, 1), (53, 1), (59, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(0, 2), (18, 1), (36, 1), (46, 1), (57, 1), (59, 1), (64, 1)] }, { coefficient := 1, powers := [(0, 1), (3, 1), (18, 1), (39, 1), (46, 1), (57, 1), (59, 1), (64, 1)] }, { coefficient := 1, powers := [(0, 1), (3, 1), (18, 1), (44, 1), (46, 1), (57, 1), (59, 1), (64, 1)] }, { coefficient := 2, powers := [(0, 1), (3, 1), (18, 1), (46, 1), (59, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (22, 1), (42, 1), (51, 1), (53, 1), (62, 1), (64, 1)] }, { coefficient := -1, powers := [(0, 1), (22, 1), (51, 1), (57, 1), (62, 1), (64, 1)] }, { coefficient := -1, powers := [(0, 1), (26, 1), (42, 1), (51, 2), (53, 1), (62, 1), (64, 1)] }, { coefficient := 1, powers := [(0, 1), (26, 1), (51, 2), (57, 1), (62, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (22, 1), (42, 1), (51, 1), (62, 1), (64, 1)] }, { coefficient := 1, powers := [(0, 1), (26, 1), (42, 1), (51, 2), (62, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (22, 1), (53, 1), (62, 1), (64, 1)] }, { coefficient := -1, powers := [(0, 1), (26, 1), (51, 1), (53, 1), (62, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(0, 2), (23, 1), (36, 1), (57, 2), (59, 1), (64, 1)] }, { coefficient := -2, powers := [(0, 2), (28, 1), (36, 1), (47, 1), (57, 1), (59, 1), (64, 1)] }, { coefficient := 1, powers := [(0, 1), (3, 1), (23, 1), (39, 1), (57, 2), (59, 1), (64, 1)] }, { coefficient := 1, powers := [(0, 1), (3, 1), (23, 1), (44, 1), (57, 2), (59, 1), (64, 1)] }, { coefficient := 2, powers := [(0, 1), (3, 1), (23, 1), (57, 1), (59, 1), (61, 1)] }, { coefficient := 2, powers := [(0, 1), (3, 1), (28, 1), (39, 1), (47, 1), (57, 1), (59, 1), (64, 1)] }, { coefficient := 2, powers := [(0, 1), (3, 1), (28, 1), (44, 1), (47, 1), (57, 1), (59, 1), (64, 1)] }, { coefficient := 4, powers := [(0, 1), (3, 1), (28, 1), (47, 1), (59, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (11, 1), (22, 1), (51, 1), (53, 1), (62, 1), (64, 1)] }, { coefficient := 1, powers := [(0, 1), (11, 1), (26, 1), (51, 2), (53, 1), (62, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(0, 2), (36, 1), (54, 1), (57, 1), (59, 1), (64, 1)] }, { coefficient := 1, powers := [(0, 1), (3, 1), (39, 1), (54, 1), (57, 1), (59, 1), (64, 1)] }, { coefficient := 1, powers := [(0, 1), (3, 1), (44, 1), (54, 1), (57, 1), (59, 1), (64, 1)] }, { coefficient := 2, powers := [(0, 1), (3, 1), (54, 1), (59, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(0, 2), (36, 1), (47, 1), (57, 1), (59, 1), (64, 1)] }, { coefficient := -1, powers := [(0, 1), (3, 1), (39, 1), (47, 1), (57, 1), (59, 1), (64, 1)] }, { coefficient := -1, powers := [(0, 1), (3, 1), (44, 1), (47, 1), (57, 1), (59, 1), (64, 1)] }, { coefficient := -2, powers := [(0, 1), (3, 1), (47, 1), (59, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (22, 1), (24, 1), (53, 1), (62, 1), (64, 1)] }, { coefficient := 1, powers := [(0, 1), (24, 1), (26, 1), (51, 1), (53, 1), (62, 1), (64, 1)] }, { coefficient := -1, powers := [(0, 1), (25, 1), (26, 1), (51, 1), (62, 1), (64, 1)] }, { coefficient := 1, powers := [(0, 1), (26, 1), (53, 1), (62, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (11, 1), (22, 1), (25, 1), (51, 1), (62, 1), (64, 1)] }, { coefficient := -1, powers := [(0, 1), (11, 1), (22, 1), (53, 1), (62, 1), (64, 1)] }, { coefficient := -1, powers := [(0, 1), (11, 1), (25, 1), (26, 1), (51, 2), (62, 1), (64, 1)] }, { coefficient := 1, powers := [(0, 1), (11, 1), (26, 1), (51, 1), (53, 1), (62, 1), (64, 1)] }, { coefficient := -1, powers := [(0, 1), (16, 1), (22, 1), (25, 1), (51, 1), (62, 1), (64, 1)] }, { coefficient := 1, powers := [(0, 1), (16, 1), (25, 1), (26, 1), (51, 2), (62, 1), (64, 1)] }, { coefficient := 1, powers := [(0, 1), (25, 1), (39, 1), (51, 1), (57, 1), (64, 2)] }, { coefficient := 1, powers := [(0, 1), (25, 1), (39, 1), (51, 1), (64, 1)] }, { coefficient := 1, powers := [(0, 1), (25, 1), (44, 1), (51, 1), (57, 1), (64, 2)] }, { coefficient := 2, powers := [(0, 1), (25, 1), (51, 1), (61, 1), (64, 1)] }, { coefficient := -1, powers := [(0, 1), (39, 1), (53, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (22, 1), (51, 1), (62, 1), (64, 1)] }, { coefficient := 1, powers := [(0, 1), (26, 1), (51, 2), (62, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (22, 1), (25, 1), (51, 1), (62, 1), (64, 1)] }, { coefficient := 1, powers := [(0, 1), (22, 1), (53, 1), (62, 1), (64, 1)] }, { coefficient := 1, powers := [(0, 1), (25, 1), (26, 1), (51, 2), (62, 1), (64, 1)] }, { coefficient := -1, powers := [(0, 1), (26, 1), (51, 1), (53, 1), (62, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (11, 1), (22, 1), (42, 1), (51, 1), (62, 1), (64, 1)] }, { coefficient := -1, powers := [(0, 1), (11, 1), (26, 1), (42, 1), (51, 2), (62, 1), (64, 1)] }, { coefficient := -1, powers := [(0, 1), (16, 1), (22, 1), (42, 1), (51, 1), (62, 1), (64, 1)] }, { coefficient := 1, powers := [(0, 1), (16, 1), (26, 1), (42, 1), (51, 2), (62, 1), (64, 1)] }, { coefficient := 1, powers := [(0, 1), (39, 1), (42, 1), (51, 1), (57, 1), (64, 2)] }, { coefficient := 1, powers := [(0, 1), (39, 1), (42, 1), (51, 1), (64, 1)] }, { coefficient := 1, powers := [(0, 1), (42, 1), (44, 1), (51, 1), (57, 1), (64, 2)] }, { coefficient := 2, powers := [(0, 1), (42, 1), (51, 1), (61, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (25, 1), (51, 1), (62, 1), (64, 1)] }, { coefficient := -1, powers := [(0, 1), (53, 1), (62, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(0, 2), (28, 1), (36, 1), (57, 1), (59, 1), (64, 1)] }, { coefficient := -1, powers := [(0, 1), (3, 1), (28, 1), (39, 1), (57, 1), (59, 1), (64, 1)] }, { coefficient := -1, powers := [(0, 1), (3, 1), (28, 1), (44, 1), (57, 1), (59, 1), (64, 1)] }, { coefficient := -2, powers := [(0, 1), (3, 1), (28, 1), (59, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(0, 2), (23, 1), (36, 1), (57, 1), (59, 1), (64, 1)] }, { coefficient := -1, powers := [(0, 1), (3, 1), (23, 1), (39, 1), (57, 1), (59, 1), (64, 1)] }, { coefficient := -1, powers := [(0, 1), (3, 1), (23, 1), (44, 1), (57, 1), (59, 1), (64, 1)] }, { coefficient := -2, powers := [(0, 1), (3, 1), (23, 1), (59, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(0, 2), (18, 1), (36, 1), (57, 1), (59, 1), (64, 1)] }, { coefficient := -1, powers := [(0, 1), (3, 1), (18, 1), (39, 1), (57, 1), (59, 1), (64, 1)] }, { coefficient := -1, powers := [(0, 1), (3, 1), (18, 1), (44, 1), (57, 1), (59, 1), (64, 1)] }, { coefficient := -2, powers := [(0, 1), (3, 1), (18, 1), (59, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (11, 1), (22, 1), (51, 1), (62, 1), (64, 1)] }, { coefficient := -1, powers := [(0, 1), (11, 1), (26, 1), (51, 2), (62, 1), (64, 1)] }, { coefficient := 1, powers := [(0, 1), (16, 1), (22, 1), (51, 1), (62, 1), (64, 1)] }, { coefficient := -1, powers := [(0, 1), (16, 1), (26, 1), (51, 2), (62, 1), (64, 1)] }, { coefficient := -1, powers := [(0, 1), (39, 1), (51, 1), (57, 1), (64, 2)] }, { coefficient := -1, powers := [(0, 1), (44, 1), (51, 1), (57, 1), (64, 2)] }, { coefficient := -2, powers := [(0, 1), (51, 1), (61, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (39, 1), (53, 1), (63, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (22, 1), (24, 1), (51, 1), (62, 1), (64, 1)] }, { coefficient := -1, powers := [(0, 1), (24, 1), (26, 1), (51, 2), (62, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(0, 2), (13, 1), (36, 1), (57, 1), (59, 1), (64, 1)] }, { coefficient := -1, powers := [(0, 1), (3, 1), (13, 1), (39, 1), (57, 1), (59, 1), (64, 1)] }, { coefficient := -1, powers := [(0, 1), (3, 1), (13, 1), (44, 1), (57, 1), (59, 1), (64, 1)] }, { coefficient := -2, powers := [(0, 1), (3, 1), (13, 1), (59, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (11, 1), (22, 1), (25, 1), (42, 1), (51, 1), (62, 1), (64, 1)] }, { coefficient := 1, powers := [(0, 1), (11, 1), (25, 1), (26, 1), (42, 1), (51, 2), (62, 1), (64, 1)] }, { coefficient := 1, powers := [(0, 1), (16, 1), (22, 1), (25, 1), (42, 1), (51, 1), (62, 1), (64, 1)] }, { coefficient := -1, powers := [(0, 1), (16, 1), (25, 1), (26, 1), (42, 1), (51, 2), (62, 1), (64, 1)] }, { coefficient := -1, powers := [(0, 1), (25, 1), (39, 1), (42, 1), (51, 1), (57, 1), (64, 2)] }, { coefficient := -1, powers := [(0, 1), (25, 1), (39, 1), (42, 1), (51, 1), (64, 1)] }, { coefficient := -1, powers := [(0, 1), (25, 1), (42, 1), (44, 1), (51, 1), (57, 1), (64, 2)] }, { coefficient := -2, powers := [(0, 1), (25, 1), (42, 1), (51, 1), (61, 1), (64, 1)] }, { coefficient := 1, powers := [(0, 1), (39, 1), (57, 1), (64, 1)] }, { coefficient := 1, powers := [(0, 1), (44, 1), (57, 1), (64, 1)] }, { coefficient := 2, powers := [(0, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (39, 1), (51, 1), (63, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(0, 2), (57, 1), (61, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(0, 2), (36, 1), (57, 1), (59, 1), (64, 1)] }, { coefficient := 1, powers := [(0, 1), (3, 1), (39, 1), (57, 1), (59, 1), (64, 1)] }, { coefficient := 1, powers := [(0, 1), (3, 1), (44, 1), (57, 1), (59, 1), (64, 1)] }, { coefficient := 2, powers := [(0, 1), (3, 1), (59, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(0, 2), (36, 1), (57, 1), (59, 1), (64, 1)] }, { coefficient := 1, powers := [(0, 2), (44, 1), (51, 1), (57, 1), (64, 1)] }, { coefficient := 1, powers := [(0, 1), (39, 1), (57, 1), (64, 1)] }, { coefficient := 1, powers := [(0, 1), (44, 1), (57, 1), (64, 1)] }, { coefficient := 1, powers := [(0, 1), (51, 1), (57, 1), (64, 1)] }, { coefficient := -2, powers := [(0, 1), (51, 1)] }, { coefficient := -2, powers := [] }],
  [{ coefficient := -1, powers := [(0, 1), (25, 1), (45, 1), (51, 1), (64, 1)] }, { coefficient := 1, powers := [(0, 1), (45, 1), (53, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(0, 2), (36, 1), (37, 1), (57, 1), (59, 1), (60, 1), (64, 1)] }, { coefficient := 1, powers := [(0, 2), (36, 1), (40, 1), (57, 2), (59, 1), (64, 1)] }, { coefficient := 1, powers := [(0, 2), (36, 1), (47, 1), (54, 1), (57, 1), (59, 1), (64, 1)] }, { coefficient := -1, powers := [(0, 1), (3, 1), (37, 1), (39, 1), (57, 1), (59, 1), (60, 1), (64, 1)] }, { coefficient := -1, powers := [(0, 1), (3, 1), (37, 1), (44, 1), (57, 1), (59, 1), (60, 1), (64, 1)] }, { coefficient := -2, powers := [(0, 1), (3, 1), (37, 1), (59, 1), (60, 1), (61, 1)] }, { coefficient := -1, powers := [(0, 1), (3, 1), (39, 1), (40, 1), (57, 2), (59, 1), (64, 1)] }, { coefficient := -1, powers := [(0, 1), (3, 1), (39, 1), (47, 1), (54, 1), (57, 1), (59, 1), (64, 1)] }, { coefficient := -1, powers := [(0, 1), (3, 1), (40, 1), (44, 1), (57, 2), (59, 1), (64, 1)] }, { coefficient := -2, powers := [(0, 1), (3, 1), (40, 1), (57, 1), (59, 1), (61, 1)] }, { coefficient := -1, powers := [(0, 1), (3, 1), (44, 1), (47, 1), (54, 1), (57, 1), (59, 1), (64, 1)] }, { coefficient := -2, powers := [(0, 1), (3, 1), (47, 1), (54, 1), (59, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(0, 2), (39, 1), (51, 1), (57, 1), (64, 1)] }, { coefficient := 1, powers := [(0, 1), (25, 1), (39, 1), (42, 1), (51, 1), (64, 1)] }, { coefficient := 1, powers := [(0, 1), (25, 1), (45, 1), (51, 1), (64, 1)] }, { coefficient := -1, powers := [(0, 1), (39, 1), (42, 1), (53, 1), (64, 1)] }, { coefficient := -1, powers := [(0, 1), (45, 1), (53, 1), (64, 1)] }, { coefficient := 1, powers := [(0, 1), (51, 1), (57, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(0, 2), (8, 1), (34, 1), (36, 1), (57, 1), (59, 1), (64, 1)] }, { coefficient := -1, powers := [(0, 2), (18, 1), (28, 1), (36, 1), (57, 1), (59, 1), (64, 1)] }, { coefficient := -1, powers := [(0, 1), (3, 1), (8, 1), (34, 1), (39, 1), (57, 1), (59, 1), (64, 1)] }, { coefficient := -1, powers := [(0, 1), (3, 1), (8, 1), (34, 1), (44, 1), (57, 1), (59, 1), (64, 1)] }, { coefficient := -2, powers := [(0, 1), (3, 1), (8, 1), (34, 1), (59, 1), (61, 1)] }, { coefficient := 1, powers := [(0, 1), (3, 1), (18, 1), (28, 1), (39, 1), (57, 1), (59, 1), (64, 1)] }, { coefficient := 1, powers := [(0, 1), (3, 1), (18, 1), (28, 1), (44, 1), (57, 1), (59, 1), (64, 1)] }, { coefficient := 2, powers := [(0, 1), (3, 1), (18, 1), (28, 1), (59, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(0, 3), (39, 1), (57, 1), (61, 1), (64, 1)] }, { coefficient := 1, powers := [(0, 2), (13, 1), (19, 1), (23, 1), (36, 1), (57, 2), (59, 1), (64, 1)] }, { coefficient := 2, powers := [(0, 2), (13, 1), (19, 1), (28, 1), (36, 1), (47, 1), (57, 1), (59, 1), (64, 1)] }, { coefficient := 1, powers := [(0, 2), (57, 1), (61, 1), (64, 1)] }, { coefficient := -1, powers := [(0, 1), (3, 1), (13, 1), (19, 1), (23, 1), (39, 1), (57, 2), (59, 1), (64, 1)] }, { coefficient := -1, powers := [(0, 1), (3, 1), (13, 1), (19, 1), (23, 1), (44, 1), (57, 2), (59, 1), (64, 1)] }, { coefficient := -2, powers := [(0, 1), (3, 1), (13, 1), (19, 1), (23, 1), (57, 1), (59, 1), (61, 1)] }, { coefficient := -2, powers := [(0, 1), (3, 1), (13, 1), (19, 1), (28, 1), (39, 1), (47, 1), (57, 1), (59, 1), (64, 1)] }, { coefficient := -2, powers := [(0, 1), (3, 1), (13, 1), (19, 1), (28, 1), (44, 1), (47, 1), (57, 1), (59, 1), (64, 1)] }, { coefficient := -4, powers := [(0, 1), (3, 1), (13, 1), (19, 1), (28, 1), (47, 1), (59, 1), (61, 1)] }, { coefficient := 1, powers := [(0, 1), (11, 1), (19, 1), (22, 1), (25, 1), (42, 1), (51, 1), (62, 1), (64, 1)] }, { coefficient := -1, powers := [(0, 1), (11, 1), (19, 1), (25, 1), (26, 1), (42, 1), (51, 2), (62, 1), (64, 1)] }, { coefficient := -1, powers := [(0, 1), (16, 1), (19, 1), (22, 1), (25, 1), (42, 1), (51, 1), (62, 1), (64, 1)] }, { coefficient := 1, powers := [(0, 1), (16, 1), (19, 1), (25, 1), (26, 1), (42, 1), (51, 2), (62, 1), (64, 1)] }, { coefficient := 1, powers := [(0, 1), (19, 1), (25, 1), (39, 1), (42, 1), (51, 1), (57, 1), (64, 2)] }, { coefficient := 1, powers := [(0, 1), (19, 1), (25, 1), (39, 1), (42, 1), (51, 1), (64, 1)] }, { coefficient := 1, powers := [(0, 1), (19, 1), (25, 1), (42, 1), (44, 1), (51, 1), (57, 1), (64, 2)] }, { coefficient := 2, powers := [(0, 1), (19, 1), (25, 1), (42, 1), (51, 1), (61, 1), (64, 1)] }, { coefficient := -1, powers := [(0, 1), (19, 1), (39, 1), (57, 1), (64, 1)] }, { coefficient := -1, powers := [(0, 1), (19, 1), (44, 1), (57, 1), (64, 1)] }, { coefficient := -2, powers := [(0, 1), (19, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (19, 1), (39, 1), (51, 1), (57, 1), (64, 1)] }, { coefficient := 1, powers := [(0, 1), (19, 1), (44, 1), (51, 1), (57, 1), (64, 1)] }, { coefficient := 2, powers := [(0, 1), (19, 1), (51, 1), (61, 1)] }, { coefficient := 2, powers := [(0, 1), (51, 1)] }]
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
    ¬ ∀ index : Fin 36,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((2 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (2 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (2 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component65.SelectedLeafB6_2_1.selectedHasNoCommonZero

end Krenn.Component65.SelectedLeafB6_2_1
