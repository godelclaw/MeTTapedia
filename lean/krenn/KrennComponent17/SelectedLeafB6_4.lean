import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component17.SelectedLeafB6_4

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "9278f153fca9ba0d00029d6e91f5f7abe594ac8291e4f00be0494e17a764b07a"
def certificateSHA256 : String := "49c4ff802fabb7b33d859f91165b88e8d6a8052855db19beba4f7a11372fee2e"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 32 → Fin 608 := ![
  1,
  2,
  3,
  4,
  6,
  7,
  9,
  18,
  32,
  127,
  208,
  212,
  311,
  323,
  325,
  372,
  378,
  434,
  438,
  440,
  441,
  445,
  465,
  500,
  538,
  541,
  549,
  601,
  603,
  604,
  606,
  607
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 32 → SparsePoly (Fin 62) := ![
  [{ coefficient := 1, powers := [(1, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (34, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (31, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (34, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (47, 1)] }, { coefficient := 1, powers := [(18, 1), (20, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(31, 1), (38, 1)] }, { coefficient := 1, powers := [(34, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (58, 1)] }, { coefficient := 1, powers := [(13, 1), (47, 1)] }, { coefficient := 1, powers := [(18, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (45, 1)] }, { coefficient := 1, powers := [(18, 1), (40, 1)] }, { coefficient := 1, powers := [(18, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (52, 1)] }, { coefficient := 1, powers := [(29, 1), (41, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (31, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1), (47, 1)] }, { coefficient := 1, powers := [(18, 1), (31, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (23, 1), (57, 1)] }, { coefficient := 1, powers := [(23, 1)] }, { coefficient := 1, powers := [(27, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (52, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1)] }, { coefficient := 1, powers := [(13, 1), (29, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (57, 1)] }, { coefficient := 1, powers := [(17, 1), (20, 1), (50, 1)] }, { coefficient := 1, powers := [(17, 1), (20, 1), (54, 1)] }, { coefficient := 1, powers := [(17, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (57, 1)] }, { coefficient := 1, powers := [(17, 1), (25, 1), (40, 1)] }, { coefficient := 1, powers := [(17, 1), (25, 1), (44, 1)] }, { coefficient := 1, powers := [(17, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (58, 1)] }, { coefficient := 1, powers := [(13, 1), (25, 1), (45, 1)] }, { coefficient := 1, powers := [(13, 1), (55, 1)] }, { coefficient := 1, powers := [(18, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (40, 1)] }, { coefficient := 1, powers := [(17, 1), (44, 1)] }, { coefficient := 1, powers := [(17, 1), (50, 1)] }, { coefficient := 1, powers := [(17, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (36, 1), (57, 1)] }, { coefficient := 1, powers := [(1, 1)] }, { coefficient := 1, powers := [(11, 1), (34, 1), (36, 1)] }, { coefficient := 1, powers := [(15, 1), (31, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (25, 1), (57, 1)] }, { coefficient := 1, powers := [(8, 1), (20, 1), (57, 1)] }, { coefficient := 1, powers := [(17, 1), (20, 1), (51, 1)] }, { coefficient := 1, powers := [(17, 1), (25, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (25, 1), (45, 1)] }, { coefficient := 1, powers := [(17, 1), (55, 1)] }, { coefficient := 1, powers := [(18, 1), (25, 1), (40, 1)] }, { coefficient := 1, powers := [(18, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (43, 1), (51, 1)] }, { coefficient := 1, powers := [(23, 1), (55, 1)] }, { coefficient := 1, powers := [(29, 1), (47, 1)] }, { coefficient := 1, powers := [(35, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1)] }, { coefficient := 1, powers := [(6, 1), (57, 1)] }, { coefficient := 1, powers := [(24, 1), (40, 1)] }, { coefficient := 1, powers := [(24, 1), (44, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (41, 1), (55, 1)] }, { coefficient := 1, powers := [(2, 1), (47, 1), (52, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (52, 1)] }, { coefficient := 1, powers := [(8, 1), (23, 1), (58, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (47, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(13, 1), (23, 1), (55, 1)] }, { coefficient := 1, powers := [(13, 1), (29, 1), (47, 1)] }, { coefficient := 1, powers := [(13, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (52, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (41, 1)] }, { coefficient := 1, powers := [(18, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1), (60, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(40, 1)] }],
  [{ coefficient := 1, powers := [(41, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 32 → SparsePoly (Fin 62) := ![
  [{ coefficient := -1, powers := [(13, 1), (27, 1), (36, 1), (55, 1), (57, 1), (60, 1)] }, { coefficient := 1, powers := [(17, 1), (32, 1), (36, 1), (55, 1), (60, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (13, 1), (29, 1), (36, 1), (44, 1), (57, 1), (60, 1)] }, { coefficient := -2, powers := [(6, 1), (13, 1), (29, 1), (36, 1), (57, 2), (60, 1)] }, { coefficient := 2, powers := [(11, 1), (13, 1), (29, 1), (34, 1), (36, 1), (60, 2)] }, { coefficient := 2, powers := [(13, 1), (15, 1), (29, 1), (31, 1), (36, 1), (60, 2)] }, { coefficient := -2, powers := [(13, 1), (24, 1), (29, 1), (36, 1), (44, 1), (57, 1), (60, 1)] }, { coefficient := 1, powers := [(17, 1), (25, 1), (32, 1), (36, 1), (44, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (13, 1), (23, 1), (36, 1), (43, 1), (44, 1), (57, 1), (60, 1)] }, { coefficient := -1, powers := [(6, 1), (13, 1), (23, 1), (36, 1), (43, 1), (57, 2), (60, 1)] }, { coefficient := 1, powers := [(11, 1), (13, 1), (23, 1), (34, 1), (36, 1), (43, 1), (60, 2)] }, { coefficient := 1, powers := [(13, 1), (15, 1), (23, 1), (31, 1), (36, 1), (43, 1), (60, 2)] }, { coefficient := -1, powers := [(13, 1), (23, 1), (24, 1), (36, 1), (43, 1), (44, 1), (57, 1), (60, 1)] }, { coefficient := 1, powers := [(18, 1), (20, 1), (32, 1), (36, 1), (44, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (5, 1), (35, 1), (36, 1), (44, 1), (57, 1), (60, 1)] }, { coefficient := -1, powers := [(0, 1), (18, 1), (23, 1), (36, 1), (44, 1), (57, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (6, 1), (35, 1), (36, 1), (57, 2), (60, 1)] }, { coefficient := -1, powers := [(5, 1), (11, 1), (34, 1), (35, 1), (36, 1), (60, 2)] }, { coefficient := -1, powers := [(5, 1), (15, 1), (31, 1), (35, 1), (36, 1), (60, 2)] }, { coefficient := 1, powers := [(5, 1), (24, 1), (35, 1), (36, 1), (44, 1), (57, 1), (60, 1)] }, { coefficient := 1, powers := [(11, 1), (18, 1), (23, 1), (34, 1), (36, 1), (60, 2)] }, { coefficient := 1, powers := [(15, 1), (18, 1), (23, 1), (34, 1), (36, 1), (60, 2)] }, { coefficient := -1, powers := [(18, 1), (23, 1), (24, 1), (36, 1), (44, 1), (57, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(11, 1), (32, 1), (36, 1), (55, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (23, 1), (36, 1), (57, 2)] }],
  [{ coefficient := -1, powers := [(15, 1), (23, 1), (36, 1), (58, 1), (60, 1)] }, { coefficient := 1, powers := [(15, 1), (32, 1), (36, 1), (47, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (23, 1), (25, 1), (36, 1), (44, 1), (57, 1)] }, { coefficient := 1, powers := [(11, 1), (23, 1), (25, 1), (34, 1), (36, 1), (60, 1)] }, { coefficient := -1, powers := [(23, 1), (24, 1), (25, 1), (36, 1), (44, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (17, 1), (36, 1), (44, 1), (47, 1), (57, 1)] }, { coefficient := -1, powers := [(6, 1), (17, 1), (36, 1), (47, 1), (57, 2)] }, { coefficient := 1, powers := [(11, 1), (17, 1), (34, 1), (36, 1), (47, 1), (60, 1)] }, { coefficient := 1, powers := [(15, 1), (17, 1), (31, 1), (36, 1), (47, 1), (60, 1)] }, { coefficient := -1, powers := [(17, 1), (24, 1), (36, 1), (44, 1), (47, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (23, 1), (55, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(25, 1), (32, 1), (36, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(15, 1), (18, 1), (32, 1), (36, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (29, 1), (36, 1), (44, 1), (57, 1)] }, { coefficient := 1, powers := [(6, 1), (29, 1), (36, 1), (57, 2)] }, { coefficient := -1, powers := [(11, 1), (29, 1), (34, 1), (36, 1), (60, 1)] }, { coefficient := -1, powers := [(15, 1), (29, 1), (31, 1), (36, 1), (60, 1)] }, { coefficient := 1, powers := [(24, 1), (29, 1), (36, 1), (44, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (25, 1), (32, 1), (36, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (18, 1), (36, 1), (44, 1), (57, 1)] }, { coefficient := 1, powers := [(6, 1), (18, 1), (36, 1), (57, 2)] }, { coefficient := -1, powers := [(11, 1), (18, 1), (34, 1), (36, 1), (60, 1)] }, { coefficient := -1, powers := [(15, 1), (18, 1), (31, 1), (36, 1), (60, 1)] }, { coefficient := -1, powers := [(15, 1), (18, 1), (34, 1), (36, 1), (60, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (36, 1), (44, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [(15, 1), (32, 1), (36, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (36, 1), (55, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (36, 1), (44, 1), (47, 1), (57, 1)] }, { coefficient := 1, powers := [(6, 1), (36, 1), (47, 1), (57, 2)] }, { coefficient := -1, powers := [(11, 1), (34, 1), (36, 1), (47, 1), (60, 1)] }, { coefficient := -1, powers := [(15, 1), (31, 1), (36, 1), (47, 1), (60, 1)] }, { coefficient := 1, powers := [(24, 1), (36, 1), (44, 1), (47, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (32, 1), (36, 1), (45, 1)] }, { coefficient := -1, powers := [(32, 1), (36, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (32, 1), (36, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (23, 1), (36, 1), (44, 1), (57, 1)] }, { coefficient := -1, powers := [(11, 1), (23, 1), (34, 1), (36, 1), (60, 1)] }, { coefficient := 1, powers := [(23, 1), (24, 1), (36, 1), (44, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [(20, 1), (25, 1), (32, 1), (36, 1), (45, 1)] }, { coefficient := 1, powers := [(20, 1), (32, 1), (36, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(60, 1)] }],
  [{ coefficient := -1, powers := [(32, 1), (36, 1), (45, 1)] }],
  [{ coefficient := -1, powers := [(20, 1), (32, 1), (36, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (13, 1), (36, 1), (44, 1), (57, 1)] }, { coefficient := 1, powers := [(6, 1), (13, 1), (36, 1), (57, 2)] }, { coefficient := -1, powers := [(11, 1), (13, 1), (34, 1), (36, 1), (60, 1)] }, { coefficient := -1, powers := [(13, 1), (15, 1), (31, 1), (36, 1), (60, 1)] }, { coefficient := 1, powers := [(13, 1), (24, 1), (36, 1), (44, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (32, 1), (36, 1), (55, 1), (57, 1)] }, { coefficient := -1, powers := [(13, 1), (23, 1), (36, 1), (55, 1), (57, 1)] }, { coefficient := -1, powers := [(36, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (36, 1), (44, 1), (57, 1)] }, { coefficient := -1, powers := [(6, 1), (36, 1), (57, 2)] }, { coefficient := 1, powers := [(11, 1), (34, 1), (36, 1), (60, 1)] }, { coefficient := 1, powers := [(15, 1), (31, 1), (36, 1), (60, 1)] }, { coefficient := -1, powers := [(24, 1), (36, 1), (44, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (5, 1), (35, 1), (36, 1), (44, 1), (52, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (13, 1), (23, 1), (36, 1), (43, 1), (44, 1), (51, 1), (57, 1)] }, { coefficient := 2, powers := [(0, 1), (13, 1), (29, 1), (36, 1), (44, 1), (47, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (18, 1), (23, 1), (36, 1), (44, 1), (52, 1), (57, 1)] }, { coefficient := -1, powers := [(5, 1), (6, 1), (35, 1), (36, 1), (52, 1), (57, 2)] }, { coefficient := 1, powers := [(5, 1), (11, 1), (34, 1), (35, 1), (36, 1), (52, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (15, 1), (31, 1), (35, 1), (36, 1), (52, 1), (60, 1)] }, { coefficient := -1, powers := [(5, 1), (24, 1), (35, 1), (36, 1), (44, 1), (52, 1), (57, 1)] }, { coefficient := 1, powers := [(6, 1), (13, 1), (23, 1), (36, 1), (43, 1), (51, 1), (57, 2)] }, { coefficient := 2, powers := [(6, 1), (13, 1), (29, 1), (36, 1), (47, 1), (57, 2)] }, { coefficient := -1, powers := [(11, 1), (13, 1), (23, 1), (34, 1), (36, 1), (43, 1), (51, 1), (60, 1)] }, { coefficient := -2, powers := [(11, 1), (13, 1), (29, 1), (34, 1), (36, 1), (47, 1), (60, 1)] }, { coefficient := -1, powers := [(11, 1), (18, 1), (23, 1), (34, 1), (36, 1), (52, 1), (60, 1)] }, { coefficient := -1, powers := [(13, 1), (15, 1), (23, 1), (31, 1), (36, 1), (43, 1), (51, 1), (60, 1)] }, { coefficient := -2, powers := [(13, 1), (15, 1), (29, 1), (31, 1), (36, 1), (47, 1), (60, 1)] }, { coefficient := 1, powers := [(13, 1), (23, 1), (24, 1), (36, 1), (43, 1), (44, 1), (51, 1), (57, 1)] }, { coefficient := 2, powers := [(13, 1), (24, 1), (29, 1), (36, 1), (44, 1), (47, 1), (57, 1)] }, { coefficient := 1, powers := [(13, 1), (27, 1), (36, 1), (46, 1), (55, 1), (57, 1)] }, { coefficient := -1, powers := [(15, 1), (18, 1), (23, 1), (34, 1), (36, 1), (52, 1), (60, 1)] }, { coefficient := -1, powers := [(17, 1), (25, 1), (32, 1), (36, 1), (44, 1), (47, 1)] }, { coefficient := -1, powers := [(17, 1), (32, 1), (36, 1), (46, 1), (55, 1)] }, { coefficient := -1, powers := [(18, 1), (20, 1), (32, 1), (36, 1), (44, 1), (51, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (24, 1), (36, 1), (44, 1), (52, 1), (57, 1)] }, { coefficient := -1, powers := [(36, 1), (57, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (36, 1), (38, 1), (44, 1), (57, 1), (58, 1)] }, { coefficient := 1, powers := [(6, 1), (36, 1), (38, 1), (57, 2), (58, 1)] }, { coefficient := -1, powers := [(11, 1), (34, 1), (36, 1), (38, 1), (58, 1), (60, 1)] }, { coefficient := -1, powers := [(15, 1), (31, 1), (36, 1), (38, 1), (58, 1), (60, 1)] }, { coefficient := 1, powers := [(24, 1), (36, 1), (38, 1), (44, 1), (57, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (24, 1), (32, 1), (36, 1), (55, 1), (57, 1)] }, { coefficient := 1, powers := [(13, 1), (23, 1), (24, 1), (36, 1), (55, 1), (57, 1)] }, { coefficient := -1, powers := [(17, 1), (20, 1), (32, 1), (36, 1), (55, 1)] }, { coefficient := 1, powers := [(24, 1), (36, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (2, 1), (36, 1), (44, 1), (55, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (8, 1), (35, 1), (36, 1), (44, 1), (57, 1)] }, { coefficient := -1, powers := [(0, 1), (18, 1), (29, 1), (36, 1), (44, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (6, 1), (36, 1), (55, 1), (57, 2)] }, { coefficient := -1, powers := [(2, 1), (11, 1), (34, 1), (36, 1), (55, 1), (60, 1)] }, { coefficient := -1, powers := [(2, 1), (15, 1), (31, 1), (36, 1), (55, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (24, 1), (36, 1), (44, 1), (55, 1), (57, 1)] }, { coefficient := 1, powers := [(6, 1), (8, 1), (35, 1), (36, 1), (57, 2)] }, { coefficient := -1, powers := [(6, 1), (18, 1), (29, 1), (36, 1), (57, 2)] }, { coefficient := -1, powers := [(8, 1), (11, 1), (34, 1), (35, 1), (36, 1), (60, 1)] }, { coefficient := -1, powers := [(8, 1), (15, 1), (31, 1), (35, 1), (36, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (35, 1), (36, 1), (44, 1), (57, 1)] }, { coefficient := 1, powers := [(11, 1), (18, 1), (29, 1), (34, 1), (36, 1), (60, 1)] }, { coefficient := 1, powers := [(15, 1), (18, 1), (29, 1), (31, 1), (36, 1), (60, 1)] }, { coefficient := 1, powers := [(15, 1), (18, 1), (29, 1), (34, 1), (36, 1), (60, 1)] }, { coefficient := -1, powers := [(18, 1), (24, 1), (29, 1), (36, 1), (44, 1), (57, 1)] }]
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
    (values : Fin 62 → R) :
    ¬ ∀ index : Fin 32,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component17.SelectedLeafB6_4.selectedHasNoCommonZero

end Krenn.Component17.SelectedLeafB6_4
