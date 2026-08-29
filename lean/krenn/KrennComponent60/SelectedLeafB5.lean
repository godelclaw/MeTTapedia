import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component60.SelectedLeafB5

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "0e6dc4e3821f6a22e82a8319871201830a36145079869a8f82ed4573083c2385"
def certificateSHA256 : String := "99e2b26dc7608d72ff9c6f849fda02bc7ffd66ef33b43f5f8ac602dc0be9ade5"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 62 → Fin 659 := ![
  1,
  2,
  4,
  5,
  8,
  22,
  25,
  26,
  27,
  43,
  143,
  145,
  147,
  163,
  172,
  177,
  178,
  179,
  184,
  198,
  292,
  293,
  295,
  310,
  312,
  315,
  316,
  329,
  354,
  364,
  404,
  431,
  433,
  434,
  435,
  442,
  443,
  448,
  453,
  459,
  464,
  467,
  470,
  489,
  517,
  556,
  578,
  579,
  592,
  593,
  604,
  605,
  606,
  614,
  621,
  643,
  644,
  654,
  655,
  656,
  657,
  658
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 62 → SparsePoly (Fin 63) := ![
  [{ coefficient := 1, powers := [(2, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (32, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(32, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(35, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (32, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (47, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (53, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (32, 1)] }, { coefficient := 1, powers := [(32, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (43, 1)] }, { coefficient := -1, powers := [(16, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (20, 1)] }, { coefficient := 1, powers := [(18, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (51, 1)] }, { coefficient := 1, powers := [(24, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (53, 1)] }, { coefficient := 1, powers := [(29, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (40, 1)] }, { coefficient := 1, powers := [(29, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (36, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (24, 1), (59, 1)] }, { coefficient := 1, powers := [(24, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1)] }, { coefficient := 1, powers := [(20, 1), (43, 1)] }, { coefficient := 1, powers := [(25, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (48, 1)] }, { coefficient := 1, powers := [(21, 1), (43, 1)] }, { coefficient := 1, powers := [(25, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (54, 1)] }, { coefficient := 1, powers := [(20, 1), (54, 1)] }, { coefficient := 1, powers := [(26, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (46, 1)] }, { coefficient := 1, powers := [(19, 1), (40, 1)] }, { coefficient := 1, powers := [(19, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1), (51, 1)] }, { coefficient := 1, powers := [(20, 1), (43, 1), (51, 1)] }, { coefficient := 1, powers := [(43, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1), (54, 1)] }, { coefficient := 1, powers := [(26, 1), (45, 1), (50, 1)] }, { coefficient := 1, powers := [(54, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (48, 1), (51, 1)] }, { coefficient := 1, powers := [(21, 1), (43, 1), (51, 1)] }, { coefficient := 1, powers := [(48, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (37, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (40, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (45, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (32, 1), (56, 1)] }, { coefficient := 1, powers := [(7, 1), (32, 1), (45, 1)] }, { coefficient := 1, powers := [(15, 1), (32, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (20, 1), (60, 1)] }, { coefficient := 1, powers := [(11, 1), (43, 1)] }, { coefficient := 1, powers := [(16, 1), (20, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (25, 1), (46, 1)] }, { coefficient := 1, powers := [(19, 1), (25, 1), (40, 1)] }, { coefficient := 1, powers := [(19, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (60, 1)] }, { coefficient := 1, powers := [(11, 1), (46, 1)] }, { coefficient := 1, powers := [(16, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (59, 1)] }, { coefficient := 1, powers := [(18, 1), (21, 1), (51, 1)] }, { coefficient := 1, powers := [(18, 1), (21, 1), (56, 1)] }, { coefficient := 1, powers := [(18, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (60, 1)] }, { coefficient := 1, powers := [(12, 1), (48, 1)] }, { coefficient := 1, powers := [(19, 1), (21, 1), (52, 1)] }, { coefficient := 1, powers := [(19, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (59, 1)] }, { coefficient := 1, powers := [(18, 1), (26, 1), (40, 1)] }, { coefficient := 1, powers := [(18, 1), (26, 1), (45, 1)] }, { coefficient := 1, powers := [(18, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (40, 1)] }, { coefficient := 1, powers := [(18, 1), (45, 1)] }, { coefficient := 1, powers := [(18, 1), (51, 1)] }, { coefficient := 1, powers := [(18, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (54, 1)] }, { coefficient := 1, powers := [(29, 1), (41, 1)] }, { coefficient := 1, powers := [(29, 1), (47, 1), (50, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (38, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (47, 1), (53, 1)] }, { coefficient := 1, powers := [(21, 1), (53, 1)] }, { coefficient := 1, powers := [(26, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1), (52, 1)] }, { coefficient := 1, powers := [(3, 1), (60, 1)] }, { coefficient := 1, powers := [(20, 1), (43, 1), (52, 1)] }, { coefficient := 1, powers := [(43, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1), (52, 1)] }, { coefficient := 1, powers := [(45, 1), (50, 1)] }, { coefficient := 1, powers := [(50, 1), (56, 1)] }, { coefficient := 1, powers := [(52, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1), (54, 1)] }, { coefficient := 1, powers := [(26, 1), (46, 1), (50, 1)] }, { coefficient := 1, powers := [(43, 1), (54, 1)] }, { coefficient := 1, powers := [(50, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1), (51, 1)] }, { coefficient := 1, powers := [(21, 1), (51, 1)] }, { coefficient := 1, powers := [(21, 1), (56, 1)] }, { coefficient := 1, powers := [(47, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (48, 1), (52, 1)] }, { coefficient := 1, powers := [(21, 1), (43, 1), (52, 1)] }, { coefficient := 1, powers := [(41, 1), (43, 1)] }, { coefficient := 1, powers := [(48, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (37, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(12, 1), (35, 1), (37, 1)] }, { coefficient := 1, powers := [(19, 1), (32, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (24, 1), (60, 1)] }, { coefficient := 1, powers := [(6, 1), (32, 1), (48, 1)] }, { coefficient := 1, powers := [(6, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(24, 1), (43, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (43, 1), (53, 1)] }, { coefficient := 1, powers := [(24, 1), (57, 1)] }, { coefficient := 1, powers := [(29, 1), (48, 1)] }, { coefficient := 1, powers := [(35, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1)] }, { coefficient := 1, powers := [(6, 1), (59, 1)] }, { coefficient := 1, powers := [(25, 1), (40, 1)] }, { coefficient := 1, powers := [(25, 1), (45, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (51, 1)] }, { coefficient := 1, powers := [(3, 1), (59, 1)] }, { coefficient := 1, powers := [(20, 1), (51, 1)] }, { coefficient := 1, powers := [(20, 1), (56, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (46, 1), (53, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (40, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (46, 1)] }, { coefficient := 1, powers := [(19, 1), (29, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (41, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (47, 1), (52, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (56, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (56, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (59, 1)] }, { coefficient := 1, powers := [(10, 1), (45, 1)] }, { coefficient := 1, powers := [(10, 1), (56, 1)] }, { coefficient := 1, powers := [(15, 1), (40, 1)] }, { coefficient := 1, powers := [(15, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (51, 1)] }, { coefficient := 1, powers := [(23, 1), (56, 1)] }, { coefficient := 1, powers := [(28, 1), (40, 1)] }, { coefficient := 1, powers := [(28, 1), (45, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (36, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1)] }, { coefficient := 1, powers := [(3, 1), (25, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1), (59, 1)] }, { coefficient := 1, powers := [(20, 1)] }, { coefficient := 1, powers := [(25, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (37, 1), (60, 1)] }, { coefficient := 1, powers := [(1, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(4, 1), (28, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (23, 1), (60, 1)] }, { coefficient := 1, powers := [(11, 1), (28, 1), (46, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (47, 1), (53, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (59, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (59, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (53, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (37, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (40, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (45, 1), (51, 1)] }, { coefficient := 1, powers := [(40, 1)] }, { coefficient := 1, powers := [(45, 1)] }, { coefficient := 1, powers := [(51, 1)] }, { coefficient := 1, powers := [(56, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (38, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (41, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (48, 1), (54, 1)] }, { coefficient := 1, powers := [(21, 1), (43, 1), (54, 1)] }, { coefficient := 1, powers := [(21, 1), (50, 1), (57, 1)] }, { coefficient := 1, powers := [(26, 1), (41, 1), (43, 1)] }, { coefficient := 1, powers := [(26, 1), (48, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (37, 1), (59, 1)] }, { coefficient := 1, powers := [(1, 1), (40, 1), (56, 1)] }, { coefficient := 1, powers := [(1, 1), (45, 1), (51, 1)] }, { coefficient := 1, powers := [(4, 1), (28, 1), (59, 1)] }, { coefficient := 1, powers := [(4, 1), (31, 1), (56, 1)] }, { coefficient := 1, powers := [(4, 1), (34, 1), (51, 1)] }, { coefficient := 1, powers := [(7, 1), (23, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (31, 1), (45, 1)] }, { coefficient := 1, powers := [(7, 1), (34, 1), (40, 1)] }, { coefficient := 1, powers := [(10, 1), (23, 1), (56, 1)] }, { coefficient := 1, powers := [(10, 1), (28, 1), (45, 1)] }, { coefficient := 1, powers := [(10, 1), (34, 1), (37, 1)] }, { coefficient := 1, powers := [(15, 1), (23, 1), (51, 1)] }, { coefficient := 1, powers := [(15, 1), (28, 1), (40, 1)] }, { coefficient := 1, powers := [(15, 1), (31, 1), (37, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (41, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (48, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (48, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1), (29, 1), (48, 1)] }, { coefficient := 1, powers := [(12, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (54, 1)] }, { coefficient := 1, powers := [(19, 1), (29, 1), (41, 1)] }, { coefficient := 1, powers := [(19, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (61, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (62, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 62 → SparsePoly (Fin 63) := ![
  [{ coefficient := 2, powers := [(0, 1), (2, 1), (38, 1), (60, 1), (62, 1)] }, { coefficient := 2, powers := [(0, 1), (2, 1), (41, 1), (57, 1), (62, 1)] }, { coefficient := -2, powers := [(0, 1), (8, 1), (35, 1), (41, 1), (62, 1)] }, { coefficient := -2, powers := [(0, 1), (41, 1), (57, 1)] }, { coefficient := 2, powers := [(2, 1), (3, 1), (7, 1), (34, 1), (38, 1), (59, 1), (60, 1), (62, 1)] }, { coefficient := -2, powers := [(2, 1), (3, 1), (15, 1), (23, 1), (38, 1), (59, 1), (60, 1), (62, 1)] }, { coefficient := 2, powers := [(2, 1), (3, 1), (25, 1), (38, 1), (59, 1), (60, 1), (62, 1)] }, { coefficient := 2, powers := [(2, 1), (3, 1), (25, 1), (41, 1), (57, 1), (59, 1), (62, 1)] }, { coefficient := 2, powers := [(2, 1), (7, 1), (20, 1), (34, 1), (38, 1), (56, 1), (60, 1), (62, 1)] }, { coefficient := 2, powers := [(2, 1), (7, 1), (31, 1), (38, 1), (60, 1), (62, 1)] }, { coefficient := -2, powers := [(2, 1), (10, 1), (23, 1), (38, 1), (60, 1), (62, 1)] }, { coefficient := 2, powers := [(2, 1), (10, 1), (28, 1), (38, 1), (60, 1), (62, 1)] }, { coefficient := -2, powers := [(2, 1), (15, 1), (20, 1), (23, 1), (38, 1), (56, 1), (60, 1), (62, 1)] }, { coefficient := -2, powers := [(2, 1), (15, 1), (28, 1), (38, 1), (60, 1), (62, 1)] }, { coefficient := 2, powers := [(2, 1), (16, 1), (31, 1), (38, 1), (50, 1), (56, 1), (62, 1)] }, { coefficient := 2, powers := [(2, 1), (16, 1), (34, 1), (38, 1), (50, 1), (56, 1), (62, 1)] }, { coefficient := 2, powers := [(2, 1), (20, 1), (25, 1), (38, 1), (56, 1), (60, 1), (62, 1)] }, { coefficient := 2, powers := [(2, 1), (20, 1), (25, 1), (41, 1), (56, 1), (57, 1), (62, 1)] }, { coefficient := 2, powers := [(2, 1), (25, 1), (38, 1), (60, 1), (62, 1)] }, { coefficient := 2, powers := [(2, 1), (25, 1), (41, 1), (57, 1), (62, 1)] }, { coefficient := 4, powers := [(3, 1), (5, 1), (7, 1), (31, 1), (32, 1), (57, 1), (59, 1), (62, 1)] }, { coefficient := 2, powers := [(5, 1), (20, 1), (35, 1), (54, 1), (62, 1)] }, { coefficient := -2, powers := [(8, 1), (25, 1), (35, 1), (41, 1), (62, 1)] }, { coefficient := -2, powers := [(19, 1), (25, 1), (29, 1), (41, 1), (62, 1)] }, { coefficient := -2, powers := [(25, 1), (41, 1), (57, 1)] }],
  [{ coefficient := 2, powers := [(2, 1), (11, 1), (23, 1), (38, 1), (59, 1), (62, 1)] }, { coefficient := -2, powers := [(2, 1), (11, 1), (28, 1), (38, 1), (59, 1), (62, 1)] }, { coefficient := -2, powers := [(2, 1), (11, 1), (31, 1), (38, 1), (56, 1), (62, 1)] }, { coefficient := -2, powers := [(2, 1), (20, 1), (21, 1), (54, 1), (61, 1), (62, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (2, 1), (6, 1), (18, 1), (29, 1), (47, 1), (60, 1), (62, 2)] }, { coefficient := 2, powers := [(0, 1), (2, 1), (7, 1), (31, 1), (38, 1), (56, 1), (60, 1), (62, 1)] }, { coefficient := 2, powers := [(0, 1), (2, 1), (7, 1), (34, 1), (38, 1), (45, 1), (60, 1), (62, 1)] }, { coefficient := 2, powers := [(0, 1), (2, 1), (7, 1), (34, 1), (38, 1), (56, 1), (60, 1), (62, 1)] }, { coefficient := -2, powers := [(0, 1), (2, 1), (15, 1), (23, 1), (38, 1), (45, 1), (60, 1), (62, 1)] }, { coefficient := 2, powers := [(0, 1), (2, 1), (25, 1), (38, 1), (45, 1), (60, 1), (62, 1)] }, { coefficient := 2, powers := [(0, 1), (2, 1), (25, 1), (41, 1), (45, 1), (57, 1), (62, 1)] }, { coefficient := 4, powers := [(0, 1), (5, 1), (32, 1), (57, 1), (62, 1)] }, { coefficient := -6, powers := [(0, 1), (18, 1), (32, 1), (36, 1), (47, 1), (57, 1), (62, 1)] }, { coefficient := 2, powers := [(2, 1), (4, 1), (34, 1), (38, 1), (60, 1), (62, 1)] }, { coefficient := -2, powers := [(2, 1), (6, 1), (18, 1), (24, 1), (26, 1), (60, 1), (62, 2)] }, { coefficient := -2, powers := [(2, 1), (6, 1), (26, 1), (47, 1), (60, 1), (62, 1)] }, { coefficient := 2, powers := [(2, 1), (7, 1), (20, 1), (31, 1), (38, 1), (56, 1), (60, 1), (62, 1)] }, { coefficient := 2, powers := [(2, 1), (7, 1), (20, 1), (34, 1), (38, 1), (45, 1), (60, 1), (62, 1)] }, { coefficient := 2, powers := [(2, 1), (7, 1), (20, 1), (34, 1), (38, 1), (56, 1), (60, 1), (62, 1)] }, { coefficient := -2, powers := [(2, 1), (7, 1), (25, 1), (31, 1), (38, 1), (43, 1), (50, 1), (56, 1), (59, 1), (62, 1)] }, { coefficient := -2, powers := [(2, 1), (7, 1), (25, 1), (34, 1), (38, 1), (43, 1), (50, 1), (56, 1), (59, 1), (62, 1)] }, { coefficient := -2, powers := [(2, 1), (7, 1), (34, 1), (38, 1), (60, 1), (62, 1)] }, { coefficient := -2, powers := [(2, 1), (15, 1), (20, 1), (23, 1), (38, 1), (45, 1), (60, 1), (62, 1)] }, { coefficient := -2, powers := [(2, 1), (20, 1), (21, 1), (36, 1), (53, 1), (60, 1), (61, 1), (62, 1)] }, { coefficient := 2, powers := [(2, 1), (20, 1), (25, 1), (38, 1), (45, 1), (60, 1), (62, 1)] }, { coefficient := 2, powers := [(2, 1), (20, 1), (25, 1), (41, 1), (45, 1), (57, 1), (62, 1)] }, { coefficient := -2, powers := [(2, 1), (20, 1), (26, 1), (36, 1), (47, 1), (60, 1), (61, 1), (62, 1)] }, { coefficient := 2, powers := [(2, 1), (21, 1), (25, 1), (43, 1), (54, 1), (61, 1), (62, 1)] }, { coefficient := 2, powers := [(2, 1), (25, 2), (48, 1), (54, 1), (61, 1), (62, 1)] }, { coefficient := -2, powers := [(2, 1), (25, 1), (38, 1), (60, 1), (62, 1)] }, { coefficient := -2, powers := [(2, 1), (25, 1), (41, 1), (57, 1), (62, 1)] }, { coefficient := 2, powers := [(2, 1), (25, 1), (48, 1), (54, 1), (62, 1)] }, { coefficient := 4, powers := [(3, 1), (4, 1), (5, 1), (32, 1), (34, 1), (57, 1), (59, 1), (62, 1)] }, { coefficient := 4, powers := [(3, 1), (5, 1), (15, 1), (23, 1), (32, 1), (57, 1), (59, 1), (62, 1)] }, { coefficient := -4, powers := [(3, 1), (5, 1), (15, 1), (28, 1), (32, 1), (57, 1), (59, 1), (62, 1)] }, { coefficient := 4, powers := [(5, 1), (20, 1), (32, 1), (57, 1), (62, 1)] }, { coefficient := -2, powers := [(8, 1), (25, 1), (32, 1), (36, 1), (48, 1), (59, 1), (62, 1)] }, { coefficient := 2, powers := [(8, 1), (25, 1), (32, 1), (48, 1), (62, 1)] }, { coefficient := -2, powers := [(12, 1), (24, 1), (25, 1), (57, 1), (62, 1)] }, { coefficient := -2, powers := [(12, 1), (25, 1), (29, 1), (48, 1), (62, 1)] }, { coefficient := -2, powers := [(19, 1), (25, 1), (29, 1), (41, 1), (62, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (2, 1), (16, 1), (31, 1), (38, 1), (45, 1), (56, 1), (62, 1)] }, { coefficient := 2, powers := [(0, 1), (2, 1), (16, 1), (34, 1), (38, 1), (45, 1), (56, 1), (62, 1)] }, { coefficient := 2, powers := [(2, 1), (7, 1), (25, 1), (31, 1), (38, 1), (43, 1), (56, 1), (59, 1), (62, 1)] }, { coefficient := 2, powers := [(2, 1), (7, 1), (25, 1), (34, 1), (38, 1), (43, 1), (56, 1), (59, 1), (62, 1)] }, { coefficient := -2, powers := [(2, 1), (10, 1), (34, 1), (38, 1), (46, 1), (62, 1)] }, { coefficient := 2, powers := [(2, 1), (15, 1), (34, 1), (38, 1), (46, 1), (62, 1)] }, { coefficient := -2, powers := [(2, 1), (16, 1), (20, 1), (31, 1), (38, 1), (56, 2), (62, 1)] }, { coefficient := -2, powers := [(2, 1), (16, 1), (20, 1), (34, 1), (38, 1), (56, 2), (62, 1)] }, { coefficient := 2, powers := [(2, 1), (16, 1), (34, 1), (38, 1), (56, 1), (62, 1)] }, { coefficient := -2, powers := [(2, 1), (25, 1), (26, 1), (48, 1), (61, 1), (62, 1)] }, { coefficient := -2, powers := [(19, 1), (21, 1), (29, 1), (62, 1)] }],
  [{ coefficient := 4, powers := [(3, 1), (5, 1), (23, 1), (57, 1), (59, 2)] }, { coefficient := -4, powers := [(3, 1), (5, 1), (28, 1), (57, 1), (59, 2)] }, { coefficient := -4, powers := [(3, 1), (5, 1), (31, 1), (45, 1), (57, 1), (59, 1)] }, { coefficient := 4, powers := [(3, 1), (5, 1), (34, 1), (40, 1), (57, 1), (59, 1)] }],
  [{ coefficient := 2, powers := [(8, 1), (50, 1), (59, 1)] }, { coefficient := -2, powers := [(12, 1), (53, 1)] }],
  [{ coefficient := -2, powers := [(19, 1), (47, 1)] }],
  [{ coefficient := -2, powers := [(2, 1), (10, 1), (19, 1), (34, 1), (38, 1), (62, 1)] }, { coefficient := 2, powers := [(2, 1), (15, 1), (19, 1), (34, 1), (38, 1), (62, 1)] }, { coefficient := 4, powers := [(3, 1), (5, 1), (10, 1), (34, 1), (57, 1), (59, 1)] }],
  [{ coefficient := -2, powers := [(2, 1), (10, 1), (12, 1), (34, 1), (38, 1), (62, 1)] }, { coefficient := 2, powers := [(2, 1), (12, 1), (15, 1), (34, 1), (38, 1), (62, 1)] }],
  [{ coefficient := 4, powers := [(5, 1), (10, 1), (23, 1), (57, 1), (59, 1)] }, { coefficient := -4, powers := [(5, 1), (10, 1), (28, 1), (57, 1), (59, 1)] }, { coefficient := -2, powers := [(5, 1), (25, 1), (57, 1), (59, 1)] }],
  [{ coefficient := 2, powers := [(2, 1), (6, 1), (26, 1), (51, 1), (60, 1), (62, 1)] }, { coefficient := 2, powers := [(2, 1), (20, 1), (26, 1), (36, 1), (51, 1), (60, 1), (61, 1), (62, 1)] }, { coefficient := -2, powers := [(2, 1), (25, 1), (26, 1), (36, 1), (56, 1), (60, 1), (61, 1), (62, 1)] }, { coefficient := -1, powers := [(2, 1), (25, 1), (36, 1), (53, 1), (56, 1), (60, 1), (62, 1)] }, { coefficient := 2, powers := [(25, 1), (52, 1), (57, 1)] }],
  [{ coefficient := -2, powers := [(2, 1), (6, 1), (47, 1), (60, 1), (62, 1)] }, { coefficient := 2, powers := [(2, 1), (20, 1), (21, 1), (36, 1), (51, 1), (60, 1), (61, 1), (62, 1)] }, { coefficient := -2, powers := [(2, 1), (21, 1), (25, 1), (36, 1), (56, 1), (60, 1), (61, 1), (62, 1)] }, { coefficient := -1, powers := [(2, 1), (25, 1), (36, 1), (47, 1), (56, 1), (60, 1), (62, 1)] }, { coefficient := 2, powers := [(25, 1), (41, 1), (46, 1)] }],
  [{ coefficient := -2, powers := [(5, 1), (20, 1), (56, 1), (57, 1), (59, 1)] }, { coefficient := 2, powers := [(8, 1), (48, 1), (59, 1)] }],
  [{ coefficient := -2, powers := [(2, 1), (31, 1), (38, 1), (56, 2)] }, { coefficient := -2, powers := [(2, 1), (34, 1), (38, 1), (56, 2)] }],
  [{ coefficient := 2, powers := [(2, 1), (21, 1), (29, 1), (36, 1), (56, 1), (60, 1), (61, 1), (62, 1)] }, { coefficient := 2, powers := [(2, 1), (24, 1), (26, 1), (36, 1), (56, 1), (60, 1), (61, 1), (62, 1)] }],
  [{ coefficient := -2, powers := [(2, 1), (6, 1), (18, 1), (26, 1), (60, 1), (62, 1)] }, { coefficient := -2, powers := [(2, 1), (18, 1), (20, 1), (26, 1), (36, 1), (60, 1), (61, 1), (62, 1)] }, { coefficient := 2, powers := [(12, 1), (25, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (18, 1), (25, 1), (36, 1), (56, 1), (60, 1), (62, 1)] }],
  [{ coefficient := 2, powers := [(2, 1), (18, 1), (20, 1), (21, 1), (36, 1), (60, 1), (61, 1), (62, 1)] }, { coefficient := 2, powers := [(19, 1), (25, 1), (41, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (5, 1), (32, 1), (56, 1), (57, 1), (62, 1)] }, { coefficient := -2, powers := [(2, 1), (25, 1), (38, 1), (56, 1), (60, 1), (62, 1)] }, { coefficient := 2, powers := [(5, 1), (20, 1), (32, 1), (56, 1), (57, 1), (62, 1)] }, { coefficient := 6, powers := [(5, 1), (32, 1), (57, 1), (62, 1)] }],
  [{ coefficient := 2, powers := [(8, 1), (60, 1)] }],
  [{ coefficient := 2, powers := [(2, 1), (7, 1), (31, 1), (38, 1), (50, 1), (51, 1), (56, 1), (59, 1)] }, { coefficient := -2, powers := [(2, 1), (7, 1), (31, 1), (38, 1), (52, 1), (56, 1), (59, 1)] }, { coefficient := 2, powers := [(2, 1), (7, 1), (34, 1), (38, 1), (50, 1), (51, 1), (56, 1), (59, 1)] }, { coefficient := -2, powers := [(2, 1), (7, 1), (34, 1), (38, 1), (52, 1), (56, 1), (59, 1)] }, { coefficient := -2, powers := [(2, 1), (21, 1), (51, 1), (54, 1), (61, 1)] }],
  [{ coefficient := -2, powers := [(2, 1), (25, 1), (51, 1), (54, 1), (61, 1)] }, { coefficient := 2, powers := [(2, 1), (26, 1), (52, 1), (61, 1)] }, { coefficient := -2, powers := [(2, 1), (51, 1), (54, 1)] }, { coefficient := -2, powers := [(2, 1), (54, 1), (61, 1)] }, { coefficient := 2, powers := [(8, 1), (32, 1), (36, 1), (51, 1), (59, 1)] }, { coefficient := -2, powers := [(8, 1), (32, 1), (51, 1)] }, { coefficient := 2, powers := [(12, 1), (29, 1), (51, 1)] }],
  [{ coefficient := 2, powers := [(2, 1), (21, 1), (46, 1), (61, 1)] }, { coefficient := -2, powers := [(5, 1), (35, 1), (45, 1)] }],
  [{ coefficient := 2, powers := [(25, 1), (29, 1), (41, 1)] }],
  [{ coefficient := -2, powers := [(2, 1), (7, 1), (31, 1), (38, 1), (50, 1), (56, 1), (59, 1)] }, { coefficient := -2, powers := [(2, 1), (7, 1), (34, 1), (38, 1), (50, 1), (56, 1), (59, 1)] }, { coefficient := 2, powers := [(2, 1), (21, 1), (54, 1), (61, 1)] }],
  [{ coefficient := 2, powers := [(5, 1), (35, 1)] }],
  [{ coefficient := 2, powers := [(2, 1), (25, 1), (54, 1), (61, 1)] }, { coefficient := 2, powers := [(2, 1), (54, 1)] }, { coefficient := -2, powers := [(8, 1), (32, 1), (36, 1), (59, 1)] }, { coefficient := 2, powers := [(8, 1), (32, 1)] }, { coefficient := -2, powers := [(12, 1), (29, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (2, 1), (7, 1), (34, 1), (38, 1), (60, 1), (62, 1)] }, { coefficient := 2, powers := [(0, 1), (2, 1), (15, 1), (23, 1), (38, 1), (60, 1), (62, 1)] }, { coefficient := -2, powers := [(0, 1), (2, 1), (25, 1), (38, 1), (60, 1), (62, 1)] }, { coefficient := -2, powers := [(0, 1), (2, 1), (25, 1), (41, 1), (57, 1), (62, 1)] }],
  [{ coefficient := 4, powers := [(3, 1), (5, 1), (31, 1), (57, 1), (59, 1)] }],
  [{ coefficient := 2, powers := [(2, 1), (31, 1), (38, 1), (56, 2)] }, { coefficient := 2, powers := [(2, 1), (34, 1), (38, 1), (56, 2)] }],
  [{ coefficient := -2, powers := [(29, 1), (41, 1)] }],
  [{ coefficient := -2, powers := [(2, 1), (23, 1), (38, 1), (59, 1)] }, { coefficient := 2, powers := [(2, 1), (31, 1), (38, 1), (56, 1)] }],
  [{ coefficient := -2, powers := [(2, 1), (6, 1), (29, 1), (60, 1), (62, 1)] }, { coefficient := -6, powers := [(32, 1), (36, 1), (57, 1)] }],
  [{ coefficient := 2, powers := [(29, 1)] }],
  [{ coefficient := -2, powers := [(2, 1), (6, 1), (24, 1), (60, 1), (62, 1)] }],
  [{ coefficient := 2, powers := [(2, 1), (6, 1), (24, 1), (26, 1), (60, 1), (62, 1)] }, { coefficient := -2, powers := [(2, 1), (20, 1), (21, 1), (29, 1), (36, 1), (60, 1), (61, 1), (62, 1)] }],
  [{ coefficient := 2, powers := [(19, 1)] }],
  [{ coefficient := 2, powers := [(2, 1), (25, 1), (36, 1), (56, 1), (60, 1), (61, 1)] }],
  [{ coefficient := 2, powers := [(2, 1), (7, 1), (31, 1), (38, 1), (56, 1), (59, 1)] }, { coefficient := 2, powers := [(2, 1), (7, 1), (34, 1), (38, 1), (56, 1), (59, 1)] }],
  [{ coefficient := -2, powers := [(2, 1), (16, 1), (31, 1), (38, 1), (56, 1)] }, { coefficient := -2, powers := [(2, 1), (16, 1), (34, 1), (38, 1), (56, 1)] }],
  [{ coefficient := -2, powers := [(2, 1), (21, 1), (61, 1)] }],
  [{ coefficient := 2, powers := [(2, 1), (6, 1), (18, 1), (29, 1), (60, 1), (62, 1)] }, { coefficient := 6, powers := [(18, 1), (32, 1), (36, 1), (57, 1)] }],
  [{ coefficient := -2, powers := [(2, 1), (26, 1), (61, 1)] }],
  [{ coefficient := 2, powers := [(2, 1), (10, 1), (34, 1), (38, 1), (62, 1)] }, { coefficient := -2, powers := [(2, 1), (15, 1), (34, 1), (38, 1), (62, 1)] }],
  [{ coefficient := -2, powers := [(8, 1), (59, 1)] }],
  [{ coefficient := 2, powers := [(12, 1)] }],
  [{ coefficient := -2, powers := [(2, 1), (38, 1), (60, 1)] }, { coefficient := 2, powers := [(8, 1), (35, 1), (41, 1)] }],
  [{ coefficient := -2, powers := [(2, 1), (7, 1), (31, 1), (38, 1), (56, 1), (60, 1)] }, { coefficient := -2, powers := [(2, 1), (7, 1), (34, 1), (38, 1), (45, 1), (60, 1)] }, { coefficient := -2, powers := [(2, 1), (7, 1), (34, 1), (38, 1), (56, 1), (60, 1)] }, { coefficient := 2, powers := [(2, 1), (15, 1), (23, 1), (38, 1), (45, 1), (60, 1)] }, { coefficient := -2, powers := [(2, 1), (25, 1), (38, 1), (45, 1), (60, 1)] }, { coefficient := -2, powers := [(2, 1), (25, 1), (41, 1), (45, 1), (57, 1)] }, { coefficient := -4, powers := [(5, 1), (32, 1), (57, 1)] }],
  [{ coefficient := -2, powers := [(25, 1), (41, 1)] }],
  [{ coefficient := -2, powers := [(25, 1), (57, 1)] }],
  [{ coefficient := 2, powers := [(2, 1), (23, 1), (38, 1), (60, 1)] }, { coefficient := 4, powers := [(3, 1), (5, 1), (28, 1), (32, 1), (57, 1), (59, 1)] }],
  [{ coefficient := 2, powers := [(2, 1), (15, 1), (38, 1), (60, 1)] }],
  [{ coefficient := 2, powers := [(5, 1), (32, 1), (56, 1), (57, 1)] }],
  [{ coefficient := 2, powers := [(2, 1), (38, 1), (59, 1)] }],
  [{ coefficient := 2, powers := [(2, 1), (6, 1), (60, 1), (62, 1)] }],
  [{ coefficient := 2, powers := [(2, 1), (7, 1), (34, 1), (38, 1), (60, 1)] }, { coefficient := -2, powers := [(2, 1), (15, 1), (23, 1), (38, 1), (60, 1)] }, { coefficient := 2, powers := [(2, 1), (25, 1), (38, 1), (60, 1)] }, { coefficient := 2, powers := [(2, 1), (25, 1), (41, 1), (57, 1)] }],
  [{ coefficient := 2, powers := [(2, 1), (61, 1)] }],
  [{ coefficient := -2, powers := [(2, 1), (38, 1), (60, 1)] }, { coefficient := -4, powers := [(3, 1), (5, 1), (32, 1), (57, 1), (59, 1)] }],
  [{ coefficient := -2, powers := [] }],
  [{ coefficient := -2, powers := [(2, 1), (25, 1), (36, 1), (38, 1), (56, 1), (59, 1), (60, 1)] }, { coefficient := -2, powers := [(2, 1), (25, 1), (36, 1), (47, 1), (53, 1), (56, 1), (60, 1)] }, { coefficient := -2, powers := [(2, 1), (38, 1), (60, 1)] }, { coefficient := -2, powers := [(2, 1), (41, 1), (57, 1)] }],
  [{ coefficient := 2, powers := [(2, 1), (38, 1), (40, 1), (56, 1), (60, 1)] }, { coefficient := 2, powers := [(2, 1), (38, 1), (45, 1), (51, 1), (60, 1)] }, { coefficient := -2, powers := [(2, 1), (38, 1), (46, 1), (52, 1), (59, 1)] }, { coefficient := 4, powers := [(3, 1), (5, 1), (32, 1), (37, 1), (57, 1), (59, 2)] }, { coefficient := 4, powers := [(3, 1), (5, 1), (32, 1), (40, 1), (56, 1), (57, 1), (59, 1)] }, { coefficient := 4, powers := [(3, 1), (5, 1), (32, 1), (45, 1), (51, 1), (57, 1), (59, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (2, 1), (6, 1), (18, 1), (29, 1), (47, 1), (51, 1), (60, 1), (62, 1)] }, { coefficient := -2, powers := [(0, 1), (2, 1), (7, 1), (31, 1), (38, 1), (51, 1), (56, 1), (60, 1)] }, { coefficient := 2, powers := [(0, 1), (2, 1), (7, 1), (34, 1), (37, 1), (38, 1), (59, 1), (60, 1)] }, { coefficient := 2, powers := [(0, 1), (2, 1), (7, 1), (34, 1), (38, 1), (40, 1), (56, 1), (60, 1)] }, { coefficient := -2, powers := [(0, 1), (2, 1), (7, 1), (34, 1), (38, 1), (51, 1), (56, 1), (60, 1)] }, { coefficient := -2, powers := [(0, 1), (2, 1), (15, 1), (23, 1), (37, 1), (38, 1), (59, 1), (60, 1)] }, { coefficient := -2, powers := [(0, 1), (2, 1), (15, 1), (23, 1), (38, 1), (40, 1), (56, 1), (60, 1)] }, { coefficient := -2, powers := [(0, 1), (2, 1), (16, 1), (31, 1), (38, 1), (45, 1), (52, 1), (56, 1)] }, { coefficient := -2, powers := [(0, 1), (2, 1), (16, 1), (34, 1), (38, 1), (45, 1), (52, 1), (56, 1)] }, { coefficient := 2, powers := [(0, 1), (2, 1), (25, 1), (37, 1), (38, 1), (59, 1), (60, 1)] }, { coefficient := 2, powers := [(0, 1), (2, 1), (25, 1), (37, 1), (41, 1), (57, 1), (59, 1)] }, { coefficient := 2, powers := [(0, 1), (2, 1), (25, 1), (38, 1), (40, 1), (56, 1), (60, 1)] }, { coefficient := 2, powers := [(0, 1), (2, 1), (25, 1), (40, 1), (41, 1), (56, 1), (57, 1)] }, { coefficient := -2, powers := [(0, 1), (2, 1), (38, 1), (45, 1), (60, 1)] }, { coefficient := -2, powers := [(0, 1), (2, 1), (41, 1), (45, 1), (57, 1)] }, { coefficient := 2, powers := [(0, 1), (5, 1), (32, 1), (36, 1), (56, 1), (57, 1), (59, 1)] }, { coefficient := -4, powers := [(0, 1), (5, 1), (32, 1), (51, 1), (57, 1)] }, { coefficient := 2, powers := [(0, 1), (5, 1), (32, 1), (56, 1), (57, 1)] }, { coefficient := 2, powers := [(0, 1), (8, 1), (35, 1), (41, 1), (45, 1)] }, { coefficient := 6, powers := [(0, 1), (18, 1), (32, 1), (36, 1), (47, 1), (51, 1), (57, 1)] }, { coefficient := -2, powers := [(2, 1), (3, 1), (7, 1), (34, 1), (38, 1), (45, 1), (59, 1), (60, 1)] }, { coefficient := 2, powers := [(2, 1), (3, 1), (15, 1), (23, 1), (38, 1), (45, 1), (59, 1), (60, 1)] }, { coefficient := -2, powers := [(2, 1), (3, 1), (25, 1), (38, 1), (45, 1), (59, 1), (60, 1)] }, { coefficient := -2, powers := [(2, 1), (3, 1), (25, 1), (41, 1), (45, 1), (57, 1), (59, 1)] }, { coefficient := -2, powers := [(2, 1), (4, 1), (34, 1), (38, 1), (51, 1), (60, 1)] }, { coefficient := 2, powers := [(2, 1), (6, 1), (18, 1), (24, 1), (26, 1), (51, 1), (60, 1), (62, 1)] }, { coefficient := -2, powers := [(2, 1), (6, 1), (38, 1), (59, 1), (60, 1)] }, { coefficient := -2, powers := [(2, 1), (7, 1), (20, 1), (31, 1), (38, 1), (51, 1), (56, 1), (60, 1)] }, { coefficient := -2, powers := [(2, 1), (7, 1), (20, 1), (34, 1), (38, 1), (45, 1), (51, 1), (60, 1)] }, { coefficient := -2, powers := [(2, 1), (7, 1), (20, 1), (34, 1), (38, 1), (45, 1), (56, 1), (60, 1)] }, { coefficient := -2, powers := [(2, 1), (7, 1), (20, 1), (34, 1), (38, 1), (51, 1), (56, 1), (60, 1)] }, { coefficient := 2, powers := [(2, 1), (7, 1), (25, 1), (31, 1), (38, 1), (43, 1), (50, 1), (51, 1), (56, 1), (59, 1)] }, { coefficient := -2, powers := [(2, 1), (7, 1), (25, 1), (31, 1), (38, 1), (43, 1), (52, 1), (56, 1), (59, 1)] }, { coefficient := 2, powers := [(2, 1), (7, 1), (25, 1), (34, 1), (38, 1), (43, 1), (50, 1), (51, 1), (56, 1), (59, 1)] }, { coefficient := -2, powers := [(2, 1), (7, 1), (25, 1), (34, 1), (38, 1), (43, 1), (52, 1), (56, 1), (59, 1)] }, { coefficient := -2, powers := [(2, 1), (7, 1), (31, 1), (38, 1), (45, 1), (60, 1)] }, { coefficient := 2, powers := [(2, 1), (7, 1), (34, 1), (38, 1), (51, 1), (60, 1)] }, { coefficient := 2, powers := [(2, 1), (10, 1), (23, 1), (38, 1), (45, 1), (60, 1)] }, { coefficient := -2, powers := [(2, 1), (10, 1), (28, 1), (38, 1), (45, 1), (60, 1)] }, { coefficient := -2, powers := [(2, 1), (10, 1), (34, 1), (37, 1), (38, 1), (60, 1)] }, { coefficient := -2, powers := [(2, 1), (11, 1), (23, 1), (38, 1), (46, 1), (59, 1)] }, { coefficient := 2, powers := [(2, 1), (11, 1), (28, 1), (38, 1), (46, 1), (59, 1)] }, { coefficient := 2, powers := [(2, 1), (11, 1), (31, 1), (38, 1), (46, 1), (56, 1)] }, { coefficient := 2, powers := [(2, 1), (15, 1), (20, 1), (23, 1), (38, 1), (45, 1), (51, 1), (60, 1)] }, { coefficient := 2, powers := [(2, 1), (15, 1), (20, 1), (23, 1), (38, 1), (45, 1), (56, 1), (60, 1)] }, { coefficient := 2, powers := [(2, 1), (15, 1), (28, 1), (38, 1), (45, 1), (60, 1)] }, { coefficient := 2, powers := [(2, 1), (15, 1), (34, 1), (37, 1), (38, 1), (60, 1)] }, { coefficient := 2, powers := [(2, 1), (16, 1), (20, 1), (31, 1), (38, 1), (52, 1), (56, 2)] }, { coefficient := 2, powers := [(2, 1), (16, 1), (20, 1), (34, 1), (38, 1), (52, 1), (56, 2)] }, { coefficient := -2, powers := [(2, 1), (16, 1), (31, 1), (38, 1), (45, 1), (50, 1), (56, 1)] }, { coefficient := -2, powers := [(2, 1), (16, 1), (34, 1), (38, 1), (45, 1), (50, 1), (56, 1)] }, { coefficient := -2, powers := [(2, 1), (16, 1), (34, 1), (38, 1), (52, 1), (56, 1)] }, { coefficient := 2, powers := [(2, 1), (20, 1), (21, 1), (46, 1), (54, 1), (61, 1)] }, { coefficient := -2, powers := [(2, 1), (20, 1), (25, 1), (38, 1), (45, 1), (51, 1), (60, 1)] }, { coefficient := -2, powers := [(2, 1), (20, 1), (25, 1), (38, 1), (45, 1), (56, 1), (60, 1)] }, { coefficient := -2, powers := [(2, 1), (20, 1), (25, 1), (41, 1), (45, 1), (51, 1), (57, 1)] }, { coefficient := -2, powers := [(2, 1), (20, 1), (25, 1), (41, 1), (45, 1), (56, 1), (57, 1)] }, { coefficient := 2, powers := [(2, 1), (21, 1), (25, 1), (36, 1), (53, 1), (56, 1), (60, 1), (61, 1)] }, { coefficient := -2, powers := [(2, 1), (21, 1), (25, 1), (43, 1), (51, 1), (54, 1), (61, 1)] }, { coefficient := -2, powers := [(2, 1), (25, 2), (48, 1), (51, 1), (54, 1), (61, 1)] }, { coefficient := 2, powers := [(2, 1), (25, 1), (26, 1), (36, 1), (47, 1), (56, 1), (60, 1), (61, 1)] }, { coefficient := 2, powers := [(2, 1), (25, 1), (26, 1), (48, 1), (52, 1), (61, 1)] }, { coefficient := 2, powers := [(2, 1), (25, 1), (36, 1), (38, 1), (56, 1), (59, 1), (60, 1)] }, { coefficient := 2, powers := [(2, 1), (25, 1), (36, 1), (47, 1), (53, 1), (56, 1), (60, 1)] }, { coefficient := -2, powers := [(2, 1), (25, 1), (38, 1), (45, 1), (60, 1)] }, { coefficient := 2, powers := [(2, 1), (25, 1), (38, 1), (51, 1), (60, 1)] }, { coefficient := 2, powers := [(2, 1), (25, 1), (38, 1), (56, 1), (60, 1)] }, { coefficient := -2, powers := [(2, 1), (25, 1), (41, 1), (45, 1), (57, 1)] }, { coefficient := 2, powers := [(2, 1), (25, 1), (41, 1), (51, 1), (57, 1)] }, { coefficient := -2, powers := [(2, 1), (25, 1), (48, 1), (51, 1), (54, 1)] }, { coefficient := -4, powers := [(3, 1), (4, 1), (5, 1), (32, 1), (34, 1), (51, 1), (57, 1), (59, 1)] }, { coefficient := -4, powers := [(3, 1), (5, 1), (7, 1), (31, 1), (32, 1), (45, 1), (57, 1), (59, 1)] }, { coefficient := -4, powers := [(3, 1), (5, 1), (15, 1), (23, 1), (32, 1), (51, 1), (57, 1), (59, 1)] }, { coefficient := 4, powers := [(3, 1), (5, 1), (15, 1), (28, 1), (32, 1), (51, 1), (57, 1), (59, 1)] }, { coefficient := -2, powers := [(5, 1), (20, 1), (32, 1), (36, 1), (56, 1), (57, 1), (59, 1)] }, { coefficient := -4, powers := [(5, 1), (20, 1), (32, 1), (51, 1), (57, 1)] }, { coefficient := -2, powers := [(5, 1), (20, 1), (32, 1), (56, 1), (57, 1)] }, { coefficient := -2, powers := [(5, 1), (20, 1), (35, 1), (45, 1), (54, 1)] }, { coefficient := -6, powers := [(5, 1), (32, 1), (36, 1), (57, 1), (59, 1)] }, { coefficient := -6, powers := [(5, 1), (32, 1), (57, 1)] }, { coefficient := 2, powers := [(8, 1), (25, 1), (32, 1), (36, 1), (48, 1), (51, 1), (59, 1)] }, { coefficient := -2, powers := [(8, 1), (25, 1), (32, 1), (48, 1), (51, 1)] }, { coefficient := 2, powers := [(8, 1), (25, 1), (35, 1), (41, 1), (45, 1)] }, { coefficient := 2, powers := [(12, 1), (24, 1), (25, 1), (51, 1), (57, 1)] }, { coefficient := 2, powers := [(12, 1), (25, 1), (29, 1), (48, 1), (51, 1)] }, { coefficient := 2, powers := [(19, 1), (21, 1), (29, 1), (52, 1)] }, { coefficient := 2, powers := [(19, 1), (25, 1), (29, 1), (41, 1), (45, 1)] }, { coefficient := 2, powers := [(19, 1), (25, 1), (29, 1), (41, 1), (51, 1)] }]
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
    ¬ ∀ index : Fin 62,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((2 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (2 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (2 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component60.SelectedLeafB5.selectedHasNoCommonZero

end Krenn.Component60.SelectedLeafB5
