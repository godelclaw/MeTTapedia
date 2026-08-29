import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component55.SelectedLeafB4_1

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "17ad4a97bb9f4e3c4327cfe1ff1178ef5a312173d39b639afbc58204d7c2a610"
def certificateSHA256 : String := "498af8c6d5f44a5d0a890646efbd18a1ba59ab83f86c0a350893b8bf70fba63d"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 54 → Fin 590 := ![
  6,
  8,
  14,
  18,
  21,
  29,
  33,
  39,
  41,
  194,
  200,
  212,
  223,
  224,
  227,
  228,
  233,
  234,
  256,
  257,
  322,
  336,
  337,
  341,
  342,
  345,
  348,
  360,
  361,
  362,
  366,
  368,
  390,
  408,
  425,
  469,
  480,
  490,
  502,
  519,
  521,
  529,
  531,
  542,
  543,
  558,
  559,
  582,
  583,
  584,
  585,
  586,
  588,
  589
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 54 → SparsePoly (Fin 60) := ![
  [{ coefficient := 1, powers := [(4, 1), (35, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (32, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (29, 1)] }],
  [{ coefficient := 1, powers := [(15, 1), (21, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(28, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(32, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(35, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (32, 1)] }, { coefficient := 1, powers := [(32, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (25, 1)] }, { coefficient := 1, powers := [(15, 1), (20, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (25, 1)] }, { coefficient := 1, powers := [(18, 1), (20, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (20, 1)] }, { coefficient := 1, powers := [(18, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (43, 1)] }, { coefficient := 1, powers := [(19, 1), (20, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (48, 1)] }, { coefficient := 1, powers := [(25, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (49, 1)] }, { coefficient := 1, powers := [(21, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(26, 1), (40, 1)] }, { coefficient := 1, powers := [(26, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (40, 1)] }, { coefficient := 1, powers := [(29, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (21, 1), (56, 1)] }, { coefficient := 1, powers := [(21, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (24, 1), (56, 1)] }, { coefficient := 1, powers := [(24, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (25, 1), (46, 1)] }, { coefficient := 1, powers := [(19, 1), (21, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1)] }, { coefficient := 1, powers := [(21, 1), (43, 1)] }, { coefficient := 1, powers := [(25, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (48, 1)] }, { coefficient := 1, powers := [(20, 1), (48, 1)] }, { coefficient := 1, powers := [(25, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (46, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (51, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1)] }, { coefficient := 1, powers := [(13, 1), (29, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (56, 1)] }, { coefficient := 1, powers := [(18, 1), (21, 1), (49, 1)] }, { coefficient := 1, powers := [(18, 1), (21, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (56, 1)] }, { coefficient := 1, powers := [(18, 1), (26, 1), (40, 1)] }, { coefficient := 1, powers := [(18, 1), (26, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (45, 1)] }, { coefficient := 1, powers := [(19, 1), (40, 1)] }, { coefficient := 1, powers := [(19, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (51, 1)] }, { coefficient := 1, powers := [(29, 1), (41, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (54, 1)] }, { coefficient := 1, powers := [(29, 1), (46, 1)] }, { coefficient := 1, powers := [(35, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1), (48, 1)] }, { coefficient := 1, powers := [(25, 1), (44, 1), (48, 1)] }, { coefficient := 1, powers := [(48, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1), (49, 1)] }, { coefficient := 1, powers := [(21, 1), (43, 1), (49, 1)] }, { coefficient := 1, powers := [(46, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (56, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (29, 1), (56, 1)] }, { coefficient := 1, powers := [(10, 1), (29, 1), (44, 1)] }, { coefficient := 1, powers := [(15, 1), (29, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (21, 1), (56, 1)] }, { coefficient := 1, powers := [(10, 1), (21, 1), (53, 1)] }, { coefficient := 1, powers := [(15, 1), (21, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (25, 1), (45, 1)] }, { coefficient := 1, powers := [(19, 1), (25, 1), (40, 1)] }, { coefficient := 1, powers := [(19, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (57, 1)] }, { coefficient := 1, powers := [(13, 1), (46, 1)] }, { coefficient := 1, powers := [(19, 1), (21, 1), (50, 1)] }, { coefficient := 1, powers := [(19, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (41, 1), (53, 1)] }, { coefficient := 1, powers := [(21, 1), (48, 1), (53, 1)] }, { coefficient := 1, powers := [(21, 1), (50, 1)] }, { coefficient := 1, powers := [(41, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1), (50, 1)] }, { coefficient := 1, powers := [(21, 1), (43, 1), (50, 1)] }, { coefficient := 1, powers := [(41, 1), (43, 1)] }, { coefficient := 1, powers := [(46, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (25, 1), (56, 1)] }, { coefficient := 1, powers := [(10, 1), (25, 1), (44, 1)] }, { coefficient := 1, powers := [(15, 1), (25, 1), (40, 1)] }, { coefficient := 1, powers := [(15, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (29, 1), (57, 1)] }, { coefficient := 1, powers := [(4, 1), (32, 1), (54, 1)] }, { coefficient := 1, powers := [(4, 1), (35, 1), (51, 1)] }, { coefficient := 1, powers := [(11, 1), (29, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (20, 1), (56, 1)] }, { coefficient := 1, powers := [(10, 1), (20, 1), (53, 1)] }, { coefficient := 1, powers := [(10, 1)] }, { coefficient := 1, powers := [(15, 1), (20, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (24, 1), (57, 1)] }, { coefficient := 1, powers := [(7, 1), (32, 1), (46, 1)] }, { coefficient := 1, powers := [(7, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(16, 1), (24, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1)] }, { coefficient := 1, powers := [(6, 1), (56, 1)] }, { coefficient := 1, powers := [(25, 1), (40, 1)] }, { coefficient := 1, powers := [(25, 1), (44, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (49, 1)] }, { coefficient := 1, powers := [(3, 1), (56, 1)] }, { coefficient := 1, powers := [(20, 1), (49, 1)] }, { coefficient := 1, powers := [(20, 1), (53, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(4, 1), (56, 1)] }, { coefficient := 1, powers := [(7, 1), (56, 1)] }, { coefficient := 1, powers := [(10, 1), (44, 1)] }, { coefficient := 1, powers := [(10, 1), (53, 1)] }, { coefficient := 1, powers := [(15, 1), (40, 1)] }, { coefficient := 1, powers := [(15, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (49, 1)] }, { coefficient := 1, powers := [(23, 1), (53, 1)] }, { coefficient := 1, powers := [(28, 1), (40, 1)] }, { coefficient := 1, powers := [(28, 1), (44, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (37, 1), (56, 1)] }, { coefficient := 1, powers := [(1, 1), (40, 1), (53, 1)] }, { coefficient := 1, powers := [(1, 1), (44, 1), (49, 1)] }, { coefficient := 1, powers := [(4, 1), (28, 1), (56, 1)] }, { coefficient := 1, powers := [(4, 1), (31, 1), (53, 1)] }, { coefficient := 1, powers := [(4, 1), (34, 1), (49, 1)] }, { coefficient := 1, powers := [(7, 1), (23, 1), (56, 1)] }, { coefficient := 1, powers := [(7, 1), (31, 1), (44, 1)] }, { coefficient := 1, powers := [(7, 1), (34, 1), (40, 1)] }, { coefficient := 1, powers := [(10, 1), (23, 1), (53, 1)] }, { coefficient := 1, powers := [(10, 1), (28, 1), (44, 1)] }, { coefficient := 1, powers := [(10, 1), (34, 1), (37, 1)] }, { coefficient := 1, powers := [(15, 1), (23, 1), (49, 1)] }, { coefficient := 1, powers := [(15, 1), (28, 1), (40, 1)] }, { coefficient := 1, powers := [(15, 1), (31, 1), (37, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (41, 1), (54, 1)] }, { coefficient := 1, powers := [(2, 1), (46, 1), (51, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (51, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (57, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (46, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(13, 1), (24, 1), (54, 1)] }, { coefficient := 1, powers := [(13, 1), (29, 1), (46, 1)] }, { coefficient := 1, powers := [(13, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (51, 1)] }, { coefficient := 1, powers := [(19, 1), (29, 1), (41, 1)] }, { coefficient := 1, powers := [(19, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (58, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1)] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(40, 1)] }],
  [{ coefficient := 1, powers := [(41, 1), (59, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 54 → SparsePoly (Fin 60) := ![
  [{ coefficient := 2, powers := [(8, 1), (31, 1), (41, 1), (53, 1)] }, { coefficient := 2, powers := [(8, 1), (34, 1), (41, 1), (49, 1)] }],
  [{ coefficient := -2, powers := [(5, 1), (31, 1), (54, 1), (58, 1)] }],
  [{ coefficient := -2, powers := [(5, 1), (31, 1), (45, 1), (53, 1)] }, { coefficient := -2, powers := [(5, 1), (34, 1), (45, 1), (49, 1)] }],
  [{ coefficient := -1, powers := [(20, 1), (23, 1), (49, 1), (50, 1), (53, 1), (59, 1)] }, { coefficient := -1, powers := [(20, 1), (23, 1), (50, 1), (53, 2), (59, 1)] }, { coefficient := 2, powers := [(23, 1), (50, 1), (58, 1), (59, 1)] }],
  [{ coefficient := 2, powers := [(8, 1), (31, 1), (50, 1), (58, 1)] }],
  [{ coefficient := 2, powers := [(7, 1), (18, 1), (31, 1), (51, 1), (58, 1)] }],
  [{ coefficient := -2, powers := [(7, 1), (56, 1), (59, 1)] }, { coefficient := -2, powers := [(10, 1), (53, 1), (59, 1)] }, { coefficient := -2, powers := [(15, 1), (44, 1), (59, 1)] }, { coefficient := -2, powers := [(15, 1), (49, 1), (59, 1)] }],
  [{ coefficient := 2, powers := [(5, 1), (10, 1), (34, 1), (54, 1)] }, { coefficient := -2, powers := [(5, 1), (15, 1), (34, 1), (54, 1)] }, { coefficient := 2, powers := [(8, 1), (10, 1), (34, 1), (46, 1)] }, { coefficient := -2, powers := [(8, 1), (15, 1), (34, 1), (46, 1)] }],
  [{ coefficient := 2, powers := [(5, 1), (10, 1), (34, 1), (51, 1)] }, { coefficient := -2, powers := [(5, 1), (15, 1), (34, 1), (51, 1)] }, { coefficient := 2, powers := [(8, 1), (10, 1), (34, 1), (41, 1)] }, { coefficient := -2, powers := [(8, 1), (15, 1), (34, 1), (41, 1)] }],
  [{ coefficient := -2, powers := [(4, 1), (8, 1), (31, 1), (46, 1), (53, 1), (56, 1)] }, { coefficient := -2, powers := [(4, 1), (8, 1), (34, 1), (46, 1), (49, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (23, 1), (49, 1), (50, 1), (53, 1), (59, 1)] }, { coefficient := 1, powers := [(21, 1), (23, 1), (50, 1), (53, 2), (59, 1)] }, { coefficient := -1, powers := [(23, 1), (49, 1), (53, 1)] }, { coefficient := -1, powers := [(23, 1), (53, 2)] }],
  [{ coefficient := 2, powers := [(7, 1), (29, 1), (31, 1), (46, 1), (49, 1), (58, 1)] }],
  [{ coefficient := -2, powers := [(7, 1), (24, 1), (31, 1), (45, 1), (51, 1), (58, 1)] }, { coefficient := -2, powers := [(7, 1), (29, 1), (31, 1), (41, 1), (45, 1), (58, 1)] }, { coefficient := -2, powers := [(7, 1), (29, 1), (31, 1), (46, 1), (48, 1), (49, 1), (58, 1)] }, { coefficient := 2, powers := [(7, 1), (29, 1), (31, 1), (46, 1), (48, 1), (58, 2)] }],
  [{ coefficient := -2, powers := [(7, 1), (24, 1), (31, 1), (51, 1), (58, 1)] }, { coefficient := -2, powers := [(7, 1), (29, 1), (31, 1), (41, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (23, 1), (53, 1), (56, 1), (59, 1)] }, { coefficient := 2, powers := [(7, 1), (23, 1), (56, 1), (58, 1), (59, 1)] }, { coefficient := -2, powers := [(7, 1), (31, 1), (44, 1), (58, 1), (59, 1)] }, { coefficient := 1, powers := [(10, 1), (23, 1), (49, 1), (53, 1), (59, 1)] }, { coefficient := 1, powers := [(10, 1), (23, 1), (53, 2), (59, 1)] }, { coefficient := 2, powers := [(10, 1), (23, 1), (53, 1), (58, 1), (59, 1)] }, { coefficient := 2, powers := [(15, 1), (23, 1), (49, 1), (58, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (4, 1), (18, 1), (23, 1), (32, 1), (53, 1), (54, 1)] }, { coefficient := -1, powers := [(0, 1), (4, 1), (18, 1), (23, 1), (35, 1), (51, 1), (53, 1)] }, { coefficient := -1, powers := [(0, 1), (7, 1), (18, 1), (23, 1), (32, 1), (53, 1), (54, 1)] }, { coefficient := -1, powers := [(0, 1), (7, 1), (18, 1), (23, 1), (35, 1), (51, 1), (53, 1)] }, { coefficient := 1, powers := [(3, 1), (15, 1), (18, 1), (23, 1), (32, 1), (53, 1), (54, 1)] }, { coefficient := 1, powers := [(3, 1), (15, 1), (18, 1), (23, 1), (35, 1), (51, 1), (53, 1)] }, { coefficient := 2, powers := [(6, 1), (7, 1), (18, 1), (31, 1), (32, 1), (54, 1), (58, 1)] }, { coefficient := 2, powers := [(6, 1), (7, 1), (18, 1), (31, 1), (35, 1), (51, 1), (58, 1)] }, { coefficient := 1, powers := [(6, 1), (10, 1), (18, 1), (23, 1), (32, 1), (53, 1), (54, 1)] }, { coefficient := 1, powers := [(6, 1), (10, 1), (18, 1), (23, 1), (35, 1), (51, 1), (53, 1)] }, { coefficient := -2, powers := [(7, 1), (18, 1), (23, 1), (32, 1), (54, 1)] }, { coefficient := -2, powers := [(7, 1), (18, 1), (23, 1), (35, 1), (51, 1)] }, { coefficient := -1, powers := [(10, 1), (23, 1), (25, 1), (50, 1), (53, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (4, 1), (18, 1), (23, 1), (32, 1), (46, 1), (53, 1)] }, { coefficient := -1, powers := [(0, 1), (4, 1), (18, 1), (23, 1), (35, 1), (41, 1), (53, 1)] }, { coefficient := -1, powers := [(0, 1), (7, 1), (18, 1), (23, 1), (32, 1), (46, 1), (53, 1)] }, { coefficient := -1, powers := [(0, 1), (7, 1), (18, 1), (23, 1), (35, 1), (41, 1), (53, 1)] }, { coefficient := 1, powers := [(3, 1), (15, 1), (18, 1), (23, 1), (32, 1), (46, 1), (53, 1)] }, { coefficient := 1, powers := [(3, 1), (15, 1), (18, 1), (23, 1), (35, 1), (41, 1), (53, 1)] }, { coefficient := -2, powers := [(4, 1), (18, 1), (31, 1), (32, 1), (36, 1), (46, 1), (53, 1)] }, { coefficient := -2, powers := [(4, 1), (18, 1), (32, 1), (34, 1), (36, 1), (46, 1), (49, 1)] }, { coefficient := 2, powers := [(6, 1), (7, 1), (18, 1), (31, 1), (32, 1), (46, 1), (58, 1)] }, { coefficient := 2, powers := [(6, 1), (7, 1), (18, 1), (31, 1), (35, 1), (41, 1), (58, 1)] }, { coefficient := 1, powers := [(6, 1), (10, 1), (18, 1), (23, 1), (32, 1), (46, 1), (53, 1)] }, { coefficient := 1, powers := [(6, 1), (10, 1), (18, 1), (23, 1), (35, 1), (41, 1), (53, 1)] }, { coefficient := -2, powers := [(7, 1), (18, 1), (23, 1), (32, 1), (46, 1)] }, { coefficient := -2, powers := [(7, 1), (18, 1), (23, 1), (35, 1), (41, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (4, 1), (13, 1), (31, 1), (46, 1), (53, 1)] }, { coefficient := 2, powers := [(0, 1), (4, 1), (13, 1), (34, 1), (46, 1), (49, 1)] }, { coefficient := -2, powers := [(0, 1), (5, 1), (10, 1), (34, 1), (37, 1), (57, 1)] }, { coefficient := 2, powers := [(0, 1), (5, 1), (15, 1), (34, 1), (37, 1), (57, 1)] }, { coefficient := 2, powers := [(4, 1), (13, 1), (25, 1), (31, 1), (46, 1), (53, 1)] }, { coefficient := 2, powers := [(4, 1), (13, 1), (25, 1), (34, 1), (46, 1), (49, 1)] }, { coefficient := -2, powers := [(5, 1), (6, 1), (10, 1), (31, 1), (53, 1), (57, 1)] }, { coefficient := -2, powers := [(5, 1), (6, 1), (10, 1), (34, 1), (49, 1), (57, 1)] }, { coefficient := -2, powers := [(5, 1), (10, 1), (25, 1), (34, 1), (37, 1), (57, 1)] }, { coefficient := 2, powers := [(5, 1), (15, 1), (25, 1), (34, 1), (37, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (23, 1), (48, 1), (53, 1), (56, 1), (59, 1)] }, { coefficient := -2, powers := [(7, 1), (19, 1), (29, 1), (31, 1), (48, 1), (49, 1), (58, 1)] }, { coefficient := 2, powers := [(7, 1), (31, 1), (44, 1), (48, 1), (58, 1), (59, 1)] }, { coefficient := -1, powers := [(10, 1), (23, 1), (48, 1), (49, 1), (53, 1), (59, 1)] }, { coefficient := -2, powers := [(10, 1), (23, 1), (48, 1), (53, 2), (59, 1)] }, { coefficient := 2, powers := [(15, 1), (23, 1), (48, 1), (53, 1), (58, 1), (59, 1)] }],
  [{ coefficient := 2, powers := [(4, 1), (8, 1), (31, 1), (53, 1), (57, 1)] }, { coefficient := 2, powers := [(4, 1), (8, 1), (34, 1), (49, 1), (57, 1)] }, { coefficient := 2, powers := [(8, 1), (10, 1), (34, 1), (37, 1), (57, 1)] }, { coefficient := -2, powers := [(8, 1), (15, 1), (34, 1), (37, 1), (57, 1)] }],
  [{ coefficient := 2, powers := [(7, 1), (29, 1), (31, 1), (48, 1), (49, 1), (58, 1)] }, { coefficient := 2, powers := [(7, 1), (29, 1), (31, 1), (50, 1), (58, 1)] }],
  [{ coefficient := -2, powers := [(7, 1), (13, 1), (29, 1), (31, 1), (49, 1), (58, 1)] }, { coefficient := -2, powers := [(7, 1), (18, 1), (29, 1), (31, 1), (50, 1), (58, 1)] }],
  [{ coefficient := -2, powers := [(7, 1), (18, 1), (29, 1), (31, 1), (46, 1), (58, 2)] }],
  [{ coefficient := -2, powers := [(7, 1), (31, 1), (51, 1), (58, 1)] }],
  [{ coefficient := 2, powers := [(4, 1), (6, 1), (31, 1), (46, 1), (53, 1), (56, 1)] }, { coefficient := 2, powers := [(4, 1), (6, 1), (34, 1), (46, 1), (49, 1), (56, 1)] }, { coefficient := 2, powers := [(4, 1), (31, 1), (46, 1), (53, 1)] }, { coefficient := 2, powers := [(4, 1), (34, 1), (46, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (4, 1), (23, 1), (32, 1), (53, 1), (54, 1)] }, { coefficient := 1, powers := [(0, 1), (4, 1), (23, 1), (35, 1), (51, 1), (53, 1)] }, { coefficient := 1, powers := [(0, 1), (7, 1), (23, 1), (32, 1), (53, 1), (54, 1)] }, { coefficient := 1, powers := [(0, 1), (7, 1), (23, 1), (35, 1), (51, 1), (53, 1)] }, { coefficient := -1, powers := [(3, 1), (15, 1), (23, 1), (32, 1), (53, 1), (54, 1)] }, { coefficient := -1, powers := [(3, 1), (15, 1), (23, 1), (35, 1), (51, 1), (53, 1)] }, { coefficient := -2, powers := [(6, 1), (7, 1), (31, 1), (32, 1), (54, 1), (58, 1)] }, { coefficient := -2, powers := [(6, 1), (7, 1), (31, 1), (35, 1), (51, 1), (58, 1)] }, { coefficient := -1, powers := [(6, 1), (10, 1), (23, 1), (32, 1), (53, 1), (54, 1)] }, { coefficient := -1, powers := [(6, 1), (10, 1), (23, 1), (35, 1), (51, 1), (53, 1)] }, { coefficient := 2, powers := [(7, 1), (23, 1), (32, 1), (54, 1)] }, { coefficient := 2, powers := [(7, 1), (23, 1), (35, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (4, 1), (23, 1), (32, 1), (46, 1), (53, 1)] }, { coefficient := 1, powers := [(0, 1), (4, 1), (23, 1), (35, 1), (41, 1), (53, 1)] }, { coefficient := 1, powers := [(0, 1), (7, 1), (23, 1), (32, 1), (46, 1), (53, 1)] }, { coefficient := 1, powers := [(0, 1), (7, 1), (23, 1), (35, 1), (41, 1), (53, 1)] }, { coefficient := -1, powers := [(3, 1), (15, 1), (23, 1), (32, 1), (46, 1), (53, 1)] }, { coefficient := -1, powers := [(3, 1), (15, 1), (23, 1), (35, 1), (41, 1), (53, 1)] }, { coefficient := 2, powers := [(4, 1), (31, 1), (32, 1), (36, 1), (46, 1), (53, 1)] }, { coefficient := 2, powers := [(4, 1), (32, 1), (34, 1), (36, 1), (46, 1), (49, 1)] }, { coefficient := -2, powers := [(6, 1), (7, 1), (31, 1), (32, 1), (46, 1), (58, 1)] }, { coefficient := -2, powers := [(6, 1), (7, 1), (31, 1), (35, 1), (41, 1), (58, 1)] }, { coefficient := -1, powers := [(6, 1), (10, 1), (23, 1), (32, 1), (46, 1), (53, 1)] }, { coefficient := -1, powers := [(6, 1), (10, 1), (23, 1), (35, 1), (41, 1), (53, 1)] }, { coefficient := 2, powers := [(7, 1), (23, 1), (32, 1), (46, 1)] }, { coefficient := 2, powers := [(7, 1), (23, 1), (35, 1), (41, 1)] }],
  [{ coefficient := 2, powers := [(7, 1), (20, 1), (24, 1), (31, 1), (51, 1), (58, 1)] }, { coefficient := 2, powers := [(7, 1), (20, 1), (29, 1), (31, 1), (41, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (4, 1), (19, 1), (23, 1), (53, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (7, 1), (19, 1), (23, 1), (53, 1), (56, 1)] }, { coefficient := -1, powers := [(3, 1), (15, 1), (19, 1), (23, 1), (53, 1), (56, 1)] }, { coefficient := 2, powers := [(4, 1), (19, 1), (31, 1), (53, 1)] }, { coefficient := 2, powers := [(4, 1), (19, 1), (34, 1), (49, 1)] }, { coefficient := -2, powers := [(6, 1), (7, 1), (19, 1), (31, 1), (56, 1), (58, 1)] }, { coefficient := -1, powers := [(6, 1), (10, 1), (19, 1), (23, 1), (53, 1), (56, 1)] }, { coefficient := 2, powers := [(7, 1), (19, 1), (23, 1), (56, 1)] }, { coefficient := -2, powers := [(7, 1), (19, 1), (31, 1), (58, 1)] }, { coefficient := 2, powers := [(10, 1), (19, 1), (34, 1), (37, 1)] }, { coefficient := -2, powers := [(15, 1), (19, 1), (34, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (4, 1), (13, 1), (23, 1), (53, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (7, 1), (13, 1), (23, 1), (53, 1), (56, 1)] }, { coefficient := -1, powers := [(3, 1), (13, 1), (15, 1), (23, 1), (53, 1), (56, 1)] }, { coefficient := 2, powers := [(4, 1), (13, 1), (31, 1), (53, 1)] }, { coefficient := 2, powers := [(4, 1), (13, 1), (34, 1), (49, 1)] }, { coefficient := -2, powers := [(6, 1), (7, 1), (13, 1), (31, 1), (56, 1), (58, 1)] }, { coefficient := -1, powers := [(6, 1), (10, 1), (13, 1), (23, 1), (53, 1), (56, 1)] }, { coefficient := 2, powers := [(7, 1), (13, 1), (23, 1), (56, 1)] }, { coefficient := -2, powers := [(7, 1), (13, 1), (31, 1), (58, 1)] }, { coefficient := 2, powers := [(10, 1), (13, 1), (34, 1), (37, 1)] }, { coefficient := -2, powers := [(13, 1), (15, 1), (34, 1), (37, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (21, 1), (23, 1), (53, 1), (56, 1), (59, 1)] }, { coefficient := -2, powers := [(7, 1), (19, 1), (21, 1), (29, 1), (31, 1), (49, 1), (58, 1)] }, { coefficient := 2, powers := [(7, 1), (21, 1), (31, 1), (44, 1), (58, 1), (59, 1)] }, { coefficient := -1, powers := [(10, 1), (21, 1), (23, 1), (49, 1), (53, 1), (59, 1)] }, { coefficient := -2, powers := [(10, 1), (21, 1), (23, 1), (53, 2), (59, 1)] }, { coefficient := 2, powers := [(15, 1), (21, 1), (23, 1), (53, 1), (58, 1), (59, 1)] }],
  [{ coefficient := 2, powers := [(7, 1), (13, 1), (29, 1), (31, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (4, 1), (23, 1), (53, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (7, 1), (23, 1), (53, 1), (57, 1)] }, { coefficient := -1, powers := [(3, 1), (15, 1), (23, 1), (53, 1), (57, 1)] }, { coefficient := -2, powers := [(4, 1), (6, 1), (31, 1), (53, 1), (57, 1)] }, { coefficient := -2, powers := [(4, 1), (6, 1), (34, 1), (49, 1), (57, 1)] }, { coefficient := -2, powers := [(6, 1), (7, 1), (31, 1), (57, 1), (58, 1)] }, { coefficient := -1, powers := [(6, 1), (10, 1), (23, 1), (53, 1), (57, 1)] }, { coefficient := -2, powers := [(6, 1), (10, 1), (34, 1), (37, 1), (57, 1)] }, { coefficient := 2, powers := [(6, 1), (15, 1), (34, 1), (37, 1), (57, 1)] }, { coefficient := 2, powers := [(7, 1), (23, 1), (57, 1)] }],
  [{ coefficient := 2, powers := [(5, 1), (6, 1), (31, 1), (53, 1), (57, 1)] }, { coefficient := 2, powers := [(5, 1), (6, 1), (34, 1), (49, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (23, 1), (50, 1), (53, 1), (59, 1)] }, { coefficient := -2, powers := [(23, 1), (48, 1), (58, 1), (59, 1)] }],
  [{ coefficient := 2, powers := [(7, 1), (24, 1), (31, 1), (51, 1), (58, 1)] }, { coefficient := 2, powers := [(7, 1), (29, 1), (31, 1), (41, 1), (58, 1)] }],
  [{ coefficient := -2, powers := [(7, 1), (29, 1), (31, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (23, 1), (53, 1), (59, 1)] }, { coefficient := -2, powers := [(15, 1), (23, 1), (58, 1), (59, 1)] }],
  [{ coefficient := 2, powers := [(7, 1), (18, 1), (29, 1), (31, 1), (58, 1)] }],
  [{ coefficient := 2, powers := [(23, 1), (41, 1), (58, 1), (59, 1)] }, { coefficient := -1, powers := [(23, 1), (53, 1)] }],
  [{ coefficient := 2, powers := [(5, 1), (31, 1), (53, 1)] }, { coefficient := 2, powers := [(5, 1), (34, 1), (49, 1)] }],
  [{ coefficient := -1, powers := [(21, 1), (23, 1), (50, 1), (53, 1), (59, 1)] }],
  [{ coefficient := -2, powers := [(8, 1), (31, 1), (58, 1)] }],
  [{ coefficient := -2, powers := [(4, 1), (13, 1), (29, 1), (31, 1), (46, 1), (53, 1)] }, { coefficient := -2, powers := [(4, 1), (13, 1), (29, 1), (34, 1), (46, 1), (49, 1)] }, { coefficient := 1, powers := [(4, 1), (21, 1), (23, 1), (48, 1), (53, 1), (56, 1), (59, 1)] }, { coefficient := 2, powers := [(5, 1), (10, 1), (29, 1), (34, 1), (37, 1), (57, 1)] }, { coefficient := -2, powers := [(5, 1), (15, 1), (29, 1), (34, 1), (37, 1), (57, 1)] }, { coefficient := 2, powers := [(7, 1), (19, 1), (21, 1), (29, 1), (31, 1), (48, 1), (49, 1), (58, 1)] }, { coefficient := -2, powers := [(7, 1), (21, 1), (31, 1), (44, 1), (48, 1), (58, 1), (59, 1)] }, { coefficient := 2, powers := [(7, 1), (31, 1), (58, 1)] }, { coefficient := 1, powers := [(10, 1), (21, 1), (23, 1), (48, 1), (49, 1), (53, 1), (59, 1)] }, { coefficient := 2, powers := [(10, 1), (21, 1), (23, 1), (48, 1), (53, 2), (59, 1)] }, { coefficient := 1, powers := [(10, 1), (23, 1), (53, 1)] }, { coefficient := -2, powers := [(15, 1), (21, 1), (23, 1), (48, 1), (53, 1), (58, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(15, 1), (23, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (23, 1), (53, 1)] }, { coefficient := -2, powers := [(23, 1), (25, 1), (41, 1), (58, 1), (59, 1)] }, { coefficient := 2, powers := [(28, 1)] }],
  [{ coefficient := 2, powers := [(15, 1)] }],
  [{ coefficient := -2, powers := [] }],
  [{ coefficient := -1, powers := [(0, 1), (4, 1), (23, 1), (53, 1), (56, 1)] }, { coefficient := -1, powers := [(0, 1), (7, 1), (23, 1), (53, 1), (56, 1)] }, { coefficient := 1, powers := [(3, 1), (15, 1), (23, 1), (53, 1), (56, 1)] }, { coefficient := -2, powers := [(4, 1), (31, 1), (53, 1)] }, { coefficient := -2, powers := [(4, 1), (34, 1), (49, 1)] }, { coefficient := 2, powers := [(6, 1), (7, 1), (31, 1), (56, 1), (58, 1)] }, { coefficient := 1, powers := [(6, 1), (10, 1), (23, 1), (53, 1), (56, 1)] }, { coefficient := -2, powers := [(7, 1), (23, 1), (56, 1)] }, { coefficient := 2, powers := [(7, 1), (31, 1), (58, 1)] }, { coefficient := -2, powers := [(10, 1), (34, 1), (37, 1)] }, { coefficient := 2, powers := [(15, 1), (34, 1), (37, 1)] }],
  [{ coefficient := 2, powers := [(7, 1), (18, 1), (29, 1), (31, 1), (46, 1), (48, 1), (58, 1)] }, { coefficient := -2, powers := [(7, 1), (31, 1), (44, 1)] }, { coefficient := 2, powers := [(15, 1), (23, 1), (53, 1)] }],
  [{ coefficient := 2, powers := [(37, 1), (56, 1)] }, { coefficient := 2, powers := [(44, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (4, 1), (23, 1), (41, 1), (53, 1), (54, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (4, 1), (23, 1), (46, 1), (51, 1), (53, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (7, 1), (23, 1), (41, 1), (53, 1), (54, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (7, 1), (23, 1), (46, 1), (51, 1), (53, 1), (56, 1)] }, { coefficient := -1, powers := [(3, 1), (15, 1), (23, 1), (41, 1), (53, 1), (54, 1), (56, 1)] }, { coefficient := -1, powers := [(3, 1), (15, 1), (23, 1), (46, 1), (51, 1), (53, 1), (56, 1)] }, { coefficient := 2, powers := [(4, 1), (6, 1), (31, 1), (38, 1), (53, 1), (56, 1), (57, 1)] }, { coefficient := -2, powers := [(4, 1), (6, 1), (31, 1), (46, 1), (51, 1), (53, 1), (56, 1)] }, { coefficient := 2, powers := [(4, 1), (6, 1), (34, 1), (38, 1), (49, 1), (56, 1), (57, 1)] }, { coefficient := -2, powers := [(4, 1), (6, 1), (34, 1), (46, 1), (49, 1), (51, 1), (56, 1)] }, { coefficient := 2, powers := [(4, 1), (31, 1), (38, 1), (53, 1), (57, 1)] }, { coefficient := 2, powers := [(4, 1), (31, 1), (41, 1), (53, 1), (54, 1)] }, { coefficient := 2, powers := [(4, 1), (34, 1), (38, 1), (49, 1), (57, 1)] }, { coefficient := 2, powers := [(4, 1), (34, 1), (41, 1), (49, 1), (54, 1)] }, { coefficient := -2, powers := [(6, 1), (7, 1), (31, 1), (41, 1), (54, 1), (56, 1), (58, 1)] }, { coefficient := -2, powers := [(6, 1), (7, 1), (31, 1), (46, 1), (51, 1), (56, 1), (58, 1)] }, { coefficient := -1, powers := [(6, 1), (10, 1), (23, 1), (41, 1), (53, 1), (54, 1), (56, 1)] }, { coefficient := -1, powers := [(6, 1), (10, 1), (23, 1), (46, 1), (51, 1), (53, 1), (56, 1)] }, { coefficient := 2, powers := [(6, 1), (10, 1), (34, 1), (37, 1), (38, 1), (56, 1), (57, 1)] }, { coefficient := -2, powers := [(6, 1), (15, 1), (34, 1), (37, 1), (38, 1), (56, 1), (57, 1)] }, { coefficient := 2, powers := [(7, 1), (23, 1), (41, 1), (54, 1), (56, 1)] }, { coefficient := 2, powers := [(7, 1), (23, 1), (46, 1), (51, 1), (56, 1)] }, { coefficient := -2, powers := [(7, 1), (31, 1), (38, 1), (57, 1), (58, 1)] }, { coefficient := -2, powers := [(7, 1), (31, 1), (41, 1), (54, 1), (58, 1)] }, { coefficient := 2, powers := [(10, 1), (34, 1), (37, 1), (38, 1), (57, 1)] }, { coefficient := 2, powers := [(10, 1), (34, 1), (37, 1), (41, 1), (54, 1)] }, { coefficient := 2, powers := [(10, 1), (34, 1), (37, 1), (46, 1), (51, 1)] }, { coefficient := -2, powers := [(15, 1), (34, 1), (37, 1), (38, 1), (57, 1)] }, { coefficient := -2, powers := [(15, 1), (34, 1), (37, 1), (41, 1), (54, 1)] }, { coefficient := -2, powers := [(15, 1), (34, 1), (37, 1), (46, 1), (51, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (4, 1), (13, 1), (29, 1), (31, 1), (46, 1), (53, 1)] }, { coefficient := -2, powers := [(0, 1), (4, 1), (13, 1), (29, 1), (34, 1), (46, 1), (49, 1)] }, { coefficient := 2, powers := [(0, 1), (5, 1), (10, 1), (29, 1), (34, 1), (37, 1), (57, 1)] }, { coefficient := -2, powers := [(0, 1), (5, 1), (15, 1), (29, 1), (34, 1), (37, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (15, 1), (23, 1), (53, 1)] }, { coefficient := 2, powers := [(1, 1), (53, 1)] }, { coefficient := -1, powers := [(4, 1), (21, 1), (23, 1), (25, 1), (48, 1), (53, 1), (56, 1), (59, 1)] }, { coefficient := 2, powers := [(5, 1), (6, 1), (10, 1), (29, 1), (31, 1), (53, 1), (57, 1)] }, { coefficient := 2, powers := [(5, 1), (6, 1), (10, 1), (29, 1), (34, 1), (49, 1), (57, 1)] }, { coefficient := -2, powers := [(5, 1), (6, 1), (15, 1), (29, 1), (31, 1), (53, 1), (57, 1)] }, { coefficient := -2, powers := [(5, 1), (6, 1), (15, 1), (29, 1), (34, 1), (49, 1), (57, 1)] }, { coefficient := -2, powers := [(7, 1), (19, 1), (20, 1), (24, 1), (31, 1), (51, 1), (58, 1)] }, { coefficient := -2, powers := [(7, 1), (19, 1), (20, 1), (29, 1), (31, 1), (41, 1), (58, 1)] }, { coefficient := -2, powers := [(7, 1), (19, 1), (21, 1), (25, 1), (29, 1), (31, 1), (48, 1), (49, 1), (58, 1)] }, { coefficient := -2, powers := [(7, 1), (19, 1), (24, 1), (25, 1), (31, 1), (51, 1), (58, 1)] }, { coefficient := -2, powers := [(7, 1), (19, 1), (25, 1), (29, 1), (31, 1), (41, 1), (58, 1)] }, { coefficient := 2, powers := [(7, 1), (21, 1), (25, 1), (31, 1), (44, 1), (48, 1), (58, 1), (59, 1)] }, { coefficient := -2, powers := [(7, 1), (25, 1), (31, 1), (58, 1)] }, { coefficient := 2, powers := [(7, 1), (34, 1)] }, { coefficient := -1, powers := [(10, 1), (21, 1), (23, 1), (25, 1), (48, 1), (49, 1), (53, 1), (59, 1)] }, { coefficient := -2, powers := [(10, 1), (21, 1), (23, 1), (25, 1), (48, 1), (53, 2), (59, 1)] }, { coefficient := -1, powers := [(10, 1), (23, 1), (25, 1), (53, 1)] }, { coefficient := 2, powers := [(15, 1), (21, 1), (23, 1), (25, 1), (48, 1), (53, 1), (58, 1), (59, 1)] }, { coefficient := 1, powers := [(15, 1), (23, 1), (25, 1), (53, 1)] }, { coefficient := -2, powers := [(15, 1), (28, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (10, 1), (23, 1), (53, 2)] }, { coefficient := 2, powers := [(0, 1), (15, 1), (23, 1), (53, 1), (58, 1)] }, { coefficient := -1, powers := [(4, 1), (23, 1), (25, 1), (53, 1), (56, 1)] }, { coefficient := 2, powers := [(7, 1), (25, 1), (31, 1), (44, 1), (58, 1)] }, { coefficient := 2, powers := [(7, 1), (28, 1), (56, 1)] }, { coefficient := -1, powers := [(10, 1), (23, 1), (25, 1), (49, 1), (53, 1)] }, { coefficient := -1, powers := [(10, 1), (23, 1), (25, 1), (53, 2)] }, { coefficient := -1, powers := [(10, 1), (23, 1), (53, 1)] }, { coefficient := 2, powers := [(10, 1), (28, 1), (53, 1)] }, { coefficient := 2, powers := [(15, 1), (28, 1), (44, 1)] }, { coefficient := 2, powers := [(15, 1), (28, 1), (49, 1)] }]
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
    (values : Fin 60 → R) :
    ¬ ∀ index : Fin 54,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((2 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (2 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (2 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component55.SelectedLeafB4_1.selectedHasNoCommonZero

end Krenn.Component55.SelectedLeafB4_1
