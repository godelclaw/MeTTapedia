import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component39.SelectedLeafB4_6_3_6

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "6fdec429b93de9296adfe43a7d113c068b5faa0ceb4cf589b335b63f7099cc95"
def certificateSHA256 : String := "5065b9c52eb608ee7c89a6a7d98bd5e880b401f086da2b7d7eef51ff9381b6b0"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 35 → Fin 673 := ![
  11,
  14,
  22,
  26,
  29,
  191,
  192,
  193,
  232,
  280,
  304,
  305,
  307,
  353,
  360,
  419,
  425,
  461,
  476,
  478,
  511,
  566,
  574,
  581,
  602,
  659,
  660,
  662,
  663,
  664,
  666,
  669,
  670,
  671,
  672
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 35 → SparsePoly (Fin 68) := ![
  [{ coefficient := 1, powers := [(8, 1), (30, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (54, 1)] }, { coefficient := 1, powers := [(28, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (42, 1)] }, { coefficient := 1, powers := [(26, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (53, 1)] }, { coefficient := 1, powers := [(28, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (24, 1), (45, 1)] }, { coefficient := 1, powers := [(10, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (42, 1), (53, 1)] }, { coefficient := 1, powers := [(20, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (44, 1)] }, { coefficient := 1, powers := [(4, 1), (33, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (51, 1)] }, { coefficient := 1, powers := [(7, 1), (30, 1)] }, { coefficient := 1, powers := [(10, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (29, 1)] }, { coefficient := 1, powers := [(14, 1), (18, 1), (50, 1)] }, { coefficient := 1, powers := [(14, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (33, 1), (50, 1)] }, { coefficient := 1, powers := [(9, 1), (25, 1)] }, { coefficient := 1, powers := [(25, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (30, 1), (57, 1)] }, { coefficient := 1, powers := [(8, 1), (30, 1), (47, 1)] }, { coefficient := 1, powers := [(17, 1), (30, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (47, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1)] }, { coefficient := 1, powers := [(16, 1), (26, 1), (47, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1)] }, { coefficient := 1, powers := [(12, 1), (28, 1)] }, { coefficient := 1, powers := [(16, 1), (21, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1), (50, 1)] }, { coefficient := 1, powers := [(9, 1), (45, 1)] }, { coefficient := 1, powers := [(29, 1), (36, 1), (42, 1)] }, { coefficient := 1, powers := [(42, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (38, 1), (56, 1)] }, { coefficient := 1, powers := [(1, 1), (50, 1)] }, { coefficient := 1, powers := [(7, 1), (33, 1), (38, 1)] }, { coefficient := 1, powers := [(14, 1), (25, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (39, 1), (57, 1)] }, { coefficient := 1, powers := [(1, 1), (45, 1), (53, 1)] }, { coefficient := 1, powers := [(4, 1), (30, 1), (57, 1)] }, { coefficient := 1, powers := [(10, 1), (20, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (23, 1), (59, 1)] }, { coefficient := 1, powers := [(10, 1), (23, 1), (44, 1)] }, { coefficient := 1, powers := [(14, 1), (23, 1), (39, 1)] }, { coefficient := 1, powers := [(14, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (42, 1), (53, 1)] }, { coefficient := 1, powers := [(22, 1), (57, 1)] }, { coefficient := 1, powers := [(28, 1), (47, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (24, 1), (45, 1), (50, 1)] }, { coefficient := 1, powers := [(9, 1), (24, 1), (45, 1)] }, { coefficient := 1, powers := [(9, 1), (57, 1)] }, { coefficient := 1, powers := [(24, 1), (42, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (51, 1)] }, { coefficient := 1, powers := [(3, 1), (59, 1)] }, { coefficient := 1, powers := [(18, 1), (51, 1)] }, { coefficient := 1, powers := [(18, 1), (56, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(4, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (59, 1)] }, { coefficient := 1, powers := [(10, 1), (44, 1)] }, { coefficient := 1, powers := [(10, 1), (56, 1)] }, { coefficient := 1, powers := [(14, 1), (39, 1)] }, { coefficient := 1, powers := [(14, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (36, 1), (59, 1)] }, { coefficient := 1, powers := [(1, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(1, 1), (44, 1), (51, 1)] }, { coefficient := 1, powers := [(4, 1), (25, 1), (59, 1)] }, { coefficient := 1, powers := [(4, 1), (30, 1), (56, 1)] }, { coefficient := 1, powers := [(4, 1), (33, 1), (51, 1)] }, { coefficient := 1, powers := [(7, 1), (20, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (30, 1), (44, 1)] }, { coefficient := 1, powers := [(7, 1), (33, 1), (39, 1)] }, { coefficient := 1, powers := [(10, 1), (20, 1), (56, 1)] }, { coefficient := 1, powers := [(10, 1), (25, 1), (44, 1)] }, { coefficient := 1, powers := [(10, 1), (33, 1), (36, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1), (51, 1)] }, { coefficient := 1, powers := [(14, 1), (25, 1), (39, 1)] }, { coefficient := 1, powers := [(14, 1), (30, 1), (36, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (37, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (47, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (28, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (22, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1), (47, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (40, 1)] }, { coefficient := 1, powers := [(12, 1), (22, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1), (28, 1), (47, 1)] }, { coefficient := 1, powers := [(12, 1), (34, 1), (37, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (54, 1)] }, { coefficient := 1, powers := [(17, 1), (28, 1), (40, 1)] }, { coefficient := 1, powers := [(17, 1), (31, 1), (37, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1)] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(38, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(40, 1)] }],
  [{ coefficient := 1, powers := [(57, 1), (65, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(23, 1), (66, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(25, 1), (67, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(28, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 35 → SparsePoly (Fin 68) := ![
  [{ coefficient := 1, powers := [(9, 1), (14, 1), (22, 1), (36, 1), (60, 1), (62, 1)] }, { coefficient := -1, powers := [(9, 1), (14, 1), (31, 1), (36, 1), (47, 1), (62, 1)] }, { coefficient := 1, powers := [(14, 1), (22, 1), (36, 1), (38, 1), (60, 1), (62, 1)] }, { coefficient := -1, powers := [(14, 1), (31, 1), (36, 1), (38, 1), (47, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (20, 1), (24, 1), (56, 1), (62, 1), (65, 1)] }, { coefficient := -1, powers := [(9, 1), (24, 1), (33, 1), (36, 1), (62, 1), (65, 1)] }, { coefficient := 1, powers := [(20, 1), (24, 1), (38, 1), (56, 1), (62, 1), (65, 1)] }, { coefficient := -1, powers := [(24, 1), (33, 1), (36, 1), (38, 1), (62, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (14, 1), (22, 1), (30, 1), (36, 1), (42, 1), (54, 1), (62, 1), (67, 1)] }, { coefficient := 1, powers := [(14, 1), (22, 1), (30, 1), (36, 1), (38, 1), (42, 1), (54, 1), (62, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (14, 1), (42, 1), (50, 1), (51, 1), (62, 1), (65, 1)] }, { coefficient := -1, powers := [(7, 1), (29, 1), (42, 1), (51, 1), (62, 1), (65, 1)] }, { coefficient := -1, powers := [(7, 1), (29, 1), (42, 1), (56, 1), (62, 1), (65, 1)] }, { coefficient := 1, powers := [(9, 1), (14, 1), (42, 1), (51, 1), (62, 1), (65, 1)] }, { coefficient := -1, powers := [(9, 1), (14, 1), (42, 1), (62, 1), (65, 1), (66, 1)] }, { coefficient := -1, powers := [(14, 1), (38, 1), (42, 1), (56, 1), (62, 1), (65, 1)] }, { coefficient := -1, powers := [(14, 1), (38, 1), (42, 1), (62, 1), (65, 1), (66, 1)] }, { coefficient := 1, powers := [(14, 1), (42, 1), (50, 1), (62, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(24, 1), (29, 1), (36, 1), (62, 1), (65, 1), (67, 1)] }],
  [{ coefficient := -1, powers := [(9, 1), (14, 1), (16, 1), (30, 1), (36, 1), (47, 1), (62, 1)] }, { coefficient := -1, powers := [(14, 1), (16, 1), (30, 1), (36, 1), (38, 1), (47, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(9, 1), (14, 1), (16, 1), (30, 1), (36, 1), (54, 1), (62, 1)] }, { coefficient := -1, powers := [(14, 1), (16, 1), (30, 1), (36, 1), (38, 1), (54, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(9, 1), (12, 1), (14, 1), (30, 1), (36, 1), (42, 1), (62, 1)] }, { coefficient := -1, powers := [(12, 1), (14, 1), (30, 1), (36, 1), (38, 1), (42, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(9, 1), (20, 1), (56, 1), (62, 1), (65, 1)] }, { coefficient := 1, powers := [(9, 1), (33, 1), (36, 1), (62, 1), (65, 1)] }, { coefficient := -1, powers := [(20, 1), (38, 1), (56, 1), (62, 1), (65, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1), (38, 1), (62, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (14, 1), (50, 1), (51, 1), (62, 1), (65, 1)] }, { coefficient := 1, powers := [(7, 1), (29, 1), (51, 1), (62, 1), (65, 1)] }, { coefficient := 1, powers := [(7, 1), (29, 1), (56, 1), (62, 1), (65, 1)] }, { coefficient := -1, powers := [(9, 1), (14, 1), (51, 1), (62, 1), (65, 1)] }, { coefficient := 1, powers := [(9, 1), (14, 1), (62, 1), (65, 1), (66, 1)] }, { coefficient := 1, powers := [(14, 1), (38, 1), (56, 1), (62, 1), (65, 1)] }, { coefficient := 1, powers := [(14, 1), (38, 1), (62, 1), (65, 1), (66, 1)] }, { coefficient := -1, powers := [(14, 1), (50, 1), (62, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (50, 1), (51, 1), (62, 1)] }, { coefficient := 1, powers := [(9, 1), (51, 1), (62, 1)] }, { coefficient := 1, powers := [(18, 1), (50, 1), (51, 1), (62, 1)] }, { coefficient := 1, powers := [(18, 1), (50, 1), (56, 1), (62, 1)] }, { coefficient := 1, powers := [(38, 1), (51, 1), (62, 1)] }, { coefficient := 1, powers := [(50, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (44, 1), (62, 1)] }, { coefficient := 1, powers := [(38, 1), (44, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(20, 1), (51, 1), (62, 1)] }, { coefficient := -1, powers := [(20, 1), (56, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (59, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (14, 1), (31, 1), (36, 1), (62, 1)] }, { coefficient := 1, powers := [(14, 1), (31, 1), (36, 1), (38, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (14, 1), (30, 1), (36, 1), (54, 1), (62, 1)] }, { coefficient := 1, powers := [(14, 1), (30, 1), (36, 1), (38, 1), (54, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (14, 1), (30, 1), (36, 1), (47, 1), (62, 1)] }, { coefficient := 1, powers := [(14, 1), (30, 1), (36, 1), (38, 1), (47, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (62, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (39, 1), (62, 2)] }, { coefficient := 1, powers := [(38, 1), (39, 1), (62, 2)] }],
  [{ coefficient := 1, powers := [(9, 1), (56, 1), (62, 1), (65, 1)] }, { coefficient := 1, powers := [(38, 1), (56, 1), (62, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(9, 1), (20, 1), (62, 1), (66, 1)] }, { coefficient := -1, powers := [(20, 1), (38, 1), (62, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (12, 1), (14, 1), (30, 1), (36, 1), (62, 1)] }, { coefficient := 1, powers := [(12, 1), (14, 1), (30, 1), (36, 1), (38, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(62, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (33, 1), (50, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (20, 1), (23, 1), (62, 1), (66, 1)] }, { coefficient := 1, powers := [(20, 1), (23, 1), (38, 1), (62, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(9, 1), (62, 1)] }, { coefficient := -1, powers := [(38, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(9, 1), (14, 1), (30, 1), (36, 1), (62, 1)] }, { coefficient := -1, powers := [(14, 1), (30, 1), (36, 1), (38, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (44, 1), (50, 1), (51, 1), (62, 1)] }, { coefficient := 1, powers := [(9, 1), (36, 1), (59, 1), (62, 1)] }, { coefficient := -1, powers := [(9, 1), (38, 1), (39, 1), (56, 1), (62, 2)] }, { coefficient := -1, powers := [(9, 1), (39, 1), (50, 1), (62, 2)] }, { coefficient := -1, powers := [(9, 1), (39, 1), (56, 1), (57, 1), (62, 1), (65, 1)] }, { coefficient := 1, powers := [(9, 1), (39, 1), (56, 1), (62, 1)] }, { coefficient := -1, powers := [(9, 1), (44, 1), (51, 1), (62, 1)] }, { coefficient := -1, powers := [(9, 1), (45, 1), (53, 1), (56, 1), (62, 1), (65, 1)] }, { coefficient := -1, powers := [(18, 1), (44, 1), (50, 1), (51, 1), (62, 1)] }, { coefficient := -1, powers := [(18, 1), (44, 1), (50, 1), (56, 1), (62, 1)] }, { coefficient := 1, powers := [(36, 1), (38, 1), (59, 1), (62, 1)] }, { coefficient := -1, powers := [(38, 2), (39, 1), (56, 1), (62, 2)] }, { coefficient := -1, powers := [(38, 1), (39, 1), (50, 1), (62, 2)] }, { coefficient := -1, powers := [(38, 1), (39, 1), (56, 1), (57, 1), (62, 1), (65, 1)] }, { coefficient := 1, powers := [(38, 1), (39, 1), (56, 1), (62, 1)] }, { coefficient := -1, powers := [(38, 1), (44, 1), (51, 1), (62, 1)] }, { coefficient := -1, powers := [(38, 1), (45, 1), (53, 1), (56, 1), (62, 1), (65, 1)] }, { coefficient := -1, powers := [(44, 1), (50, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (14, 1), (30, 1), (36, 1), (37, 1), (60, 1), (62, 1)] }, { coefficient := 1, powers := [(9, 1), (14, 1), (30, 1), (36, 1), (40, 1), (57, 1), (62, 1)] }, { coefficient := -1, powers := [(9, 1), (14, 1), (30, 1), (36, 1), (47, 1), (54, 1), (62, 1)] }, { coefficient := 1, powers := [(14, 1), (30, 1), (36, 1), (37, 1), (38, 1), (60, 1), (62, 1)] }, { coefficient := 1, powers := [(14, 1), (30, 1), (36, 1), (38, 1), (40, 1), (57, 1), (62, 1)] }, { coefficient := -1, powers := [(14, 1), (30, 1), (36, 1), (38, 1), (47, 1), (54, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (9, 1), (33, 1), (39, 1), (62, 1)] }, { coefficient := -1, powers := [(7, 1), (33, 1), (38, 1), (39, 1), (62, 1)] }, { coefficient := -1, powers := [(9, 1), (14, 1), (25, 1), (39, 1), (62, 1)] }, { coefficient := -1, powers := [(14, 1), (25, 1), (38, 1), (39, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(8, 1), (9, 1), (14, 1), (30, 1), (34, 1), (36, 1), (62, 1)] }, { coefficient := 1, powers := [(8, 1), (14, 1), (30, 1), (34, 1), (36, 1), (38, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (14, 1), (20, 1), (50, 1), (51, 1), (62, 1)] }, { coefficient := -1, powers := [(4, 1), (9, 1), (30, 1), (56, 1), (62, 1)] }, { coefficient := -1, powers := [(4, 1), (30, 1), (38, 1), (56, 1), (62, 1)] }, { coefficient := -1, powers := [(7, 1), (20, 1), (29, 1), (51, 1), (62, 1)] }, { coefficient := -1, powers := [(7, 1), (20, 1), (29, 1), (56, 1), (62, 1)] }, { coefficient := -1, powers := [(9, 1), (10, 1), (33, 1), (36, 1), (62, 1)] }, { coefficient := 1, powers := [(9, 1), (14, 1), (20, 1), (51, 1), (62, 1)] }, { coefficient := -1, powers := [(9, 1), (14, 1), (20, 1), (62, 1), (66, 1)] }, { coefficient := 1, powers := [(9, 1), (62, 1)] }, { coefficient := -1, powers := [(10, 1), (33, 1), (36, 1), (38, 1), (62, 1)] }, { coefficient := -1, powers := [(14, 1), (20, 1), (38, 1), (56, 1), (62, 1)] }, { coefficient := -1, powers := [(14, 1), (20, 1), (38, 1), (62, 1), (66, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1), (50, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (9, 1), (20, 1), (59, 1), (62, 1)] }, { coefficient := -1, powers := [(7, 1), (20, 1), (38, 1), (59, 1), (62, 1)] }, { coefficient := -1, powers := [(9, 1), (10, 1), (20, 1), (56, 1), (62, 1)] }, { coefficient := -1, powers := [(9, 1), (14, 1), (20, 1), (51, 1), (62, 1)] }, { coefficient := -1, powers := [(10, 1), (20, 1), (38, 1), (56, 1), (62, 1)] }, { coefficient := -1, powers := [(14, 1), (20, 1), (38, 1), (51, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(9, 1), (14, 1), (16, 1), (22, 1), (30, 1), (36, 1), (42, 1), (54, 1), (62, 1)] }, { coefficient := -1, powers := [(14, 1), (16, 1), (22, 1), (30, 1), (36, 1), (38, 1), (42, 1), (54, 1), (62, 1)] }, { coefficient := 1, powers := [(24, 1), (29, 1), (36, 1), (42, 1), (62, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (9, 1), (14, 1), (30, 1), (36, 1), (60, 1), (62, 1)] }, { coefficient := 1, powers := [(5, 1), (14, 1), (30, 1), (36, 1), (38, 1), (60, 1), (62, 1)] }, { coefficient := 1, powers := [(9, 1), (12, 1), (14, 1), (30, 1), (36, 1), (42, 1), (46, 1), (62, 1)] }, { coefficient := -1, powers := [(9, 1), (12, 1), (14, 1), (30, 1), (36, 1), (47, 1), (62, 1)] }, { coefficient := 1, powers := [(9, 1), (14, 1), (16, 1), (30, 1), (36, 1), (47, 1), (49, 1), (62, 1)] }, { coefficient := 1, powers := [(9, 1), (14, 1), (17, 1), (30, 1), (36, 1), (40, 1), (62, 1)] }, { coefficient := 1, powers := [(12, 1), (14, 1), (30, 1), (36, 1), (38, 1), (42, 1), (46, 1), (62, 1)] }, { coefficient := -1, powers := [(12, 1), (14, 1), (30, 1), (36, 1), (38, 1), (47, 1), (62, 1)] }, { coefficient := 1, powers := [(14, 1), (16, 1), (30, 1), (36, 1), (38, 1), (47, 1), (49, 1), (62, 1)] }, { coefficient := 1, powers := [(14, 1), (17, 1), (30, 1), (36, 1), (38, 1), (40, 1), (62, 1)] }]
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
    (values : Fin 68 → R) :
    ¬ ∀ index : Fin 35,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component39.SelectedLeafB4_6_3_6.selectedHasNoCommonZero

end Krenn.Component39.SelectedLeafB4_6_3_6
