import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component13.SelectedLeafB4_1

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "6226771427fcc7d07049a4e7db0e534a18bd4324a56be8c76c16f4ae83f9769b"
def certificateSHA256 : String := "9f18bed7b53aafd21ca127ace8856a7f8a243f0a253100fbddad0d6db37de0a0"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 34 → Fin 611 := ![
  1,
  3,
  11,
  17,
  19,
  24,
  150,
  151,
  152,
  162,
  173,
  189,
  251,
  325,
  360,
  361,
  371,
  372,
  376,
  381,
  432,
  480,
  483,
  525,
  532,
  544,
  545,
  550,
  602,
  604,
  607,
  608,
  609,
  610
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 34 → SparsePoly (Fin 60) := ![
  [{ coefficient := 1, powers := [(5, 1), (31, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (28, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(31, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1)] }, { coefficient := 1, powers := [(23, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1)] }, { coefficient := 1, powers := [(23, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (50, 1)] }, { coefficient := 1, powers := [(18, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (56, 1)] }, { coefficient := 1, powers := [(16, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (18, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1)] }],
  [{ coefficient := 1, powers := [(38, 1), (41, 1)] }, { coefficient := 1, powers := [(41, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (28, 1), (42, 1)] }, { coefficient := 1, powers := [(8, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (23, 1), (38, 1)] }, { coefficient := 1, powers := [(17, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1), (45, 1)] }, { coefficient := 1, powers := [(17, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1), (54, 1)] }, { coefficient := 1, powers := [(17, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (38, 1), (54, 1)] }, { coefficient := 1, powers := [(41, 1), (50, 1)] }, { coefficient := 1, powers := [(54, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (39, 1), (52, 1)] }, { coefficient := 1, powers := [(6, 1), (31, 1), (39, 1)] }, { coefficient := 1, powers := [(13, 1), (23, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (41, 1), (49, 1)] }, { coefficient := 1, powers := [(18, 1), (41, 1), (49, 1)] }, { coefficient := 1, powers := [(41, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1), (47, 1)] }, { coefficient := 1, powers := [(23, 1), (39, 1)] }, { coefficient := 1, powers := [(23, 1), (44, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (31, 1), (51, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1), (39, 1)] }, { coefficient := 1, powers := [(12, 1), (31, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (45, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1)] }, { coefficient := 1, powers := [(16, 1), (26, 1), (45, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (51, 1)] }, { coefficient := 1, powers := [(8, 1), (30, 1)] }, { coefficient := 1, powers := [(12, 1), (27, 1)] }, { coefficient := 1, powers := [(16, 1), (21, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (41, 1), (50, 1)] }, { coefficient := 1, powers := [(22, 1), (54, 1)] }, { coefficient := 1, powers := [(27, 1), (45, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1)] }, { coefficient := 1, powers := [(6, 1), (56, 1)] }, { coefficient := 1, powers := [(23, 1), (38, 1)] }, { coefficient := 1, powers := [(23, 1), (43, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (40, 1)] }, { coefficient := 1, powers := [(3, 1), (31, 1)] }, { coefficient := 1, powers := [(13, 1), (18, 1)] }, { coefficient := 1, powers := [(18, 1), (52, 1)] }, { coefficient := 1, powers := [(23, 1), (40, 1)] }, { coefficient := 1, powers := [(31, 1), (34, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1)] }, { coefficient := 1, powers := [(6, 1), (28, 1)] }, { coefficient := 1, powers := [(9, 1), (23, 1)] }, { coefficient := 1, powers := [(18, 1), (46, 1)] }, { coefficient := 1, powers := [(23, 1), (37, 1)] }, { coefficient := 1, powers := [(28, 1), (34, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (34, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1)] }, { coefficient := 1, powers := [(3, 1), (23, 1), (56, 1)] }, { coefficient := 1, powers := [(6, 1), (18, 1), (56, 1)] }, { coefficient := 1, powers := [(18, 1)] }, { coefficient := 1, powers := [(23, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (34, 1), (55, 1)] }, { coefficient := 1, powers := [(0, 1), (37, 1), (52, 1)] }, { coefficient := 1, powers := [(0, 1), (40, 1), (46, 1)] }, { coefficient := 1, powers := [(3, 1), (23, 1), (55, 1)] }, { coefficient := 1, powers := [(3, 1), (28, 1), (52, 1)] }, { coefficient := 1, powers := [(3, 1), (31, 1), (46, 1)] }, { coefficient := 1, powers := [(6, 1), (18, 1), (55, 1)] }, { coefficient := 1, powers := [(6, 1), (28, 1), (40, 1)] }, { coefficient := 1, powers := [(6, 1), (31, 1), (37, 1)] }, { coefficient := 1, powers := [(9, 1), (18, 1), (52, 1)] }, { coefficient := 1, powers := [(9, 1), (23, 1), (40, 1)] }, { coefficient := 1, powers := [(9, 1), (31, 1), (34, 1)] }, { coefficient := 1, powers := [(13, 1), (18, 1), (46, 1)] }, { coefficient := 1, powers := [(13, 1), (23, 1), (37, 1)] }, { coefficient := 1, powers := [(13, 1), (28, 1), (34, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (36, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (39, 1), (54, 1)] }, { coefficient := 1, powers := [(2, 1), (45, 1), (51, 1)] }, { coefficient := 1, powers := [(5, 1), (27, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (51, 1)] }, { coefficient := 1, powers := [(8, 1), (22, 1), (57, 1)] }, { coefficient := 1, powers := [(8, 1), (30, 1), (45, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (39, 1)] }, { coefficient := 1, powers := [(12, 1), (22, 1), (54, 1)] }, { coefficient := 1, powers := [(12, 1), (27, 1), (45, 1)] }, { coefficient := 1, powers := [(12, 1), (33, 1), (36, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (51, 1)] }, { coefficient := 1, powers := [(17, 1), (27, 1), (39, 1)] }, { coefficient := 1, powers := [(17, 1), (30, 1), (36, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(37, 1)] }],
  [{ coefficient := 1, powers := [(38, 1)] }],
  [{ coefficient := 1, powers := [(39, 1), (59, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 34 → SparsePoly (Fin 60) := ![
  [{ coefficient := -1, powers := [(6, 1), (9, 1), (33, 1), (39, 1), (51, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (33, 1), (39, 1), (46, 1), (51, 1), (59, 1)] }, { coefficient := -1, powers := [(9, 1), (33, 1), (34, 1), (39, 1), (51, 1), (59, 1)] }, { coefficient := 1, powers := [(33, 1), (34, 1), (39, 1), (46, 1), (51, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (33, 1), (34, 1), (39, 1), (42, 1)] }, { coefficient := -1, powers := [(3, 1), (23, 1), (33, 1), (39, 1), (42, 1)] }, { coefficient := 1, powers := [(3, 1), (33, 1), (39, 1), (52, 1)] }, { coefficient := -1, powers := [(6, 1), (18, 1), (33, 1), (39, 1), (42, 1)] }, { coefficient := -1, powers := [(33, 1), (34, 1), (39, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (9, 1), (23, 1), (33, 1), (39, 1), (59, 1)] }, { coefficient := -1, powers := [(8, 1), (23, 1), (33, 1), (39, 1), (46, 1), (59, 1)] }, { coefficient := 1, powers := [(8, 1), (28, 1), (33, 1), (34, 1), (39, 1), (59, 1)] }],
  [{ coefficient := 2, powers := [(6, 1), (30, 1), (50, 1)] }, { coefficient := -1, powers := [(26, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (45, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (9, 1), (12, 1), (33, 1), (39, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (12, 1), (33, 1), (39, 1), (46, 1), (59, 1)] }, { coefficient := -1, powers := [(9, 1), (12, 1), (33, 1), (34, 1), (39, 1), (59, 1)] }, { coefficient := 1, powers := [(12, 1), (33, 1), (34, 1), (39, 1), (46, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (8, 1), (9, 1), (33, 1), (39, 1), (47, 1), (52, 1), (56, 1), (59, 1)] }, { coefficient := -1, powers := [(3, 1), (8, 1), (33, 1), (39, 1), (40, 1), (46, 1), (47, 1), (56, 1), (59, 1)] }, { coefficient := -1, powers := [(3, 1), (8, 1), (33, 1), (39, 1), (46, 1), (47, 1), (52, 1), (56, 1), (59, 1)] }, { coefficient := -1, powers := [(6, 1), (8, 1), (9, 1), (33, 1), (39, 1), (47, 1), (52, 1), (56, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (8, 1), (33, 1), (39, 1), (40, 1), (46, 1), (47, 1), (56, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (8, 1), (33, 1), (39, 1), (46, 1), (47, 1), (52, 1), (56, 1), (59, 1)] }, { coefficient := 1, powers := [(8, 1), (9, 1), (33, 1), (34, 1), (39, 1), (47, 1), (52, 1), (56, 1), (59, 1)] }, { coefficient := 1, powers := [(8, 1), (9, 1), (33, 1), (39, 1), (47, 1), (52, 1), (59, 1)] }, { coefficient := -1, powers := [(8, 1), (33, 1), (34, 1), (39, 1), (40, 1), (46, 1), (47, 1), (56, 1), (59, 1)] }, { coefficient := -1, powers := [(8, 1), (33, 1), (34, 1), (39, 1), (46, 1), (47, 1), (52, 1), (56, 1), (59, 1)] }, { coefficient := -1, powers := [(8, 1), (33, 1), (39, 1), (46, 1), (47, 1), (52, 1), (59, 1)] }],
  [{ coefficient := -2, powers := [(8, 1), (30, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (16, 1), (33, 1), (34, 1), (39, 1), (52, 1)] }, { coefficient := -1, powers := [(16, 1), (33, 1), (34, 1), (39, 1), (40, 1), (46, 1)] }, { coefficient := -1, powers := [(16, 1), (33, 1), (34, 1), (39, 1), (46, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (9, 1), (33, 1), (34, 1), (39, 1), (52, 1)] }, { coefficient := 1, powers := [(0, 1), (33, 1), (34, 1), (39, 1), (40, 1), (46, 1)] }, { coefficient := 1, powers := [(0, 1), (33, 1), (34, 1), (39, 1), (46, 1), (52, 1)] }, { coefficient := -1, powers := [(6, 1), (9, 1), (18, 1), (33, 1), (39, 1), (52, 1)] }, { coefficient := -1, powers := [(6, 1), (9, 1), (23, 1), (33, 1), (39, 1), (52, 1)] }, { coefficient := 1, powers := [(6, 1), (18, 1), (33, 1), (39, 1), (40, 1), (46, 1)] }, { coefficient := 1, powers := [(6, 1), (18, 1), (33, 1), (39, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(6, 1), (23, 1), (33, 1), (39, 1), (40, 1), (46, 1)] }, { coefficient := 1, powers := [(6, 1), (23, 1), (33, 1), (39, 1), (46, 1), (52, 1)] }, { coefficient := -2, powers := [(6, 1), (30, 1), (45, 1)] }, { coefficient := 1, powers := [(9, 1), (23, 1), (33, 1), (34, 1), (39, 1), (52, 1)] }, { coefficient := -1, powers := [(23, 1), (33, 1), (34, 1), (39, 1), (40, 1), (46, 1)] }, { coefficient := -1, powers := [(23, 1), (33, 1), (34, 1), (39, 1), (46, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (9, 1), (33, 1), (39, 1), (50, 1), (52, 1)] }, { coefficient := -1, powers := [(6, 1), (33, 1), (39, 1), (40, 1), (46, 1), (50, 1)] }, { coefficient := -1, powers := [(6, 1), (33, 1), (39, 1), (46, 1), (50, 1), (52, 1)] }, { coefficient := -1, powers := [(9, 1), (33, 1), (34, 1), (39, 1), (50, 1), (52, 1)] }, { coefficient := 1, powers := [(33, 1), (34, 1), (39, 1), (40, 1), (46, 1), (50, 1)] }, { coefficient := 1, powers := [(33, 1), (34, 1), (39, 1), (46, 1), (50, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (5, 1), (30, 1), (50, 1)] }, { coefficient := 1, powers := [(5, 1), (18, 1), (30, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (33, 1), (34, 1), (39, 1)] }, { coefficient := 1, powers := [(3, 1), (23, 1), (33, 1), (39, 1)] }, { coefficient := 1, powers := [(6, 1), (18, 1), (33, 1), (39, 1)] }],
  [{ coefficient := -1, powers := [(22, 1), (51, 1)] }, { coefficient := 1, powers := [(30, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(27, 1)] }],
  [{ coefficient := 1, powers := [(22, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (30, 1)] }, { coefficient := -1, powers := [(12, 1), (22, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (9, 1), (33, 1), (39, 1), (59, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (39, 1), (46, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (30, 1), (50, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (8, 1), (9, 1), (33, 1), (39, 1), (52, 1), (56, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (8, 1), (33, 1), (39, 1), (40, 1), (46, 1), (56, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (8, 1), (33, 1), (39, 1), (46, 1), (52, 1), (56, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (8, 1), (9, 1), (33, 1), (39, 1), (52, 1), (56, 1), (59, 1)] }, { coefficient := -1, powers := [(6, 1), (8, 1), (33, 1), (39, 1), (40, 1), (46, 1), (56, 1), (59, 1)] }, { coefficient := -1, powers := [(6, 1), (8, 1), (33, 1), (39, 1), (46, 1), (52, 1), (56, 1), (59, 1)] }, { coefficient := -1, powers := [(8, 1), (9, 1), (33, 1), (34, 1), (39, 1), (52, 1), (56, 1), (59, 1)] }, { coefficient := -1, powers := [(8, 1), (9, 1), (33, 1), (39, 1), (52, 1), (59, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (34, 1), (39, 1), (40, 1), (46, 1), (56, 1), (59, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (34, 1), (39, 1), (46, 1), (52, 1), (56, 1), (59, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (39, 1), (46, 1), (52, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (9, 1), (33, 1), (39, 1), (59, 1)] }, { coefficient := -1, powers := [(6, 1), (33, 1), (39, 1), (46, 1), (59, 1)] }, { coefficient := 1, powers := [(9, 1), (33, 1), (34, 1), (39, 1), (59, 1)] }, { coefficient := -1, powers := [(33, 1), (34, 1), (39, 1), (46, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(51, 1)] }],
  [{ coefficient := -1, powers := [(45, 1)] }],
  [{ coefficient := 1, powers := [(12, 1)] }],
  [{ coefficient := 2, powers := [(8, 1), (30, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (33, 1), (39, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (33, 1), (39, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (9, 1), (33, 1), (39, 1), (52, 1)] }, { coefficient := -1, powers := [(8, 1), (33, 1), (39, 1), (40, 1), (46, 1)] }, { coefficient := -1, powers := [(8, 1), (33, 1), (39, 1), (46, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (33, 1), (39, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(36, 1), (57, 1)] }, { coefficient := 1, powers := [(39, 1), (54, 1)] }, { coefficient := 1, powers := [(45, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (8, 1), (33, 1), (39, 1), (52, 1)] }, { coefficient := 1, powers := [(6, 1), (8, 1), (31, 1), (33, 1), (39, 1)] }, { coefficient := 1, powers := [(8, 1), (13, 1), (23, 1), (33, 1), (39, 1)] }, { coefficient := -1, powers := [(8, 1), (23, 1), (33, 1), (39, 1), (40, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (5, 1), (30, 1), (41, 1), (50, 1)] }, { coefficient := -1, powers := [(0, 1), (5, 1), (30, 1), (54, 1)] }, { coefficient := 1, powers := [(0, 1), (12, 1), (22, 1), (54, 1)] }, { coefficient := -1, powers := [(5, 1), (18, 1), (30, 1), (41, 1), (50, 1)] }, { coefficient := -2, powers := [(8, 1), (23, 1), (30, 1), (45, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (23, 1), (51, 1)] }, { coefficient := -1, powers := [(17, 1), (23, 1), (30, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (8, 1), (9, 1), (33, 1), (39, 1), (52, 1)] }, { coefficient := -1, powers := [(0, 1), (8, 1), (33, 1), (39, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(3, 1), (8, 1), (9, 1), (23, 1), (33, 1), (39, 1), (52, 1), (56, 1)] }, { coefficient := -1, powers := [(3, 1), (8, 1), (23, 1), (33, 1), (39, 1), (40, 1), (46, 1), (56, 1)] }, { coefficient := -1, powers := [(3, 1), (8, 1), (23, 1), (33, 1), (39, 1), (46, 1), (52, 1), (56, 1)] }, { coefficient := -1, powers := [(6, 1), (8, 1), (9, 1), (23, 1), (33, 1), (39, 1), (52, 1), (56, 1)] }, { coefficient := 1, powers := [(6, 1), (8, 1), (23, 1), (33, 1), (39, 1), (40, 1), (46, 1), (56, 1)] }, { coefficient := 1, powers := [(6, 1), (8, 1), (23, 1), (33, 1), (39, 1), (46, 1), (52, 1), (56, 1)] }, { coefficient := 1, powers := [(8, 1), (9, 1), (23, 1), (33, 1), (34, 1), (39, 1), (52, 1), (56, 1)] }, { coefficient := 1, powers := [(8, 1), (9, 1), (23, 1), (33, 1), (39, 1), (52, 1)] }, { coefficient := -1, powers := [(8, 1), (9, 1), (31, 1), (33, 1), (34, 1), (39, 1)] }, { coefficient := -1, powers := [(8, 1), (13, 1), (28, 1), (33, 1), (34, 1), (39, 1)] }, { coefficient := -1, powers := [(8, 1), (23, 1), (33, 1), (34, 1), (39, 1), (40, 1), (46, 1), (56, 1)] }, { coefficient := -1, powers := [(8, 1), (23, 1), (33, 1), (34, 1), (39, 1), (46, 1), (52, 1), (56, 1)] }, { coefficient := -1, powers := [(8, 1), (23, 1), (33, 1), (39, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1), (33, 1), (34, 1), (39, 1), (46, 1)] }]
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
    (values : Fin 60 → R) :
    ¬ ∀ index : Fin 34,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component13.SelectedLeafB4_1.selectedHasNoCommonZero

end Krenn.Component13.SelectedLeafB4_1
