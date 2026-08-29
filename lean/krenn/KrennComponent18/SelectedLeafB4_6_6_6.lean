import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component18.SelectedLeafB4_6_6_6

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "c4fab14b6aca92054807c3b031d1742a661e6e38412af66ee78c546e31570686"
def certificateSHA256 : String := "4d95a944d21be33262a30dbf49cba7e5d0cdf26758444d584395f8d92e4d25cc"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 18 → Fin 670 := ![
  0,
  10,
  19,
  142,
  168,
  318,
  437,
  443,
  496,
  562,
  581,
  646,
  657,
  660,
  661,
  663,
  666,
  669
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 18 → SparsePoly (Fin 68) := ![
  [{ coefficient := 1, powers := [(3, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (54, 1)] }, { coefficient := 1, powers := [(19, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (53, 1)] }, { coefficient := 1, powers := [(31, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (54, 1)] }, { coefficient := 1, powers := [(31, 1), (43, 1)] }, { coefficient := 1, powers := [(34, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1)] }, { coefficient := 1, powers := [(13, 1), (31, 1)] }, { coefficient := 1, powers := [(17, 1), (23, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (60, 1)] }, { coefficient := 1, powers := [(13, 1), (26, 1), (47, 1)] }, { coefficient := 1, powers := [(13, 1), (57, 1)] }, { coefficient := 1, powers := [(18, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (31, 1), (60, 1)] }, { coefficient := 1, powers := [(3, 1), (34, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (37, 1), (54, 1)] }, { coefficient := 1, powers := [(23, 1), (45, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (45, 1), (53, 1)] }, { coefficient := 1, powers := [(24, 1), (57, 1)] }, { coefficient := 1, powers := [(31, 1), (49, 1)] }, { coefficient := 1, powers := [(37, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (52, 1)] }, { coefficient := 1, powers := [(3, 1), (59, 1)] }, { coefficient := 1, powers := [(19, 1), (52, 1)] }, { coefficient := 1, powers := [(19, 1), (56, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (41, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (51, 1)] }, { coefficient := 1, powers := [(3, 1), (32, 1), (56, 1)] }, { coefficient := 1, powers := [(9, 1), (19, 1), (56, 1)] }, { coefficient := 1, powers := [(9, 1)] }, { coefficient := 1, powers := [(19, 1), (51, 1)] }, { coefficient := 1, powers := [(41, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (40, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (43, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (49, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (37, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (49, 1)] }, { coefficient := 1, powers := [(8, 1), (37, 1), (43, 1)] }, { coefficient := 1, powers := [(13, 1), (24, 1), (57, 1)] }, { coefficient := 1, powers := [(13, 1), (31, 1), (49, 1)] }, { coefficient := 1, powers := [(13, 1), (37, 1), (40, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (54, 1)] }, { coefficient := 1, powers := [(18, 1), (31, 1), (43, 1)] }, { coefficient := 1, powers := [(18, 1), (34, 1), (40, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(41, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(43, 1)] }],
  [{ coefficient := 1, powers := [(57, 1)] }],
  [{ coefficient := 1, powers := [(31, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 18 → SparsePoly (Fin 68) := ![
  [{ coefficient := 1, powers := [(8, 1), (9, 1), (24, 1), (59, 1), (62, 1)] }, { coefficient := -1, powers := [(8, 1), (24, 1), (32, 1), (56, 1), (62, 1)] }, { coefficient := -1, powers := [(8, 1), (24, 1), (41, 1), (59, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (9, 1), (24, 1), (26, 1), (52, 1), (62, 1)] }, { coefficient := 1, powers := [(0, 1), (24, 1), (26, 1), (41, 1), (52, 1), (62, 1)] }, { coefficient := 1, powers := [(0, 1), (24, 1), (26, 1), (41, 1), (56, 1), (62, 1)] }, { coefficient := 1, powers := [(0, 1), (24, 1), (26, 1), (51, 1), (62, 1)] }, { coefficient := -1, powers := [(9, 1), (19, 1), (24, 1), (26, 1), (52, 1), (62, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (26, 1), (41, 1), (52, 1), (62, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (26, 1), (41, 1), (56, 1), (62, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (26, 1), (51, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (9, 1), (17, 1), (49, 1), (52, 1), (62, 1)] }, { coefficient := 1, powers := [(0, 1), (17, 1), (41, 1), (49, 1), (52, 1), (62, 1)] }, { coefficient := 1, powers := [(0, 1), (17, 1), (41, 1), (49, 1), (56, 1), (62, 1)] }, { coefficient := 1, powers := [(0, 1), (17, 1), (49, 1), (51, 1), (62, 1)] }, { coefficient := -1, powers := [(3, 1), (9, 1), (17, 1), (49, 1), (59, 1), (62, 1)] }, { coefficient := 1, powers := [(3, 1), (17, 1), (32, 1), (49, 1), (56, 1), (62, 1)] }, { coefficient := 1, powers := [(3, 1), (17, 1), (41, 1), (49, 1), (59, 1), (62, 1)] }, { coefficient := -1, powers := [(5, 1), (9, 1), (45, 1), (59, 1), (62, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (45, 1), (56, 1), (62, 1)] }, { coefficient := 1, powers := [(5, 1), (41, 1), (45, 1), (59, 1), (62, 1)] }, { coefficient := -1, powers := [(9, 1), (17, 1), (19, 1), (49, 1), (52, 1), (62, 1)] }, { coefficient := 1, powers := [(17, 1), (19, 1), (41, 1), (49, 1), (52, 1), (62, 1)] }, { coefficient := 1, powers := [(17, 1), (19, 1), (41, 1), (49, 1), (56, 1), (62, 1)] }, { coefficient := 1, powers := [(17, 1), (19, 1), (49, 1), (51, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (9, 1), (37, 1), (52, 1), (62, 1)] }, { coefficient := -1, powers := [(5, 1), (37, 1), (41, 1), (52, 1), (62, 1)] }, { coefficient := -1, powers := [(5, 1), (37, 1), (41, 1), (56, 1), (62, 1)] }, { coefficient := -1, powers := [(5, 1), (37, 1), (51, 1), (62, 1)] }, { coefficient := -1, powers := [(9, 1), (18, 1), (24, 1), (52, 1), (62, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (41, 1), (52, 1), (62, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (41, 1), (56, 1), (62, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (51, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (9, 1), (13, 1), (45, 1), (52, 1), (62, 1)] }, { coefficient := 1, powers := [(0, 1), (13, 1), (41, 1), (45, 1), (52, 1), (62, 1)] }, { coefficient := 1, powers := [(0, 1), (13, 1), (41, 1), (45, 1), (56, 1), (62, 1)] }, { coefficient := 1, powers := [(0, 1), (13, 1), (45, 1), (51, 1), (62, 1)] }, { coefficient := -1, powers := [(3, 1), (9, 1), (13, 1), (45, 1), (59, 1), (62, 1)] }, { coefficient := 1, powers := [(3, 1), (13, 1), (32, 1), (45, 1), (56, 1), (62, 1)] }, { coefficient := 1, powers := [(3, 1), (13, 1), (41, 1), (45, 1), (59, 1), (62, 1)] }, { coefficient := -1, powers := [(9, 1), (13, 1), (19, 1), (45, 1), (52, 1), (62, 1)] }, { coefficient := 1, powers := [(13, 1), (19, 1), (41, 1), (45, 1), (52, 1), (62, 1)] }, { coefficient := 1, powers := [(13, 1), (19, 1), (41, 1), (45, 1), (56, 1), (62, 1)] }, { coefficient := 1, powers := [(13, 1), (19, 1), (45, 1), (51, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (9, 1), (18, 1), (52, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 1), (18, 1), (41, 1), (52, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 1), (18, 1), (41, 1), (56, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 1), (18, 1), (51, 1), (62, 1)] }, { coefficient := 1, powers := [(3, 1), (9, 1), (18, 1), (59, 1), (62, 1)] }, { coefficient := -1, powers := [(3, 1), (18, 1), (32, 1), (56, 1), (62, 1)] }, { coefficient := -1, powers := [(3, 1), (18, 1), (41, 1), (59, 1), (62, 1)] }, { coefficient := 1, powers := [(9, 1), (18, 1), (19, 1), (52, 1), (62, 1)] }, { coefficient := -1, powers := [(18, 1), (19, 1), (41, 1), (52, 1), (62, 1)] }, { coefficient := -1, powers := [(18, 1), (19, 1), (41, 1), (56, 1), (62, 1)] }, { coefficient := -1, powers := [(18, 1), (19, 1), (51, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (9, 1), (49, 1), (52, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 1), (41, 1), (49, 1), (52, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 1), (41, 1), (49, 1), (56, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 1), (49, 1), (51, 1), (62, 1)] }, { coefficient := 1, powers := [(3, 1), (9, 1), (49, 1), (59, 1), (62, 1)] }, { coefficient := -1, powers := [(3, 1), (32, 1), (49, 1), (56, 1), (62, 1)] }, { coefficient := -1, powers := [(3, 1), (41, 1), (49, 1), (59, 1), (62, 1)] }, { coefficient := 1, powers := [(9, 1), (19, 1), (49, 1), (52, 1), (62, 1)] }, { coefficient := -1, powers := [(19, 1), (41, 1), (49, 1), (52, 1), (62, 1)] }, { coefficient := -1, powers := [(19, 1), (41, 1), (49, 1), (56, 1), (62, 1)] }, { coefficient := -1, powers := [(19, 1), (49, 1), (51, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (9, 1), (24, 1), (52, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 1), (24, 1), (41, 1), (52, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 1), (24, 1), (41, 1), (56, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 1), (24, 1), (51, 1), (62, 1)] }, { coefficient := 1, powers := [(9, 1), (19, 1), (24, 1), (52, 1), (62, 1)] }, { coefficient := -1, powers := [(19, 1), (24, 1), (41, 1), (52, 1), (62, 1)] }, { coefficient := -1, powers := [(19, 1), (24, 1), (41, 1), (56, 1), (62, 1)] }, { coefficient := -1, powers := [(19, 1), (24, 1), (51, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (9, 1), (59, 1), (62, 1)] }, { coefficient := -1, powers := [(5, 1), (32, 1), (56, 1), (62, 1)] }, { coefficient := -1, powers := [(5, 1), (41, 1), (59, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (9, 1), (13, 1), (52, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 1), (13, 1), (41, 1), (52, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 1), (13, 1), (41, 1), (56, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 1), (13, 1), (51, 1), (62, 1)] }, { coefficient := 1, powers := [(3, 1), (9, 1), (13, 1), (59, 1), (62, 1)] }, { coefficient := -1, powers := [(3, 1), (13, 1), (32, 1), (56, 1), (62, 1)] }, { coefficient := -1, powers := [(3, 1), (13, 1), (41, 1), (59, 1), (62, 1)] }, { coefficient := 1, powers := [(9, 1), (13, 1), (19, 1), (52, 1), (62, 1)] }, { coefficient := -1, powers := [(13, 1), (19, 1), (41, 1), (52, 1), (62, 1)] }, { coefficient := -1, powers := [(13, 1), (19, 1), (41, 1), (56, 1), (62, 1)] }, { coefficient := -1, powers := [(13, 1), (19, 1), (51, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(9, 1), (62, 1)] }, { coefficient := 1, powers := [(41, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(62, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (9, 1), (52, 1), (62, 1)] }, { coefficient := 1, powers := [(0, 1), (41, 1), (52, 1), (62, 1)] }, { coefficient := 1, powers := [(0, 1), (41, 1), (56, 1), (62, 1)] }, { coefficient := 1, powers := [(0, 1), (51, 1), (62, 1)] }, { coefficient := -1, powers := [(3, 1), (9, 1), (59, 1), (62, 1)] }, { coefficient := 1, powers := [(3, 1), (32, 1), (56, 1), (62, 1)] }, { coefficient := 1, powers := [(3, 1), (41, 1), (59, 1), (62, 1)] }, { coefficient := -1, powers := [(9, 1), (19, 1), (52, 1), (62, 1)] }, { coefficient := 1, powers := [(19, 1), (41, 1), (52, 1), (62, 1)] }, { coefficient := 1, powers := [(19, 1), (41, 1), (56, 1), (62, 1)] }, { coefficient := 1, powers := [(19, 1), (51, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (9, 1), (40, 1), (52, 1), (60, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 1), (40, 1), (41, 1), (52, 1), (60, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 1), (40, 1), (41, 1), (56, 1), (60, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 1), (40, 1), (51, 1), (60, 1), (62, 1)] }, { coefficient := 1, powers := [(3, 1), (9, 1), (40, 1), (59, 1), (60, 1), (62, 1)] }, { coefficient := -1, powers := [(3, 1), (32, 1), (40, 1), (56, 1), (60, 1), (62, 1)] }, { coefficient := -1, powers := [(3, 1), (40, 1), (41, 1), (59, 1), (60, 1), (62, 1)] }, { coefficient := 1, powers := [(9, 1), (19, 1), (40, 1), (52, 1), (60, 1), (62, 1)] }, { coefficient := -1, powers := [(19, 1), (40, 1), (41, 1), (52, 1), (60, 1), (62, 1)] }, { coefficient := -1, powers := [(19, 1), (40, 1), (41, 1), (56, 1), (60, 1), (62, 1)] }, { coefficient := -1, powers := [(19, 1), (40, 1), (51, 1), (60, 1), (62, 1)] }],
  [{ coefficient := -2, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (8, 1), (9, 1), (37, 1), (52, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 1), (8, 1), (37, 1), (41, 1), (52, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 1), (8, 1), (37, 1), (41, 1), (56, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 1), (8, 1), (37, 1), (51, 1), (62, 1)] }, { coefficient := 1, powers := [(3, 1), (8, 1), (9, 1), (37, 1), (59, 1), (62, 1)] }, { coefficient := -1, powers := [(3, 1), (8, 1), (32, 1), (37, 1), (56, 1), (62, 1)] }, { coefficient := -1, powers := [(3, 1), (8, 1), (37, 1), (41, 1), (59, 1), (62, 1)] }, { coefficient := 1, powers := [(8, 1), (9, 1), (19, 1), (37, 1), (52, 1), (62, 1)] }, { coefficient := -1, powers := [(8, 1), (19, 1), (37, 1), (41, 1), (52, 1), (62, 1)] }, { coefficient := -1, powers := [(8, 1), (19, 1), (37, 1), (41, 1), (56, 1), (62, 1)] }, { coefficient := -1, powers := [(8, 1), (19, 1), (37, 1), (51, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (2, 1), (9, 1), (43, 1), (52, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 1), (2, 1), (41, 1), (43, 1), (52, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 1), (2, 1), (41, 1), (43, 1), (56, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 1), (2, 1), (43, 1), (51, 1), (62, 1)] }, { coefficient := 1, powers := [(0, 1), (5, 1), (9, 1), (34, 1), (52, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 1), (5, 1), (34, 1), (41, 1), (52, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 1), (5, 1), (34, 1), (41, 1), (56, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 1), (5, 1), (34, 1), (51, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 1), (9, 1), (13, 1), (24, 1), (52, 1), (62, 1)] }, { coefficient := 1, powers := [(0, 1), (13, 1), (24, 1), (41, 1), (52, 1), (62, 1)] }, { coefficient := 1, powers := [(0, 1), (13, 1), (24, 1), (41, 1), (56, 1), (62, 1)] }, { coefficient := 1, powers := [(0, 1), (13, 1), (24, 1), (51, 1), (62, 1)] }, { coefficient := 1, powers := [(2, 1), (3, 1), (9, 1), (43, 1), (59, 1), (62, 1)] }, { coefficient := -1, powers := [(2, 1), (3, 1), (32, 1), (43, 1), (56, 1), (62, 1)] }, { coefficient := -1, powers := [(2, 1), (3, 1), (41, 1), (43, 1), (59, 1), (62, 1)] }, { coefficient := 1, powers := [(2, 1), (9, 1), (19, 1), (43, 1), (52, 1), (62, 1)] }, { coefficient := -1, powers := [(2, 1), (19, 1), (41, 1), (43, 1), (52, 1), (62, 1)] }, { coefficient := -1, powers := [(2, 1), (19, 1), (41, 1), (43, 1), (56, 1), (62, 1)] }, { coefficient := -1, powers := [(2, 1), (19, 1), (43, 1), (51, 1), (62, 1)] }, { coefficient := 1, powers := [(5, 1), (9, 1), (19, 1), (34, 1), (52, 1), (62, 1)] }, { coefficient := -1, powers := [(5, 1), (19, 1), (34, 1), (41, 1), (52, 1), (62, 1)] }, { coefficient := -1, powers := [(5, 1), (19, 1), (34, 1), (41, 1), (56, 1), (62, 1)] }, { coefficient := -1, powers := [(5, 1), (19, 1), (34, 1), (51, 1), (62, 1)] }, { coefficient := -1, powers := [(9, 1), (13, 1), (19, 1), (24, 1), (52, 1), (62, 1)] }, { coefficient := 1, powers := [(13, 1), (19, 1), (24, 1), (41, 1), (52, 1), (62, 1)] }, { coefficient := 1, powers := [(13, 1), (19, 1), (24, 1), (41, 1), (56, 1), (62, 1)] }, { coefficient := 1, powers := [(13, 1), (19, 1), (24, 1), (51, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (5, 1), (9, 1), (52, 1), (60, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 1), (5, 1), (41, 1), (52, 1), (60, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 1), (5, 1), (41, 1), (56, 1), (60, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 1), (5, 1), (51, 1), (60, 1), (62, 1)] }, { coefficient := 1, powers := [(0, 1), (9, 1), (13, 1), (45, 1), (48, 1), (52, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 1), (9, 1), (13, 1), (49, 1), (52, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 1), (13, 1), (41, 1), (45, 1), (48, 1), (52, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 1), (13, 1), (41, 1), (45, 1), (48, 1), (56, 1), (62, 1)] }, { coefficient := 1, powers := [(0, 1), (13, 1), (41, 1), (49, 1), (52, 1), (62, 1)] }, { coefficient := 1, powers := [(0, 1), (13, 1), (41, 1), (49, 1), (56, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 1), (13, 1), (45, 1), (48, 1), (51, 1), (62, 1)] }, { coefficient := 1, powers := [(0, 1), (13, 1), (49, 1), (51, 1), (62, 1)] }, { coefficient := 1, powers := [(3, 1), (9, 1), (13, 1), (45, 1), (48, 1), (59, 1), (62, 1)] }, { coefficient := -1, powers := [(3, 1), (9, 1), (13, 1), (49, 1), (59, 1), (62, 1)] }, { coefficient := -1, powers := [(3, 1), (13, 1), (32, 1), (45, 1), (48, 1), (56, 1), (62, 1)] }, { coefficient := 1, powers := [(3, 1), (13, 1), (32, 1), (49, 1), (56, 1), (62, 1)] }, { coefficient := -1, powers := [(3, 1), (13, 1), (41, 1), (45, 1), (48, 1), (59, 1), (62, 1)] }, { coefficient := 1, powers := [(3, 1), (13, 1), (41, 1), (49, 1), (59, 1), (62, 1)] }, { coefficient := 1, powers := [(5, 1), (9, 1), (19, 1), (52, 1), (60, 1), (62, 1)] }, { coefficient := -1, powers := [(5, 1), (19, 1), (41, 1), (52, 1), (60, 1), (62, 1)] }, { coefficient := -1, powers := [(5, 1), (19, 1), (41, 1), (56, 1), (60, 1), (62, 1)] }, { coefficient := -1, powers := [(5, 1), (19, 1), (51, 1), (60, 1), (62, 1)] }, { coefficient := 1, powers := [(9, 1), (13, 1), (19, 1), (45, 1), (48, 1), (52, 1), (62, 1)] }, { coefficient := -1, powers := [(9, 1), (13, 1), (19, 1), (49, 1), (52, 1), (62, 1)] }, { coefficient := -1, powers := [(13, 1), (19, 1), (41, 1), (45, 1), (48, 1), (52, 1), (62, 1)] }, { coefficient := -1, powers := [(13, 1), (19, 1), (41, 1), (45, 1), (48, 1), (56, 1), (62, 1)] }, { coefficient := 1, powers := [(13, 1), (19, 1), (41, 1), (49, 1), (52, 1), (62, 1)] }, { coefficient := 1, powers := [(13, 1), (19, 1), (41, 1), (49, 1), (56, 1), (62, 1)] }, { coefficient := -1, powers := [(13, 1), (19, 1), (45, 1), (48, 1), (51, 1), (62, 1)] }, { coefficient := 1, powers := [(13, 1), (19, 1), (49, 1), (51, 1), (62, 1)] }]
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
    (values : Fin 68 → R) :
    ¬ ∀ index : Fin 18,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((2 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (2 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (2 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component18.SelectedLeafB4_6_6_6.selectedHasNoCommonZero

end Krenn.Component18.SelectedLeafB4_6_6_6
