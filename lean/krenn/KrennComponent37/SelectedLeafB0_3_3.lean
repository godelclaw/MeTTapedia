import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component37.SelectedLeafB0_3_3

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "df357f3f345d765fada47a090c88493c18db38f9b35c8dc536f2e73ea4dbef5a"
def certificateSHA256 : String := "73af12f0791f01d058ff092c37c90579326349712fffb5ae021ff9e19008130f"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 28 → Fin 667 := ![
  149,
  152,
  221,
  296,
  301,
  313,
  315,
  461,
  466,
  470,
  471,
  472,
  473,
  475,
  478,
  580,
  584,
  602,
  603,
  608,
  609,
  612,
  655,
  658,
  661,
  663,
  664,
  666
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 28 → SparsePoly (Fin 66) := ![
  [{ coefficient := 1, powers := [(9, 1), (26, 1)] }, { coefficient := 1, powers := [(26, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (44, 1)] }, { coefficient := 1, powers := [(40, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (26, 1), (47, 1)] }, { coefficient := 1, powers := [(9, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (51, 1)] }, { coefficient := 1, powers := [(20, 1), (51, 1)] }, { coefficient := 1, powers := [(25, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (59, 1)] }, { coefficient := 1, powers := [(9, 1), (43, 1)] }, { coefficient := 1, powers := [(13, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(20, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(44, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1), (51, 1)] }, { coefficient := 1, powers := [(25, 1), (46, 1), (51, 1)] }, { coefficient := 1, powers := [(51, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1), (52, 1)] }, { coefficient := 1, powers := [(3, 1), (34, 1), (52, 1)] }, { coefficient := 1, powers := [(13, 1), (20, 1), (52, 1)] }, { coefficient := 1, powers := [(43, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1), (54, 1)] }, { coefficient := 1, powers := [(20, 1), (44, 1), (54, 1)] }, { coefficient := 1, powers := [(20, 1), (58, 1)] }, { coefficient := 1, powers := [(26, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1), (50, 1)] }, { coefficient := 1, powers := [(6, 1), (31, 1), (46, 1)] }, { coefficient := 1, powers := [(9, 1), (25, 1), (46, 1)] }, { coefficient := 1, powers := [(50, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1), (53, 1)] }, { coefficient := 1, powers := [(46, 1), (51, 1)] }, { coefficient := 1, powers := [(51, 1), (57, 1)] }, { coefficient := 1, powers := [(53, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1), (54, 1)] }, { coefficient := 1, powers := [(26, 1), (41, 1)] }, { coefficient := 1, powers := [(26, 1), (46, 1)] }, { coefficient := 1, powers := [(54, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1), (50, 1)] }, { coefficient := 1, powers := [(6, 1), (31, 1), (47, 1)] }, { coefficient := 1, powers := [(9, 1), (25, 1), (47, 1)] }, { coefficient := 1, powers := [(44, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1), (52, 1)] }, { coefficient := 1, powers := [(41, 1), (44, 1)] }, { coefficient := 1, powers := [(44, 1), (52, 1)] }, { coefficient := 1, powers := [(47, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (48, 1), (51, 1)] }, { coefficient := 1, powers := [(21, 1), (51, 1)] }, { coefficient := 1, powers := [(25, 1), (42, 1)] }, { coefficient := 1, powers := [(25, 1), (48, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1)] }, { coefficient := 1, powers := [(6, 1), (60, 1)] }, { coefficient := 1, powers := [(25, 1), (41, 1)] }, { coefficient := 1, powers := [(25, 1), (46, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (40, 1), (58, 1)] }, { coefficient := 1, powers := [(3, 1), (31, 1), (58, 1)] }, { coefficient := 1, powers := [(9, 1), (20, 1), (58, 1)] }, { coefficient := 1, powers := [(9, 1), (26, 1), (44, 1)] }, { coefficient := 1, powers := [(26, 1), (40, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1)] }, { coefficient := 1, powers := [(3, 1), (34, 1)] }, { coefficient := 1, powers := [(13, 1), (20, 1)] }, { coefficient := 1, powers := [(20, 1), (56, 1)] }, { coefficient := 1, powers := [(25, 1), (43, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (50, 1)] }, { coefficient := 1, powers := [(6, 1), (31, 1)] }, { coefficient := 1, powers := [(9, 1), (25, 1)] }, { coefficient := 1, powers := [(20, 1), (50, 1)] }, { coefficient := 1, powers := [(25, 1), (40, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (41, 1), (58, 1)] }, { coefficient := 1, powers := [(0, 1), (47, 1), (54, 1)] }, { coefficient := 1, powers := [(26, 1), (41, 1), (44, 1)] }, { coefficient := 1, powers := [(26, 1), (47, 1)] }, { coefficient := 1, powers := [(44, 1), (54, 1)] }, { coefficient := 1, powers := [(58, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (48, 1), (53, 1)] }, { coefficient := 1, powers := [(21, 1), (51, 1), (57, 1)] }, { coefficient := 1, powers := [(21, 1), (53, 1)] }, { coefficient := 1, powers := [(42, 1)] }, { coefficient := 1, powers := [(48, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1), (50, 1)] }, { coefficient := 1, powers := [(6, 1), (31, 1), (45, 1)] }, { coefficient := 1, powers := [(6, 1), (59, 1)] }, { coefficient := 1, powers := [(9, 1), (25, 1), (45, 1)] }, { coefficient := 1, powers := [(9, 1), (56, 1)] }, { coefficient := 1, powers := [(13, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (37, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (40, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (43, 1), (50, 1)] }, { coefficient := 1, powers := [(3, 1), (25, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (31, 1), (56, 1)] }, { coefficient := 1, powers := [(3, 1), (34, 1), (50, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (31, 1), (43, 1)] }, { coefficient := 1, powers := [(6, 1), (34, 1), (40, 1)] }, { coefficient := 1, powers := [(9, 1), (20, 1), (56, 1)] }, { coefficient := 1, powers := [(9, 1), (25, 1), (43, 1)] }, { coefficient := 1, powers := [(9, 1), (34, 1), (37, 1)] }, { coefficient := 1, powers := [(13, 1), (20, 1), (50, 1)] }, { coefficient := 1, powers := [(13, 1), (25, 1), (40, 1)] }, { coefficient := 1, powers := [(13, 1), (31, 1), (37, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1)] }],
  [{ coefficient := 1, powers := [(40, 1)] }],
  [{ coefficient := 1, powers := [(42, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(56, 1)] }],
  [{ coefficient := 1, powers := [(58, 1), (65, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 28 → SparsePoly (Fin 66) := ![
  [{ coefficient := -1, powers := [(6, 1), (25, 1), (43, 1), (47, 1), (60, 1), (65, 1)] }, { coefficient := -3, powers := [(20, 1), (25, 1), (43, 1), (47, 1), (52, 1), (65, 1)] }, { coefficient := 2, powers := [(20, 1), (43, 1), (47, 1), (65, 1)] }, { coefficient := -1, powers := [(25, 2), (41, 1), (43, 1), (47, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (26, 1), (43, 1), (52, 1), (65, 1)] }, { coefficient := -1, powers := [(26, 1), (43, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (25, 1), (43, 1), (60, 1), (65, 1)] }, { coefficient := 3, powers := [(20, 1), (25, 1), (43, 1), (52, 1), (65, 1)] }, { coefficient := -2, powers := [(20, 1), (43, 1), (65, 1)] }, { coefficient := 1, powers := [(25, 2), (41, 1), (43, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (21, 1), (25, 1), (46, 2), (59, 1), (63, 1)] }, { coefficient := 1, powers := [(6, 1), (21, 1), (46, 1), (59, 1), (63, 1)] }, { coefficient := -1, powers := [(6, 1), (25, 1), (46, 1), (48, 1), (59, 1), (63, 1)] }, { coefficient := -1, powers := [(6, 1), (48, 1), (59, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (25, 1), (60, 1)] }, { coefficient := -1, powers := [(20, 1), (25, 1), (52, 1)] }, { coefficient := -1, powers := [(25, 2), (41, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (20, 1), (54, 1), (59, 1), (65, 1)] }, { coefficient := -1, powers := [(20, 1), (43, 1), (50, 1), (54, 1), (65, 1)] }, { coefficient := -1, powers := [(31, 1), (37, 1), (43, 1), (54, 1), (65, 1)] }, { coefficient := -1, powers := [(54, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (25, 1), (48, 1), (59, 1), (63, 1)] }, { coefficient := -1, powers := [(6, 1), (21, 1), (25, 1), (46, 1), (59, 1), (63, 1)] }, { coefficient := -1, powers := [(6, 1), (21, 1), (59, 1), (63, 1)] }, { coefficient := 1, powers := [(6, 1), (25, 1), (48, 1), (59, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (31, 1)] }, { coefficient := 1, powers := [(9, 1), (20, 1)] }, { coefficient := -1, powers := [(20, 1), (50, 1)] }, { coefficient := -1, powers := [(31, 1), (37, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (20, 1), (52, 1), (59, 1), (65, 1)] }, { coefficient := 1, powers := [(20, 1), (43, 1), (50, 1), (52, 1), (65, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1), (43, 1), (52, 1), (65, 1)] }, { coefficient := 1, powers := [(52, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(13, 1), (20, 1), (25, 1), (26, 1), (46, 1), (47, 1), (65, 1)] }, { coefficient := 1, powers := [(20, 1), (25, 1), (26, 1), (45, 1), (47, 1), (65, 1)] }, { coefficient := 1, powers := [(20, 1), (25, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (21, 1), (25, 1), (59, 1), (63, 1)] }, { coefficient := -1, powers := [(6, 1), (20, 1), (21, 1), (25, 1), (46, 1), (59, 1), (63, 1)] }, { coefficient := -1, powers := [(6, 1), (20, 1), (21, 1), (59, 1), (63, 1)] }, { coefficient := 1, powers := [(6, 1), (21, 1), (25, 1), (59, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(13, 1), (20, 1), (25, 1), (44, 1), (46, 1), (50, 1), (65, 1)] }, { coefficient := 1, powers := [(20, 1), (25, 1), (44, 1), (45, 1), (50, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (20, 1), (25, 1), (26, 1), (46, 2), (65, 1)] }, { coefficient := -1, powers := [(20, 1), (25, 1), (26, 1), (45, 1), (46, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (20, 1), (26, 1), (59, 1), (65, 1)] }, { coefficient := -1, powers := [(20, 1), (26, 1), (43, 1), (50, 1), (65, 1)] }, { coefficient := -1, powers := [(26, 1), (31, 1), (37, 1), (43, 1), (65, 1)] }, { coefficient := -1, powers := [(26, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (25, 1), (46, 1), (59, 1), (63, 1)] }, { coefficient := 1, powers := [(6, 1), (59, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (25, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(25, 1), (43, 1), (52, 1), (65, 1)] }, { coefficient := 1, powers := [(43, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (31, 1), (52, 1)] }, { coefficient := -1, powers := [(9, 1), (20, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(20, 1), (43, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (20, 1), (59, 1), (65, 1)] }, { coefficient := 1, powers := [(13, 1), (20, 1), (25, 1), (46, 1), (50, 1), (65, 1)] }, { coefficient := -1, powers := [(20, 1), (25, 1), (45, 1), (50, 1), (65, 1)] }, { coefficient := 1, powers := [(20, 1), (43, 1), (50, 1), (65, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1), (43, 1), (65, 1)] }, { coefficient := 1, powers := [(65, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (25, 1), (59, 1), (63, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1), (25, 1), (46, 1), (59, 1), (63, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1), (59, 1), (63, 1)] }, { coefficient := -1, powers := [(6, 1), (25, 1), (59, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(20, 1), (25, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (21, 1), (25, 1), (46, 1), (53, 1), (59, 1), (63, 1)] }, { coefficient := 1, powers := [(3, 1), (25, 1), (42, 1), (57, 1), (59, 1), (63, 1)] }, { coefficient := -1, powers := [(3, 1), (25, 1), (46, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (25, 1), (48, 1), (53, 1), (59, 1), (63, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1), (21, 1), (25, 1), (46, 2), (53, 1), (59, 1), (63, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1), (21, 1), (46, 1), (53, 1), (59, 1), (63, 1)] }, { coefficient := -1, powers := [(6, 1), (20, 1), (25, 1), (42, 1), (46, 1), (57, 1), (59, 1), (63, 1)] }, { coefficient := -1, powers := [(6, 1), (20, 1), (25, 1), (46, 1), (48, 1), (53, 1), (59, 1), (63, 1)] }, { coefficient := -1, powers := [(6, 1), (20, 1), (26, 1), (47, 1), (52, 1), (59, 1), (65, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1), (41, 1), (58, 1), (59, 1), (65, 1)] }, { coefficient := -1, powers := [(6, 1), (20, 1), (42, 1), (57, 1), (59, 1), (63, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1), (47, 1), (54, 1), (59, 1), (65, 1)] }, { coefficient := -1, powers := [(6, 1), (20, 1), (48, 1), (53, 1), (59, 1), (63, 1)] }, { coefficient := -1, powers := [(6, 1), (21, 1), (25, 1), (46, 1), (53, 1), (59, 1), (63, 1)] }, { coefficient := 1, powers := [(6, 1), (25, 1), (42, 1), (57, 1), (59, 1), (63, 1)] }, { coefficient := 1, powers := [(6, 1), (25, 1), (48, 1), (53, 1), (59, 1), (63, 1)] }, { coefficient := -1, powers := [(13, 1), (20, 1), (25, 1), (41, 1), (46, 1), (50, 1), (58, 1), (65, 1)] }, { coefficient := 1, powers := [(13, 1), (20, 1), (25, 1), (44, 1), (46, 2), (50, 1), (54, 1), (65, 1)] }, { coefficient := -1, powers := [(13, 1), (20, 1), (25, 1), (46, 1), (47, 1), (50, 1), (54, 1), (65, 1)] }, { coefficient := 1, powers := [(20, 1), (25, 1), (41, 1), (45, 1), (50, 1), (58, 1), (65, 1)] }, { coefficient := -1, powers := [(20, 1), (25, 1), (44, 1), (45, 1), (46, 1), (50, 1), (54, 1), (65, 1)] }, { coefficient := 1, powers := [(20, 1), (25, 1), (45, 1), (47, 1), (50, 1), (54, 1), (65, 1)] }, { coefficient := 1, powers := [(20, 1), (26, 1), (43, 1), (47, 1), (50, 1), (52, 1), (65, 1)] }, { coefficient := -1, powers := [(20, 1), (37, 1), (52, 1), (59, 1)] }, { coefficient := -1, powers := [(20, 1), (41, 1), (43, 1), (50, 1), (58, 1), (65, 1)] }, { coefficient := -1, powers := [(20, 1), (43, 1), (47, 1), (50, 1), (54, 1), (65, 1)] }, { coefficient := 1, powers := [(20, 1), (43, 1), (50, 1), (52, 1)] }, { coefficient := 1, powers := [(26, 1), (31, 1), (37, 1), (43, 1), (47, 1), (52, 1), (65, 1)] }, { coefficient := 1, powers := [(26, 1), (47, 1), (52, 1), (65, 1)] }, { coefficient := -1, powers := [(31, 1), (37, 1), (41, 1), (43, 1), (58, 1), (65, 1)] }, { coefficient := -1, powers := [(31, 1), (37, 1), (43, 1), (47, 1), (54, 1), (65, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1), (43, 1), (52, 1)] }, { coefficient := -1, powers := [(41, 1), (58, 1), (65, 1)] }, { coefficient := -1, powers := [(47, 1), (54, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (20, 1), (52, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (25, 1), (43, 1), (52, 1), (58, 1), (65, 1)] }, { coefficient := -1, powers := [(0, 1), (43, 1), (58, 1), (65, 1)] }, { coefficient := 1, powers := [(6, 1), (13, 1), (25, 1), (60, 1)] }, { coefficient := -1, powers := [(6, 1), (20, 1), (34, 1), (52, 1)] }, { coefficient := 1, powers := [(6, 1), (25, 1), (26, 1), (43, 1), (47, 1), (60, 1), (65, 1)] }, { coefficient := 1, powers := [(13, 1), (25, 2), (41, 1)] }, { coefficient := 3, powers := [(20, 1), (25, 1), (26, 1), (43, 1), (47, 1), (52, 1), (65, 1)] }, { coefficient := 1, powers := [(20, 1), (25, 1), (43, 1), (52, 1)] }, { coefficient := -2, powers := [(20, 1), (26, 1), (43, 1), (47, 1), (65, 1)] }, { coefficient := 1, powers := [(25, 2), (26, 1), (41, 1), (43, 1), (47, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (25, 2), (46, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (25, 1), (59, 1)] }, { coefficient := -1, powers := [(6, 1), (20, 1), (25, 1), (46, 1), (59, 1)] }, { coefficient := -1, powers := [(6, 1), (20, 1), (59, 1)] }],
  [{ coefficient := -2, powers := [(3, 1), (20, 1), (31, 1), (52, 1)] }, { coefficient := 1, powers := [(9, 1), (20, 1), (25, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (25, 1), (31, 1), (43, 1), (52, 1)] }, { coefficient := -1, powers := [(3, 1), (31, 1), (43, 1)] }, { coefficient := -1, powers := [(6, 1), (9, 1), (25, 1), (43, 1), (60, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 2), (52, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1), (59, 1)] }, { coefficient := -2, powers := [(9, 1), (20, 1), (25, 1), (43, 1), (52, 1)] }, { coefficient := 1, powers := [(9, 1), (20, 1), (43, 1)] }, { coefficient := -1, powers := [(9, 1), (25, 2), (41, 1), (43, 1)] }, { coefficient := -1, powers := [(13, 1), (20, 1), (25, 1), (46, 1), (50, 1)] }, { coefficient := -1, powers := [(20, 2), (43, 1), (50, 1), (52, 1)] }, { coefficient := 1, powers := [(20, 1), (25, 1), (45, 1), (50, 1)] }, { coefficient := -1, powers := [(20, 1), (31, 1), (37, 1), (43, 1), (52, 1)] }, { coefficient := -1, powers := [(20, 1), (43, 1), (50, 1)] }, { coefficient := -1, powers := [(20, 1), (52, 1)] }, { coefficient := -1, powers := [(31, 1), (37, 1), (43, 1)] }, { coefficient := -1, powers := [] }]
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
    (values : Fin 66 → R) :
    ¬ ∀ index : Fin 28,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component37.SelectedLeafB0_3_3.selectedHasNoCommonZero

end Krenn.Component37.SelectedLeafB0_3_3
