import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component37.SelectedLeafB5_2_1

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "38ed22121a1304a360f8a44242b727e5b36821d0e1a9100fc472dafa9499c533"
def certificateSHA256 : String := "98a3fa2c7afc173b2a542e78ae4864bc6f513bb5169242d99d47271fecde12e5"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 30 → Fin 667 := ![
  13,
  17,
  149,
  152,
  175,
  221,
  300,
  301,
  312,
  313,
  340,
  406,
  427,
  435,
  453,
  466,
  489,
  581,
  583,
  584,
  591,
  602,
  603,
  612,
  655,
  660,
  661,
  664,
  665,
  666
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 30 → SparsePoly (Fin 66) := ![
  [{ coefficient := 1, powers := [(17, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (26, 1)] }, { coefficient := 1, powers := [(26, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (44, 1)] }, { coefficient := 1, powers := [(40, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (20, 1)] }, { coefficient := 1, powers := [(18, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (26, 1), (47, 1)] }, { coefficient := 1, powers := [(9, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (50, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (50, 1)] }, { coefficient := 1, powers := [(18, 1), (28, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (59, 1)] }, { coefficient := 1, powers := [(9, 1), (43, 1)] }, { coefficient := 1, powers := [(13, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (54, 1)] }, { coefficient := 1, powers := [(30, 1), (41, 1)] }, { coefficient := 1, powers := [(30, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(20, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(44, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (44, 1)] }, { coefficient := 1, powers := [(19, 1), (23, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (20, 1), (50, 1)] }, { coefficient := 1, powers := [(18, 1), (25, 1), (40, 1)] }, { coefficient := 1, powers := [(18, 1), (31, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (54, 1)] }, { coefficient := 1, powers := [(3, 1), (26, 1), (60, 1)] }, { coefficient := 1, powers := [(20, 1), (54, 1)] }, { coefficient := 1, powers := [(26, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (52, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (52, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (57, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (41, 1)] }, { coefficient := 1, powers := [(18, 1), (46, 1)] }, { coefficient := 1, powers := [(18, 1), (52, 1)] }, { coefficient := 1, powers := [(18, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1), (54, 1)] }, { coefficient := 1, powers := [(20, 1), (44, 1), (54, 1)] }, { coefficient := 1, powers := [(20, 1), (58, 1)] }, { coefficient := 1, powers := [(26, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (44, 1), (54, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (58, 1)] }, { coefficient := 1, powers := [(18, 1), (30, 1), (44, 1)] }, { coefficient := 1, powers := [(19, 1), (23, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (52, 1)] }, { coefficient := 1, powers := [(3, 1), (60, 1)] }, { coefficient := 1, powers := [(20, 1), (52, 1)] }, { coefficient := 1, powers := [(20, 1), (57, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (31, 1), (57, 1)] }, { coefficient := 1, powers := [(9, 1), (20, 1), (57, 1)] }, { coefficient := 1, powers := [(9, 1)] }, { coefficient := 1, powers := [(40, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (40, 1), (58, 1)] }, { coefficient := 1, powers := [(3, 1), (31, 1), (58, 1)] }, { coefficient := 1, powers := [(9, 1), (20, 1), (58, 1)] }, { coefficient := 1, powers := [(9, 1), (26, 1), (44, 1)] }, { coefficient := 1, powers := [(26, 1), (40, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (37, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (40, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (43, 1), (50, 1)] }, { coefficient := 1, powers := [(17, 1), (23, 1), (50, 1)] }, { coefficient := 1, powers := [(17, 1), (28, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1)] }, { coefficient := 1, powers := [(3, 1), (34, 1)] }, { coefficient := 1, powers := [(13, 1), (20, 1)] }, { coefficient := 1, powers := [(20, 1), (56, 1)] }, { coefficient := 1, powers := [(25, 1), (43, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (50, 1)] }, { coefficient := 1, powers := [(6, 1), (31, 1)] }, { coefficient := 1, powers := [(9, 1), (25, 1)] }, { coefficient := 1, powers := [(20, 1), (50, 1)] }, { coefficient := 1, powers := [(25, 1), (40, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1), (50, 1)] }, { coefficient := 1, powers := [(6, 1), (31, 1), (45, 1)] }, { coefficient := 1, powers := [(6, 1), (59, 1)] }, { coefficient := 1, powers := [(9, 1), (25, 1), (45, 1)] }, { coefficient := 1, powers := [(9, 1), (56, 1)] }, { coefficient := 1, powers := [(13, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (37, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (40, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (43, 1), (50, 1)] }, { coefficient := 1, powers := [(3, 1), (25, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (31, 1), (56, 1)] }, { coefficient := 1, powers := [(3, 1), (34, 1), (50, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (31, 1), (43, 1)] }, { coefficient := 1, powers := [(6, 1), (34, 1), (40, 1)] }, { coefficient := 1, powers := [(9, 1), (20, 1), (56, 1)] }, { coefficient := 1, powers := [(9, 1), (25, 1), (43, 1)] }, { coefficient := 1, powers := [(9, 1), (34, 1), (37, 1)] }, { coefficient := 1, powers := [(13, 1), (20, 1), (50, 1)] }, { coefficient := 1, powers := [(13, 1), (25, 1), (40, 1)] }, { coefficient := 1, powers := [(13, 1), (31, 1), (37, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(40, 1)] }],
  [{ coefficient := 1, powers := [(56, 1)] }],
  [{ coefficient := 1, powers := [(57, 1)] }],
  [{ coefficient := 1, powers := [(58, 1), (65, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 30 → SparsePoly (Fin 66) := ![
  [{ coefficient := -1, powers := [(0, 2), (18, 1), (23, 1), (29, 1), (63, 2)] }],
  [{ coefficient := 1, powers := [(0, 2), (18, 1), (23, 1), (29, 1), (43, 1), (63, 2)] }, { coefficient := -1, powers := [(0, 2), (29, 1), (43, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (3, 1), (23, 1), (43, 1), (60, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (13, 1), (20, 1), (29, 1), (63, 1)] }, { coefficient := 1, powers := [(0, 1), (13, 1), (25, 1), (29, 1), (63, 1)] }, { coefficient := 1, powers := [(0, 1), (23, 1), (37, 1), (43, 1), (60, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (25, 1), (29, 1), (43, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (29, 1), (34, 1), (37, 1), (63, 1)] }, { coefficient := -1, powers := [(3, 1), (20, 1), (23, 1), (43, 1), (60, 1), (63, 1)] }, { coefficient := -1, powers := [(3, 1), (23, 1), (25, 1), (43, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(13, 1), (20, 1), (23, 1), (37, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(23, 1), (25, 1), (37, 1), (43, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(23, 1), (34, 1), (37, 2), (60, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(13, 1), (20, 1), (37, 1), (47, 1), (60, 1), (65, 1)] }, { coefficient := 1, powers := [(20, 1), (37, 1), (43, 1), (47, 1), (60, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (26, 1), (37, 1), (60, 1), (65, 1)] }, { coefficient := -1, powers := [(26, 1), (37, 1), (43, 1), (60, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (6, 1), (29, 1), (59, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (20, 1), (37, 1), (60, 1), (65, 1)] }, { coefficient := -1, powers := [(20, 1), (37, 1), (43, 1), (60, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(0, 2), (18, 1), (29, 1), (43, 1), (63, 2)] }, { coefficient := 1, powers := [(0, 1), (3, 1), (43, 1), (60, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (37, 1), (43, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(3, 1), (20, 1), (43, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(3, 1), (25, 1), (43, 1), (60, 1), (63, 1)] }, { coefficient := -1, powers := [(13, 1), (20, 1), (37, 1), (60, 1), (63, 1)] }, { coefficient := -1, powers := [(25, 1), (37, 1), (43, 1), (60, 1), (63, 1)] }, { coefficient := -1, powers := [(34, 1), (37, 2), (60, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (18, 1), (25, 1), (29, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (37, 1), (60, 1)] }, { coefficient := -1, powers := [(3, 1), (25, 1), (60, 1)] }, { coefficient := -1, powers := [(6, 1), (20, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (18, 1), (44, 1), (63, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(26, 1), (52, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (54, 1), (63, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (13, 1), (29, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (25, 1), (29, 1), (45, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (29, 1), (43, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(44, 1), (52, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (58, 1), (63, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (30, 1), (44, 1), (63, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(52, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (52, 1), (63, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(26, 1), (44, 1), (52, 1), (65, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := -1, powers := [(0, 1), (18, 1), (25, 1), (29, 1), (43, 1), (63, 1)] }, { coefficient := 1, powers := [(0, 1), (18, 1), (29, 1), (34, 1), (37, 1), (63, 1)] }, { coefficient := 1, powers := [(0, 1), (37, 1), (43, 1), (60, 1)] }, { coefficient := 1, powers := [(3, 1), (25, 1), (43, 1), (60, 1)] }, { coefficient := -1, powers := [(3, 1), (34, 1), (37, 1), (60, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1), (43, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(13, 1), (37, 1), (60, 1), (65, 1)] }, { coefficient := 1, powers := [(37, 1), (43, 1), (60, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(0, 2), (18, 1), (29, 1), (63, 2)] }],
  [{ coefficient := 1, powers := [(0, 1), (18, 1), (29, 1), (50, 1), (63, 1)] }, { coefficient := -1, powers := [(3, 1), (50, 1), (60, 1)] }, { coefficient := 1, powers := [(37, 1), (50, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (18, 1), (25, 1), (29, 1), (45, 1), (63, 1)] }, { coefficient := 1, powers := [(0, 1), (18, 1), (29, 1), (43, 1), (63, 1)] }, { coefficient := -1, powers := [(3, 1), (43, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (18, 1), (25, 1), (29, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (18, 1), (29, 1), (63, 1)] }, { coefficient := 1, powers := [(3, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(0, 2), (18, 1), (29, 1), (37, 1), (59, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (3, 1), (43, 1), (50, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (37, 1), (43, 1), (50, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (52, 1)] }, { coefficient := -1, powers := [(3, 1), (20, 1), (43, 1), (50, 1), (60, 1)] }, { coefficient := -1, powers := [(3, 1), (25, 1), (43, 1), (50, 1), (60, 1)] }, { coefficient := 1, powers := [(13, 1), (20, 1), (37, 1), (50, 1), (60, 1)] }, { coefficient := 1, powers := [(25, 1), (37, 1), (43, 1), (50, 1), (60, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 2), (50, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(0, 2), (2, 1), (18, 1), (29, 1), (56, 1), (63, 2)] }, { coefficient := -1, powers := [(0, 2), (17, 1), (18, 1), (28, 1), (29, 1), (63, 2)] }, { coefficient := 1, powers := [(0, 2), (18, 2), (28, 1), (29, 1), (43, 1), (63, 2)] }, { coefficient := 1, powers := [(0, 2), (18, 1), (25, 1), (29, 1), (43, 1), (57, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 2), (18, 1), (29, 1), (34, 1), (37, 1), (57, 1), (63, 1)] }, { coefficient := 1, powers := [(0, 2), (18, 1), (29, 1), (56, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 2), (37, 1), (43, 1), (57, 1), (60, 1)] }, { coefficient := -1, powers := [(0, 1), (3, 1), (18, 1), (28, 1), (43, 1), (60, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (3, 1), (25, 1), (43, 1), (57, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (3, 1), (34, 1), (37, 1), (57, 1), (60, 1)] }, { coefficient := -1, powers := [(0, 1), (3, 1), (56, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (6, 1), (18, 1), (29, 1), (34, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (6, 1), (20, 1), (43, 1), (57, 1), (60, 1)] }, { coefficient := -1, powers := [(0, 1), (13, 1), (18, 1), (25, 1), (29, 1), (63, 1)] }, { coefficient := 1, powers := [(0, 1), (13, 1), (37, 1), (58, 1), (60, 1), (65, 1)] }, { coefficient := 1, powers := [(0, 1), (13, 1), (37, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (18, 1), (25, 1), (29, 1), (43, 1), (63, 1)] }, { coefficient := 1, powers := [(0, 1), (18, 1), (28, 1), (37, 1), (43, 1), (60, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (18, 1), (29, 1), (34, 1), (37, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (37, 1), (43, 1), (58, 1), (60, 1), (65, 1)] }, { coefficient := -1, powers := [(0, 1), (37, 1), (43, 1), (60, 1)] }, { coefficient := -1, powers := [(3, 1), (6, 1), (34, 1), (60, 1)] }, { coefficient := -1, powers := [(3, 1), (18, 1), (20, 1), (28, 1), (43, 1), (60, 1), (63, 1)] }, { coefficient := -1, powers := [(3, 1), (18, 1), (25, 1), (28, 1), (43, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(3, 1), (34, 1), (37, 1), (60, 1)] }, { coefficient := 1, powers := [(6, 1), (13, 1), (20, 1), (60, 1)] }, { coefficient := -1, powers := [(6, 1), (20, 1), (43, 1), (60, 1)] }, { coefficient := 1, powers := [(13, 1), (18, 1), (20, 1), (28, 1), (37, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(13, 1), (20, 1), (26, 1), (37, 1), (47, 1), (60, 1), (65, 1)] }, { coefficient := 1, powers := [(18, 1), (25, 1), (28, 1), (37, 1), (43, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(18, 1), (28, 1), (34, 1), (37, 2), (60, 1), (63, 1)] }, { coefficient := -1, powers := [(20, 1), (26, 1), (37, 1), (43, 1), (47, 1), (60, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (3, 1), (18, 1), (29, 1), (31, 1), (63, 1)] }, { coefficient := 1, powers := [(0, 1), (9, 1), (18, 1), (20, 1), (29, 1), (63, 1)] }, { coefficient := 1, powers := [(0, 1), (9, 1), (18, 1), (25, 1), (29, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (18, 1), (20, 1), (29, 1), (50, 1), (63, 1)] }, { coefficient := -1, powers := [(3, 2), (31, 1), (60, 1)] }, { coefficient := -1, powers := [(3, 1), (9, 1), (20, 1), (60, 1)] }, { coefficient := 1, powers := [(3, 1), (20, 1), (50, 1), (60, 1)] }, { coefficient := -1, powers := [(20, 1), (37, 1), (50, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (3, 1), (18, 1), (25, 1), (29, 1), (31, 1), (43, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (3, 1), (18, 1), (29, 1), (31, 1), (34, 1), (37, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (3, 1), (31, 1), (37, 1), (43, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (9, 1), (18, 1), (20, 1), (25, 1), (29, 1), (43, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (9, 1), (18, 1), (20, 1), (29, 1), (34, 1), (37, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (9, 1), (20, 1), (37, 1), (43, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (18, 1), (23, 1), (58, 1), (63, 1), (65, 1)] }, { coefficient := 1, powers := [(0, 1), (18, 1), (30, 1), (44, 1), (63, 1), (65, 1)] }, { coefficient := -1, powers := [(3, 2), (25, 1), (31, 1), (43, 1), (60, 1)] }, { coefficient := 1, powers := [(3, 2), (31, 1), (34, 1), (37, 1), (60, 1)] }, { coefficient := -1, powers := [(3, 1), (6, 1), (20, 1), (31, 1), (43, 1), (60, 1)] }, { coefficient := -1, powers := [(3, 1), (9, 1), (20, 1), (25, 1), (43, 1), (60, 1)] }, { coefficient := 1, powers := [(3, 1), (9, 1), (20, 1), (34, 1), (37, 1), (60, 1)] }, { coefficient := -1, powers := [(6, 1), (9, 1), (20, 2), (43, 1), (60, 1)] }, { coefficient := 1, powers := [(20, 1), (26, 1), (44, 1), (52, 1), (65, 1)] }, { coefficient := -1, powers := [(20, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (2, 1), (52, 1), (63, 1)] }, { coefficient := 1, powers := [(0, 1), (18, 1), (29, 1), (63, 1)] }, { coefficient := 1, powers := [(3, 1), (13, 1), (31, 1), (37, 1), (60, 1)] }, { coefficient := -1, powers := [(3, 1), (31, 1), (37, 1), (43, 1), (60, 1)] }, { coefficient := 1, powers := [(20, 1), (52, 1)] }]
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
    ¬ ∀ index : Fin 30,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component37.SelectedLeafB5_2_1.selectedHasNoCommonZero

end Krenn.Component37.SelectedLeafB5_2_1
