import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component60.SelectedLeafB6_6_3_4_2

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "814c2ddbd23cdb32802cd9957860249261b08a4f8342696500ac0c42c08e8ef6"
def certificateSHA256 : String := "872d5f823081b53f7e7faa70fc41413985e5a9bd3da3ea9b983dc23930c38a21"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 31 → Fin 671 := ![
  8,
  18,
  20,
  22,
  23,
  68,
  143,
  149,
  301,
  302,
  303,
  318,
  359,
  443,
  556,
  593,
  600,
  627,
  653,
  655,
  657,
  658,
  659,
  661,
  662,
  663,
  664,
  666,
  667,
  668,
  670
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 31 → SparsePoly (Fin 69) := ![
  [{ coefficient := 1, powers := [(7, 1), (32, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (24, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (47, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (30, 1)] }, { coefficient := 1, powers := [(18, 1), (26, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (48, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1)] }, { coefficient := 1, powers := [(12, 1), (29, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (58, 1)] }, { coefficient := 1, powers := [(9, 1), (42, 1)] }, { coefficient := 1, powers := [(13, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(7, 1), (34, 1), (39, 1)] }, { coefficient := 1, powers := [(15, 1), (28, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (30, 1), (57, 1)] }, { coefficient := 1, powers := [(8, 1), (30, 1), (48, 1)] }, { coefficient := 1, powers := [(19, 1), (30, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (54, 1)] }, { coefficient := 1, powers := [(29, 1), (41, 1)] }, { coefficient := 1, powers := [(29, 1), (47, 1), (50, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (43, 1), (53, 1)] }, { coefficient := 1, powers := [(24, 1), (57, 1)] }, { coefficient := 1, powers := [(29, 1), (48, 1)] }, { coefficient := 1, powers := [(35, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (41, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (47, 1), (52, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (56, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (56, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1)] }, { coefficient := 1, powers := [(3, 1), (33, 1)] }, { coefficient := 1, powers := [(13, 1), (20, 1)] }, { coefficient := 1, powers := [(20, 1), (55, 1)] }, { coefficient := 1, powers := [(25, 1), (42, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (34, 1), (49, 1)] }, { coefficient := 1, powers := [(6, 1), (34, 1), (39, 1)] }, { coefficient := 1, powers := [(9, 1), (27, 1)] }, { coefficient := 1, powers := [(9, 1), (34, 1), (36, 1)] }, { coefficient := 1, powers := [(22, 1), (49, 1)] }, { coefficient := 1, powers := [(27, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (36, 1), (58, 1)] }, { coefficient := 1, powers := [(0, 1), (39, 1), (55, 1)] }, { coefficient := 1, powers := [(0, 1), (42, 1), (49, 1)] }, { coefficient := 1, powers := [(3, 1), (25, 1), (58, 1)] }, { coefficient := 1, powers := [(3, 1), (30, 1), (55, 1)] }, { coefficient := 1, powers := [(3, 1), (33, 1), (49, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1), (58, 1)] }, { coefficient := 1, powers := [(6, 1), (30, 1), (42, 1)] }, { coefficient := 1, powers := [(6, 1), (33, 1), (39, 1)] }, { coefficient := 1, powers := [(9, 1), (20, 1), (55, 1)] }, { coefficient := 1, powers := [(9, 1), (25, 1), (42, 1)] }, { coefficient := 1, powers := [(9, 1), (33, 1), (36, 1)] }, { coefficient := 1, powers := [(13, 1), (20, 1), (49, 1)] }, { coefficient := 1, powers := [(13, 1), (25, 1), (39, 1)] }, { coefficient := 1, powers := [(13, 1), (30, 1), (36, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (41, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (48, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (48, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1), (29, 1), (48, 1)] }, { coefficient := 1, powers := [(12, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (54, 1)] }, { coefficient := 1, powers := [(19, 1), (29, 1), (41, 1)] }, { coefficient := 1, powers := [(19, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(39, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(41, 1)] }],
  [{ coefficient := 1, powers := [(55, 1)] }],
  [{ coefficient := 1, powers := [(56, 1), (65, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(57, 1), (66, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(28, 1)] }],
  [{ coefficient := 1, powers := [(29, 1)] }],
  [{ coefficient := 1, powers := [(58, 1)] }],
  [{ coefficient := 1, powers := [(60, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 31 → SparsePoly (Fin 69) := ![
  [{ coefficient := 1, powers := [(3, 1), (5, 1), (33, 1), (34, 1), (49, 1), (57, 1), (62, 1), (65, 1)] }, { coefficient := 1, powers := [(5, 1), (9, 1), (27, 1), (33, 1), (57, 1), (62, 1), (65, 1)] }, { coefficient := 1, powers := [(5, 1), (9, 1), (33, 1), (34, 1), (36, 1), (57, 1), (62, 1), (65, 1)] }, { coefficient := 1, powers := [(5, 1), (22, 1), (33, 1), (49, 1), (57, 1), (62, 1), (65, 1)] }, { coefficient := 1, powers := [(5, 1), (27, 1), (33, 1), (39, 1), (57, 1), (62, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (26, 1), (32, 1), (42, 1), (48, 1)] }, { coefficient := 1, powers := [(13, 1), (26, 1), (32, 1), (36, 1), (48, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (7, 1), (24, 1), (33, 1), (34, 1), (49, 1), (54, 1), (62, 1), (63, 1), (65, 1)] }, { coefficient := -1, powers := [(6, 1), (24, 1), (30, 1), (42, 1), (54, 1), (63, 1)] }, { coefficient := -1, powers := [(6, 1), (30, 1), (32, 1), (38, 1), (42, 1), (63, 1)] }, { coefficient := -1, powers := [(7, 1), (9, 1), (24, 1), (27, 1), (33, 1), (54, 1), (62, 1), (63, 1), (65, 1)] }, { coefficient := -1, powers := [(7, 1), (9, 1), (24, 1), (33, 1), (34, 1), (36, 1), (54, 1), (62, 1), (63, 1), (65, 1)] }, { coefficient := -1, powers := [(7, 1), (22, 1), (24, 1), (33, 1), (49, 1), (54, 1), (62, 1), (63, 1), (65, 1)] }, { coefficient := -1, powers := [(7, 1), (24, 1), (27, 1), (33, 1), (39, 1), (54, 1), (62, 1), (63, 1), (65, 1)] }, { coefficient := -1, powers := [(9, 1), (24, 1), (33, 1), (36, 1), (54, 1), (57, 1), (63, 1), (66, 1)] }, { coefficient := -1, powers := [(13, 1), (24, 1), (30, 1), (36, 1), (54, 1), (63, 1)] }, { coefficient := -1, powers := [(13, 1), (30, 1), (32, 1), (36, 1), (38, 1), (63, 1)] }, { coefficient := 1, powers := [(24, 1), (25, 1), (42, 1), (49, 1), (54, 1), (57, 1), (63, 1), (66, 1)] }, { coefficient := 1, powers := [(24, 1), (33, 1), (36, 1), (49, 1), (54, 1), (57, 1), (63, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (7, 1), (12, 1), (33, 1), (34, 1), (49, 1), (53, 1), (62, 1), (65, 1)] }, { coefficient := -1, powers := [(6, 1), (12, 1), (30, 1), (42, 1), (53, 1)] }, { coefficient := -1, powers := [(7, 1), (9, 1), (12, 1), (27, 1), (33, 1), (53, 1), (62, 1), (65, 1)] }, { coefficient := -1, powers := [(7, 1), (9, 1), (12, 1), (33, 1), (34, 1), (36, 1), (53, 1), (62, 1), (65, 1)] }, { coefficient := -1, powers := [(7, 1), (12, 1), (22, 1), (33, 1), (49, 1), (53, 1), (62, 1), (65, 1)] }, { coefficient := -1, powers := [(7, 1), (12, 1), (27, 1), (33, 1), (39, 1), (53, 1), (62, 1), (65, 1)] }, { coefficient := -1, powers := [(9, 1), (12, 1), (33, 1), (36, 1), (53, 1), (57, 1), (66, 1)] }, { coefficient := -1, powers := [(12, 1), (13, 1), (30, 1), (36, 1), (53, 1)] }, { coefficient := 1, powers := [(12, 1), (25, 1), (42, 1), (49, 1), (53, 1), (57, 1), (66, 1)] }, { coefficient := 1, powers := [(12, 1), (33, 1), (36, 1), (49, 1), (53, 1), (57, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (25, 1), (42, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1), (33, 1), (36, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (33, 1), (36, 1), (57, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(9, 1), (33, 1), (36, 1), (52, 1), (57, 1), (65, 1)] }, { coefficient := 1, powers := [(25, 1), (42, 1), (49, 1), (52, 1), (57, 1), (65, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1), (49, 1), (52, 1), (57, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (32, 1), (42, 1), (48, 1)] }, { coefficient := -1, powers := [(13, 1), (32, 1), (36, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (7, 1), (33, 1), (34, 1), (49, 1), (54, 1), (62, 1), (65, 1)] }, { coefficient := 1, powers := [(6, 1), (30, 1), (42, 1), (54, 1)] }, { coefficient := 1, powers := [(7, 1), (9, 1), (27, 1), (33, 1), (54, 1), (62, 1), (65, 1)] }, { coefficient := 1, powers := [(7, 1), (9, 1), (33, 1), (34, 1), (36, 1), (54, 1), (62, 1), (65, 1)] }, { coefficient := 1, powers := [(7, 1), (22, 1), (33, 1), (49, 1), (54, 1), (62, 1), (65, 1)] }, { coefficient := 1, powers := [(7, 1), (27, 1), (33, 1), (39, 1), (54, 1), (62, 1), (65, 1)] }, { coefficient := 1, powers := [(9, 1), (33, 1), (36, 1), (54, 1), (57, 1), (66, 1)] }, { coefficient := 1, powers := [(13, 1), (30, 1), (36, 1), (54, 1)] }, { coefficient := -1, powers := [(25, 1), (42, 1), (49, 1), (54, 1), (57, 1), (66, 1)] }, { coefficient := -1, powers := [(33, 1), (36, 1), (49, 1), (54, 1), (57, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (7, 1), (33, 1), (34, 1), (48, 1), (49, 1), (62, 1), (65, 1)] }, { coefficient := 1, powers := [(6, 1), (30, 1), (42, 1), (48, 1)] }, { coefficient := 1, powers := [(7, 1), (9, 1), (27, 1), (33, 1), (48, 1), (62, 1), (65, 1)] }, { coefficient := 1, powers := [(7, 1), (9, 1), (33, 1), (34, 1), (36, 1), (48, 1), (62, 1), (65, 1)] }, { coefficient := 1, powers := [(7, 1), (22, 1), (33, 1), (48, 1), (49, 1), (62, 1), (65, 1)] }, { coefficient := 1, powers := [(7, 1), (27, 1), (33, 1), (39, 1), (48, 1), (62, 1), (65, 1)] }, { coefficient := 1, powers := [(9, 1), (33, 1), (36, 1), (48, 1), (57, 1), (66, 1)] }, { coefficient := 1, powers := [(13, 1), (30, 1), (36, 1), (48, 1)] }, { coefficient := -1, powers := [(25, 1), (42, 1), (48, 1), (49, 1), (57, 1), (66, 1)] }, { coefficient := -1, powers := [(33, 1), (36, 1), (48, 1), (49, 1), (57, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(25, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (33, 1), (62, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (32, 1), (42, 1)] }, { coefficient := 1, powers := [(13, 1), (32, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (7, 1), (19, 1), (33, 1), (34, 1), (49, 1), (62, 1), (65, 1)] }, { coefficient := 1, powers := [(6, 1), (19, 1), (30, 1), (42, 1)] }, { coefficient := 1, powers := [(7, 1), (9, 1), (19, 1), (27, 1), (33, 1), (62, 1), (65, 1)] }, { coefficient := 1, powers := [(7, 1), (9, 1), (19, 1), (33, 1), (34, 1), (36, 1), (62, 1), (65, 1)] }, { coefficient := 1, powers := [(7, 1), (19, 1), (22, 1), (33, 1), (49, 1), (62, 1), (65, 1)] }, { coefficient := 1, powers := [(7, 1), (19, 1), (27, 1), (33, 1), (39, 1), (62, 1), (65, 1)] }, { coefficient := 1, powers := [(9, 1), (19, 1), (33, 1), (36, 1), (57, 1), (66, 1)] }, { coefficient := 1, powers := [(13, 1), (19, 1), (30, 1), (36, 1)] }, { coefficient := -1, powers := [(19, 1), (25, 1), (42, 1), (49, 1), (57, 1), (66, 1)] }, { coefficient := -1, powers := [(19, 1), (33, 1), (36, 1), (49, 1), (57, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (7, 1), (12, 1), (33, 1), (34, 1), (49, 1), (62, 1), (65, 1)] }, { coefficient := 1, powers := [(6, 1), (12, 1), (30, 1), (42, 1)] }, { coefficient := 1, powers := [(7, 1), (9, 1), (12, 1), (27, 1), (33, 1), (62, 1), (65, 1)] }, { coefficient := 1, powers := [(7, 1), (9, 1), (12, 1), (33, 1), (34, 1), (36, 1), (62, 1), (65, 1)] }, { coefficient := 1, powers := [(7, 1), (12, 1), (22, 1), (33, 1), (49, 1), (62, 1), (65, 1)] }, { coefficient := 1, powers := [(7, 1), (12, 1), (27, 1), (33, 1), (39, 1), (62, 1), (65, 1)] }, { coefficient := 1, powers := [(9, 1), (12, 1), (33, 1), (36, 1), (57, 1), (66, 1)] }, { coefficient := 1, powers := [(12, 1), (13, 1), (30, 1), (36, 1)] }, { coefficient := -1, powers := [(12, 1), (25, 1), (42, 1), (49, 1), (57, 1), (66, 1)] }, { coefficient := -1, powers := [(12, 1), (33, 1), (36, 1), (49, 1), (57, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (33, 1), (36, 1), (57, 1), (65, 1)] }, { coefficient := -1, powers := [(25, 1), (42, 1), (49, 1), (57, 1), (65, 1)] }, { coefficient := -1, powers := [(33, 1), (36, 1), (49, 1), (57, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(49, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (33, 1), (62, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(3, 1), (7, 1), (33, 1), (34, 1), (49, 1), (62, 1), (65, 1)] }, { coefficient := -1, powers := [(6, 1), (30, 1), (42, 1)] }, { coefficient := -1, powers := [(7, 1), (9, 1), (27, 1), (33, 1), (62, 1), (65, 1)] }, { coefficient := -1, powers := [(7, 1), (9, 1), (33, 1), (34, 1), (36, 1), (62, 1), (65, 1)] }, { coefficient := -1, powers := [(7, 1), (22, 1), (33, 1), (49, 1), (62, 1), (65, 1)] }, { coefficient := -1, powers := [(7, 1), (27, 1), (33, 1), (39, 1), (62, 1), (65, 1)] }, { coefficient := -1, powers := [(9, 1), (33, 1), (36, 1), (57, 1), (66, 1)] }, { coefficient := -1, powers := [(13, 1), (30, 1), (36, 1)] }, { coefficient := 1, powers := [(25, 1), (42, 1), (49, 1), (57, 1), (66, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1), (49, 1), (57, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (33, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (7, 1), (33, 1), (34, 1), (38, 1), (49, 1), (60, 1), (62, 1), (65, 1)] }, { coefficient := -1, powers := [(3, 1), (7, 1), (33, 1), (34, 1), (48, 1), (49, 1), (54, 1), (62, 1), (65, 1)] }, { coefficient := 1, powers := [(6, 1), (30, 1), (38, 1), (42, 1), (60, 1)] }, { coefficient := -1, powers := [(6, 1), (30, 1), (42, 1), (48, 1), (54, 1)] }, { coefficient := 1, powers := [(7, 1), (9, 1), (27, 1), (33, 1), (38, 1), (60, 1), (62, 1), (65, 1)] }, { coefficient := -1, powers := [(7, 1), (9, 1), (27, 1), (33, 1), (48, 1), (54, 1), (62, 1), (65, 1)] }, { coefficient := 1, powers := [(7, 1), (9, 1), (33, 1), (34, 1), (36, 1), (38, 1), (60, 1), (62, 1), (65, 1)] }, { coefficient := -1, powers := [(7, 1), (9, 1), (33, 1), (34, 1), (36, 1), (48, 1), (54, 1), (62, 1), (65, 1)] }, { coefficient := 1, powers := [(7, 1), (22, 1), (33, 1), (38, 1), (49, 1), (60, 1), (62, 1), (65, 1)] }, { coefficient := -1, powers := [(7, 1), (22, 1), (33, 1), (48, 1), (49, 1), (54, 1), (62, 1), (65, 1)] }, { coefficient := 1, powers := [(7, 1), (27, 1), (33, 1), (38, 1), (39, 1), (60, 1), (62, 1), (65, 1)] }, { coefficient := -1, powers := [(7, 1), (27, 1), (33, 1), (39, 1), (48, 1), (54, 1), (62, 1), (65, 1)] }, { coefficient := 1, powers := [(9, 1), (33, 1), (36, 1), (38, 1), (57, 1), (60, 1), (66, 1)] }, { coefficient := -1, powers := [(9, 1), (33, 1), (36, 1), (48, 1), (54, 1), (57, 1), (66, 1)] }, { coefficient := 1, powers := [(13, 1), (30, 1), (36, 1), (38, 1), (60, 1)] }, { coefficient := -1, powers := [(13, 1), (30, 1), (36, 1), (48, 1), (54, 1)] }, { coefficient := -1, powers := [(25, 1), (38, 1), (42, 1), (49, 1), (57, 1), (60, 1), (66, 1)] }, { coefficient := 1, powers := [(25, 1), (42, 1), (48, 1), (49, 1), (54, 1), (57, 1), (66, 1)] }, { coefficient := -1, powers := [(33, 1), (36, 1), (38, 1), (49, 1), (57, 1), (60, 1), (66, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1), (48, 1), (49, 1), (54, 1), (57, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (7, 1), (19, 1), (24, 1), (33, 1), (34, 1), (49, 1), (54, 1), (62, 1), (65, 1)] }, { coefficient := 1, powers := [(6, 1), (19, 1), (24, 1), (30, 1), (42, 1), (54, 1)] }, { coefficient := 1, powers := [(6, 1), (19, 1), (30, 1), (32, 1), (38, 1), (42, 1)] }, { coefficient := 1, powers := [(7, 1), (9, 1), (19, 1), (24, 1), (27, 1), (33, 1), (54, 1), (62, 1), (65, 1)] }, { coefficient := 1, powers := [(7, 1), (9, 1), (19, 1), (24, 1), (33, 1), (34, 1), (36, 1), (54, 1), (62, 1), (65, 1)] }, { coefficient := 1, powers := [(7, 1), (19, 1), (22, 1), (24, 1), (33, 1), (49, 1), (54, 1), (62, 1), (65, 1)] }, { coefficient := 1, powers := [(7, 1), (19, 1), (24, 1), (27, 1), (33, 1), (39, 1), (54, 1), (62, 1), (65, 1)] }, { coefficient := 1, powers := [(9, 1), (19, 1), (24, 1), (33, 1), (36, 1), (54, 1), (57, 1), (66, 1)] }, { coefficient := 1, powers := [(13, 1), (19, 1), (24, 1), (30, 1), (36, 1), (54, 1)] }, { coefficient := 1, powers := [(13, 1), (19, 1), (30, 1), (32, 1), (36, 1), (38, 1)] }, { coefficient := -1, powers := [(19, 1), (24, 1), (25, 1), (42, 1), (49, 1), (54, 1), (57, 1), (66, 1)] }, { coefficient := -1, powers := [(19, 1), (24, 1), (33, 1), (36, 1), (49, 1), (54, 1), (57, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (3, 1), (7, 1), (33, 1), (34, 1), (49, 1), (57, 1), (62, 1), (65, 1)] }, { coefficient := 1, powers := [(2, 1), (6, 1), (30, 1), (42, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (7, 1), (9, 1), (27, 1), (33, 1), (57, 1), (62, 1), (65, 1)] }, { coefficient := 1, powers := [(2, 1), (7, 1), (9, 1), (33, 1), (34, 1), (36, 1), (57, 1), (62, 1), (65, 1)] }, { coefficient := 1, powers := [(2, 1), (7, 1), (22, 1), (33, 1), (49, 1), (57, 1), (62, 1), (65, 1)] }, { coefficient := 1, powers := [(2, 1), (7, 1), (27, 1), (33, 1), (39, 1), (57, 1), (62, 1), (65, 1)] }, { coefficient := -1, powers := [(2, 1), (9, 1), (33, 1), (36, 1), (56, 1), (57, 1), (65, 1)] }, { coefficient := 1, powers := [(2, 1), (9, 1), (33, 1), (36, 1), (57, 2), (66, 1)] }, { coefficient := 1, powers := [(2, 1), (13, 1), (30, 1), (36, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (25, 1), (42, 1), (49, 1), (56, 1), (57, 1), (65, 1)] }, { coefficient := -1, powers := [(2, 1), (25, 1), (42, 1), (49, 1), (57, 2), (66, 1)] }, { coefficient := 1, powers := [(2, 1), (33, 1), (36, 1), (49, 1), (56, 1), (57, 1), (65, 1)] }, { coefficient := -1, powers := [(2, 1), (33, 1), (36, 1), (49, 1), (57, 2), (66, 1)] }, { coefficient := 1, powers := [(3, 1), (7, 1), (8, 1), (33, 1), (34, 1), (35, 1), (49, 1), (62, 1), (65, 1)] }, { coefficient := 1, powers := [(6, 1), (8, 1), (30, 1), (35, 1), (42, 1)] }, { coefficient := 1, powers := [(7, 1), (8, 1), (9, 1), (27, 1), (33, 1), (35, 1), (62, 1), (65, 1)] }, { coefficient := 1, powers := [(7, 1), (8, 1), (9, 1), (33, 1), (34, 1), (35, 1), (36, 1), (62, 1), (65, 1)] }, { coefficient := 1, powers := [(7, 1), (8, 1), (22, 1), (33, 1), (35, 1), (49, 1), (62, 1), (65, 1)] }, { coefficient := 1, powers := [(7, 1), (8, 1), (27, 1), (33, 1), (35, 1), (39, 1), (62, 1), (65, 1)] }, { coefficient := 1, powers := [(8, 1), (9, 1), (33, 1), (35, 1), (36, 1), (57, 1), (66, 1)] }, { coefficient := 1, powers := [(8, 1), (13, 1), (30, 1), (35, 1), (36, 1)] }, { coefficient := -1, powers := [(8, 1), (25, 1), (35, 1), (42, 1), (49, 1), (57, 1), (66, 1)] }, { coefficient := -1, powers := [(8, 1), (33, 1), (35, 1), (36, 1), (49, 1), (57, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (39, 1)] }, { coefficient := 1, powers := [(3, 1), (30, 1)] }, { coefficient := 1, powers := [(9, 1), (20, 1)] }, { coefficient := -1, powers := [(20, 1), (49, 1)] }],
  [{ coefficient := -1, powers := [(1, 1), (6, 1), (33, 1), (39, 1), (62, 1)] }, { coefficient := -1, powers := [(5, 1), (9, 1), (32, 1), (33, 1), (36, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (25, 1), (32, 1), (42, 1), (49, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (33, 1), (36, 1), (49, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (25, 1), (42, 1), (49, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (33, 1), (36, 1), (49, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (9, 1), (32, 1), (33, 1), (36, 1), (57, 1)] }, { coefficient := -1, powers := [(5, 1), (25, 1), (32, 1), (42, 1), (49, 1), (57, 1)] }, { coefficient := -1, powers := [(5, 1), (32, 1), (33, 1), (36, 1), (49, 1), (57, 1)] }, { coefficient := -1, powers := [(9, 1), (33, 1), (36, 1)] }, { coefficient := 1, powers := [(25, 1), (42, 1), (49, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1), (49, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (15, 1), (33, 1), (39, 1), (62, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (5, 1), (7, 1), (33, 1), (34, 1), (49, 1), (60, 1), (62, 1), (65, 1)] }, { coefficient := -1, powers := [(3, 1), (7, 1), (12, 1), (33, 1), (34, 1), (48, 1), (49, 1), (62, 1), (65, 1)] }, { coefficient := -1, powers := [(3, 1), (7, 1), (19, 1), (33, 1), (34, 1), (47, 1), (49, 1), (50, 1), (62, 1), (65, 1)] }, { coefficient := 1, powers := [(5, 1), (6, 1), (30, 1), (42, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (7, 1), (9, 1), (27, 1), (33, 1), (60, 1), (62, 1), (65, 1)] }, { coefficient := 1, powers := [(5, 1), (7, 1), (9, 1), (33, 1), (34, 1), (36, 1), (60, 1), (62, 1), (65, 1)] }, { coefficient := 1, powers := [(5, 1), (7, 1), (22, 1), (33, 1), (49, 1), (60, 1), (62, 1), (65, 1)] }, { coefficient := 1, powers := [(5, 1), (7, 1), (27, 1), (33, 1), (39, 1), (60, 1), (62, 1), (65, 1)] }, { coefficient := 1, powers := [(5, 1), (9, 1), (33, 1), (36, 1), (57, 1), (60, 1), (66, 1)] }, { coefficient := 1, powers := [(5, 1), (13, 1), (30, 1), (36, 1), (60, 1)] }, { coefficient := -1, powers := [(5, 1), (25, 1), (42, 1), (49, 1), (57, 1), (60, 1), (66, 1)] }, { coefficient := -1, powers := [(5, 1), (33, 1), (36, 1), (49, 1), (57, 1), (60, 1), (66, 1)] }, { coefficient := -1, powers := [(6, 1), (12, 1), (30, 1), (42, 1), (48, 1)] }, { coefficient := -1, powers := [(6, 1), (19, 1), (30, 1), (42, 1), (47, 1), (50, 1)] }, { coefficient := -1, powers := [(7, 1), (9, 1), (12, 1), (27, 1), (33, 1), (48, 1), (62, 1), (65, 1)] }, { coefficient := -1, powers := [(7, 1), (9, 1), (12, 1), (33, 1), (34, 1), (36, 1), (48, 1), (62, 1), (65, 1)] }, { coefficient := -1, powers := [(7, 1), (9, 1), (19, 1), (27, 1), (33, 1), (47, 1), (50, 1), (62, 1), (65, 1)] }, { coefficient := -1, powers := [(7, 1), (9, 1), (19, 1), (33, 1), (34, 1), (36, 1), (47, 1), (50, 1), (62, 1), (65, 1)] }, { coefficient := -1, powers := [(7, 1), (12, 1), (22, 1), (33, 1), (48, 1), (49, 1), (62, 1), (65, 1)] }, { coefficient := -1, powers := [(7, 1), (12, 1), (27, 1), (33, 1), (39, 1), (48, 1), (62, 1), (65, 1)] }, { coefficient := -1, powers := [(7, 1), (19, 1), (22, 1), (33, 1), (47, 1), (49, 1), (50, 1), (62, 1), (65, 1)] }, { coefficient := -1, powers := [(7, 1), (19, 1), (27, 1), (33, 1), (39, 1), (47, 1), (50, 1), (62, 1), (65, 1)] }, { coefficient := -1, powers := [(9, 1), (12, 1), (33, 1), (36, 1), (48, 1), (57, 1), (66, 1)] }, { coefficient := -1, powers := [(9, 1), (19, 1), (33, 1), (36, 1), (47, 1), (50, 1), (57, 1), (66, 1)] }, { coefficient := -1, powers := [(12, 1), (13, 1), (30, 1), (36, 1), (48, 1)] }, { coefficient := 1, powers := [(12, 1), (25, 1), (42, 1), (48, 1), (49, 1), (57, 1), (66, 1)] }, { coefficient := 1, powers := [(12, 1), (33, 1), (36, 1), (48, 1), (49, 1), (57, 1), (66, 1)] }, { coefficient := -1, powers := [(13, 1), (19, 1), (30, 1), (36, 1), (47, 1), (50, 1)] }, { coefficient := 1, powers := [(19, 1), (25, 1), (42, 1), (47, 1), (49, 1), (50, 1), (57, 1), (66, 1)] }, { coefficient := 1, powers := [(19, 1), (33, 1), (36, 1), (47, 1), (49, 1), (50, 1), (57, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (36, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (7, 1), (8, 1), (24, 1), (33, 1), (34, 1), (49, 1), (62, 1), (65, 1)] }, { coefficient := 1, powers := [(6, 1), (8, 1), (24, 1), (30, 1), (42, 1)] }, { coefficient := 1, powers := [(7, 1), (8, 1), (9, 1), (24, 1), (27, 1), (33, 1), (62, 1), (65, 1)] }, { coefficient := 1, powers := [(7, 1), (8, 1), (9, 1), (24, 1), (33, 1), (34, 1), (36, 1), (62, 1), (65, 1)] }, { coefficient := 1, powers := [(7, 1), (8, 1), (22, 1), (24, 1), (33, 1), (49, 1), (62, 1), (65, 1)] }, { coefficient := 1, powers := [(7, 1), (8, 1), (24, 1), (27, 1), (33, 1), (39, 1), (62, 1), (65, 1)] }, { coefficient := 1, powers := [(8, 1), (9, 1), (24, 1), (33, 1), (36, 1), (57, 1), (66, 1)] }, { coefficient := 1, powers := [(8, 1), (13, 1), (24, 1), (30, 1), (36, 1)] }, { coefficient := -1, powers := [(8, 1), (24, 1), (25, 1), (42, 1), (49, 1), (57, 1), (66, 1)] }, { coefficient := -1, powers := [(8, 1), (24, 1), (33, 1), (36, 1), (49, 1), (57, 1), (66, 1)] }]
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
    (values : Fin 69 → R) :
    ¬ ∀ index : Fin 31,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component60.SelectedLeafB6_6_3_4_2.selectedHasNoCommonZero

end Krenn.Component60.SelectedLeafB6_6_3_4_2
