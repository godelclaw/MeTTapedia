import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component36.SelectedLeafB6_4

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "4b9e2572fcebdab713745be025bcf134fed15f390940a1104d365ea9f1289c67"
def certificateSHA256 : String := "9bd6f56ad60a2ebbbc4e92ba655fcffcd11bd364fcbb9f77be8e8ce20cbb2cb7"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 38 → Fin 669 := ![
  0,
  1,
  2,
  3,
  10,
  12,
  13,
  15,
  16,
  19,
  24,
  130,
  153,
  160,
  164,
  272,
  276,
  302,
  303,
  305,
  307,
  313,
  318,
  375,
  448,
  451,
  549,
  562,
  596,
  607,
  608,
  612,
  661,
  662,
  664,
  665,
  667,
  668
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 38 → SparsePoly (Fin 65) := ![
  [{ coefficient := 1, powers := [(1, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (31, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (26, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (20, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (46, 1)] }, { coefficient := 1, powers := [(17, 1), (21, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (45, 1)] }, { coefficient := 1, powers := [(13, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (54, 1)] }, { coefficient := 1, powers := [(29, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(31, 1), (38, 1)] }, { coefficient := 1, powers := [(34, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (24, 1), (40, 1)] }, { coefficient := 1, powers := [(18, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (43, 1), (54, 1)] }, { coefficient := 1, powers := [(21, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (45, 1)] }, { coefficient := 1, powers := [(4, 1), (34, 1)] }, { coefficient := 1, powers := [(16, 1), (21, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (52, 1)] }, { coefficient := 1, powers := [(7, 1), (31, 1)] }, { coefficient := 1, powers := [(11, 1), (26, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (48, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1)] }, { coefficient := 1, powers := [(13, 1), (29, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (46, 1)] }, { coefficient := 1, powers := [(17, 1), (40, 1)] }, { coefficient := 1, powers := [(17, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (52, 1)] }, { coefficient := 1, powers := [(23, 1), (57, 1)] }, { coefficient := 1, powers := [(28, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (31, 1), (58, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1), (48, 1)] }, { coefficient := 1, powers := [(18, 1), (31, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (61, 1)] }, { coefficient := 1, powers := [(13, 1), (48, 1)] }, { coefficient := 1, powers := [(18, 1), (20, 1), (53, 1)] }, { coefficient := 1, powers := [(18, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (61, 1)] }, { coefficient := 1, powers := [(13, 1), (25, 1), (46, 1)] }, { coefficient := 1, powers := [(13, 1), (58, 1)] }, { coefficient := 1, powers := [(18, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (25, 1), (46, 1)] }, { coefficient := 1, powers := [(11, 1), (58, 1)] }, { coefficient := 1, powers := [(17, 1), (25, 1), (40, 1)] }, { coefficient := 1, powers := [(17, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (43, 1), (54, 1)] }, { coefficient := 1, powers := [(23, 1), (58, 1)] }, { coefficient := 1, powers := [(29, 1), (48, 1)] }, { coefficient := 1, powers := [(35, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (41, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (47, 1), (53, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (57, 1)] }, { coefficient := 1, powers := [(13, 1), (23, 1), (57, 1)] }, { coefficient := 1, powers := [(13, 1), (28, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (60, 1)] }, { coefficient := 1, powers := [(11, 1), (45, 1)] }, { coefficient := 1, powers := [(11, 1), (57, 1)] }, { coefficient := 1, powers := [(16, 1), (40, 1)] }, { coefficient := 1, powers := [(16, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (52, 1)] }, { coefficient := 1, powers := [(21, 1), (57, 1)] }, { coefficient := 1, powers := [(26, 1), (40, 1)] }, { coefficient := 1, powers := [(26, 1), (45, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (40, 1), (58, 1)] }, { coefficient := 1, powers := [(0, 1), (46, 1), (54, 1)] }, { coefficient := 1, powers := [(25, 1), (40, 1), (43, 1)] }, { coefficient := 1, powers := [(25, 1), (46, 1)] }, { coefficient := 1, powers := [(43, 1), (54, 1)] }, { coefficient := 1, powers := [(58, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (37, 1), (60, 1)] }, { coefficient := 1, powers := [(1, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(1, 1), (45, 1), (52, 1)] }, { coefficient := 1, powers := [(4, 1), (26, 1), (60, 1)] }, { coefficient := 1, powers := [(4, 1), (31, 1), (57, 1)] }, { coefficient := 1, powers := [(4, 1), (34, 1), (52, 1)] }, { coefficient := 1, powers := [(7, 1), (21, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (31, 1), (45, 1)] }, { coefficient := 1, powers := [(7, 1), (34, 1), (40, 1)] }, { coefficient := 1, powers := [(11, 1), (21, 1), (57, 1)] }, { coefficient := 1, powers := [(11, 1), (26, 1), (45, 1)] }, { coefficient := 1, powers := [(11, 1), (34, 1), (37, 1)] }, { coefficient := 1, powers := [(16, 1), (21, 1), (52, 1)] }, { coefficient := 1, powers := [(16, 1), (26, 1), (40, 1)] }, { coefficient := 1, powers := [(16, 1), (31, 1), (37, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (41, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (48, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (23, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (48, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(13, 1), (23, 1), (58, 1)] }, { coefficient := 1, powers := [(13, 1), (29, 1), (48, 1)] }, { coefficient := 1, powers := [(13, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (55, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (41, 1)] }, { coefficient := 1, powers := [(18, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(40, 1)] }],
  [{ coefficient := 1, powers := [(41, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 38 → SparsePoly (Fin 65) := ![
  [{ coefficient := 2, powers := [(1, 1), (13, 1), (29, 1), (37, 1), (43, 1), (60, 1), (63, 1)] }, { coefficient := 2, powers := [(4, 1), (13, 1), (29, 1), (31, 1), (43, 1), (57, 1), (63, 1)] }, { coefficient := 2, powers := [(7, 1), (13, 1), (21, 1), (29, 1), (43, 1), (60, 1), (63, 1)] }, { coefficient := -2, powers := [(7, 1), (13, 1), (26, 1), (29, 1), (43, 1), (60, 1), (63, 1)] }, { coefficient := 2, powers := [(7, 1), (13, 1), (29, 1), (31, 1), (43, 1), (45, 1), (63, 1)] }, { coefficient := -2, powers := [(11, 1), (13, 1), (21, 1), (29, 1), (43, 1), (52, 1), (63, 1)] }, { coefficient := -2, powers := [(11, 1), (13, 1), (26, 1), (28, 1), (58, 1), (63, 1)] }, { coefficient := -2, powers := [(11, 1), (13, 1), (26, 1), (29, 1), (43, 1), (45, 1), (63, 1)] }, { coefficient := -2, powers := [(11, 1), (13, 1), (26, 1), (29, 1), (43, 1), (57, 1), (63, 1)] }, { coefficient := -2, powers := [(11, 1), (13, 1), (29, 1), (31, 1), (37, 1), (43, 1), (63, 1)] }, { coefficient := 1, powers := [(13, 1), (16, 1), (21, 1), (28, 1), (58, 1), (63, 1)] }, { coefficient := -2, powers := [(13, 1), (16, 1), (26, 1), (29, 1), (43, 1), (52, 1), (63, 1)] }, { coefficient := 2, powers := [(13, 1), (16, 1), (29, 1), (31, 1), (37, 1), (43, 1), (63, 1)] }],
  [{ coefficient := -4, powers := [(1, 1), (13, 1), (29, 1), (37, 1), (60, 1), (63, 1)] }, { coefficient := -4, powers := [(4, 1), (13, 1), (29, 1), (31, 1), (57, 1), (63, 1)] }, { coefficient := -4, powers := [(7, 1), (13, 1), (21, 1), (29, 1), (60, 1), (63, 1)] }, { coefficient := 4, powers := [(7, 1), (13, 1), (26, 1), (29, 1), (60, 1), (63, 1)] }, { coefficient := -4, powers := [(7, 1), (13, 1), (29, 1), (31, 1), (45, 1), (63, 1)] }, { coefficient := 4, powers := [(11, 1), (13, 1), (21, 1), (29, 1), (52, 1), (63, 1)] }, { coefficient := 4, powers := [(11, 1), (13, 1), (26, 1), (29, 1), (45, 1), (63, 1)] }, { coefficient := 4, powers := [(11, 1), (13, 1), (26, 1), (29, 1), (57, 1), (63, 1)] }, { coefficient := 4, powers := [(11, 1), (13, 1), (29, 1), (31, 1), (37, 1), (63, 1)] }, { coefficient := 4, powers := [(13, 1), (16, 1), (26, 1), (29, 1), (52, 1), (63, 1)] }, { coefficient := -4, powers := [(13, 1), (16, 1), (29, 1), (31, 1), (37, 1), (63, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (1, 1), (5, 1), (32, 1), (46, 1), (52, 1), (57, 1), (63, 1)] }, { coefficient := 2, powers := [(1, 1), (5, 1), (32, 1), (43, 1), (52, 1), (57, 1), (63, 1)] }, { coefficient := -2, powers := [(5, 1), (17, 1), (21, 1), (32, 1), (57, 1), (63, 1)] }],
  [{ coefficient := 2, powers := [(11, 1), (18, 1), (21, 1), (23, 1), (52, 1), (63, 1)] }, { coefficient := 2, powers := [(11, 1), (18, 1), (23, 1), (26, 1), (45, 1), (63, 1)] }, { coefficient := 2, powers := [(11, 1), (18, 1), (23, 1), (26, 1), (57, 1), (63, 1)] }, { coefficient := 2, powers := [(16, 1), (18, 1), (23, 1), (26, 1), (52, 1), (63, 1)] }],
  [{ coefficient := 2, powers := [(1, 1), (32, 1), (37, 1), (58, 1)] }, { coefficient := -2, powers := [(4, 1), (21, 1), (32, 1), (58, 1)] }, { coefficient := 2, powers := [(4, 1), (26, 1), (32, 1), (58, 1)] }],
  [{ coefficient := 2, powers := [(4, 1), (23, 1), (57, 1), (61, 1)] }, { coefficient := -2, powers := [(4, 1), (32, 1), (48, 1), (57, 1)] }, { coefficient := 2, powers := [(7, 1), (23, 1), (45, 1), (61, 1)] }, { coefficient := -2, powers := [(7, 1), (32, 1), (45, 1), (48, 1)] }, { coefficient := 2, powers := [(7, 1), (32, 1), (48, 1), (57, 1)] }, { coefficient := -2, powers := [(11, 1), (23, 1), (37, 1), (61, 1)] }, { coefficient := 2, powers := [(11, 1), (32, 1), (37, 1), (48, 1)] }, { coefficient := 2, powers := [(16, 1), (23, 1), (37, 1), (61, 1)] }, { coefficient := -2, powers := [(16, 1), (32, 1), (37, 1), (48, 1)] }],
  [{ coefficient := 2, powers := [(1, 1), (23, 1), (37, 1), (61, 1)] }, { coefficient := 2, powers := [(7, 1), (21, 1), (23, 1), (61, 1)] }, { coefficient := -2, powers := [(7, 1), (23, 1), (26, 1), (61, 1)] }],
  [{ coefficient := 2, powers := [(11, 1), (21, 1), (23, 1), (46, 1), (52, 1)] }, { coefficient := 2, powers := [(11, 1), (23, 1), (26, 1), (45, 1), (46, 1)] }, { coefficient := 2, powers := [(11, 1), (23, 1), (26, 1), (46, 1), (57, 1)] }, { coefficient := 2, powers := [(16, 1), (23, 1), (26, 1), (46, 1), (52, 1)] }],
  [{ coefficient := -4, powers := [(11, 1), (23, 1), (52, 1), (58, 1)] }, { coefficient := -2, powers := [(11, 1), (23, 1), (57, 1), (58, 1)] }, { coefficient := 2, powers := [(16, 1), (23, 1), (52, 1), (58, 1)] }],
  [{ coefficient := -2, powers := [(1, 1), (29, 1), (37, 1), (53, 1), (60, 1)] }, { coefficient := -2, powers := [(4, 1), (29, 1), (31, 1), (53, 1), (57, 1)] }, { coefficient := -2, powers := [(7, 1), (21, 1), (29, 1), (53, 1), (60, 1)] }, { coefficient := 2, powers := [(7, 1), (26, 1), (29, 1), (53, 1), (60, 1)] }, { coefficient := -2, powers := [(7, 1), (29, 1), (31, 1), (45, 1), (53, 1)] }, { coefficient := 2, powers := [(11, 1), (21, 1), (29, 1), (52, 1), (53, 1)] }, { coefficient := 2, powers := [(11, 1), (26, 1), (29, 1), (45, 1), (53, 1)] }, { coefficient := 2, powers := [(11, 1), (26, 1), (29, 1), (53, 1), (57, 1)] }, { coefficient := 2, powers := [(11, 1), (29, 1), (31, 1), (37, 1), (53, 1)] }, { coefficient := 2, powers := [(16, 1), (26, 1), (29, 1), (52, 1), (53, 1)] }, { coefficient := -2, powers := [(16, 1), (29, 1), (31, 1), (37, 1), (53, 1)] }],
  [{ coefficient := 2, powers := [(5, 1), (11, 1), (32, 1), (43, 1), (45, 1)] }, { coefficient := 2, powers := [(5, 1), (11, 1), (32, 1), (43, 1), (52, 1)] }, { coefficient := 4, powers := [(5, 1), (11, 1), (32, 1), (43, 1), (57, 1)] }, { coefficient := 2, powers := [(5, 1), (16, 1), (32, 1), (43, 1), (52, 1)] }, { coefficient := 1, powers := [(5, 1), (16, 1), (32, 1), (43, 1), (57, 1)] }, { coefficient := -2, powers := [(11, 1), (13, 1), (23, 1), (43, 1), (45, 1)] }, { coefficient := -2, powers := [(11, 1), (13, 1), (23, 1), (43, 1), (52, 1)] }, { coefficient := -2, powers := [(11, 1), (13, 1), (23, 1), (43, 1), (57, 1)] }, { coefficient := -2, powers := [(13, 1), (16, 1), (23, 1), (43, 1), (52, 1)] }, { coefficient := -1, powers := [(13, 1), (16, 1), (23, 1), (43, 1), (57, 1)] }],
  [{ coefficient := 2, powers := [(5, 1), (25, 1), (32, 1), (52, 1), (57, 1)] }],
  [{ coefficient := -2, powers := [(11, 1), (21, 1), (23, 1), (58, 1)] }, { coefficient := 2, powers := [(11, 1), (23, 1), (26, 1), (58, 1)] }],
  [{ coefficient := -2, powers := [(1, 1), (13, 1), (37, 1), (43, 1), (60, 1)] }, { coefficient := -2, powers := [(4, 1), (13, 1), (31, 1), (43, 1), (57, 1)] }, { coefficient := -2, powers := [(7, 1), (13, 1), (21, 1), (43, 1), (60, 1)] }, { coefficient := 2, powers := [(7, 1), (13, 1), (26, 1), (43, 1), (60, 1)] }, { coefficient := -2, powers := [(7, 1), (13, 1), (31, 1), (43, 1), (45, 1)] }, { coefficient := 2, powers := [(11, 1), (13, 1), (21, 1), (43, 1), (52, 1)] }, { coefficient := 2, powers := [(11, 1), (13, 1), (26, 1), (43, 1), (45, 1)] }, { coefficient := 2, powers := [(11, 1), (13, 1), (26, 1), (43, 1), (57, 1)] }, { coefficient := 2, powers := [(11, 1), (13, 1), (31, 1), (37, 1), (43, 1)] }, { coefficient := 2, powers := [(13, 1), (16, 1), (26, 1), (43, 1), (52, 1)] }, { coefficient := -2, powers := [(13, 1), (16, 1), (31, 1), (37, 1), (43, 1)] }],
  [{ coefficient := -2, powers := [(4, 1), (18, 1), (32, 1), (57, 1)] }, { coefficient := -2, powers := [(7, 1), (18, 1), (32, 1), (45, 1)] }, { coefficient := 2, powers := [(7, 1), (18, 1), (32, 1), (57, 1)] }, { coefficient := 2, powers := [(11, 1), (18, 1), (32, 1), (37, 1)] }, { coefficient := -2, powers := [(16, 1), (18, 1), (32, 1), (37, 1)] }],
  [{ coefficient := 2, powers := [(1, 1), (32, 1), (37, 1), (38, 1), (60, 1)] }, { coefficient := 2, powers := [(4, 1), (31, 1), (32, 1), (38, 1), (57, 1)] }, { coefficient := 2, powers := [(4, 1), (32, 1), (34, 1), (38, 1), (57, 1)] }, { coefficient := 2, powers := [(7, 1), (21, 1), (32, 1), (38, 1), (60, 1)] }, { coefficient := -2, powers := [(7, 1), (26, 1), (32, 1), (38, 1), (60, 1)] }, { coefficient := 2, powers := [(7, 1), (31, 1), (32, 1), (38, 1), (45, 1)] }, { coefficient := 2, powers := [(7, 1), (32, 1), (34, 1), (38, 1), (45, 1)] }, { coefficient := -2, powers := [(7, 1), (32, 1), (34, 1), (38, 1), (57, 1)] }, { coefficient := -2, powers := [(11, 1), (21, 1), (32, 1), (38, 1), (52, 1)] }, { coefficient := -2, powers := [(11, 1), (26, 1), (32, 1), (38, 1), (45, 1)] }, { coefficient := -2, powers := [(11, 1), (26, 1), (32, 1), (38, 1), (57, 1)] }, { coefficient := -2, powers := [(11, 1), (31, 1), (32, 1), (37, 1), (38, 1)] }, { coefficient := -2, powers := [(11, 1), (32, 1), (34, 1), (37, 1), (38, 1)] }, { coefficient := -2, powers := [(16, 1), (26, 1), (32, 1), (38, 1), (52, 1)] }, { coefficient := 2, powers := [(16, 1), (31, 1), (32, 1), (37, 1), (38, 1)] }, { coefficient := 2, powers := [(16, 1), (32, 1), (34, 1), (37, 1), (38, 1)] }],
  [{ coefficient := -2, powers := [(5, 1), (11, 1), (32, 1), (45, 1)] }, { coefficient := -2, powers := [(5, 1), (11, 1), (32, 1), (52, 1)] }, { coefficient := -4, powers := [(5, 1), (11, 1), (32, 1), (57, 1)] }, { coefficient := -2, powers := [(5, 1), (16, 1), (32, 1), (52, 1)] }, { coefficient := -1, powers := [(5, 1), (16, 1), (32, 1), (57, 1)] }, { coefficient := 2, powers := [(11, 1), (13, 1), (23, 1), (45, 1)] }, { coefficient := 2, powers := [(11, 1), (13, 1), (23, 1), (52, 1)] }, { coefficient := 2, powers := [(11, 1), (13, 1), (23, 1), (57, 1)] }, { coefficient := 2, powers := [(13, 1), (16, 1), (23, 1), (52, 1)] }, { coefficient := 1, powers := [(13, 1), (16, 1), (23, 1), (57, 1)] }],
  [{ coefficient := 2, powers := [(52, 1)] }],
  [{ coefficient := 2, powers := [(5, 1), (32, 1), (57, 1), (58, 1)] }],
  [{ coefficient := 2, powers := [(1, 1), (37, 1), (55, 1), (60, 1)] }, { coefficient := 2, powers := [(4, 1), (31, 1), (55, 1), (57, 1)] }, { coefficient := 2, powers := [(7, 1), (21, 1), (55, 1), (60, 1)] }, { coefficient := -2, powers := [(7, 1), (26, 1), (55, 1), (60, 1)] }, { coefficient := 2, powers := [(7, 1), (31, 1), (45, 1), (55, 1)] }, { coefficient := -2, powers := [(11, 1), (21, 1), (52, 1), (55, 1)] }, { coefficient := -2, powers := [(11, 1), (26, 1), (45, 1), (55, 1)] }, { coefficient := -2, powers := [(11, 1), (26, 1), (55, 1), (57, 1)] }, { coefficient := -2, powers := [(11, 1), (31, 1), (37, 1), (55, 1)] }, { coefficient := -2, powers := [(16, 1), (26, 1), (52, 1), (55, 1)] }, { coefficient := 2, powers := [(16, 1), (31, 1), (37, 1), (55, 1)] }],
  [{ coefficient := 2, powers := [(1, 1), (37, 1), (48, 1), (60, 1)] }, { coefficient := 2, powers := [(4, 1), (31, 1), (48, 1), (57, 1)] }, { coefficient := 2, powers := [(7, 1), (21, 1), (48, 1), (60, 1)] }, { coefficient := -2, powers := [(7, 1), (26, 1), (48, 1), (60, 1)] }, { coefficient := 2, powers := [(7, 1), (31, 1), (45, 1), (48, 1)] }, { coefficient := -2, powers := [(11, 1), (21, 1), (48, 1), (52, 1)] }, { coefficient := -2, powers := [(11, 1), (26, 1), (45, 1), (48, 1)] }, { coefficient := -2, powers := [(11, 1), (26, 1), (48, 1), (57, 1)] }, { coefficient := -2, powers := [(11, 1), (31, 1), (37, 1), (48, 1)] }, { coefficient := -2, powers := [(16, 1), (26, 1), (48, 1), (52, 1)] }, { coefficient := 2, powers := [(16, 1), (31, 1), (37, 1), (48, 1)] }],
  [{ coefficient := -2, powers := [(5, 1), (21, 1), (25, 1), (32, 1), (57, 1)] }],
  [{ coefficient := 4, powers := [(11, 1), (13, 1), (26, 1), (58, 1)] }, { coefficient := -2, powers := [(13, 1), (16, 1), (21, 1), (58, 1)] }],
  [{ coefficient := 2, powers := [(4, 1), (32, 1), (57, 1)] }, { coefficient := 2, powers := [(7, 1), (32, 1), (45, 1)] }, { coefficient := -2, powers := [(7, 1), (32, 1), (57, 1)] }, { coefficient := -2, powers := [(11, 1), (32, 1), (37, 1)] }, { coefficient := 2, powers := [(16, 1), (32, 1), (37, 1)] }],
  [{ coefficient := 2, powers := [(1, 1), (29, 1), (37, 1), (60, 1)] }, { coefficient := 2, powers := [(4, 1), (29, 1), (31, 1), (57, 1)] }, { coefficient := 2, powers := [(7, 1), (21, 1), (29, 1), (60, 1)] }, { coefficient := -2, powers := [(7, 1), (26, 1), (29, 1), (60, 1)] }, { coefficient := 2, powers := [(7, 1), (29, 1), (31, 1), (45, 1)] }, { coefficient := -2, powers := [(11, 1), (21, 1), (29, 1), (52, 1)] }, { coefficient := -2, powers := [(11, 1), (26, 1), (29, 1), (45, 1)] }, { coefficient := -2, powers := [(11, 1), (26, 1), (29, 1), (57, 1)] }, { coefficient := -2, powers := [(11, 1), (29, 1), (31, 1), (37, 1)] }, { coefficient := -2, powers := [(16, 1), (26, 1), (29, 1), (52, 1)] }, { coefficient := 2, powers := [(16, 1), (29, 1), (31, 1), (37, 1)] }],
  [{ coefficient := -2, powers := [(11, 1), (21, 1), (23, 1), (52, 1)] }, { coefficient := -2, powers := [(11, 1), (23, 1), (26, 1), (45, 1)] }, { coefficient := -2, powers := [(11, 1), (23, 1), (26, 1), (57, 1)] }, { coefficient := -2, powers := [(16, 1), (23, 1), (26, 1), (52, 1)] }],
  [{ coefficient := 2, powers := [(5, 1), (21, 1), (32, 1), (57, 1)] }],
  [{ coefficient := 2, powers := [(1, 1), (13, 1), (37, 1), (60, 1)] }, { coefficient := 2, powers := [(4, 1), (13, 1), (31, 1), (57, 1)] }, { coefficient := 2, powers := [(7, 1), (13, 1), (21, 1), (60, 1)] }, { coefficient := -2, powers := [(7, 1), (13, 1), (26, 1), (60, 1)] }, { coefficient := 2, powers := [(7, 1), (13, 1), (31, 1), (45, 1)] }, { coefficient := -2, powers := [(11, 1), (13, 1), (21, 1), (52, 1)] }, { coefficient := -2, powers := [(11, 1), (13, 1), (26, 1), (45, 1)] }, { coefficient := -2, powers := [(11, 1), (13, 1), (26, 1), (57, 1)] }, { coefficient := -2, powers := [(11, 1), (13, 1), (31, 1), (37, 1)] }, { coefficient := -2, powers := [(13, 1), (16, 1), (26, 1), (52, 1)] }, { coefficient := 2, powers := [(13, 1), (16, 1), (31, 1), (37, 1)] }],
  [{ coefficient := -2, powers := [(11, 1), (26, 1), (58, 1)] }, { coefficient := 1, powers := [(16, 1), (21, 1), (58, 1)] }],
  [{ coefficient := 2, powers := [(5, 1), (21, 1), (32, 1), (58, 1)] }, { coefficient := -2, powers := [(5, 1), (26, 1), (32, 1), (58, 1)] }, { coefficient := 2, powers := [(26, 1)] }],
  [{ coefficient := 2, powers := [(11, 1)] }],
  [{ coefficient := -2, powers := [(1, 1), (5, 1), (32, 1), (52, 1), (57, 1)] }],
  [{ coefficient := -2, powers := [] }],
  [{ coefficient := -2, powers := [(1, 1), (37, 1), (60, 1)] }, { coefficient := -2, powers := [(4, 1), (31, 1), (57, 1)] }, { coefficient := -2, powers := [(7, 1), (21, 1), (60, 1)] }, { coefficient := 2, powers := [(7, 1), (26, 1), (60, 1)] }, { coefficient := -2, powers := [(7, 1), (31, 1), (45, 1)] }, { coefficient := 2, powers := [(11, 1), (21, 1), (52, 1)] }, { coefficient := 2, powers := [(11, 1), (26, 1), (45, 1)] }, { coefficient := 2, powers := [(11, 1), (26, 1), (57, 1)] }, { coefficient := 2, powers := [(11, 1), (31, 1), (37, 1)] }, { coefficient := 2, powers := [(16, 1), (26, 1), (52, 1)] }, { coefficient := -2, powers := [(16, 1), (31, 1), (37, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (1, 1), (5, 1), (32, 1), (46, 1), (52, 1), (54, 1), (57, 1)] }, { coefficient := -2, powers := [(1, 1), (5, 1), (32, 1), (43, 1), (52, 1), (54, 1), (57, 1)] }, { coefficient := -2, powers := [(1, 1), (13, 1), (29, 1), (37, 1), (43, 1), (47, 1), (60, 1)] }, { coefficient := 4, powers := [(1, 1), (13, 1), (29, 1), (37, 1), (48, 1), (60, 1)] }, { coefficient := -2, powers := [(4, 1), (13, 1), (29, 1), (31, 1), (43, 1), (47, 1), (57, 1)] }, { coefficient := 4, powers := [(4, 1), (13, 1), (29, 1), (31, 1), (48, 1), (57, 1)] }, { coefficient := 2, powers := [(5, 1), (17, 1), (21, 1), (32, 1), (54, 1), (57, 1)] }, { coefficient := -2, powers := [(7, 1), (13, 1), (21, 1), (29, 1), (43, 1), (47, 1), (60, 1)] }, { coefficient := 4, powers := [(7, 1), (13, 1), (21, 1), (29, 1), (48, 1), (60, 1)] }, { coefficient := 2, powers := [(7, 1), (13, 1), (26, 1), (29, 1), (43, 1), (47, 1), (60, 1)] }, { coefficient := -4, powers := [(7, 1), (13, 1), (26, 1), (29, 1), (48, 1), (60, 1)] }, { coefficient := -2, powers := [(7, 1), (13, 1), (29, 1), (31, 1), (43, 1), (45, 1), (47, 1)] }, { coefficient := 4, powers := [(7, 1), (13, 1), (29, 1), (31, 1), (45, 1), (48, 1)] }, { coefficient := 2, powers := [(11, 1), (13, 1), (21, 1), (29, 1), (43, 1), (47, 1), (52, 1)] }, { coefficient := -4, powers := [(11, 1), (13, 1), (21, 1), (29, 1), (48, 1), (52, 1)] }, { coefficient := 2, powers := [(11, 1), (13, 1), (26, 1), (28, 1), (47, 1), (58, 1)] }, { coefficient := 2, powers := [(11, 1), (13, 1), (26, 1), (29, 1), (43, 1), (45, 1), (47, 1)] }, { coefficient := 2, powers := [(11, 1), (13, 1), (26, 1), (29, 1), (43, 1), (47, 1), (57, 1)] }, { coefficient := -4, powers := [(11, 1), (13, 1), (26, 1), (29, 1), (45, 1), (48, 1)] }, { coefficient := -4, powers := [(11, 1), (13, 1), (26, 1), (29, 1), (48, 1), (57, 1)] }, { coefficient := 2, powers := [(11, 1), (13, 1), (29, 1), (31, 1), (37, 1), (43, 1), (47, 1)] }, { coefficient := -4, powers := [(11, 1), (13, 1), (29, 1), (31, 1), (37, 1), (48, 1)] }, { coefficient := -2, powers := [(11, 1), (18, 1), (21, 1), (23, 1), (52, 1), (55, 1)] }, { coefficient := -2, powers := [(11, 1), (18, 1), (23, 1), (26, 1), (45, 1), (55, 1)] }, { coefficient := -2, powers := [(11, 1), (18, 1), (23, 1), (26, 1), (55, 1), (57, 1)] }, { coefficient := -1, powers := [(13, 1), (16, 1), (21, 1), (28, 1), (47, 1), (58, 1)] }, { coefficient := 2, powers := [(13, 1), (16, 1), (26, 1), (29, 1), (43, 1), (47, 1), (52, 1)] }, { coefficient := -4, powers := [(13, 1), (16, 1), (26, 1), (29, 1), (48, 1), (52, 1)] }, { coefficient := -2, powers := [(13, 1), (16, 1), (29, 1), (31, 1), (37, 1), (43, 1), (47, 1)] }, { coefficient := 4, powers := [(13, 1), (16, 1), (29, 1), (31, 1), (37, 1), (48, 1)] }, { coefficient := -2, powers := [(16, 1), (18, 1), (23, 1), (26, 1), (52, 1), (55, 1)] }],
  [{ coefficient := 2, powers := [(1, 1), (37, 1), (38, 1), (60, 1), (61, 1)] }, { coefficient := 2, powers := [(1, 1), (37, 1), (41, 1), (58, 1), (60, 1)] }, { coefficient := -2, powers := [(1, 1), (37, 1), (48, 1), (55, 1), (60, 1)] }, { coefficient := 2, powers := [(4, 1), (31, 1), (38, 1), (57, 1), (61, 1)] }, { coefficient := 2, powers := [(4, 1), (31, 1), (41, 1), (57, 1), (58, 1)] }, { coefficient := -2, powers := [(4, 1), (31, 1), (48, 1), (55, 1), (57, 1)] }, { coefficient := 2, powers := [(7, 1), (21, 1), (38, 1), (60, 1), (61, 1)] }, { coefficient := 2, powers := [(7, 1), (21, 1), (41, 1), (58, 1), (60, 1)] }, { coefficient := -2, powers := [(7, 1), (21, 1), (48, 1), (55, 1), (60, 1)] }, { coefficient := -2, powers := [(7, 1), (26, 1), (38, 1), (60, 1), (61, 1)] }, { coefficient := -2, powers := [(7, 1), (26, 1), (41, 1), (58, 1), (60, 1)] }, { coefficient := 2, powers := [(7, 1), (26, 1), (48, 1), (55, 1), (60, 1)] }, { coefficient := 2, powers := [(7, 1), (31, 1), (38, 1), (45, 1), (61, 1)] }, { coefficient := 2, powers := [(7, 1), (31, 1), (41, 1), (45, 1), (58, 1)] }, { coefficient := -2, powers := [(7, 1), (31, 1), (45, 1), (48, 1), (55, 1)] }, { coefficient := -2, powers := [(11, 1), (21, 1), (38, 1), (52, 1), (61, 1)] }, { coefficient := -2, powers := [(11, 1), (21, 1), (41, 1), (52, 1), (58, 1)] }, { coefficient := 2, powers := [(11, 1), (21, 1), (48, 1), (52, 1), (55, 1)] }, { coefficient := -2, powers := [(11, 1), (26, 1), (38, 1), (45, 1), (61, 1)] }, { coefficient := -2, powers := [(11, 1), (26, 1), (38, 1), (57, 1), (61, 1)] }, { coefficient := -2, powers := [(11, 1), (26, 1), (41, 1), (45, 1), (58, 1)] }, { coefficient := 2, powers := [(11, 1), (26, 1), (45, 1), (48, 1), (55, 1)] }, { coefficient := 2, powers := [(11, 1), (26, 1), (47, 1), (53, 1), (58, 1)] }, { coefficient := 2, powers := [(11, 1), (26, 1), (48, 1), (55, 1), (57, 1)] }, { coefficient := -2, powers := [(11, 1), (31, 1), (37, 1), (38, 1), (61, 1)] }, { coefficient := -2, powers := [(11, 1), (31, 1), (37, 1), (41, 1), (58, 1)] }, { coefficient := 2, powers := [(11, 1), (31, 1), (37, 1), (48, 1), (55, 1)] }, { coefficient := -1, powers := [(16, 1), (21, 1), (41, 1), (57, 1), (58, 1)] }, { coefficient := -1, powers := [(16, 1), (21, 1), (47, 1), (53, 1), (58, 1)] }, { coefficient := -2, powers := [(16, 1), (26, 1), (38, 1), (52, 1), (61, 1)] }, { coefficient := -2, powers := [(16, 1), (26, 1), (41, 1), (52, 1), (58, 1)] }, { coefficient := 2, powers := [(16, 1), (26, 1), (48, 1), (52, 1), (55, 1)] }, { coefficient := 2, powers := [(16, 1), (31, 1), (37, 1), (38, 1), (61, 1)] }, { coefficient := 2, powers := [(16, 1), (31, 1), (37, 1), (41, 1), (58, 1)] }, { coefficient := -2, powers := [(16, 1), (31, 1), (37, 1), (48, 1), (55, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (1, 1), (5, 1), (32, 1), (52, 1), (57, 1), (58, 1)] }, { coefficient := 2, powers := [(1, 1), (5, 1), (25, 1), (32, 1), (43, 1), (52, 1), (57, 1)] }, { coefficient := -2, powers := [(1, 1), (18, 1), (24, 1), (32, 1), (37, 1), (38, 1), (60, 1)] }, { coefficient := 2, powers := [(1, 1), (57, 1)] }, { coefficient := -2, powers := [(4, 1), (18, 1), (24, 1), (31, 1), (32, 1), (38, 1), (57, 1)] }, { coefficient := -2, powers := [(4, 1), (18, 1), (24, 1), (32, 1), (34, 1), (38, 1), (57, 1)] }, { coefficient := -2, powers := [(5, 1), (16, 1), (21, 1), (32, 1), (58, 1)] }, { coefficient := 2, powers := [(5, 1), (16, 1), (26, 1), (32, 1), (58, 1)] }, { coefficient := -2, powers := [(7, 1), (18, 1), (21, 1), (24, 1), (32, 1), (38, 1), (60, 1)] }, { coefficient := 2, powers := [(7, 1), (18, 1), (24, 1), (26, 1), (32, 1), (38, 1), (60, 1)] }, { coefficient := -2, powers := [(7, 1), (18, 1), (24, 1), (31, 1), (32, 1), (38, 1), (45, 1)] }, { coefficient := -2, powers := [(7, 1), (18, 1), (24, 1), (32, 1), (34, 1), (38, 1), (45, 1)] }, { coefficient := 2, powers := [(7, 1), (18, 1), (24, 1), (32, 1), (34, 1), (38, 1), (57, 1)] }, { coefficient := 2, powers := [(7, 1), (34, 1)] }, { coefficient := 2, powers := [(11, 1), (18, 1), (21, 1), (24, 1), (32, 1), (38, 1), (52, 1)] }, { coefficient := 2, powers := [(11, 1), (18, 1), (24, 1), (26, 1), (32, 1), (38, 1), (45, 1)] }, { coefficient := 2, powers := [(11, 1), (18, 1), (24, 1), (26, 1), (32, 1), (38, 1), (57, 1)] }, { coefficient := 2, powers := [(11, 1), (18, 1), (24, 1), (31, 1), (32, 1), (37, 1), (38, 1)] }, { coefficient := 2, powers := [(11, 1), (18, 1), (24, 1), (32, 1), (34, 1), (37, 1), (38, 1)] }, { coefficient := -2, powers := [(11, 1), (26, 1)] }, { coefficient := 2, powers := [(16, 1), (18, 1), (24, 1), (26, 1), (32, 1), (38, 1), (52, 1)] }, { coefficient := -2, powers := [(16, 1), (18, 1), (24, 1), (31, 1), (32, 1), (37, 1), (38, 1)] }, { coefficient := -2, powers := [(16, 1), (18, 1), (24, 1), (32, 1), (34, 1), (37, 1), (38, 1)] }],
  [{ coefficient := 2, powers := [(1, 1), (8, 1), (35, 1), (37, 1), (60, 1)] }, { coefficient := 2, powers := [(4, 1), (8, 1), (31, 1), (35, 1), (57, 1)] }, { coefficient := 2, powers := [(7, 1), (8, 1), (21, 1), (35, 1), (60, 1)] }, { coefficient := -2, powers := [(7, 1), (8, 1), (26, 1), (35, 1), (60, 1)] }, { coefficient := 2, powers := [(7, 1), (8, 1), (31, 1), (35, 1), (45, 1)] }, { coefficient := -2, powers := [(8, 1), (11, 1), (21, 1), (35, 1), (52, 1)] }, { coefficient := -2, powers := [(8, 1), (11, 1), (26, 1), (35, 1), (45, 1)] }, { coefficient := -2, powers := [(8, 1), (11, 1), (26, 1), (35, 1), (57, 1)] }, { coefficient := -2, powers := [(8, 1), (11, 1), (31, 1), (35, 1), (37, 1)] }, { coefficient := -2, powers := [(8, 1), (16, 1), (26, 1), (35, 1), (52, 1)] }, { coefficient := 2, powers := [(8, 1), (16, 1), (31, 1), (35, 1), (37, 1)] }]
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
    ¬ ∀ index : Fin 38,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((2 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (2 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (2 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component36.SelectedLeafB6_4.selectedHasNoCommonZero

end Krenn.Component36.SelectedLeafB6_4
