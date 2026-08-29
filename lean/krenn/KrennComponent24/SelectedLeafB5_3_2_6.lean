import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component24.SelectedLeafB5_3_2_6

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "59f655964d71a6bc4bf173487305bfa1923f807e6498b4621cd6c084cb2179a0"
def certificateSHA256 : String := "a506e835139e99e65dc0ccee5722a217c7ff46817d44d9daa56690fbcca6ffcc"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 41 → Fin 676 := ![
  8,
  14,
  15,
  24,
  25,
  128,
  146,
  149,
  153,
  258,
  259,
  266,
  299,
  301,
  305,
  306,
  307,
  325,
  328,
  330,
  457,
  458,
  515,
  596,
  598,
  606,
  607,
  624,
  635,
  661,
  663,
  664,
  666,
  667,
  668,
  669,
  670,
  672,
  673,
  674,
  675
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 41 → SparsePoly (Fin 69) := ![
  [{ coefficient := 1, powers := [(13, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(32, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(35, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (55, 1)] }, { coefficient := 1, powers := [(20, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (26, 1)] }, { coefficient := 1, powers := [(18, 1), (20, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(15, 1), (21, 1)] }, { coefficient := 1, powers := [(21, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (20, 1)] }, { coefficient := 1, powers := [(18, 1), (26, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (26, 1), (45, 1)] }, { coefficient := 1, powers := [(19, 1), (20, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (26, 1), (46, 1)] }, { coefficient := 1, powers := [(18, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(15, 1), (21, 1), (54, 1)] }, { coefficient := 1, powers := [(15, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1)] }, { coefficient := 1, powers := [(20, 1), (45, 1)] }, { coefficient := 1, powers := [(26, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (51, 1)] }, { coefficient := 1, powers := [(20, 1), (51, 1)] }, { coefficient := 1, powers := [(26, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (44, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (56, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (59, 1)] }, { coefficient := 1, powers := [(9, 1), (56, 1)] }, { coefficient := 1, powers := [(15, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (61, 1)] }, { coefficient := 1, powers := [(14, 1), (58, 1)] }, { coefficient := 1, powers := [(19, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (40, 1), (59, 1)] }, { coefficient := 1, powers := [(9, 1), (35, 1), (40, 1)] }, { coefficient := 1, powers := [(15, 1), (32, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1), (53, 1)] }, { coefficient := 1, powers := [(20, 1), (45, 1), (53, 1)] }, { coefficient := 1, powers := [(45, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1), (51, 1)] }, { coefficient := 1, powers := [(26, 1), (46, 1), (51, 1)] }, { coefficient := 1, powers := [(51, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1)] }, { coefficient := 1, powers := [(14, 1), (31, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (37, 1)] }, { coefficient := 1, powers := [(24, 1), (45, 1)] }, { coefficient := 1, powers := [(29, 1), (45, 1)] }, { coefficient := 1, powers := [(37, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (28, 1), (59, 1)] }, { coefficient := 1, powers := [(9, 1), (28, 1), (44, 1)] }, { coefficient := 1, powers := [(15, 1), (22, 1), (52, 1)] }, { coefficient := 1, powers := [(15, 1), (28, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (41, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (44, 1), (50, 1)] }, { coefficient := 1, powers := [(13, 1), (24, 1), (56, 1)] }, { coefficient := 1, powers := [(13, 1), (29, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (42, 1), (58, 1)] }, { coefficient := 1, powers := [(8, 1), (37, 1), (42, 1)] }, { coefficient := 1, powers := [(18, 1), (30, 1), (58, 1)] }, { coefficient := 1, powers := [(18, 1), (31, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (31, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1)] }, { coefficient := 1, powers := [(3, 1), (35, 1)] }, { coefficient := 1, powers := [(15, 1), (20, 1)] }, { coefficient := 1, powers := [(20, 1), (56, 1)] }, { coefficient := 1, powers := [(26, 1), (44, 1)] }, { coefficient := 1, powers := [(35, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (50, 1)] }, { coefficient := 1, powers := [(6, 1), (32, 1)] }, { coefficient := 1, powers := [(9, 1), (26, 1)] }, { coefficient := 1, powers := [(20, 1), (50, 1)] }, { coefficient := 1, powers := [(26, 1), (41, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (45, 1), (51, 1)] }, { coefficient := 1, powers := [(14, 1), (29, 1), (45, 1)] }, { coefficient := 1, powers := [(14, 1), (37, 1), (38, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (51, 1)] }, { coefficient := 1, powers := [(19, 1), (34, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (31, 1), (61, 1)] }, { coefficient := 1, powers := [(3, 1), (34, 1), (58, 1)] }, { coefficient := 1, powers := [(3, 1), (37, 1), (55, 1)] }, { coefficient := 1, powers := [(24, 1), (45, 1), (55, 1)] }, { coefficient := 1, powers := [(24, 1), (51, 1), (58, 1)] }, { coefficient := 1, powers := [(31, 1), (45, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (38, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (41, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (44, 1), (50, 1)] }, { coefficient := 1, powers := [(3, 1), (26, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (32, 1), (56, 1)] }, { coefficient := 1, powers := [(3, 1), (35, 1), (50, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (32, 1), (44, 1)] }, { coefficient := 1, powers := [(6, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(9, 1), (20, 1), (56, 1)] }, { coefficient := 1, powers := [(9, 1), (26, 1), (44, 1)] }, { coefficient := 1, powers := [(9, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(15, 1), (20, 1), (50, 1)] }, { coefficient := 1, powers := [(15, 1), (26, 1), (41, 1)] }, { coefficient := 1, powers := [(15, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (40, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (43, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (49, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (37, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (25, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (49, 1)] }, { coefficient := 1, powers := [(8, 1), (37, 1), (43, 1)] }, { coefficient := 1, powers := [(14, 1), (25, 1), (58, 1)] }, { coefficient := 1, powers := [(14, 1), (31, 1), (49, 1)] }, { coefficient := 1, powers := [(14, 1), (37, 1), (40, 1)] }, { coefficient := 1, powers := [(19, 1), (25, 1), (55, 1)] }, { coefficient := 1, powers := [(19, 1), (31, 1), (43, 1)] }, { coefficient := 1, powers := [(19, 1), (34, 1), (40, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(41, 1)] }],
  [{ coefficient := 1, powers := [(42, 1), (64, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(43, 1), (65, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(56, 1)] }],
  [{ coefficient := 1, powers := [(58, 1)] }],
  [{ coefficient := 1, powers := [(26, 1), (67, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(28, 1), (68, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(31, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 41 → SparsePoly (Fin 69) := ![
  [{ coefficient := -1, powers := [(0, 1), (29, 1), (63, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (29, 1), (50, 1), (63, 1)] }, { coefficient := -1, powers := [(2, 1), (9, 1), (20, 1), (29, 1), (35, 1), (40, 1), (45, 1), (50, 1), (51, 1), (63, 1)] }, { coefficient := 1, powers := [(2, 1), (20, 1), (29, 1), (35, 1), (40, 1), (45, 1), (50, 2), (51, 1), (63, 1)] }, { coefficient := 1, powers := [(9, 1), (26, 1), (29, 1), (63, 1)] }, { coefficient := 1, powers := [(20, 1), (29, 1), (50, 1), (63, 1)] }, { coefficient := 1, powers := [(26, 1), (29, 1), (50, 1), (63, 1)] }, { coefficient := 1, powers := [(29, 1), (32, 1), (38, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(9, 1), (24, 1), (35, 1), (38, 1), (49, 1)] }, { coefficient := 1, powers := [(24, 1), (35, 1), (38, 1), (49, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (3, 1), (9, 1), (15, 1), (26, 1), (35, 1), (45, 1), (51, 1), (62, 1)] }, { coefficient := -1, powers := [(2, 1), (3, 1), (15, 1), (26, 1), (35, 1), (45, 1), (50, 1), (51, 1), (62, 1)] }, { coefficient := 1, powers := [(2, 1), (9, 1), (35, 1), (38, 1), (44, 1), (45, 1), (51, 1)] }, { coefficient := -1, powers := [(2, 1), (35, 1), (38, 1), (44, 1), (45, 1), (50, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (3, 1), (9, 2), (26, 1), (35, 1), (45, 1), (51, 1), (62, 1)] }, { coefficient := -1, powers := [(2, 1), (3, 1), (9, 1), (26, 1), (35, 1), (45, 1), (50, 1), (51, 1), (62, 1)] }, { coefficient := -1, powers := [(2, 1), (3, 1), (9, 1), (35, 1), (45, 1), (50, 1), (51, 1)] }, { coefficient := 1, powers := [(2, 1), (3, 1), (35, 1), (45, 1), (50, 2), (51, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (9, 1), (29, 1), (35, 1), (45, 1), (53, 1)] }, { coefficient := -1, powers := [(5, 1), (29, 1), (35, 1), (45, 1), (50, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(9, 1), (29, 1), (35, 1), (40, 1), (45, 1), (67, 1)] }, { coefficient := 1, powers := [(29, 1), (35, 1), (40, 1), (45, 1), (50, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (50, 1), (54, 1), (65, 1)] }, { coefficient := 1, powers := [(22, 1), (26, 1), (52, 1), (54, 1), (65, 1), (68, 1)] }, { coefficient := -1, powers := [(32, 1), (38, 1), (54, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (24, 1), (35, 1), (40, 1), (45, 1), (51, 1), (62, 1)] }, { coefficient := 1, powers := [(9, 1), (29, 1), (35, 1), (40, 1), (45, 1), (51, 1), (62, 1)] }, { coefficient := 1, powers := [(9, 1), (29, 1), (35, 1), (40, 1), (45, 1), (51, 1), (67, 1)] }, { coefficient := -1, powers := [(24, 1), (35, 1), (40, 1), (45, 1), (50, 1), (51, 1), (62, 1)] }, { coefficient := -1, powers := [(29, 1), (35, 1), (40, 1), (45, 1), (50, 1), (51, 1), (62, 1)] }, { coefficient := -1, powers := [(29, 1), (35, 1), (40, 1), (45, 1), (50, 1), (51, 1), (67, 1)] }],
  [{ coefficient := -1, powers := [(9, 1), (24, 1), (35, 1), (40, 1), (46, 1)] }, { coefficient := 1, powers := [(24, 1), (35, 1), (40, 1), (46, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (24, 1), (35, 1), (40, 1), (45, 1)] }, { coefficient := -1, powers := [(24, 1), (35, 1), (40, 1), (45, 1), (50, 1)] }],
  [{ coefficient := -1, powers := [(20, 1), (50, 1), (65, 1)] }, { coefficient := -1, powers := [(22, 1), (26, 1), (52, 1), (65, 1), (68, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(9, 1), (18, 1), (24, 1), (35, 1), (40, 1), (51, 1), (62, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (35, 1), (40, 1), (50, 1), (51, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(9, 1), (18, 1), (29, 1), (35, 1), (40, 1), (45, 1), (62, 1)] }, { coefficient := 1, powers := [(9, 1), (19, 1), (24, 1), (35, 1), (40, 1), (46, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (35, 1), (40, 1), (45, 1), (50, 1), (62, 1)] }, { coefficient := -1, powers := [(19, 1), (24, 1), (35, 1), (40, 1), (46, 1), (50, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (50, 1), (63, 1)] }, { coefficient := 1, powers := [(2, 1), (9, 1), (20, 1), (35, 1), (40, 1), (45, 1), (50, 1), (51, 1), (63, 1)] }, { coefficient := -1, powers := [(2, 1), (20, 1), (35, 1), (40, 1), (45, 1), (50, 2), (51, 1), (63, 1)] }, { coefficient := -1, powers := [(9, 1), (26, 1), (63, 1)] }, { coefficient := -1, powers := [(20, 1), (50, 1), (63, 1)] }, { coefficient := -1, powers := [(26, 1), (50, 1), (63, 1)] }, { coefficient := -1, powers := [(32, 1), (38, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (9, 1), (20, 1), (35, 1), (40, 1), (45, 1), (51, 1)] }, { coefficient := 1, powers := [(2, 1), (20, 1), (35, 1), (40, 1), (45, 1), (50, 1), (51, 1)] }, { coefficient := 1, powers := [(20, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (25, 1), (35, 1), (38, 1)] }, { coefficient := -1, powers := [(25, 1), (35, 1), (38, 1), (50, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (3, 1), (9, 1), (26, 1), (35, 1), (45, 1), (51, 1), (62, 1)] }, { coefficient := 1, powers := [(2, 1), (3, 1), (26, 1), (35, 1), (45, 1), (50, 1), (51, 1), (62, 1)] }, { coefficient := -1, powers := [(2, 1), (9, 1), (35, 1), (38, 1), (45, 1), (51, 1)] }, { coefficient := 1, powers := [(2, 1), (35, 1), (38, 1), (45, 1), (50, 1), (51, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (9, 1), (29, 1), (35, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (35, 1), (50, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(9, 1), (19, 1), (24, 1), (35, 1), (40, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (35, 1), (40, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (35, 1), (38, 1), (49, 1)] }, { coefficient := -1, powers := [(35, 1), (38, 1), (49, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (9, 1), (35, 1), (55, 1)] }, { coefficient := -1, powers := [(5, 1), (35, 1), (50, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(26, 1), (68, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (35, 1), (38, 1), (43, 1), (64, 1)] }, { coefficient := -1, powers := [(35, 1), (38, 1), (43, 1), (50, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(50, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (9, 1), (35, 1), (40, 1), (44, 1), (45, 1), (51, 1)] }, { coefficient := 1, powers := [(2, 1), (35, 1), (40, 1), (44, 1), (45, 1), (50, 1), (51, 1)] }, { coefficient := 1, powers := [(44, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (35, 1), (40, 1)] }, { coefficient := -1, powers := [(35, 1), (40, 1), (50, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (9, 1), (35, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (9, 1), (35, 1), (40, 1), (45, 1), (51, 1)] }, { coefficient := -1, powers := [(2, 1), (35, 1), (40, 1), (45, 1), (50, 1), (51, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(9, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(35, 1), (38, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (3, 1), (9, 1), (26, 1), (35, 1), (40, 1), (45, 1), (51, 1), (59, 1)] }, { coefficient := -1, powers := [(2, 1), (3, 1), (26, 1), (35, 1), (40, 1), (45, 1), (50, 1), (51, 1), (59, 1)] }, { coefficient := 1, powers := [(9, 1), (18, 1), (24, 1), (35, 1), (40, 1), (45, 1), (51, 1)] }, { coefficient := 1, powers := [(9, 1), (18, 1), (29, 1), (35, 1), (40, 1), (45, 1), (51, 1)] }, { coefficient := -1, powers := [(18, 1), (24, 1), (35, 1), (40, 1), (45, 1), (50, 1), (51, 1)] }, { coefficient := -1, powers := [(18, 1), (29, 1), (35, 1), (40, 1), (45, 1), (50, 1), (51, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (38, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (44, 1), (50, 1)] }, { coefficient := -1, powers := [(2, 1), (9, 1), (20, 1), (35, 1), (40, 1), (44, 1), (45, 1), (50, 1), (51, 1)] }, { coefficient := 1, powers := [(2, 1), (20, 1), (35, 1), (40, 1), (44, 1), (45, 1), (50, 2), (51, 1)] }, { coefficient := 1, powers := [(9, 1), (26, 1), (44, 1)] }, { coefficient := 1, powers := [(20, 1), (44, 1), (50, 1)] }, { coefficient := 1, powers := [(26, 1), (44, 1), (50, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1), (44, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (6, 1), (9, 1), (35, 2), (40, 1), (45, 1), (51, 1)] }, { coefficient := 1, powers := [(2, 1), (6, 1), (35, 2), (40, 1), (45, 1), (50, 1), (51, 1)] }, { coefficient := -1, powers := [(2, 1), (9, 1), (15, 1), (26, 1), (35, 1), (40, 1), (45, 1), (51, 1)] }, { coefficient := 1, powers := [(2, 1), (9, 1), (26, 1), (35, 1), (40, 1), (44, 1), (45, 1), (51, 1)] }, { coefficient := 1, powers := [(2, 1), (15, 1), (26, 1), (35, 1), (40, 1), (45, 1), (50, 1), (51, 1)] }, { coefficient := -1, powers := [(2, 1), (26, 1), (35, 1), (40, 1), (44, 1), (45, 1), (50, 1), (51, 1)] }, { coefficient := 1, powers := [(6, 1), (35, 1)] }, { coefficient := -1, powers := [(15, 1), (26, 1), (28, 1), (68, 1)] }, { coefficient := 1, powers := [(15, 1), (26, 1)] }, { coefficient := -1, powers := [(26, 1), (44, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (9, 1), (35, 1), (37, 1), (38, 1), (43, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (37, 1), (38, 1), (43, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(15, 1), (20, 1), (50, 1)] }, { coefficient := 1, powers := [(15, 1), (22, 1), (26, 1), (52, 1), (68, 1)] }, { coefficient := -1, powers := [(15, 1), (32, 1), (38, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (2, 1), (9, 1), (35, 1), (40, 1), (41, 1), (45, 1), (51, 1)] }, { coefficient := 1, powers := [(0, 1), (2, 1), (35, 1), (40, 1), (41, 1), (45, 1), (50, 1), (51, 1)] }, { coefficient := -1, powers := [(0, 1), (2, 1), (41, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (13, 1), (24, 1), (63, 1)] }, { coefficient := 2, powers := [(0, 1), (18, 1), (24, 1), (50, 1), (63, 1)] }, { coefficient := 1, powers := [(0, 1), (41, 1)] }, { coefficient := -1, powers := [(2, 1), (3, 1), (9, 1), (32, 1), (35, 1), (40, 1), (45, 1), (51, 1)] }, { coefficient := 1, powers := [(2, 1), (3, 1), (32, 1), (35, 1), (40, 1), (45, 1), (50, 1), (51, 1)] }, { coefficient := -1, powers := [(2, 1), (9, 1), (18, 1), (20, 1), (24, 1), (35, 1), (40, 1), (45, 1), (50, 1), (51, 1), (63, 1)] }, { coefficient := 1, powers := [(2, 1), (18, 1), (20, 1), (24, 1), (35, 1), (40, 1), (45, 1), (50, 2), (51, 1), (63, 1)] }, { coefficient := 1, powers := [(3, 1), (32, 1)] }, { coefficient := 1, powers := [(9, 1), (18, 1), (24, 1), (26, 1), (63, 1)] }, { coefficient := 1, powers := [(18, 1), (20, 1), (24, 1), (50, 1), (63, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (26, 1), (50, 1), (63, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (32, 1), (38, 1), (63, 1)] }, { coefficient := -1, powers := [(20, 1), (21, 1), (50, 1), (54, 1), (65, 1)] }, { coefficient := -1, powers := [(20, 1), (50, 1)] }, { coefficient := -1, powers := [(21, 1), (22, 1), (26, 1), (52, 1), (54, 1), (65, 1), (68, 1)] }, { coefficient := 1, powers := [(21, 1), (32, 1), (38, 1), (54, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (9, 1), (35, 1), (38, 1), (42, 1), (43, 1), (64, 1)] }, { coefficient := 1, powers := [(2, 1), (9, 1), (35, 1), (38, 1), (43, 1)] }, { coefficient := 1, powers := [(2, 1), (35, 1), (38, 1), (42, 1), (43, 1), (50, 1), (64, 1)] }, { coefficient := -1, powers := [(2, 1), (35, 1), (38, 1), (43, 1), (50, 1)] }, { coefficient := 1, powers := [(3, 1), (5, 1), (9, 1), (34, 1), (35, 1)] }, { coefficient := -1, powers := [(3, 1), (5, 1), (34, 1), (35, 1), (50, 1)] }, { coefficient := 1, powers := [(5, 1), (9, 1), (24, 1), (35, 1), (51, 1)] }, { coefficient := 1, powers := [(5, 1), (9, 1), (34, 1), (35, 1), (38, 1)] }, { coefficient := -1, powers := [(5, 1), (24, 1), (35, 1), (50, 1), (51, 1)] }, { coefficient := -1, powers := [(5, 1), (34, 1), (35, 1), (38, 1), (50, 1)] }, { coefficient := -1, powers := [(9, 1), (18, 1), (30, 1), (35, 1), (38, 1), (43, 1), (64, 1)] }, { coefficient := 1, powers := [(18, 1), (30, 1), (35, 1), (38, 1), (43, 1), (50, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (14, 1), (29, 1), (35, 1), (40, 1), (45, 1)] }, { coefficient := -1, powers := [(9, 1), (18, 1), (29, 1), (35, 1), (40, 1), (45, 1), (51, 1)] }, { coefficient := -1, powers := [(14, 1), (29, 1), (35, 1), (40, 1), (45, 1), (50, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (35, 1), (40, 1), (45, 1), (50, 1), (51, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (26, 1), (59, 1)] }, { coefficient := -1, powers := [(9, 1), (26, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (5, 1), (9, 1), (35, 1), (61, 1)] }, { coefficient := -1, powers := [(3, 1), (5, 1), (35, 1), (50, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (9, 1), (35, 1), (38, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (9, 1), (35, 1), (45, 1), (51, 1)] }, { coefficient := -1, powers := [(5, 1), (35, 1), (38, 1), (50, 1), (61, 1)] }, { coefficient := -1, powers := [(5, 1), (35, 1), (45, 1), (50, 1), (51, 1)] }, { coefficient := -1, powers := [(9, 1), (18, 1), (35, 1), (38, 1), (43, 1), (47, 1), (64, 1)] }, { coefficient := -1, powers := [(9, 1), (19, 1), (35, 1), (38, 1), (42, 1), (43, 1), (64, 1)] }, { coefficient := 1, powers := [(9, 1), (19, 1), (35, 1), (38, 1), (43, 1)] }, { coefficient := 1, powers := [(18, 1), (35, 1), (38, 1), (43, 1), (47, 1), (50, 1), (64, 1)] }, { coefficient := 1, powers := [(19, 1), (35, 1), (38, 1), (42, 1), (43, 1), (50, 1), (64, 1)] }, { coefficient := -1, powers := [(19, 1), (35, 1), (38, 1), (43, 1), (50, 1)] }]
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
    ¬ ∀ index : Fin 41,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component24.SelectedLeafB5_3_2_6.selectedHasNoCommonZero

end Krenn.Component24.SelectedLeafB5_3_2_6
