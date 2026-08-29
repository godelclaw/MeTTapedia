import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component18.SelectedLeafB6_2_1_4

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "f75a5776ffa36ec8085bfe130971e72fa47dcf7c14d824fcf8b765afd7222b43"
def certificateSHA256 : String := "b33fefd7817088e41aa0105a123b50ef6e5ab84112f21e351845918e4ee401bf"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 49 → Fin 670 := ![
  4,
  7,
  10,
  15,
  19,
  143,
  154,
  155,
  168,
  296,
  302,
  309,
  318,
  323,
  405,
  414,
  426,
  437,
  441,
  443,
  451,
  458,
  462,
  465,
  490,
  496,
  552,
  562,
  565,
  566,
  581,
  586,
  587,
  602,
  635,
  646,
  647,
  655,
  657,
  659,
  660,
  661,
  663,
  664,
  665,
  666,
  667,
  668,
  669
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 49 → SparsePoly (Fin 66) := ![
  [{ coefficient := 1, powers := [(11, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(15, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (54, 1)] }, { coefficient := 1, powers := [(15, 1), (21, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (49, 1)] }, { coefficient := 1, powers := [(18, 1), (20, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (53, 1)] }, { coefficient := -1, powers := [(17, 1), (26, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (53, 1)] }, { coefficient := 1, powers := [(31, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (44, 1)] }, { coefficient := 1, powers := [(11, 1), (21, 1), (55, 1)] }, { coefficient := 1, powers := [(11, 1), (27, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (58, 1)] }, { coefficient := 1, powers := [(9, 1), (55, 1)] }, { coefficient := 1, powers := [(14, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (45, 1)] }, { coefficient := 1, powers := [(18, 1), (19, 1), (51, 1)] }, { coefficient := 1, powers := [(18, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (54, 1)] }, { coefficient := 1, powers := [(31, 1), (43, 1)] }, { coefficient := 1, powers := [(34, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1), (52, 1)] }, { coefficient := 1, powers := [(19, 1), (45, 1), (52, 1)] }, { coefficient := 1, powers := [(45, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (19, 1), (57, 1)] }, { coefficient := 1, powers := [(17, 1), (26, 1), (45, 1)] }, { coefficient := 1, powers := [(18, 1), (19, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (26, 1), (46, 1), (51, 1)] }, { coefficient := 1, powers := [(9, 1), (26, 1), (46, 1)] }, { coefficient := 1, powers := [(26, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (53, 1)] }, { coefficient := 1, powers := [(3, 1), (26, 1), (59, 1)] }, { coefficient := 1, powers := [(19, 1), (53, 1)] }, { coefficient := 1, powers := [(26, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1)] }, { coefficient := 1, powers := [(13, 1), (31, 1)] }, { coefficient := 1, powers := [(17, 1), (23, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (32, 1)] }, { coefficient := 1, powers := [(12, 1), (26, 1)] }, { coefficient := 1, powers := [(17, 1), (19, 1), (26, 1), (51, 1)] }, { coefficient := 1, powers := [(17, 1), (26, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (60, 1)] }, { coefficient := 1, powers := [(13, 1), (26, 1), (47, 1)] }, { coefficient := 1, powers := [(13, 1), (57, 1)] }, { coefficient := 1, powers := [(18, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (26, 1), (51, 1)] }, { coefficient := 1, powers := [(9, 1), (26, 1)] }, { coefficient := 1, powers := [(19, 1), (26, 1), (51, 1)] }, { coefficient := 1, powers := [(26, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1), (53, 1)] }, { coefficient := 1, powers := [(19, 1), (45, 1), (53, 1)] }, { coefficient := 1, powers := [(19, 1), (57, 1)] }, { coefficient := 1, powers := [(26, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1), (51, 1)] }, { coefficient := 1, powers := [(9, 1), (47, 1)] }, { coefficient := 1, powers := [(32, 1), (39, 1), (45, 1)] }, { coefficient := 1, powers := [(45, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (48, 1), (51, 1)] }, { coefficient := 1, powers := [(9, 1), (20, 1), (56, 1)] }, { coefficient := 1, powers := [(9, 1), (48, 1)] }, { coefficient := 1, powers := [(20, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (28, 1), (58, 1)] }, { coefficient := 1, powers := [(9, 1), (28, 1), (44, 1)] }, { coefficient := 1, powers := [(14, 1), (21, 1), (51, 1)] }, { coefficient := 1, powers := [(14, 1), (28, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (31, 1), (60, 1)] }, { coefficient := 1, powers := [(3, 1), (34, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (37, 1), (54, 1)] }, { coefficient := 1, powers := [(23, 1), (45, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (19, 1), (56, 1)] }, { coefficient := 1, powers := [(12, 1)] }, { coefficient := 1, powers := [(17, 1), (19, 1), (51, 1)] }, { coefficient := 1, powers := [(17, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (45, 1), (53, 1)] }, { coefficient := 1, powers := [(24, 1), (57, 1)] }, { coefficient := 1, powers := [(31, 1), (49, 1)] }, { coefficient := 1, powers := [(37, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (26, 1), (47, 1), (51, 1)] }, { coefficient := 1, powers := [(9, 1), (26, 1), (47, 1)] }, { coefficient := 1, powers := [(9, 1), (57, 1)] }, { coefficient := 1, powers := [(26, 1), (45, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (26, 1), (48, 1), (51, 1)] }, { coefficient := 1, powers := [(9, 1), (26, 1), (48, 1)] }, { coefficient := 1, powers := [(20, 1), (26, 1), (51, 1)] }, { coefficient := 1, powers := [(32, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (52, 1)] }, { coefficient := 1, powers := [(3, 1), (59, 1)] }, { coefficient := 1, powers := [(19, 1), (52, 1)] }, { coefficient := 1, powers := [(19, 1), (56, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1), (51, 1)] }, { coefficient := 1, powers := [(9, 1), (46, 1)] }, { coefficient := 1, powers := [(9, 1), (56, 1)] }, { coefficient := 1, powers := [(32, 1), (39, 1)] }, { coefficient := 1, powers := [(51, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (38, 1), (58, 1)] }, { coefficient := 1, powers := [(1, 1), (41, 1), (55, 1)] }, { coefficient := 1, powers := [(1, 1), (44, 1), (50, 1)] }, { coefficient := 1, powers := [(10, 1), (21, 1), (55, 1)] }, { coefficient := 1, powers := [(10, 1), (27, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1)] }, { coefficient := 1, powers := [(3, 1), (35, 1)] }, { coefficient := 1, powers := [(14, 1), (19, 1)] }, { coefficient := 1, powers := [(19, 1), (55, 1)] }, { coefficient := 1, powers := [(25, 1), (44, 1)] }, { coefficient := 1, powers := [(35, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (32, 1), (57, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (49, 1)] }, { coefficient := 1, powers := [(12, 1), (20, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1), (26, 1), (49, 1)] }, { coefficient := 1, powers := [(18, 1), (20, 1), (26, 1), (51, 1)] }, { coefficient := 1, powers := [(18, 1), (32, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (41, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (51, 1)] }, { coefficient := 1, powers := [(3, 1), (32, 1), (56, 1)] }, { coefficient := 1, powers := [(9, 1), (19, 1), (56, 1)] }, { coefficient := 1, powers := [(9, 1)] }, { coefficient := 1, powers := [(19, 1), (51, 1)] }, { coefficient := 1, powers := [(41, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (41, 1), (56, 1)] }, { coefficient := 1, powers := [(1, 1), (51, 1)] }, { coefficient := 1, powers := [(7, 1), (36, 1), (41, 1)] }, { coefficient := 1, powers := [(10, 1), (21, 1), (56, 1)] }, { coefficient := 1, powers := [(10, 1), (28, 1)] }, { coefficient := 1, powers := [(15, 1), (21, 1), (51, 1)] }, { coefficient := 1, powers := [(15, 1), (28, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (38, 1), (58, 1)] }, { coefficient := 1, powers := [(0, 1), (41, 1), (55, 1)] }, { coefficient := 1, powers := [(0, 1), (44, 1), (50, 1)] }, { coefficient := 1, powers := [(3, 1), (25, 1), (58, 1)] }, { coefficient := 1, powers := [(3, 1), (32, 1), (55, 1)] }, { coefficient := 1, powers := [(3, 1), (35, 1), (50, 1)] }, { coefficient := 1, powers := [(6, 1), (19, 1), (58, 1)] }, { coefficient := 1, powers := [(6, 1), (32, 1), (44, 1)] }, { coefficient := 1, powers := [(6, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(9, 1), (19, 1), (55, 1)] }, { coefficient := 1, powers := [(9, 1), (25, 1), (44, 1)] }, { coefficient := 1, powers := [(9, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(14, 1), (19, 1), (50, 1)] }, { coefficient := 1, powers := [(14, 1), (25, 1), (41, 1)] }, { coefficient := 1, powers := [(14, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (40, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (43, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (49, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (37, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (49, 1)] }, { coefficient := 1, powers := [(8, 1), (37, 1), (43, 1)] }, { coefficient := 1, powers := [(13, 1), (24, 1), (57, 1)] }, { coefficient := 1, powers := [(13, 1), (31, 1), (49, 1)] }, { coefficient := 1, powers := [(13, 1), (37, 1), (40, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (54, 1)] }, { coefficient := 1, powers := [(18, 1), (31, 1), (43, 1)] }, { coefficient := 1, powers := [(18, 1), (34, 1), (40, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(41, 1)] }],
  [{ coefficient := 1, powers := [(43, 1)] }],
  [{ coefficient := 1, powers := [(55, 1)] }],
  [{ coefficient := 1, powers := [(56, 1)] }],
  [{ coefficient := 1, powers := [(57, 1), (64, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(25, 1), (65, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(28, 1)] }],
  [{ coefficient := 1, powers := [(31, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 49 → SparsePoly (Fin 66) := ![
  [{ coefficient := 1, powers := [(0, 1), (9, 1), (27, 1), (62, 1)] }, { coefficient := 1, powers := [(0, 1), (10, 1), (27, 2), (62, 2)] }, { coefficient := -1, powers := [(6, 1), (27, 1), (32, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (24, 1), (25, 1), (57, 1), (58, 1), (65, 1)] }, { coefficient := -1, powers := [(3, 1), (24, 1), (35, 1), (50, 1), (57, 1), (65, 1)] }, { coefficient := -1, powers := [(14, 1), (24, 1), (32, 1), (38, 1), (57, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (24, 1), (25, 1), (26, 1), (58, 1)] }, { coefficient := -1, powers := [(3, 1), (24, 1), (26, 1), (35, 1), (50, 1)] }, { coefficient := -1, powers := [(14, 1), (24, 1), (26, 1), (32, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (18, 1), (21, 1), (24, 1), (25, 1), (58, 1), (62, 1)] }, { coefficient := 1, powers := [(3, 1), (18, 1), (21, 1), (24, 1), (35, 1), (50, 1), (62, 1)] }, { coefficient := -1, powers := [(5, 1), (14, 1), (21, 1), (32, 1), (37, 1), (38, 1), (62, 1)] }, { coefficient := 1, powers := [(14, 1), (18, 1), (21, 1), (24, 1), (32, 1), (38, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (17, 1), (25, 1), (49, 1), (58, 1)] }, { coefficient := -1, powers := [(3, 1), (17, 1), (35, 1), (49, 1), (50, 1)] }, { coefficient := -1, powers := [(5, 1), (25, 1), (45, 1), (58, 1)] }, { coefficient := -1, powers := [(5, 1), (35, 1), (45, 1), (50, 1)] }, { coefficient := -1, powers := [(14, 1), (17, 1), (32, 1), (38, 1), (49, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (18, 1), (24, 1), (25, 1), (58, 1), (62, 1)] }, { coefficient := -1, powers := [(3, 1), (18, 1), (24, 1), (35, 1), (50, 1), (62, 1)] }, { coefficient := 1, powers := [(5, 1), (14, 1), (32, 1), (37, 1), (38, 1), (62, 1)] }, { coefficient := -1, powers := [(14, 1), (18, 1), (24, 1), (32, 1), (38, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(14, 1), (26, 1), (34, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (20, 1), (34, 1), (38, 1), (45, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (13, 1), (25, 1), (45, 1), (58, 1)] }, { coefficient := -1, powers := [(3, 1), (13, 1), (35, 1), (45, 1), (50, 1)] }, { coefficient := -1, powers := [(13, 1), (14, 1), (32, 1), (38, 1), (45, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (9, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 1), (10, 1), (27, 1), (62, 2)] }, { coefficient := 1, powers := [(6, 1), (32, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(19, 1)] }],
  [{ coefficient := -1, powers := [(14, 1), (20, 1), (34, 1), (38, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (18, 1), (25, 1), (58, 1)] }, { coefficient := 1, powers := [(3, 1), (18, 1), (35, 1), (50, 1)] }, { coefficient := 1, powers := [(14, 1), (18, 1), (32, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (14, 1), (26, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (20, 1), (34, 1), (38, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (35, 1), (45, 1), (64, 1)] }, { coefficient := -1, powers := [(14, 1), (25, 1), (45, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (14, 1), (45, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (25, 1), (49, 1), (58, 1)] }, { coefficient := 1, powers := [(3, 1), (35, 1), (49, 1), (50, 1)] }, { coefficient := 1, powers := [(14, 1), (32, 1), (38, 1), (49, 1)] }],
  [{ coefficient := -1, powers := [(14, 1), (34, 1), (38, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (24, 1), (25, 1), (58, 1)] }, { coefficient := 1, powers := [(3, 1), (24, 1), (35, 1), (50, 1)] }, { coefficient := 1, powers := [(14, 1), (24, 1), (32, 1), (38, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (35, 1), (45, 1), (46, 1), (64, 1)] }, { coefficient := 1, powers := [(3, 1), (35, 1), (47, 1), (64, 1)] }, { coefficient := 1, powers := [(14, 1), (18, 1), (34, 1), (38, 1), (48, 1)] }, { coefficient := 1, powers := [(14, 1), (25, 1), (45, 1), (46, 1), (64, 1)] }, { coefficient := -1, powers := [(14, 1), (25, 1), (47, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(9, 1), (14, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (26, 1), (35, 1), (64, 1)] }, { coefficient := -1, powers := [(14, 1), (25, 1), (26, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (18, 1), (26, 1), (34, 1), (38, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (15, 1), (25, 1), (62, 1)] }, { coefficient := -1, powers := [(15, 1), (19, 1), (25, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (25, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (50, 1)] }],
  [{ coefficient := -1, powers := [(14, 1), (20, 1), (34, 1), (38, 1), (57, 1)] }, { coefficient := 1, powers := [(14, 1), (26, 1), (34, 1), (38, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (13, 1), (25, 1), (58, 1)] }, { coefficient := 1, powers := [(3, 1), (13, 1), (35, 1), (50, 1)] }, { coefficient := 1, powers := [(13, 1), (14, 1), (32, 1), (38, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (35, 1), (64, 1)] }, { coefficient := 1, powers := [(14, 1), (25, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(14, 1), (18, 1), (34, 1), (38, 1)] }],
  [{ coefficient := -1, powers := [(9, 1), (14, 1), (26, 1), (45, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (26, 1), (35, 1), (45, 1), (64, 1)] }, { coefficient := 1, powers := [(14, 1), (25, 1), (26, 1), (45, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(9, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (34, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (26, 1), (35, 1), (45, 1), (46, 1), (64, 1)] }, { coefficient := -1, powers := [(3, 1), (26, 1), (35, 1), (47, 1), (64, 1)] }, { coefficient := -1, powers := [(14, 1), (18, 1), (26, 1), (34, 1), (38, 1), (48, 1)] }, { coefficient := -1, powers := [(14, 1), (25, 1), (26, 1), (45, 1), (46, 1), (64, 1)] }, { coefficient := 1, powers := [(14, 1), (25, 1), (26, 1), (47, 1), (64, 1)] }, { coefficient := -1, powers := [(14, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (14, 1), (25, 1), (62, 1)] }, { coefficient := 1, powers := [(14, 1), (19, 1), (25, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(3, 1), (25, 1), (58, 1)] }, { coefficient := -1, powers := [(3, 1), (35, 1), (50, 1)] }, { coefficient := -1, powers := [(14, 1), (32, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (9, 1), (44, 1)] }, { coefficient := 1, powers := [(0, 1), (10, 1), (27, 1), (44, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 1), (14, 1), (25, 1), (51, 1)] }, { coefficient := -1, powers := [(0, 1), (38, 1), (58, 1)] }, { coefficient := -1, powers := [(0, 1), (44, 1), (50, 1)] }, { coefficient := 1, powers := [(3, 1), (18, 1), (24, 1), (25, 1), (54, 1), (58, 1)] }, { coefficient := 1, powers := [(3, 1), (18, 1), (24, 1), (35, 1), (50, 1), (54, 1)] }, { coefficient := -1, powers := [(5, 1), (14, 1), (32, 1), (37, 1), (38, 1), (54, 1)] }, { coefficient := -1, powers := [(6, 1), (32, 1), (44, 1)] }, { coefficient := 1, powers := [(14, 1), (18, 1), (24, 1), (32, 1), (38, 1), (54, 1)] }, { coefficient := -1, powers := [(14, 1), (19, 1), (25, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (25, 1), (40, 1), (58, 1), (60, 1)] }, { coefficient := 1, powers := [(3, 1), (35, 1), (40, 1), (50, 1), (60, 1)] }, { coefficient := 1, powers := [(14, 1), (32, 1), (38, 1), (40, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (7, 1), (14, 1), (25, 1), (36, 1), (62, 1)] }, { coefficient := 1, powers := [(6, 1), (35, 1)] }, { coefficient := -1, powers := [(7, 1), (14, 1), (19, 1), (25, 1), (36, 1), (62, 1)] }, { coefficient := 1, powers := [(14, 1), (17, 1), (20, 1), (34, 1), (38, 1), (57, 1)] }, { coefficient := 1, powers := [(14, 1), (18, 1), (20, 1), (34, 1), (38, 1), (53, 1)] }, { coefficient := 2, powers := [(14, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (3, 1), (25, 1), (57, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (3, 1), (35, 1), (50, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (14, 1), (32, 1), (38, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (8, 1), (25, 1), (37, 1), (58, 1)] }, { coefficient := 1, powers := [(3, 1), (8, 1), (35, 1), (37, 1), (50, 1)] }, { coefficient := 1, powers := [(8, 1), (14, 1), (32, 1), (37, 1), (38, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (1, 1), (41, 1), (62, 1)] }, { coefficient := 1, powers := [(0, 1), (9, 1), (11, 1), (21, 1), (62, 1)] }, { coefficient := 1, powers := [(0, 1), (10, 1), (11, 1), (21, 1), (27, 1), (62, 2)] }, { coefficient := -1, powers := [(0, 1), (10, 1), (21, 1), (62, 1)] }, { coefficient := 1, powers := [(0, 1), (41, 1)] }, { coefficient := 1, powers := [(3, 1), (32, 1)] }, { coefficient := -1, powers := [(6, 1), (11, 1), (21, 1), (32, 1), (62, 1)] }, { coefficient := -1, powers := [(9, 1), (19, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (1, 1), (14, 1), (25, 1), (41, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 1), (3, 1), (26, 1), (35, 1), (41, 1), (45, 1), (46, 1), (64, 1)] }, { coefficient := 1, powers := [(0, 1), (3, 1), (26, 1), (35, 1), (41, 1), (47, 1), (64, 1)] }, { coefficient := -1, powers := [(0, 1), (10, 1), (14, 1), (21, 1), (25, 1), (62, 1)] }, { coefficient := 1, powers := [(0, 1), (14, 1), (18, 1), (26, 1), (34, 1), (38, 1), (41, 1), (48, 1)] }, { coefficient := 1, powers := [(0, 1), (14, 1), (25, 1), (26, 1), (41, 1), (45, 1), (46, 1), (64, 1)] }, { coefficient := -1, powers := [(0, 1), (14, 1), (25, 1), (26, 1), (41, 1), (47, 1), (64, 1)] }, { coefficient := 1, powers := [(0, 1), (14, 1), (25, 1), (41, 1)] }, { coefficient := -1, powers := [(1, 1), (14, 1), (19, 1), (25, 1), (41, 1), (62, 1)] }, { coefficient := -1, powers := [(3, 2), (26, 1), (32, 1), (35, 1), (45, 1), (46, 1), (64, 1)] }, { coefficient := 1, powers := [(3, 2), (26, 1), (32, 1), (35, 1), (47, 1), (64, 1)] }, { coefficient := -1, powers := [(3, 1), (9, 1), (19, 1), (26, 1), (35, 1), (45, 1), (46, 1), (64, 1)] }, { coefficient := 1, powers := [(3, 1), (9, 1), (19, 1), (26, 1), (35, 1), (47, 1), (64, 1)] }, { coefficient := 1, powers := [(3, 1), (9, 1), (26, 1), (35, 1), (45, 1), (64, 1)] }, { coefficient := 1, powers := [(3, 1), (14, 1), (18, 1), (26, 1), (32, 1), (34, 1), (38, 1), (48, 1)] }, { coefficient := 1, powers := [(3, 1), (14, 1), (25, 1), (26, 1), (32, 1), (45, 1), (46, 1), (64, 1)] }, { coefficient := -1, powers := [(3, 1), (14, 1), (25, 1), (26, 1), (32, 1), (47, 1), (64, 1)] }, { coefficient := 1, powers := [(3, 1), (14, 1), (25, 1), (32, 1)] }, { coefficient := 1, powers := [(9, 1), (14, 1), (18, 1), (19, 1), (26, 1), (34, 1), (38, 1), (48, 1)] }, { coefficient := -1, powers := [(9, 1), (14, 1), (18, 1), (20, 1), (26, 1), (34, 1), (38, 1)] }, { coefficient := 1, powers := [(9, 1), (14, 1), (19, 1), (25, 1), (26, 1), (45, 1), (46, 1), (64, 1)] }, { coefficient := -1, powers := [(9, 1), (14, 1), (19, 1), (25, 1), (26, 1), (47, 1), (64, 1)] }, { coefficient := 1, powers := [(9, 1), (14, 1), (19, 1), (25, 1)] }, { coefficient := 1, powers := [(9, 1), (14, 1), (19, 1), (26, 1), (45, 1), (64, 1)] }, { coefficient := -1, powers := [(9, 1), (14, 1), (25, 1), (26, 1), (45, 1), (64, 1)] }, { coefficient := -1, powers := [(10, 1), (14, 1), (19, 1), (21, 1), (25, 1), (62, 1)] }, { coefficient := 1, powers := [(12, 1), (14, 1), (19, 1), (20, 1), (34, 1), (38, 1), (57, 1)] }, { coefficient := -1, powers := [(12, 1), (14, 1), (19, 1), (26, 1), (34, 1), (38, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (9, 1), (35, 1)] }, { coefficient := 1, powers := [(9, 1), (14, 1), (19, 1)] }, { coefficient := -1, powers := [(9, 1), (14, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (13, 1), (24, 1), (25, 1), (57, 1), (58, 1)] }, { coefficient := 1, powers := [(3, 1), (13, 1), (24, 1), (35, 1), (50, 1), (57, 1)] }, { coefficient := 1, powers := [(13, 1), (14, 1), (24, 1), (32, 1), (38, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (3, 1), (15, 1), (25, 1), (58, 1), (62, 1)] }, { coefficient := 1, powers := [(0, 1), (9, 1), (15, 1), (25, 1), (44, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 1), (10, 1), (14, 1), (25, 1), (62, 1)] }, { coefficient := 1, powers := [(3, 1), (15, 1), (19, 1), (25, 1), (58, 1), (62, 1)] }, { coefficient := 1, powers := [(9, 1), (15, 1), (19, 1), (25, 1), (44, 1), (62, 1)] }, { coefficient := -1, powers := [(10, 1), (14, 1), (19, 1), (25, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (13, 1), (25, 1), (45, 1), (48, 1), (58, 1)] }, { coefficient := -1, powers := [(3, 1), (13, 1), (25, 1), (49, 1), (58, 1)] }, { coefficient := 1, powers := [(3, 1), (13, 1), (35, 1), (45, 1), (48, 1), (50, 1)] }, { coefficient := -1, powers := [(3, 1), (13, 1), (35, 1), (49, 1), (50, 1)] }, { coefficient := 1, powers := [(5, 1), (14, 1), (32, 1), (38, 1), (60, 1)] }, { coefficient := 1, powers := [(13, 1), (14, 1), (32, 1), (38, 1), (45, 1), (48, 1)] }, { coefficient := -1, powers := [(13, 1), (14, 1), (32, 1), (38, 1), (49, 1)] }]
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
    ¬ ∀ index : Fin 49,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component18.SelectedLeafB6_2_1_4.selectedHasNoCommonZero

end Krenn.Component18.SelectedLeafB6_2_1_4
