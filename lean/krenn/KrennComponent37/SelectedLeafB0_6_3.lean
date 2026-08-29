import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component37.SelectedLeafB0_6_3

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "2248365597c53bef3365d7309a3a1b89199173651b4bc7e35357905fb985195c"
def certificateSHA256 : String := "233064809230f36a7d49ab033b642a0279de9181f7570486652221b805e6a3b6"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 68 → Fin 667 := ![
  8,
  16,
  19,
  70,
  71,
  79,
  149,
  151,
  152,
  170,
  171,
  178,
  179,
  180,
  183,
  184,
  221,
  230,
  231,
  294,
  301,
  303,
  312,
  313,
  315,
  316,
  414,
  424,
  433,
  438,
  440,
  446,
  447,
  450,
  458,
  461,
  463,
  465,
  466,
  470,
  472,
  473,
  474,
  475,
  476,
  501,
  527,
  568,
  570,
  581,
  583,
  584,
  586,
  602,
  603,
  608,
  612,
  617,
  628,
  645,
  655,
  657,
  658,
  660,
  661,
  663,
  664,
  666
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 68 → SparsePoly (Fin 66) := ![
  [{ coefficient := 1, powers := [(9, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (26, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (26, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (30, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (26, 1)] }, { coefficient := 1, powers := [(26, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (30, 1)] }, { coefficient := 1, powers := [(30, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (44, 1)] }, { coefficient := 1, powers := [(40, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (44, 1)] }, { coefficient := 1, powers := [(19, 1), (20, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (47, 1)] }, { coefficient := -1, powers := [(29, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (55, 1)] }, { coefficient := 1, powers := [(30, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (44, 1)] }, { coefficient := 1, powers := [(28, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(28, 1), (53, 1)] }, { coefficient := -1, powers := [(29, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (55, 1)] }, { coefficient := 1, powers := [(30, 1), (46, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (26, 1), (47, 1)] }, { coefficient := 1, powers := [(9, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (29, 1), (47, 1)] }, { coefficient := 1, powers := [(9, 1), (36, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (29, 1), (58, 1)] }, { coefficient := 1, powers := [(9, 1), (30, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1)] }, { coefficient := 1, powers := [(20, 1), (44, 1)] }, { coefficient := 1, powers := [(25, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (59, 1)] }, { coefficient := 1, powers := [(9, 1), (43, 1)] }, { coefficient := 1, powers := [(13, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (46, 1)] }, { coefficient := 1, powers := [(9, 1), (57, 1)] }, { coefficient := 1, powers := [(31, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (54, 1)] }, { coefficient := 1, powers := [(30, 1), (41, 1)] }, { coefficient := 1, powers := [(30, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(20, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(44, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1), (51, 1)] }, { coefficient := 1, powers := [(25, 1), (46, 1), (51, 1)] }, { coefficient := 1, powers := [(51, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1), (55, 1)] }, { coefficient := 1, powers := [(26, 1), (46, 1), (51, 1)] }, { coefficient := 1, powers := [(55, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (44, 1), (55, 1)] }, { coefficient := 1, powers := [(29, 1), (51, 1), (58, 1)] }, { coefficient := 1, powers := [(30, 1), (47, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1)] }, { coefficient := 1, powers := [(25, 1), (41, 1), (44, 1)] }, { coefficient := 1, powers := [(25, 1), (47, 1)] }, { coefficient := 1, powers := [(44, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (49, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1)] }, { coefficient := 1, powers := [(18, 1), (28, 1), (49, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1)] }, { coefficient := 1, powers := [(12, 1), (30, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (36, 1)] }, { coefficient := 1, powers := [(23, 1), (44, 1)] }, { coefficient := 1, powers := [(28, 1), (44, 1)] }, { coefficient := 1, powers := [(36, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (61, 1)] }, { coefficient := 1, powers := [(12, 1), (49, 1)] }, { coefficient := 1, powers := [(19, 1), (21, 1), (53, 1)] }, { coefficient := 1, powers := [(19, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (33, 1)] }, { coefficient := 1, powers := [(23, 1), (51, 1)] }, { coefficient := 1, powers := [(28, 1), (51, 1)] }, { coefficient := 1, powers := [(33, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (61, 1)] }, { coefficient := 1, powers := [(12, 1), (26, 1), (47, 1)] }, { coefficient := 1, powers := [(12, 1), (58, 1)] }, { coefficient := 1, powers := [(19, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (38, 1), (61, 1)] }, { coefficient := 1, powers := [(0, 1), (47, 1), (53, 1)] }, { coefficient := 1, powers := [(44, 1), (53, 1)] }, { coefficient := 1, powers := [(47, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1), (52, 1)] }, { coefficient := 1, powers := [(3, 1), (34, 1), (52, 1)] }, { coefficient := 1, powers := [(13, 1), (20, 1), (52, 1)] }, { coefficient := 1, powers := [(43, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1), (54, 1)] }, { coefficient := 1, powers := [(3, 1), (34, 1), (54, 1)] }, { coefficient := 1, powers := [(13, 1), (20, 1), (54, 1)] }, { coefficient := 1, powers := [(26, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1), (53, 1)] }, { coefficient := 1, powers := [(3, 1), (61, 1)] }, { coefficient := 1, powers := [(20, 1), (44, 1), (53, 1)] }, { coefficient := 1, powers := [(44, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1), (54, 1)] }, { coefficient := 1, powers := [(20, 1), (44, 1), (54, 1)] }, { coefficient := 1, powers := [(20, 1), (58, 1)] }, { coefficient := 1, powers := [(26, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1), (50, 1)] }, { coefficient := 1, powers := [(6, 1), (31, 1), (46, 1)] }, { coefficient := 1, powers := [(9, 1), (25, 1), (46, 1)] }, { coefficient := 1, powers := [(50, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1), (54, 1)] }, { coefficient := 1, powers := [(26, 1), (41, 1)] }, { coefficient := 1, powers := [(26, 1), (46, 1)] }, { coefficient := 1, powers := [(54, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1), (50, 1)] }, { coefficient := 1, powers := [(6, 1), (31, 1), (47, 1)] }, { coefficient := 1, powers := [(9, 1), (25, 1), (47, 1)] }, { coefficient := 1, powers := [(44, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1), (51, 1)] }, { coefficient := 1, powers := [(6, 1), (61, 1)] }, { coefficient := 1, powers := [(25, 1), (47, 1), (51, 1)] }, { coefficient := 1, powers := [(44, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1), (52, 1)] }, { coefficient := 1, powers := [(41, 1), (44, 1)] }, { coefficient := 1, powers := [(44, 1), (52, 1)] }, { coefficient := 1, powers := [(47, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1), (55, 1)] }, { coefficient := 1, powers := [(26, 1), (47, 1), (51, 1)] }, { coefficient := 1, powers := [(44, 1), (55, 1)] }, { coefficient := 1, powers := [(51, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (29, 1), (61, 1)] }, { coefficient := 1, powers := [(3, 1), (36, 1), (53, 1)] }, { coefficient := 1, powers := [(23, 1), (44, 1), (53, 1)] }, { coefficient := 1, powers := [(29, 1), (44, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (29, 1), (61, 1)] }, { coefficient := 1, powers := [(6, 1), (33, 1), (47, 1)] }, { coefficient := 1, powers := [(28, 1), (47, 1), (51, 1)] }, { coefficient := 1, powers := [(29, 1), (44, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (41, 1), (44, 1)] }, { coefficient := 1, powers := [(29, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(29, 1), (47, 1)] }, { coefficient := 1, powers := [(36, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (44, 1), (54, 1)] }, { coefficient := 1, powers := [(29, 1), (58, 1)] }, { coefficient := 1, powers := [(30, 1), (41, 1), (44, 1)] }, { coefficient := 1, powers := [(30, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (52, 1)] }, { coefficient := 1, powers := [(3, 1), (60, 1)] }, { coefficient := 1, powers := [(20, 1), (52, 1)] }, { coefficient := 1, powers := [(20, 1), (57, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (31, 1), (57, 1)] }, { coefficient := 1, powers := [(9, 1), (20, 1), (57, 1)] }, { coefficient := 1, powers := [(9, 1)] }, { coefficient := 1, powers := [(40, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (40, 1), (58, 1)] }, { coefficient := 1, powers := [(3, 1), (31, 1), (58, 1)] }, { coefficient := 1, powers := [(9, 1), (20, 1), (58, 1)] }, { coefficient := 1, powers := [(9, 1), (26, 1), (44, 1)] }, { coefficient := 1, powers := [(26, 1), (40, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1), (52, 1)] }, { coefficient := 1, powers := [(13, 1), (41, 1)] }, { coefficient := 1, powers := [(13, 1), (52, 1)] }, { coefficient := 1, powers := [(34, 1), (38, 1)] }, { coefficient := 1, powers := [(45, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1)] }, { coefficient := 1, powers := [(3, 1), (34, 1)] }, { coefficient := 1, powers := [(13, 1), (20, 1)] }, { coefficient := 1, powers := [(20, 1), (56, 1)] }, { coefficient := 1, powers := [(25, 1), (43, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (50, 1)] }, { coefficient := 1, powers := [(6, 1), (31, 1)] }, { coefficient := 1, powers := [(9, 1), (25, 1)] }, { coefficient := 1, powers := [(20, 1), (50, 1)] }, { coefficient := 1, powers := [(25, 1), (40, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (41, 1), (58, 1)] }, { coefficient := 1, powers := [(0, 1), (47, 1), (54, 1)] }, { coefficient := 1, powers := [(26, 1), (41, 1), (44, 1)] }, { coefficient := 1, powers := [(26, 1), (47, 1)] }, { coefficient := 1, powers := [(44, 1), (54, 1)] }, { coefficient := 1, powers := [(58, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1), (50, 1)] }, { coefficient := 1, powers := [(6, 1), (31, 1), (45, 1)] }, { coefficient := 1, powers := [(6, 1), (59, 1)] }, { coefficient := 1, powers := [(9, 1), (25, 1), (45, 1)] }, { coefficient := 1, powers := [(9, 1), (56, 1)] }, { coefficient := 1, powers := [(13, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (37, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (44, 1), (51, 1)] }, { coefficient := 1, powers := [(12, 1), (28, 1), (44, 1)] }, { coefficient := 1, powers := [(12, 1), (36, 1), (37, 1)] }, { coefficient := 1, powers := [(19, 1), (23, 1), (51, 1)] }, { coefficient := 1, powers := [(19, 1), (33, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (30, 1), (61, 1)] }, { coefficient := 1, powers := [(3, 1), (33, 1), (58, 1)] }, { coefficient := 1, powers := [(3, 1), (36, 1), (55, 1)] }, { coefficient := 1, powers := [(23, 1), (44, 1), (55, 1)] }, { coefficient := 1, powers := [(23, 1), (51, 1), (58, 1)] }, { coefficient := 1, powers := [(30, 1), (44, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (38, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (41, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(41, 1)] }, { coefficient := 1, powers := [(46, 1)] }, { coefficient := 1, powers := [(52, 1)] }, { coefficient := 1, powers := [(57, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (37, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (40, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (43, 1), (50, 1)] }, { coefficient := 1, powers := [(3, 1), (25, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (31, 1), (56, 1)] }, { coefficient := 1, powers := [(3, 1), (34, 1), (50, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (31, 1), (43, 1)] }, { coefficient := 1, powers := [(6, 1), (34, 1), (40, 1)] }, { coefficient := 1, powers := [(9, 1), (20, 1), (56, 1)] }, { coefficient := 1, powers := [(9, 1), (25, 1), (43, 1)] }, { coefficient := 1, powers := [(9, 1), (34, 1), (37, 1)] }, { coefficient := 1, powers := [(13, 1), (20, 1), (50, 1)] }, { coefficient := 1, powers := [(13, 1), (25, 1), (40, 1)] }, { coefficient := 1, powers := [(13, 1), (31, 1), (37, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (39, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (42, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (49, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (49, 1)] }, { coefficient := 1, powers := [(8, 1), (36, 1), (42, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (58, 1)] }, { coefficient := 1, powers := [(12, 1), (30, 1), (49, 1)] }, { coefficient := 1, powers := [(12, 1), (36, 1), (39, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (55, 1)] }, { coefficient := 1, powers := [(19, 1), (30, 1), (42, 1)] }, { coefficient := 1, powers := [(19, 1), (33, 1), (39, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1)] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(40, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(42, 1)] }],
  [{ coefficient := 1, powers := [(56, 1)] }],
  [{ coefficient := 1, powers := [(58, 1), (65, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 68 → SparsePoly (Fin 66) := ![
  [{ coefficient := -2, powers := [(3, 1), (12, 1), (30, 1), (60, 1), (62, 1)] }, { coefficient := 2, powers := [(6, 1), (12, 1), (30, 1), (60, 1), (62, 1)] }],
  [{ coefficient := -2, powers := [(3, 1), (24, 1), (44, 1), (55, 1), (60, 1), (62, 1)] }, { coefficient := -2, powers := [(3, 1), (30, 1), (49, 1), (51, 1), (60, 1), (62, 1)] }, { coefficient := -5, powers := [(9, 1), (24, 1), (25, 1), (34, 1), (37, 1), (44, 1), (47, 1), (54, 1), (55, 1), (62, 1), (65, 1)] }, { coefficient := -5, powers := [(9, 1), (25, 1), (30, 1), (34, 1), (37, 1), (47, 1), (49, 1), (51, 1), (54, 1), (62, 1), (65, 1)] }, { coefficient := -2, powers := [(24, 1), (37, 1), (44, 1), (55, 1), (60, 1), (62, 1)] }],
  [{ coefficient := 5, powers := [(3, 1), (9, 1), (25, 1), (29, 1), (34, 1), (39, 1), (54, 1), (61, 1), (62, 1), (65, 1)] }, { coefficient := 2, powers := [(3, 1), (21, 1), (30, 1), (53, 1), (60, 1), (62, 1)] }, { coefficient := -2, powers := [(3, 1), (24, 1), (26, 1), (53, 1), (60, 1), (62, 1)] }, { coefficient := 2, powers := [(3, 1), (24, 1), (55, 1), (60, 1), (62, 1)] }, { coefficient := -2, powers := [(3, 1), (33, 1), (39, 1), (60, 1), (62, 1)] }, { coefficient := 5, powers := [(6, 1), (9, 1), (21, 1), (25, 1), (29, 1), (34, 1), (53, 1), (54, 1), (58, 1), (62, 1), (65, 1)] }, { coefficient := -2, powers := [(6, 1), (21, 1), (30, 1), (53, 1), (60, 1), (62, 1)] }, { coefficient := 5, powers := [(9, 1), (21, 1), (25, 1), (30, 1), (34, 1), (37, 1), (47, 1), (53, 1), (54, 1), (62, 1), (65, 1)] }, { coefficient := -5, powers := [(9, 1), (24, 1), (25, 1), (26, 1), (34, 1), (37, 1), (47, 1), (53, 1), (54, 1), (62, 1), (65, 1)] }, { coefficient := 5, powers := [(9, 1), (24, 1), (25, 1), (34, 1), (37, 1), (47, 1), (54, 1), (55, 1), (62, 1), (65, 1)] }, { coefficient := -5, powers := [(9, 1), (25, 1), (30, 1), (34, 1), (37, 1), (49, 1), (53, 1), (54, 1), (62, 1), (65, 1)] }, { coefficient := -5, powers := [(9, 1), (25, 1), (33, 1), (34, 1), (37, 1), (39, 1), (47, 1), (54, 1), (62, 1), (65, 1)] }, { coefficient := -2, powers := [(20, 1), (23, 1), (39, 1), (53, 1), (60, 1), (62, 1)] }, { coefficient := -2, powers := [(23, 1), (39, 1), (51, 1), (60, 1), (62, 1)] }, { coefficient := 2, powers := [(24, 1), (37, 1), (55, 1), (60, 1), (62, 1)] }, { coefficient := -2, powers := [(33, 1), (37, 1), (39, 1), (60, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(25, 2), (44, 1), (47, 1), (54, 1), (65, 2)] }],
  [{ coefficient := 2, powers := [(25, 1), (41, 1), (44, 1), (62, 1), (65, 1)] }],
  [{ coefficient := -5, powers := [(6, 1), (9, 1), (12, 1), (25, 1), (34, 1), (44, 1), (49, 1), (54, 1), (62, 1), (65, 1)] }],
  [{ coefficient := -5, powers := [(6, 1), (9, 1), (12, 1), (25, 1), (34, 1), (36, 1), (38, 1), (49, 1), (54, 1), (62, 1), (65, 1)] }, { coefficient := -2, powers := [(25, 1), (41, 1), (44, 1), (46, 1), (62, 1), (65, 1)] }, { coefficient := -2, powers := [(25, 1), (46, 1), (47, 1), (62, 1), (65, 1)] }],
  [{ coefficient := 2, powers := [(3, 1), (12, 1), (49, 1), (60, 1), (62, 1)] }, { coefficient := 5, powers := [(6, 1), (9, 1), (12, 1), (25, 1), (34, 1), (44, 1), (46, 1), (49, 1), (54, 1), (62, 1), (65, 1)] }, { coefficient := -5, powers := [(6, 1), (9, 1), (12, 1), (25, 1), (34, 1), (47, 1), (49, 1), (54, 1), (62, 1), (65, 1)] }, { coefficient := -2, powers := [(6, 1), (12, 1), (49, 1), (60, 1), (62, 1)] }],
  [{ coefficient := -2, powers := [(5, 1), (28, 1), (55, 1), (60, 1), (62, 1)] }, { coefficient := 2, powers := [(6, 1), (25, 1), (34, 1), (41, 1), (54, 1), (65, 1)] }, { coefficient := 2, powers := [(6, 1), (25, 1), (34, 1), (52, 1), (54, 1), (65, 1)] }, { coefficient := -4, powers := [(13, 1), (25, 2), (41, 1), (54, 1), (65, 1)] }, { coefficient := -4, powers := [(13, 1), (25, 2), (52, 1), (54, 1), (65, 1)] }, { coefficient := -1, powers := [(13, 1), (25, 1), (26, 1), (47, 1), (54, 1), (65, 2)] }, { coefficient := -2, powers := [(25, 2), (45, 1), (54, 1), (65, 1)] }, { coefficient := 2, powers := [(25, 1), (26, 1), (41, 1), (46, 1), (62, 1), (65, 1)] }, { coefficient := 1, powers := [(25, 1), (26, 1), (44, 1), (45, 1), (54, 1), (65, 2)] }, { coefficient := 2, powers := [(25, 1), (26, 1), (46, 2), (62, 1), (65, 1)] }, { coefficient := 2, powers := [(25, 1), (26, 1), (46, 1), (52, 1), (62, 1), (65, 1)] }],
  [{ coefficient := 2, powers := [(23, 1), (39, 1), (60, 1)] }],
  [{ coefficient := 2, powers := [(3, 1), (24, 1), (26, 1), (60, 1)] }, { coefficient := 5, powers := [(9, 1), (24, 1), (25, 1), (26, 1), (34, 1), (37, 1), (47, 1), (54, 1), (65, 1)] }, { coefficient := 5, powers := [(9, 1), (25, 1), (30, 1), (34, 1), (37, 1), (49, 1), (54, 1), (65, 1)] }, { coefficient := -5, powers := [(9, 1), (25, 1), (34, 1), (36, 1), (37, 1), (39, 1), (54, 1), (65, 1)] }],
  [{ coefficient := 5, powers := [(5, 1), (9, 1), (25, 1), (34, 1), (51, 1), (54, 1), (58, 1), (65, 1)] }, { coefficient := 2, powers := [(5, 1), (26, 1), (44, 1), (55, 1), (60, 1), (65, 1)] }, { coefficient := -2, powers := [(5, 1), (26, 1), (51, 1), (60, 1)] }],
  [{ coefficient := 2, powers := [(3, 1), (18, 1), (49, 1), (60, 1)] }, { coefficient := -2, powers := [(5, 1), (26, 1), (44, 1), (47, 1), (60, 1), (65, 1)] }, { coefficient := -2, powers := [(5, 1), (44, 1), (60, 1)] }, { coefficient := 5, powers := [(9, 1), (18, 1), (25, 1), (34, 1), (37, 1), (47, 1), (49, 1), (54, 1), (65, 1)] }],
  [{ coefficient := 2, powers := [(3, 1), (18, 1), (55, 1), (60, 1)] }, { coefficient := 5, powers := [(9, 1), (18, 1), (25, 1), (34, 1), (37, 1), (47, 1), (54, 1), (55, 1), (65, 1)] }, { coefficient := 2, powers := [(18, 1), (37, 1), (55, 1), (60, 1)] }],
  [{ coefficient := -5, powers := [(9, 1), (19, 1), (25, 1), (34, 1), (39, 1), (44, 1), (54, 1), (65, 1)] }],
  [{ coefficient := -4, powers := [(5, 1), (25, 1), (44, 1), (60, 1)] }],
  [{ coefficient := -2, powers := [(5, 1), (28, 1), (51, 1), (60, 1), (62, 1)] }, { coefficient := -5, powers := [(6, 1), (9, 1), (12, 1), (25, 1), (29, 1), (34, 1), (49, 1), (54, 1), (62, 1), (65, 1)] }, { coefficient := -1, powers := [(25, 2), (44, 1), (45, 1), (54, 1), (65, 2)] }, { coefficient := 2, powers := [(25, 1), (46, 1), (62, 1), (65, 1)] }],
  [{ coefficient := 5, powers := [(6, 1), (9, 1), (12, 1), (25, 1), (26, 1), (34, 1), (49, 1), (54, 1), (62, 1), (65, 1)] }],
  [{ coefficient := 5, powers := [(6, 1), (9, 1), (12, 1), (25, 1), (34, 1), (49, 1), (54, 1), (62, 1), (65, 1)] }],
  [{ coefficient := -2, powers := [(5, 1), (30, 1), (53, 1), (60, 1)] }, { coefficient := 2, powers := [(9, 1), (13, 1), (25, 1), (41, 1), (54, 1), (65, 1)] }, { coefficient := 1, powers := [(9, 1), (25, 1), (45, 1), (54, 1), (65, 1)] }, { coefficient := -6, powers := [(13, 1), (25, 1), (41, 1), (50, 1), (54, 1), (65, 1)] }, { coefficient := -4, powers := [(25, 1), (45, 1), (50, 1), (54, 1), (65, 1)] }, { coefficient := 2, powers := [(26, 1), (41, 1), (52, 1), (65, 1)] }, { coefficient := 2, powers := [(26, 1), (46, 1), (52, 1), (65, 1)] }, { coefficient := -2, powers := [(41, 1), (54, 1), (65, 1)] }, { coefficient := -2, powers := [(46, 1), (54, 1), (65, 1)] }],
  [{ coefficient := -2, powers := [(25, 2), (47, 1), (54, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (25, 1), (34, 1), (44, 1), (54, 1), (65, 1)] }, { coefficient := 2, powers := [(6, 1), (25, 1), (34, 1), (44, 1), (54, 1), (65, 1)] }, { coefficient := 2, powers := [(25, 1), (34, 1), (37, 1), (44, 1), (54, 1), (65, 1)] }],
  [{ coefficient := -5, powers := [(6, 1), (9, 1), (12, 1), (25, 1), (34, 1), (44, 1), (49, 1), (54, 1), (65, 1)] }],
  [{ coefficient := 2, powers := [(9, 1), (13, 1), (25, 1), (54, 1), (65, 1)] }, { coefficient := -6, powers := [(13, 1), (25, 1), (50, 1), (54, 1), (65, 1)] }, { coefficient := -2, powers := [(26, 1), (41, 1), (65, 1)] }, { coefficient := -2, powers := [(26, 1), (46, 1), (65, 1)] }],
  [{ coefficient := -4, powers := [(5, 1), (26, 1), (29, 1), (44, 1), (60, 1)] }, { coefficient := 4, powers := [(5, 1), (30, 1), (44, 1), (60, 1)] }],
  [{ coefficient := 4, powers := [(5, 1), (25, 1), (29, 1), (44, 1), (60, 1)] }],
  [{ coefficient := 2, powers := [(5, 1), (26, 1), (44, 1), (60, 1), (65, 1)] }],
  [{ coefficient := -2, powers := [(9, 1), (13, 1), (25, 1), (54, 1), (65, 1)] }, { coefficient := 6, powers := [(13, 1), (25, 1), (50, 1), (54, 1), (65, 1)] }],
  [{ coefficient := -2, powers := [(3, 1), (55, 1), (60, 1)] }, { coefficient := -5, powers := [(9, 1), (25, 1), (34, 1), (37, 1), (47, 1), (54, 1), (55, 1), (65, 1)] }, { coefficient := -2, powers := [(37, 1), (55, 1), (60, 1)] }],
  [{ coefficient := -2, powers := [(3, 1), (49, 1), (60, 1)] }, { coefficient := -5, powers := [(9, 1), (25, 1), (34, 1), (37, 1), (47, 1), (49, 1), (54, 1), (65, 1)] }],
  [{ coefficient := 2, powers := [(5, 1), (55, 1), (60, 1)] }, { coefficient := 5, powers := [(9, 1), (19, 1), (25, 1), (34, 1), (39, 1), (53, 1), (54, 1), (65, 1)] }, { coefficient := -2, powers := [(12, 1), (39, 1), (60, 1)] }],
  [{ coefficient := -2, powers := [(3, 1), (30, 1), (60, 1)] }, { coefficient := -5, powers := [(6, 1), (9, 1), (25, 1), (29, 1), (34, 1), (54, 1), (58, 1), (65, 1)] }, { coefficient := 2, powers := [(6, 1), (30, 1), (60, 1)] }, { coefficient := -5, powers := [(9, 1), (25, 1), (30, 1), (34, 1), (37, 1), (47, 1), (54, 1), (65, 1)] }],
  [{ coefficient := -5, powers := [(5, 1), (9, 1), (25, 1), (34, 1), (47, 1), (54, 1), (58, 1), (65, 1)] }],
  [{ coefficient := -2, powers := [(3, 1), (24, 1), (60, 1)] }, { coefficient := -5, powers := [(9, 1), (24, 1), (25, 1), (34, 1), (37, 1), (47, 1), (54, 1), (65, 1)] }],
  [{ coefficient := 2, powers := [(5, 1), (25, 1), (30, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(9, 1), (25, 2), (44, 1), (47, 1), (54, 2), (65, 2)] }],
  [{ coefficient := 1, powers := [(9, 1), (25, 2), (44, 1), (47, 1), (52, 1), (54, 1), (65, 2)] }],
  [{ coefficient := 2, powers := [(5, 1), (30, 1), (60, 1)] }],
  [{ coefficient := 2, powers := [(41, 1), (65, 1)] }, { coefficient := 2, powers := [(46, 1), (65, 1)] }],
  [{ coefficient := 6, powers := [(13, 1), (25, 2), (26, 1), (47, 2), (54, 1), (65, 2)] }, { coefficient := 2, powers := [(13, 1), (25, 1), (26, 1), (44, 1), (47, 1), (54, 1), (65, 2)] }, { coefficient := -2, powers := [(25, 2), (26, 1), (43, 1), (47, 2), (54, 1), (65, 2)] }, { coefficient := -4, powers := [(25, 2), (26, 1), (44, 1), (45, 1), (47, 1), (54, 1), (65, 2)] }, { coefficient := -2, powers := [(25, 1), (26, 1), (34, 1), (37, 1), (47, 2), (54, 1), (65, 2)] }, { coefficient := -2, powers := [(25, 1), (26, 1), (43, 1), (44, 1), (47, 1), (54, 1), (65, 2)] }],
  [{ coefficient := 6, powers := [(13, 1), (25, 2), (44, 1), (47, 1), (50, 1), (54, 1), (65, 2)] }, { coefficient := 2, powers := [(13, 1), (25, 1), (44, 2), (50, 1), (54, 1), (65, 2)] }, { coefficient := -2, powers := [(25, 2), (43, 1), (44, 1), (47, 1), (50, 1), (54, 1), (65, 2)] }, { coefficient := -4, powers := [(25, 2), (44, 2), (45, 1), (50, 1), (54, 1), (65, 2)] }, { coefficient := -2, powers := [(25, 1), (34, 1), (37, 1), (44, 1), (47, 1), (50, 1), (54, 1), (65, 2)] }, { coefficient := 2, powers := [(25, 1), (40, 1), (41, 1), (44, 1), (62, 1), (65, 1)] }, { coefficient := 2, powers := [(25, 1), (40, 1), (47, 1), (62, 1), (65, 1)] }, { coefficient := -2, powers := [(25, 1), (43, 1), (44, 2), (50, 1), (54, 1), (65, 2)] }],
  [{ coefficient := -6, powers := [(13, 1), (25, 2), (26, 1), (46, 1), (47, 1), (54, 1), (65, 2)] }, { coefficient := -2, powers := [(13, 1), (25, 1), (26, 1), (44, 1), (46, 1), (54, 1), (65, 2)] }, { coefficient := 2, powers := [(13, 1), (25, 1), (54, 1), (65, 1)] }, { coefficient := 2, powers := [(20, 1), (25, 1), (45, 1), (54, 1), (65, 1)] }, { coefficient := 2, powers := [(25, 2), (26, 1), (43, 1), (46, 1), (47, 1), (54, 1), (65, 2)] }, { coefficient := 4, powers := [(25, 2), (26, 1), (44, 1), (45, 1), (46, 1), (54, 1), (65, 2)] }, { coefficient := 2, powers := [(25, 1), (26, 1), (34, 1), (37, 1), (46, 1), (47, 1), (54, 1), (65, 2)] }, { coefficient := 2, powers := [(25, 1), (26, 1), (43, 1), (44, 1), (46, 1), (54, 1), (65, 2)] }, { coefficient := -2, powers := [(25, 1), (43, 1), (54, 1), (65, 1)] }],
  [{ coefficient := -2, powers := [(5, 1), (30, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (9, 1), (25, 1), (34, 1), (54, 1), (65, 1)] }, { coefficient := -1, powers := [(3, 1), (13, 1), (25, 1), (31, 1), (54, 1), (65, 1)] }, { coefficient := -5, powers := [(6, 1), (9, 1), (12, 1), (25, 1), (26, 1), (29, 1), (34, 1), (49, 1), (54, 1), (65, 1)] }, { coefficient := 2, powers := [(6, 1), (13, 1), (25, 1), (31, 1), (54, 1), (65, 1)] }, { coefficient := -2, powers := [(6, 1), (25, 1), (34, 1), (40, 1), (54, 1), (65, 1)] }, { coefficient := -2, powers := [(9, 1), (13, 1), (20, 1), (25, 1), (54, 1), (65, 1)] }, { coefficient := 4, powers := [(9, 1), (13, 1), (25, 2), (54, 1), (65, 1)] }, { coefficient := -1, powers := [(9, 1), (25, 2), (26, 1), (43, 1), (47, 1), (54, 1), (65, 2)] }, { coefficient := 2, powers := [(9, 1), (25, 1), (34, 1), (37, 1), (54, 1), (65, 1)] }, { coefficient := 6, powers := [(13, 1), (20, 1), (25, 1), (50, 1), (54, 1), (65, 1)] }, { coefficient := 4, powers := [(13, 1), (25, 2), (40, 1), (54, 1), (65, 1)] }, { coefficient := 2, powers := [(13, 1), (25, 1), (31, 1), (37, 1), (54, 1), (65, 1)] }, { coefficient := -2, powers := [(25, 1), (26, 1), (41, 1), (65, 1)] }, { coefficient := -2, powers := [(25, 1), (26, 1), (46, 1), (65, 1)] }],
  [{ coefficient := 2, powers := [(5, 1), (9, 1), (28, 1), (60, 1), (62, 1)] }, { coefficient := 2, powers := [(5, 1), (23, 1), (60, 1)] }],
  [{ coefficient := -5, powers := [(9, 1), (19, 1), (25, 1), (34, 1), (39, 1), (54, 1), (65, 1)] }],
  [{ coefficient := 5, powers := [(5, 1), (9, 1), (25, 1), (34, 1), (54, 1), (58, 1), (65, 1)] }],
  [{ coefficient := 5, powers := [(6, 1), (9, 1), (12, 1), (25, 1), (26, 1), (34, 1), (49, 1), (54, 1), (65, 1)] }],
  [{ coefficient := 5, powers := [(6, 1), (9, 1), (12, 1), (25, 1), (34, 1), (49, 1), (54, 1), (65, 1)] }],
  [{ coefficient := 2, powers := [] }],
  [{ coefficient := -2, powers := [(25, 1), (46, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (25, 1), (47, 1), (54, 1), (65, 2)] }, { coefficient := -2, powers := [(25, 1), (41, 1), (46, 1), (62, 1), (65, 1)] }, { coefficient := -1, powers := [(25, 1), (44, 1), (45, 1), (54, 1), (65, 2)] }, { coefficient := -2, powers := [(25, 1), (46, 2), (62, 1), (65, 1)] }, { coefficient := -2, powers := [(25, 1), (46, 1), (52, 1), (62, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (25, 1), (31, 1), (44, 1), (54, 1), (65, 1)] }, { coefficient := -2, powers := [(6, 1), (25, 1), (31, 1), (44, 1), (54, 1), (65, 1)] }, { coefficient := -2, powers := [(25, 1), (31, 1), (37, 1), (44, 1), (54, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (25, 1), (47, 1), (54, 1), (65, 1)] }, { coefficient := -2, powers := [(25, 1), (47, 1), (50, 1), (54, 1), (65, 1)] }],
  [{ coefficient := -4, powers := [(13, 1), (25, 1), (47, 1), (54, 1), (65, 1)] }, { coefficient := 2, powers := [(25, 1), (44, 1), (45, 1), (54, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (25, 2), (43, 1), (47, 1), (54, 1), (65, 2)] }, { coefficient := -6, powers := [(13, 1), (25, 2), (47, 1), (50, 1), (54, 1), (65, 2)] }, { coefficient := -2, powers := [(13, 1), (25, 1), (44, 1), (50, 1), (54, 1), (65, 2)] }, { coefficient := 2, powers := [(25, 2), (43, 1), (47, 1), (50, 1), (54, 1), (65, 2)] }, { coefficient := 4, powers := [(25, 2), (44, 1), (45, 1), (50, 1), (54, 1), (65, 2)] }, { coefficient := 2, powers := [(25, 1), (34, 1), (37, 1), (47, 1), (50, 1), (54, 1), (65, 2)] }, { coefficient := 2, powers := [(25, 1), (43, 1), (44, 1), (50, 1), (54, 1), (65, 2)] }, { coefficient := 2, powers := [(25, 1), (46, 1), (65, 1)] }],
  [{ coefficient := -2, powers := [(20, 1), (25, 1), (47, 1), (54, 1), (65, 1)] }],
  [{ coefficient := 2, powers := [(39, 1), (60, 1)] }],
  [{ coefficient := -2, powers := [(5, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (9, 1), (25, 1), (34, 1), (44, 1), (54, 1), (65, 1)] }, { coefficient := 2, powers := [(3, 1), (25, 1), (31, 1), (46, 1), (62, 1)] }, { coefficient := -2, powers := [(6, 1), (9, 1), (25, 1), (34, 1), (44, 1), (54, 1), (65, 1)] }, { coefficient := 2, powers := [(9, 1), (20, 1), (25, 1), (46, 1), (62, 1)] }, { coefficient := -2, powers := [(9, 1), (25, 1), (34, 1), (37, 1), (44, 1), (54, 1), (65, 1)] }, { coefficient := -2, powers := [(20, 1)] }],
  [{ coefficient := 2, powers := [(25, 1), (47, 1), (54, 1), (65, 1)] }],
  [{ coefficient := 2, powers := [(3, 1), (60, 1)] }, { coefficient := 5, powers := [(9, 1), (25, 1), (34, 1), (37, 1), (47, 1), (54, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (9, 1), (25, 1), (34, 1), (38, 1), (44, 1), (54, 1), (60, 1), (65, 1)] }, { coefficient := -1, powers := [(3, 1), (9, 1), (25, 1), (34, 1), (41, 1), (44, 1), (54, 1), (57, 1), (65, 1)] }, { coefficient := -1, powers := [(3, 1), (9, 1), (25, 1), (34, 1), (44, 1), (46, 1), (52, 1), (54, 1), (65, 1)] }, { coefficient := 1, powers := [(3, 1), (9, 1), (25, 1), (34, 1), (47, 1), (52, 1), (54, 1), (65, 1)] }, { coefficient := 1, powers := [(3, 1), (13, 1), (25, 1), (31, 1), (47, 1), (52, 1), (54, 1), (65, 1)] }, { coefficient := -2, powers := [(3, 1), (25, 1), (31, 1), (38, 1), (46, 1), (60, 1), (62, 1)] }, { coefficient := -2, powers := [(3, 1), (25, 1), (31, 1), (41, 1), (46, 1), (57, 1), (62, 1)] }, { coefficient := -1, powers := [(3, 1), (25, 1), (31, 1), (44, 1), (45, 1), (52, 1), (54, 1), (65, 1)] }, { coefficient := -2, powers := [(3, 1), (25, 1), (31, 1), (46, 2), (52, 1), (62, 1)] }, { coefficient := -2, powers := [(5, 1), (9, 1), (28, 1), (47, 1), (55, 1), (60, 1), (62, 1)] }, { coefficient := -2, powers := [(5, 1), (23, 1), (47, 1), (55, 1), (60, 1)] }, { coefficient := -4, powers := [(5, 1), (25, 1), (29, 1), (44, 1), (46, 1), (55, 1), (60, 1)] }, { coefficient := -2, powers := [(5, 1), (25, 1), (30, 1), (38, 1), (60, 1), (61, 1)] }, { coefficient := -2, powers := [(5, 1), (25, 1), (30, 1), (47, 1), (53, 1), (60, 1)] }, { coefficient := 4, powers := [(5, 1), (26, 1), (29, 1), (44, 1), (46, 1), (51, 1), (60, 1)] }, { coefficient := -4, powers := [(5, 1), (30, 1), (44, 1), (46, 1), (51, 1), (60, 1)] }, { coefficient := 2, powers := [(5, 1), (30, 1), (47, 1), (51, 1), (60, 1)] }, { coefficient := 5, powers := [(6, 1), (9, 1), (12, 1), (25, 1), (26, 1), (29, 1), (34, 1), (47, 1), (49, 1), (52, 1), (54, 1), (65, 1)] }, { coefficient := 2, powers := [(6, 1), (9, 1), (25, 1), (34, 1), (38, 1), (44, 1), (54, 1), (60, 1), (65, 1)] }, { coefficient := 2, powers := [(6, 1), (9, 1), (25, 1), (34, 1), (41, 1), (44, 1), (54, 1), (57, 1), (65, 1)] }, { coefficient := 2, powers := [(6, 1), (9, 1), (25, 1), (34, 1), (44, 1), (46, 1), (52, 1), (54, 1), (65, 1)] }, { coefficient := -2, powers := [(6, 1), (13, 1), (25, 1), (31, 1), (47, 1), (52, 1), (54, 1), (65, 1)] }, { coefficient := 2, powers := [(6, 1), (25, 1), (31, 1), (44, 1), (45, 1), (52, 1), (54, 1), (65, 1)] }, { coefficient := 2, powers := [(6, 1), (25, 1), (34, 1), (40, 1), (47, 1), (52, 1), (54, 1), (65, 1)] }, { coefficient := 2, powers := [(9, 1), (13, 1), (20, 1), (25, 1), (47, 1), (52, 1), (54, 1), (65, 1)] }, { coefficient := -4, powers := [(9, 1), (13, 1), (25, 2), (47, 1), (52, 1), (54, 1), (65, 1)] }, { coefficient := -2, powers := [(9, 1), (13, 1), (25, 1), (41, 1), (44, 1), (54, 1), (65, 1)] }, { coefficient := -2, powers := [(9, 1), (13, 1), (25, 1), (44, 1), (52, 1), (54, 1), (65, 1)] }, { coefficient := 2, powers := [(9, 1), (13, 1), (25, 1), (47, 1), (54, 1), (65, 1)] }, { coefficient := -2, powers := [(9, 1), (20, 1), (25, 1), (38, 1), (46, 1), (60, 1), (62, 1)] }, { coefficient := -2, powers := [(9, 1), (20, 1), (25, 1), (41, 1), (46, 1), (57, 1), (62, 1)] }, { coefficient := -2, powers := [(9, 1), (20, 1), (25, 1), (46, 2), (52, 1), (62, 1)] }, { coefficient := 1, powers := [(9, 1), (25, 2), (26, 1), (43, 1), (47, 2), (52, 1), (54, 1), (65, 2)] }, { coefficient := -1, powers := [(9, 1), (25, 2), (41, 1), (43, 1), (47, 1), (54, 1), (58, 1), (65, 2)] }, { coefficient := -1, powers := [(9, 1), (25, 2), (43, 1), (47, 2), (54, 2), (65, 2)] }, { coefficient := 2, powers := [(9, 1), (25, 1), (34, 1), (37, 1), (38, 1), (44, 1), (54, 1), (60, 1), (65, 1)] }, { coefficient := 2, powers := [(9, 1), (25, 1), (34, 1), (37, 1), (41, 1), (44, 1), (54, 1), (57, 1), (65, 1)] }, { coefficient := 2, powers := [(9, 1), (25, 1), (34, 1), (37, 1), (44, 1), (46, 1), (52, 1), (54, 1), (65, 1)] }, { coefficient := -2, powers := [(9, 1), (25, 1), (34, 1), (37, 1), (47, 1), (52, 1), (54, 1), (65, 1)] }, { coefficient := -1, powers := [(9, 1), (25, 1), (43, 1), (47, 1), (54, 1), (65, 1)] }, { coefficient := -1, powers := [(9, 1), (25, 1), (44, 1), (45, 1), (54, 1), (65, 1)] }, { coefficient := -6, powers := [(13, 1), (20, 1), (25, 1), (47, 1), (50, 1), (52, 1), (54, 1), (65, 1)] }, { coefficient := -4, powers := [(13, 1), (25, 2), (40, 1), (47, 1), (52, 1), (54, 1), (65, 1)] }, { coefficient := 6, powers := [(13, 1), (25, 2), (41, 1), (47, 1), (50, 1), (54, 1), (58, 1), (65, 2)] }, { coefficient := -6, powers := [(13, 1), (25, 2), (44, 1), (46, 1), (47, 1), (50, 1), (54, 2), (65, 2)] }, { coefficient := 6, powers := [(13, 1), (25, 2), (47, 2), (50, 1), (54, 2), (65, 2)] }, { coefficient := -2, powers := [(13, 1), (25, 1), (31, 1), (37, 1), (47, 1), (52, 1), (54, 1), (65, 1)] }, { coefficient := -1, powers := [(13, 1), (25, 1), (40, 1), (47, 1), (54, 1), (58, 1), (65, 2)] }, { coefficient := 2, powers := [(13, 1), (25, 1), (41, 1), (44, 1), (50, 1), (54, 1), (58, 1), (65, 2)] }, { coefficient := 6, powers := [(13, 1), (25, 1), (41, 1), (44, 1), (50, 1), (54, 1), (65, 1)] }, { coefficient := -2, powers := [(13, 1), (25, 1), (44, 2), (46, 1), (50, 1), (54, 2), (65, 2)] }, { coefficient := 2, powers := [(13, 1), (25, 1), (44, 1), (47, 1), (50, 1), (54, 2), (65, 2)] }, { coefficient := 6, powers := [(13, 1), (25, 1), (44, 1), (50, 1), (52, 1), (54, 1), (65, 1)] }, { coefficient := -4, powers := [(13, 1), (25, 1), (47, 1), (50, 1), (54, 1), (65, 1)] }, { coefficient := 2, powers := [(20, 1), (38, 1), (60, 1)] }, { coefficient := 2, powers := [(20, 1), (41, 1), (57, 1)] }, { coefficient := 2, powers := [(20, 1), (46, 1), (52, 1)] }, { coefficient := -2, powers := [(25, 2), (41, 1), (43, 1), (47, 1), (50, 1), (54, 1), (58, 1), (65, 2)] }, { coefficient := -4, powers := [(25, 2), (41, 1), (44, 1), (45, 1), (50, 1), (54, 1), (58, 1), (65, 2)] }, { coefficient := 2, powers := [(25, 2), (43, 1), (44, 1), (46, 1), (47, 1), (50, 1), (54, 2), (65, 2)] }, { coefficient := -2, powers := [(25, 2), (43, 1), (47, 2), (50, 1), (54, 2), (65, 2)] }, { coefficient := 4, powers := [(25, 2), (44, 2), (45, 1), (46, 1), (50, 1), (54, 2), (65, 2)] }, { coefficient := -4, powers := [(25, 2), (44, 1), (45, 1), (47, 1), (50, 1), (54, 2), (65, 2)] }, { coefficient := 2, powers := [(25, 1), (26, 1), (41, 1), (47, 1), (52, 1), (65, 1)] }, { coefficient := 2, powers := [(25, 1), (26, 1), (46, 1), (47, 1), (52, 1), (65, 1)] }, { coefficient := 2, powers := [(25, 1), (31, 1), (37, 1), (44, 1), (45, 1), (52, 1), (54, 1), (65, 1)] }, { coefficient := -2, powers := [(25, 1), (34, 1), (37, 1), (41, 1), (47, 1), (50, 1), (54, 1), (58, 1), (65, 2)] }, { coefficient := 2, powers := [(25, 1), (34, 1), (37, 1), (44, 1), (46, 1), (47, 1), (50, 1), (54, 2), (65, 2)] }, { coefficient := -2, powers := [(25, 1), (34, 1), (37, 1), (47, 2), (50, 1), (54, 2), (65, 2)] }, { coefficient := -2, powers := [(25, 1), (37, 1), (47, 1), (54, 1), (59, 1), (65, 1)] }, { coefficient := -2, powers := [(25, 1), (40, 1), (41, 1), (44, 1), (46, 1), (54, 1), (62, 1), (65, 1)] }, { coefficient := 2, powers := [(25, 1), (40, 1), (41, 1), (46, 1), (58, 1), (62, 1), (65, 1)] }, { coefficient := 1, powers := [(25, 1), (40, 1), (44, 1), (45, 1), (54, 1), (58, 1), (65, 2)] }, { coefficient := 2, powers := [(25, 1), (40, 1), (46, 2), (58, 1), (62, 1), (65, 1)] }, { coefficient := -2, powers := [(25, 1), (40, 1), (46, 1), (47, 1), (54, 1), (62, 1), (65, 1)] }, { coefficient := 2, powers := [(25, 1), (40, 1), (46, 1), (52, 1), (58, 1), (62, 1), (65, 1)] }, { coefficient := 2, powers := [(25, 1), (40, 1), (46, 1), (57, 1), (62, 1)] }, { coefficient := -2, powers := [(25, 1), (40, 1), (47, 1), (54, 1), (56, 1), (65, 1)] }, { coefficient := -2, powers := [(25, 1), (41, 1), (43, 1), (44, 1), (50, 1), (54, 1), (58, 1), (65, 2)] }, { coefficient := -2, powers := [(25, 1), (41, 1), (46, 1), (58, 1), (65, 1)] }, { coefficient := 2, powers := [(25, 1), (43, 1), (44, 2), (46, 1), (50, 1), (54, 2), (65, 2)] }, { coefficient := -2, powers := [(25, 1), (43, 1), (44, 1), (47, 1), (50, 1), (54, 2), (65, 2)] }, { coefficient := 2, powers := [(25, 1), (43, 1), (47, 1), (50, 1), (54, 1), (65, 1)] }, { coefficient := 2, powers := [(25, 1), (44, 1), (45, 1), (50, 1), (54, 1), (65, 1)] }, { coefficient := -2, powers := [(25, 1), (46, 1), (47, 1), (54, 1), (65, 1)] }, { coefficient := -2, powers := [(52, 1)] }],
  [{ coefficient := -2, powers := [(3, 1), (39, 1), (60, 1), (61, 1)] }, { coefficient := 2, powers := [(3, 1), (49, 1), (55, 1), (60, 1)] }, { coefficient := -5, powers := [(9, 1), (25, 1), (34, 1), (37, 1), (39, 1), (47, 1), (54, 1), (61, 1), (65, 1)] }, { coefficient := 5, powers := [(9, 1), (25, 1), (34, 1), (37, 1), (47, 1), (49, 1), (54, 1), (55, 1), (65, 1)] }, { coefficient := -2, powers := [(37, 1), (39, 1), (60, 1), (61, 1)] }, { coefficient := 2, powers := [(37, 1), (49, 1), (55, 1), (60, 1)] }, { coefficient := -2, powers := [(39, 1), (44, 1), (51, 1), (60, 1)] }],
  [{ coefficient := -5, powers := [(3, 1), (9, 1), (19, 1), (25, 1), (29, 1), (34, 1), (39, 1), (54, 1), (61, 1), (65, 1)] }, { coefficient := -2, powers := [(3, 1), (12, 1), (30, 1), (49, 1), (60, 1)] }, { coefficient := 2, powers := [(3, 1), (18, 1), (24, 1), (44, 1), (55, 1), (60, 1)] }, { coefficient := 2, powers := [(3, 1), (18, 1), (30, 1), (49, 1), (51, 1), (60, 1)] }, { coefficient := -2, powers := [(3, 1), (19, 1), (21, 1), (30, 1), (53, 1), (60, 1)] }, { coefficient := 2, powers := [(3, 1), (19, 1), (24, 1), (26, 1), (53, 1), (60, 1)] }, { coefficient := -2, powers := [(3, 1), (19, 1), (24, 1), (55, 1), (60, 1)] }, { coefficient := 2, powers := [(3, 1), (19, 1), (33, 1), (39, 1), (60, 1)] }, { coefficient := 2, powers := [(5, 1), (28, 1), (44, 1), (55, 1), (60, 1)] }, { coefficient := 5, powers := [(6, 1), (9, 1), (12, 1), (25, 1), (26, 1), (34, 1), (36, 1), (38, 1), (49, 1), (54, 1), (65, 1)] }, { coefficient := -5, powers := [(6, 1), (9, 1), (12, 1), (25, 1), (30, 1), (34, 1), (44, 1), (46, 1), (49, 1), (54, 1), (65, 1)] }, { coefficient := 5, powers := [(6, 1), (9, 1), (12, 1), (25, 1), (30, 1), (34, 1), (47, 1), (49, 1), (54, 1), (65, 1)] }, { coefficient := -5, powers := [(6, 1), (9, 1), (19, 1), (21, 1), (25, 1), (29, 1), (34, 1), (53, 1), (54, 1), (58, 1), (65, 1)] }, { coefficient := 2, powers := [(6, 1), (12, 1), (30, 1), (49, 1), (60, 1)] }, { coefficient := 2, powers := [(6, 1), (19, 1), (21, 1), (30, 1), (53, 1), (60, 1)] }, { coefficient := 5, powers := [(9, 1), (18, 1), (24, 1), (25, 1), (34, 1), (37, 1), (44, 1), (47, 1), (54, 1), (55, 1), (65, 1)] }, { coefficient := 5, powers := [(9, 1), (18, 1), (25, 1), (30, 1), (34, 1), (37, 1), (47, 1), (49, 1), (51, 1), (54, 1), (65, 1)] }, { coefficient := -5, powers := [(9, 1), (19, 1), (21, 1), (25, 1), (30, 1), (34, 1), (37, 1), (47, 1), (53, 1), (54, 1), (65, 1)] }, { coefficient := 5, powers := [(9, 1), (19, 1), (24, 1), (25, 1), (26, 1), (34, 1), (37, 1), (47, 1), (53, 1), (54, 1), (65, 1)] }, { coefficient := -5, powers := [(9, 1), (19, 1), (24, 1), (25, 1), (34, 1), (37, 1), (47, 1), (54, 1), (55, 1), (65, 1)] }, { coefficient := 5, powers := [(9, 1), (19, 1), (25, 1), (30, 1), (34, 1), (37, 1), (49, 1), (53, 1), (54, 1), (65, 1)] }, { coefficient := 5, powers := [(9, 1), (19, 1), (25, 1), (33, 1), (34, 1), (37, 1), (39, 1), (47, 1), (54, 1), (65, 1)] }, { coefficient := 2, powers := [(18, 1), (24, 1), (37, 1), (44, 1), (55, 1), (60, 1)] }, { coefficient := 2, powers := [(19, 1), (20, 1), (23, 1), (39, 1), (53, 1), (60, 1)] }, { coefficient := 2, powers := [(19, 1), (23, 1), (39, 1), (51, 1), (60, 1)] }, { coefficient := -2, powers := [(19, 1), (24, 1), (37, 1), (55, 1), (60, 1)] }, { coefficient := 2, powers := [(19, 1), (33, 1), (37, 1), (39, 1), (60, 1)] }, { coefficient := -2, powers := [(25, 1), (26, 1), (41, 2), (44, 1), (65, 1)] }, { coefficient := -2, powers := [(25, 1), (26, 1), (41, 1), (47, 1), (65, 1)] }, { coefficient := -2, powers := [(25, 1), (41, 1), (44, 1), (54, 1), (65, 1)] }, { coefficient := 2, powers := [(25, 1), (46, 1)] }, { coefficient := -2, powers := [(25, 1), (47, 1), (54, 1), (65, 1)] }],
  [{ coefficient := -2, powers := [(2, 1), (3, 1), (58, 1), (60, 1)] }, { coefficient := -5, powers := [(2, 1), (9, 1), (25, 1), (34, 1), (37, 1), (47, 1), (54, 1), (58, 1), (65, 1)] }, { coefficient := -2, powers := [(3, 1), (8, 1), (36, 1), (60, 1)] }, { coefficient := 5, powers := [(6, 1), (9, 1), (19, 1), (25, 1), (29, 1), (34, 1), (54, 1), (58, 1), (65, 1)] }, { coefficient := -2, powers := [(6, 1), (19, 1), (30, 1), (60, 1)] }, { coefficient := -5, powers := [(8, 1), (9, 1), (25, 1), (34, 1), (36, 1), (37, 1), (47, 1), (54, 1), (65, 1)] }],
  [{ coefficient := -2, powers := [(3, 1), (25, 1), (31, 1), (47, 1), (54, 1), (65, 1)] }, { coefficient := -1, powers := [(9, 1), (20, 1), (25, 1), (47, 1), (54, 1), (65, 1)] }, { coefficient := 2, powers := [(20, 1), (25, 1), (47, 1), (50, 1), (54, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (13, 1), (25, 1), (31, 1), (47, 1), (54, 1), (65, 1)] }, { coefficient := 2, powers := [(3, 1), (25, 1), (31, 1), (41, 1), (46, 1), (62, 1)] }, { coefficient := 1, powers := [(3, 1), (25, 1), (31, 1), (44, 1), (45, 1), (54, 1), (65, 1)] }, { coefficient := 2, powers := [(3, 1), (25, 1), (31, 1), (46, 2), (62, 1)] }, { coefficient := 2, powers := [(3, 1), (25, 1), (31, 1), (46, 1), (52, 1), (62, 1)] }, { coefficient := -2, powers := [(5, 1), (26, 1), (29, 1), (44, 1), (51, 1), (60, 1)] }, { coefficient := -1, powers := [(9, 1), (13, 1), (20, 1), (25, 1), (47, 1), (54, 1), (65, 1)] }, { coefficient := 2, powers := [(9, 1), (20, 1), (25, 1), (41, 1), (46, 1), (62, 1)] }, { coefficient := 1, powers := [(9, 1), (20, 1), (25, 1), (44, 1), (45, 1), (54, 1), (65, 1)] }, { coefficient := 2, powers := [(9, 1), (20, 1), (25, 1), (46, 2), (62, 1)] }, { coefficient := 2, powers := [(9, 1), (20, 1), (25, 1), (46, 1), (52, 1), (62, 1)] }, { coefficient := -1, powers := [(9, 1), (25, 2), (43, 1), (47, 1), (54, 1), (65, 1)] }, { coefficient := 1, powers := [(9, 1), (25, 2), (44, 1), (45, 1), (54, 1), (65, 1)] }, { coefficient := -2, powers := [(9, 1), (25, 1), (46, 1), (62, 1)] }, { coefficient := 6, powers := [(13, 1), (25, 2), (47, 1), (50, 1), (54, 1), (65, 1)] }, { coefficient := 2, powers := [(13, 1), (25, 1), (44, 1), (50, 1), (54, 1), (65, 1)] }, { coefficient := -2, powers := [(20, 1), (41, 1)] }, { coefficient := -2, powers := [(20, 1), (46, 1)] }, { coefficient := -2, powers := [(25, 2), (43, 1), (47, 1), (50, 1), (54, 1), (65, 1)] }, { coefficient := -4, powers := [(25, 2), (44, 1), (45, 1), (50, 1), (54, 1), (65, 1)] }, { coefficient := -2, powers := [(25, 1), (34, 1), (37, 1), (47, 1), (50, 1), (54, 1), (65, 1)] }, { coefficient := -2, powers := [(25, 1), (43, 1), (44, 1), (50, 1), (54, 1), (65, 1)] }, { coefficient := -2, powers := [(25, 1), (46, 1)] }]
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
    (values : Fin 66 → R) :
    ¬ ∀ index : Fin 68,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((2 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (2 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (2 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component37.SelectedLeafB0_6_3.selectedHasNoCommonZero

end Krenn.Component37.SelectedLeafB0_6_3
