import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component37.SelectedLeafB0_2_2_5

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "977f401d76bdaa5a24e1d8471e79d7443825bd255512eaf8c6c8f448a65c884f"
def certificateSHA256 : String := "3cd10ce1dadf212bd67f7c843c0ab2d011a9d592040eb10b6979e3b5ba777766"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 64 → Fin 670 := ![
  20,
  151,
  167,
  168,
  175,
  177,
  178,
  179,
  180,
  181,
  183,
  256,
  257,
  279,
  280,
  285,
  295,
  297,
  301,
  307,
  310,
  311,
  312,
  315,
  316,
  317,
  340,
  342,
  410,
  411,
  412,
  430,
  431,
  433,
  434,
  436,
  438,
  446,
  450,
  453,
  472,
  475,
  479,
  482,
  487,
  497,
  566,
  570,
  602,
  603,
  612,
  645,
  655,
  657,
  658,
  660,
  661,
  662,
  663,
  664,
  665,
  666,
  667,
  669
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 64 → SparsePoly (Fin 66) := ![
  [{ coefficient := 1, powers := [(19, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (30, 1)] }, { coefficient := 1, powers := [(30, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (25, 1)] }, { coefficient := 1, powers := [(18, 1), (20, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (26, 1)] }, { coefficient := 1, powers := [(18, 1), (20, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (20, 1)] }, { coefficient := 1, powers := [(18, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (49, 1)] }, { coefficient := 1, powers := [(19, 1), (21, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (47, 1)] }, { coefficient := -1, powers := [(29, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (55, 1)] }, { coefficient := 1, powers := [(30, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (44, 1)] }, { coefficient := 1, powers := [(28, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (54, 1)] }, { coefficient := 1, powers := [(30, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(28, 1), (53, 1)] }, { coefficient := -1, powers := [(29, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (25, 1), (46, 1)] }, { coefficient := 1, powers := [(18, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (25, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (25, 1), (44, 1)] }, { coefficient := 1, powers := [(19, 1), (20, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (25, 1), (49, 1)] }, { coefficient := 1, powers := [(19, 1), (21, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(29, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (49, 1)] }, { coefficient := 1, powers := [(21, 1), (44, 1)] }, { coefficient := 1, powers := [(25, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (55, 1)] }, { coefficient := 1, powers := [(20, 1), (55, 1)] }, { coefficient := 1, powers := [(26, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (59, 1)] }, { coefficient := 1, powers := [(9, 1), (43, 1)] }, { coefficient := 1, powers := [(13, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (46, 1)] }, { coefficient := 1, powers := [(12, 1), (57, 1)] }, { coefficient := 1, powers := [(18, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (41, 1)] }, { coefficient := 1, powers := [(19, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (52, 1)] }, { coefficient := 1, powers := [(24, 1), (57, 1)] }, { coefficient := 1, powers := [(29, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (54, 1)] }, { coefficient := 1, powers := [(30, 1), (41, 1)] }, { coefficient := 1, powers := [(30, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1), (51, 1)] }, { coefficient := 1, powers := [(25, 1), (46, 1), (51, 1)] }, { coefficient := 1, powers := [(51, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1), (55, 1)] }, { coefficient := 1, powers := [(26, 1), (46, 1), (51, 1)] }, { coefficient := 1, powers := [(55, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (49, 1), (52, 1)] }, { coefficient := 1, powers := [(21, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(49, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (44, 1)] }, { coefficient := 1, powers := [(19, 1), (23, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (46, 1), (51, 1)] }, { coefficient := 1, powers := [(12, 1), (28, 1), (46, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (25, 1), (41, 1)] }, { coefficient := 1, powers := [(18, 1), (25, 1), (46, 1)] }, { coefficient := 1, powers := [(18, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (25, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (25, 1), (41, 1)] }, { coefficient := 1, powers := [(19, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (20, 1), (50, 1)] }, { coefficient := 1, powers := [(19, 1), (25, 1), (40, 1)] }, { coefficient := 1, powers := [(19, 1), (31, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (46, 1)] }, { coefficient := 1, powers := [(18, 1), (28, 1), (41, 1)] }, { coefficient := 1, powers := [(18, 1), (28, 1), (46, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (47, 1)] }, { coefficient := 1, powers := [(18, 1), (28, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (28, 1), (41, 1)] }, { coefficient := 1, powers := [(19, 1), (29, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (49, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1)] }, { coefficient := 1, powers := [(18, 1), (28, 1), (49, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (51, 1)] }, { coefficient := 1, powers := [(12, 1), (28, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (51, 1)] }, { coefficient := 1, powers := [(18, 1), (33, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (53, 1)] }, { coefficient := 1, powers := [(12, 1), (23, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1), (29, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1)] }, { coefficient := 1, powers := [(12, 1), (30, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (61, 1)] }, { coefficient := 1, powers := [(12, 1), (49, 1)] }, { coefficient := 1, powers := [(19, 1), (21, 1), (53, 1)] }, { coefficient := 1, powers := [(19, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (61, 1)] }, { coefficient := 1, powers := [(12, 1), (26, 1), (47, 1)] }, { coefficient := 1, powers := [(12, 1), (58, 1)] }, { coefficient := 1, powers := [(19, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (41, 1)] }, { coefficient := 1, powers := [(18, 1), (46, 1)] }, { coefficient := 1, powers := [(18, 1), (52, 1)] }, { coefficient := 1, powers := [(18, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1), (54, 1)] }, { coefficient := 1, powers := [(26, 1), (41, 1)] }, { coefficient := 1, powers := [(26, 1), (46, 1)] }, { coefficient := 1, powers := [(54, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1), (52, 1)] }, { coefficient := 1, powers := [(41, 1), (44, 1)] }, { coefficient := 1, powers := [(44, 1), (52, 1)] }, { coefficient := 1, powers := [(47, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (48, 1), (52, 1)] }, { coefficient := 1, powers := [(21, 1), (52, 1)] }, { coefficient := 1, powers := [(21, 1), (57, 1)] }, { coefficient := 1, powers := [(48, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (49, 1), (53, 1)] }, { coefficient := 1, powers := [(21, 1), (44, 1), (53, 1)] }, { coefficient := 1, powers := [(42, 1), (44, 1)] }, { coefficient := 1, powers := [(49, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (37, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1)] }, { coefficient := 1, powers := [(18, 1), (28, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (49, 1), (52, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1), (52, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (49, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (44, 1), (54, 1)] }, { coefficient := 1, powers := [(24, 1), (58, 1)] }, { coefficient := 1, powers := [(30, 1), (49, 1)] }, { coefficient := 1, powers := [(36, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (44, 1), (54, 1)] }, { coefficient := 1, powers := [(29, 1), (58, 1)] }, { coefficient := 1, powers := [(30, 1), (41, 1), (44, 1)] }, { coefficient := 1, powers := [(30, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1)] }, { coefficient := 1, powers := [(3, 1), (34, 1)] }, { coefficient := 1, powers := [(13, 1), (20, 1)] }, { coefficient := 1, powers := [(20, 1), (56, 1)] }, { coefficient := 1, powers := [(25, 1), (43, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (50, 1)] }, { coefficient := 1, powers := [(6, 1), (31, 1)] }, { coefficient := 1, powers := [(9, 1), (25, 1)] }, { coefficient := 1, powers := [(20, 1), (50, 1)] }, { coefficient := 1, powers := [(25, 1), (40, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1), (50, 1)] }, { coefficient := 1, powers := [(6, 1), (31, 1), (45, 1)] }, { coefficient := 1, powers := [(6, 1), (59, 1)] }, { coefficient := 1, powers := [(9, 1), (25, 1), (45, 1)] }, { coefficient := 1, powers := [(9, 1), (56, 1)] }, { coefficient := 1, powers := [(13, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (38, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (41, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(41, 1)] }, { coefficient := 1, powers := [(46, 1)] }, { coefficient := 1, powers := [(52, 1)] }, { coefficient := 1, powers := [(57, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (37, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (40, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (43, 1), (50, 1)] }, { coefficient := 1, powers := [(3, 1), (25, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (31, 1), (56, 1)] }, { coefficient := 1, powers := [(3, 1), (34, 1), (50, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (31, 1), (43, 1)] }, { coefficient := 1, powers := [(6, 1), (34, 1), (40, 1)] }, { coefficient := 1, powers := [(9, 1), (20, 1), (56, 1)] }, { coefficient := 1, powers := [(9, 1), (25, 1), (43, 1)] }, { coefficient := 1, powers := [(9, 1), (34, 1), (37, 1)] }, { coefficient := 1, powers := [(13, 1), (20, 1), (50, 1)] }, { coefficient := 1, powers := [(13, 1), (25, 1), (40, 1)] }, { coefficient := 1, powers := [(13, 1), (31, 1), (37, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (39, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (42, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (49, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (49, 1)] }, { coefficient := 1, powers := [(8, 1), (36, 1), (42, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (58, 1)] }, { coefficient := 1, powers := [(12, 1), (30, 1), (49, 1)] }, { coefficient := 1, powers := [(12, 1), (36, 1), (39, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (55, 1)] }, { coefficient := 1, powers := [(19, 1), (30, 1), (42, 1)] }, { coefficient := 1, powers := [(19, 1), (33, 1), (39, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1)] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(40, 1)] }],
  [{ coefficient := 1, powers := [(41, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(42, 1)] }],
  [{ coefficient := 1, powers := [(56, 1)] }],
  [{ coefficient := 1, powers := [(57, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(58, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (64, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(30, 1), (65, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 64 → SparsePoly (Fin 66) := ![
  [{ coefficient := -2, powers := [(13, 1), (20, 1), (33, 1), (39, 1)] }, { coefficient := -1, powers := [(25, 1), (33, 1), (39, 1), (43, 1)] }, { coefficient := -1, powers := [(33, 1), (34, 1), (37, 1), (39, 1)] }],
  [{ coefficient := -1, powers := [(19, 1), (25, 1), (33, 1), (39, 1), (43, 1), (65, 1)] }, { coefficient := 1, powers := [(19, 1), (33, 1), (34, 1), (37, 1), (39, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(26, 1), (29, 1), (49, 1), (64, 1)] }, { coefficient := 1, powers := [(30, 1), (41, 1), (49, 1)] }, { coefficient := 1, powers := [(30, 1), (46, 1), (49, 1)] }, { coefficient := -1, powers := [(30, 1), (49, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(29, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (41, 1), (44, 1), (55, 1)] }, { coefficient := 1, powers := [(24, 1), (44, 1), (46, 1), (55, 1)] }, { coefficient := -1, powers := [(26, 1), (29, 1), (49, 1), (51, 1), (64, 1)] }, { coefficient := -1, powers := [(29, 1), (49, 1), (55, 1)] }, { coefficient := -1, powers := [(30, 1), (41, 1), (49, 1), (51, 1)] }, { coefficient := -1, powers := [(30, 1), (46, 1), (49, 1), (51, 1)] }, { coefficient := 1, powers := [(30, 1), (49, 1), (51, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(28, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(18, 1), (48, 1), (55, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(18, 1), (49, 1)] }],
  [{ coefficient := -2, powers := [(18, 1), (20, 1), (41, 1), (55, 1)] }, { coefficient := -2, powers := [(18, 1), (20, 1), (46, 1), (55, 1)] }, { coefficient := -1, powers := [(18, 1), (20, 1), (55, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (44, 1)] }],
  [{ coefficient := -1, powers := [(18, 1), (26, 1), (41, 1), (49, 1), (63, 1)] }, { coefficient := -1, powers := [(18, 1), (26, 1), (49, 1), (52, 1), (63, 1)] }, { coefficient := -1, powers := [(18, 1), (26, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (49, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(24, 1), (26, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(24, 1), (41, 1), (55, 1)] }, { coefficient := -1, powers := [(24, 1), (46, 1), (55, 1)] }, { coefficient := 1, powers := [(29, 1), (48, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (55, 1)] }, { coefficient := -1, powers := [(30, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(18, 1), (20, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (30, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (29, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (25, 1), (33, 1), (39, 1)] }],
  [{ coefficient := -1, powers := [(23, 1), (25, 1), (49, 1), (54, 1)] }, { coefficient := 1, powers := [(26, 1), (28, 1), (41, 1), (49, 1), (63, 1)] }, { coefficient := 1, powers := [(26, 1), (28, 1), (49, 1), (52, 1), (63, 1)] }, { coefficient := 1, powers := [(26, 1), (28, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (28, 1), (55, 1)] }, { coefficient := 1, powers := [(23, 1), (25, 1), (48, 1), (55, 1)] }, { coefficient := 1, powers := [(23, 1), (48, 1), (55, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(19, 1), (20, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (21, 1), (30, 1), (44, 1), (65, 1)] }, { coefficient := -1, powers := [(12, 1), (25, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (24, 1), (26, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(19, 1), (24, 1), (25, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (30, 1)] }],
  [{ coefficient := -1, powers := [(25, 1), (48, 1), (55, 1)] }, { coefficient := -1, powers := [(48, 1), (55, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(26, 1), (41, 1), (49, 1), (63, 1)] }, { coefficient := -1, powers := [(26, 1), (49, 1), (52, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(30, 1), (49, 1), (51, 1)] }],
  [{ coefficient := -1, powers := [(23, 1), (48, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (33, 1), (39, 1)] }, { coefficient := 1, powers := [(20, 1), (33, 1), (39, 1), (45, 1)] }, { coefficient := -1, powers := [(33, 1), (39, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (49, 1), (55, 1)] }, { coefficient := -1, powers := [(26, 1), (49, 1), (51, 1)] }],
  [{ coefficient := -1, powers := [(21, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (41, 1), (55, 1)] }, { coefficient := 1, powers := [(20, 1), (46, 1), (55, 1)] }, { coefficient := 1, powers := [(20, 1), (55, 1), (57, 1)] }, { coefficient := 1, powers := [(55, 1)] }],
  [{ coefficient := -1, powers := [(26, 1), (41, 1), (49, 1)] }, { coefficient := -1, powers := [(26, 1), (46, 1), (49, 1)] }, { coefficient := -1, powers := [(26, 1), (49, 1), (52, 1)] }, { coefficient := -1, powers := [(26, 1), (49, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (49, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(49, 1)] }],
  [{ coefficient := 1, powers := [(30, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (25, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (24, 1), (44, 1), (55, 1)] }, { coefficient := 1, powers := [(23, 1), (26, 1), (49, 1), (51, 1)] }, { coefficient := 1, powers := [(26, 1), (33, 1), (37, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (28, 1), (49, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (21, 1), (30, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (30, 1), (44, 1)] }],
  [{ coefficient := -1, powers := [(18, 1), (30, 1)] }],
  [{ coefficient := -1, powers := [(49, 1), (51, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(12, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (21, 1), (30, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (33, 1), (39, 1), (50, 1)] }],
  [{ coefficient := -1, powers := [(19, 1), (20, 1), (33, 1), (39, 1), (45, 1)] }, { coefficient := 1, powers := [(19, 1), (33, 1), (39, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (20, 1), (33, 1), (39, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (20, 1), (36, 1), (55, 1)] }, { coefficient := -1, powers := [(12, 1), (21, 1), (30, 1), (44, 1)] }],
  [{ coefficient := -1, powers := [(19, 1), (33, 1), (39, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(5, 1), (20, 1), (36, 1), (38, 1), (55, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (20, 1), (36, 1), (41, 1), (55, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (20, 1), (36, 1), (46, 1), (52, 1), (55, 1)] }, { coefficient := 1, powers := [(12, 1), (21, 1), (30, 1), (38, 1), (44, 1), (60, 1)] }, { coefficient := 1, powers := [(12, 1), (21, 1), (30, 1), (41, 1), (44, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1), (21, 1), (30, 1), (44, 1), (46, 1), (52, 1)] }, { coefficient := -1, powers := [(12, 1), (21, 1), (30, 1), (47, 1), (52, 1)] }, { coefficient := -1, powers := [(12, 1), (30, 1), (44, 1), (48, 1), (52, 1)] }, { coefficient := 1, powers := [(12, 1), (30, 1), (49, 1), (52, 1)] }, { coefficient := -1, powers := [(18, 1), (28, 1), (46, 1), (49, 1), (51, 1), (54, 1)] }, { coefficient := -1, powers := [(18, 1), (29, 1), (49, 1), (55, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (25, 1), (46, 1), (55, 1), (64, 1)] }, { coefficient := -1, powers := [(19, 1), (24, 1), (26, 1), (46, 1), (51, 1), (64, 1)] }, { coefficient := 1, powers := [(19, 1), (33, 1), (37, 1), (39, 1), (59, 1)] }, { coefficient := -1, powers := [(19, 1), (33, 1), (39, 1), (43, 1), (50, 1)] }],
  [{ coefficient := -1, powers := [(20, 1), (41, 1), (49, 1), (55, 1)] }, { coefficient := -2, powers := [(20, 1), (46, 1), (49, 1), (55, 1)] }, { coefficient := -1, powers := [(20, 1), (49, 1), (52, 1), (55, 1)] }, { coefficient := -1, powers := [(20, 1), (49, 1), (55, 1), (57, 1)] }, { coefficient := 1, powers := [(21, 1), (47, 1), (55, 1)] }, { coefficient := 1, powers := [(25, 1), (44, 1), (48, 1), (52, 1), (55, 1)] }, { coefficient := -1, powers := [(25, 1), (49, 1), (53, 1), (54, 1)] }, { coefficient := 1, powers := [(26, 1), (41, 1), (46, 1), (49, 1), (51, 1), (63, 1)] }, { coefficient := 1, powers := [(26, 1), (41, 1), (49, 1), (51, 1)] }, { coefficient := 1, powers := [(26, 1), (46, 1), (49, 1), (51, 1), (52, 1), (63, 1)] }, { coefficient := 2, powers := [(26, 1), (46, 1), (49, 1), (51, 1)] }, { coefficient := 1, powers := [(26, 1), (49, 1), (51, 1), (52, 1)] }, { coefficient := 1, powers := [(26, 1), (49, 1), (51, 1), (57, 1)] }, { coefficient := 1, powers := [(37, 1), (49, 1), (51, 1), (54, 1), (60, 1)] }, { coefficient := 1, powers := [(39, 1), (61, 1)] }, { coefficient := 1, powers := [(44, 1), (48, 1), (52, 1), (55, 1), (62, 1)] }, { coefficient := 1, powers := [(49, 1), (51, 1), (54, 1)] }, { coefficient := -1, powers := [(49, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (19, 1), (33, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(6, 1), (19, 1), (33, 1), (34, 1), (39, 1)] }, { coefficient := -1, powers := [(13, 1), (19, 1), (25, 1), (33, 1), (39, 1)] }, { coefficient := 1, powers := [(19, 1), (25, 1), (30, 1), (33, 1), (39, 1), (43, 1), (65, 1)] }, { coefficient := -1, powers := [(19, 1), (30, 1), (33, 1), (34, 1), (37, 1), (39, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(19, 1), (23, 1), (48, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (58, 1)] }, { coefficient := 1, powers := [(8, 1), (36, 1)] }, { coefficient := 1, powers := [(18, 1), (30, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (19, 1), (31, 1), (33, 1), (39, 1)] }, { coefficient := -1, powers := [(19, 1), (20, 1), (33, 1), (39, 1), (50, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (26, 1), (28, 1), (41, 1), (49, 1)] }, { coefficient := -1, powers := [(12, 1), (26, 1), (28, 1), (49, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (33, 1)] }, { coefficient := 1, powers := [(12, 1), (21, 1), (29, 1), (30, 1), (65, 1)] }, { coefficient := -1, powers := [(12, 1), (24, 1), (25, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (24, 1), (61, 1)] }, { coefficient := -1, powers := [(12, 1), (26, 1), (29, 1), (49, 1)] }, { coefficient := 1, powers := [(12, 1), (30, 1), (49, 1)] }, { coefficient := 1, powers := [(18, 1), (26, 1), (29, 1), (49, 1), (51, 1)] }, { coefficient := -1, powers := [(18, 1), (30, 1), (49, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (19, 1), (25, 1), (33, 1), (39, 1), (43, 1)] }, { coefficient := -1, powers := [(9, 1), (19, 1), (33, 1), (34, 1), (37, 1), (39, 1)] }, { coefficient := -1, powers := [(12, 1), (21, 1), (30, 1), (44, 1), (46, 1)] }, { coefficient := 1, powers := [(12, 1), (21, 1), (30, 1), (47, 1)] }]
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
    ¬ ∀ index : Fin 64,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component37.SelectedLeafB0_2_2_5.selectedHasNoCommonZero

end Krenn.Component37.SelectedLeafB0_2_2_5
