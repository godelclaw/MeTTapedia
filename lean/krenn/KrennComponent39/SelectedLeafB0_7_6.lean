import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component39.SelectedLeafB0_7_6

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "349cf553aaa47e9a0a467a71983d1257c9c9756f88a8b5d9de42f3cff984399a"
def certificateSHA256 : String := "b369e651239f3ed4c10635cebdf7029fc70a2f6fa00cd0a04922fbe61564063e"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 68 → Fin 670 := ![
  10,
  11,
  14,
  19,
  21,
  26,
  30,
  92,
  95,
  170,
  180,
  181,
  183,
  184,
  187,
  189,
  191,
  194,
  249,
  250,
  254,
  268,
  276,
  277,
  300,
  301,
  302,
  304,
  305,
  313,
  382,
  384,
  393,
  395,
  397,
  411,
  412,
  425,
  429,
  430,
  433,
  439,
  440,
  444,
  457,
  458,
  460,
  465,
  467,
  470,
  477,
  487,
  520,
  555,
  580,
  585,
  603,
  608,
  644,
  659,
  660,
  661,
  662,
  663,
  664,
  666,
  667,
  669
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 68 → SparsePoly (Fin 66) := ![
  [{ coefficient := 1, powers := [(5, 1), (33, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (30, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (20, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (34, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (33, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (34, 1)] }, { coefficient := 1, powers := [(10, 1), (26, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (23, 1)] }, { coefficient := 1, powers := [(16, 1), (18, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (24, 1)] }, { coefficient := 1, powers := [(16, 1), (18, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (42, 1)] }, { coefficient := 1, powers := [(17, 1), (18, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (45, 1)] }, { coefficient := 1, powers := [(17, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (18, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (47, 1)] }, { coefficient := 1, powers := [(17, 1), (19, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (54, 1)] }, { coefficient := 1, powers := [(28, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (40, 1)] }, { coefficient := 1, powers := [(25, 1), (46, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (23, 1), (42, 1)] }, { coefficient := 1, powers := [(17, 1), (18, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (23, 1), (44, 1)] }, { coefficient := 1, powers := [(16, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (24, 1), (44, 1)] }, { coefficient := 1, powers := [(16, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (19, 1), (52, 1)] }, { coefficient := 1, powers := [(14, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (23, 1), (42, 1)] }, { coefficient := 1, powers := [(17, 1), (18, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (23, 1), (47, 1)] }, { coefficient := 1, powers := [(17, 1), (19, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1)] }, { coefficient := 1, powers := [(18, 1), (42, 1)] }, { coefficient := 1, powers := [(23, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (42, 1)] }, { coefficient := 1, powers := [(23, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (49, 1)] }, { coefficient := 1, powers := [(18, 1), (49, 1)] }, { coefficient := 1, powers := [(23, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (44, 1)] }, { coefficient := 1, powers := [(4, 1), (33, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (51, 1)] }, { coefficient := 1, powers := [(7, 1), (30, 1)] }, { coefficient := 1, powers := [(10, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (44, 1)] }, { coefficient := 1, powers := [(12, 1), (56, 1)] }, { coefficient := 1, powers := [(16, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (18, 1), (56, 1)] }, { coefficient := 1, powers := [(12, 1)] }, { coefficient := 1, powers := [(16, 1), (18, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (23, 1), (46, 1)] }, { coefficient := 1, powers := [(16, 1), (19, 1), (49, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (18, 1), (51, 1)] }, { coefficient := 1, powers := [(16, 1), (18, 1), (56, 1)] }, { coefficient := 1, powers := [(16, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (19, 1), (57, 1)] }, { coefficient := 1, powers := [(16, 1), (24, 1), (47, 1)] }, { coefficient := 1, powers := [(17, 1), (19, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (23, 1), (45, 1)] }, { coefficient := 1, powers := [(17, 1), (23, 1), (39, 1)] }, { coefficient := 1, powers := [(17, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1)] }, { coefficient := 1, powers := [(6, 1), (19, 1), (59, 1)] }, { coefficient := 1, powers := [(19, 1)] }, { coefficient := 1, powers := [(23, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (52, 1)] }, { coefficient := 1, powers := [(18, 1), (49, 1), (56, 1)] }, { coefficient := 1, powers := [(18, 1), (52, 1)] }, { coefficient := 1, powers := [(49, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1)] }, { coefficient := 1, powers := [(12, 1), (28, 1)] }, { coefficient := 1, powers := [(16, 1), (21, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (59, 1)] }, { coefficient := 1, powers := [(16, 1), (19, 1), (51, 1)] }, { coefficient := 1, powers := [(16, 1), (19, 1), (56, 1)] }, { coefficient := 1, powers := [(16, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (60, 1)] }, { coefficient := 1, powers := [(12, 1), (47, 1)] }, { coefficient := 1, powers := [(17, 1), (19, 1), (52, 1)] }, { coefficient := 1, powers := [(17, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (59, 1)] }, { coefficient := 1, powers := [(16, 1), (24, 1), (39, 1)] }, { coefficient := 1, powers := [(16, 1), (24, 1), (44, 1)] }, { coefficient := 1, powers := [(16, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (39, 1)] }, { coefficient := 1, powers := [(16, 1), (44, 1)] }, { coefficient := 1, powers := [(16, 1), (51, 1)] }, { coefficient := 1, powers := [(16, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (54, 1)] }, { coefficient := 1, powers := [(28, 1), (40, 1)] }, { coefficient := 1, powers := [(28, 1), (46, 1), (49, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (36, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (45, 1), (52, 1)] }, { coefficient := 1, powers := [(42, 1), (52, 1)] }, { coefficient := 1, powers := [(45, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(44, 1), (49, 1)] }, { coefficient := 1, powers := [(49, 1), (56, 1)] }, { coefficient := 1, powers := [(52, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1), (53, 1)] }, { coefficient := 1, powers := [(24, 1), (39, 1)] }, { coefficient := 1, powers := [(24, 1), (44, 1)] }, { coefficient := 1, powers := [(53, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1), (49, 1)] }, { coefficient := 1, powers := [(6, 1), (60, 1)] }, { coefficient := 1, powers := [(23, 1), (45, 1), (49, 1)] }, { coefficient := 1, powers := [(42, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1), (49, 1)] }, { coefficient := 1, powers := [(19, 1), (49, 1)] }, { coefficient := 1, powers := [(23, 1), (40, 1)] }, { coefficient := 1, powers := [(23, 1), (46, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1), (51, 1)] }, { coefficient := 1, powers := [(19, 1), (51, 1)] }, { coefficient := 1, powers := [(19, 1), (56, 1)] }, { coefficient := 1, powers := [(46, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1), (52, 1)] }, { coefficient := 1, powers := [(19, 1), (42, 1), (52, 1)] }, { coefficient := 1, powers := [(40, 1), (42, 1)] }, { coefficient := 1, powers := [(47, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (39, 1), (55, 1)] }, { coefficient := 1, powers := [(1, 1), (43, 1)] }, { coefficient := 1, powers := [(4, 1), (30, 1), (55, 1)] }, { coefficient := 1, powers := [(10, 1), (20, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (42, 1), (53, 1)] }, { coefficient := 1, powers := [(16, 1), (21, 1), (57, 1)] }, { coefficient := 1, powers := [(16, 1), (28, 1), (42, 1)] }, { coefficient := 1, powers := [(17, 1), (21, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (34, 1), (51, 1)] }, { coefficient := 1, powers := [(7, 1), (34, 1), (39, 1)] }, { coefficient := 1, powers := [(10, 1), (27, 1), (45, 1)] }, { coefficient := 1, powers := [(10, 1), (34, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (19, 1), (56, 1)] }, { coefficient := 1, powers := [(12, 1), (46, 1)] }, { coefficient := 1, powers := [(16, 1), (19, 1), (52, 1)] }, { coefficient := 1, powers := [(16, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1)] }, { coefficient := 1, powers := [(6, 1), (59, 1)] }, { coefficient := 1, powers := [(23, 1), (39, 1)] }, { coefficient := 1, powers := [(23, 1), (44, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1), (49, 1)] }, { coefficient := 1, powers := [(6, 1), (19, 1), (60, 1)] }, { coefficient := 1, powers := [(19, 1), (42, 1), (49, 1)] }, { coefficient := 1, powers := [(23, 1), (40, 1), (42, 1)] }, { coefficient := 1, powers := [(23, 1), (47, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (51, 1)] }, { coefficient := 1, powers := [(20, 1), (56, 1)] }, { coefficient := 1, powers := [(25, 1), (39, 1)] }, { coefficient := 1, powers := [(25, 1), (44, 1)] }, { coefficient := 1, powers := [(30, 1), (36, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (40, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(19, 1), (49, 1), (56, 1)] }, { coefficient := 1, powers := [(19, 1), (52, 1)] }, { coefficient := 1, powers := [(40, 1)] }, { coefficient := 1, powers := [(46, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (36, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (44, 1), (51, 1)] }, { coefficient := 1, powers := [(39, 1)] }, { coefficient := 1, powers := [(44, 1)] }, { coefficient := 1, powers := [(51, 1)] }, { coefficient := 1, powers := [(56, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (36, 1), (59, 1)] }, { coefficient := 1, powers := [(1, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(1, 1), (44, 1), (51, 1)] }, { coefficient := 1, powers := [(4, 1), (25, 1), (59, 1)] }, { coefficient := 1, powers := [(4, 1), (30, 1), (56, 1)] }, { coefficient := 1, powers := [(4, 1), (33, 1), (51, 1)] }, { coefficient := 1, powers := [(7, 1), (20, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (30, 1), (44, 1)] }, { coefficient := 1, powers := [(7, 1), (33, 1), (39, 1)] }, { coefficient := 1, powers := [(10, 1), (20, 1), (56, 1)] }, { coefficient := 1, powers := [(10, 1), (25, 1), (44, 1)] }, { coefficient := 1, powers := [(10, 1), (33, 1), (36, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1), (51, 1)] }, { coefficient := 1, powers := [(14, 1), (25, 1), (39, 1)] }, { coefficient := 1, powers := [(14, 1), (30, 1), (36, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (37, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (47, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (28, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (22, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1), (47, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (40, 1)] }, { coefficient := 1, powers := [(12, 1), (22, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1), (28, 1), (47, 1)] }, { coefficient := 1, powers := [(12, 1), (34, 1), (37, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (54, 1)] }, { coefficient := 1, powers := [(17, 1), (28, 1), (40, 1)] }, { coefficient := 1, powers := [(17, 1), (31, 1), (37, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1)] }],
  [{ coefficient := 1, powers := [(1, 1)] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(38, 1), (61, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(40, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(55, 1), (64, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(57, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 68 → SparsePoly (Fin 66) := ![
  [{ coefficient := -1, powers := [(4, 1), (21, 1), (51, 1), (53, 1), (60, 1)] }, { coefficient := -1, powers := [(4, 1), (21, 1), (53, 1), (56, 1), (60, 1)] }, { coefficient := 3, powers := [(4, 1), (28, 1), (51, 1), (60, 1)] }, { coefficient := 3, powers := [(4, 1), (28, 1), (56, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (21, 1), (44, 1), (53, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (21, 1), (51, 1), (53, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (21, 1), (53, 1), (56, 1), (60, 1)] }, { coefficient := -3, powers := [(7, 1), (28, 1), (44, 1), (60, 1)] }, { coefficient := -3, powers := [(7, 1), (28, 1), (51, 1), (60, 1)] }, { coefficient := -3, powers := [(7, 1), (28, 1), (56, 1), (60, 1)] }, { coefficient := -1, powers := [(10, 1), (21, 1), (36, 1), (53, 1), (60, 1)] }, { coefficient := 3, powers := [(10, 1), (28, 1), (36, 1), (60, 1)] }, { coefficient := 1, powers := [(14, 1), (21, 1), (36, 1), (53, 1), (60, 1)] }, { coefficient := -3, powers := [(14, 1), (28, 1), (36, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (22, 1), (51, 1), (60, 1)] }, { coefficient := 1, powers := [(4, 1), (22, 1), (56, 1), (60, 1)] }, { coefficient := -1, powers := [(4, 1), (31, 1), (47, 1), (51, 1)] }, { coefficient := -1, powers := [(4, 1), (31, 1), (47, 1), (56, 1)] }, { coefficient := -1, powers := [(7, 1), (22, 1), (51, 1), (60, 1)] }, { coefficient := -1, powers := [(7, 1), (22, 1), (56, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (31, 1), (47, 1), (51, 1)] }, { coefficient := 1, powers := [(7, 1), (31, 1), (47, 1), (56, 1)] }, { coefficient := -1, powers := [(10, 1), (22, 1), (36, 1), (60, 1)] }, { coefficient := 1, powers := [(10, 1), (31, 1), (36, 1), (47, 1)] }, { coefficient := 1, powers := [(14, 1), (22, 1), (36, 1), (60, 1)] }, { coefficient := -1, powers := [(14, 1), (31, 1), (36, 1), (47, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (25, 1), (26, 1), (54, 1), (59, 1)] }, { coefficient := -1, powers := [(5, 1), (26, 1), (33, 1), (54, 1), (56, 1)] }, { coefficient := -1, powers := [(5, 1), (27, 1), (33, 1), (54, 1)] }, { coefficient := -1, powers := [(8, 1), (25, 1), (26, 1), (40, 1), (59, 1)] }, { coefficient := -1, powers := [(8, 1), (26, 1), (33, 1), (40, 1), (56, 1)] }, { coefficient := -1, powers := [(8, 1), (27, 1), (33, 1), (40, 1)] }, { coefficient := -1, powers := [(12, 1), (25, 1), (26, 1), (37, 1), (59, 1)] }, { coefficient := -1, powers := [(12, 1), (26, 1), (33, 1), (37, 1), (56, 1)] }, { coefficient := -1, powers := [(12, 1), (27, 1), (33, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (19, 1), (33, 1), (34, 1), (36, 1), (54, 1), (63, 1)] }, { coefficient := 1, powers := [(8, 1), (19, 1), (33, 1), (34, 1), (36, 1), (40, 1), (63, 1)] }, { coefficient := 1, powers := [(12, 1), (19, 1), (33, 1), (34, 1), (36, 1), (37, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (22, 1), (24, 1), (51, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (22, 1), (24, 1), (56, 1), (60, 1)] }, { coefficient := -1, powers := [(7, 1), (24, 1), (31, 1), (47, 1), (51, 1)] }, { coefficient := -1, powers := [(7, 1), (24, 1), (31, 1), (47, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (16, 1), (22, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (16, 1), (31, 1), (47, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (8, 1), (22, 1), (49, 1), (59, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(4, 1), (8, 1), (31, 1), (47, 1), (49, 1), (59, 1), (63, 1)] }, { coefficient := -1, powers := [(5, 1), (14, 1), (21, 1), (44, 1), (49, 1), (53, 1), (60, 1), (63, 1)] }, { coefficient := 3, powers := [(5, 1), (14, 1), (28, 1), (44, 1), (49, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(5, 1), (14, 1), (34, 1), (44, 1), (49, 1), (54, 1), (63, 1)] }, { coefficient := 1, powers := [(8, 1), (14, 1), (22, 1), (44, 1), (49, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(8, 1), (14, 1), (22, 1), (49, 1), (51, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(8, 1), (14, 1), (22, 1), (49, 1), (56, 1), (60, 1), (63, 1)] }, { coefficient := -1, powers := [(8, 1), (14, 1), (31, 1), (44, 1), (47, 1), (49, 1), (63, 1)] }, { coefficient := -1, powers := [(8, 1), (14, 1), (31, 1), (47, 1), (49, 1), (51, 1), (63, 1)] }, { coefficient := -1, powers := [(8, 1), (14, 1), (31, 1), (47, 1), (49, 1), (56, 1), (63, 1)] }, { coefficient := 1, powers := [(8, 1), (14, 1), (34, 1), (40, 1), (44, 1), (49, 1), (63, 1)] }, { coefficient := 1, powers := [(12, 1), (14, 1), (34, 1), (37, 1), (44, 1), (49, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (20, 1), (54, 1), (59, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (20, 1), (40, 1), (59, 1), (61, 1)] }, { coefficient := 1, powers := [(12, 1), (20, 1), (37, 1), (59, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (22, 1), (44, 1), (60, 1), (61, 1)] }, { coefficient := -1, powers := [(7, 1), (22, 1), (51, 1), (60, 1), (61, 1)] }, { coefficient := -1, powers := [(7, 1), (22, 1), (56, 1), (60, 1), (61, 1)] }, { coefficient := 1, powers := [(7, 1), (31, 1), (44, 1), (47, 1), (61, 1)] }, { coefficient := 1, powers := [(7, 1), (31, 1), (47, 1), (51, 1), (61, 1)] }, { coefficient := 1, powers := [(7, 1), (31, 1), (47, 1), (56, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (25, 1), (54, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (54, 1), (56, 1)] }, { coefficient := 1, powers := [(8, 1), (25, 1), (40, 1), (59, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (40, 1), (56, 1)] }, { coefficient := 1, powers := [(12, 1), (25, 1), (37, 1), (59, 1)] }, { coefficient := 1, powers := [(12, 1), (33, 1), (37, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [(28, 1), (44, 1), (47, 1)] }, { coefficient := -3, powers := [(28, 1), (47, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [(21, 1), (47, 1), (51, 1)] }, { coefficient := -2, powers := [(21, 1), (47, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [(19, 1), (28, 1), (44, 1)] }],
  [{ coefficient := -1, powers := [(23, 1), (28, 1), (46, 1)] }],
  [{ coefficient := -1, powers := [(19, 1), (28, 1), (42, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(21, 1), (47, 1), (54, 1), (56, 1)] }, { coefficient := -2, powers := [(28, 1), (42, 1), (46, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(21, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(16, 1), (47, 1)] }, { coefficient := -1, powers := [(17, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (8, 1), (22, 1), (59, 1), (60, 1), (63, 1)] }, { coefficient := -1, powers := [(4, 1), (8, 1), (31, 1), (47, 1), (59, 1), (63, 1)] }, { coefficient := 1, powers := [(5, 1), (14, 1), (21, 1), (44, 1), (53, 1), (60, 1), (63, 1)] }, { coefficient := -3, powers := [(5, 1), (14, 1), (28, 1), (44, 1), (60, 1), (63, 1)] }, { coefficient := -1, powers := [(5, 1), (14, 1), (34, 1), (44, 1), (54, 1), (63, 1)] }, { coefficient := -1, powers := [(8, 1), (14, 1), (22, 1), (44, 1), (60, 1), (63, 1)] }, { coefficient := -1, powers := [(8, 1), (14, 1), (22, 1), (51, 1), (60, 1), (63, 1)] }, { coefficient := -1, powers := [(8, 1), (14, 1), (22, 1), (56, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(8, 1), (14, 1), (31, 1), (44, 1), (47, 1), (63, 1)] }, { coefficient := 1, powers := [(8, 1), (14, 1), (31, 1), (47, 1), (51, 1), (63, 1)] }, { coefficient := 1, powers := [(8, 1), (14, 1), (31, 1), (47, 1), (56, 1), (63, 1)] }, { coefficient := -1, powers := [(8, 1), (14, 1), (34, 1), (40, 1), (44, 1), (63, 1)] }, { coefficient := -1, powers := [(12, 1), (14, 1), (34, 1), (37, 1), (44, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(28, 1), (44, 1), (46, 1)] }, { coefficient := 2, powers := [(28, 1), (46, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [(19, 1), (28, 1), (42, 1), (44, 1)] }, { coefficient := -1, powers := [(28, 1), (47, 1)] }],
  [{ coefficient := -1, powers := [(21, 1), (47, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (33, 1), (34, 1), (36, 1), (54, 1), (63, 1)] }, { coefficient := -1, powers := [(8, 1), (33, 1), (34, 1), (36, 1), (40, 1), (63, 1)] }, { coefficient := -1, powers := [(12, 1), (33, 1), (34, 1), (36, 1), (37, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (28, 1), (44, 1), (52, 1)] }, { coefficient := 2, powers := [(28, 1), (46, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(21, 1), (54, 1), (56, 1)] }, { coefficient := -3, powers := [(28, 1), (49, 1), (56, 1)] }, { coefficient := -2, powers := [(28, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (19, 1), (28, 1), (44, 1), (56, 1)] }, { coefficient := -2, powers := [(12, 1), (28, 1), (46, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (28, 1), (51, 1)] }, { coefficient := 2, powers := [(12, 1), (28, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (28, 1), (44, 1), (47, 1)] }, { coefficient := 3, powers := [(16, 1), (28, 1), (47, 1), (56, 1)] }, { coefficient := 1, powers := [(17, 1), (28, 1), (44, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (21, 1), (53, 1), (56, 1), (60, 1)] }, { coefficient := -3, powers := [(5, 1), (28, 1), (56, 1), (60, 1)] }, { coefficient := -1, powers := [(5, 1), (34, 1), (54, 1), (56, 1)] }, { coefficient := 1, powers := [(8, 1), (22, 1), (51, 1), (60, 1)] }, { coefficient := -1, powers := [(8, 1), (31, 1), (47, 1), (51, 1)] }, { coefficient := -1, powers := [(8, 1), (34, 1), (40, 1), (56, 1)] }, { coefficient := -1, powers := [(12, 1), (34, 1), (37, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (21, 1), (44, 1), (53, 1), (60, 1)] }, { coefficient := 3, powers := [(5, 1), (28, 1), (44, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (44, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (22, 1), (44, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (22, 1), (51, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (22, 1), (56, 1), (60, 1)] }, { coefficient := -1, powers := [(8, 1), (31, 1), (44, 1), (47, 1)] }, { coefficient := -1, powers := [(8, 1), (31, 1), (47, 1), (51, 1)] }, { coefficient := -1, powers := [(8, 1), (31, 1), (47, 1), (56, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (40, 1), (44, 1)] }, { coefficient := 1, powers := [(12, 1), (34, 1), (37, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (23, 1), (28, 1), (42, 1), (44, 1)] }, { coefficient := 1, powers := [(21, 1), (24, 1), (47, 1)] }, { coefficient := 2, powers := [(23, 1), (28, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (28, 1), (42, 1), (44, 1)] }, { coefficient := 2, powers := [(28, 1), (42, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(28, 1), (42, 1), (44, 1)] }, { coefficient := 1, powers := [(28, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (47, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(21, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(28, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (28, 1), (52, 1)] }],
  [{ coefficient := -2, powers := [(17, 1), (28, 1), (46, 1)] }],
  [{ coefficient := 2, powers := [(47, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (21, 1), (25, 1), (53, 1), (60, 1)] }, { coefficient := 3, powers := [(4, 1), (25, 1), (28, 1), (60, 1)] }, { coefficient := 1, powers := [(6, 1), (28, 1), (60, 1)] }, { coefficient := -1, powers := [(7, 1), (20, 1), (21, 1), (53, 1), (60, 1)] }, { coefficient := 3, powers := [(7, 1), (20, 1), (28, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (28, 1), (59, 1)] }, { coefficient := 1, powers := [(21, 1), (53, 1)] }, { coefficient := -2, powers := [(28, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (20, 1), (22, 1), (60, 1)] }, { coefficient := -1, powers := [(7, 1), (20, 1), (31, 1), (47, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (20, 1), (22, 1), (24, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (20, 1), (24, 1), (31, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(17, 1)] }],
  [{ coefficient := -1, powers := [(16, 1), (19, 1), (23, 1), (28, 1), (44, 1)] }, { coefficient := -1, powers := [(16, 1), (19, 1), (28, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (19, 1), (28, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (21, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (19, 1), (28, 1), (44, 1)] }],
  [{ coefficient := -1, powers := [(17, 1), (28, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (16, 1), (21, 1), (25, 1), (53, 1), (60, 1)] }, { coefficient := -3, powers := [(4, 1), (16, 1), (25, 1), (28, 1), (60, 1)] }, { coefficient := -1, powers := [(6, 1), (16, 1), (28, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (16, 1), (20, 1), (21, 1), (53, 1), (60, 1)] }, { coefficient := -3, powers := [(7, 1), (16, 1), (20, 1), (28, 1), (60, 1)] }, { coefficient := -1, powers := [(12, 1), (28, 1), (42, 1)] }, { coefficient := 1, powers := [(17, 1), (21, 1), (54, 1)] }],
  [{ coefficient := 2, powers := [(16, 1), (28, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (21, 1), (53, 1), (56, 1), (60, 1), (64, 1)] }, { coefficient := 3, powers := [(5, 1), (28, 1), (56, 1), (60, 1), (64, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (54, 1), (56, 1), (64, 1)] }, { coefficient := -1, powers := [(8, 1), (22, 1), (51, 1), (60, 1), (64, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1), (47, 1), (51, 1), (64, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (40, 1), (56, 1), (64, 1)] }, { coefficient := 1, powers := [(12, 1), (34, 1), (37, 1), (56, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(40, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (33, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (40, 1)] }, { coefficient := 1, powers := [(12, 1), (33, 1), (37, 1)] }],
  [{ coefficient := -1, powers := [(28, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (28, 1), (47, 1)] }, { coefficient := 1, powers := [(17, 1), (28, 1), (40, 1)] }],
  [{ coefficient := -1, powers := [(16, 1), (28, 1), (44, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (14, 1), (21, 1), (53, 1), (60, 1)] }, { coefficient := 3, powers := [(5, 1), (14, 1), (28, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (14, 1), (34, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (10, 1), (22, 1), (60, 1)] }, { coefficient := -1, powers := [(8, 1), (10, 1), (31, 1), (47, 1)] }, { coefficient := 1, powers := [(8, 1), (14, 1), (34, 1), (40, 1)] }, { coefficient := 1, powers := [(12, 1), (14, 1), (34, 1), (37, 1)] }],
  [{ coefficient := 2, powers := [(17, 1), (28, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (7, 1), (21, 1), (33, 1), (53, 1), (60, 1)] }, { coefficient := 3, powers := [(5, 1), (7, 1), (28, 1), (33, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (8, 1), (22, 1), (33, 1), (60, 1)] }, { coefficient := -1, powers := [(7, 1), (8, 1), (31, 1), (33, 1), (47, 1)] }, { coefficient := -1, powers := [(8, 1), (10, 1), (22, 1), (25, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (10, 1), (25, 1), (31, 1), (47, 1)] }, { coefficient := 1, powers := [(8, 1), (14, 1), (22, 1), (25, 1), (60, 1)] }, { coefficient := -1, powers := [(8, 1), (14, 1), (25, 1), (31, 1), (47, 1)] }, { coefficient := 1, powers := [(12, 1), (21, 1), (24, 1), (47, 1)] }, { coefficient := -1, powers := [(12, 1), (23, 1), (28, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (21, 1), (53, 1), (60, 1)] }, { coefficient := -3, powers := [(5, 1), (28, 1), (60, 1)] }, { coefficient := -1, powers := [(5, 1), (34, 1), (54, 1)] }, { coefficient := -1, powers := [(8, 1), (22, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1), (47, 1)] }, { coefficient := -1, powers := [(8, 1), (34, 1), (40, 1)] }, { coefficient := -1, powers := [(12, 1), (34, 1), (37, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(4, 1), (16, 1), (21, 1), (25, 1), (46, 1), (51, 1), (53, 1), (60, 1)] }, { coefficient := 3, powers := [(4, 1), (16, 1), (25, 1), (28, 1), (46, 1), (51, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (7, 1), (21, 1), (33, 1), (36, 1), (53, 1), (59, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (7, 1), (21, 1), (33, 1), (39, 1), (53, 1), (56, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (7, 1), (21, 1), (33, 1), (44, 1), (51, 1), (53, 1), (60, 1)] }, { coefficient := -3, powers := [(5, 1), (7, 1), (28, 1), (33, 1), (36, 1), (59, 1), (60, 1)] }, { coefficient := -3, powers := [(5, 1), (7, 1), (28, 1), (33, 1), (39, 1), (56, 1), (60, 1)] }, { coefficient := -3, powers := [(5, 1), (7, 1), (28, 1), (33, 1), (44, 1), (51, 1), (60, 1)] }, { coefficient := 1, powers := [(6, 1), (16, 1), (28, 1), (46, 1), (51, 1), (60, 1)] }, { coefficient := -1, powers := [(7, 1), (8, 1), (22, 1), (33, 1), (36, 1), (59, 1), (60, 1)] }, { coefficient := -1, powers := [(7, 1), (8, 1), (22, 1), (33, 1), (39, 1), (56, 1), (60, 1)] }, { coefficient := -1, powers := [(7, 1), (8, 1), (22, 1), (33, 1), (44, 1), (51, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (8, 1), (31, 1), (33, 1), (36, 1), (47, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (8, 1), (31, 1), (33, 1), (39, 1), (47, 1), (56, 1)] }, { coefficient := 1, powers := [(7, 1), (8, 1), (31, 1), (33, 1), (44, 1), (47, 1), (51, 1)] }, { coefficient := -1, powers := [(7, 1), (16, 1), (20, 1), (21, 1), (46, 1), (51, 1), (53, 1), (60, 1)] }, { coefficient := 3, powers := [(7, 1), (16, 1), (20, 1), (28, 1), (46, 1), (51, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (10, 1), (22, 1), (25, 1), (36, 1), (59, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (10, 1), (22, 1), (25, 1), (39, 1), (56, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (10, 1), (22, 1), (25, 1), (44, 1), (51, 1), (60, 1)] }, { coefficient := -1, powers := [(8, 1), (10, 1), (25, 1), (31, 1), (36, 1), (47, 1), (59, 1)] }, { coefficient := -1, powers := [(8, 1), (10, 1), (25, 1), (31, 1), (39, 1), (47, 1), (56, 1)] }, { coefficient := -1, powers := [(8, 1), (10, 1), (25, 1), (31, 1), (44, 1), (47, 1), (51, 1)] }, { coefficient := -1, powers := [(8, 1), (14, 1), (22, 1), (25, 1), (36, 1), (59, 1), (60, 1)] }, { coefficient := -1, powers := [(8, 1), (14, 1), (22, 1), (25, 1), (39, 1), (56, 1), (60, 1)] }, { coefficient := -1, powers := [(8, 1), (14, 1), (22, 1), (25, 1), (44, 1), (51, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (14, 1), (25, 1), (31, 1), (36, 1), (47, 1), (59, 1)] }, { coefficient := 1, powers := [(8, 1), (14, 1), (25, 1), (31, 1), (39, 1), (47, 1), (56, 1)] }, { coefficient := 1, powers := [(8, 1), (14, 1), (25, 1), (31, 1), (44, 1), (47, 1), (51, 1)] }, { coefficient := 1, powers := [(12, 1), (19, 1), (28, 1), (42, 1), (44, 1), (56, 1)] }, { coefficient := -1, powers := [(12, 1), (21, 1), (24, 1), (36, 1), (47, 1), (59, 1)] }, { coefficient := -1, powers := [(12, 1), (21, 1), (24, 1), (39, 1), (47, 1), (56, 1)] }, { coefficient := -1, powers := [(12, 1), (21, 1), (24, 1), (44, 1), (47, 1), (51, 1)] }, { coefficient := 1, powers := [(12, 1), (21, 1), (44, 1), (47, 1), (53, 1)] }, { coefficient := 1, powers := [(12, 1), (23, 1), (28, 1), (36, 1), (47, 1), (59, 1)] }, { coefficient := 1, powers := [(12, 1), (23, 1), (28, 1), (39, 1), (47, 1), (56, 1)] }, { coefficient := 1, powers := [(12, 1), (23, 1), (28, 1), (44, 1), (47, 1), (51, 1)] }, { coefficient := 1, powers := [(12, 1), (28, 1), (42, 1), (46, 1), (51, 1)] }, { coefficient := 2, powers := [(12, 1), (28, 1), (42, 1), (46, 1), (56, 1)] }, { coefficient := -1, powers := [(12, 1), (28, 1), (44, 1), (47, 1)] }, { coefficient := -1, powers := [(12, 1), (28, 1), (47, 1), (51, 1)] }, { coefficient := -2, powers := [(12, 1), (28, 1), (47, 1), (56, 1)] }, { coefficient := 1, powers := [(16, 1), (19, 1), (23, 1), (28, 1), (36, 1), (44, 1), (60, 1)] }, { coefficient := 1, powers := [(16, 1), (19, 1), (23, 1), (28, 1), (44, 1), (45, 1), (52, 1)] }, { coefficient := 1, powers := [(16, 1), (19, 1), (28, 1), (36, 1), (60, 1)] }, { coefficient := -1, powers := [(16, 1), (19, 1), (28, 1), (44, 1), (45, 1), (49, 1)] }, { coefficient := 1, powers := [(16, 1), (19, 1), (28, 1), (45, 1), (52, 1)] }, { coefficient := -3, powers := [(16, 1), (28, 1), (47, 1), (49, 1), (56, 1)] }, { coefficient := -2, powers := [(16, 1), (28, 1), (47, 1), (52, 1)] }, { coefficient := -1, powers := [(17, 1), (19, 1), (28, 1), (44, 1), (52, 1)] }, { coefficient := -1, powers := [(17, 1), (21, 1), (46, 1), (51, 1), (54, 1)] }, { coefficient := -1, powers := [(17, 1), (28, 1), (40, 1), (44, 1)] }, { coefficient := -2, powers := [(17, 1), (28, 1), (40, 1), (56, 1)] }, { coefficient := -1, powers := [(17, 1), (28, 1), (46, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (21, 1), (36, 1), (53, 1), (59, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (21, 1), (39, 1), (53, 1), (55, 1), (56, 1), (60, 1), (64, 1)] }, { coefficient := -1, powers := [(5, 1), (21, 1), (39, 1), (53, 1), (56, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (21, 1), (43, 1), (53, 1), (56, 1), (60, 1), (64, 1)] }, { coefficient := -1, powers := [(5, 1), (21, 1), (44, 1), (53, 1), (56, 1), (60, 1)] }, { coefficient := 3, powers := [(5, 1), (28, 1), (36, 1), (59, 1), (60, 1)] }, { coefficient := -3, powers := [(5, 1), (28, 1), (39, 1), (55, 1), (56, 1), (60, 1), (64, 1)] }, { coefficient := 3, powers := [(5, 1), (28, 1), (39, 1), (56, 1), (60, 1)] }, { coefficient := -3, powers := [(5, 1), (28, 1), (43, 1), (56, 1), (60, 1), (64, 1)] }, { coefficient := 3, powers := [(5, 1), (28, 1), (44, 1), (56, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (36, 1), (54, 1), (59, 1)] }, { coefficient := -1, powers := [(5, 1), (34, 1), (39, 1), (54, 1), (55, 1), (56, 1), (64, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (39, 1), (54, 1), (56, 1)] }, { coefficient := -1, powers := [(5, 1), (34, 1), (43, 1), (54, 1), (56, 1), (64, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (44, 1), (54, 1), (56, 1)] }, { coefficient := 1, powers := [(8, 1), (22, 1), (36, 1), (59, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (22, 1), (39, 1), (51, 1), (55, 1), (60, 1), (64, 1)] }, { coefficient := 1, powers := [(8, 1), (22, 1), (39, 1), (56, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (22, 1), (43, 1), (51, 1), (60, 1), (64, 1)] }, { coefficient := -1, powers := [(8, 1), (22, 1), (44, 1), (51, 1), (60, 1)] }, { coefficient := -1, powers := [(8, 1), (22, 1), (51, 2), (60, 1)] }, { coefficient := -1, powers := [(8, 1), (22, 1), (51, 1), (56, 1), (60, 1)] }, { coefficient := -1, powers := [(8, 1), (31, 1), (36, 1), (47, 1), (59, 1)] }, { coefficient := -1, powers := [(8, 1), (31, 1), (39, 1), (47, 1), (51, 1), (55, 1), (64, 1)] }, { coefficient := -1, powers := [(8, 1), (31, 1), (39, 1), (47, 1), (56, 1)] }, { coefficient := -1, powers := [(8, 1), (31, 1), (43, 1), (47, 1), (51, 1), (64, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1), (44, 1), (47, 1), (51, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1), (47, 1), (51, 2)] }, { coefficient := 1, powers := [(8, 1), (31, 1), (47, 1), (51, 1), (56, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (36, 1), (40, 1), (59, 1)] }, { coefficient := -1, powers := [(8, 1), (34, 1), (39, 1), (40, 1), (55, 1), (56, 1), (64, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (39, 1), (40, 1), (56, 1)] }, { coefficient := -1, powers := [(8, 1), (34, 1), (40, 1), (43, 1), (56, 1), (64, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (40, 1), (44, 1), (56, 1)] }, { coefficient := 1, powers := [(12, 1), (34, 1), (36, 1), (37, 1), (59, 1)] }, { coefficient := -1, powers := [(12, 1), (34, 1), (37, 1), (39, 1), (55, 1), (56, 1), (64, 1)] }, { coefficient := 1, powers := [(12, 1), (34, 1), (37, 1), (39, 1), (56, 1)] }, { coefficient := -1, powers := [(12, 1), (34, 1), (37, 1), (43, 1), (56, 1), (64, 1)] }, { coefficient := 1, powers := [(12, 1), (34, 1), (37, 1), (44, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(37, 1), (60, 1)] }, { coefficient := 1, powers := [(40, 1), (42, 1), (53, 1)] }, { coefficient := -1, powers := [(47, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (7, 1), (20, 1), (34, 1), (54, 1), (59, 1)] }, { coefficient := -1, powers := [(7, 1), (8, 1), (20, 1), (34, 1), (40, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (8, 1), (22, 1), (33, 1), (44, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (8, 1), (22, 1), (33, 1), (51, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (8, 1), (22, 1), (33, 1), (56, 1), (60, 1)] }, { coefficient := -1, powers := [(7, 1), (8, 1), (31, 1), (33, 1), (44, 1), (47, 1)] }, { coefficient := -1, powers := [(7, 1), (8, 1), (31, 1), (33, 1), (47, 1), (51, 1)] }, { coefficient := -1, powers := [(7, 1), (8, 1), (31, 1), (33, 1), (47, 1), (56, 1)] }, { coefficient := -1, powers := [(7, 1), (12, 1), (20, 1), (34, 1), (37, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (8, 1), (22, 1), (25, 1), (59, 1), (60, 1)] }, { coefficient := 1, powers := [(4, 1), (8, 1), (25, 1), (31, 1), (47, 1), (59, 1)] }, { coefficient := -1, powers := [(5, 1), (14, 1), (21, 1), (25, 1), (44, 1), (53, 1), (60, 1)] }, { coefficient := 3, powers := [(5, 1), (14, 1), (25, 1), (28, 1), (44, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (14, 1), (25, 1), (34, 1), (44, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (14, 1), (33, 1), (34, 1), (36, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (14, 1), (22, 1), (25, 1), (44, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (14, 1), (22, 1), (25, 1), (51, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (14, 1), (22, 1), (25, 1), (56, 1), (60, 1)] }, { coefficient := -1, powers := [(8, 1), (14, 1), (25, 1), (31, 1), (44, 1), (47, 1)] }, { coefficient := -1, powers := [(8, 1), (14, 1), (25, 1), (31, 1), (47, 1), (51, 1)] }, { coefficient := -1, powers := [(8, 1), (14, 1), (25, 1), (31, 1), (47, 1), (56, 1)] }, { coefficient := 1, powers := [(8, 1), (14, 1), (25, 1), (34, 1), (40, 1), (44, 1)] }, { coefficient := 1, powers := [(8, 1), (14, 1), (33, 1), (34, 1), (36, 1), (40, 1)] }, { coefficient := 1, powers := [(12, 1), (14, 1), (25, 1), (34, 1), (37, 1), (44, 1)] }, { coefficient := 1, powers := [(12, 1), (14, 1), (33, 1), (34, 1), (36, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (5, 1), (21, 1), (30, 1), (53, 1), (56, 1), (60, 1)] }, { coefficient := -3, powers := [(4, 1), (5, 1), (28, 1), (30, 1), (56, 1), (60, 1)] }, { coefficient := -1, powers := [(4, 1), (5, 1), (30, 1), (34, 1), (54, 1), (56, 1)] }, { coefficient := 1, powers := [(4, 1), (8, 1), (22, 1), (30, 1), (51, 1), (60, 1)] }, { coefficient := -1, powers := [(4, 1), (8, 1), (30, 1), (31, 1), (47, 1), (51, 1)] }, { coefficient := -1, powers := [(4, 1), (8, 1), (30, 1), (34, 1), (40, 1), (56, 1)] }, { coefficient := -1, powers := [(4, 1), (12, 1), (30, 1), (34, 1), (37, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (10, 1), (20, 1), (21, 1), (53, 1), (56, 1), (60, 1)] }, { coefficient := -3, powers := [(5, 1), (10, 1), (20, 1), (28, 1), (56, 1), (60, 1)] }, { coefficient := -1, powers := [(5, 1), (10, 1), (20, 1), (34, 1), (54, 1), (56, 1)] }, { coefficient := 1, powers := [(8, 1), (10, 1), (20, 1), (22, 1), (51, 1), (60, 1)] }, { coefficient := -1, powers := [(8, 1), (10, 1), (20, 1), (31, 1), (47, 1), (51, 1)] }, { coefficient := -1, powers := [(8, 1), (10, 1), (20, 1), (34, 1), (40, 1), (56, 1)] }, { coefficient := -1, powers := [(10, 1), (12, 1), (20, 1), (34, 1), (37, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (40, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1)] }, { coefficient := 1, powers := [(12, 1), (22, 1)] }, { coefficient := 1, powers := [(16, 1), (19, 1), (21, 1), (52, 1)] }, { coefficient := 1, powers := [(16, 1), (21, 1), (40, 1)] }]
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
    ¬ ∀ index : Fin 68,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component39.SelectedLeafB0_7_6.selectedHasNoCommonZero

end Krenn.Component39.SelectedLeafB0_7_6
