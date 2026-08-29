import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component39.SelectedLeafB5_2_3_5_2

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "387b0b1d347d34d3e9feb30ea16c6d0ddc7bb62f1d660265e960ec05022792d1"
def certificateSHA256 : String := "fafc8fb568dc056e1cb77b694605dc7c2ba413ab62d71e098fbbcded3ffb6bc7"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 62 → Fin 676 := ![
  10,
  11,
  14,
  21,
  26,
  180,
  181,
  184,
  187,
  188,
  190,
  191,
  195,
  232,
  276,
  277,
  280,
  300,
  301,
  302,
  303,
  304,
  305,
  316,
  318,
  319,
  321,
  324,
  347,
  396,
  397,
  399,
  418,
  422,
  430,
  434,
  439,
  452,
  460,
  463,
  465,
  470,
  471,
  515,
  523,
  542,
  602,
  603,
  645,
  651,
  659,
  660,
  661,
  662,
  663,
  666,
  668,
  669,
  670,
  671,
  672,
  675
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 62 → SparsePoly (Fin 69) := ![
  [{ coefficient := 1, powers := [(5, 1), (33, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (30, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (20, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (23, 1)] }, { coefficient := 1, powers := [(16, 1), (18, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (24, 1)] }, { coefficient := 1, powers := [(16, 1), (18, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (45, 1)] }, { coefficient := 1, powers := [(17, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (18, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (42, 1)] }, { coefficient := 1, powers := [(17, 1), (18, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (45, 1)] }, { coefficient := -1, powers := [(27, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (54, 1)] }, { coefficient := 1, powers := [(28, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(26, 1), (52, 1)] }, { coefficient := -1, powers := [(27, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (24, 1), (45, 1)] }, { coefficient := 1, powers := [(10, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (23, 1), (42, 1)] }, { coefficient := 1, powers := [(17, 1), (18, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (23, 1), (47, 1)] }, { coefficient := 1, powers := [(17, 1), (19, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (42, 1), (53, 1)] }, { coefficient := 1, powers := [(20, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1)] }, { coefficient := 1, powers := [(18, 1), (42, 1)] }, { coefficient := 1, powers := [(23, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (42, 1)] }, { coefficient := 1, powers := [(23, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (49, 1)] }, { coefficient := 1, powers := [(18, 1), (49, 1)] }, { coefficient := 1, powers := [(23, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (54, 1)] }, { coefficient := 1, powers := [(18, 1), (54, 1)] }, { coefficient := 1, powers := [(24, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (44, 1)] }, { coefficient := 1, powers := [(4, 1), (33, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (51, 1)] }, { coefficient := 1, powers := [(7, 1), (30, 1)] }, { coefficient := 1, powers := [(10, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (45, 1)] }, { coefficient := 1, powers := [(17, 1), (39, 1)] }, { coefficient := 1, powers := [(17, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (53, 1)] }, { coefficient := 1, powers := [(28, 1), (39, 1)] }, { coefficient := 1, powers := [(28, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1), (51, 1)] }, { coefficient := 1, powers := [(18, 1), (42, 1), (51, 1)] }, { coefficient := 1, powers := [(42, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1), (49, 1)] }, { coefficient := 1, powers := [(23, 1), (44, 1), (49, 1)] }, { coefficient := 1, powers := [(49, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1), (51, 1)] }, { coefficient := 1, powers := [(19, 1), (42, 1), (51, 1)] }, { coefficient := 1, powers := [(47, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (45, 1), (49, 1)] }, { coefficient := 1, powers := [(12, 1), (26, 1), (45, 1)] }, { coefficient := 1, powers := [(17, 1), (27, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (23, 1), (39, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1), (44, 1)] }, { coefficient := 1, powers := [(16, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (23, 1), (45, 1)] }, { coefficient := 1, powers := [(17, 1), (23, 1), (39, 1)] }, { coefficient := 1, powers := [(17, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (42, 1), (54, 1)] }, { coefficient := 1, powers := [(27, 1), (49, 1), (57, 1)] }, { coefficient := 1, powers := [(28, 1), (45, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (46, 1)] }, { coefficient := 1, powers := [(5, 1), (26, 1), (59, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1)] }, { coefficient := 1, powers := [(16, 1), (26, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (51, 1)] }, { coefficient := 1, powers := [(16, 1), (21, 1), (51, 1)] }, { coefficient := 1, powers := [(16, 1), (21, 1), (56, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (60, 1)] }, { coefficient := 1, powers := [(12, 1), (47, 1)] }, { coefficient := 1, powers := [(17, 1), (19, 1), (52, 1)] }, { coefficient := 1, powers := [(17, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (60, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (45, 1)] }, { coefficient := 1, powers := [(12, 1), (57, 1)] }, { coefficient := 1, powers := [(17, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (39, 1)] }, { coefficient := 1, powers := [(16, 1), (44, 1)] }, { coefficient := 1, powers := [(16, 1), (51, 1)] }, { coefficient := 1, powers := [(16, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1), (53, 1)] }, { coefficient := 1, powers := [(18, 1), (42, 1), (53, 1)] }, { coefficient := 1, powers := [(18, 1), (57, 1)] }, { coefficient := 1, powers := [(24, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1), (49, 1)] }, { coefficient := 1, powers := [(6, 1), (60, 1)] }, { coefficient := 1, powers := [(23, 1), (45, 1), (49, 1)] }, { coefficient := 1, powers := [(42, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1), (54, 1)] }, { coefficient := 1, powers := [(24, 1), (45, 1), (49, 1)] }, { coefficient := 1, powers := [(42, 1), (54, 1)] }, { coefficient := 1, powers := [(49, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1), (49, 1)] }, { coefficient := 1, powers := [(19, 1), (49, 1)] }, { coefficient := 1, powers := [(23, 1), (40, 1)] }, { coefficient := 1, powers := [(23, 1), (46, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1), (52, 1)] }, { coefficient := 1, powers := [(19, 1), (42, 1), (52, 1)] }, { coefficient := 1, powers := [(40, 1), (42, 1)] }, { coefficient := 1, powers := [(47, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1), (53, 1)] }, { coefficient := 1, powers := [(19, 1), (42, 1), (53, 1)] }, { coefficient := 1, powers := [(19, 1), (57, 1)] }, { coefficient := 1, powers := [(24, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (28, 1), (59, 1)] }, { coefficient := 1, powers := [(10, 1), (28, 1), (44, 1)] }, { coefficient := 1, powers := [(14, 1), (27, 1), (53, 1)] }, { coefficient := 1, powers := [(14, 1), (28, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (25, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (51, 1)] }, { coefficient := 1, powers := [(16, 1), (25, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (20, 1), (59, 1)] }, { coefficient := 1, powers := [(8, 1), (30, 1), (44, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (39, 1)] }, { coefficient := 1, powers := [(16, 1), (20, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (59, 1)] }, { coefficient := 1, powers := [(10, 1), (44, 1)] }, { coefficient := 1, powers := [(10, 1), (56, 1)] }, { coefficient := 1, powers := [(14, 1), (39, 1)] }, { coefficient := 1, powers := [(14, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (51, 1)] }, { coefficient := 1, powers := [(20, 1), (56, 1)] }, { coefficient := 1, powers := [(25, 1), (39, 1)] }, { coefficient := 1, powers := [(25, 1), (44, 1)] }, { coefficient := 1, powers := [(30, 1), (36, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (37, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (47, 1), (54, 1)] }, { coefficient := 1, powers := [(19, 1), (42, 1), (54, 1)] }, { coefficient := 1, powers := [(19, 1), (49, 1), (57, 1)] }, { coefficient := 1, powers := [(24, 1), (40, 1), (42, 1)] }, { coefficient := 1, powers := [(24, 1), (47, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (40, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (56, 1)] }, { coefficient := 1, powers := [(12, 1), (22, 1), (56, 1)] }, { coefficient := 1, powers := [(12, 1), (27, 1), (46, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1), (52, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (36, 1), (59, 1)] }, { coefficient := 1, powers := [(1, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(1, 1), (44, 1), (51, 1)] }, { coefficient := 1, powers := [(4, 1), (25, 1), (59, 1)] }, { coefficient := 1, powers := [(4, 1), (30, 1), (56, 1)] }, { coefficient := 1, powers := [(4, 1), (33, 1), (51, 1)] }, { coefficient := 1, powers := [(7, 1), (20, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (30, 1), (44, 1)] }, { coefficient := 1, powers := [(7, 1), (33, 1), (39, 1)] }, { coefficient := 1, powers := [(10, 1), (20, 1), (56, 1)] }, { coefficient := 1, powers := [(10, 1), (25, 1), (44, 1)] }, { coefficient := 1, powers := [(10, 1), (33, 1), (36, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1), (51, 1)] }, { coefficient := 1, powers := [(14, 1), (25, 1), (39, 1)] }, { coefficient := 1, powers := [(14, 1), (30, 1), (36, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (37, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (47, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (28, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (22, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1), (47, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (40, 1)] }, { coefficient := 1, powers := [(12, 1), (22, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1), (28, 1), (47, 1)] }, { coefficient := 1, powers := [(12, 1), (34, 1), (37, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (54, 1)] }, { coefficient := 1, powers := [(17, 1), (28, 1), (40, 1)] }, { coefficient := 1, powers := [(17, 1), (31, 1), (37, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (61, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(40, 1)] }],
  [{ coefficient := 1, powers := [(56, 1), (64, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(57, 1), (65, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(23, 1), (66, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(25, 1)] }],
  [{ coefficient := 1, powers := [(28, 1), (67, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(60, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 62 → SparsePoly (Fin 69) := ![
  [{ coefficient := 1, powers := [(4, 1), (34, 1), (39, 1), (54, 1)] }, { coefficient := 1, powers := [(4, 1), (34, 1), (44, 1), (54, 1)] }, { coefficient := 1, powers := [(4, 1), (34, 1), (51, 1), (54, 1)] }, { coefficient := 1, powers := [(4, 1), (34, 1), (54, 1), (56, 1)] }, { coefficient := 1, powers := [(7, 1), (34, 1), (39, 1), (54, 1)] }, { coefficient := 1, powers := [(10, 1), (34, 1), (36, 1), (54, 1)] }, { coefficient := -1, powers := [(14, 1), (34, 1), (36, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (31, 1), (47, 1), (56, 1)] }, { coefficient := -1, powers := [(7, 1), (31, 1), (44, 1), (47, 1)] }, { coefficient := -1, powers := [(10, 1), (31, 1), (36, 1), (47, 1)] }, { coefficient := 1, powers := [(14, 1), (31, 1), (36, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (20, 1), (24, 1), (34, 1), (54, 1), (56, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (31, 1), (47, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (10, 1), (34, 1), (42, 1), (54, 1), (56, 1), (65, 1)] }, { coefficient := 1, powers := [(8, 1), (10, 1), (31, 1), (42, 1), (47, 1), (51, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(22, 1), (57, 1), (66, 1)] }, { coefficient := -1, powers := [(27, 1), (46, 1), (57, 1), (64, 1), (66, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(22, 1), (45, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (19, 1), (26, 1), (53, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(17, 1), (21, 1), (31, 1), (37, 1), (51, 1), (62, 1)] }, { coefficient := -1, powers := [(17, 1), (21, 1), (31, 1), (37, 1), (56, 1), (62, 1)] }, { coefficient := -1, powers := [(17, 1), (27, 1), (31, 1), (37, 1), (62, 1)] }, { coefficient := -1, powers := [(22, 1), (42, 1), (54, 1), (61, 1)] }, { coefficient := 1, powers := [(22, 1), (49, 1), (57, 1), (66, 1)] }, { coefficient := 1, powers := [(27, 1), (46, 1), (49, 1), (57, 1), (64, 1), (66, 1)] }, { coefficient := -1, powers := [(28, 1), (47, 1), (49, 1), (61, 1)] }, { coefficient := -1, powers := [(34, 1), (37, 1), (49, 1), (61, 1)] }, { coefficient := -1, powers := [(34, 1), (37, 1), (49, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(31, 1), (37, 1), (64, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (54, 1), (57, 1), (59, 1), (64, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (45, 1), (57, 1), (59, 1), (64, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (17, 1), (19, 1), (53, 1), (62, 1)] }, { coefficient := 1, powers := [(5, 1), (57, 1), (59, 1), (64, 1)] }, { coefficient := 1, powers := [(16, 1), (46, 1), (57, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (20, 1), (34, 1), (54, 1), (56, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(31, 1), (37, 1), (51, 1), (64, 1), (66, 1)] }, { coefficient := -1, powers := [(31, 1), (37, 1), (56, 1), (64, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(28, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (10, 1), (34, 1), (54, 1), (56, 1), (65, 1)] }, { coefficient := -1, powers := [(8, 1), (10, 1), (31, 1), (47, 1), (51, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (22, 1), (54, 1), (61, 1)] }, { coefficient := 1, powers := [(17, 1), (24, 1), (31, 1), (37, 1), (51, 1), (65, 1), (66, 1)] }, { coefficient := -1, powers := [(17, 1), (31, 1), (37, 1), (53, 1), (65, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (44, 1), (49, 1), (53, 1)] }, { coefficient := 1, powers := [(16, 1), (28, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (28, 1), (47, 1), (61, 1)] }, { coefficient := 1, powers := [(16, 1), (34, 1), (37, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (22, 1), (45, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (34, 1), (39, 1), (54, 1)] }, { coefficient := -1, powers := [(5, 1), (34, 1), (44, 1), (54, 1)] }, { coefficient := -1, powers := [(5, 1), (34, 1), (51, 1), (54, 1)] }, { coefficient := -1, powers := [(5, 1), (34, 1), (54, 1), (56, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1), (47, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (34, 1), (44, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1), (44, 1), (47, 1)] }],
  [{ coefficient := -1, powers := [(23, 1), (31, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (14, 1), (20, 1), (34, 1), (54, 1), (67, 1)] }],
  [{ coefficient := -1, powers := [(17, 1), (24, 1), (31, 1), (37, 1), (65, 1), (66, 1)] }, { coefficient := 1, powers := [(17, 1), (31, 1), (37, 1), (53, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (42, 1), (46, 1), (53, 1)] }, { coefficient := 1, powers := [(2, 1), (47, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (49, 1), (53, 1)] }, { coefficient := 1, powers := [(2, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (19, 1), (53, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(31, 1), (37, 1), (42, 1), (64, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(31, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (57, 1), (59, 1), (64, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(52, 1), (57, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (18, 1), (31, 1), (37, 1), (62, 1)] }, { coefficient := 1, powers := [(17, 1), (23, 1), (31, 1), (37, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(28, 1)] }],
  [{ coefficient := 1, powers := [(22, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (31, 1), (37, 1), (42, 1), (64, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(17, 1), (31, 1), (37, 1), (51, 1), (65, 1)] }, { coefficient := 1, powers := [(17, 1), (31, 1), (37, 1), (65, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (46, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(16, 1), (22, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (42, 1), (44, 1), (53, 1)] }, { coefficient := -1, powers := [(2, 1), (45, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(16, 1), (28, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (49, 1), (51, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (20, 1), (34, 1), (54, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (34, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (31, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (20, 1), (28, 1), (34, 1), (54, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (14, 1), (34, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (10, 1), (31, 1), (47, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(57, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (34, 1), (54, 1)] }, { coefficient := -1, powers := [(8, 1), (31, 1), (47, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(16, 1), (22, 1), (42, 1), (54, 1)] }, { coefficient := -1, powers := [(16, 1), (28, 1), (47, 1), (49, 1)] }, { coefficient := -1, powers := [(16, 1), (34, 1), (37, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (34, 1), (36, 1), (54, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (39, 1), (44, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (39, 1), (54, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (44, 2), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (44, 1), (51, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (44, 1), (54, 1), (56, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1), (36, 1), (47, 1), (59, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1), (39, 1), (47, 1), (56, 1)] }, { coefficient := -1, powers := [(8, 1), (31, 1), (44, 1), (47, 1), (51, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (19, 1), (45, 1), (49, 1), (53, 1)] }, { coefficient := -1, powers := [(17, 1), (18, 1), (31, 1), (37, 1), (51, 1)] }, { coefficient := -1, powers := [(17, 1), (23, 1), (31, 1), (37, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (2, 1), (51, 1), (57, 1)] }, { coefficient := -1, powers := [(2, 1), (23, 1), (42, 1), (44, 1), (53, 1)] }, { coefficient := 1, powers := [(2, 1), (23, 1), (45, 1), (53, 1)] }, { coefficient := 1, powers := [(2, 1), (24, 1), (42, 1), (51, 1)] }, { coefficient := -1, powers := [(2, 1), (56, 1), (57, 1), (64, 1)] }, { coefficient := 1, powers := [(2, 1), (57, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1)] }, { coefficient := -1, powers := [(16, 1), (27, 1), (57, 1), (64, 1)] }, { coefficient := 1, powers := [(16, 1), (28, 1), (42, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (31, 1), (57, 1)] }, { coefficient := -1, powers := [(12, 1), (22, 1), (57, 1)] }, { coefficient := 1, powers := [(17, 1), (18, 1), (31, 1), (37, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (27, 1), (49, 1), (57, 1), (59, 1), (64, 1)] }, { coefficient := 1, powers := [(8, 1), (10, 1), (20, 1), (31, 1), (47, 1), (51, 1)] }, { coefficient := 1, powers := [(17, 1), (18, 1), (31, 1), (37, 1), (51, 1)] }, { coefficient := -1, powers := [(17, 1), (18, 1), (31, 1), (37, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (22, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1), (27, 1), (46, 1), (57, 1), (64, 1)] }, { coefficient := -1, powers := [(12, 1), (34, 1), (37, 1)] }, { coefficient := -1, powers := [(16, 1), (22, 1), (49, 1), (57, 1)] }, { coefficient := -1, powers := [(16, 1), (27, 1), (46, 1), (49, 1), (57, 1), (64, 1)] }, { coefficient := 1, powers := [(16, 1), (34, 1), (37, 1), (49, 1)] }, { coefficient := -1, powers := [(17, 1), (24, 1), (31, 1), (37, 1), (42, 1), (51, 1), (65, 1)] }, { coefficient := 1, powers := [(17, 1), (31, 1), (37, 1), (42, 1), (53, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (8, 1), (31, 1), (47, 1), (59, 1)] }, { coefficient := -1, powers := [(4, 1), (16, 1), (34, 1), (46, 1), (54, 1)] }, { coefficient := -1, powers := [(5, 1), (14, 1), (34, 1), (44, 1), (54, 1)] }, { coefficient := -1, powers := [(8, 1), (10, 1), (31, 1), (39, 1), (47, 1)] }, { coefficient := -1, powers := [(8, 1), (10, 1), (31, 1), (44, 1), (47, 1)] }, { coefficient := 1, powers := [(8, 1), (14, 1), (31, 1), (39, 1), (47, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (7, 1), (20, 1), (34, 1), (54, 1), (59, 1)] }, { coefficient := -1, powers := [(5, 1), (10, 1), (20, 1), (34, 1), (54, 1), (56, 1)] }, { coefficient := -1, powers := [(5, 1), (14, 1), (20, 1), (34, 1), (39, 1), (54, 1)] }, { coefficient := -1, powers := [(5, 1), (14, 1), (20, 1), (34, 1), (44, 1), (54, 1)] }, { coefficient := -1, powers := [(5, 1), (14, 1), (20, 1), (34, 1), (51, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (2, 1), (37, 1), (51, 1)] }, { coefficient := -1, powers := [(2, 1), (6, 1), (46, 1), (53, 1)] }, { coefficient := 1, powers := [(2, 1), (37, 1)] }]
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
    ¬ ∀ index : Fin 62,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component39.SelectedLeafB5_2_3_5_2.selectedHasNoCommonZero

end Krenn.Component39.SelectedLeafB5_2_3_5_2
