import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component39.SelectedLeafB4_4_7

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "7fd460d5b5d77e9aa20af2f185a326d7163e72742390bc46f25fb0c6ba83e70f"
def certificateSHA256 : String := "4f5c33940b89735e6807a9e4519702c49ffb3c2aabe14994ecb4891975c2d651"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 44 → Fin 670 := ![
  10,
  11,
  14,
  19,
  21,
  22,
  26,
  30,
  70,
  172,
  181,
  187,
  188,
  191,
  192,
  193,
  232,
  280,
  304,
  305,
  316,
  397,
  419,
  423,
  433,
  434,
  440,
  502,
  517,
  523,
  542,
  555,
  566,
  602,
  603,
  618,
  659,
  660,
  662,
  663,
  665,
  666,
  667,
  669
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 44 → SparsePoly (Fin 66) := ![
  [{ coefficient := 1, powers := [(5, 1), (33, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (30, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (20, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (31, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (31, 1)] }, { coefficient := 1, powers := [(14, 1), (21, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (24, 1)] }, { coefficient := 1, powers := [(16, 1), (18, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (18, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (42, 1)] }, { coefficient := 1, powers := [(17, 1), (18, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (54, 1)] }, { coefficient := 1, powers := [(28, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (42, 1)] }, { coefficient := 1, powers := [(26, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (53, 1)] }, { coefficient := 1, powers := [(28, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (24, 1), (45, 1)] }, { coefficient := 1, powers := [(10, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (42, 1), (53, 1)] }, { coefficient := 1, powers := [(20, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (44, 1)] }, { coefficient := 1, powers := [(4, 1), (33, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (51, 1)] }, { coefficient := 1, powers := [(7, 1), (30, 1)] }, { coefficient := 1, powers := [(10, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (45, 1)] }, { coefficient := 1, powers := [(17, 1), (39, 1)] }, { coefficient := 1, powers := [(17, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (23, 1), (45, 1)] }, { coefficient := 1, powers := [(17, 1), (23, 1), (39, 1)] }, { coefficient := 1, powers := [(17, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (47, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1)] }, { coefficient := 1, powers := [(16, 1), (26, 1), (47, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (52, 1)] }, { coefficient := 1, powers := [(12, 1), (21, 1), (56, 1)] }, { coefficient := 1, powers := [(12, 1), (27, 1)] }, { coefficient := 1, powers := [(16, 1), (21, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (59, 1)] }, { coefficient := 1, powers := [(16, 1), (24, 1), (39, 1)] }, { coefficient := 1, powers := [(16, 1), (24, 1), (44, 1)] }, { coefficient := 1, powers := [(16, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (60, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (45, 1)] }, { coefficient := 1, powers := [(12, 1), (57, 1)] }, { coefficient := 1, powers := [(17, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (54, 1)] }, { coefficient := 1, powers := [(28, 1), (40, 1)] }, { coefficient := 1, powers := [(28, 1), (46, 1), (49, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (25, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (30, 1), (56, 1)] }, { coefficient := 1, powers := [(3, 1), (33, 1), (51, 1)] }, { coefficient := 1, powers := [(25, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (31, 1), (56, 1)] }, { coefficient := 1, powers := [(7, 1), (31, 1), (44, 1)] }, { coefficient := 1, powers := [(14, 1), (27, 1), (52, 1)] }, { coefficient := 1, powers := [(14, 1), (31, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (25, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (51, 1)] }, { coefficient := 1, powers := [(16, 1), (25, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (20, 1), (59, 1)] }, { coefficient := 1, powers := [(8, 1), (30, 1), (44, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (39, 1)] }, { coefficient := 1, powers := [(16, 1), (20, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (19, 1), (56, 1)] }, { coefficient := 1, powers := [(12, 1), (46, 1)] }, { coefficient := 1, powers := [(16, 1), (19, 1), (52, 1)] }, { coefficient := 1, powers := [(16, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (42, 1), (53, 1)] }, { coefficient := 1, powers := [(22, 1), (57, 1)] }, { coefficient := 1, powers := [(28, 1), (47, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (59, 1)] }, { coefficient := 1, powers := [(10, 1), (44, 1)] }, { coefficient := 1, powers := [(10, 1), (56, 1)] }, { coefficient := 1, powers := [(14, 1), (39, 1)] }, { coefficient := 1, powers := [(14, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (51, 1)] }, { coefficient := 1, powers := [(20, 1), (56, 1)] }, { coefficient := 1, powers := [(25, 1), (39, 1)] }, { coefficient := 1, powers := [(25, 1), (44, 1)] }, { coefficient := 1, powers := [(30, 1), (36, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (42, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (21, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1), (42, 1)] }, { coefficient := 1, powers := [(12, 1), (21, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1), (28, 1), (42, 1)] }, { coefficient := 1, powers := [(17, 1), (21, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (36, 1), (59, 1)] }, { coefficient := 1, powers := [(1, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(1, 1), (44, 1), (51, 1)] }, { coefficient := 1, powers := [(4, 1), (25, 1), (59, 1)] }, { coefficient := 1, powers := [(4, 1), (30, 1), (56, 1)] }, { coefficient := 1, powers := [(4, 1), (33, 1), (51, 1)] }, { coefficient := 1, powers := [(7, 1), (20, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (30, 1), (44, 1)] }, { coefficient := 1, powers := [(7, 1), (33, 1), (39, 1)] }, { coefficient := 1, powers := [(10, 1), (20, 1), (56, 1)] }, { coefficient := 1, powers := [(10, 1), (25, 1), (44, 1)] }, { coefficient := 1, powers := [(10, 1), (33, 1), (36, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1), (51, 1)] }, { coefficient := 1, powers := [(14, 1), (25, 1), (39, 1)] }, { coefficient := 1, powers := [(14, 1), (30, 1), (36, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (37, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (47, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (28, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (22, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1), (47, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (40, 1)] }, { coefficient := 1, powers := [(12, 1), (22, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1), (28, 1), (47, 1)] }, { coefficient := 1, powers := [(12, 1), (34, 1), (37, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (54, 1)] }, { coefficient := 1, powers := [(17, 1), (28, 1), (40, 1)] }, { coefficient := 1, powers := [(17, 1), (31, 1), (37, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1)] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(39, 1)] }],
  [{ coefficient := 1, powers := [(40, 1)] }],
  [{ coefficient := 1, powers := [(55, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(57, 1), (65, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 44 → SparsePoly (Fin 66) := ![
  [{ coefficient := 1, powers := [(4, 1), (28, 1), (51, 1), (60, 1)] }, { coefficient := 1, powers := [(4, 1), (28, 1), (56, 1), (60, 1)] }, { coefficient := 1, powers := [(10, 1), (28, 1), (36, 1), (60, 1)] }, { coefficient := -1, powers := [(14, 1), (28, 1), (36, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (19, 1), (27, 1), (56, 1), (60, 1)] }, { coefficient := -1, powers := [(4, 1), (21, 1), (46, 1), (56, 1), (60, 1)] }, { coefficient := 1, powers := [(4, 1), (22, 1), (56, 1), (60, 1)] }, { coefficient := -1, powers := [(4, 1), (31, 1), (42, 1), (46, 1), (56, 1)] }, { coefficient := 1, powers := [(4, 1), (31, 1), (47, 1), (56, 1)] }, { coefficient := -1, powers := [(10, 1), (19, 1), (27, 1), (36, 1), (60, 1)] }, { coefficient := 1, powers := [(10, 1), (21, 1), (36, 1), (46, 1), (60, 1)] }, { coefficient := -1, powers := [(10, 1), (22, 1), (36, 1), (60, 1)] }, { coefficient := 1, powers := [(10, 1), (31, 1), (36, 1), (42, 1), (46, 1)] }, { coefficient := -1, powers := [(10, 1), (31, 1), (36, 1), (47, 1)] }, { coefficient := 1, powers := [(14, 1), (19, 1), (27, 1), (36, 1), (60, 1)] }, { coefficient := -1, powers := [(14, 1), (21, 1), (36, 1), (46, 1), (60, 1)] }, { coefficient := 1, powers := [(14, 1), (22, 1), (36, 1), (60, 1)] }, { coefficient := -1, powers := [(14, 1), (31, 1), (36, 1), (42, 1), (46, 1)] }, { coefficient := 1, powers := [(14, 1), (31, 1), (36, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (20, 1), (24, 1), (28, 1), (44, 1), (60, 1), (65, 1)] }, { coefficient := 1, powers := [(5, 1), (20, 1), (24, 1), (31, 1), (51, 1), (57, 1), (65, 1)] }, { coefficient := 1, powers := [(5, 1), (24, 1), (30, 1), (31, 1), (36, 1), (57, 1), (65, 1)] }, { coefficient := 1, powers := [(8, 1), (19, 1), (20, 1), (24, 1), (27, 1), (51, 1), (60, 1), (65, 1)] }, { coefficient := -1, powers := [(8, 1), (20, 1), (21, 1), (24, 1), (46, 1), (51, 1), (60, 1), (65, 1)] }, { coefficient := 1, powers := [(8, 1), (20, 1), (22, 1), (24, 1), (51, 1), (60, 1), (65, 1)] }, { coefficient := -1, powers := [(8, 1), (20, 1), (24, 1), (31, 1), (42, 1), (46, 1), (51, 1), (65, 1)] }, { coefficient := 1, powers := [(8, 1), (20, 1), (24, 1), (31, 1), (47, 1), (51, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (20, 1), (21, 1), (57, 1), (59, 1)] }, { coefficient := -1, powers := [(5, 1), (27, 1), (30, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (19, 1), (27, 1), (53, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (21, 1), (46, 1), (53, 1), (60, 1)] }, { coefficient := -1, powers := [(7, 1), (22, 1), (53, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (31, 1), (42, 1), (46, 1), (53, 1)] }, { coefficient := -1, powers := [(7, 1), (31, 1), (47, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (19, 1), (24, 1), (27, 1), (44, 1), (60, 1)] }, { coefficient := -1, powers := [(4, 1), (19, 1), (27, 1), (53, 1), (60, 1)] }, { coefficient := 1, powers := [(4, 1), (21, 1), (24, 1), (44, 1), (46, 1), (60, 1)] }, { coefficient := 1, powers := [(4, 1), (21, 1), (46, 1), (53, 1), (60, 1)] }, { coefficient := -1, powers := [(4, 1), (22, 1), (24, 1), (44, 1), (60, 1)] }, { coefficient := -1, powers := [(4, 1), (22, 1), (53, 1), (60, 1)] }, { coefficient := 1, powers := [(4, 1), (24, 1), (31, 1), (42, 1), (44, 1), (46, 1)] }, { coefficient := -1, powers := [(4, 1), (24, 1), (31, 1), (44, 1), (47, 1)] }, { coefficient := 1, powers := [(4, 1), (31, 1), (42, 1), (46, 1), (53, 1)] }, { coefficient := -1, powers := [(4, 1), (31, 1), (47, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (5, 1), (28, 1), (42, 1), (59, 1), (60, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (14, 1), (16, 1), (28, 1), (44, 1), (60, 1)] }, { coefficient := -1, powers := [(4, 1), (16, 1), (28, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (25, 1), (57, 1), (59, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (20, 1), (57, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (27, 1), (45, 1)] }],
  [{ coefficient := -1, powers := [(19, 1), (27, 1), (45, 1), (54, 1)] }, { coefficient := 1, powers := [(22, 1), (45, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(17, 1), (46, 1)] }],
  [{ coefficient := -1, powers := [(16, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (42, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (20, 1), (28, 1), (44, 1), (60, 1), (65, 1)] }, { coefficient := -1, powers := [(5, 1), (20, 1), (31, 1), (51, 1), (57, 1), (65, 1)] }, { coefficient := -1, powers := [(5, 1), (30, 1), (31, 1), (36, 1), (57, 1), (65, 1)] }, { coefficient := -1, powers := [(8, 1), (19, 1), (20, 1), (27, 1), (51, 1), (60, 1), (65, 1)] }, { coefficient := 1, powers := [(8, 1), (20, 1), (21, 1), (46, 1), (51, 1), (60, 1), (65, 1)] }, { coefficient := -1, powers := [(8, 1), (20, 1), (22, 1), (51, 1), (60, 1), (65, 1)] }, { coefficient := 1, powers := [(8, 1), (20, 1), (31, 1), (42, 1), (46, 1), (51, 1), (65, 1)] }, { coefficient := -1, powers := [(8, 1), (20, 1), (31, 1), (47, 1), (51, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (5, 1), (28, 1), (59, 1), (60, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (28, 1), (51, 1), (60, 1)] }, { coefficient := -1, powers := [(5, 1), (28, 1), (56, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (51, 1), (57, 1)] }, { coefficient := 1, powers := [(8, 1), (19, 1), (27, 1), (51, 1), (60, 1)] }, { coefficient := -1, powers := [(8, 1), (21, 1), (46, 1), (51, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (22, 1), (51, 1), (60, 1)] }, { coefficient := -1, powers := [(8, 1), (31, 1), (42, 1), (46, 1), (51, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1), (47, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (28, 1), (44, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(18, 1), (22, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (27, 1), (54, 1)] }, { coefficient := -1, powers := [(22, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(54, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (19, 1), (25, 1), (27, 1), (60, 1)] }, { coefficient := -1, powers := [(4, 1), (21, 1), (25, 1), (46, 1), (60, 1)] }, { coefficient := 1, powers := [(4, 1), (22, 1), (25, 1), (60, 1)] }, { coefficient := -1, powers := [(4, 1), (25, 1), (31, 1), (42, 1), (46, 1)] }, { coefficient := 1, powers := [(4, 1), (25, 1), (31, 1), (47, 1)] }],
  [{ coefficient := -1, powers := [(19, 1), (27, 1)] }],
  [{ coefficient := 1, powers := [(17, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (14, 1), (28, 1), (44, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (30, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (14, 1), (28, 1), (44, 1), (60, 1)] }, { coefficient := 1, powers := [(4, 1), (28, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (19, 1), (27, 1), (60, 1)] }, { coefficient := -1, powers := [(7, 1), (21, 1), (46, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (22, 1), (60, 1)] }, { coefficient := -1, powers := [(7, 1), (31, 1), (42, 1), (46, 1)] }, { coefficient := 1, powers := [(7, 1), (31, 1), (47, 1)] }],
  [{ coefficient := -1, powers := [(21, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(12, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (20, 1), (28, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (10, 1), (31, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (14, 1), (28, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (10, 1), (19, 1), (27, 1), (60, 1)] }, { coefficient := -1, powers := [(8, 1), (10, 1), (21, 1), (46, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (10, 1), (22, 1), (60, 1)] }, { coefficient := -1, powers := [(8, 1), (10, 1), (31, 1), (42, 1), (46, 1)] }, { coefficient := 1, powers := [(8, 1), (10, 1), (31, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(46, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (28, 1), (60, 1)] }, { coefficient := -1, powers := [(5, 1), (31, 1), (57, 1)] }, { coefficient := -1, powers := [(8, 1), (19, 1), (27, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (21, 1), (46, 1), (60, 1)] }, { coefficient := -1, powers := [(8, 1), (22, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1), (42, 1), (46, 1)] }, { coefficient := -1, powers := [(8, 1), (31, 1), (47, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(5, 1), (28, 1), (36, 1), (59, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (28, 1), (39, 1), (56, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (28, 1), (44, 1), (51, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (28, 1), (44, 1), (56, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (36, 1), (57, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (39, 1), (56, 1), (57, 1)] }, { coefficient := 1, powers := [(8, 1), (19, 1), (27, 1), (36, 1), (59, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (19, 1), (27, 1), (39, 1), (56, 1), (60, 1)] }, { coefficient := -1, powers := [(8, 1), (21, 1), (36, 1), (46, 1), (59, 1), (60, 1)] }, { coefficient := -1, powers := [(8, 1), (21, 1), (39, 1), (46, 1), (56, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (22, 1), (36, 1), (59, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (22, 1), (39, 1), (56, 1), (60, 1)] }, { coefficient := -1, powers := [(8, 1), (31, 1), (36, 1), (42, 1), (46, 1), (59, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1), (36, 1), (47, 1), (59, 1)] }, { coefficient := -1, powers := [(8, 1), (31, 1), (39, 1), (42, 1), (46, 1), (56, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1), (39, 1), (47, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [(19, 1), (52, 1), (57, 1)] }, { coefficient := 1, powers := [(37, 1), (60, 1)] }, { coefficient := 1, powers := [(40, 1), (57, 1)] }, { coefficient := -1, powers := [(42, 1), (46, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (16, 1), (19, 1), (24, 1), (25, 1), (27, 1), (60, 1)] }, { coefficient := 1, powers := [(4, 1), (16, 1), (21, 1), (24, 1), (25, 1), (46, 1), (60, 1)] }, { coefficient := -1, powers := [(4, 1), (16, 1), (22, 1), (24, 1), (25, 1), (60, 1)] }, { coefficient := 1, powers := [(4, 1), (16, 1), (24, 1), (25, 1), (31, 1), (42, 1), (46, 1)] }, { coefficient := -1, powers := [(4, 1), (16, 1), (24, 1), (25, 1), (31, 1), (47, 1)] }, { coefficient := 1, powers := [(5, 1), (7, 1), (28, 1), (33, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (7, 1), (31, 1), (33, 1), (57, 1)] }, { coefficient := -1, powers := [(5, 1), (10, 1), (25, 1), (31, 1), (57, 1)] }, { coefficient := -1, powers := [(5, 1), (14, 1), (20, 1), (28, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (14, 1), (25, 1), (31, 1), (57, 1)] }, { coefficient := -1, powers := [(8, 1), (10, 1), (19, 1), (25, 1), (27, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (10, 1), (21, 1), (25, 1), (46, 1), (60, 1)] }, { coefficient := -1, powers := [(8, 1), (10, 1), (22, 1), (25, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (10, 1), (25, 1), (31, 1), (42, 1), (46, 1)] }, { coefficient := -1, powers := [(8, 1), (10, 1), (25, 1), (31, 1), (47, 1)] }, { coefficient := 1, powers := [(8, 1), (14, 1), (19, 1), (25, 1), (27, 1), (60, 1)] }, { coefficient := -1, powers := [(8, 1), (14, 1), (21, 1), (25, 1), (46, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (14, 1), (22, 1), (25, 1), (60, 1)] }, { coefficient := -1, powers := [(8, 1), (14, 1), (25, 1), (31, 1), (42, 1), (46, 1)] }, { coefficient := 1, powers := [(8, 1), (14, 1), (25, 1), (31, 1), (47, 1)] }, { coefficient := 1, powers := [(17, 1), (18, 1), (22, 1), (54, 1)] }, { coefficient := -1, powers := [(17, 1), (19, 1), (23, 1), (27, 1), (54, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (23, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (34, 1)] }, { coefficient := 1, powers := [(16, 1), (21, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (5, 1), (25, 1), (31, 1), (57, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (5, 1), (20, 1), (28, 1), (59, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (10, 1), (20, 1), (28, 1), (44, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (10, 1), (20, 1), (31, 1), (51, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (10, 1), (30, 1), (31, 1), (36, 1), (57, 1)] }, { coefficient := 1, powers := [(8, 1), (10, 1), (19, 1), (20, 1), (27, 1), (51, 1), (60, 1)] }, { coefficient := -1, powers := [(8, 1), (10, 1), (20, 1), (21, 1), (46, 1), (51, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (10, 1), (20, 1), (22, 1), (51, 1), (60, 1)] }, { coefficient := -1, powers := [(8, 1), (10, 1), (20, 1), (31, 1), (42, 1), (46, 1), (51, 1)] }, { coefficient := 1, powers := [(8, 1), (10, 1), (20, 1), (31, 1), (47, 1), (51, 1)] }]
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
    ¬ ∀ index : Fin 44,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component39.SelectedLeafB4_4_7.selectedHasNoCommonZero

end Krenn.Component39.SelectedLeafB4_4_7
