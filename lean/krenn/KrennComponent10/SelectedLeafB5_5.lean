import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component10.SelectedLeafB5_5

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "384d3a16e8c783b30ed35c58c43e20f4ded909050cb136f5786947a580da15b7"
def certificateSHA256 : String := "5ee180fb34390c73966639ab8900578773c78b8dea5de43ccc726c3d059d511f"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 37 → Fin 641 := ![
  0,
  2,
  3,
  13,
  16,
  23,
  24,
  25,
  26,
  27,
  161,
  162,
  163,
  169,
  184,
  189,
  192,
  353,
  359,
  361,
  409,
  456,
  466,
  468,
  473,
  527,
  550,
  557,
  581,
  582,
  610,
  633,
  634,
  635,
  636,
  639,
  640
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 37 → SparsePoly (Fin 64) := ![
  [{ coefficient := 1, powers := [(3, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (32, 1)] }],
  [{ coefficient := 1, powers := [(15, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(26, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(28, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1)] }, { coefficient := 1, powers := [(24, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (48, 1)] }, { coefficient := 1, powers := [(24, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (52, 1)] }, { coefficient := 1, powers := [(19, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (58, 1)] }, { coefficient := 1, powers := [(17, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (19, 1)] }, { coefficient := 1, powers := [(17, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (43, 1)] }, { coefficient := 1, powers := [(27, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (41, 1), (55, 1)] }, { coefficient := 1, powers := [(41, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (46, 1)] }, { coefficient := 1, powers := [(16, 1), (40, 1)] }, { coefficient := 1, powers := [(16, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (53, 1)] }, { coefficient := 1, powers := [(29, 1), (41, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (36, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (24, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (19, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (23, 1), (58, 1)] }, { coefficient := 1, powers := [(23, 1)] }, { coefficient := 1, powers := [(27, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1)] }, { coefficient := 1, powers := [(24, 1), (40, 1), (43, 1)] }, { coefficient := 1, powers := [(24, 1), (46, 1)] }, { coefficient := 1, powers := [(43, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (53, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1)] }, { coefficient := 1, powers := [(12, 1), (29, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (35, 1)] }, { coefficient := 1, powers := [(11, 1), (27, 1), (46, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1), (40, 1)] }, { coefficient := 1, powers := [(16, 1), (28, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (40, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(43, 1), (52, 1)] }, { coefficient := 1, powers := [(56, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (23, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (32, 1), (48, 1)] }, { coefficient := 1, powers := [(7, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(16, 1), (28, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (43, 1), (52, 1)] }, { coefficient := 1, powers := [(23, 1), (56, 1)] }, { coefficient := 1, powers := [(29, 1), (48, 1)] }, { coefficient := 1, powers := [(35, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (51, 1)] }, { coefficient := 1, powers := [(3, 1), (58, 1)] }, { coefficient := 1, powers := [(19, 1), (51, 1)] }, { coefficient := 1, powers := [(19, 1), (55, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(21, 1), (51, 1)] }, { coefficient := 1, powers := [(21, 1), (55, 1)] }, { coefficient := 1, powers := [(26, 1), (40, 1)] }, { coefficient := 1, powers := [(26, 1), (45, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (36, 1), (58, 1)] }, { coefficient := 1, powers := [(0, 1)] }, { coefficient := 1, powers := [(3, 1), (24, 1), (58, 1)] }, { coefficient := 1, powers := [(6, 1), (19, 1), (58, 1)] }, { coefficient := 1, powers := [(19, 1)] }, { coefficient := 1, powers := [(24, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (35, 1), (51, 1)] }, { coefficient := 1, powers := [(7, 1), (35, 1), (40, 1)] }, { coefficient := 1, powers := [(11, 1), (28, 1), (46, 1)] }, { coefficient := 1, powers := [(11, 1), (35, 1), (37, 1)] }, { coefficient := 1, powers := [(16, 1), (28, 1), (40, 1)] }, { coefficient := 1, powers := [(16, 1), (28, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (37, 1), (58, 1)] }, { coefficient := 1, powers := [(1, 1), (40, 1), (55, 1)] }, { coefficient := 1, powers := [(1, 1), (45, 1), (51, 1)] }, { coefficient := 1, powers := [(4, 1), (26, 1), (58, 1)] }, { coefficient := 1, powers := [(4, 1), (31, 1), (55, 1)] }, { coefficient := 1, powers := [(4, 1), (34, 1), (51, 1)] }, { coefficient := 1, powers := [(7, 1), (21, 1), (58, 1)] }, { coefficient := 1, powers := [(7, 1), (31, 1), (45, 1)] }, { coefficient := 1, powers := [(7, 1), (34, 1), (40, 1)] }, { coefficient := 1, powers := [(11, 1), (21, 1), (55, 1)] }, { coefficient := 1, powers := [(11, 1), (26, 1), (45, 1)] }, { coefficient := 1, powers := [(11, 1), (34, 1), (37, 1)] }, { coefficient := 1, powers := [(15, 1), (21, 1), (51, 1)] }, { coefficient := 1, powers := [(15, 1), (26, 1), (40, 1)] }, { coefficient := 1, powers := [(15, 1), (31, 1), (37, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (41, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (48, 1), (53, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (53, 1)] }, { coefficient := 1, powers := [(8, 1), (23, 1), (59, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (48, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(12, 1), (23, 1), (56, 1)] }, { coefficient := 1, powers := [(12, 1), (29, 1), (48, 1)] }, { coefficient := 1, powers := [(12, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (53, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (41, 1)] }, { coefficient := 1, powers := [(18, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (60, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1)] }],
  [{ coefficient := 1, powers := [(40, 1)] }],
  [{ coefficient := 1, powers := [(41, 1), (63, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 37 → SparsePoly (Fin 64) := ![
  [{ coefficient := -1, powers := [(2, 1), (24, 1), (38, 1), (51, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (24, 1), (38, 1), (58, 1), (60, 1)] }, { coefficient := -1, powers := [(2, 1), (38, 1), (58, 1)] }, { coefficient := -1, powers := [(5, 1), (24, 1), (29, 1), (51, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (24, 1), (29, 1), (58, 1), (60, 1)] }, { coefficient := -1, powers := [(5, 1), (29, 1), (58, 1)] }],
  [{ coefficient := 2, powers := [(5, 1), (7, 1), (21, 1), (23, 1), (53, 1), (58, 2), (63, 1)] }, { coefficient := 2, powers := [(5, 1), (7, 1), (23, 1), (31, 1), (45, 1), (53, 1), (58, 1), (63, 1)] }, { coefficient := -2, powers := [(8, 1), (23, 1), (58, 1)] }],
  [{ coefficient := -2, powers := [(5, 1), (21, 1), (48, 1), (53, 1), (58, 1), (63, 1)] }, { coefficient := -2, powers := [(5, 1), (31, 1), (45, 1), (48, 1), (53, 1), (63, 1)] }],
  [{ coefficient := -2, powers := [(5, 1), (21, 1), (35, 1), (53, 1), (55, 1), (63, 1)] }, { coefficient := -2, powers := [(5, 1), (34, 1), (35, 1), (37, 1), (53, 1), (63, 1)] }],
  [{ coefficient := 2, powers := [(5, 1), (27, 1), (31, 1), (51, 2), (53, 1), (63, 1)] }, { coefficient := 2, powers := [(5, 1), (27, 1), (31, 1), (51, 1), (53, 1), (55, 1), (63, 1)] }, { coefficient := 2, powers := [(5, 1), (27, 1), (34, 1), (51, 2), (53, 1), (63, 1)] }],
  [{ coefficient := -2, powers := [(5, 1), (11, 1), (35, 1), (51, 1)] }],
  [{ coefficient := -2, powers := [(17, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (3, 1), (38, 1), (51, 1), (58, 1), (59, 1), (63, 1)] }, { coefficient := -1, powers := [(2, 1), (3, 1), (38, 1), (58, 1), (59, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(2, 1), (38, 1), (51, 1), (59, 1), (63, 1)] }, { coefficient := -1, powers := [(2, 1), (38, 1), (59, 1), (60, 1), (63, 1)] }, { coefficient := 2, powers := [(2, 1), (41, 1), (46, 1), (52, 1), (63, 1)] }, { coefficient := 1, powers := [(3, 1), (5, 1), (29, 1), (51, 1), (58, 1), (59, 1), (63, 1)] }, { coefficient := -1, powers := [(3, 1), (5, 1), (29, 1), (58, 1), (59, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(3, 1), (8, 1), (35, 1), (41, 1), (51, 1), (58, 1), (63, 1)] }, { coefficient := -2, powers := [(3, 1), (8, 1), (35, 1), (41, 1), (58, 1), (60, 1), (63, 1)] }, { coefficient := -2, powers := [(5, 1), (7, 1), (21, 1), (27, 1), (47, 1), (53, 1), (58, 1), (59, 1), (60, 1), (63, 2)] }, { coefficient := -2, powers := [(5, 1), (7, 1), (27, 1), (31, 1), (45, 1), (47, 1), (53, 1), (59, 1), (60, 1), (63, 2)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (51, 1), (59, 1), (63, 1)] }, { coefficient := -1, powers := [(5, 1), (29, 1), (59, 1), (60, 1), (63, 1)] }, { coefficient := 2, powers := [(5, 1), (32, 1), (46, 1), (52, 1), (63, 1)] }, { coefficient := -1, powers := [(6, 1), (8, 1), (35, 1), (41, 1), (51, 1), (58, 1), (63, 1)] }, { coefficient := 1, powers := [(6, 1), (8, 1), (35, 1), (41, 1), (58, 1), (60, 1), (63, 1)] }, { coefficient := 2, powers := [(8, 1), (27, 1), (47, 1), (59, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (36, 1), (41, 1), (51, 1), (58, 1), (63, 1)] }, { coefficient := -1, powers := [(8, 1), (35, 1), (36, 1), (41, 1), (58, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (41, 1), (51, 1), (63, 1)] }, { coefficient := -1, powers := [(8, 1), (35, 1), (41, 1), (60, 1), (63, 1)] }, { coefficient := -2, powers := [(12, 1), (27, 1), (48, 1), (52, 1), (60, 1), (63, 1)] }, { coefficient := 2, powers := [(12, 1), (29, 1), (48, 1), (60, 1), (63, 1)] }],
  [{ coefficient := 2, powers := [(4, 1), (5, 1), (35, 1), (53, 1), (58, 1), (63, 1)] }, { coefficient := -2, powers := [(5, 1), (15, 1), (35, 1), (45, 1), (53, 1), (63, 1)] }],
  [{ coefficient := -2, powers := [(5, 1), (16, 1), (21, 1), (53, 1), (58, 1), (63, 1)] }, { coefficient := -2, powers := [(5, 1), (16, 1), (31, 1), (45, 1), (53, 1), (63, 1)] }, { coefficient := -2, powers := [(5, 1), (16, 1), (31, 1), (51, 1), (53, 1), (63, 1)] }, { coefficient := -2, powers := [(5, 1), (16, 1), (31, 1), (53, 1), (55, 1), (63, 1)] }, { coefficient := -2, powers := [(5, 1), (16, 1), (34, 1), (51, 1), (53, 1), (63, 1)] }],
  [{ coefficient := 2, powers := [(5, 1), (7, 1), (21, 1), (27, 1), (53, 1), (58, 1), (59, 1), (60, 1), (63, 1)] }, { coefficient := 2, powers := [(5, 1), (7, 1), (27, 1), (31, 1), (45, 1), (53, 1), (59, 1), (60, 1), (63, 1)] }, { coefficient := -2, powers := [(8, 1), (27, 1), (59, 1), (60, 1)] }],
  [{ coefficient := 2, powers := [(12, 1), (27, 1), (52, 1), (60, 1)] }, { coefficient := -2, powers := [(12, 1), (29, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (17, 1), (35, 1), (41, 1), (60, 1)] }, { coefficient := -1, powers := [(17, 1), (35, 1), (36, 1), (41, 1), (51, 1)] }, { coefficient := 1, powers := [(17, 1), (35, 1), (36, 1), (41, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (3, 1), (35, 1), (41, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (35, 1), (36, 1), (41, 1), (51, 1)] }, { coefficient := -1, powers := [(0, 1), (35, 1), (36, 1), (41, 1), (60, 1)] }, { coefficient := 1, powers := [(3, 1), (24, 1), (35, 1), (41, 1), (60, 1)] }, { coefficient := 1, powers := [(6, 1), (19, 1), (35, 1), (41, 1), (51, 1)] }, { coefficient := -1, powers := [(6, 1), (19, 1), (35, 1), (41, 1), (60, 1)] }, { coefficient := 1, powers := [(6, 1), (24, 1), (35, 1), (41, 1), (51, 1)] }, { coefficient := -1, powers := [(6, 1), (24, 1), (35, 1), (41, 1), (60, 1)] }, { coefficient := -1, powers := [(24, 1), (35, 1), (36, 1), (41, 1), (51, 1)] }, { coefficient := 1, powers := [(24, 1), (35, 1), (36, 1), (41, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (35, 1), (41, 1), (52, 1), (60, 1)] }, { coefficient := -1, powers := [(6, 1), (35, 1), (41, 1), (51, 1), (52, 1)] }, { coefficient := 1, powers := [(6, 1), (35, 1), (41, 1), (52, 1), (60, 1)] }, { coefficient := 1, powers := [(35, 1), (36, 1), (41, 1), (51, 1), (52, 1)] }, { coefficient := -1, powers := [(35, 1), (36, 1), (41, 1), (52, 1), (60, 1)] }],
  [{ coefficient := -2, powers := [(12, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (19, 1), (38, 1), (59, 1), (60, 1), (63, 1)] }, { coefficient := -1, powers := [(5, 1), (19, 1), (29, 1), (59, 1), (60, 1), (63, 1)] }, { coefficient := -1, powers := [(8, 1), (19, 1), (35, 1), (41, 1), (60, 1), (63, 1)] }],
  [{ coefficient := -2, powers := [(5, 1), (27, 1), (31, 1), (51, 1), (53, 1)] }, { coefficient := -2, powers := [(5, 1), (27, 1), (31, 1), (53, 1), (55, 1)] }, { coefficient := -2, powers := [(5, 1), (27, 1), (34, 1), (51, 1), (53, 1)] }, { coefficient := 2, powers := [(5, 1), (28, 1), (31, 1), (53, 1)] }],
  [{ coefficient := 2, powers := [(18, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (51, 1), (58, 1)] }, { coefficient := -1, powers := [(2, 1), (38, 1), (58, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (51, 1), (58, 1)] }, { coefficient := -1, powers := [(5, 1), (29, 1), (58, 1), (60, 1)] }],
  [{ coefficient := -2, powers := [(5, 1), (7, 1), (21, 1), (53, 1), (58, 1), (59, 1), (63, 1)] }, { coefficient := -2, powers := [(5, 1), (7, 1), (31, 1), (45, 1), (53, 1), (59, 1), (63, 1)] }, { coefficient := 2, powers := [(8, 1), (59, 1)] }],
  [{ coefficient := -2, powers := [(2, 1), (41, 1), (52, 1)] }, { coefficient := -2, powers := [(5, 1), (32, 1), (52, 1)] }],
  [{ coefficient := 2, powers := [(48, 1)] }],
  [{ coefficient := 2, powers := [(5, 1), (31, 1), (51, 1), (53, 1)] }, { coefficient := 2, powers := [(5, 1), (31, 1), (53, 1), (55, 1)] }, { coefficient := 2, powers := [(5, 1), (34, 1), (51, 1), (53, 1)] }],
  [{ coefficient := 2, powers := [(2, 1), (41, 1)] }, { coefficient := 2, powers := [(5, 1), (32, 1)] }],
  [{ coefficient := 2, powers := [(5, 1), (21, 1), (53, 1), (58, 1), (63, 1)] }, { coefficient := 2, powers := [(5, 1), (31, 1), (45, 1), (53, 1), (63, 1)] }],
  [{ coefficient := 2, powers := [(12, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (59, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (41, 1)] }],
  [{ coefficient := 2, powers := [(5, 1), (11, 1), (35, 1), (53, 1)] }, { coefficient := 2, powers := [(5, 1), (15, 1), (35, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (38, 1), (51, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (38, 1), (59, 1), (60, 1)] }, { coefficient := -1, powers := [(5, 1), (29, 1), (51, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (59, 1), (60, 1)] }, { coefficient := -1, powers := [(8, 1), (35, 1), (41, 1), (51, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (41, 1), (60, 1)] }],
  [{ coefficient := -2, powers := [(5, 1), (31, 1), (53, 1)] }],
  [{ coefficient := -2, powers := [(5, 1), (35, 1), (53, 1)] }],
  [{ coefficient := -2, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (19, 1), (38, 1), (41, 1), (55, 1), (59, 1), (63, 1)] }, { coefficient := -1, powers := [(2, 1), (38, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (8, 1), (35, 1), (41, 1), (58, 1)] }, { coefficient := -2, powers := [(5, 1), (7, 1), (21, 1), (27, 1), (47, 1), (53, 1), (58, 1), (59, 1), (63, 1)] }, { coefficient := -2, powers := [(5, 1), (7, 1), (27, 1), (31, 1), (45, 1), (47, 1), (53, 1), (59, 1), (63, 1)] }, { coefficient := 1, powers := [(5, 1), (19, 1), (29, 1), (41, 1), (55, 1), (59, 1), (63, 1)] }, { coefficient := -1, powers := [(5, 1), (29, 1), (59, 1)] }, { coefficient := 1, powers := [(8, 1), (19, 1), (35, 1), (41, 2), (55, 1), (63, 1)] }, { coefficient := 2, powers := [(8, 1), (27, 1), (47, 1), (59, 1)] }, { coefficient := -1, powers := [(8, 1), (35, 1), (41, 1)] }, { coefficient := -2, powers := [(12, 1), (27, 1), (48, 1), (52, 1)] }, { coefficient := 2, powers := [(12, 1), (29, 1), (48, 1)] }],
  [{ coefficient := 2, powers := [(5, 1), (35, 1), (37, 1), (53, 1), (58, 1)] }, { coefficient := 2, powers := [(5, 1), (35, 1), (45, 1), (51, 1), (53, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (2, 1), (41, 1), (56, 1)] }, { coefficient := -2, powers := [(0, 1), (5, 1), (32, 1), (56, 1)] }, { coefficient := 2, powers := [(1, 1), (5, 1), (35, 1), (53, 1), (55, 1)] }, { coefficient := 2, powers := [(2, 1), (24, 1), (41, 1), (43, 1), (52, 1)] }, { coefficient := 2, powers := [(5, 1), (7, 1), (31, 1), (35, 1), (53, 1)] }, { coefficient := 2, powers := [(5, 1), (7, 1), (34, 1), (35, 1), (53, 1)] }, { coefficient := -2, powers := [(5, 1), (11, 1), (26, 1), (35, 1), (53, 1)] }, { coefficient := 2, powers := [(5, 1), (24, 1), (32, 1), (43, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (3, 1), (24, 1), (38, 1), (51, 1), (58, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (3, 1), (24, 1), (38, 1), (58, 1), (59, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (19, 1), (38, 1), (55, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (19, 1), (38, 1), (59, 1), (60, 1)] }, { coefficient := -1, powers := [(2, 1), (24, 1), (38, 1), (51, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (24, 1), (38, 1), (59, 1), (60, 1)] }, { coefficient := -2, powers := [(2, 1), (24, 1), (41, 1), (46, 1), (52, 1)] }, { coefficient := -1, powers := [(3, 1), (5, 1), (24, 1), (29, 1), (51, 1), (58, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (5, 1), (24, 1), (29, 1), (58, 1), (59, 1), (60, 1)] }, { coefficient := -1, powers := [(3, 1), (8, 1), (24, 1), (35, 1), (41, 1), (51, 1), (58, 1)] }, { coefficient := 2, powers := [(3, 1), (8, 1), (24, 1), (35, 1), (41, 1), (58, 1), (60, 1)] }, { coefficient := -2, powers := [(4, 1), (5, 1), (26, 1), (35, 1), (53, 1), (58, 1)] }, { coefficient := 2, powers := [(5, 1), (7, 1), (21, 1), (24, 1), (27, 1), (47, 1), (53, 1), (58, 1), (59, 1), (60, 1), (63, 1)] }, { coefficient := -2, powers := [(5, 1), (7, 1), (21, 1), (35, 1), (53, 1), (58, 1)] }, { coefficient := 2, powers := [(5, 1), (7, 1), (24, 1), (27, 1), (31, 1), (45, 1), (47, 1), (53, 1), (59, 1), (60, 1), (63, 1)] }, { coefficient := -2, powers := [(5, 1), (7, 1), (31, 1), (35, 1), (45, 1), (53, 1)] }, { coefficient := 2, powers := [(5, 1), (15, 1), (21, 1), (35, 1), (53, 1), (55, 1)] }, { coefficient := 2, powers := [(5, 1), (15, 1), (26, 1), (35, 1), (45, 1), (53, 1)] }, { coefficient := 2, powers := [(5, 1), (15, 1), (34, 1), (35, 1), (37, 1), (53, 1)] }, { coefficient := -2, powers := [(5, 1), (16, 1), (27, 1), (31, 1), (51, 2), (53, 1)] }, { coefficient := -2, powers := [(5, 1), (16, 1), (27, 1), (31, 1), (51, 1), (53, 1), (55, 1)] }, { coefficient := -2, powers := [(5, 1), (16, 1), (27, 1), (34, 1), (51, 2), (53, 1)] }, { coefficient := 2, powers := [(5, 1), (16, 1), (28, 1), (31, 1), (51, 1), (53, 1)] }, { coefficient := 2, powers := [(5, 1), (16, 1), (28, 1), (31, 1), (53, 1), (55, 1)] }, { coefficient := 2, powers := [(5, 1), (16, 1), (28, 1), (34, 1), (51, 1), (53, 1)] }, { coefficient := 1, powers := [(5, 1), (19, 1), (29, 1), (55, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (19, 1), (29, 1), (59, 1), (60, 1)] }, { coefficient := -1, powers := [(5, 1), (24, 1), (29, 1), (51, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (24, 1), (29, 1), (59, 1), (60, 1)] }, { coefficient := -2, powers := [(5, 1), (24, 1), (32, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(6, 1), (8, 1), (24, 1), (35, 1), (41, 1), (51, 1), (58, 1)] }, { coefficient := -1, powers := [(6, 1), (8, 1), (24, 1), (35, 1), (41, 1), (58, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (19, 1), (35, 1), (41, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (19, 1), (35, 1), (41, 1), (60, 1)] }, { coefficient := -2, powers := [(8, 1), (24, 1), (27, 1), (47, 1), (59, 1), (60, 1)] }, { coefficient := -1, powers := [(8, 1), (24, 1), (35, 1), (36, 1), (41, 1), (51, 1), (58, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (35, 1), (36, 1), (41, 1), (58, 1), (60, 1)] }, { coefficient := -1, powers := [(8, 1), (24, 1), (35, 1), (41, 1), (51, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (35, 1), (41, 1), (60, 1)] }, { coefficient := 2, powers := [(12, 1), (24, 1), (27, 1), (48, 1), (52, 1), (60, 1)] }, { coefficient := -2, powers := [(12, 1), (24, 1), (29, 1), (48, 1), (60, 1)] }]
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
    (values : Fin 64 → R) :
    ¬ ∀ index : Fin 37,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((2 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (2 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (2 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component10.SelectedLeafB5_5.selectedHasNoCommonZero

end Krenn.Component10.SelectedLeafB5_5
