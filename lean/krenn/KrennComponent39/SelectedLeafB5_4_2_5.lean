import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component39.SelectedLeafB5_4_2_5

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "ea2db3e99a670d0016f4fef8d0445934bf46b53165a9cff67ef6ff9e1b4793da"
def certificateSHA256 : String := "065817903051ee9f548fe246a2b78231c2be26f5ab4aa74d3086146b9973d6d4"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 53 → Fin 673 := ![
  21,
  26,
  180,
  181,
  184,
  187,
  188,
  189,
  190,
  192,
  197,
  277,
  300,
  301,
  302,
  303,
  304,
  305,
  316,
  318,
  319,
  342,
  365,
  397,
  419,
  422,
  430,
  434,
  439,
  463,
  468,
  470,
  475,
  515,
  536,
  570,
  580,
  602,
  603,
  619,
  630,
  633,
  659,
  660,
  661,
  662,
  663,
  665,
  666,
  669,
  670,
  671,
  672
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 53 → SparsePoly (Fin 67) := ![
  [{ coefficient := 1, powers := [(16, 1), (20, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (23, 1)] }, { coefficient := 1, powers := [(16, 1), (18, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (24, 1)] }, { coefficient := 1, powers := [(16, 1), (18, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (45, 1)] }, { coefficient := 1, powers := [(17, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (18, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (42, 1)] }, { coefficient := 1, powers := [(17, 1), (18, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (47, 1)] }, { coefficient := 1, powers := [(17, 1), (19, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (45, 1)] }, { coefficient := -1, powers := [(27, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (42, 1)] }, { coefficient := 1, powers := [(26, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(30, 1), (37, 1)] }, { coefficient := 1, powers := [(33, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (23, 1), (47, 1)] }, { coefficient := 1, powers := [(17, 1), (19, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1)] }, { coefficient := 1, powers := [(18, 1), (42, 1)] }, { coefficient := 1, powers := [(23, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (42, 1)] }, { coefficient := 1, powers := [(23, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (49, 1)] }, { coefficient := 1, powers := [(18, 1), (49, 1)] }, { coefficient := 1, powers := [(23, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (54, 1)] }, { coefficient := 1, powers := [(18, 1), (54, 1)] }, { coefficient := 1, powers := [(24, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (44, 1)] }, { coefficient := 1, powers := [(4, 1), (33, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (51, 1)] }, { coefficient := 1, powers := [(7, 1), (30, 1)] }, { coefficient := 1, powers := [(10, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (45, 1)] }, { coefficient := 1, powers := [(17, 1), (39, 1)] }, { coefficient := 1, powers := [(17, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (53, 1)] }, { coefficient := 1, powers := [(28, 1), (39, 1)] }, { coefficient := 1, powers := [(28, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1), (51, 1)] }, { coefficient := 1, powers := [(18, 1), (42, 1), (51, 1)] }, { coefficient := 1, powers := [(42, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (42, 1), (51, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1), (42, 1)] }, { coefficient := 1, powers := [(17, 1), (21, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (22, 1), (59, 1)] }, { coefficient := 1, powers := [(22, 1)] }, { coefficient := 1, powers := [(26, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (23, 1), (45, 1)] }, { coefficient := 1, powers := [(17, 1), (23, 1), (39, 1)] }, { coefficient := 1, powers := [(17, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (47, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1)] }, { coefficient := 1, powers := [(16, 1), (26, 1), (47, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (51, 1)] }, { coefficient := 1, powers := [(16, 1), (21, 1), (51, 1)] }, { coefficient := 1, powers := [(16, 1), (21, 1), (56, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (60, 1)] }, { coefficient := 1, powers := [(12, 1), (47, 1)] }, { coefficient := 1, powers := [(17, 1), (19, 1), (52, 1)] }, { coefficient := 1, powers := [(17, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (60, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (45, 1)] }, { coefficient := 1, powers := [(12, 1), (57, 1)] }, { coefficient := 1, powers := [(17, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (39, 1)] }, { coefficient := 1, powers := [(16, 1), (44, 1)] }, { coefficient := 1, powers := [(16, 1), (51, 1)] }, { coefficient := 1, powers := [(16, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1), (54, 1)] }, { coefficient := 1, powers := [(24, 1), (45, 1), (49, 1)] }, { coefficient := 1, powers := [(42, 1), (54, 1)] }, { coefficient := 1, powers := [(49, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1), (54, 1)] }, { coefficient := 1, powers := [(19, 1), (54, 1)] }, { coefficient := 1, powers := [(24, 1), (40, 1)] }, { coefficient := 1, powers := [(24, 1), (46, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1), (52, 1)] }, { coefficient := 1, powers := [(19, 1), (42, 1), (52, 1)] }, { coefficient := 1, powers := [(40, 1), (42, 1)] }, { coefficient := 1, powers := [(47, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (37, 1), (59, 1)] }, { coefficient := 1, powers := [(1, 1), (46, 1), (53, 1)] }, { coefficient := 1, powers := [(10, 1), (33, 1), (37, 1)] }, { coefficient := 1, powers := [(14, 1), (30, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (28, 1), (59, 1)] }, { coefficient := 1, powers := [(10, 1), (28, 1), (44, 1)] }, { coefficient := 1, powers := [(14, 1), (27, 1), (53, 1)] }, { coefficient := 1, powers := [(14, 1), (28, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (34, 1), (39, 1)] }, { coefficient := 1, powers := [(26, 1), (39, 1), (42, 1)] }, { coefficient := 1, powers := [(26, 1), (45, 1)] }, { coefficient := 1, powers := [(27, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (42, 1), (53, 1)] }, { coefficient := 1, powers := [(27, 1), (57, 1)] }, { coefficient := 1, powers := [(28, 1), (39, 1), (42, 1)] }, { coefficient := 1, powers := [(28, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1)] }, { coefficient := 1, powers := [(6, 1), (59, 1)] }, { coefficient := 1, powers := [(23, 1), (39, 1)] }, { coefficient := 1, powers := [(23, 1), (44, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(4, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (59, 1)] }, { coefficient := 1, powers := [(10, 1), (44, 1)] }, { coefficient := 1, powers := [(10, 1), (56, 1)] }, { coefficient := 1, powers := [(14, 1), (39, 1)] }, { coefficient := 1, powers := [(14, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (51, 1)] }, { coefficient := 1, powers := [(20, 1), (56, 1)] }, { coefficient := 1, powers := [(25, 1), (39, 1)] }, { coefficient := 1, powers := [(25, 1), (44, 1)] }, { coefficient := 1, powers := [(30, 1), (36, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (45, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (27, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1), (45, 1)] }, { coefficient := 1, powers := [(12, 1), (27, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1), (28, 1), (45, 1)] }, { coefficient := 1, powers := [(17, 1), (27, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (24, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (19, 1), (60, 1)] }, { coefficient := 1, powers := [(12, 1), (19, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (47, 1)] }, { coefficient := 1, powers := [(17, 1), (19, 1), (54, 1)] }, { coefficient := 1, powers := [(17, 1), (24, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (22, 1), (60, 1)] }, { coefficient := 1, powers := [(6, 1), (31, 1), (47, 1)] }, { coefficient := 1, powers := [(6, 1), (34, 1), (40, 1)] }, { coefficient := 1, powers := [(22, 1), (42, 1), (49, 1)] }, { coefficient := 1, powers := [(26, 1), (40, 1), (42, 1)] }, { coefficient := 1, powers := [(26, 1), (47, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (36, 1), (59, 1)] }, { coefficient := 1, powers := [(1, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(1, 1), (44, 1), (51, 1)] }, { coefficient := 1, powers := [(4, 1), (25, 1), (59, 1)] }, { coefficient := 1, powers := [(4, 1), (30, 1), (56, 1)] }, { coefficient := 1, powers := [(4, 1), (33, 1), (51, 1)] }, { coefficient := 1, powers := [(7, 1), (20, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (30, 1), (44, 1)] }, { coefficient := 1, powers := [(7, 1), (33, 1), (39, 1)] }, { coefficient := 1, powers := [(10, 1), (20, 1), (56, 1)] }, { coefficient := 1, powers := [(10, 1), (25, 1), (44, 1)] }, { coefficient := 1, powers := [(10, 1), (33, 1), (36, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1), (51, 1)] }, { coefficient := 1, powers := [(14, 1), (25, 1), (39, 1)] }, { coefficient := 1, powers := [(14, 1), (30, 1), (36, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (37, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (47, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (28, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (22, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1), (47, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (40, 1)] }, { coefficient := 1, powers := [(12, 1), (22, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1), (28, 1), (47, 1)] }, { coefficient := 1, powers := [(12, 1), (34, 1), (37, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (54, 1)] }, { coefficient := 1, powers := [(17, 1), (28, 1), (40, 1)] }, { coefficient := 1, powers := [(17, 1), (31, 1), (37, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (61, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(39, 1)] }],
  [{ coefficient := 1, powers := [(40, 1)] }],
  [{ coefficient := 1, powers := [(57, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (65, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(25, 1)] }],
  [{ coefficient := 1, powers := [(28, 1), (66, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 53 → SparsePoly (Fin 67) := ![
  [{ coefficient := -2, powers := [(2, 1), (14, 1), (21, 1), (37, 1), (44, 1), (60, 1), (62, 1)] }, { coefficient := 2, powers := [(2, 1), (14, 1), (27, 1), (37, 1), (60, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (14, 1), (27, 1), (37, 1), (60, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(34, 1), (37, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(26, 1), (45, 1), (46, 1)] }],
  [{ coefficient := -1, powers := [(19, 1), (28, 1)] }],
  [{ coefficient := -1, powers := [(19, 1), (27, 1), (42, 1), (54, 1), (61, 1)] }, { coefficient := -1, powers := [(24, 1), (27, 1), (47, 1), (49, 1), (61, 1)] }, { coefficient := -1, powers := [(26, 1), (45, 1), (46, 1), (54, 1)] }, { coefficient := -1, powers := [(31, 1), (37, 1), (42, 1), (61, 1)] }, { coefficient := -1, powers := [(31, 1), (37, 1), (45, 1)] }, { coefficient := -1, powers := [(34, 1), (37, 1), (49, 1), (61, 1)] }, { coefficient := -1, powers := [(34, 1), (37, 1), (49, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(26, 1), (46, 1), (54, 1)] }, { coefficient := -1, powers := [(31, 1), (37, 1)] }],
  [{ coefficient := -1, powers := [(26, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(16, 1), (23, 1), (46, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (49, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (4, 1), (56, 1), (60, 1)] }, { coefficient := -1, powers := [(2, 1), (14, 1), (36, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(24, 1), (27, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (46, 1), (51, 1), (54, 1)] }, { coefficient := 1, powers := [(16, 1), (19, 1), (27, 1), (54, 1), (61, 1)] }, { coefficient := 1, powers := [(16, 1), (31, 1), (37, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (31, 1), (44, 1)] }, { coefficient := 1, powers := [(16, 1), (24, 1), (27, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (24, 1), (27, 1), (47, 1), (61, 1)] }, { coefficient := 1, powers := [(16, 1), (34, 1), (37, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(16, 1), (26, 1), (45, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (37, 1), (51, 1), (60, 1)] }, { coefficient := -1, powers := [(2, 1), (37, 1), (56, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (37, 1), (44, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (26, 1), (46, 1), (54, 1)] }, { coefficient := 1, powers := [(18, 1), (31, 1), (37, 1)] }, { coefficient := 1, powers := [(19, 1), (26, 1), (54, 1)] }, { coefficient := 1, powers := [(21, 1), (23, 1), (46, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (19, 1), (31, 1), (42, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (46, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(23, 1), (46, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(26, 1), (46, 1), (54, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(54, 1)] }],
  [{ coefficient := -2, powers := [(2, 1), (14, 1), (20, 1), (37, 1), (60, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (27, 1)] }, { coefficient := 1, powers := [(28, 1)] }],
  [{ coefficient := -1, powers := [(26, 1), (46, 1)] }],
  [{ coefficient := 2, powers := [(2, 1), (14, 1), (20, 1), (21, 1), (37, 1), (60, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (46, 1)] }, { coefficient := 1, powers := [(16, 1), (26, 1), (46, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (45, 1)] }],
  [{ coefficient := -1, powers := [(16, 1), (24, 1), (27, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (36, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (20, 1), (37, 1), (60, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(16, 1), (19, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (19, 1), (31, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (31, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (20, 1), (28, 1), (37, 1), (60, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (14, 1), (37, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(19, 1)] }],
  [{ coefficient := -1, powers := [(27, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (37, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(16, 1), (19, 1), (27, 1), (42, 1), (54, 1)] }, { coefficient := -1, powers := [(16, 1), (24, 1), (27, 1), (47, 1), (49, 1)] }, { coefficient := -1, powers := [(16, 1), (31, 1), (37, 1), (42, 1)] }, { coefficient := -1, powers := [(16, 1), (34, 1), (37, 1), (49, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (36, 1), (46, 1), (53, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (37, 1), (39, 1), (56, 1), (60, 1)] }, { coefficient := -1, powers := [(2, 1), (37, 1), (44, 1), (51, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (37, 1), (44, 1), (56, 1), (60, 1)] }],
  [{ coefficient := 2, powers := [(2, 1), (14, 1), (20, 1), (37, 1), (51, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (7, 1), (33, 1), (37, 1), (60, 1)] }, { coefficient := -2, powers := [(2, 1), (14, 1), (16, 1), (20, 1), (21, 1), (37, 1), (60, 1), (62, 1)] }, { coefficient := 1, powers := [(6, 1), (16, 1), (19, 1), (34, 1), (54, 1)] }, { coefficient := -1, powers := [(8, 1), (23, 1), (31, 1), (47, 1)] }, { coefficient := 1, powers := [(16, 1), (19, 1), (26, 1), (42, 1), (54, 1)] }, { coefficient := -1, powers := [(17, 1), (18, 1), (26, 1), (46, 1), (54, 1)] }, { coefficient := -1, powers := [(17, 1), (18, 1), (31, 1), (37, 1)] }, { coefficient := -1, powers := [(17, 1), (19, 1), (26, 1), (54, 1)] }, { coefficient := -1, powers := [(17, 1), (21, 1), (23, 1), (46, 1), (54, 1)] }, { coefficient := -1, powers := [(17, 1), (23, 1), (26, 1), (46, 1), (54, 1)] }, { coefficient := -1, powers := [(17, 1), (23, 1), (31, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (24, 1), (45, 1)] }, { coefficient := 1, powers := [(6, 1), (8, 1), (34, 1), (59, 1)] }, { coefficient := 1, powers := [(8, 1), (26, 1), (42, 1), (59, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1)] }, { coefficient := 1, powers := [(16, 1), (24, 1), (27, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (40, 1)] }, { coefficient := -1, powers := [(2, 1), (46, 1), (49, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1)] }, { coefficient := 1, powers := [(8, 1), (19, 1), (27, 1), (31, 1), (66, 1)] }, { coefficient := 1, powers := [(12, 1), (22, 1)] }, { coefficient := 1, powers := [(12, 1), (26, 1), (46, 1)] }, { coefficient := -1, powers := [(16, 1), (26, 1), (46, 1), (49, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (34, 1), (37, 1)] }, { coefficient := 1, powers := [(16, 1), (34, 1), (37, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (4, 1), (37, 1), (59, 1), (60, 1)] }, { coefficient := -1, powers := [(2, 1), (14, 1), (37, 1), (44, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (7, 1), (20, 1), (37, 1), (59, 1), (60, 1)] }, { coefficient := -1, powers := [(2, 1), (10, 1), (20, 1), (37, 1), (56, 1), (60, 1)] }, { coefficient := -1, powers := [(2, 1), (14, 1), (20, 1), (37, 1), (51, 1), (60, 1)] }, { coefficient := -1, powers := [(8, 1), (19, 1), (31, 1), (42, 1), (44, 1)] }, { coefficient := 1, powers := [(8, 1), (19, 1), (31, 1), (45, 1)] }]
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
    (values : Fin 67 → R) :
    ¬ ∀ index : Fin 53,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component39.SelectedLeafB5_4_2_5.selectedHasNoCommonZero

end Krenn.Component39.SelectedLeafB5_4_2_5
