import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component39.SelectedLeafB0_6_2

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "54f4245a100a74a4b013860bb98df27d4ec38e423d954929fc60f22ac4d8211d"
def certificateSHA256 : String := "3094deabd946c27edfad4539b1b701e938cf8eb313d834d32e307594c6091cd1"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 47 → Fin 670 := ![
  11,
  21,
  95,
  180,
  181,
  183,
  187,
  191,
  192,
  193,
  277,
  300,
  301,
  303,
  304,
  305,
  313,
  419,
  429,
  430,
  433,
  434,
  439,
  440,
  458,
  463,
  467,
  476,
  521,
  529,
  542,
  566,
  581,
  602,
  603,
  604,
  605,
  618,
  644,
  659,
  660,
  661,
  662,
  663,
  664,
  666,
  669
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 47 → SparsePoly (Fin 64) := ![
  [{ coefficient := 1, powers := [(8, 1), (30, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (20, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (33, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (23, 1)] }, { coefficient := 1, powers := [(16, 1), (18, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (24, 1)] }, { coefficient := 1, powers := [(16, 1), (18, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (42, 1)] }, { coefficient := 1, powers := [(17, 1), (18, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (18, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (54, 1)] }, { coefficient := 1, powers := [(28, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (42, 1)] }, { coefficient := 1, powers := [(26, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (53, 1)] }, { coefficient := 1, powers := [(28, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (23, 1), (47, 1)] }, { coefficient := 1, powers := [(17, 1), (19, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1)] }, { coefficient := 1, powers := [(18, 1), (42, 1)] }, { coefficient := 1, powers := [(23, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (42, 1)] }, { coefficient := 1, powers := [(23, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (54, 1)] }, { coefficient := 1, powers := [(18, 1), (54, 1)] }, { coefficient := 1, powers := [(24, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (44, 1)] }, { coefficient := 1, powers := [(4, 1), (33, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (51, 1)] }, { coefficient := 1, powers := [(7, 1), (30, 1)] }, { coefficient := 1, powers := [(10, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (44, 1)] }, { coefficient := 1, powers := [(12, 1), (56, 1)] }, { coefficient := 1, powers := [(16, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (47, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1)] }, { coefficient := 1, powers := [(16, 1), (26, 1), (47, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (59, 1)] }, { coefficient := 1, powers := [(16, 1), (19, 1), (51, 1)] }, { coefficient := 1, powers := [(16, 1), (19, 1), (56, 1)] }, { coefficient := 1, powers := [(16, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (60, 1)] }, { coefficient := 1, powers := [(12, 1), (47, 1)] }, { coefficient := 1, powers := [(17, 1), (19, 1), (52, 1)] }, { coefficient := 1, powers := [(17, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (59, 1)] }, { coefficient := 1, powers := [(16, 1), (24, 1), (39, 1)] }, { coefficient := 1, powers := [(16, 1), (24, 1), (44, 1)] }, { coefficient := 1, powers := [(16, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (60, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (45, 1)] }, { coefficient := 1, powers := [(12, 1), (57, 1)] }, { coefficient := 1, powers := [(17, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (39, 1)] }, { coefficient := 1, powers := [(16, 1), (44, 1)] }, { coefficient := 1, powers := [(16, 1), (51, 1)] }, { coefficient := 1, powers := [(16, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (54, 1)] }, { coefficient := 1, powers := [(28, 1), (40, 1)] }, { coefficient := 1, powers := [(28, 1), (46, 1), (49, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1), (53, 1)] }, { coefficient := 1, powers := [(24, 1), (39, 1)] }, { coefficient := 1, powers := [(24, 1), (44, 1)] }, { coefficient := 1, powers := [(53, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1), (54, 1)] }, { coefficient := 1, powers := [(24, 1), (45, 1), (49, 1)] }, { coefficient := 1, powers := [(42, 1), (54, 1)] }, { coefficient := 1, powers := [(49, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1), (51, 1)] }, { coefficient := 1, powers := [(19, 1), (51, 1)] }, { coefficient := 1, powers := [(19, 1), (56, 1)] }, { coefficient := 1, powers := [(46, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (38, 1), (56, 1)] }, { coefficient := 1, powers := [(1, 1), (50, 1)] }, { coefficient := 1, powers := [(7, 1), (33, 1), (38, 1)] }, { coefficient := 1, powers := [(14, 1), (25, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (23, 1), (60, 1)] }, { coefficient := 1, powers := [(12, 1), (23, 1), (47, 1)] }, { coefficient := 1, powers := [(17, 1), (19, 1), (49, 1)] }, { coefficient := 1, powers := [(17, 1), (23, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (20, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (30, 1), (44, 1)] }, { coefficient := 1, powers := [(6, 1), (33, 1), (39, 1)] }, { coefficient := 1, powers := [(20, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (20, 1), (59, 1)] }, { coefficient := 1, powers := [(8, 1), (30, 1), (44, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (39, 1)] }, { coefficient := 1, powers := [(16, 1), (20, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (42, 1), (53, 1)] }, { coefficient := 1, powers := [(22, 1), (57, 1)] }, { coefficient := 1, powers := [(28, 1), (47, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (51, 1)] }, { coefficient := 1, powers := [(3, 1), (59, 1)] }, { coefficient := 1, powers := [(18, 1), (51, 1)] }, { coefficient := 1, powers := [(18, 1), (56, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(4, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (59, 1)] }, { coefficient := 1, powers := [(10, 1), (44, 1)] }, { coefficient := 1, powers := [(10, 1), (56, 1)] }, { coefficient := 1, powers := [(14, 1), (39, 1)] }, { coefficient := 1, powers := [(14, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (51, 1)] }, { coefficient := 1, powers := [(20, 1), (56, 1)] }, { coefficient := 1, powers := [(25, 1), (39, 1)] }, { coefficient := 1, powers := [(25, 1), (44, 1)] }, { coefficient := 1, powers := [(30, 1), (36, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (35, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1)] }, { coefficient := 1, powers := [(3, 1), (23, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (18, 1), (59, 1)] }, { coefficient := 1, powers := [(18, 1)] }, { coefficient := 1, powers := [(23, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (35, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (42, 1), (49, 1)] }, { coefficient := 1, powers := [(3, 1), (23, 1), (60, 1)] }, { coefficient := 1, powers := [(6, 1), (18, 1), (60, 1)] }, { coefficient := 1, powers := [(18, 1), (42, 1), (49, 1)] }, { coefficient := 1, powers := [(23, 1), (42, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (42, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (21, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1), (42, 1)] }, { coefficient := 1, powers := [(12, 1), (21, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1), (28, 1), (42, 1)] }, { coefficient := 1, powers := [(17, 1), (21, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (36, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (44, 1), (51, 1)] }, { coefficient := 1, powers := [(39, 1)] }, { coefficient := 1, powers := [(44, 1)] }, { coefficient := 1, powers := [(51, 1)] }, { coefficient := 1, powers := [(56, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (36, 1), (59, 1)] }, { coefficient := 1, powers := [(1, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(1, 1), (44, 1), (51, 1)] }, { coefficient := 1, powers := [(4, 1), (25, 1), (59, 1)] }, { coefficient := 1, powers := [(4, 1), (30, 1), (56, 1)] }, { coefficient := 1, powers := [(4, 1), (33, 1), (51, 1)] }, { coefficient := 1, powers := [(7, 1), (20, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (30, 1), (44, 1)] }, { coefficient := 1, powers := [(7, 1), (33, 1), (39, 1)] }, { coefficient := 1, powers := [(10, 1), (20, 1), (56, 1)] }, { coefficient := 1, powers := [(10, 1), (25, 1), (44, 1)] }, { coefficient := 1, powers := [(10, 1), (33, 1), (36, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1), (51, 1)] }, { coefficient := 1, powers := [(14, 1), (25, 1), (39, 1)] }, { coefficient := 1, powers := [(14, 1), (30, 1), (36, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (37, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (47, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (28, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (22, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1), (47, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (40, 1)] }, { coefficient := 1, powers := [(12, 1), (22, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1), (28, 1), (47, 1)] }, { coefficient := 1, powers := [(12, 1), (34, 1), (37, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (54, 1)] }, { coefficient := 1, powers := [(17, 1), (28, 1), (40, 1)] }, { coefficient := 1, powers := [(17, 1), (31, 1), (37, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1)] }],
  [{ coefficient := 1, powers := [(1, 1)] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(38, 1), (61, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(40, 1)] }],
  [{ coefficient := 1, powers := [(57, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 47 → SparsePoly (Fin 64) := ![
  [{ coefficient := 1, powers := [(4, 1), (21, 1), (39, 1), (46, 1), (60, 1)] }, { coefficient := 2, powers := [(4, 1), (21, 1), (44, 1), (46, 1), (60, 1)] }, { coefficient := 1, powers := [(4, 1), (21, 1), (46, 1), (51, 1), (60, 1)] }, { coefficient := -2, powers := [(4, 1), (22, 1), (39, 1), (60, 1)] }, { coefficient := -4, powers := [(4, 1), (22, 1), (44, 1), (60, 1)] }, { coefficient := -2, powers := [(4, 1), (22, 1), (51, 1), (60, 1)] }, { coefficient := 1, powers := [(4, 1), (31, 1), (39, 1), (42, 1), (46, 1)] }, { coefficient := -1, powers := [(4, 1), (31, 1), (39, 1), (47, 1)] }, { coefficient := 2, powers := [(4, 1), (31, 1), (42, 1), (44, 1), (46, 1)] }, { coefficient := 1, powers := [(4, 1), (31, 1), (42, 1), (46, 1), (51, 1)] }, { coefficient := -2, powers := [(4, 1), (31, 1), (44, 1), (47, 1)] }, { coefficient := -1, powers := [(4, 1), (31, 1), (47, 1), (51, 1)] }, { coefficient := -1, powers := [(7, 1), (21, 1), (39, 1), (46, 1), (60, 1)] }, { coefficient := -1, powers := [(7, 1), (21, 1), (44, 1), (46, 1), (60, 1)] }, { coefficient := 2, powers := [(7, 1), (22, 1), (39, 1), (60, 1)] }, { coefficient := 2, powers := [(7, 1), (22, 1), (44, 1), (60, 1)] }, { coefficient := -1, powers := [(7, 1), (31, 1), (39, 1), (42, 1), (46, 1)] }, { coefficient := 1, powers := [(7, 1), (31, 1), (39, 1), (47, 1)] }, { coefficient := -1, powers := [(7, 1), (31, 1), (42, 1), (44, 1), (46, 1)] }, { coefficient := 1, powers := [(7, 1), (31, 1), (44, 1), (47, 1)] }, { coefficient := 1, powers := [(10, 1), (21, 1), (36, 1), (46, 1), (60, 1)] }, { coefficient := -2, powers := [(10, 1), (22, 1), (36, 1), (60, 1)] }, { coefficient := 1, powers := [(10, 1), (31, 1), (36, 1), (42, 1), (46, 1)] }, { coefficient := -1, powers := [(10, 1), (31, 1), (36, 1), (47, 1)] }, { coefficient := -1, powers := [(14, 1), (21, 1), (36, 1), (46, 1), (60, 1)] }, { coefficient := 2, powers := [(14, 1), (22, 1), (36, 1), (60, 1)] }, { coefficient := -1, powers := [(14, 1), (31, 1), (36, 1), (42, 1), (46, 1)] }, { coefficient := 1, powers := [(14, 1), (31, 1), (36, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (21, 1), (46, 1), (53, 1), (60, 1)] }, { coefficient := -2, powers := [(4, 1), (22, 1), (53, 1), (60, 1)] }, { coefficient := 1, powers := [(4, 1), (31, 1), (42, 1), (46, 1), (53, 1)] }, { coefficient := -1, powers := [(4, 1), (31, 1), (47, 1), (53, 1)] }, { coefficient := -1, powers := [(6, 1), (10, 1), (21, 1), (39, 1), (46, 1), (53, 1), (60, 1)] }, { coefficient := 2, powers := [(6, 1), (10, 1), (22, 1), (39, 1), (53, 1), (60, 1)] }, { coefficient := -1, powers := [(6, 1), (10, 1), (31, 1), (39, 1), (42, 1), (46, 1), (53, 1)] }, { coefficient := 1, powers := [(6, 1), (10, 1), (31, 1), (39, 1), (47, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (21, 1), (46, 1), (51, 1), (60, 1), (61, 1)] }, { coefficient := 2, powers := [(4, 1), (22, 1), (51, 1), (60, 1), (61, 1)] }, { coefficient := -1, powers := [(4, 1), (31, 1), (42, 1), (46, 1), (51, 1), (61, 1)] }, { coefficient := 1, powers := [(4, 1), (31, 1), (47, 1), (51, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(28, 1), (44, 1), (47, 1)] }, { coefficient := -1, powers := [(28, 1), (47, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (28, 1), (44, 1)] }, { coefficient := 1, powers := [(19, 1), (28, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [(28, 1), (44, 1), (47, 1), (49, 1)] }, { coefficient := 1, powers := [(28, 1), (47, 1), (49, 1), (51, 1)] }, { coefficient := -1, powers := [(28, 1), (47, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(17, 1), (46, 1)] }],
  [{ coefficient := -1, powers := [(16, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(28, 1), (44, 1), (49, 1)] }, { coefficient := -1, powers := [(28, 1), (49, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (28, 1), (44, 1), (49, 1), (59, 1)] }, { coefficient := -1, powers := [(5, 1), (28, 1), (49, 1), (51, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (28, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(16, 1), (22, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (21, 1), (39, 1), (46, 1), (60, 1)] }, { coefficient := -2, powers := [(8, 1), (22, 1), (39, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1), (39, 1), (42, 1), (46, 1)] }, { coefficient := -1, powers := [(8, 1), (31, 1), (39, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (21, 1), (39, 1), (46, 1), (60, 1)] }, { coefficient := -2, powers := [(8, 1), (22, 1), (39, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1), (39, 1), (42, 1), (46, 1)] }, { coefficient := -1, powers := [(8, 1), (31, 1), (39, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (28, 1), (47, 1)] }, { coefficient := -1, powers := [(19, 1), (28, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(54, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (28, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(18, 1), (28, 1), (44, 1)] }, { coefficient := -1, powers := [(18, 1), (28, 1), (56, 1)] }],
  [{ coefficient := 2, powers := [(4, 1), (20, 1), (21, 1), (46, 1), (60, 1)] }, { coefficient := -4, powers := [(4, 1), (20, 1), (22, 1), (60, 1)] }, { coefficient := 2, powers := [(4, 1), (20, 1), (31, 1), (42, 1), (46, 1)] }, { coefficient := -2, powers := [(4, 1), (20, 1), (31, 1), (47, 1)] }, { coefficient := -1, powers := [(4, 1), (21, 1), (25, 1), (46, 1), (60, 1)] }, { coefficient := 2, powers := [(4, 1), (22, 1), (25, 1), (60, 1)] }, { coefficient := -1, powers := [(4, 1), (25, 1), (31, 1), (42, 1), (46, 1)] }, { coefficient := 1, powers := [(4, 1), (25, 1), (31, 1), (47, 1)] }],
  [{ coefficient := -1, powers := [(22, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (19, 1), (28, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(17, 1)] }],
  [{ coefficient := -2, powers := [(4, 1), (16, 1), (20, 1), (21, 1), (46, 1), (60, 1)] }, { coefficient := 4, powers := [(4, 1), (16, 1), (20, 1), (22, 1), (60, 1)] }, { coefficient := -2, powers := [(4, 1), (16, 1), (20, 1), (31, 1), (42, 1), (46, 1)] }, { coefficient := 2, powers := [(4, 1), (16, 1), (20, 1), (31, 1), (47, 1)] }, { coefficient := 1, powers := [(4, 1), (16, 1), (21, 1), (25, 1), (46, 1), (60, 1)] }, { coefficient := -2, powers := [(4, 1), (16, 1), (22, 1), (25, 1), (60, 1)] }, { coefficient := 1, powers := [(4, 1), (16, 1), (25, 1), (31, 1), (42, 1), (46, 1)] }, { coefficient := -1, powers := [(4, 1), (16, 1), (25, 1), (31, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (22, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (16, 1), (28, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (21, 1), (39, 1), (46, 1), (60, 1), (61, 1)] }, { coefficient := 2, powers := [(8, 1), (22, 1), (39, 1), (60, 1), (61, 1)] }, { coefficient := -1, powers := [(8, 1), (31, 1), (39, 1), (42, 1), (46, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1), (39, 1), (47, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(28, 1), (44, 1)] }, { coefficient := 1, powers := [(28, 1), (51, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (10, 1), (21, 1), (39, 1), (46, 1), (60, 1)] }, { coefficient := 2, powers := [(8, 1), (10, 1), (22, 1), (39, 1), (60, 1)] }, { coefficient := -1, powers := [(8, 1), (10, 1), (31, 1), (39, 1), (42, 1), (46, 1)] }, { coefficient := 1, powers := [(8, 1), (10, 1), (31, 1), (39, 1), (47, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (21, 1), (46, 1), (60, 1)] }, { coefficient := 2, powers := [(4, 1), (22, 1), (60, 1)] }, { coefficient := -1, powers := [(4, 1), (31, 1), (42, 1), (46, 1)] }, { coefficient := 1, powers := [(4, 1), (31, 1), (47, 1)] }, { coefficient := 1, powers := [(6, 1), (10, 1), (21, 1), (39, 1), (46, 1), (60, 1)] }, { coefficient := -2, powers := [(6, 1), (10, 1), (22, 1), (39, 1), (60, 1)] }, { coefficient := 1, powers := [(6, 1), (10, 1), (31, 1), (39, 1), (42, 1), (46, 1)] }, { coefficient := -1, powers := [(6, 1), (10, 1), (31, 1), (39, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(12, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (28, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (20, 1), (21, 1), (46, 1), (60, 1)] }, { coefficient := 2, powers := [(8, 1), (20, 1), (22, 1), (60, 1)] }, { coefficient := -1, powers := [(8, 1), (20, 1), (31, 1), (42, 1), (46, 1)] }, { coefficient := 1, powers := [(8, 1), (20, 1), (31, 1), (47, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (10, 1), (21, 1), (46, 1), (60, 1)] }, { coefficient := 2, powers := [(8, 1), (10, 1), (22, 1), (60, 1)] }, { coefficient := -1, powers := [(8, 1), (10, 1), (31, 1), (42, 1), (46, 1)] }, { coefficient := 1, powers := [(8, 1), (10, 1), (31, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (28, 1), (44, 1), (60, 1)] }, { coefficient := -1, powers := [(5, 1), (28, 1), (51, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (28, 1), (44, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (28, 1), (51, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(46, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (16, 1), (19, 1), (28, 1), (60, 1)] }, { coefficient := -1, powers := [(4, 1), (8, 1), (21, 1), (30, 1), (46, 1), (60, 1)] }, { coefficient := 2, powers := [(4, 1), (8, 1), (22, 1), (30, 1), (60, 1)] }, { coefficient := -1, powers := [(4, 1), (8, 1), (30, 1), (31, 1), (42, 1), (46, 1)] }, { coefficient := 1, powers := [(4, 1), (8, 1), (30, 1), (31, 1), (47, 1)] }, { coefficient := 1, powers := [(8, 1), (10, 1), (20, 1), (21, 1), (46, 1), (60, 1)] }, { coefficient := -2, powers := [(8, 1), (10, 1), (20, 1), (22, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (10, 1), (20, 1), (31, 1), (42, 1), (46, 1)] }, { coefficient := -1, powers := [(8, 1), (10, 1), (20, 1), (31, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (21, 1), (46, 1), (60, 1)] }, { coefficient := -2, powers := [(8, 1), (22, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1), (42, 1), (46, 1)] }, { coefficient := -1, powers := [(8, 1), (31, 1), (47, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(3, 1), (16, 1), (19, 1), (28, 1), (36, 1), (59, 1), (60, 1)] }, { coefficient := 1, powers := [(3, 1), (16, 1), (19, 1), (28, 1), (39, 1), (56, 1), (60, 1)] }, { coefficient := 1, powers := [(3, 1), (16, 1), (19, 1), (28, 1), (44, 1), (51, 1), (60, 1)] }, { coefficient := -1, powers := [(3, 1), (16, 1), (28, 1), (46, 1), (51, 1), (60, 1)] }, { coefficient := 1, powers := [(4, 1), (8, 1), (21, 1), (30, 1), (36, 1), (46, 1), (59, 1), (60, 1)] }, { coefficient := 1, powers := [(4, 1), (8, 1), (21, 1), (30, 1), (39, 1), (46, 1), (56, 1), (60, 1)] }, { coefficient := 1, powers := [(4, 1), (8, 1), (21, 1), (30, 1), (44, 1), (46, 1), (51, 1), (60, 1)] }, { coefficient := -2, powers := [(4, 1), (8, 1), (22, 1), (30, 1), (36, 1), (59, 1), (60, 1)] }, { coefficient := -2, powers := [(4, 1), (8, 1), (22, 1), (30, 1), (39, 1), (56, 1), (60, 1)] }, { coefficient := -2, powers := [(4, 1), (8, 1), (22, 1), (30, 1), (44, 1), (51, 1), (60, 1)] }, { coefficient := 1, powers := [(4, 1), (8, 1), (30, 1), (31, 1), (36, 1), (42, 1), (46, 1), (59, 1)] }, { coefficient := -1, powers := [(4, 1), (8, 1), (30, 1), (31, 1), (36, 1), (47, 1), (59, 1)] }, { coefficient := 1, powers := [(4, 1), (8, 1), (30, 1), (31, 1), (39, 1), (42, 1), (46, 1), (56, 1)] }, { coefficient := -1, powers := [(4, 1), (8, 1), (30, 1), (31, 1), (39, 1), (47, 1), (56, 1)] }, { coefficient := 1, powers := [(4, 1), (8, 1), (30, 1), (31, 1), (42, 1), (44, 1), (46, 1), (51, 1)] }, { coefficient := -1, powers := [(4, 1), (8, 1), (30, 1), (31, 1), (44, 1), (47, 1), (51, 1)] }, { coefficient := 2, powers := [(4, 1), (16, 1), (20, 1), (21, 1), (44, 1), (46, 1), (53, 1), (60, 1)] }, { coefficient := -4, powers := [(4, 1), (16, 1), (20, 1), (22, 1), (44, 1), (53, 1), (60, 1)] }, { coefficient := 2, powers := [(4, 1), (16, 1), (20, 1), (31, 1), (42, 1), (44, 1), (46, 1), (53, 1)] }, { coefficient := -2, powers := [(4, 1), (16, 1), (20, 1), (31, 1), (44, 1), (47, 1), (53, 1)] }, { coefficient := -1, powers := [(4, 1), (16, 1), (21, 1), (25, 1), (44, 1), (46, 1), (53, 1), (60, 1)] }, { coefficient := 2, powers := [(4, 1), (16, 1), (22, 1), (25, 1), (44, 1), (53, 1), (60, 1)] }, { coefficient := -1, powers := [(4, 1), (16, 1), (25, 1), (31, 1), (42, 1), (44, 1), (46, 1), (53, 1)] }, { coefficient := 1, powers := [(4, 1), (16, 1), (25, 1), (31, 1), (44, 1), (47, 1), (53, 1)] }, { coefficient := -1, powers := [(5, 1), (28, 1), (44, 1), (60, 1)] }, { coefficient := -1, powers := [(8, 1), (10, 1), (20, 1), (21, 1), (36, 1), (46, 1), (59, 1), (60, 1)] }, { coefficient := -1, powers := [(8, 1), (10, 1), (20, 1), (21, 1), (39, 1), (46, 1), (56, 1), (60, 1)] }, { coefficient := -1, powers := [(8, 1), (10, 1), (20, 1), (21, 1), (44, 1), (46, 1), (51, 1), (60, 1)] }, { coefficient := 2, powers := [(8, 1), (10, 1), (20, 1), (22, 1), (36, 1), (59, 1), (60, 1)] }, { coefficient := 2, powers := [(8, 1), (10, 1), (20, 1), (22, 1), (39, 1), (56, 1), (60, 1)] }, { coefficient := 2, powers := [(8, 1), (10, 1), (20, 1), (22, 1), (44, 1), (51, 1), (60, 1)] }, { coefficient := -1, powers := [(8, 1), (10, 1), (20, 1), (31, 1), (36, 1), (42, 1), (46, 1), (59, 1)] }, { coefficient := 1, powers := [(8, 1), (10, 1), (20, 1), (31, 1), (36, 1), (47, 1), (59, 1)] }, { coefficient := -1, powers := [(8, 1), (10, 1), (20, 1), (31, 1), (39, 1), (42, 1), (46, 1), (56, 1)] }, { coefficient := 1, powers := [(8, 1), (10, 1), (20, 1), (31, 1), (39, 1), (47, 1), (56, 1)] }, { coefficient := -1, powers := [(8, 1), (10, 1), (20, 1), (31, 1), (42, 1), (44, 1), (46, 1), (51, 1)] }, { coefficient := 1, powers := [(8, 1), (10, 1), (20, 1), (31, 1), (44, 1), (47, 1), (51, 1)] }, { coefficient := -1, powers := [(16, 1), (28, 1), (47, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (21, 1), (36, 1), (46, 1), (59, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (21, 1), (38, 1), (39, 1), (46, 1), (56, 1), (60, 1), (61, 1)] }, { coefficient := -1, powers := [(8, 1), (21, 1), (39, 1), (44, 1), (46, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (21, 1), (39, 1), (46, 1), (50, 1), (60, 1), (61, 1)] }, { coefficient := -1, powers := [(8, 1), (21, 1), (39, 1), (46, 1), (51, 1), (60, 1)] }, { coefficient := -1, powers := [(8, 1), (21, 1), (39, 1), (46, 1), (56, 1), (60, 1)] }, { coefficient := -1, powers := [(8, 1), (21, 1), (44, 1), (46, 1), (51, 1), (60, 1)] }, { coefficient := 2, powers := [(8, 1), (22, 1), (36, 1), (59, 1), (60, 1)] }, { coefficient := -2, powers := [(8, 1), (22, 1), (38, 1), (39, 1), (56, 1), (60, 1), (61, 1)] }, { coefficient := 2, powers := [(8, 1), (22, 1), (39, 1), (44, 1), (60, 1)] }, { coefficient := -2, powers := [(8, 1), (22, 1), (39, 1), (50, 1), (60, 1), (61, 1)] }, { coefficient := 2, powers := [(8, 1), (22, 1), (39, 1), (51, 1), (60, 1)] }, { coefficient := 2, powers := [(8, 1), (22, 1), (39, 1), (56, 1), (60, 1)] }, { coefficient := 2, powers := [(8, 1), (22, 1), (44, 1), (51, 1), (60, 1)] }, { coefficient := -1, powers := [(8, 1), (31, 1), (36, 1), (42, 1), (46, 1), (59, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1), (36, 1), (47, 1), (59, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1), (38, 1), (39, 1), (42, 1), (46, 1), (56, 1), (61, 1)] }, { coefficient := -1, powers := [(8, 1), (31, 1), (38, 1), (39, 1), (47, 1), (56, 1), (61, 1)] }, { coefficient := -1, powers := [(8, 1), (31, 1), (39, 1), (42, 1), (44, 1), (46, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1), (39, 1), (42, 1), (46, 1), (50, 1), (61, 1)] }, { coefficient := -1, powers := [(8, 1), (31, 1), (39, 1), (42, 1), (46, 1), (51, 1)] }, { coefficient := -1, powers := [(8, 1), (31, 1), (39, 1), (42, 1), (46, 1), (56, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1), (39, 1), (44, 1), (47, 1)] }, { coefficient := -1, powers := [(8, 1), (31, 1), (39, 1), (47, 1), (50, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1), (39, 1), (47, 1), (51, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1), (39, 1), (47, 1), (56, 1)] }, { coefficient := -1, powers := [(8, 1), (31, 1), (42, 1), (44, 1), (46, 1), (51, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1), (44, 1), (47, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(37, 1), (60, 1)] }, { coefficient := 1, powers := [(40, 1), (57, 1)] }, { coefficient := -1, powers := [(42, 1), (46, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (8, 1), (21, 1), (33, 1), (46, 1), (51, 1), (60, 1)] }, { coefficient := -2, powers := [(4, 1), (8, 1), (22, 1), (33, 1), (51, 1), (60, 1)] }, { coefficient := 1, powers := [(4, 1), (8, 1), (31, 1), (33, 1), (42, 1), (46, 1), (51, 1)] }, { coefficient := -1, powers := [(4, 1), (8, 1), (31, 1), (33, 1), (47, 1), (51, 1)] }, { coefficient := 1, powers := [(7, 1), (8, 1), (21, 1), (33, 1), (39, 1), (46, 1), (60, 1)] }, { coefficient := -2, powers := [(7, 1), (8, 1), (22, 1), (33, 1), (39, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (8, 1), (31, 1), (33, 1), (39, 1), (42, 1), (46, 1)] }, { coefficient := -1, powers := [(7, 1), (8, 1), (31, 1), (33, 1), (39, 1), (47, 1)] }, { coefficient := 1, powers := [(8, 1), (14, 1), (21, 1), (25, 1), (39, 1), (46, 1), (60, 1)] }, { coefficient := -2, powers := [(8, 1), (14, 1), (22, 1), (25, 1), (39, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (14, 1), (25, 1), (31, 1), (39, 1), (42, 1), (46, 1)] }, { coefficient := -1, powers := [(8, 1), (14, 1), (25, 1), (31, 1), (39, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (34, 1)] }, { coefficient := 1, powers := [(17, 1), (18, 1), (28, 1), (44, 1)] }, { coefficient := 1, powers := [(17, 1), (18, 1), (28, 1), (56, 1)] }, { coefficient := 1, powers := [(17, 1), (23, 1), (28, 1), (44, 1)] }, { coefficient := -1, powers := [(17, 1), (23, 1), (28, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (31, 1)] }, { coefficient := -1, powers := [(12, 1), (21, 1), (46, 1)] }, { coefficient := 1, powers := [(12, 1), (22, 1)] }, { coefficient := -1, powers := [(16, 1), (22, 1), (49, 1)] }]
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
    (values : Fin 64 → R) :
    ¬ ∀ index : Fin 47,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component39.SelectedLeafB0_6_2.selectedHasNoCommonZero

end Krenn.Component39.SelectedLeafB0_6_2
