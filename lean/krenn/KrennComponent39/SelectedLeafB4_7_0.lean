import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component39.SelectedLeafB4_7_0

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "beadf27ed65510f53e05b2f2721e9453ada1c323176c4b1be4edfe81094c5892"
def certificateSHA256 : String := "9906b4eaeb1bf62480a3bd1c1bfb45d5591d0b83f46a64287aa27effb6c81261"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 50 → Fin 670 := ![
  14,
  19,
  30,
  92,
  170,
  181,
  183,
  184,
  187,
  188,
  189,
  191,
  194,
  196,
  250,
  254,
  268,
  300,
  302,
  303,
  305,
  313,
  316,
  317,
  322,
  382,
  397,
  412,
  417,
  419,
  425,
  430,
  434,
  440,
  463,
  468,
  520,
  567,
  603,
  608,
  659,
  660,
  661,
  662,
  663,
  664,
  665,
  666,
  668,
  669
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 50 → SparsePoly (Fin 65) := ![
  [{ coefficient := 1, powers := [(10, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (34, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (34, 1)] }, { coefficient := 1, powers := [(10, 1), (26, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (24, 1)] }, { coefficient := 1, powers := [(16, 1), (18, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (42, 1)] }, { coefficient := 1, powers := [(17, 1), (18, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (45, 1)] }, { coefficient := 1, powers := [(17, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (18, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (42, 1)] }, { coefficient := 1, powers := [(17, 1), (18, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (47, 1)] }, { coefficient := 1, powers := [(17, 1), (19, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (54, 1)] }, { coefficient := 1, powers := [(28, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (40, 1)] }, { coefficient := 1, powers := [(25, 1), (46, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (54, 1)] }, { coefficient := 1, powers := [(28, 1), (44, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (23, 1), (44, 1)] }, { coefficient := 1, powers := [(16, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (24, 1), (44, 1)] }, { coefficient := 1, powers := [(16, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (19, 1), (52, 1)] }, { coefficient := 1, powers := [(14, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1)] }, { coefficient := 1, powers := [(18, 1), (42, 1)] }, { coefficient := 1, powers := [(23, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (49, 1)] }, { coefficient := 1, powers := [(18, 1), (49, 1)] }, { coefficient := 1, powers := [(23, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (54, 1)] }, { coefficient := 1, powers := [(18, 1), (54, 1)] }, { coefficient := 1, powers := [(24, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (51, 1)] }, { coefficient := 1, powers := [(7, 1), (30, 1)] }, { coefficient := 1, powers := [(10, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (44, 1)] }, { coefficient := 1, powers := [(12, 1), (56, 1)] }, { coefficient := 1, powers := [(16, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (45, 1)] }, { coefficient := 1, powers := [(17, 1), (39, 1)] }, { coefficient := 1, powers := [(17, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (51, 1)] }, { coefficient := 1, powers := [(22, 1), (56, 1)] }, { coefficient := 1, powers := [(27, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1), (54, 1)] }, { coefficient := 1, powers := [(24, 1), (44, 1), (49, 1)] }, { coefficient := 1, powers := [(54, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (18, 1), (56, 1)] }, { coefficient := 1, powers := [(12, 1)] }, { coefficient := 1, powers := [(16, 1), (18, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (23, 1), (45, 1)] }, { coefficient := 1, powers := [(17, 1), (23, 1), (39, 1)] }, { coefficient := 1, powers := [(17, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (52, 1)] }, { coefficient := 1, powers := [(18, 1), (49, 1), (56, 1)] }, { coefficient := 1, powers := [(18, 1), (52, 1)] }, { coefficient := 1, powers := [(49, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (45, 1)] }, { coefficient := 1, powers := [(16, 1), (26, 1), (45, 1)] }, { coefficient := 1, powers := [(17, 1), (26, 1), (39, 1)] }, { coefficient := 1, powers := [(17, 1), (27, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (47, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1)] }, { coefficient := 1, powers := [(16, 1), (26, 1), (47, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1)] }, { coefficient := 1, powers := [(12, 1), (28, 1)] }, { coefficient := 1, powers := [(16, 1), (21, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (60, 1)] }, { coefficient := 1, powers := [(12, 1), (47, 1)] }, { coefficient := 1, powers := [(17, 1), (19, 1), (52, 1)] }, { coefficient := 1, powers := [(17, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (60, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (45, 1)] }, { coefficient := 1, powers := [(12, 1), (57, 1)] }, { coefficient := 1, powers := [(17, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (54, 1)] }, { coefficient := 1, powers := [(28, 1), (40, 1)] }, { coefficient := 1, powers := [(28, 1), (46, 1), (49, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1), (54, 1)] }, { coefficient := 1, powers := [(24, 1), (45, 1), (49, 1)] }, { coefficient := 1, powers := [(42, 1), (54, 1)] }, { coefficient := 1, powers := [(49, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1), (54, 1)] }, { coefficient := 1, powers := [(19, 1), (54, 1)] }, { coefficient := 1, powers := [(24, 1), (40, 1)] }, { coefficient := 1, powers := [(24, 1), (46, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (34, 1), (51, 1)] }, { coefficient := 1, powers := [(7, 1), (34, 1), (39, 1)] }, { coefficient := 1, powers := [(10, 1), (27, 1), (45, 1)] }, { coefficient := 1, powers := [(10, 1), (34, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (49, 1), (56, 1)] }, { coefficient := 1, powers := [(22, 1), (52, 1)] }, { coefficient := 1, powers := [(27, 1), (40, 1)] }, { coefficient := 1, powers := [(27, 1), (46, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (51, 1)] }, { coefficient := 1, powers := [(20, 1), (56, 1)] }, { coefficient := 1, powers := [(25, 1), (39, 1)] }, { coefficient := 1, powers := [(25, 1), (44, 1)] }, { coefficient := 1, powers := [(30, 1), (36, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (40, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(19, 1), (49, 1), (56, 1)] }, { coefficient := 1, powers := [(19, 1), (52, 1)] }, { coefficient := 1, powers := [(40, 1)] }, { coefficient := 1, powers := [(46, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (36, 1), (59, 1)] }, { coefficient := 1, powers := [(1, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(1, 1), (44, 1), (51, 1)] }, { coefficient := 1, powers := [(4, 1), (25, 1), (59, 1)] }, { coefficient := 1, powers := [(4, 1), (30, 1), (56, 1)] }, { coefficient := 1, powers := [(4, 1), (33, 1), (51, 1)] }, { coefficient := 1, powers := [(7, 1), (20, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (30, 1), (44, 1)] }, { coefficient := 1, powers := [(7, 1), (33, 1), (39, 1)] }, { coefficient := 1, powers := [(10, 1), (20, 1), (56, 1)] }, { coefficient := 1, powers := [(10, 1), (25, 1), (44, 1)] }, { coefficient := 1, powers := [(10, 1), (33, 1), (36, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1), (51, 1)] }, { coefficient := 1, powers := [(14, 1), (25, 1), (39, 1)] }, { coefficient := 1, powers := [(14, 1), (30, 1), (36, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (37, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (47, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (28, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (22, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1), (47, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (40, 1)] }, { coefficient := 1, powers := [(12, 1), (22, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1), (28, 1), (47, 1)] }, { coefficient := 1, powers := [(12, 1), (34, 1), (37, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (54, 1)] }, { coefficient := 1, powers := [(17, 1), (28, 1), (40, 1)] }, { coefficient := 1, powers := [(17, 1), (31, 1), (37, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (61, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1)] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(38, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(39, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(40, 1), (64, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(56, 1)] }],
  [{ coefficient := 1, powers := [(57, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 50 → SparsePoly (Fin 65) := ![
  [{ coefficient := -2, powers := [(5, 1), (25, 1), (26, 1), (54, 1), (59, 1)] }, { coefficient := -2, powers := [(5, 1), (27, 1), (33, 1), (54, 1)] }, { coefficient := -1, powers := [(8, 1), (25, 1), (26, 1), (40, 1), (59, 1)] }, { coefficient := -1, powers := [(8, 1), (27, 1), (33, 1), (40, 1)] }],
  [{ coefficient := 2, powers := [(5, 1), (19, 1), (33, 1), (34, 1), (36, 1), (54, 1), (64, 1)] }, { coefficient := 1, powers := [(8, 1), (19, 1), (33, 1), (34, 1), (36, 1), (40, 1), (64, 1)] }],
  [{ coefficient := 2, powers := [(5, 1), (14, 1), (34, 1), (44, 1), (49, 1), (54, 1), (64, 1)] }, { coefficient := 1, powers := [(8, 1), (14, 1), (34, 1), (40, 1), (44, 1), (49, 1), (64, 1)] }],
  [{ coefficient := 2, powers := [(5, 1), (20, 1), (54, 1), (59, 1), (62, 1)] }, { coefficient := 1, powers := [(8, 1), (20, 1), (40, 1), (59, 1), (62, 1)] }],
  [{ coefficient := 2, powers := [(5, 1), (25, 1), (54, 1), (59, 1)] }, { coefficient := 1, powers := [(8, 1), (25, 1), (40, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(22, 1), (45, 1), (51, 1), (63, 1)] }, { coefficient := -1, powers := [(22, 1), (45, 1)] }],
  [{ coefficient := -1, powers := [(28, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (24, 1), (39, 1), (63, 1)] }, { coefficient := 1, powers := [(22, 1), (24, 1), (51, 1), (63, 1)] }, { coefficient := -1, powers := [(22, 1), (24, 1)] }],
  [{ coefficient := -1, powers := [(22, 1), (42, 1), (44, 1), (54, 1), (61, 1), (63, 1)] }, { coefficient := -1, powers := [(22, 1), (42, 1), (51, 1), (54, 1), (61, 1), (63, 1)] }, { coefficient := -1, powers := [(22, 1), (42, 1), (54, 1), (61, 1)] }, { coefficient := -1, powers := [(28, 1), (42, 1), (46, 1), (49, 1), (61, 1)] }, { coefficient := -1, powers := [(28, 1), (42, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(28, 1), (47, 1), (52, 1)] }, { coefficient := -1, powers := [(34, 1), (37, 1), (49, 1), (61, 1)] }, { coefficient := -1, powers := [(34, 1), (37, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(22, 1), (44, 1), (54, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(26, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(16, 1), (47, 1)] }, { coefficient := 1, powers := [(17, 1), (18, 1), (44, 1), (46, 1)] }, { coefficient := -1, powers := [(17, 1), (46, 1)] }],
  [{ coefficient := -2, powers := [(5, 1), (14, 1), (34, 1), (44, 1), (54, 1), (64, 1)] }, { coefficient := -1, powers := [(8, 1), (14, 1), (34, 1), (40, 1), (44, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (17, 1), (46, 1)] }, { coefficient := 1, powers := [(17, 1), (23, 1), (46, 1)] }],
  [{ coefficient := -1, powers := [(28, 1), (42, 1), (46, 1)] }, { coefficient := 1, powers := [(28, 1), (47, 1)] }, { coefficient := -1, powers := [(34, 1), (37, 1)] }],
  [{ coefficient := -1, powers := [(22, 1), (45, 1), (63, 1)] }],
  [{ coefficient := -2, powers := [(5, 1), (33, 1), (34, 1), (36, 1), (54, 1), (64, 1)] }, { coefficient := -1, powers := [(8, 1), (33, 1), (34, 1), (36, 1), (40, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (22, 1), (44, 1), (54, 1), (61, 1), (63, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1), (51, 1), (54, 1), (61, 1), (63, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1), (54, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (28, 1), (42, 1), (46, 1), (61, 1)] }, { coefficient := 1, powers := [(16, 1), (34, 1), (37, 1), (61, 1)] }, { coefficient := -1, powers := [(17, 1), (28, 1), (44, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (22, 1), (45, 1), (51, 1), (63, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1), (45, 1)] }, { coefficient := -1, powers := [(17, 1), (21, 1), (44, 1), (46, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (44, 1), (51, 1), (63, 1)] }],
  [{ coefficient := 2, powers := [(5, 1), (34, 1), (44, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (40, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (24, 1), (45, 1), (63, 1)] }, { coefficient := 1, powers := [(23, 1), (28, 1), (42, 1), (46, 1)] }, { coefficient := -1, powers := [(23, 1), (28, 1), (47, 1)] }, { coefficient := 1, powers := [(23, 1), (34, 1), (37, 1)] }],
  [{ coefficient := -1, powers := [(19, 1), (26, 1), (54, 1)] }, { coefficient := 1, powers := [(22, 1), (23, 1), (54, 1)] }, { coefficient := -1, powers := [(22, 1), (24, 1), (52, 1), (63, 1)] }, { coefficient := 1, powers := [(22, 1), (54, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(17, 1), (23, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (21, 1), (46, 1)] }, { coefficient := -1, powers := [(17, 1), (22, 1), (51, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(28, 1), (42, 1), (46, 1)] }, { coefficient := -1, powers := [(28, 1), (47, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1)] }],
  [{ coefficient := -1, powers := [(22, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (28, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(54, 1)] }],
  [{ coefficient := 1, powers := [(47, 1)] }],
  [{ coefficient := 1, powers := [(28, 1)] }],
  [{ coefficient := -1, powers := [(22, 1), (39, 1), (63, 1)] }, { coefficient := 2, powers := [(22, 1)] }],
  [{ coefficient := 1, powers := [(17, 1)] }],
  [{ coefficient := -1, powers := [(16, 1), (22, 1), (51, 1), (63, 1)] }, { coefficient := -1, powers := [(16, 1), (22, 1)] }],
  [{ coefficient := -1, powers := [(17, 1), (27, 1)] }],
  [{ coefficient := 2, powers := [(5, 1), (33, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (24, 1)] }],
  [{ coefficient := 2, powers := [(5, 1), (14, 1), (34, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (14, 1), (34, 1), (40, 1)] }],
  [{ coefficient := -1, powers := [(17, 1), (28, 1)] }],
  [{ coefficient := -2, powers := [(5, 1), (34, 1), (54, 1)] }, { coefficient := -1, powers := [(8, 1), (34, 1), (40, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(16, 1), (22, 1), (42, 1), (44, 1), (54, 1), (63, 1)] }, { coefficient := -1, powers := [(16, 1), (22, 1), (42, 1), (51, 1), (54, 1), (63, 1)] }, { coefficient := -1, powers := [(16, 1), (22, 1), (42, 1), (54, 1)] }, { coefficient := -1, powers := [(16, 1), (28, 1), (42, 1), (46, 1), (49, 1)] }, { coefficient := -1, powers := [(16, 1), (34, 1), (37, 1), (49, 1)] }],
  [{ coefficient := 2, powers := [(5, 1), (34, 1), (36, 1), (54, 1), (59, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (36, 1), (40, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(19, 1), (45, 1), (54, 1)] }, { coefficient := 1, powers := [(37, 1), (60, 1)] }, { coefficient := 1, powers := [(47, 1), (54, 1)] }],
  [{ coefficient := -2, powers := [(5, 1), (7, 1), (20, 1), (34, 1), (54, 1), (59, 1)] }, { coefficient := -1, powers := [(7, 1), (8, 1), (20, 1), (34, 1), (40, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (22, 1), (60, 1)] }],
  [{ coefficient := 2, powers := [(5, 1), (14, 1), (25, 1), (34, 1), (44, 1), (54, 1)] }, { coefficient := 2, powers := [(5, 1), (14, 1), (33, 1), (34, 1), (36, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (14, 1), (25, 1), (34, 1), (40, 1), (44, 1)] }, { coefficient := 1, powers := [(8, 1), (14, 1), (33, 1), (34, 1), (36, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (17, 1), (28, 1), (40, 1)] }, { coefficient := 2, powers := [(1, 1), (5, 1), (34, 1), (39, 1), (54, 1)] }, { coefficient := 1, powers := [(1, 1), (8, 1), (34, 1), (39, 1), (40, 1)] }, { coefficient := 2, powers := [(4, 1), (5, 1), (30, 1), (34, 1), (54, 1)] }, { coefficient := 1, powers := [(4, 1), (8, 1), (30, 1), (34, 1), (40, 1)] }, { coefficient := 2, powers := [(5, 1), (10, 1), (20, 1), (34, 1), (54, 1)] }, { coefficient := -2, powers := [(5, 1), (14, 1), (20, 1), (34, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (10, 1), (20, 1), (34, 1), (40, 1)] }, { coefficient := -1, powers := [(8, 1), (14, 1), (20, 1), (34, 1), (40, 1)] }, { coefficient := -1, powers := [(12, 1), (18, 1), (28, 1), (42, 1), (46, 1)] }, { coefficient := 1, powers := [(12, 1), (18, 1), (28, 1), (47, 1)] }, { coefficient := -1, powers := [(12, 1), (18, 1), (34, 1), (37, 1)] }, { coefficient := -1, powers := [(12, 1), (22, 1), (24, 1), (45, 1), (63, 1)] }, { coefficient := -1, powers := [(12, 1), (23, 1), (28, 1), (42, 1), (46, 1)] }, { coefficient := 1, powers := [(12, 1), (23, 1), (28, 1), (47, 1)] }, { coefficient := -1, powers := [(12, 1), (23, 1), (34, 1), (37, 1)] }, { coefficient := -1, powers := [(17, 1), (18, 1), (28, 1), (46, 1), (49, 1)] }, { coefficient := 1, powers := [(17, 1), (19, 1), (28, 1), (49, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (23, 1), (54, 1)] }, { coefficient := -1, powers := [(17, 1), (22, 1), (24, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (40, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1)] }, { coefficient := 1, powers := [(12, 1), (22, 1), (39, 1), (63, 1)] }, { coefficient := -1, powers := [(12, 1), (22, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1), (49, 1), (51, 1), (63, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1), (49, 1)] }]
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
    (values : Fin 65 → R) :
    ¬ ∀ index : Fin 50,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component39.SelectedLeafB4_7_0.selectedHasNoCommonZero

end Krenn.Component39.SelectedLeafB4_7_0
