import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component39.SelectedLeafB0_2_2

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "d7d6efc1f3c0d2bcdd2e5c749d9c802d7118b49eb2fc6188dc1d19110fb2f074"
def certificateSHA256 : String := "9b4a679de8e4b5f5be53909f33cb6381fda3df5554b3258fe0b84d3076a61b2f"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 47 → Fin 670 := ![
  180,
  181,
  183,
  187,
  191,
  192,
  250,
  254,
  276,
  277,
  300,
  301,
  303,
  313,
  322,
  345,
  419,
  425,
  429,
  430,
  433,
  434,
  439,
  440,
  458,
  463,
  467,
  482,
  495,
  521,
  566,
  580,
  581,
  604,
  605,
  607,
  618,
  620,
  621,
  623,
  637,
  644,
  660,
  661,
  663,
  666,
  669
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 47 → SparsePoly (Fin 63) := ![
  [{ coefficient := 1, powers := [(12, 1), (23, 1)] }, { coefficient := 1, powers := [(16, 1), (18, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (24, 1)] }, { coefficient := 1, powers := [(16, 1), (18, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (42, 1)] }, { coefficient := 1, powers := [(17, 1), (18, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (18, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (54, 1)] }, { coefficient := 1, powers := [(28, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (42, 1)] }, { coefficient := 1, powers := [(26, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (23, 1), (44, 1)] }, { coefficient := 1, powers := [(16, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (24, 1), (44, 1)] }, { coefficient := 1, powers := [(16, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (23, 1), (42, 1)] }, { coefficient := 1, powers := [(17, 1), (18, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (23, 1), (47, 1)] }, { coefficient := 1, powers := [(17, 1), (19, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1)] }, { coefficient := 1, powers := [(18, 1), (42, 1)] }, { coefficient := 1, powers := [(23, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (42, 1)] }, { coefficient := 1, powers := [(23, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (54, 1)] }, { coefficient := 1, powers := [(18, 1), (54, 1)] }, { coefficient := 1, powers := [(24, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (44, 1)] }, { coefficient := 1, powers := [(12, 1), (56, 1)] }, { coefficient := 1, powers := [(16, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1), (54, 1)] }, { coefficient := 1, powers := [(24, 1), (44, 1), (49, 1)] }, { coefficient := 1, powers := [(54, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (44, 1), (49, 1)] }, { coefficient := 1, powers := [(12, 1), (26, 1), (44, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (47, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1)] }, { coefficient := 1, powers := [(16, 1), (26, 1), (47, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1)] }, { coefficient := 1, powers := [(12, 1), (28, 1)] }, { coefficient := 1, powers := [(16, 1), (21, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (59, 1)] }, { coefficient := 1, powers := [(16, 1), (19, 1), (51, 1)] }, { coefficient := 1, powers := [(16, 1), (19, 1), (56, 1)] }, { coefficient := 1, powers := [(16, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (60, 1)] }, { coefficient := 1, powers := [(12, 1), (47, 1)] }, { coefficient := 1, powers := [(17, 1), (19, 1), (52, 1)] }, { coefficient := 1, powers := [(17, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (59, 1)] }, { coefficient := 1, powers := [(16, 1), (24, 1), (39, 1)] }, { coefficient := 1, powers := [(16, 1), (24, 1), (44, 1)] }, { coefficient := 1, powers := [(16, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (60, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (45, 1)] }, { coefficient := 1, powers := [(12, 1), (57, 1)] }, { coefficient := 1, powers := [(17, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (39, 1)] }, { coefficient := 1, powers := [(16, 1), (44, 1)] }, { coefficient := 1, powers := [(16, 1), (51, 1)] }, { coefficient := 1, powers := [(16, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (54, 1)] }, { coefficient := 1, powers := [(28, 1), (40, 1)] }, { coefficient := 1, powers := [(28, 1), (46, 1), (49, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1), (53, 1)] }, { coefficient := 1, powers := [(24, 1), (39, 1)] }, { coefficient := 1, powers := [(24, 1), (44, 1)] }, { coefficient := 1, powers := [(53, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1), (54, 1)] }, { coefficient := 1, powers := [(24, 1), (45, 1), (49, 1)] }, { coefficient := 1, powers := [(42, 1), (54, 1)] }, { coefficient := 1, powers := [(49, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1), (51, 1)] }, { coefficient := 1, powers := [(19, 1), (51, 1)] }, { coefficient := 1, powers := [(19, 1), (56, 1)] }, { coefficient := 1, powers := [(46, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (35, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1)] }, { coefficient := 1, powers := [(16, 1), (21, 1)] }, { coefficient := 1, powers := [(16, 1), (26, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (44, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1), (44, 1)] }, { coefficient := 1, powers := [(12, 1), (28, 1), (44, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (23, 1), (60, 1)] }, { coefficient := 1, powers := [(12, 1), (23, 1), (47, 1)] }, { coefficient := 1, powers := [(17, 1), (19, 1), (49, 1)] }, { coefficient := 1, powers := [(17, 1), (23, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (42, 1), (53, 1)] }, { coefficient := 1, powers := [(22, 1), (57, 1)] }, { coefficient := 1, powers := [(28, 1), (47, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1)] }, { coefficient := 1, powers := [(6, 1), (59, 1)] }, { coefficient := 1, powers := [(23, 1), (39, 1)] }, { coefficient := 1, powers := [(23, 1), (44, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (51, 1)] }, { coefficient := 1, powers := [(3, 1), (59, 1)] }, { coefficient := 1, powers := [(18, 1), (51, 1)] }, { coefficient := 1, powers := [(18, 1), (56, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (35, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1)] }, { coefficient := 1, powers := [(3, 1), (23, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (18, 1), (59, 1)] }, { coefficient := 1, powers := [(18, 1)] }, { coefficient := 1, powers := [(23, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (35, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (42, 1), (49, 1)] }, { coefficient := 1, powers := [(3, 1), (23, 1), (60, 1)] }, { coefficient := 1, powers := [(6, 1), (18, 1), (60, 1)] }, { coefficient := 1, powers := [(18, 1), (42, 1), (49, 1)] }, { coefficient := 1, powers := [(23, 1), (42, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (39, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (45, 1), (53, 1)] }, { coefficient := 1, powers := [(24, 1), (39, 1), (42, 1)] }, { coefficient := 1, powers := [(24, 1), (45, 1)] }, { coefficient := 1, powers := [(42, 1), (53, 1)] }, { coefficient := 1, powers := [(57, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (42, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (21, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1), (42, 1)] }, { coefficient := 1, powers := [(12, 1), (21, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1), (28, 1), (42, 1)] }, { coefficient := 1, powers := [(17, 1), (21, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (46, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1), (46, 1)] }, { coefficient := 1, powers := [(12, 1), (28, 1), (46, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1), (54, 1)] }, { coefficient := 1, powers := [(16, 1), (28, 1), (40, 1)] }, { coefficient := 1, powers := [(16, 1), (31, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (47, 1), (49, 1)] }, { coefficient := 1, powers := [(5, 1), (26, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (49, 1)] }, { coefficient := 1, powers := [(12, 1), (26, 1), (47, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (49, 1)] }, { coefficient := 1, powers := [(17, 1), (26, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (47, 1), (53, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (53, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1), (57, 1)] }, { coefficient := 1, powers := [(16, 1), (28, 1), (47, 1)] }, { coefficient := 1, powers := [(16, 1), (34, 1), (37, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (42, 1), (54, 1)] }, { coefficient := 1, powers := [(22, 1), (49, 1), (57, 1)] }, { coefficient := 1, powers := [(28, 1), (40, 1), (42, 1)] }, { coefficient := 1, powers := [(28, 1), (47, 1), (49, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1), (42, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (36, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (44, 1), (51, 1)] }, { coefficient := 1, powers := [(39, 1)] }, { coefficient := 1, powers := [(44, 1)] }, { coefficient := 1, powers := [(51, 1)] }, { coefficient := 1, powers := [(56, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (37, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (47, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (28, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (22, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1), (47, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (40, 1)] }, { coefficient := 1, powers := [(12, 1), (22, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1), (28, 1), (47, 1)] }, { coefficient := 1, powers := [(12, 1), (34, 1), (37, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (54, 1)] }, { coefficient := 1, powers := [(17, 1), (28, 1), (40, 1)] }, { coefficient := 1, powers := [(17, 1), (31, 1), (37, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1)] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(40, 1)] }],
  [{ coefficient := 1, powers := [(57, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 47 → SparsePoly (Fin 63) := ![
  [{ coefficient := -1, powers := [(26, 1), (44, 1), (47, 1), (53, 1)] }, { coefficient := 1, powers := [(26, 1), (47, 1), (51, 1), (53, 1)] }, { coefficient := 1, powers := [(28, 1), (39, 1), (47, 1)] }, { coefficient := 1, powers := [(28, 1), (44, 1), (47, 1)] }, { coefficient := -1, powers := [(28, 1), (47, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (42, 1), (44, 1), (46, 1)] }, { coefficient := -2, powers := [(22, 1), (42, 1), (44, 1)] }, { coefficient := 1, powers := [(22, 1), (45, 1)] }],
  [{ coefficient := -1, powers := [(19, 1), (26, 1), (44, 1), (53, 1)] }, { coefficient := -1, powers := [(19, 1), (26, 1), (53, 1), (56, 1)] }, { coefficient := 1, powers := [(19, 1), (28, 1), (44, 1)] }, { coefficient := 1, powers := [(19, 1), (28, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (39, 1), (47, 1), (54, 1)] }, { coefficient := -1, powers := [(21, 1), (42, 1), (44, 1), (46, 1), (54, 1)] }, { coefficient := 2, powers := [(22, 1), (42, 1), (44, 1), (54, 1)] }, { coefficient := 1, powers := [(26, 1), (44, 1), (47, 1), (49, 1), (53, 1)] }, { coefficient := -1, powers := [(26, 1), (47, 1), (49, 1), (51, 1), (53, 1)] }, { coefficient := 1, powers := [(26, 1), (47, 1), (52, 1), (53, 1)] }, { coefficient := 1, powers := [(27, 1), (47, 1), (54, 1)] }, { coefficient := -1, powers := [(28, 1), (44, 1), (47, 1), (49, 1)] }, { coefficient := 1, powers := [(28, 1), (47, 1), (49, 1), (51, 1)] }, { coefficient := -1, powers := [(28, 1), (47, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(16, 1), (18, 1), (39, 1), (47, 1)] }, { coefficient := -1, powers := [(16, 1), (47, 1)] }, { coefficient := -1, powers := [(17, 1), (46, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (53, 1)] }, { coefficient := -1, powers := [(16, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(28, 1), (47, 1)] }],
  [{ coefficient := -1, powers := [(26, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (44, 1), (46, 1), (54, 1)] }, { coefficient := -2, powers := [(22, 1), (44, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(26, 1), (44, 1), (49, 1), (53, 1)] }, { coefficient := 1, powers := [(26, 1), (49, 1), (51, 1), (53, 1)] }, { coefficient := 1, powers := [(28, 1), (44, 1), (49, 1)] }, { coefficient := -1, powers := [(28, 1), (49, 1), (51, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (26, 1), (44, 1), (49, 1), (53, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (26, 1), (49, 1), (51, 1), (53, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (28, 1), (44, 1), (49, 1), (59, 1)] }, { coefficient := -1, powers := [(5, 1), (28, 1), (49, 1), (51, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(16, 1), (26, 1), (52, 1), (53, 1)] }, { coefficient := 1, powers := [(16, 1), (28, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(16, 1), (22, 1), (45, 1)] }, { coefficient := -1, powers := [(16, 1), (27, 1), (47, 1)] }, { coefficient := -1, powers := [(17, 1), (21, 1), (44, 1), (46, 1)] }, { coefficient := 2, powers := [(17, 1), (22, 1), (44, 1)] }],
  [{ coefficient := -1, powers := [(18, 1), (26, 1), (47, 1), (53, 1)] }, { coefficient := 1, powers := [(18, 1), (28, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (26, 1), (42, 1), (53, 1)] }, { coefficient := -1, powers := [(19, 1), (28, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (21, 1), (46, 1)] }, { coefficient := -2, powers := [(17, 1), (22, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(54, 1)] }],
  [{ coefficient := -1, powers := [(23, 1), (39, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (26, 1), (53, 1), (60, 1)] }, { coefficient := -1, powers := [(3, 1), (28, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (26, 1), (44, 1), (53, 1)] }, { coefficient := 1, powers := [(18, 1), (26, 1), (53, 1), (56, 1)] }, { coefficient := -1, powers := [(18, 1), (28, 1), (44, 1)] }, { coefficient := -1, powers := [(18, 1), (28, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (31, 1), (47, 1)] }],
  [{ coefficient := -1, powers := [(21, 1), (46, 1)] }, { coefficient := 1, powers := [(22, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (19, 1), (26, 1), (53, 1), (60, 1)] }, { coefficient := 1, powers := [(3, 1), (19, 1), (28, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(17, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (16, 1), (31, 1), (47, 1)] }, { coefficient := -1, powers := [(12, 1), (21, 1), (42, 1), (46, 1)] }, { coefficient := 2, powers := [(12, 1), (22, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (22, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (16, 1), (26, 1), (53, 1), (60, 1)] }, { coefficient := 1, powers := [(3, 1), (16, 1), (28, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(47, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(23, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(26, 1), (44, 1), (53, 1)] }, { coefficient := -1, powers := [(26, 1), (51, 1), (53, 1)] }, { coefficient := -1, powers := [(28, 1), (44, 1)] }, { coefficient := 1, powers := [(28, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(12, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (31, 1), (47, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (26, 1), (53, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (28, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (26, 1), (44, 1), (53, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (26, 1), (51, 1), (53, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (28, 1), (44, 1), (60, 1)] }, { coefficient := -1, powers := [(5, 1), (28, 1), (51, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (26, 1), (44, 1), (53, 1), (59, 1)] }, { coefficient := -1, powers := [(5, 1), (26, 1), (51, 1), (53, 1), (59, 1)] }, { coefficient := -1, powers := [(5, 1), (28, 1), (44, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (28, 1), (51, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (21, 1), (46, 1)] }, { coefficient := -2, powers := [(12, 1), (22, 1)] }],
  [{ coefficient := 1, powers := [(46, 1)] }],
  [{ coefficient := -1, powers := [(42, 1)] }],
  [{ coefficient := 1, powers := [(53, 1)] }],
  [{ coefficient := -1, powers := [(49, 1)] }],
  [{ coefficient := 1, powers := [(16, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (16, 1), (19, 1), (26, 1), (53, 1), (60, 1)] }, { coefficient := -1, powers := [(3, 1), (16, 1), (19, 1), (28, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(3, 1), (16, 1), (19, 1), (26, 1), (36, 1), (53, 1), (59, 1), (60, 1)] }, { coefficient := -1, powers := [(3, 1), (16, 1), (19, 1), (26, 1), (39, 1), (53, 1), (56, 1), (60, 1)] }, { coefficient := -1, powers := [(3, 1), (16, 1), (19, 1), (26, 1), (44, 1), (51, 1), (53, 1), (60, 1)] }, { coefficient := 1, powers := [(3, 1), (16, 1), (19, 1), (28, 1), (36, 1), (59, 1), (60, 1)] }, { coefficient := 1, powers := [(3, 1), (16, 1), (19, 1), (28, 1), (39, 1), (56, 1), (60, 1)] }, { coefficient := 1, powers := [(3, 1), (16, 1), (19, 1), (28, 1), (44, 1), (51, 1), (60, 1)] }, { coefficient := 1, powers := [(3, 1), (16, 1), (26, 1), (46, 1), (51, 1), (53, 1), (60, 1)] }, { coefficient := -1, powers := [(3, 1), (16, 1), (28, 1), (46, 1), (51, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (26, 1), (44, 1), (53, 1), (60, 1)] }, { coefficient := -1, powers := [(5, 1), (28, 1), (44, 1), (60, 1)] }, { coefficient := -1, powers := [(6, 1), (16, 1), (31, 1), (44, 1), (47, 1), (53, 1)] }, { coefficient := -1, powers := [(8, 1), (31, 1), (44, 1), (47, 1)] }, { coefficient := -1, powers := [(12, 1), (21, 1), (39, 1), (46, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1), (21, 1), (42, 1), (44, 1), (46, 1), (53, 1)] }, { coefficient := -1, powers := [(12, 1), (21, 1), (45, 1), (46, 1), (53, 1)] }, { coefficient := 2, powers := [(12, 1), (22, 1), (39, 1), (57, 1)] }, { coefficient := -2, powers := [(12, 1), (22, 1), (42, 1), (44, 1), (53, 1)] }, { coefficient := 2, powers := [(12, 1), (22, 1), (45, 1), (53, 1)] }, { coefficient := 1, powers := [(16, 1), (26, 1), (47, 1), (52, 1), (53, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1), (47, 1), (54, 1)] }, { coefficient := -1, powers := [(16, 1), (28, 1), (47, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (39, 1), (47, 1), (54, 1)] }, { coefficient := 1, powers := [(23, 1), (44, 1), (47, 1), (54, 1)] }, { coefficient := -1, powers := [(24, 1), (44, 1), (47, 1), (49, 1)] }, { coefficient := -1, powers := [(35, 1), (47, 1), (54, 1), (59, 1)] }, { coefficient := 1, powers := [(37, 1), (60, 1)] }, { coefficient := 1, powers := [(40, 1), (57, 1)] }, { coefficient := -1, powers := [(47, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (34, 1)] }, { coefficient := -1, powers := [(17, 1), (18, 1), (26, 1), (44, 1), (53, 1)] }, { coefficient := -1, powers := [(17, 1), (18, 1), (26, 1), (53, 1), (56, 1)] }, { coefficient := 1, powers := [(17, 1), (18, 1), (28, 1), (44, 1)] }, { coefficient := 1, powers := [(17, 1), (18, 1), (28, 1), (56, 1)] }, { coefficient := -1, powers := [(17, 1), (23, 1), (26, 1), (44, 1), (53, 1)] }, { coefficient := 1, powers := [(17, 1), (23, 1), (26, 1), (51, 1), (53, 1)] }, { coefficient := 1, powers := [(17, 1), (23, 1), (28, 1), (44, 1)] }, { coefficient := -1, powers := [(17, 1), (23, 1), (28, 1), (51, 1)] }, { coefficient := -1, powers := [(17, 1), (26, 1), (53, 1)] }],
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
    (values : Fin 63 → R) :
    ¬ ∀ index : Fin 47,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component39.SelectedLeafB0_2_2.selectedHasNoCommonZero

end Krenn.Component39.SelectedLeafB0_2_2
