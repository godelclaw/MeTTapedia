import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component39.SelectedLeafB5_2_2_5_2

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "9f9f4f1f573ee790c829aa9c28292448c4f6db0d7a564457f6e3e4cbe1c48cbe"
def certificateSHA256 : String := "359e338279fdca59483588891f42e50ec1856ac24c0698b66619cda3d0311e49"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 44 → Fin 676 := ![
  180,
  184,
  187,
  190,
  191,
  192,
  193,
  251,
  302,
  303,
  319,
  343,
  350,
  367,
  396,
  419,
  421,
  425,
  427,
  431,
  440,
  451,
  452,
  460,
  482,
  510,
  535,
  580,
  581,
  618,
  620,
  621,
  623,
  625,
  633,
  637,
  660,
  661,
  663,
  666,
  669,
  670,
  672,
  675
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 44 → SparsePoly (Fin 68) := ![
  [{ coefficient := 1, powers := [(12, 1), (23, 1)] }, { coefficient := 1, powers := [(16, 1), (18, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (45, 1)] }, { coefficient := 1, powers := [(17, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (18, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (45, 1)] }, { coefficient := -1, powers := [(27, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (54, 1)] }, { coefficient := 1, powers := [(28, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (42, 1)] }, { coefficient := 1, powers := [(26, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (53, 1)] }, { coefficient := 1, powers := [(28, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (23, 1), (45, 1)] }, { coefficient := 1, powers := [(17, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (49, 1)] }, { coefficient := 1, powers := [(18, 1), (49, 1)] }, { coefficient := 1, powers := [(23, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (54, 1)] }, { coefficient := 1, powers := [(18, 1), (54, 1)] }, { coefficient := 1, powers := [(24, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1), (51, 1)] }, { coefficient := 1, powers := [(18, 1), (42, 1), (51, 1)] }, { coefficient := 1, powers := [(42, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (42, 1), (52, 1)] }, { coefficient := 1, powers := [(12, 1), (27, 1), (42, 1)] }, { coefficient := 1, powers := [(17, 1), (21, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (28, 1), (59, 1)] }, { coefficient := 1, powers := [(21, 1), (53, 1)] }, { coefficient := 1, powers := [(28, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (31, 1), (44, 1)] }, { coefficient := 1, powers := [(26, 1), (44, 1), (49, 1)] }, { coefficient := 1, powers := [(27, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (23, 1), (39, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1), (44, 1)] }, { coefficient := 1, powers := [(16, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (47, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1)] }, { coefficient := 1, powers := [(16, 1), (26, 1), (47, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (49, 1)] }, { coefficient := 1, powers := [(12, 1), (26, 1)] }, { coefficient := 1, powers := [(16, 1), (21, 1), (49, 1)] }, { coefficient := 1, powers := [(16, 1), (31, 1), (35, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1)] }, { coefficient := 1, powers := [(12, 1), (28, 1)] }, { coefficient := 1, powers := [(16, 1), (21, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (34, 1)] }, { coefficient := 1, powers := [(21, 1), (42, 1)] }, { coefficient := 1, powers := [(26, 1), (42, 1)] }, { coefficient := 1, powers := [(34, 1), (35, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (31, 1)] }, { coefficient := 1, powers := [(21, 1), (49, 1)] }, { coefficient := 1, powers := [(26, 1), (49, 1)] }, { coefficient := 1, powers := [(31, 1), (35, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (54, 1)] }, { coefficient := 1, powers := [(28, 1), (40, 1)] }, { coefficient := 1, powers := [(28, 1), (46, 1), (49, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1), (52, 1)] }, { coefficient := 1, powers := [(3, 1), (60, 1)] }, { coefficient := 1, powers := [(18, 1), (42, 1), (52, 1)] }, { coefficient := 1, powers := [(42, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1), (53, 1)] }, { coefficient := 1, powers := [(18, 1), (42, 1), (53, 1)] }, { coefficient := 1, powers := [(18, 1), (57, 1)] }, { coefficient := 1, powers := [(24, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1), (49, 1)] }, { coefficient := 1, powers := [(6, 1), (60, 1)] }, { coefficient := 1, powers := [(23, 1), (45, 1), (49, 1)] }, { coefficient := 1, powers := [(42, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (35, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1)] }, { coefficient := 1, powers := [(16, 1), (21, 1)] }, { coefficient := 1, powers := [(16, 1), (26, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (34, 1), (53, 1)] }, { coefficient := 1, powers := [(21, 1), (42, 1), (53, 1)] }, { coefficient := 1, powers := [(21, 1), (57, 1)] }, { coefficient := 1, powers := [(28, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (31, 1), (46, 1)] }, { coefficient := 1, powers := [(22, 1), (49, 1)] }, { coefficient := 1, powers := [(26, 1), (40, 1)] }, { coefficient := 1, powers := [(26, 1), (46, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1)] }, { coefficient := 1, powers := [(6, 1), (59, 1)] }, { coefficient := 1, powers := [(23, 1), (39, 1)] }, { coefficient := 1, powers := [(23, 1), (44, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (51, 1)] }, { coefficient := 1, powers := [(3, 1), (59, 1)] }, { coefficient := 1, powers := [(18, 1), (51, 1)] }, { coefficient := 1, powers := [(18, 1), (56, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (42, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (21, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1), (42, 1)] }, { coefficient := 1, powers := [(12, 1), (21, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1), (28, 1), (42, 1)] }, { coefficient := 1, powers := [(17, 1), (21, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (46, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1), (46, 1)] }, { coefficient := 1, powers := [(12, 1), (28, 1), (46, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1), (54, 1)] }, { coefficient := 1, powers := [(16, 1), (28, 1), (40, 1)] }, { coefficient := 1, powers := [(16, 1), (31, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (47, 1), (49, 1)] }, { coefficient := 1, powers := [(5, 1), (26, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (49, 1)] }, { coefficient := 1, powers := [(12, 1), (26, 1), (47, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (49, 1)] }, { coefficient := 1, powers := [(17, 1), (26, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (47, 1), (53, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (53, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1), (57, 1)] }, { coefficient := 1, powers := [(16, 1), (28, 1), (47, 1)] }, { coefficient := 1, powers := [(16, 1), (34, 1), (37, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (28, 1), (60, 1)] }, { coefficient := 1, powers := [(3, 1), (31, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (34, 1), (54, 1)] }, { coefficient := 1, powers := [(21, 1), (42, 1), (54, 1)] }, { coefficient := 1, powers := [(21, 1), (49, 1), (57, 1)] }, { coefficient := 1, powers := [(28, 1), (42, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (22, 1), (60, 1)] }, { coefficient := 1, powers := [(6, 1), (31, 1), (47, 1)] }, { coefficient := 1, powers := [(6, 1), (34, 1), (40, 1)] }, { coefficient := 1, powers := [(22, 1), (42, 1), (49, 1)] }, { coefficient := 1, powers := [(26, 1), (40, 1), (42, 1)] }, { coefficient := 1, powers := [(26, 1), (47, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (42, 1), (54, 1)] }, { coefficient := 1, powers := [(22, 1), (49, 1), (57, 1)] }, { coefficient := 1, powers := [(28, 1), (40, 1), (42, 1)] }, { coefficient := 1, powers := [(28, 1), (47, 1), (49, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1), (42, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (37, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (47, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (28, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (22, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1), (47, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (40, 1)] }, { coefficient := 1, powers := [(12, 1), (22, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1), (28, 1), (47, 1)] }, { coefficient := 1, powers := [(12, 1), (34, 1), (37, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (54, 1)] }, { coefficient := 1, powers := [(17, 1), (28, 1), (40, 1)] }, { coefficient := 1, powers := [(17, 1), (31, 1), (37, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (61, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(40, 1)] }],
  [{ coefficient := 1, powers := [(57, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (65, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(28, 1), (66, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(60, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 44 → SparsePoly (Fin 68) := ![
  [{ coefficient := -1, powers := [(3, 1), (34, 1), (37, 1), (59, 1), (65, 1)] }, { coefficient := 1, powers := [(5, 1), (26, 1), (31, 1), (34, 1), (37, 1), (42, 1), (53, 2), (65, 1), (66, 1)] }, { coefficient := 1, powers := [(5, 1), (26, 1), (31, 1), (34, 1), (37, 1), (45, 1), (53, 2), (66, 1)] }, { coefficient := -1, powers := [(5, 1), (28, 1), (31, 1), (34, 1), (37, 1), (42, 1), (53, 1), (65, 1), (66, 1)] }, { coefficient := -1, powers := [(5, 1), (28, 1), (31, 1), (34, 1), (37, 1), (45, 1), (53, 1), (66, 1)] }, { coefficient := -1, powers := [(21, 1), (34, 1), (37, 1), (53, 1), (65, 1), (66, 1)] }, { coefficient := 2, powers := [(26, 1), (34, 1), (35, 1), (37, 1), (53, 1), (59, 1), (65, 1), (66, 1)] }, { coefficient := 1, powers := [(26, 1), (34, 1), (37, 1), (53, 1), (65, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(5, 2), (21, 1), (24, 1), (26, 1), (31, 1), (34, 1), (53, 2), (62, 1), (66, 1)] }, { coefficient := 1, powers := [(5, 2), (21, 1), (24, 1), (28, 1), (31, 1), (34, 1), (53, 1), (62, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (34, 1), (37, 1), (49, 1), (59, 1), (65, 1)] }, { coefficient := -1, powers := [(5, 1), (26, 1), (31, 1), (34, 1), (37, 1), (42, 1), (49, 1), (53, 2), (65, 1), (66, 1)] }, { coefficient := 1, powers := [(5, 1), (28, 1), (31, 1), (34, 1), (37, 1), (42, 1), (49, 1), (53, 1), (65, 1), (66, 1)] }, { coefficient := 2, powers := [(21, 1), (34, 1), (37, 1), (44, 1), (49, 1), (53, 1), (66, 1)] }, { coefficient := 2, powers := [(21, 1), (34, 1), (37, 1), (49, 1), (53, 1), (61, 1), (66, 1)] }, { coefficient := 1, powers := [(21, 1), (34, 1), (37, 1), (49, 1), (53, 1), (65, 1), (66, 1)] }, { coefficient := -2, powers := [(26, 1), (34, 1), (35, 1), (37, 1), (49, 1), (53, 1), (59, 1), (65, 1), (66, 1)] }, { coefficient := 1, powers := [(26, 1), (34, 1), (37, 1), (49, 1), (53, 1), (61, 1), (66, 1)] }, { coefficient := -1, powers := [(26, 1), (34, 1), (37, 1), (49, 1), (53, 1), (65, 1), (66, 1)] }, { coefficient := -2, powers := [(27, 1), (34, 1), (37, 1), (49, 1), (53, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(5, 2), (12, 1), (24, 1), (26, 1), (31, 1), (34, 1), (53, 2), (62, 1), (66, 1)] }, { coefficient := -1, powers := [(5, 2), (12, 1), (24, 1), (28, 1), (31, 1), (34, 1), (53, 1), (62, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (16, 1), (47, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (17, 1), (46, 1), (59, 1)] }, { coefficient := -1, powers := [(5, 1), (17, 1), (26, 1), (31, 1), (47, 1), (53, 2), (66, 1)] }, { coefficient := 1, powers := [(5, 1), (17, 1), (28, 1), (31, 1), (47, 1), (53, 1), (66, 1)] }, { coefficient := -1, powers := [(5, 1), (34, 1), (53, 1), (66, 1)] }, { coefficient := 1, powers := [(5, 1), (42, 1), (59, 1)] }, { coefficient := 1, powers := [(16, 1), (21, 1), (47, 1), (53, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(16, 1), (21, 1), (49, 1), (53, 2), (66, 1)] }, { coefficient := -1, powers := [(16, 1), (28, 1), (49, 1), (53, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (42, 1), (49, 1), (53, 1), (66, 1)] }, { coefficient := 1, powers := [(6, 1), (17, 1), (31, 1), (53, 1), (66, 1)] }, { coefficient := 1, powers := [(17, 1), (21, 1), (49, 1), (53, 1), (66, 1)] }, { coefficient := 1, powers := [(17, 1), (26, 1), (49, 1), (53, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (26, 1), (31, 1), (34, 1), (37, 1), (53, 2), (66, 1)] }, { coefficient := 1, powers := [(5, 1), (28, 1), (31, 1), (34, 1), (37, 1), (53, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (16, 1), (26, 1), (31, 1), (34, 1), (37, 1), (45, 1), (53, 2), (66, 1)] }, { coefficient := 1, powers := [(5, 1), (16, 1), (28, 1), (31, 1), (34, 1), (37, 1), (45, 1), (53, 1), (66, 1)] }, { coefficient := -2, powers := [(16, 1), (21, 1), (34, 1), (37, 1), (44, 1), (53, 1), (66, 1)] }, { coefficient := -2, powers := [(16, 1), (21, 1), (34, 1), (37, 1), (53, 1), (61, 1), (66, 1)] }, { coefficient := -1, powers := [(16, 1), (26, 1), (34, 1), (37, 1), (53, 1), (61, 1), (66, 1)] }, { coefficient := 2, powers := [(16, 1), (27, 1), (34, 1), (37, 1), (53, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(5, 2), (26, 1), (31, 1), (34, 1), (42, 1), (51, 1), (53, 2), (66, 1)] }, { coefficient := 1, powers := [(5, 2), (28, 1), (31, 1), (34, 1), (42, 1), (51, 1), (53, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(5, 2), (26, 1), (31, 1), (34, 1), (49, 1), (53, 3), (66, 1)] }, { coefficient := 1, powers := [(5, 2), (26, 1), (31, 1), (34, 1), (53, 2), (54, 1), (66, 1)] }, { coefficient := 1, powers := [(5, 2), (28, 1), (31, 1), (34, 1), (49, 1), (53, 2), (66, 1)] }, { coefficient := -1, powers := [(5, 2), (28, 1), (31, 1), (34, 1), (53, 1), (54, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(5, 2), (24, 1), (26, 1), (31, 1), (34, 1), (53, 2), (62, 1), (66, 1)] }, { coefficient := -1, powers := [(5, 2), (24, 1), (28, 1), (31, 1), (34, 1), (53, 1), (62, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(66, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (16, 1), (34, 1), (37, 1), (53, 1), (66, 1)] }],
  [{ coefficient := 2, powers := [(31, 1), (34, 1), (35, 1), (37, 1), (53, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (49, 1), (53, 2), (66, 1)] }, { coefficient := 1, powers := [(28, 1), (49, 1), (53, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (47, 1), (53, 2), (66, 1)] }, { coefficient := -2, powers := [(34, 1), (35, 1), (37, 1), (53, 1), (59, 1), (66, 1)] }, { coefficient := -1, powers := [(34, 1), (37, 1), (53, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (47, 1), (59, 1)] }, { coefficient := -1, powers := [(21, 1), (47, 1), (53, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (31, 1), (53, 2), (66, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (16, 1), (34, 1), (37, 1), (44, 1), (53, 1), (66, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (53, 2), (66, 1)] }, { coefficient := -1, powers := [(16, 1), (21, 1), (47, 1), (53, 2), (66, 1)] }, { coefficient := 2, powers := [(16, 1), (34, 1), (35, 1), (37, 1), (53, 1), (59, 1), (66, 1)] }, { coefficient := 1, powers := [(16, 1), (34, 1), (37, 1), (53, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (42, 1), (53, 1), (66, 1)] }, { coefficient := -1, powers := [(3, 1), (17, 1), (59, 1)] }, { coefficient := -1, powers := [(17, 1), (21, 1), (53, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(5, 2), (26, 1), (31, 1), (34, 1), (53, 3), (66, 1)] }, { coefficient := -1, powers := [(5, 2), (28, 1), (31, 1), (34, 1), (53, 2), (66, 1)] }],
  [{ coefficient := 1, powers := [(5, 2), (26, 1), (31, 1), (34, 1), (49, 1), (51, 1), (53, 2), (66, 1)] }, { coefficient := -1, powers := [(5, 2), (26, 1), (31, 1), (34, 1), (52, 1), (53, 2), (66, 1)] }, { coefficient := -1, powers := [(5, 2), (28, 1), (31, 1), (34, 1), (49, 1), (51, 1), (53, 1), (66, 1)] }, { coefficient := 1, powers := [(5, 2), (28, 1), (31, 1), (34, 1), (52, 1), (53, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (16, 1), (26, 1), (31, 1), (34, 1), (37, 1), (53, 2), (66, 1)] }, { coefficient := -1, powers := [(5, 1), (16, 1), (28, 1), (31, 1), (34, 1), (37, 1), (53, 1), (66, 1)] }],
  [{ coefficient := 2, powers := [(34, 1), (37, 1), (49, 1), (53, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (31, 1), (53, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(17, 1), (28, 1), (53, 1), (66, 1)] }],
  [{ coefficient := -2, powers := [(16, 1), (31, 1), (34, 1), (35, 1), (37, 1), (53, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(28, 1), (66, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := -1, powers := [(3, 1), (46, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (26, 1), (31, 1), (47, 1), (53, 2), (66, 1)] }, { coefficient := -1, powers := [(5, 1), (28, 1), (31, 1), (47, 1), (53, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (42, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(21, 1), (53, 2), (66, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (31, 1), (53, 1), (66, 1)] }, { coefficient := -1, powers := [(21, 1), (49, 1), (53, 1), (66, 1)] }, { coefficient := -1, powers := [(26, 1), (49, 1), (53, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (53, 2), (66, 1)] }, { coefficient := 1, powers := [(16, 1), (21, 1), (53, 2), (66, 1)] }, { coefficient := 1, powers := [(16, 1), (28, 1), (53, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (53, 1), (66, 1)] }, { coefficient := -1, powers := [(3, 1), (16, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (17, 1), (26, 1), (31, 1), (53, 2), (66, 1)] }, { coefficient := -1, powers := [(5, 1), (17, 1), (28, 1), (31, 1), (53, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (59, 1)] }, { coefficient := -1, powers := [(5, 1), (26, 1), (31, 1), (42, 1), (53, 2), (66, 1)] }, { coefficient := 1, powers := [(5, 1), (28, 1), (31, 1), (42, 1), (53, 1), (66, 1)] }, { coefficient := 1, powers := [(21, 1), (53, 1), (66, 1)] }],
  [{ coefficient := 2, powers := [(16, 1), (21, 1), (34, 1), (37, 1), (49, 1), (53, 1), (66, 1)] }, { coefficient := 1, powers := [(16, 1), (26, 1), (34, 1), (37, 1), (49, 1), (53, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(5, 2), (24, 1), (26, 1), (31, 1), (34, 1), (42, 1), (52, 1), (53, 2), (66, 1)] }, { coefficient := 1, powers := [(5, 2), (24, 1), (28, 1), (31, 1), (34, 1), (42, 1), (52, 1), (53, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (6, 1), (34, 1), (53, 2), (66, 1)] }, { coefficient := -1, powers := [(2, 1), (26, 1), (42, 1), (53, 2), (66, 1)] }, { coefficient := -1, powers := [(3, 1), (8, 1), (34, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (8, 1), (26, 1), (31, 1), (34, 1), (42, 1), (53, 2), (66, 1)] }, { coefficient := -1, powers := [(5, 1), (8, 1), (28, 1), (31, 1), (34, 1), (42, 1), (53, 1), (66, 1)] }, { coefficient := -1, powers := [(6, 1), (16, 1), (21, 1), (34, 1), (53, 2), (66, 1)] }, { coefficient := -1, powers := [(6, 1), (16, 1), (28, 1), (34, 1), (53, 1), (66, 1)] }, { coefficient := -1, powers := [(8, 1), (21, 1), (34, 1), (53, 1), (66, 1)] }, { coefficient := -1, powers := [(16, 1), (21, 1), (26, 1), (42, 1), (53, 2), (66, 1)] }, { coefficient := -1, powers := [(16, 1), (26, 1), (28, 1), (42, 1), (53, 1), (66, 1)] }, { coefficient := 1, powers := [(17, 1), (21, 1), (26, 1), (53, 2), (66, 1)] }, { coefficient := 1, powers := [(17, 1), (26, 1), (28, 1), (53, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (3, 1), (40, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (5, 1), (26, 1), (31, 1), (40, 1), (42, 1), (53, 2), (66, 1)] }, { coefficient := -1, powers := [(2, 1), (5, 1), (28, 1), (31, 1), (40, 1), (42, 1), (53, 1), (66, 1)] }, { coefficient := -1, powers := [(2, 1), (21, 1), (40, 1), (53, 1), (66, 1)] }, { coefficient := 1, powers := [(2, 1), (22, 1), (49, 1), (53, 1), (66, 1)] }, { coefficient := 1, powers := [(3, 1), (12, 1), (21, 1), (46, 1), (59, 1)] }, { coefficient := -1, powers := [(3, 1), (12, 1), (22, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (16, 1), (22, 1), (49, 1), (59, 1)] }, { coefficient := -1, powers := [(5, 2), (18, 1), (26, 1), (31, 1), (34, 1), (49, 1), (51, 1), (53, 2), (66, 1)] }, { coefficient := 1, powers := [(5, 2), (18, 1), (26, 1), (31, 1), (34, 1), (52, 1), (53, 2), (66, 1)] }, { coefficient := 1, powers := [(5, 2), (18, 1), (28, 1), (31, 1), (34, 1), (49, 1), (51, 1), (53, 1), (66, 1)] }, { coefficient := -1, powers := [(5, 2), (18, 1), (28, 1), (31, 1), (34, 1), (52, 1), (53, 1), (66, 1)] }, { coefficient := 1, powers := [(5, 2), (26, 1), (31, 2), (42, 1), (53, 2), (66, 1)] }, { coefficient := -1, powers := [(5, 2), (28, 1), (31, 2), (42, 1), (53, 1), (66, 1)] }, { coefficient := -1, powers := [(5, 1), (12, 1), (21, 1), (26, 1), (31, 1), (47, 1), (53, 2), (66, 1)] }, { coefficient := 1, powers := [(5, 1), (12, 1), (21, 1), (28, 1), (31, 1), (47, 1), (53, 1), (66, 1)] }, { coefficient := 1, powers := [(5, 1), (12, 1), (22, 1), (26, 1), (31, 1), (42, 1), (53, 2), (66, 1)] }, { coefficient := -1, powers := [(5, 1), (12, 1), (22, 1), (28, 1), (31, 1), (42, 1), (53, 1), (66, 1)] }, { coefficient := -1, powers := [(5, 1), (17, 1), (22, 1), (26, 1), (31, 1), (49, 1), (53, 2), (66, 1)] }, { coefficient := 1, powers := [(5, 1), (17, 1), (22, 1), (28, 1), (31, 1), (49, 1), (53, 1), (66, 1)] }, { coefficient := -2, powers := [(5, 1), (21, 1), (31, 1), (53, 1), (66, 1)] }, { coefficient := 1, powers := [(5, 1), (21, 1), (49, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (16, 1), (22, 1), (31, 1), (53, 1), (66, 1)] }, { coefficient := -1, powers := [(12, 1), (21, 1), (22, 1), (53, 1), (66, 1)] }, { coefficient := 1, powers := [(16, 1), (21, 1), (22, 1), (49, 1), (53, 1), (66, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1), (26, 1), (49, 1), (53, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (12, 1), (34, 1), (37, 1), (59, 1)] }, { coefficient := -1, powers := [(3, 1), (16, 1), (34, 1), (37, 1), (49, 1), (59, 1)] }, { coefficient := -1, powers := [(5, 1), (12, 1), (26, 1), (31, 1), (34, 1), (37, 1), (42, 1), (53, 2), (66, 1)] }, { coefficient := 1, powers := [(5, 1), (12, 1), (28, 1), (31, 1), (34, 1), (37, 1), (42, 1), (53, 1), (66, 1)] }, { coefficient := 1, powers := [(5, 1), (16, 1), (26, 1), (31, 1), (34, 1), (37, 1), (42, 1), (49, 1), (53, 2), (66, 1)] }, { coefficient := -1, powers := [(5, 1), (16, 1), (28, 1), (31, 1), (34, 1), (37, 1), (42, 1), (49, 1), (53, 1), (66, 1)] }, { coefficient := 1, powers := [(12, 1), (21, 1), (34, 1), (37, 1), (53, 1), (66, 1)] }, { coefficient := -2, powers := [(12, 1), (26, 1), (34, 1), (35, 1), (37, 1), (53, 1), (59, 1), (66, 1)] }, { coefficient := -1, powers := [(12, 1), (26, 1), (34, 1), (37, 1), (53, 1), (66, 1)] }, { coefficient := -1, powers := [(16, 1), (21, 1), (34, 1), (37, 1), (49, 1), (53, 1), (66, 1)] }, { coefficient := 2, powers := [(16, 1), (26, 1), (34, 1), (35, 1), (37, 1), (49, 1), (53, 1), (59, 1), (66, 1)] }, { coefficient := 1, powers := [(16, 1), (26, 1), (34, 1), (37, 1), (49, 1), (53, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (51, 1)] }, { coefficient := 1, powers := [(18, 1), (51, 1)] }, { coefficient := 1, powers := [(18, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (3, 1), (37, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (5, 1), (26, 1), (31, 1), (37, 1), (42, 1), (53, 2), (66, 1)] }, { coefficient := -1, powers := [(2, 1), (5, 1), (28, 1), (31, 1), (37, 1), (42, 1), (53, 1), (66, 1)] }, { coefficient := -1, powers := [(2, 1), (6, 1), (22, 1), (53, 2), (66, 1)] }, { coefficient := -1, powers := [(2, 1), (21, 1), (37, 1), (53, 1), (66, 1)] }, { coefficient := -1, powers := [(3, 1), (5, 2), (26, 1), (31, 1), (34, 1), (53, 3), (66, 1)] }, { coefficient := 1, powers := [(3, 1), (5, 2), (28, 1), (31, 1), (34, 1), (53, 2), (66, 1)] }, { coefficient := 1, powers := [(3, 1), (8, 1), (21, 1), (46, 1), (59, 1)] }, { coefficient := -1, powers := [(3, 1), (8, 1), (22, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 2), (26, 1), (28, 1), (31, 1), (42, 1), (53, 2), (66, 1)] }, { coefficient := -1, powers := [(5, 2), (28, 2), (31, 1), (42, 1), (53, 1), (66, 1)] }, { coefficient := -1, powers := [(5, 1), (6, 1), (16, 1), (26, 1), (31, 1), (34, 1), (37, 1), (53, 2), (66, 1)] }, { coefficient := 1, powers := [(5, 1), (6, 1), (16, 1), (28, 1), (31, 1), (34, 1), (37, 1), (53, 1), (66, 1)] }, { coefficient := -1, powers := [(5, 1), (8, 1), (21, 1), (26, 1), (31, 1), (47, 1), (53, 2), (66, 1)] }, { coefficient := 1, powers := [(5, 1), (8, 1), (21, 1), (28, 1), (31, 1), (47, 1), (53, 1), (66, 1)] }, { coefficient := 1, powers := [(5, 1), (8, 1), (22, 1), (26, 1), (31, 1), (42, 1), (53, 2), (66, 1)] }, { coefficient := -1, powers := [(5, 1), (8, 1), (22, 1), (28, 1), (31, 1), (42, 1), (53, 1), (66, 1)] }, { coefficient := 1, powers := [(5, 1), (21, 1), (26, 1), (53, 2), (66, 1)] }, { coefficient := -1, powers := [(5, 1), (21, 1), (28, 1), (53, 1), (66, 1)] }, { coefficient := -1, powers := [(6, 1), (16, 1), (21, 1), (22, 1), (53, 2), (66, 1)] }, { coefficient := -1, powers := [(6, 1), (16, 1), (22, 1), (28, 1), (53, 1), (66, 1)] }, { coefficient := -1, powers := [(8, 1), (21, 1), (22, 1), (53, 1), (66, 1)] }]
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
    (values : Fin 68 → R) :
    ¬ ∀ index : Fin 44,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component39.SelectedLeafB5_2_2_5_2.selectedHasNoCommonZero

end Krenn.Component39.SelectedLeafB5_2_2_5_2
