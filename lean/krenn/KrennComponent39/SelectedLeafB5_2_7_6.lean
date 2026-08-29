import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component39.SelectedLeafB5_2_7_6

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "da7a949951527c7166b864e88beae0c2d9394f0468a504a87f557fa05dc128e8"
def certificateSHA256 : String := "c37b13a85b85203d42c0b79201081081c72a19db28fc4ab80307a0fb0ea561d9"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 33 → Fin 673 := ![
  22,
  29,
  31,
  190,
  191,
  193,
  196,
  300,
  318,
  350,
  424,
  425,
  427,
  433,
  439,
  440,
  451,
  463,
  471,
  482,
  566,
  570,
  625,
  645,
  650,
  660,
  661,
  663,
  665,
  666,
  669,
  671,
  672
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 33 → SparsePoly (Fin 69) := ![
  [{ coefficient := 1, powers := [(16, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (45, 1)] }, { coefficient := -1, powers := [(27, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (54, 1)] }, { coefficient := 1, powers := [(28, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (53, 1)] }, { coefficient := 1, powers := [(28, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (54, 1)] }, { coefficient := 1, powers := [(28, 1), (44, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1)] }, { coefficient := 1, powers := [(18, 1), (42, 1)] }, { coefficient := 1, powers := [(23, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (53, 1)] }, { coefficient := 1, powers := [(28, 1), (39, 1)] }, { coefficient := 1, powers := [(28, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (28, 1), (59, 1)] }, { coefficient := 1, powers := [(21, 1), (53, 1)] }, { coefficient := 1, powers := [(28, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (53, 1)] }, { coefficient := 1, powers := [(8, 1), (21, 1), (59, 1)] }, { coefficient := 1, powers := [(16, 1), (21, 1), (53, 1)] }, { coefficient := 1, powers := [(16, 1), (28, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1)] }, { coefficient := 1, powers := [(12, 1), (28, 1)] }, { coefficient := 1, powers := [(16, 1), (21, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (34, 1)] }, { coefficient := 1, powers := [(21, 1), (42, 1)] }, { coefficient := 1, powers := [(26, 1), (42, 1)] }, { coefficient := 1, powers := [(34, 1), (35, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (59, 1)] }, { coefficient := 1, powers := [(16, 1), (24, 1), (39, 1)] }, { coefficient := 1, powers := [(16, 1), (24, 1), (44, 1)] }, { coefficient := 1, powers := [(16, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (39, 1)] }, { coefficient := 1, powers := [(16, 1), (44, 1)] }, { coefficient := 1, powers := [(16, 1), (51, 1)] }, { coefficient := 1, powers := [(16, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (54, 1)] }, { coefficient := 1, powers := [(28, 1), (40, 1)] }, { coefficient := 1, powers := [(28, 1), (46, 1), (49, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1), (52, 1)] }, { coefficient := 1, powers := [(3, 1), (60, 1)] }, { coefficient := 1, powers := [(18, 1), (42, 1), (52, 1)] }, { coefficient := 1, powers := [(42, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1), (54, 1)] }, { coefficient := 1, powers := [(24, 1), (45, 1), (49, 1)] }, { coefficient := 1, powers := [(42, 1), (54, 1)] }, { coefficient := 1, powers := [(49, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1), (53, 1)] }, { coefficient := 1, powers := [(19, 1), (42, 1), (53, 1)] }, { coefficient := 1, powers := [(19, 1), (57, 1)] }, { coefficient := 1, powers := [(24, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (35, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1)] }, { coefficient := 1, powers := [(16, 1), (21, 1)] }, { coefficient := 1, powers := [(16, 1), (26, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (42, 1), (53, 1)] }, { coefficient := 1, powers := [(22, 1), (57, 1)] }, { coefficient := 1, powers := [(28, 1), (47, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (42, 1), (53, 1)] }, { coefficient := 1, powers := [(27, 1), (57, 1)] }, { coefficient := 1, powers := [(28, 1), (39, 1), (42, 1)] }, { coefficient := 1, powers := [(28, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (28, 1), (60, 1)] }, { coefficient := 1, powers := [(3, 1), (31, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (34, 1), (54, 1)] }, { coefficient := 1, powers := [(21, 1), (42, 1), (54, 1)] }, { coefficient := 1, powers := [(21, 1), (49, 1), (57, 1)] }, { coefficient := 1, powers := [(28, 1), (42, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (37, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (47, 1), (54, 1)] }, { coefficient := 1, powers := [(19, 1), (42, 1), (54, 1)] }, { coefficient := 1, powers := [(19, 1), (49, 1), (57, 1)] }, { coefficient := 1, powers := [(24, 1), (40, 1), (42, 1)] }, { coefficient := 1, powers := [(24, 1), (47, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (39, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (45, 1), (53, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (39, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1), (57, 1)] }, { coefficient := 1, powers := [(16, 1), (28, 1), (45, 1)] }, { coefficient := 1, powers := [(17, 1), (27, 1), (53, 1)] }, { coefficient := 1, powers := [(17, 1), (28, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (37, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (47, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (28, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (22, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1), (47, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (40, 1)] }, { coefficient := 1, powers := [(12, 1), (22, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1), (28, 1), (47, 1)] }, { coefficient := 1, powers := [(12, 1), (34, 1), (37, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (54, 1)] }, { coefficient := 1, powers := [(17, 1), (28, 1), (40, 1)] }, { coefficient := 1, powers := [(17, 1), (31, 1), (37, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (61, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(39, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(40, 1)] }],
  [{ coefficient := 1, powers := [(57, 1), (66, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(25, 1), (68, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(28, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 33 → SparsePoly (Fin 69) := ![
  [{ coefficient := -1, powers := [(2, 1), (21, 1), (57, 1), (62, 2), (66, 1), (68, 1)] }, { coefficient := -1, powers := [(2, 1), (26, 1), (57, 1), (62, 2), (66, 1), (68, 1)] }, { coefficient := -1, powers := [(3, 1), (21, 1), (24, 1), (45, 1), (51, 1), (59, 1), (62, 1), (63, 1), (66, 1), (68, 1)] }, { coefficient := -1, powers := [(3, 1), (21, 1), (24, 1), (45, 1), (56, 1), (59, 1), (62, 1), (63, 1), (66, 1), (68, 1)] }, { coefficient := 1, powers := [(3, 1), (21, 1), (45, 1), (53, 1), (59, 1), (62, 1), (63, 1), (66, 1), (68, 1)] }, { coefficient := -1, powers := [(21, 1), (24, 1), (35, 1), (45, 1), (51, 1), (59, 1), (62, 1), (63, 1), (66, 1), (68, 1)] }, { coefficient := -1, powers := [(21, 1), (24, 1), (35, 1), (45, 1), (56, 1), (59, 1), (62, 1), (63, 1), (66, 1), (68, 1)] }, { coefficient := 1, powers := [(21, 1), (35, 1), (45, 1), (53, 1), (59, 1), (62, 1), (63, 1), (66, 1), (68, 1)] }],
  [{ coefficient := 1, powers := [(2, 2), (3, 1), (19, 1), (49, 1), (53, 1), (57, 1), (59, 1), (61, 1), (62, 1), (66, 1), (68, 1)] }, { coefficient := -1, powers := [(2, 2), (3, 1), (19, 1), (54, 1), (57, 1), (59, 1), (61, 1), (62, 1), (66, 1), (68, 1)] }, { coefficient := 1, powers := [(2, 1), (5, 1), (21, 1), (54, 1), (57, 1), (59, 1), (62, 1), (66, 1), (68, 1)] }, { coefficient := 1, powers := [(2, 1), (5, 1), (24, 1), (27, 1), (49, 1), (57, 1), (59, 1), (62, 1), (66, 1), (68, 1)] }, { coefficient := 1, powers := [(2, 1), (8, 1), (22, 1), (23, 1), (52, 1), (57, 1), (59, 1), (62, 1), (66, 1), (68, 1)] }, { coefficient := -1, powers := [(2, 1), (8, 1), (22, 1), (49, 1), (57, 1), (59, 1), (62, 1), (66, 1), (68, 1)] }, { coefficient := -1, powers := [(8, 1), (21, 1), (59, 1), (62, 1), (66, 1), (68, 1)] }, { coefficient := -1, powers := [(8, 1), (26, 1), (59, 1), (62, 1), (66, 1), (68, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (2, 2), (3, 1), (49, 1), (53, 1), (57, 1), (59, 1), (61, 1), (62, 1), (66, 1), (68, 1)] }, { coefficient := -1, powers := [(0, 1), (2, 2), (3, 1), (54, 1), (57, 1), (59, 1), (61, 1), (62, 1), (66, 1), (68, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (2, 1), (5, 1), (54, 1), (57, 1), (59, 1), (62, 1), (66, 1)] }, { coefficient := 1, powers := [(2, 1), (5, 1), (24, 1), (49, 1), (57, 1), (59, 1), (62, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (3, 1), (16, 1), (47, 1), (57, 1), (59, 1), (62, 1), (66, 1)] }, { coefficient := -1, powers := [(2, 1), (5, 1), (42, 1), (57, 1), (59, 1), (62, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (3, 1), (12, 1), (42, 1), (57, 1), (59, 1), (62, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (2, 1), (5, 1), (42, 1), (57, 1), (59, 1), (62, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (8, 1), (22, 1), (52, 1), (57, 1), (59, 1), (62, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (16, 1), (42, 1), (59, 1), (62, 1), (63, 1), (66, 1)] }, { coefficient := 1, powers := [(3, 1), (17, 1), (59, 1), (62, 1), (63, 1), (66, 1)] }, { coefficient := -1, powers := [(16, 1), (35, 1), (42, 1), (59, 1), (62, 1), (63, 1), (66, 1)] }, { coefficient := 1, powers := [(17, 1), (35, 1), (59, 1), (62, 1), (63, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (16, 1), (45, 1), (59, 1), (62, 1), (63, 1), (66, 1)] }, { coefficient := -1, powers := [(16, 1), (35, 1), (45, 1), (59, 1), (62, 1), (63, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (45, 1), (59, 1), (62, 1), (63, 1), (66, 1)] }, { coefficient := 1, powers := [(35, 1), (45, 1), (59, 1), (62, 1), (63, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (3, 1), (47, 1), (57, 1), (59, 1), (62, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (59, 1), (62, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (21, 1), (45, 1), (59, 1), (62, 1), (63, 1), (66, 1)] }, { coefficient := -1, powers := [(21, 1), (35, 1), (45, 1), (59, 1), (62, 1), (63, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (21, 1), (24, 1), (45, 1), (59, 1), (62, 1), (63, 1), (66, 1)] }, { coefficient := 1, powers := [(21, 1), (24, 1), (35, 1), (45, 1), (59, 1), (62, 1), (63, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (3, 1), (17, 1), (57, 1), (59, 1), (62, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (8, 1), (22, 1), (57, 1), (59, 1), (62, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (5, 1), (21, 1), (57, 1), (59, 1), (62, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(2, 2), (3, 1), (49, 1), (57, 1), (59, 1), (61, 1), (62, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (57, 1), (62, 2), (66, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (3, 1), (12, 1), (57, 1), (59, 1), (62, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (16, 1), (59, 1), (62, 1), (63, 1), (66, 1)] }, { coefficient := 1, powers := [(16, 1), (35, 1), (59, 1), (62, 1), (63, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (5, 1), (57, 1), (59, 1), (62, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(2, 2), (3, 1), (57, 1), (59, 1), (61, 1), (62, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (59, 1), (62, 1), (63, 1), (66, 1)] }, { coefficient := -1, powers := [(35, 1), (59, 1), (62, 1), (63, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (3, 1), (57, 1), (59, 1), (62, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(2, 2), (3, 1), (37, 1), (57, 1), (59, 1), (60, 1), (62, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (35, 1), (57, 1), (59, 1), (62, 1), (66, 1)] }, { coefficient := -1, powers := [(2, 1), (57, 1), (62, 1), (66, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (3, 1), (57, 1), (59, 1), (62, 1), (66, 1)] }, { coefficient := 1, powers := [(2, 1), (35, 1), (57, 1), (59, 1), (62, 1), (66, 1)] }, { coefficient := 1, powers := [(3, 1), (8, 1), (34, 1), (59, 1), (62, 1), (66, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (35, 1), (59, 1), (62, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (2, 2), (3, 1), (57, 2), (59, 1), (61, 1), (62, 1), (66, 1)] }, { coefficient := -1, powers := [(2, 2), (3, 1), (24, 1), (42, 1), (57, 1), (59, 1), (61, 1), (62, 1), (66, 1)] }, { coefficient := 1, powers := [(2, 2), (3, 1), (57, 2), (59, 1), (62, 1), (66, 1)] }, { coefficient := 1, powers := [(2, 1), (3, 1), (8, 1), (34, 1), (57, 1), (59, 1), (62, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (2, 2), (3, 1), (47, 1), (49, 1), (53, 1), (57, 1), (59, 1), (61, 1), (62, 1), (66, 1)] }, { coefficient := 1, powers := [(0, 1), (2, 2), (3, 1), (47, 1), (54, 1), (57, 1), (59, 1), (61, 1), (62, 1), (66, 1)] }, { coefficient := -1, powers := [(2, 2), (3, 1), (19, 1), (42, 1), (49, 1), (53, 1), (57, 1), (59, 1), (61, 1), (62, 1), (66, 1)] }, { coefficient := 1, powers := [(2, 2), (3, 1), (19, 1), (42, 1), (54, 1), (57, 1), (59, 1), (61, 1), (62, 1), (66, 1)] }, { coefficient := -1, powers := [(2, 1), (5, 1), (21, 1), (42, 1), (54, 1), (57, 1), (59, 1), (62, 1), (66, 1)] }, { coefficient := -1, powers := [(2, 1), (5, 1), (24, 1), (27, 1), (42, 1), (49, 1), (57, 1), (59, 1), (62, 1), (66, 1)] }, { coefficient := -1, powers := [(2, 1), (8, 1), (22, 1), (23, 1), (42, 1), (52, 1), (57, 1), (59, 1), (62, 1), (66, 1)] }, { coefficient := 1, powers := [(2, 1), (8, 1), (22, 1), (42, 1), (49, 1), (57, 1), (59, 1), (62, 1), (66, 1)] }, { coefficient := 1, powers := [(2, 1), (16, 1), (21, 1), (57, 1), (62, 2), (66, 1)] }, { coefficient := 1, powers := [(2, 1), (16, 1), (26, 1), (57, 1), (62, 2), (66, 1)] }, { coefficient := 1, powers := [(3, 1), (16, 1), (21, 1), (24, 1), (45, 1), (51, 1), (59, 1), (62, 1), (63, 1), (66, 1)] }, { coefficient := 1, powers := [(3, 1), (16, 1), (21, 1), (24, 1), (45, 1), (56, 1), (59, 1), (62, 1), (63, 1), (66, 1)] }, { coefficient := -1, powers := [(3, 1), (16, 1), (21, 1), (45, 1), (53, 1), (59, 1), (62, 1), (63, 1), (66, 1)] }, { coefficient := 1, powers := [(8, 1), (21, 1), (42, 1), (59, 1), (62, 1), (66, 1)] }, { coefficient := 1, powers := [(8, 1), (26, 1), (42, 1), (59, 1), (62, 1), (66, 1)] }, { coefficient := 1, powers := [(16, 1), (21, 1), (24, 1), (35, 1), (45, 1), (51, 1), (59, 1), (62, 1), (63, 1), (66, 1)] }, { coefficient := 1, powers := [(16, 1), (21, 1), (24, 1), (35, 1), (45, 1), (56, 1), (59, 1), (62, 1), (63, 1), (66, 1)] }, { coefficient := -1, powers := [(16, 1), (21, 1), (35, 1), (45, 1), (53, 1), (59, 1), (62, 1), (63, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (2, 1), (5, 1), (42, 1), (44, 1), (49, 1), (57, 1), (59, 1), (62, 1), (66, 1)] }, { coefficient := 1, powers := [(2, 1), (3, 1), (12, 1), (42, 1), (46, 1), (57, 1), (59, 1), (62, 1), (66, 1)] }, { coefficient := -1, powers := [(2, 1), (3, 1), (12, 1), (47, 1), (57, 1), (59, 1), (62, 1), (66, 1)] }, { coefficient := 1, powers := [(2, 1), (3, 1), (16, 1), (47, 1), (49, 1), (57, 1), (59, 1), (62, 1), (66, 1)] }, { coefficient := -1, powers := [(2, 1), (3, 1), (17, 1), (46, 1), (49, 1), (57, 1), (59, 1), (62, 1), (66, 1)] }, { coefficient := 1, powers := [(3, 2), (16, 1), (45, 1), (59, 2), (62, 1), (63, 1), (66, 1)] }, { coefficient := 1, powers := [(3, 1), (16, 1), (35, 1), (45, 1), (59, 2), (62, 1), (63, 1), (66, 1)] }, { coefficient := 1, powers := [(3, 1), (16, 1), (42, 1), (44, 1), (59, 1), (62, 1), (63, 1), (66, 1)] }, { coefficient := -1, powers := [(3, 1), (17, 1), (44, 1), (59, 1), (62, 1), (63, 1), (66, 1)] }, { coefficient := 1, powers := [(16, 1), (35, 1), (42, 1), (44, 1), (59, 1), (62, 1), (63, 1), (66, 1)] }, { coefficient := -1, powers := [(17, 1), (35, 1), (44, 1), (59, 1), (62, 1), (63, 1), (66, 1)] }]
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
    ¬ ∀ index : Fin 33,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component39.SelectedLeafB5_2_7_6.selectedHasNoCommonZero

end Krenn.Component39.SelectedLeafB5_2_7_6
