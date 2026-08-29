import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component39.SelectedLeafB4_6_2_5_1

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "870e9fd610d0c02090e94f9afbcfa04568ab32227a0bdf052d1ddd0d24d767a1"
def certificateSHA256 : String := "456e09573c44e30567e35c9fa6e6951bf256573e46f5b98e398a3a2f24875008"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 50 → Fin 676 := ![
  181,
  187,
  190,
  191,
  192,
  193,
  195,
  219,
  277,
  282,
  300,
  301,
  302,
  303,
  308,
  317,
  318,
  319,
  321,
  323,
  350,
  365,
  413,
  419,
  425,
  430,
  434,
  440,
  450,
  452,
  463,
  470,
  471,
  503,
  532,
  566,
  567,
  580,
  604,
  637,
  660,
  661,
  663,
  664,
  665,
  666,
  668,
  669,
  670,
  674
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 50 → SparsePoly (Fin 68) := ![
  [{ coefficient := 1, powers := [(12, 1), (24, 1)] }, { coefficient := 1, powers := [(16, 1), (18, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (18, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (45, 1)] }, { coefficient := -1, powers := [(27, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (54, 1)] }, { coefficient := 1, powers := [(28, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (42, 1)] }, { coefficient := 1, powers := [(26, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (53, 1)] }, { coefficient := 1, powers := [(28, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(26, 1), (52, 1)] }, { coefficient := -1, powers := [(27, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (26, 1), (45, 1)] }, { coefficient := 1, powers := [(27, 1), (42, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (23, 1), (47, 1)] }, { coefficient := 1, powers := [(17, 1), (19, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (42, 1), (51, 1)] }, { coefficient := 1, powers := [(27, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1)] }, { coefficient := 1, powers := [(18, 1), (42, 1)] }, { coefficient := 1, powers := [(23, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (42, 1)] }, { coefficient := 1, powers := [(23, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (49, 1)] }, { coefficient := 1, powers := [(18, 1), (49, 1)] }, { coefficient := 1, powers := [(23, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (54, 1)] }, { coefficient := 1, powers := [(18, 1), (54, 1)] }, { coefficient := 1, powers := [(24, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (26, 1)] }, { coefficient := 1, powers := [(21, 1), (48, 1)] }, { coefficient := 1, powers := [(26, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (51, 1)] }, { coefficient := 1, powers := [(22, 1), (56, 1)] }, { coefficient := 1, powers := [(27, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (53, 1)] }, { coefficient := 1, powers := [(28, 1), (39, 1)] }, { coefficient := 1, powers := [(28, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1), (51, 1)] }, { coefficient := 1, powers := [(18, 1), (42, 1), (51, 1)] }, { coefficient := 1, powers := [(42, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1), (49, 1)] }, { coefficient := 1, powers := [(23, 1), (44, 1), (49, 1)] }, { coefficient := 1, powers := [(49, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1), (50, 1)] }, { coefficient := 1, powers := [(9, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (42, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (28, 1), (59, 1)] }, { coefficient := 1, powers := [(21, 1), (53, 1)] }, { coefficient := 1, powers := [(28, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (22, 1), (59, 1)] }, { coefficient := 1, powers := [(22, 1)] }, { coefficient := 1, powers := [(26, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (53, 1)] }, { coefficient := 1, powers := [(3, 1), (24, 1), (59, 1)] }, { coefficient := 1, powers := [(18, 1), (53, 1)] }, { coefficient := 1, powers := [(24, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (47, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1)] }, { coefficient := 1, powers := [(16, 1), (26, 1), (47, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1)] }, { coefficient := 1, powers := [(12, 1), (28, 1)] }, { coefficient := 1, powers := [(16, 1), (21, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (60, 1)] }, { coefficient := 1, powers := [(12, 1), (47, 1)] }, { coefficient := 1, powers := [(17, 1), (19, 1), (52, 1)] }, { coefficient := 1, powers := [(17, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (60, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (45, 1)] }, { coefficient := 1, powers := [(12, 1), (57, 1)] }, { coefficient := 1, powers := [(17, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (54, 1)] }, { coefficient := 1, powers := [(28, 1), (40, 1)] }, { coefficient := 1, powers := [(28, 1), (46, 1), (49, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1), (50, 1)] }, { coefficient := 1, powers := [(9, 1), (42, 1)] }, { coefficient := 1, powers := [(18, 1), (42, 1), (50, 1)] }, { coefficient := 1, powers := [(38, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1), (53, 1)] }, { coefficient := 1, powers := [(18, 1), (42, 1), (53, 1)] }, { coefficient := 1, powers := [(18, 1), (57, 1)] }, { coefficient := 1, powers := [(24, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1), (54, 1)] }, { coefficient := 1, powers := [(24, 1), (45, 1), (49, 1)] }, { coefficient := 1, powers := [(42, 1), (54, 1)] }, { coefficient := 1, powers := [(49, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1), (52, 1)] }, { coefficient := 1, powers := [(19, 1), (42, 1), (52, 1)] }, { coefficient := 1, powers := [(40, 1), (42, 1)] }, { coefficient := 1, powers := [(47, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1), (53, 1)] }, { coefficient := 1, powers := [(19, 1), (42, 1), (53, 1)] }, { coefficient := 1, powers := [(19, 1), (57, 1)] }, { coefficient := 1, powers := [(24, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (26, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (21, 1), (59, 1)] }, { coefficient := 1, powers := [(21, 1)] }, { coefficient := 1, powers := [(26, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (27, 1), (59, 1)] }, { coefficient := 1, powers := [(26, 1), (39, 1)] }, { coefficient := 1, powers := [(26, 1), (44, 1)] }, { coefficient := 1, powers := [(27, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (42, 1), (53, 1)] }, { coefficient := 1, powers := [(22, 1), (57, 1)] }, { coefficient := 1, powers := [(28, 1), (47, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (49, 1), (56, 1)] }, { coefficient := 1, powers := [(22, 1), (52, 1)] }, { coefficient := 1, powers := [(27, 1), (40, 1)] }, { coefficient := 1, powers := [(27, 1), (46, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1)] }, { coefficient := 1, powers := [(6, 1), (59, 1)] }, { coefficient := 1, powers := [(23, 1), (39, 1)] }, { coefficient := 1, powers := [(23, 1), (44, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (35, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1)] }, { coefficient := 1, powers := [(3, 1), (23, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (18, 1), (59, 1)] }, { coefficient := 1, powers := [(18, 1)] }, { coefficient := 1, powers := [(23, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (42, 1), (54, 1)] }, { coefficient := 1, powers := [(22, 1), (49, 1), (57, 1)] }, { coefficient := 1, powers := [(28, 1), (40, 1), (42, 1)] }, { coefficient := 1, powers := [(28, 1), (47, 1), (49, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1), (42, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (37, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (47, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (28, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (22, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1), (47, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (40, 1)] }, { coefficient := 1, powers := [(12, 1), (22, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1), (28, 1), (47, 1)] }, { coefficient := 1, powers := [(12, 1), (34, 1), (37, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (54, 1)] }, { coefficient := 1, powers := [(17, 1), (28, 1), (40, 1)] }, { coefficient := 1, powers := [(17, 1), (31, 1), (37, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (61, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(38, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(39, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(40, 1)] }],
  [{ coefficient := 1, powers := [(56, 1), (64, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(57, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (65, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(59, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 50 → SparsePoly (Fin 68) := ![
  [{ coefficient := -1, powers := [(22, 1), (45, 1)] }],
  [{ coefficient := -1, powers := [(22, 1), (42, 1), (54, 1), (61, 1)] }, { coefficient := -1, powers := [(28, 1), (47, 1), (49, 1), (61, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1), (42, 1), (61, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1), (49, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (24, 1), (46, 1), (48, 1), (62, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (46, 1)] }],
  [{ coefficient := -1, powers := [(16, 1), (47, 1)] }],
  [{ coefficient := -2, powers := [(12, 1), (24, 1), (39, 1), (44, 1), (64, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (39, 1)] }, { coefficient := -2, powers := [(12, 1), (24, 1), (44, 2), (64, 1)] }, { coefficient := -1, powers := [(12, 1), (24, 1), (44, 1)] }, { coefficient := -1, powers := [(16, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(17, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (46, 1), (53, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (24, 1), (46, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(28, 1), (52, 1)] }],
  [{ coefficient := -2, powers := [(12, 1), (24, 1), (44, 1), (64, 1)] }, { coefficient := -1, powers := [(12, 1), (24, 1)] }],
  [{ coefficient := 2, powers := [(12, 1), (19, 1), (28, 1), (44, 1), (50, 1), (62, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1), (54, 1), (61, 1)] }, { coefficient := -1, powers := [(16, 1), (31, 1), (37, 1), (61, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (12, 1), (28, 1), (44, 1), (50, 1), (62, 1)] }, { coefficient := 2, powers := [(9, 1), (12, 1), (28, 1), (44, 1), (62, 1)] }, { coefficient := -2, powers := [(12, 1), (27, 1), (53, 1)] }, { coefficient := 1, powers := [(16, 1), (28, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (28, 1), (47, 1), (61, 1)] }, { coefficient := -1, powers := [(16, 1), (34, 1), (37, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (22, 1), (45, 1)] }, { coefficient := 2, powers := [(17, 1), (22, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (24, 1), (45, 1), (46, 1), (62, 1)] }],
  [{ coefficient := 2, powers := [(12, 1), (24, 1), (42, 1), (44, 1), (64, 1)] }],
  [{ coefficient := 2, powers := [(12, 1), (23, 1), (47, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (22, 1), (53, 1)] }],
  [{ coefficient := 2, powers := [(17, 1), (22, 1), (53, 1), (63, 1), (65, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (12, 1), (28, 1), (44, 1), (62, 1)] }, { coefficient := -2, powers := [(12, 1), (23, 1), (28, 1), (44, 1), (62, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (12, 1), (44, 1), (47, 1)] }, { coefficient := 2, powers := [(12, 1), (19, 1), (42, 1), (44, 1)] }],
  [{ coefficient := 2, powers := [(12, 1), (24, 1), (39, 1), (42, 1), (44, 1), (64, 1)] }, { coefficient := -1, powers := [(12, 1), (24, 1), (39, 1), (42, 1)] }, { coefficient := 2, powers := [(12, 1), (24, 1), (42, 1), (44, 2), (64, 1)] }, { coefficient := -1, powers := [(12, 1), (24, 1), (42, 1), (44, 1)] }, { coefficient := -1, powers := [(17, 1), (52, 1), (53, 1), (64, 1)] }],
  [{ coefficient := -2, powers := [(17, 1), (22, 1), (49, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(54, 1)] }],
  [{ coefficient := 1, powers := [(47, 1)] }],
  [{ coefficient := 1, powers := [(28, 1)] }],
  [{ coefficient := 1, powers := [(22, 1)] }],
  [{ coefficient := 1, powers := [(17, 1)] }],
  [{ coefficient := -2, powers := [(12, 1), (19, 1), (28, 1), (44, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (22, 1), (51, 1)] }],
  [{ coefficient := -1, powers := [(16, 1), (22, 1)] }],
  [{ coefficient := -1, powers := [(16, 1), (28, 1)] }],
  [{ coefficient := -2, powers := [(12, 1), (21, 1), (44, 1)] }, { coefficient := 2, powers := [(12, 1), (27, 1)] }],
  [{ coefficient := 2, powers := [(12, 1), (24, 1), (44, 1), (47, 1)] }, { coefficient := -1, powers := [(12, 1), (24, 1), (45, 1), (46, 1)] }],
  [{ coefficient := -2, powers := [(12, 1), (24, 1), (42, 1), (44, 1), (46, 1), (64, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (42, 1), (46, 1)] }, { coefficient := 2, powers := [(12, 1), (24, 1), (44, 1), (47, 1), (64, 1)] }, { coefficient := -1, powers := [(12, 1), (24, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(12, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (53, 1), (64, 1)] }],
  [{ coefficient := -2, powers := [(12, 1), (28, 1), (47, 1)] }, { coefficient := -2, powers := [(17, 1), (22, 1), (49, 1), (53, 1), (63, 1), (65, 1)] }],
  [{ coefficient := 2, powers := [(17, 1), (22, 1), (49, 1), (53, 1), (65, 1)] }, { coefficient := -2, powers := [(17, 1), (22, 1), (54, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(16, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(16, 1), (22, 1), (42, 1), (54, 1)] }, { coefficient := -1, powers := [(16, 1), (28, 1), (47, 1), (49, 1)] }, { coefficient := 1, powers := [(16, 1), (31, 1), (37, 1), (42, 1)] }, { coefficient := 1, powers := [(16, 1), (34, 1), (37, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(37, 1), (60, 1)] }, { coefficient := 1, powers := [(40, 1), (57, 1)] }, { coefficient := -1, powers := [(47, 1), (54, 1)] }],
  [{ coefficient := 2, powers := [(12, 1), (19, 1), (28, 1), (42, 1), (44, 1)] }, { coefficient := -1, powers := [(12, 1), (24, 1), (26, 1), (45, 1), (46, 1)] }],
  [{ coefficient := 2, powers := [(17, 1), (22, 1), (23, 1), (49, 1), (53, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (34, 1)] }, { coefficient := -1, powers := [(17, 1), (27, 1), (53, 1), (64, 1)] }, { coefficient := -1, powers := [(17, 1), (28, 1)] }],
  [{ coefficient := -2, powers := [(12, 1), (22, 1), (24, 1), (42, 1), (44, 1)] }, { coefficient := -1, powers := [(17, 1), (22, 1), (49, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (31, 1)] }, { coefficient := -1, powers := [(12, 1), (18, 1), (22, 1), (51, 1)] }, { coefficient := 2, powers := [(12, 1), (19, 1), (21, 1), (44, 1)] }, { coefficient := -2, powers := [(12, 1), (19, 1), (27, 1)] }, { coefficient := -1, powers := [(12, 1), (22, 1)] }],
  [{ coefficient := 2, powers := [(17, 1), (22, 1), (54, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (3, 1), (12, 1), (28, 1), (44, 1), (47, 1)] }, { coefficient := -2, powers := [(0, 1), (17, 1), (22, 1), (35, 1), (49, 1), (53, 1), (65, 1)] }, { coefficient := 2, powers := [(0, 1), (17, 1), (22, 1), (35, 1), (54, 1), (65, 1)] }, { coefficient := -2, powers := [(3, 1), (12, 1), (19, 1), (28, 1), (42, 1), (44, 1)] }, { coefficient := -2, powers := [(3, 1), (12, 1), (24, 1), (26, 1), (44, 1), (47, 1)] }, { coefficient := 1, powers := [(3, 1), (12, 1), (24, 1), (26, 1), (45, 1), (46, 1)] }, { coefficient := -2, powers := [(3, 1), (17, 1), (22, 1), (23, 1), (49, 1), (53, 1), (65, 1)] }, { coefficient := 2, powers := [(3, 1), (17, 1), (22, 1), (23, 1), (54, 1), (65, 1)] }, { coefficient := 2, powers := [(3, 1), (17, 1), (22, 1), (24, 1), (49, 1), (65, 1)] }, { coefficient := -2, powers := [(6, 1), (12, 1), (21, 1), (24, 1), (44, 1), (47, 1)] }, { coefficient := 1, powers := [(6, 1), (12, 1), (21, 1), (24, 1), (45, 1), (46, 1)] }, { coefficient := -2, powers := [(6, 1), (12, 1), (22, 1), (24, 1), (39, 1), (42, 1), (44, 1), (64, 1)] }, { coefficient := 1, powers := [(6, 1), (12, 1), (22, 1), (24, 1), (39, 1), (42, 1)] }, { coefficient := -2, powers := [(6, 1), (12, 1), (22, 1), (24, 1), (42, 1), (44, 2), (64, 1)] }, { coefficient := 1, powers := [(6, 1), (12, 1), (22, 1), (24, 1), (42, 1), (44, 1)] }, { coefficient := 2, powers := [(6, 1), (12, 1), (24, 1), (27, 1), (42, 1), (44, 1), (46, 1), (64, 1)] }, { coefficient := -1, powers := [(6, 1), (12, 1), (24, 1), (27, 1), (42, 1), (46, 1)] }, { coefficient := -2, powers := [(6, 1), (12, 1), (24, 1), (27, 1), (44, 1), (47, 1), (64, 1)] }, { coefficient := 1, powers := [(6, 1), (12, 1), (24, 1), (27, 1), (47, 1)] }, { coefficient := 2, powers := [(6, 1), (12, 1), (28, 1), (47, 1)] }, { coefficient := -2, powers := [(6, 1), (17, 1), (18, 1), (22, 1), (49, 1), (53, 1), (65, 1)] }, { coefficient := 2, powers := [(6, 1), (17, 1), (18, 1), (22, 1), (54, 1), (65, 1)] }, { coefficient := 2, powers := [(6, 1), (17, 1), (22, 1), (49, 1), (53, 1), (63, 1), (65, 1)] }, { coefficient := 1, powers := [(6, 1), (17, 1), (22, 1), (52, 1), (53, 1), (64, 1)] }]
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
    ¬ ∀ index : Fin 50,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component39.SelectedLeafB4_6_2_5_1.selectedHasNoCommonZero

end Krenn.Component39.SelectedLeafB4_6_2_5_1
