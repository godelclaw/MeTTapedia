import KrennSparseCertificate

/-! Selected core of a strict exact certificate over a frozen system. -/

namespace Krenn.X5Case8Tree.LeafB4_4

open Krenn.SparseCertificate
open MvPolynomial

def sourceSystemFileSHA256 : String := "f8607d460211c0ff86839d220b5cc3e303a47f27d5afeb6214aeca0844db7d49"
def sourceSystemSemanticSHA256 : String := "aa981a291816464a410e49b1411ff734761d887b4e065cfa62c7ecb282905dc0"
def certificateSHA256 : String := "fe13611f23cac0adfbc20af033b92be6680b415d96c09d6686bc90a35bbd88cb"
def sourceEquationCount : Nat := 681

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedIndices : Fin 42 → Fin 681 := ![
  1,
  7,
  10,
  13,
  16,
  30,
  46,
  48,
  51,
  53,
  310,
  399,
  402,
  411,
  414,
  416,
  417,
  420,
  423,
  424,
  426,
  534,
  570,
  572,
  573,
  583,
  592,
  619,
  622,
  635,
  660,
  661,
  663,
  666,
  671,
  673,
  674,
  676,
  677,
  678,
  679,
  680
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 42 → SparsePoly (Fin 72) := ![
  [{ coefficient := 1, powers := [(53, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(39, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(48, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(49, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(49, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(51, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(47, 1), (55, 1)] }, { coefficient := 1, powers := [(55, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (48, 1), (55, 1)] }, { coefficient := 1, powers := [(55, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (50, 1), (55, 1)] }, { coefficient := 1, powers := [(33, 1), (40, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(32, 1), (36, 1), (63, 1)] }, { coefficient := 1, powers := [(63, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (63, 1)] }, { coefficient := 1, powers := [(17, 1), (57, 1)] }, { coefficient := 1, powers := [(54, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (62, 1)] }, { coefficient := 1, powers := [(19, 1), (56, 1)] }, { coefficient := 1, powers := [(27, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (63, 1)] }, { coefficient := 1, powers := [(20, 1), (57, 1)] }, { coefficient := 1, powers := [(28, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(15, 1), (63, 1)] }, { coefficient := 1, powers := [(23, 1), (57, 1)] }, { coefficient := 1, powers := [(31, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(36, 1), (65, 1)] }, { coefficient := 1, powers := [(39, 1), (59, 1)] }, { coefficient := 1, powers := [(47, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(37, 1), (69, 1)] }, { coefficient := 1, powers := [(43, 1), (60, 1)] }, { coefficient := 1, powers := [(51, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(40, 1), (69, 1)] }, { coefficient := 1, powers := [(43, 1), (66, 1)] }, { coefficient := 1, powers := [(51, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (36, 1), (69, 1)] }, { coefficient := 1, powers := [(36, 1), (66, 1)] }, { coefficient := 1, powers := [(48, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (62, 1)] }, { coefficient := 1, powers := [(25, 1), (39, 1), (58, 1)] }, { coefficient := 1, powers := [(42, 1), (58, 1)] }, { coefficient := 1, powers := [(58, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (53, 1)] }, { coefficient := 1, powers := [(36, 1), (67, 1)] }, { coefficient := 1, powers := [(39, 1), (67, 1)] }, { coefficient := 1, powers := [(53, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(36, 1), (69, 1)] }, { coefficient := 1, powers := [(39, 1), (69, 1)] }, { coefficient := 1, powers := [(48, 1), (53, 1)] }, { coefficient := 1, powers := [(53, 1), (69, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (57, 1), (65, 1)] }, { coefficient := 1, powers := [(9, 1), (43, 1), (65, 1)] }, { coefficient := 1, powers := [(37, 1), (65, 1)] }, { coefficient := 1, powers := [(50, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (53, 1), (67, 1)] }, { coefficient := 1, powers := [(11, 1), (39, 1), (67, 1)] }, { coefficient := 1, powers := [(19, 1), (36, 1), (67, 1)] }, { coefficient := 1, powers := [(26, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (57, 1), (65, 1)] }, { coefficient := 1, powers := [(15, 1), (43, 1), (65, 1)] }, { coefficient := 1, powers := [(22, 1), (50, 1), (57, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (39, 1), (67, 1)] }, { coefficient := 1, powers := [(24, 1), (39, 1), (58, 1)] }, { coefficient := 1, powers := [(32, 1), (39, 1), (55, 1)] }, { coefficient := 1, powers := [(55, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (48, 1), (63, 1)] }, { coefficient := 1, powers := [(23, 1), (36, 1), (69, 1)] }, { coefficient := 1, powers := [(31, 1), (36, 1), (66, 1)] }, { coefficient := 1, powers := [(34, 1), (36, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (48, 1), (63, 1)] }, { coefficient := 1, powers := [(17, 1), (48, 1), (57, 1)] }, { coefficient := 1, powers := [(48, 1), (54, 1)] }, { coefficient := 1, powers := [(54, 1), (69, 1)] }, { coefficient := 1, powers := [(57, 1), (66, 1)] }, { coefficient := 1, powers := [(60, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (49, 1), (63, 1)] }, { coefficient := 1, powers := [(17, 1), (49, 1), (57, 1)] }, { coefficient := 1, powers := [(32, 1), (37, 1), (63, 1)] }, { coefficient := 1, powers := [(32, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(32, 1), (43, 1), (54, 1)] }, { coefficient := 1, powers := [(49, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (50, 1), (63, 1)] }, { coefficient := 1, powers := [(20, 1), (50, 1), (57, 1)] }, { coefficient := 1, powers := [(28, 1), (50, 1), (54, 1)] }, { coefficient := 1, powers := [(33, 1), (37, 1), (63, 1)] }, { coefficient := 1, powers := [(33, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(33, 1), (43, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (54, 1), (69, 1)] }, { coefficient := 1, powers := [(1, 1), (57, 1), (66, 1)] }, { coefficient := 1, powers := [(1, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(9, 1), (40, 1), (69, 1)] }, { coefficient := 1, powers := [(9, 1), (43, 1), (66, 1)] }, { coefficient := 1, powers := [(9, 1), (51, 1), (63, 1)] }, { coefficient := 1, powers := [(17, 1), (37, 1), (69, 1)] }, { coefficient := 1, powers := [(17, 1), (43, 1), (60, 1)] }, { coefficient := 1, powers := [(17, 1), (51, 1), (57, 1)] }, { coefficient := 1, powers := [(37, 1), (66, 1)] }, { coefficient := 1, powers := [(40, 1), (60, 1)] }, { coefficient := 1, powers := [(51, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (36, 1), (65, 1)] }, { coefficient := 1, powers := [(25, 1), (39, 1), (59, 1)] }, { coefficient := 1, powers := [(25, 1), (47, 1), (53, 1)] }, { coefficient := 1, powers := [(36, 1), (68, 1)] }, { coefficient := 1, powers := [(39, 1), (68, 1)] }, { coefficient := 1, powers := [(42, 1), (59, 1)] }, { coefficient := 1, powers := [(42, 1), (65, 1)] }, { coefficient := 1, powers := [(47, 1), (56, 1)] }, { coefficient := 1, powers := [(47, 1), (62, 1)] }, { coefficient := 1, powers := [(53, 1), (68, 1)] }, { coefficient := 1, powers := [(56, 1), (65, 1)] }, { coefficient := 1, powers := [(59, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (53, 1), (68, 1)] }, { coefficient := 1, powers := [(3, 1), (56, 1), (65, 1)] }, { coefficient := 1, powers := [(3, 1), (59, 1), (62, 1)] }, { coefficient := 1, powers := [(11, 1), (39, 1), (68, 1)] }, { coefficient := 1, powers := [(11, 1), (42, 1), (65, 1)] }, { coefficient := 1, powers := [(11, 1), (47, 1), (62, 1)] }, { coefficient := 1, powers := [(19, 1), (36, 1), (68, 1)] }, { coefficient := 1, powers := [(19, 1), (42, 1), (59, 1)] }, { coefficient := 1, powers := [(19, 1), (47, 1), (56, 1)] }, { coefficient := 1, powers := [(27, 1), (36, 1), (65, 1)] }, { coefficient := 1, powers := [(27, 1), (39, 1), (59, 1)] }, { coefficient := 1, powers := [(27, 1), (47, 1), (53, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1), (62, 1)] }, { coefficient := 1, powers := [(33, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(33, 1), (42, 1), (53, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(7, 1), (54, 1), (69, 1)] }, { coefficient := 1, powers := [(7, 1), (57, 1), (66, 1)] }, { coefficient := 1, powers := [(7, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(15, 1), (40, 1), (69, 1)] }, { coefficient := 1, powers := [(15, 1), (43, 1), (66, 1)] }, { coefficient := 1, powers := [(15, 1), (51, 1), (63, 1)] }, { coefficient := 1, powers := [(23, 1), (37, 1), (69, 1)] }, { coefficient := 1, powers := [(23, 1), (43, 1), (60, 1)] }, { coefficient := 1, powers := [(23, 1), (51, 1), (57, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1), (66, 1)] }, { coefficient := 1, powers := [(31, 1), (40, 1), (60, 1)] }, { coefficient := 1, powers := [(31, 1), (51, 1), (54, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1), (63, 1)] }, { coefficient := 1, powers := [(34, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(34, 1), (43, 1), (54, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(3, 1)] }],
  [{ coefficient := 1, powers := [(7, 1)] }],
  [{ coefficient := 1, powers := [(55, 1), (71, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(56, 1)] }],
  [{ coefficient := 1, powers := [(57, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 42 → SparsePoly (Fin 72) := ![
  [{ coefficient := 1, powers := [(3, 1), (8, 1), (39, 1), (67, 1), (68, 1), (71, 1)] }, { coefficient := 1, powers := [(3, 1), (68, 1)] }, { coefficient := -1, powers := [(8, 1), (19, 1), (24, 1), (39, 1), (68, 1), (71, 1)] }, { coefficient := -1, powers := [(8, 1), (19, 1), (39, 1), (67, 1), (68, 1), (71, 1)] }, { coefficient := 1, powers := [(8, 1), (26, 1), (39, 1), (68, 1), (71, 1)] }, { coefficient := 2, powers := [(11, 1), (17, 1), (31, 1), (32, 1), (37, 1), (42, 1), (48, 1), (65, 1)] }, { coefficient := 2, powers := [(11, 1), (17, 1), (31, 1), (32, 1), (37, 1), (42, 1), (65, 1), (69, 1)] }, { coefficient := -2, powers := [(11, 1), (23, 1), (32, 1), (37, 1), (42, 1), (48, 1), (65, 1)] }, { coefficient := -2, powers := [(11, 1), (23, 1), (32, 1), (37, 1), (42, 1), (65, 1), (69, 1)] }, { coefficient := -2, powers := [(17, 1), (19, 1), (31, 1), (32, 1), (37, 1), (42, 1), (48, 1), (65, 1)] }, { coefficient := -2, powers := [(17, 1), (19, 1), (31, 1), (32, 1), (37, 1), (42, 1), (65, 1), (69, 1)] }, { coefficient := 2, powers := [(17, 1), (19, 1), (31, 1), (32, 1), (37, 1), (48, 1), (62, 1), (65, 1)] }, { coefficient := 2, powers := [(17, 1), (19, 1), (31, 1), (32, 1), (37, 1), (62, 1), (65, 1), (69, 1)] }, { coefficient := 2, powers := [(19, 1), (23, 1), (32, 1), (37, 1), (42, 1), (48, 1), (65, 1)] }, { coefficient := 2, powers := [(19, 1), (23, 1), (32, 1), (37, 1), (42, 1), (65, 1), (69, 1)] }, { coefficient := -2, powers := [(19, 1), (23, 1), (32, 1), (37, 1), (48, 1), (62, 1), (65, 1)] }, { coefficient := -2, powers := [(19, 1), (23, 1), (32, 1), (37, 1), (62, 1), (65, 1), (69, 1)] }, { coefficient := -1, powers := [(19, 1), (68, 1)] }, { coefficient := -1, powers := [(27, 1), (47, 1)] }, { coefficient := 1, powers := [(33, 1), (42, 1)] }],
  [{ coefficient := 2, powers := [(11, 1), (32, 1), (37, 1), (42, 1), (48, 1), (65, 1)] }, { coefficient := -2, powers := [(19, 1), (32, 1), (37, 1), (42, 1), (48, 1), (65, 1)] }, { coefficient := 2, powers := [(19, 1), (32, 1), (37, 1), (48, 1), (62, 1), (65, 1)] }],
  [{ coefficient := 2, powers := [(11, 1), (31, 1), (32, 1), (37, 1), (39, 1), (42, 1), (65, 1), (69, 1), (71, 1)] }, { coefficient := -2, powers := [(19, 1), (31, 1), (32, 1), (37, 1), (39, 1), (42, 1), (65, 1), (69, 1), (71, 1)] }, { coefficient := 2, powers := [(19, 1), (31, 1), (32, 1), (37, 1), (39, 1), (62, 1), (65, 1), (69, 1), (71, 1)] }],
  [{ coefficient := -1, powers := [(15, 1), (36, 1), (50, 1), (62, 1), (69, 1), (71, 1)] }, { coefficient := -1, powers := [(31, 1), (36, 1), (50, 1), (60, 1), (62, 1), (71, 1)] }],
  [{ coefficient := -2, powers := [(11, 1), (32, 1), (37, 1), (39, 1), (42, 1), (65, 1), (69, 1), (71, 1)] }, { coefficient := 2, powers := [(19, 1), (32, 1), (37, 1), (39, 1), (42, 1), (65, 1), (69, 1), (71, 1)] }, { coefficient := -2, powers := [(19, 1), (32, 1), (37, 1), (39, 1), (62, 1), (65, 1), (69, 1), (71, 1)] }],
  [{ coefficient := -1, powers := [(11, 1), (24, 1), (39, 1), (68, 1), (71, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (39, 1), (68, 1), (71, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (59, 1), (62, 1), (71, 1)] }, { coefficient := -1, powers := [(19, 1), (25, 1), (39, 1), (59, 1), (67, 1), (71, 1)] }, { coefficient := -1, powers := [(19, 1), (42, 1), (59, 1), (67, 1), (71, 1)] }, { coefficient := -1, powers := [(19, 1), (59, 1), (62, 1), (67, 1), (71, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (15, 1), (17, 1), (42, 1), (43, 1), (65, 1), (71, 1)] }, { coefficient := 1, powers := [(11, 1), (17, 1), (31, 1), (37, 1), (42, 1), (65, 1), (71, 1)] }, { coefficient := -2, powers := [(11, 1), (31, 1), (32, 1), (37, 1), (42, 1), (63, 1), (65, 1), (71, 1)] }, { coefficient := -1, powers := [(15, 1), (17, 1), (19, 1), (42, 1), (43, 1), (65, 1), (71, 1)] }, { coefficient := 1, powers := [(15, 1), (17, 1), (19, 1), (43, 1), (62, 1), (65, 1), (71, 1)] }, { coefficient := -1, powers := [(15, 1), (17, 1), (33, 1), (36, 1), (43, 1), (62, 1), (71, 1)] }, { coefficient := -1, powers := [(17, 1), (19, 1), (31, 1), (37, 1), (42, 1), (65, 1), (71, 1)] }, { coefficient := 1, powers := [(17, 1), (19, 1), (31, 1), (37, 1), (62, 1), (65, 1), (71, 1)] }, { coefficient := -1, powers := [(17, 1), (31, 1), (33, 1), (36, 1), (37, 1), (62, 1), (71, 1)] }, { coefficient := 2, powers := [(19, 1), (31, 1), (32, 1), (37, 1), (42, 1), (63, 1), (65, 1), (71, 1)] }, { coefficient := -2, powers := [(19, 1), (31, 1), (32, 1), (37, 1), (62, 1), (63, 1), (65, 1), (71, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (34, 1), (39, 2), (54, 1), (68, 1), (71, 1)] }, { coefficient := -1, powers := [(19, 1), (34, 1), (39, 2), (54, 1), (68, 1), (71, 1)] }, { coefficient := -1, powers := [(19, 1), (34, 1), (39, 1), (54, 1), (59, 1), (62, 1), (71, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (11, 1), (34, 1), (39, 2), (68, 1)] }, { coefficient := -1, powers := [(9, 1), (19, 1), (34, 1), (39, 2), (68, 1)] }, { coefficient := -1, powers := [(9, 1), (19, 1), (34, 1), (39, 1), (59, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (15, 1), (32, 1), (39, 2), (63, 1), (68, 1), (71, 1)] }, { coefficient := -1, powers := [(11, 1), (15, 1), (42, 1), (63, 1), (65, 1), (71, 1)] }, { coefficient := 1, powers := [(11, 1), (31, 1), (32, 1), (39, 2), (54, 1), (68, 1), (71, 1)] }, { coefficient := -1, powers := [(11, 1), (31, 1), (42, 1), (54, 1), (65, 1), (71, 1)] }, { coefficient := -1, powers := [(15, 1), (19, 1), (32, 1), (39, 2), (63, 1), (68, 1), (71, 1)] }, { coefficient := -1, powers := [(15, 1), (19, 1), (32, 1), (39, 1), (59, 1), (62, 1), (63, 1), (71, 1)] }, { coefficient := 1, powers := [(15, 1), (19, 1), (42, 1), (63, 1), (65, 1), (71, 1)] }, { coefficient := -1, powers := [(15, 1), (19, 1), (62, 1), (63, 1), (65, 1), (71, 1)] }, { coefficient := -1, powers := [(19, 1), (31, 1), (32, 1), (39, 2), (54, 1), (68, 1), (71, 1)] }, { coefficient := -1, powers := [(19, 1), (31, 1), (32, 1), (39, 1), (54, 1), (59, 1), (62, 1), (71, 1)] }, { coefficient := 1, powers := [(19, 1), (31, 1), (42, 1), (54, 1), (65, 1), (71, 1)] }, { coefficient := -1, powers := [(19, 1), (31, 1), (54, 1), (62, 1), (65, 1), (71, 1)] }],
  [{ coefficient := -1, powers := [(19, 1), (62, 1), (71, 1)] }],
  [{ coefficient := -1, powers := [(11, 1), (15, 1), (42, 1), (43, 1), (65, 1), (71, 1)] }, { coefficient := -1, powers := [(11, 1), (31, 1), (37, 1), (42, 1), (65, 1), (71, 1)] }, { coefficient := 1, powers := [(15, 1), (19, 1), (42, 1), (43, 1), (65, 1), (71, 1)] }, { coefficient := -1, powers := [(15, 1), (19, 1), (43, 1), (62, 1), (65, 1), (71, 1)] }, { coefficient := 1, powers := [(15, 1), (33, 1), (36, 1), (43, 1), (62, 1), (71, 1)] }, { coefficient := 1, powers := [(19, 1), (31, 1), (37, 1), (42, 1), (65, 1), (71, 1)] }, { coefficient := -1, powers := [(19, 1), (31, 1), (37, 1), (62, 1), (65, 1), (71, 1)] }, { coefficient := 1, powers := [(31, 1), (33, 1), (36, 1), (37, 1), (62, 1), (71, 1)] }],
  [{ coefficient := 1, powers := [(15, 1), (36, 1), (62, 1), (69, 1), (71, 1)] }, { coefficient := 1, powers := [(31, 1), (36, 1), (60, 1), (62, 1), (71, 1)] }],
  [{ coefficient := 2, powers := [(11, 1), (34, 1), (37, 1), (42, 1), (65, 1)] }, { coefficient := -2, powers := [(19, 1), (34, 1), (37, 1), (42, 1), (65, 1)] }, { coefficient := 2, powers := [(19, 1), (34, 1), (37, 1), (62, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(1, 1), (11, 1), (31, 1), (32, 1), (39, 2), (48, 1), (68, 1)] }, { coefficient := 1, powers := [(1, 1), (11, 1), (31, 1), (42, 1), (48, 1), (65, 1)] }, { coefficient := 1, powers := [(1, 1), (19, 1), (31, 1), (32, 1), (39, 2), (48, 1), (68, 1)] }, { coefficient := 1, powers := [(1, 1), (19, 1), (31, 1), (32, 1), (39, 1), (48, 1), (59, 1), (62, 1)] }, { coefficient := -1, powers := [(1, 1), (19, 1), (31, 1), (42, 1), (48, 1), (65, 1)] }, { coefficient := 1, powers := [(1, 1), (19, 1), (31, 1), (48, 1), (62, 1), (65, 1)] }, { coefficient := 1, powers := [(11, 1), (34, 1), (42, 1), (43, 1), (65, 1)] }, { coefficient := -1, powers := [(19, 1), (34, 1), (42, 1), (43, 1), (65, 1)] }, { coefficient := 1, powers := [(19, 1), (34, 1), (43, 1), (62, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(47, 1)] }],
  [{ coefficient := -1, powers := [(34, 1), (36, 1), (50, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(11, 1), (32, 1), (39, 2), (51, 1), (68, 1)] }, { coefficient := 1, powers := [(11, 1), (42, 1), (51, 1), (65, 1)] }, { coefficient := 1, powers := [(19, 1), (32, 1), (39, 2), (51, 1), (68, 1)] }, { coefficient := 1, powers := [(19, 1), (32, 1), (39, 1), (51, 1), (59, 1), (62, 1)] }, { coefficient := -1, powers := [(19, 1), (42, 1), (51, 1), (65, 1)] }, { coefficient := 1, powers := [(19, 1), (51, 1), (62, 1), (65, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1), (51, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(19, 1), (25, 1)] }, { coefficient := 1, powers := [(27, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (17, 1), (31, 1), (32, 1), (39, 2), (68, 1)] }, { coefficient := -1, powers := [(11, 1), (17, 1), (31, 1), (42, 1), (65, 1)] }, { coefficient := -1, powers := [(11, 1), (23, 1), (32, 1), (39, 2), (68, 1)] }, { coefficient := 1, powers := [(11, 1), (23, 1), (42, 1), (65, 1)] }, { coefficient := -1, powers := [(17, 1), (19, 1), (31, 1), (32, 1), (39, 2), (68, 1)] }, { coefficient := -1, powers := [(17, 1), (19, 1), (31, 1), (32, 1), (39, 1), (59, 1), (62, 1)] }, { coefficient := 1, powers := [(17, 1), (19, 1), (31, 1), (42, 1), (65, 1)] }, { coefficient := -1, powers := [(17, 1), (19, 1), (31, 1), (62, 1), (65, 1)] }, { coefficient := 1, powers := [(19, 1), (23, 1), (32, 1), (39, 2), (68, 1)] }, { coefficient := 1, powers := [(19, 1), (23, 1), (32, 1), (39, 1), (59, 1), (62, 1)] }, { coefficient := -1, powers := [(19, 1), (23, 1), (42, 1), (65, 1)] }, { coefficient := 1, powers := [(19, 1), (23, 1), (62, 1), (65, 1)] }, { coefficient := 1, powers := [(23, 1), (33, 1), (36, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (11, 1), (31, 1), (32, 1), (39, 2), (68, 1)] }, { coefficient := -1, powers := [(9, 1), (11, 1), (31, 1), (42, 1), (65, 1)] }, { coefficient := -1, powers := [(9, 1), (19, 1), (31, 1), (32, 1), (39, 2), (68, 1)] }, { coefficient := -1, powers := [(9, 1), (19, 1), (31, 1), (32, 1), (39, 1), (59, 1), (62, 1)] }, { coefficient := 1, powers := [(9, 1), (19, 1), (31, 1), (42, 1), (65, 1)] }, { coefficient := -1, powers := [(9, 1), (19, 1), (31, 1), (62, 1), (65, 1)] }, { coefficient := -1, powers := [(11, 1), (15, 1), (32, 1), (39, 2), (68, 1)] }, { coefficient := 1, powers := [(11, 1), (15, 1), (42, 1), (65, 1)] }, { coefficient := 1, powers := [(15, 1), (19, 1), (32, 1), (39, 2), (68, 1)] }, { coefficient := 1, powers := [(15, 1), (19, 1), (32, 1), (39, 1), (59, 1), (62, 1)] }, { coefficient := -1, powers := [(15, 1), (19, 1), (42, 1), (65, 1)] }, { coefficient := 1, powers := [(15, 1), (19, 1), (62, 1), (65, 1)] }],
  [{ coefficient := 2, powers := [(11, 1), (31, 1), (32, 1), (37, 1), (42, 1), (65, 1)] }, { coefficient := -2, powers := [(19, 1), (31, 1), (32, 1), (37, 1), (42, 1), (65, 1)] }, { coefficient := 2, powers := [(19, 1), (31, 1), (32, 1), (37, 1), (62, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (39, 1), (59, 1), (67, 1), (71, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (19, 1), (39, 1), (68, 1), (71, 1)] }],
  [{ coefficient := -2, powers := [(11, 1), (17, 1), (31, 1), (32, 1), (37, 1), (42, 1), (65, 1)] }, { coefficient := 2, powers := [(11, 1), (23, 1), (32, 1), (37, 1), (42, 1), (65, 1)] }, { coefficient := 2, powers := [(17, 1), (19, 1), (31, 1), (32, 1), (37, 1), (42, 1), (65, 1)] }, { coefficient := -2, powers := [(17, 1), (19, 1), (31, 1), (32, 1), (37, 1), (62, 1), (65, 1)] }, { coefficient := -2, powers := [(19, 1), (23, 1), (32, 1), (37, 1), (42, 1), (65, 1)] }, { coefficient := 2, powers := [(19, 1), (23, 1), (32, 1), (37, 1), (62, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(11, 1), (34, 1), (42, 1), (63, 1)] }, { coefficient := 1, powers := [(19, 1), (34, 1), (42, 1), (63, 1)] }, { coefficient := -1, powers := [(19, 1), (34, 1), (62, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (39, 1), (68, 1), (71, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (42, 1), (66, 1)] }, { coefficient := -1, powers := [(19, 1), (42, 1), (66, 1)] }, { coefficient := 1, powers := [(19, 1), (62, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (39, 1), (68, 1), (71, 1)] }, { coefficient := -1, powers := [(19, 1), (39, 1), (68, 1), (71, 1)] }, { coefficient := -1, powers := [(19, 1), (59, 1), (62, 1), (71, 1)] }],
  [{ coefficient := -2, powers := [(11, 1), (32, 1), (37, 1), (42, 1), (65, 1)] }, { coefficient := 2, powers := [(19, 1), (32, 1), (37, 1), (42, 1), (65, 1)] }, { coefficient := -2, powers := [(19, 1), (32, 1), (37, 1), (62, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (11, 1), (31, 1), (32, 1), (39, 2), (68, 1)] }, { coefficient := -1, powers := [(1, 1), (11, 1), (31, 1), (42, 1), (65, 1)] }, { coefficient := -1, powers := [(1, 1), (19, 1), (31, 1), (32, 1), (39, 2), (68, 1)] }, { coefficient := -1, powers := [(1, 1), (19, 1), (31, 1), (32, 1), (39, 1), (59, 1), (62, 1)] }, { coefficient := 1, powers := [(1, 1), (19, 1), (31, 1), (42, 1), (65, 1)] }, { coefficient := -1, powers := [(1, 1), (19, 1), (31, 1), (62, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(11, 1), (34, 1), (39, 2), (68, 1)] }, { coefficient := 1, powers := [(19, 1), (34, 1), (39, 2), (68, 1)] }, { coefficient := 1, powers := [(19, 1), (34, 1), (39, 1), (59, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(34, 1), (36, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(11, 1), (31, 1), (32, 1), (39, 2), (68, 1)] }, { coefficient := 1, powers := [(11, 1), (31, 1), (42, 1), (65, 1)] }, { coefficient := 1, powers := [(19, 1), (31, 1), (32, 1), (39, 2), (68, 1)] }, { coefficient := 1, powers := [(19, 1), (31, 1), (32, 1), (39, 1), (59, 1), (62, 1)] }, { coefficient := -1, powers := [(19, 1), (31, 1), (42, 1), (65, 1)] }, { coefficient := 1, powers := [(19, 1), (31, 1), (62, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(19, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(11, 1), (32, 1), (39, 2), (68, 1)] }, { coefficient := -1, powers := [(11, 1), (42, 1), (65, 1)] }, { coefficient := -1, powers := [(19, 1), (32, 1), (39, 2), (68, 1)] }, { coefficient := -1, powers := [(19, 1), (32, 1), (39, 1), (59, 1), (62, 1)] }, { coefficient := 1, powers := [(19, 1), (42, 1), (65, 1)] }, { coefficient := -1, powers := [(19, 1), (62, 1), (65, 1)] }, { coefficient := -1, powers := [(33, 1), (36, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(59, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(11, 1), (32, 1), (39, 2), (54, 1), (68, 1), (69, 1)] }, { coefficient := -1, powers := [(11, 1), (32, 1), (39, 2), (60, 1), (63, 1), (68, 1)] }, { coefficient := 1, powers := [(11, 1), (42, 1), (54, 1), (65, 1), (69, 1)] }, { coefficient := 1, powers := [(11, 1), (42, 1), (60, 1), (63, 1), (65, 1)] }, { coefficient := 1, powers := [(19, 1), (32, 1), (39, 2), (54, 1), (68, 1), (69, 1)] }, { coefficient := 1, powers := [(19, 1), (32, 1), (39, 2), (60, 1), (63, 1), (68, 1)] }, { coefficient := 1, powers := [(19, 1), (32, 1), (39, 1), (54, 1), (59, 1), (62, 1), (69, 1)] }, { coefficient := 1, powers := [(19, 1), (32, 1), (39, 1), (59, 1), (60, 1), (62, 1), (63, 1)] }, { coefficient := -1, powers := [(19, 1), (42, 1), (54, 1), (65, 1), (69, 1)] }, { coefficient := -1, powers := [(19, 1), (42, 1), (60, 1), (63, 1), (65, 1)] }, { coefficient := 1, powers := [(19, 1), (54, 1), (62, 1), (65, 1), (69, 1)] }, { coefficient := 1, powers := [(19, 1), (60, 1), (62, 1), (63, 1), (65, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1), (54, 1), (62, 1), (69, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1), (60, 1), (62, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(11, 1), (15, 1), (32, 1), (39, 2), (51, 1), (63, 1), (68, 1)] }, { coefficient := 1, powers := [(11, 1), (15, 1), (42, 1), (43, 1), (65, 1), (66, 1)] }, { coefficient := 1, powers := [(11, 1), (15, 1), (42, 1), (51, 1), (63, 1), (65, 1)] }, { coefficient := -2, powers := [(11, 1), (17, 1), (31, 1), (32, 1), (37, 1), (39, 1), (42, 1), (65, 1), (69, 1)] }, { coefficient := 2, powers := [(11, 1), (23, 1), (32, 1), (37, 1), (39, 1), (42, 1), (65, 1), (69, 1)] }, { coefficient := 2, powers := [(11, 1), (31, 1), (32, 1), (37, 1), (42, 1), (48, 1), (63, 1), (65, 1)] }, { coefficient := -1, powers := [(11, 1), (31, 1), (32, 1), (39, 2), (51, 1), (54, 1), (68, 1)] }, { coefficient := 1, powers := [(11, 1), (31, 1), (37, 1), (42, 1), (65, 1), (66, 1)] }, { coefficient := 1, powers := [(11, 1), (31, 1), (42, 1), (51, 1), (54, 1), (65, 1)] }, { coefficient := -1, powers := [(11, 1), (32, 1), (39, 2), (68, 1)] }, { coefficient := -1, powers := [(11, 1), (34, 1), (39, 2), (49, 1), (54, 1), (68, 1)] }, { coefficient := -1, powers := [(11, 1), (39, 1), (68, 1)] }, { coefficient := 1, powers := [(15, 1), (19, 1), (32, 1), (39, 2), (51, 1), (63, 1), (68, 1)] }, { coefficient := 1, powers := [(15, 1), (19, 1), (32, 1), (39, 1), (51, 1), (59, 1), (62, 1), (63, 1)] }, { coefficient := -1, powers := [(15, 1), (19, 1), (42, 1), (43, 1), (65, 1), (66, 1)] }, { coefficient := -1, powers := [(15, 1), (19, 1), (42, 1), (51, 1), (63, 1), (65, 1)] }, { coefficient := 1, powers := [(15, 1), (19, 1), (43, 1), (62, 1), (65, 1), (66, 1)] }, { coefficient := 1, powers := [(15, 1), (19, 1), (51, 1), (62, 1), (63, 1), (65, 1)] }, { coefficient := -1, powers := [(15, 1), (33, 1), (36, 1), (40, 1), (62, 1), (69, 1)] }, { coefficient := -1, powers := [(15, 1), (33, 1), (36, 1), (43, 1), (62, 1), (66, 1)] }, { coefficient := 2, powers := [(17, 1), (19, 1), (31, 1), (32, 1), (37, 1), (39, 1), (42, 1), (65, 1), (69, 1)] }, { coefficient := -2, powers := [(17, 1), (19, 1), (31, 1), (32, 1), (37, 1), (39, 1), (62, 1), (65, 1), (69, 1)] }, { coefficient := -2, powers := [(19, 1), (23, 1), (32, 1), (37, 1), (39, 1), (42, 1), (65, 1), (69, 1)] }, { coefficient := 2, powers := [(19, 1), (23, 1), (32, 1), (37, 1), (39, 1), (62, 1), (65, 1), (69, 1)] }, { coefficient := -2, powers := [(19, 1), (31, 1), (32, 1), (37, 1), (42, 1), (48, 1), (63, 1), (65, 1)] }, { coefficient := 2, powers := [(19, 1), (31, 1), (32, 1), (37, 1), (48, 1), (62, 1), (63, 1), (65, 1)] }, { coefficient := 1, powers := [(19, 1), (31, 1), (32, 1), (39, 2), (51, 1), (54, 1), (68, 1)] }, { coefficient := 1, powers := [(19, 1), (31, 1), (32, 1), (39, 1), (51, 1), (54, 1), (59, 1), (62, 1)] }, { coefficient := -1, powers := [(19, 1), (31, 1), (37, 1), (42, 1), (65, 1), (66, 1)] }, { coefficient := 1, powers := [(19, 1), (31, 1), (37, 1), (62, 1), (65, 1), (66, 1)] }, { coefficient := -1, powers := [(19, 1), (31, 1), (42, 1), (51, 1), (54, 1), (65, 1)] }, { coefficient := 1, powers := [(19, 1), (31, 1), (51, 1), (54, 1), (62, 1), (65, 1)] }, { coefficient := 1, powers := [(19, 1), (32, 1), (39, 2), (68, 1)] }, { coefficient := 1, powers := [(19, 1), (32, 1), (39, 1), (59, 1), (62, 1)] }, { coefficient := 1, powers := [(19, 1), (34, 1), (39, 2), (49, 1), (54, 1), (68, 1)] }, { coefficient := 1, powers := [(19, 1), (34, 1), (39, 1), (49, 1), (54, 1), (59, 1), (62, 1)] }, { coefficient := 1, powers := [(19, 1), (39, 1), (68, 1)] }, { coefficient := 1, powers := [(19, 1), (47, 1), (62, 1)] }, { coefficient := 1, powers := [(19, 1), (59, 1), (62, 1)] }, { coefficient := 1, powers := [(19, 1), (62, 1), (65, 1)] }, { coefficient := -1, powers := [(31, 1), (33, 1), (36, 1), (37, 1), (62, 1), (66, 1)] }, { coefficient := -1, powers := [(31, 1), (33, 1), (36, 1), (40, 1), (60, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (65, 1)] }, { coefficient := -1, powers := [(19, 1), (47, 1)] }, { coefficient := -1, powers := [(19, 1), (65, 1)] }, { coefficient := 1, powers := [(33, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (11, 1), (34, 1), (42, 1), (63, 1), (65, 1)] }, { coefficient := -1, powers := [(1, 1), (19, 1), (34, 1), (42, 1), (63, 1), (65, 1)] }, { coefficient := 1, powers := [(1, 1), (19, 1), (34, 1), (62, 1), (63, 1), (65, 1)] }, { coefficient := -1, powers := [(7, 1), (11, 1), (32, 1), (39, 2), (66, 1), (68, 1)] }, { coefficient := 1, powers := [(7, 1), (19, 1), (32, 1), (39, 2), (66, 1), (68, 1)] }, { coefficient := 1, powers := [(7, 1), (19, 1), (32, 1), (39, 1), (59, 1), (62, 1), (66, 1)] }, { coefficient := 1, powers := [(7, 1), (33, 1), (36, 1), (62, 1), (66, 1)] }, { coefficient := 1, powers := [(11, 1), (17, 1), (34, 1), (39, 2), (49, 1), (68, 1)] }, { coefficient := -1, powers := [(11, 1), (17, 1), (34, 1), (42, 1), (43, 1), (65, 1)] }, { coefficient := -1, powers := [(11, 1), (22, 1), (42, 1), (50, 1), (66, 1)] }, { coefficient := 1, powers := [(11, 1), (23, 1), (32, 1), (39, 2), (51, 1), (68, 1)] }, { coefficient := -1, powers := [(11, 1), (23, 1), (42, 1), (51, 1), (65, 1)] }, { coefficient := 1, powers := [(11, 1), (34, 1), (40, 1), (42, 1), (65, 1)] }, { coefficient := 1, powers := [(11, 1), (34, 1), (42, 1), (50, 1), (63, 1)] }, { coefficient := -1, powers := [(17, 1), (19, 1), (34, 1), (39, 2), (49, 1), (68, 1)] }, { coefficient := -1, powers := [(17, 1), (19, 1), (34, 1), (39, 1), (49, 1), (59, 1), (62, 1)] }, { coefficient := 1, powers := [(17, 1), (19, 1), (34, 1), (42, 1), (43, 1), (65, 1)] }, { coefficient := -1, powers := [(17, 1), (19, 1), (34, 1), (43, 1), (62, 1), (65, 1)] }, { coefficient := 1, powers := [(19, 1), (22, 1), (42, 1), (50, 1), (66, 1)] }, { coefficient := -1, powers := [(19, 1), (22, 1), (50, 1), (62, 1), (66, 1)] }, { coefficient := -1, powers := [(19, 1), (23, 1), (32, 1), (39, 2), (51, 1), (68, 1)] }, { coefficient := -1, powers := [(19, 1), (23, 1), (32, 1), (39, 1), (51, 1), (59, 1), (62, 1)] }, { coefficient := 1, powers := [(19, 1), (23, 1), (42, 1), (51, 1), (65, 1)] }, { coefficient := -1, powers := [(19, 1), (23, 1), (51, 1), (62, 1), (65, 1)] }, { coefficient := -1, powers := [(19, 1), (34, 1), (40, 1), (42, 1), (65, 1)] }, { coefficient := 1, powers := [(19, 1), (34, 1), (40, 1), (62, 1), (65, 1)] }, { coefficient := -1, powers := [(19, 1), (34, 1), (42, 1), (50, 1), (63, 1)] }, { coefficient := 1, powers := [(19, 1), (34, 1), (50, 1), (62, 1), (63, 1)] }, { coefficient := -1, powers := [(23, 1), (33, 1), (36, 1), (51, 1), (62, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
theorem constantIdentity :
    ∑ index, (multipliers index).toPoly *
      (selectedEquations index).toPoly = C (1 : ℤ) := by
  simp (config := { maxSteps := 1000000 })
    [Fin.sum_univ_succ, multipliers, selectedEquations,
      SparsePoly.toPoly, SparseTerm.toPoly]
  ring

theorem selectedHasNoCommonZero {R : Type*}
    [CommRing R] [Nontrivial R] [CharZero R]
    (values : Fin 72 → R) :
    ¬ ∀ index : Fin 42,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.X5Case8Tree.LeafB4_4.selectedHasNoCommonZero

end Krenn.X5Case8Tree.LeafB4_4
