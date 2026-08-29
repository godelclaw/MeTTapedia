import KrennSparseCertificate

/-! Selected core of a strict exact certificate over a frozen system. -/

namespace Krenn.X5Case52Tree.LeafB6

open Krenn.SparseCertificate
open MvPolynomial

def sourceSystemFileSHA256 : String := "8ebdb60bd912e85fe471f2ee28a224e97e10fcd7de204c932542691c8c7bf3b8"
def sourceSystemSemanticSHA256 : String := "69fb0ac11f9b55c709f95f5203e7cd110e77242f3789756848edbd971b9eacc0"
def certificateSHA256 : String := "a7ec00bb4ce9c1898ca2e1585342ba36d687a76c80ea9a280f3881e9b3c5fac6"
def sourceEquationCount : Nat := 678

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedIndices : Fin 21 → Fin 678 := ![
  1,
  15,
  412,
  416,
  417,
  420,
  422,
  423,
  424,
  426,
  442,
  643,
  650,
  664,
  666,
  671,
  673,
  674,
  675,
  676,
  677
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 21 → SparsePoly (Fin 72) := ![
  [{ coefficient := 1, powers := [(63, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(32, 1), (40, 1), (56, 1)] }, { coefficient := 1, powers := [(56, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (63, 1)] }, { coefficient := 1, powers := [(20, 1), (57, 1)] }, { coefficient := 1, powers := [(28, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (62, 1)] }, { coefficient := 1, powers := [(22, 1), (56, 1)] }, { coefficient := 1, powers := [(30, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (56, 1)] }, { coefficient := 1, powers := [(25, 1), (53, 1)] }, { coefficient := 1, powers := [(62, 1)] }],
  [{ coefficient := 1, powers := [(36, 1), (65, 1)] }, { coefficient := 1, powers := [(39, 1), (59, 1)] }, { coefficient := 1, powers := [(48, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(36, 1), (68, 1)] }, { coefficient := 1, powers := [(42, 1), (59, 1)] }, { coefficient := 1, powers := [(48, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(37, 1), (66, 1)] }, { coefficient := 1, powers := [(40, 1), (60, 1)] }, { coefficient := 1, powers := [(51, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(40, 1), (69, 1)] }, { coefficient := 1, powers := [(43, 1), (66, 1)] }, { coefficient := 1, powers := [(51, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (56, 1), (66, 1)] }, { coefficient := 1, powers := [(23, 1), (51, 1), (56, 1)] }, { coefficient := 1, powers := [(34, 1), (40, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (53, 1), (68, 1)] }, { coefficient := 1, powers := [(0, 1), (56, 1), (65, 1)] }, { coefficient := 1, powers := [(0, 1), (59, 1), (62, 1)] }, { coefficient := 1, powers := [(17, 1), (45, 1), (56, 1)] }, { coefficient := 1, powers := [(25, 1), (45, 1), (53, 1)] }, { coefficient := 1, powers := [(45, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (54, 1), (69, 1)] }, { coefficient := 1, powers := [(3, 1), (57, 1), (66, 1)] }, { coefficient := 1, powers := [(3, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(12, 1), (49, 1), (63, 1)] }, { coefficient := 1, powers := [(20, 1), (49, 1), (57, 1)] }, { coefficient := 1, powers := [(28, 1), (49, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (49, 1), (62, 1)] }, { coefficient := 1, powers := [(22, 1), (49, 1), (56, 1)] }, { coefficient := 1, powers := [(30, 1), (49, 1), (53, 1)] }, { coefficient := 1, powers := [(34, 1), (36, 1), (62, 1)] }, { coefficient := 1, powers := [(34, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(34, 1), (42, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (54, 1), (69, 1)] }, { coefficient := 1, powers := [(1, 1), (57, 1), (66, 1)] }, { coefficient := 1, powers := [(1, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(9, 1), (40, 1), (69, 1)] }, { coefficient := 1, powers := [(9, 1), (43, 1), (66, 1)] }, { coefficient := 1, powers := [(9, 1), (51, 1), (63, 1)] }, { coefficient := 1, powers := [(26, 1), (37, 1), (66, 1)] }, { coefficient := 1, powers := [(26, 1), (40, 1), (60, 1)] }, { coefficient := 1, powers := [(26, 1), (51, 1), (54, 1)] }, { coefficient := 1, powers := [(37, 1), (69, 1)] }, { coefficient := 1, powers := [(43, 1), (60, 1)] }, { coefficient := 1, powers := [(51, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (36, 1), (68, 1)] }, { coefficient := 1, powers := [(17, 1), (42, 1), (59, 1)] }, { coefficient := 1, powers := [(17, 1), (48, 1), (56, 1)] }, { coefficient := 1, powers := [(25, 1), (36, 1), (65, 1)] }, { coefficient := 1, powers := [(25, 1), (39, 1), (59, 1)] }, { coefficient := 1, powers := [(25, 1), (48, 1), (53, 1)] }, { coefficient := 1, powers := [(39, 1), (68, 1)] }, { coefficient := 1, powers := [(42, 1), (65, 1)] }, { coefficient := 1, powers := [(48, 1), (62, 1)] }, { coefficient := 1, powers := [(53, 1), (68, 1)] }, { coefficient := 1, powers := [(56, 1), (65, 1)] }, { coefficient := 1, powers := [(59, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (53, 1), (68, 1)] }, { coefficient := 1, powers := [(3, 1), (56, 1), (65, 1)] }, { coefficient := 1, powers := [(3, 1), (59, 1), (62, 1)] }, { coefficient := 1, powers := [(11, 1), (39, 1), (68, 1)] }, { coefficient := 1, powers := [(11, 1), (42, 1), (65, 1)] }, { coefficient := 1, powers := [(11, 1), (48, 1), (62, 1)] }, { coefficient := 1, powers := [(19, 1), (36, 1), (68, 1)] }, { coefficient := 1, powers := [(19, 1), (42, 1), (59, 1)] }, { coefficient := 1, powers := [(19, 1), (48, 1), (56, 1)] }, { coefficient := 1, powers := [(27, 1), (36, 1), (65, 1)] }, { coefficient := 1, powers := [(27, 1), (39, 1), (59, 1)] }, { coefficient := 1, powers := [(27, 1), (48, 1), (53, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1), (62, 1)] }, { coefficient := 1, powers := [(33, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(33, 1), (42, 1), (53, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(7, 1), (54, 1), (69, 1)] }, { coefficient := 1, powers := [(7, 1), (57, 1), (66, 1)] }, { coefficient := 1, powers := [(7, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(15, 1), (40, 1), (69, 1)] }, { coefficient := 1, powers := [(15, 1), (43, 1), (66, 1)] }, { coefficient := 1, powers := [(15, 1), (51, 1), (63, 1)] }, { coefficient := 1, powers := [(23, 1), (37, 1), (69, 1)] }, { coefficient := 1, powers := [(23, 1), (43, 1), (60, 1)] }, { coefficient := 1, powers := [(23, 1), (51, 1), (57, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1), (66, 1)] }, { coefficient := 1, powers := [(31, 1), (40, 1), (60, 1)] }, { coefficient := 1, powers := [(31, 1), (51, 1), (54, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1), (63, 1)] }, { coefficient := 1, powers := [(34, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(34, 1), (43, 1), (54, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (70, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(3, 1), (71, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(7, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 21 → SparsePoly (Fin 72) := ![
  [{ coefficient := 1, powers := [(1, 1), (3, 1), (23, 1), (60, 1), (71, 1)] }, { coefficient := -1, powers := [(1, 1), (23, 1), (60, 1)] }, { coefficient := -1, powers := [(3, 1), (7, 1), (34, 1), (40, 1), (56, 1), (57, 1), (60, 1), (65, 1)] }, { coefficient := -1, powers := [(3, 1), (7, 1), (34, 1), (43, 1), (54, 1), (56, 1), (60, 1), (65, 1)] }, { coefficient := -1, powers := [(3, 1), (34, 2), (37, 1), (40, 1), (56, 1), (57, 1), (65, 1)] }, { coefficient := -1, powers := [(3, 1), (34, 2), (37, 1), (43, 1), (54, 1), (56, 1), (65, 1)] }, { coefficient := 1, powers := [(7, 1), (11, 1), (34, 1), (40, 1), (56, 1), (57, 1), (60, 1), (65, 1)] }, { coefficient := 1, powers := [(7, 1), (11, 1), (34, 1), (43, 1), (54, 1), (56, 1), (60, 1), (65, 1)] }, { coefficient := 1, powers := [(7, 1), (60, 1)] }, { coefficient := 1, powers := [(11, 1), (34, 2), (37, 1), (40, 1), (56, 1), (57, 1), (65, 1)] }, { coefficient := 1, powers := [(11, 1), (34, 2), (37, 1), (43, 1), (54, 1), (56, 1), (65, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (32, 1), (34, 1), (40, 1), (43, 1), (51, 1), (54, 1), (57, 1), (65, 1)] }, { coefficient := -1, powers := [(3, 1), (32, 1), (34, 1), (43, 2), (51, 1), (54, 2), (65, 1)] }, { coefficient := 1, powers := [(3, 1), (32, 1), (40, 1), (51, 1), (57, 1), (65, 1)] }, { coefficient := 1, powers := [(3, 1), (32, 1), (43, 1), (51, 1), (54, 1), (65, 1)] }, { coefficient := -1, powers := [(3, 1), (34, 1), (37, 1), (40, 1), (57, 1), (65, 1), (69, 1)] }, { coefficient := -1, powers := [(3, 1), (34, 1), (37, 1), (43, 1), (54, 1), (65, 1), (69, 1)] }, { coefficient := -1, powers := [(3, 1), (34, 1), (40, 1), (43, 1), (57, 1), (60, 1), (65, 1)] }, { coefficient := -1, powers := [(3, 1), (34, 1), (43, 2), (54, 1), (60, 1), (65, 1)] }, { coefficient := 1, powers := [(11, 1), (32, 1), (34, 1), (40, 1), (43, 1), (51, 1), (54, 1), (57, 1), (65, 1)] }, { coefficient := 1, powers := [(11, 1), (32, 1), (34, 1), (43, 2), (51, 1), (54, 2), (65, 1)] }, { coefficient := -1, powers := [(11, 1), (32, 1), (40, 1), (51, 1), (57, 1), (65, 1)] }, { coefficient := -1, powers := [(11, 1), (32, 1), (43, 1), (51, 1), (54, 1), (65, 1)] }, { coefficient := 1, powers := [(11, 1), (34, 1), (37, 1), (40, 1), (57, 1), (65, 1), (69, 1)] }, { coefficient := 1, powers := [(11, 1), (34, 1), (37, 1), (43, 1), (54, 1), (65, 1), (69, 1)] }, { coefficient := 1, powers := [(11, 1), (34, 1), (40, 1), (43, 1), (57, 1), (60, 1), (65, 1)] }, { coefficient := 1, powers := [(11, 1), (34, 1), (43, 2), (54, 1), (60, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (34, 2), (40, 1), (43, 1), (54, 1), (57, 1), (65, 1)] }, { coefficient := -1, powers := [(3, 1), (34, 2), (43, 2), (54, 2), (65, 1)] }, { coefficient := 1, powers := [(3, 1), (34, 1), (40, 1), (57, 1), (65, 1)] }, { coefficient := 1, powers := [(3, 1), (34, 1), (43, 1), (54, 1), (65, 1)] }, { coefficient := 1, powers := [(11, 1), (34, 2), (40, 1), (43, 1), (54, 1), (57, 1), (65, 1)] }, { coefficient := 1, powers := [(11, 1), (34, 2), (43, 2), (54, 2), (65, 1)] }, { coefficient := -1, powers := [(11, 1), (34, 1), (40, 1), (57, 1), (65, 1)] }, { coefficient := -1, powers := [(11, 1), (34, 1), (43, 1), (54, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (23, 1), (49, 1), (71, 1)] }],
  [{ coefficient := -1, powers := [(33, 1), (40, 1), (49, 1), (57, 1)] }, { coefficient := -1, powers := [(33, 1), (43, 1), (49, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (34, 1), (40, 1), (45, 1), (57, 1), (70, 1)] }, { coefficient := -1, powers := [(3, 1), (34, 1), (43, 1), (45, 1), (54, 1), (70, 1)] }, { coefficient := 1, powers := [(11, 1), (34, 1), (40, 1), (45, 1), (57, 1), (70, 1)] }, { coefficient := 1, powers := [(11, 1), (34, 1), (43, 1), (45, 1), (54, 1), (70, 1)] }],
  [{ coefficient := -1, powers := [(11, 1), (25, 1), (34, 1), (40, 1), (57, 1)] }, { coefficient := -1, powers := [(11, 1), (25, 1), (34, 1), (43, 1), (54, 1)] }, { coefficient := 1, powers := [(27, 1), (34, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(27, 1), (34, 1), (43, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(11, 1), (17, 1), (34, 1), (40, 1), (57, 1)] }, { coefficient := -1, powers := [(11, 1), (17, 1), (34, 1), (43, 1), (54, 1)] }, { coefficient := 1, powers := [(19, 1), (34, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(19, 1), (34, 1), (43, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (31, 1), (34, 1), (40, 1), (56, 1), (57, 1), (65, 1)] }, { coefficient := -1, powers := [(3, 1), (31, 1), (34, 1), (43, 1), (54, 1), (56, 1), (65, 1)] }, { coefficient := 1, powers := [(11, 1), (31, 1), (34, 1), (40, 1), (56, 1), (57, 1), (65, 1)] }, { coefficient := 1, powers := [(11, 1), (31, 1), (34, 1), (43, 1), (54, 1), (56, 1), (65, 1)] }, { coefficient := -1, powers := [(23, 1), (26, 1)] }, { coefficient := 1, powers := [(31, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (15, 1), (34, 1), (40, 1), (56, 1), (57, 1), (65, 1)] }, { coefficient := -1, powers := [(3, 1), (15, 1), (34, 1), (43, 1), (54, 1), (56, 1), (65, 1)] }, { coefficient := -1, powers := [(9, 1), (23, 1)] }, { coefficient := 1, powers := [(11, 1), (15, 1), (34, 1), (40, 1), (56, 1), (57, 1), (65, 1)] }, { coefficient := 1, powers := [(11, 1), (15, 1), (34, 1), (43, 1), (54, 1), (56, 1), (65, 1)] }, { coefficient := 1, powers := [(15, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (32, 1), (34, 1), (40, 1), (43, 1), (54, 1), (57, 1), (65, 1)] }, { coefficient := 1, powers := [(3, 1), (32, 1), (34, 1), (43, 2), (54, 2), (65, 1)] }, { coefficient := -1, powers := [(3, 1), (32, 1), (40, 1), (57, 1), (65, 1)] }, { coefficient := -1, powers := [(3, 1), (32, 1), (43, 1), (54, 1), (65, 1)] }, { coefficient := -1, powers := [(3, 1), (34, 1), (40, 1), (57, 2), (65, 1)] }, { coefficient := -1, powers := [(3, 1), (34, 1), (43, 1), (54, 1), (57, 1), (65, 1)] }, { coefficient := -1, powers := [(11, 1), (32, 1), (34, 1), (40, 1), (43, 1), (54, 1), (57, 1), (65, 1)] }, { coefficient := -1, powers := [(11, 1), (32, 1), (34, 1), (43, 2), (54, 2), (65, 1)] }, { coefficient := 1, powers := [(11, 1), (32, 1), (40, 1), (57, 1), (65, 1)] }, { coefficient := 1, powers := [(11, 1), (32, 1), (43, 1), (54, 1), (65, 1)] }, { coefficient := 1, powers := [(11, 1), (34, 1), (40, 1), (57, 2), (65, 1)] }, { coefficient := 1, powers := [(11, 1), (34, 1), (43, 1), (54, 1), (57, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (34, 1), (40, 1), (57, 1), (70, 1)] }, { coefficient := 1, powers := [(3, 1), (34, 1), (43, 1), (54, 1), (70, 1)] }, { coefficient := -1, powers := [(11, 1), (34, 1), (40, 1), (57, 1), (70, 1)] }, { coefficient := -1, powers := [(11, 1), (34, 1), (43, 1), (54, 1), (70, 1)] }],
  [{ coefficient := -1, powers := [(1, 1), (23, 1), (71, 1)] }],
  [{ coefficient := 1, powers := [(33, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(33, 1), (43, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(23, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (34, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(11, 1), (34, 1), (43, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(34, 1), (40, 1), (57, 1)] }, { coefficient := -1, powers := [(34, 1), (43, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (34, 1), (40, 1), (56, 1), (57, 1), (65, 1)] }, { coefficient := 1, powers := [(3, 1), (34, 1), (43, 1), (54, 1), (56, 1), (65, 1)] }, { coefficient := -1, powers := [(11, 1), (34, 1), (40, 1), (56, 1), (57, 1), (65, 1)] }, { coefficient := -1, powers := [(11, 1), (34, 1), (43, 1), (54, 1), (56, 1), (65, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(3, 1), (34, 1), (40, 1), (53, 1), (57, 1), (68, 1)] }, { coefficient := -1, powers := [(3, 1), (34, 1), (40, 1), (56, 1), (57, 1), (65, 1)] }, { coefficient := -1, powers := [(3, 1), (34, 1), (40, 1), (57, 1), (59, 1), (62, 1)] }, { coefficient := -1, powers := [(3, 1), (34, 1), (43, 1), (53, 1), (54, 1), (68, 1)] }, { coefficient := -1, powers := [(3, 1), (34, 1), (43, 1), (54, 1), (56, 1), (65, 1)] }, { coefficient := -1, powers := [(3, 1), (34, 1), (43, 1), (54, 1), (59, 1), (62, 1)] }, { coefficient := 1, powers := [(11, 1), (34, 1), (40, 1), (53, 1), (57, 1), (68, 1)] }, { coefficient := 1, powers := [(11, 1), (34, 1), (40, 1), (56, 1), (57, 1), (65, 1)] }, { coefficient := 1, powers := [(11, 1), (34, 1), (40, 1), (57, 1), (59, 1), (62, 1)] }, { coefficient := 1, powers := [(11, 1), (34, 1), (43, 1), (53, 1), (54, 1), (68, 1)] }, { coefficient := 1, powers := [(11, 1), (34, 1), (43, 1), (54, 1), (56, 1), (65, 1)] }, { coefficient := 1, powers := [(11, 1), (34, 1), (43, 1), (54, 1), (59, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (23, 1), (54, 1), (69, 1)] }, { coefficient := 1, powers := [(1, 1), (23, 1), (57, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (32, 1), (34, 1), (40, 1), (43, 1), (54, 1), (56, 1), (57, 1), (65, 1), (66, 1)] }, { coefficient := -1, powers := [(3, 1), (32, 1), (34, 1), (43, 2), (54, 2), (56, 1), (65, 1), (66, 1)] }, { coefficient := 1, powers := [(3, 1), (32, 1), (40, 1), (56, 1), (57, 1), (65, 1), (66, 1)] }, { coefficient := 1, powers := [(3, 1), (32, 1), (43, 1), (54, 1), (56, 1), (65, 1), (66, 1)] }, { coefficient := -1, powers := [(3, 1), (34, 1), (40, 1), (54, 1), (56, 1), (57, 1), (65, 1), (69, 1)] }, { coefficient := -1, powers := [(3, 1), (34, 1), (43, 1), (54, 2), (56, 1), (65, 1), (69, 1)] }, { coefficient := 1, powers := [(11, 1), (32, 1), (34, 1), (40, 1), (43, 1), (54, 1), (56, 1), (57, 1), (65, 1), (66, 1)] }, { coefficient := 1, powers := [(11, 1), (32, 1), (34, 1), (43, 2), (54, 2), (56, 1), (65, 1), (66, 1)] }, { coefficient := -1, powers := [(11, 1), (32, 1), (40, 1), (56, 1), (57, 1), (65, 1), (66, 1)] }, { coefficient := -1, powers := [(11, 1), (32, 1), (43, 1), (54, 1), (56, 1), (65, 1), (66, 1)] }, { coefficient := 1, powers := [(11, 1), (34, 1), (40, 1), (54, 1), (56, 1), (57, 1), (65, 1), (69, 1)] }, { coefficient := 1, powers := [(11, 1), (34, 1), (43, 1), (54, 2), (56, 1), (65, 1), (69, 1)] }, { coefficient := 1, powers := [(54, 1), (69, 1)] }, { coefficient := 1, powers := [(57, 1), (66, 1)] }]
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
    ¬ ∀ index : Fin 21,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.X5Case52Tree.LeafB6.selectedHasNoCommonZero

end Krenn.X5Case52Tree.LeafB6
