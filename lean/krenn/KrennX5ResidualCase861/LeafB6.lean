import KrennSparseCertificate

/-! Selected core of a strict exact certificate over a frozen system. -/

namespace Krenn.X5ResidualCase861.LeafB6

open Krenn.SparseCertificate
open MvPolynomial

def sourceSystemFileSHA256 : String := "066b45df8c715655945e6381bdc8b3808757a37e8cd420f4c9025457e333a13e"
def sourceSystemSemanticSHA256 : String := "c1f163eed1d17f3b283568351adb97b7dd6b4ff24616fea42efd72dc6de72a31"
def certificateSHA256 : String := "b03de0e82e22327582dc1a696f294f06fc11cccbba72b74db3b93b6278cc88f6"
def sourceEquationCount : Nat := 678

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedIndices : Fin 33 → Fin 678 := ![
  10,
  13,
  28,
  30,
  32,
  36,
  41,
  43,
  45,
  55,
  56,
  347,
  351,
  403,
  412,
  414,
  421,
  422,
  423,
  424,
  425,
  426,
  429,
  620,
  638,
  660,
  664,
  668,
  672,
  674,
  675,
  676,
  677
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 33 → SparsePoly (Fin 72) := ![
  [{ coefficient := 1, powers := [(17, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(38, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(39, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(41, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(44, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(46, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(46, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(47, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(51, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(51, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (52, 1), (69, 1)] }, { coefficient := 1, powers := [(29, 1), (51, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (55, 1), (66, 1)] }, { coefficient := 1, powers := [(21, 1), (51, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (47, 1), (54, 1)] }, { coefficient := 1, powers := [(54, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(34, 1), (39, 1), (55, 1)] }, { coefficient := 1, powers := [(55, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (61, 1)] }, { coefficient := 1, powers := [(16, 1), (55, 1)] }, { coefficient := 1, powers := [(24, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (57, 1)] }, { coefficient := 1, powers := [(29, 1), (39, 1), (60, 1)] }, { coefficient := 1, powers := [(39, 1), (69, 1)] }],
  [{ coefficient := 1, powers := [(35, 1), (64, 1)] }, { coefficient := 1, powers := [(38, 1), (58, 1)] }, { coefficient := 1, powers := [(44, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(35, 1), (67, 1)] }, { coefficient := 1, powers := [(41, 1), (58, 1)] }, { coefficient := 1, powers := [(44, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(37, 1), (66, 1)] }, { coefficient := 1, powers := [(40, 1), (60, 1)] }, { coefficient := 1, powers := [(51, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(37, 1), (69, 1)] }, { coefficient := 1, powers := [(43, 1), (60, 1)] }, { coefficient := 1, powers := [(51, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(38, 1), (67, 1)] }, { coefficient := 1, powers := [(41, 1), (64, 1)] }, { coefficient := 1, powers := [(44, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (54, 1), (67, 1)] }, { coefficient := 1, powers := [(24, 1), (44, 1), (54, 1)] }, { coefficient := 1, powers := [(32, 1), (41, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (39, 1), (67, 1)] }, { coefficient := 1, powers := [(17, 1), (47, 1), (55, 1)] }, { coefficient := 1, powers := [(24, 1), (39, 1), (58, 1)] }, { coefficient := 1, powers := [(32, 1), (39, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(15, 1), (39, 1), (69, 1)] }, { coefficient := 1, powers := [(31, 1), (39, 1), (60, 1)] }, { coefficient := 1, powers := [(34, 1), (39, 1), (57, 1)] }, { coefficient := 1, powers := [(57, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (47, 1), (61, 1)] }, { coefficient := 1, powers := [(16, 1), (47, 1), (55, 1)] }, { coefficient := 1, powers := [(24, 1), (47, 1), (52, 1)] }, { coefficient := 1, powers := [(52, 1), (67, 1)] }, { coefficient := 1, powers := [(55, 1), (64, 1)] }, { coefficient := 1, powers := [(58, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (46, 1), (61, 1)] }, { coefficient := 1, powers := [(22, 1), (46, 1), (55, 1)] }, { coefficient := 1, powers := [(30, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(34, 1), (35, 1), (61, 1)] }, { coefficient := 1, powers := [(34, 1), (38, 1), (55, 1)] }, { coefficient := 1, powers := [(34, 1), (41, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (54, 1), (69, 1)] }, { coefficient := 1, powers := [(4, 1), (57, 1), (66, 1)] }, { coefficient := 1, powers := [(4, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(21, 1), (37, 1), (69, 1)] }, { coefficient := 1, powers := [(21, 1), (43, 1), (60, 1)] }, { coefficient := 1, powers := [(21, 1), (51, 1), (57, 1)] }, { coefficient := 1, powers := [(29, 1), (37, 1), (66, 1)] }, { coefficient := 1, powers := [(29, 1), (40, 1), (60, 1)] }, { coefficient := 1, powers := [(29, 1), (51, 1), (54, 1)] }, { coefficient := 1, powers := [(40, 1), (69, 1)] }, { coefficient := 1, powers := [(43, 1), (66, 1)] }, { coefficient := 1, powers := [(51, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (52, 1), (67, 1)] }, { coefficient := 1, powers := [(0, 1), (55, 1), (64, 1)] }, { coefficient := 1, powers := [(0, 1), (58, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (38, 1), (67, 1)] }, { coefficient := 1, powers := [(8, 1), (41, 1), (64, 1)] }, { coefficient := 1, powers := [(8, 1), (44, 1), (61, 1)] }, { coefficient := 1, powers := [(16, 1), (35, 1), (67, 1)] }, { coefficient := 1, powers := [(16, 1), (41, 1), (58, 1)] }, { coefficient := 1, powers := [(16, 1), (44, 1), (55, 1)] }, { coefficient := 1, powers := [(24, 1), (35, 1), (64, 1)] }, { coefficient := 1, powers := [(24, 1), (38, 1), (58, 1)] }, { coefficient := 1, powers := [(24, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(32, 1), (35, 1), (61, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1), (55, 1)] }, { coefficient := 1, powers := [(32, 1), (41, 1), (52, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(7, 1), (54, 1), (69, 1)] }, { coefficient := 1, powers := [(7, 1), (57, 1), (66, 1)] }, { coefficient := 1, powers := [(7, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(15, 1), (40, 1), (69, 1)] }, { coefficient := 1, powers := [(15, 1), (43, 1), (66, 1)] }, { coefficient := 1, powers := [(15, 1), (51, 1), (63, 1)] }, { coefficient := 1, powers := [(23, 1), (37, 1), (69, 1)] }, { coefficient := 1, powers := [(23, 1), (43, 1), (60, 1)] }, { coefficient := 1, powers := [(23, 1), (51, 1), (57, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1), (66, 1)] }, { coefficient := 1, powers := [(31, 1), (40, 1), (60, 1)] }, { coefficient := 1, powers := [(31, 1), (51, 1), (54, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1), (63, 1)] }, { coefficient := 1, powers := [(34, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(34, 1), (43, 1), (54, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(52, 1), (70, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(55, 1), (71, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(61, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 33 → SparsePoly (Fin 72) := ![
  [{ coefficient := 1, powers := [(7, 1), (34, 1), (38, 1), (47, 1), (54, 1), (69, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (15, 1), (57, 1), (66, 1), (71, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (15, 1), (32, 1), (55, 1), (63, 1)] }, { coefficient := 1, powers := [(7, 1), (15, 1), (29, 1), (32, 1), (39, 1), (55, 1), (66, 1)] }, { coefficient := -1, powers := [(7, 1), (31, 1), (32, 1), (39, 1), (55, 1), (66, 1)] }, { coefficient := 1, powers := [(7, 1), (32, 1), (55, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (8, 1), (34, 1), (38, 1), (54, 1), (69, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (15, 1), (32, 1), (52, 1), (63, 1)] }, { coefficient := 1, powers := [(7, 1), (15, 1), (29, 1), (32, 1), (39, 1), (52, 1), (66, 1)] }, { coefficient := -1, powers := [(7, 1), (31, 1), (32, 1), (39, 1), (52, 1), (66, 1)] }, { coefficient := 1, powers := [(7, 1), (32, 1), (52, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (24, 1), (52, 1), (69, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (24, 1), (30, 1), (32, 1), (38, 1), (39, 1), (54, 1), (58, 1), (69, 1)] }, { coefficient := 1, powers := [(7, 1), (30, 1), (32, 1), (39, 1), (57, 1), (66, 1)] }, { coefficient := -1, powers := [(30, 1), (32, 1), (37, 1), (63, 1)] }, { coefficient := -1, powers := [(30, 1), (32, 1), (40, 1), (57, 1)] }, { coefficient := -1, powers := [(30, 1), (32, 1), (43, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (22, 1), (24, 1), (32, 1), (38, 1), (39, 1), (54, 1), (58, 1), (69, 1)] }, { coefficient := 1, powers := [(7, 1), (22, 1), (32, 1), (39, 1), (57, 1), (66, 1)] }, { coefficient := -1, powers := [(22, 1), (32, 1), (37, 1), (63, 1)] }, { coefficient := -1, powers := [(22, 1), (32, 1), (40, 1), (57, 1)] }, { coefficient := -1, powers := [(22, 1), (32, 1), (43, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (7, 1), (24, 1), (52, 1), (69, 1)] }],
  [{ coefficient := 1, powers := [(15, 1), (29, 1), (54, 1), (70, 1)] }],
  [{ coefficient := 1, powers := [(15, 1), (21, 1), (57, 1), (71, 1)] }],
  [{ coefficient := -1, powers := [(15, 1), (54, 1), (70, 1)] }],
  [{ coefficient := -1, powers := [(15, 1), (57, 1), (71, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (7, 1), (52, 1), (69, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (32, 1), (38, 1), (54, 1), (69, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (4, 1), (15, 1), (47, 1), (60, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (7, 1), (15, 1), (29, 1), (39, 1), (47, 1), (60, 1), (66, 1)] }, { coefficient := -1, powers := [(0, 1), (7, 1), (24, 1), (34, 1), (38, 1), (39, 1), (47, 1), (54, 1), (58, 1), (69, 1)] }, { coefficient := 1, powers := [(0, 1), (7, 1), (31, 1), (39, 1), (47, 1), (60, 1), (66, 1)] }, { coefficient := 1, powers := [(0, 1), (7, 1), (34, 1), (39, 1), (47, 1), (57, 1), (66, 1)] }, { coefficient := -1, powers := [(0, 1), (7, 1), (47, 1), (54, 1), (69, 1)] }, { coefficient := -1, powers := [(0, 1), (7, 1), (47, 1), (60, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (34, 1), (37, 1), (47, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (34, 1), (40, 1), (47, 1), (57, 1)] }, { coefficient := -1, powers := [(0, 1), (34, 1), (43, 1), (47, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (15, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (15, 1), (24, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(7, 1), (15, 1), (24, 1), (29, 1), (39, 1), (60, 1), (66, 1)] }, { coefficient := 1, powers := [(7, 1), (24, 2), (34, 1), (38, 1), (39, 1), (54, 1), (58, 1), (69, 1)] }, { coefficient := -1, powers := [(7, 1), (24, 1), (31, 1), (39, 1), (60, 1), (66, 1)] }, { coefficient := -1, powers := [(7, 1), (24, 1), (34, 1), (39, 1), (57, 1), (66, 1)] }, { coefficient := 1, powers := [(7, 1), (24, 1), (54, 1), (69, 1)] }, { coefficient := 1, powers := [(7, 1), (24, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(24, 1), (34, 1), (37, 1), (63, 1)] }, { coefficient := 1, powers := [(24, 1), (34, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(24, 1), (34, 1), (43, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (15, 1), (16, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(7, 1), (15, 1), (16, 1), (29, 1), (39, 1), (60, 1), (66, 1)] }, { coefficient := 1, powers := [(7, 1), (16, 1), (24, 1), (34, 1), (38, 1), (39, 1), (54, 1), (58, 1), (69, 1)] }, { coefficient := -1, powers := [(7, 1), (16, 1), (31, 1), (39, 1), (60, 1), (66, 1)] }, { coefficient := -1, powers := [(7, 1), (16, 1), (34, 1), (39, 1), (57, 1), (66, 1)] }, { coefficient := 1, powers := [(7, 1), (16, 1), (54, 1), (69, 1)] }, { coefficient := 1, powers := [(7, 1), (16, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(16, 1), (34, 1), (37, 1), (63, 1)] }, { coefficient := 1, powers := [(16, 1), (34, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(16, 1), (34, 1), (43, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(15, 1), (29, 1)] }, { coefficient := 1, powers := [(31, 1)] }],
  [{ coefficient := -1, powers := [(15, 1), (21, 1)] }, { coefficient := 1, powers := [(23, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (8, 1), (15, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(7, 1), (8, 1), (15, 1), (29, 1), (39, 1), (60, 1), (66, 1)] }, { coefficient := 1, powers := [(7, 1), (8, 1), (24, 1), (34, 1), (38, 1), (39, 1), (54, 1), (58, 1), (69, 1)] }, { coefficient := -1, powers := [(7, 1), (8, 1), (31, 1), (39, 1), (60, 1), (66, 1)] }, { coefficient := -1, powers := [(7, 1), (8, 1), (34, 1), (39, 1), (57, 1), (66, 1)] }, { coefficient := 1, powers := [(7, 1), (8, 1), (54, 1), (69, 1)] }, { coefficient := 1, powers := [(7, 1), (8, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (37, 1), (63, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (43, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (52, 1), (69, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (34, 1), (38, 1), (54, 1), (69, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (4, 1), (15, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(0, 1), (7, 1), (15, 1), (29, 1), (39, 1), (60, 1), (66, 1)] }, { coefficient := 1, powers := [(0, 1), (7, 1), (24, 1), (34, 1), (38, 1), (39, 1), (54, 1), (58, 1), (69, 1)] }, { coefficient := -1, powers := [(0, 1), (7, 1), (31, 1), (39, 1), (60, 1), (66, 1)] }, { coefficient := -1, powers := [(0, 1), (7, 1), (34, 1), (39, 1), (57, 1), (66, 1)] }, { coefficient := 1, powers := [(0, 1), (7, 1), (54, 1), (69, 1)] }, { coefficient := 1, powers := [(0, 1), (7, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(0, 1), (34, 1), (37, 1), (63, 1)] }, { coefficient := 1, powers := [(0, 1), (34, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (34, 1), (43, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (24, 1), (32, 1), (38, 1), (39, 1), (54, 1), (58, 1), (69, 1)] }, { coefficient := -1, powers := [(7, 1), (32, 1), (39, 1), (57, 1), (66, 1)] }, { coefficient := 1, powers := [(32, 1), (37, 1), (63, 1)] }, { coefficient := 1, powers := [(32, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(32, 1), (43, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(15, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (15, 1), (60, 1), (63, 1)] }, { coefficient := -1, powers := [(7, 1), (15, 1), (29, 1), (39, 1), (60, 1), (66, 1)] }, { coefficient := -1, powers := [(7, 1), (24, 1), (34, 1), (38, 1), (39, 1), (54, 1), (58, 1), (69, 1)] }, { coefficient := 1, powers := [(7, 1), (31, 1), (39, 1), (60, 1), (66, 1)] }, { coefficient := 1, powers := [(7, 1), (34, 1), (39, 1), (57, 1), (66, 1)] }, { coefficient := -1, powers := [(7, 1), (54, 1), (69, 1)] }, { coefficient := -1, powers := [(7, 1), (60, 1), (63, 1)] }, { coefficient := -1, powers := [(34, 1), (37, 1), (63, 1)] }, { coefficient := -1, powers := [(34, 1), (40, 1), (57, 1)] }, { coefficient := -1, powers := [(34, 1), (43, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(4, 1), (15, 1), (54, 1), (69, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (15, 1), (57, 1), (66, 1)] }, { coefficient := -1, powers := [(7, 1), (15, 1), (20, 1), (57, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (15, 1), (32, 1), (35, 1), (60, 1), (63, 1)] }, { coefficient := -1, powers := [(7, 1), (13, 1), (24, 1), (32, 1), (38, 1), (39, 1), (46, 1), (54, 1), (58, 1), (69, 1)] }, { coefficient := 1, powers := [(7, 1), (13, 1), (32, 1), (39, 1), (46, 1), (57, 1), (66, 1)] }, { coefficient := 1, powers := [(7, 1), (15, 1), (29, 1), (32, 1), (35, 1), (39, 1), (60, 1), (66, 1)] }, { coefficient := -1, powers := [(7, 1), (31, 1), (32, 1), (35, 1), (39, 1), (60, 1), (66, 1)] }, { coefficient := 1, powers := [(7, 1), (32, 1), (35, 1), (54, 1), (69, 1)] }, { coefficient := 1, powers := [(7, 1), (32, 1), (35, 1), (60, 1), (63, 1)] }, { coefficient := -1, powers := [(13, 1), (32, 1), (37, 1), (46, 1), (63, 1)] }, { coefficient := -1, powers := [(13, 1), (32, 1), (40, 1), (46, 1), (57, 1)] }, { coefficient := -1, powers := [(13, 1), (32, 1), (43, 1), (46, 1), (54, 1)] }]
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
    ¬ ∀ index : Fin 33,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.X5ResidualCase861.LeafB6.selectedHasNoCommonZero

end Krenn.X5ResidualCase861.LeafB6
