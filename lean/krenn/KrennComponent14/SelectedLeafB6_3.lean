import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component14.SelectedLeafB6_3

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "08da348245c7e9104dc8ca3682acaa3ee08a0167fa125151f045081c6217a376"
def certificateSHA256 : String := "aac5fc63c0f8fc7f87523956a696052196e9acc563b78ecabb0ef2071d21fd64"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 46 → Fin 640 := ![
  6,
  9,
  11,
  18,
  19,
  20,
  23,
  90,
  128,
  132,
  133,
  162,
  163,
  164,
  165,
  167,
  179,
  183,
  188,
  191,
  192,
  194,
  195,
  198,
  219,
  282,
  313,
  345,
  348,
  349,
  350,
  351,
  383,
  384,
  395,
  406,
  460,
  465,
  524,
  555,
  556,
  633,
  635,
  636,
  638,
  639
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 46 → SparsePoly (Fin 63) := ![
  [{ coefficient := 1, powers := [(5, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(15, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(15, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (17, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (21, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (27, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (42, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (48, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (46, 1)] }, { coefficient := 1, powers := [(11, 1), (25, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (48, 1)] }, { coefficient := 1, powers := [(15, 1), (19, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (52, 1)] }, { coefficient := 1, powers := [(15, 1), (19, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (42, 1)] }, { coefficient := 1, powers := [(16, 1), (21, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (48, 1)] }, { coefficient := 1, powers := [(12, 1), (27, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (44, 1)] }, { coefficient := 1, powers := [(12, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (39, 1)] }, { coefficient := 1, powers := [(16, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (50, 1)] }, { coefficient := 1, powers := [(21, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (50, 1)] }, { coefficient := 1, powers := [(22, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (51, 1)] }, { coefficient := 1, powers := [(28, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(28, 1), (39, 1)] }, { coefficient := 1, powers := [(28, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(39, 1), (42, 1)] }, { coefficient := 1, powers := [(42, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(44, 1), (48, 1)] }, { coefficient := 1, powers := [(48, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (31, 1), (54, 1)] }, { coefficient := 1, powers := [(21, 1), (48, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (17, 1), (54, 1)] }, { coefficient := 1, powers := [(12, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (23, 1), (39, 1)] }, { coefficient := 1, powers := [(16, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (52, 1)] }, { coefficient := 1, powers := [(17, 1), (52, 1)] }, { coefficient := 1, powers := [(24, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (46, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (52, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1)] }, { coefficient := 1, powers := [(12, 1), (28, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (58, 1)] }, { coefficient := 1, powers := [(12, 1), (46, 1)] }, { coefficient := 1, powers := [(16, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (58, 1)] }, { coefficient := 1, powers := [(12, 1), (55, 1)] }, { coefficient := 1, powers := [(16, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (39, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (39, 1)] }, { coefficient := 1, powers := [(16, 1), (28, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (40, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (54, 1)] }, { coefficient := 1, powers := [(12, 1), (22, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (28, 1), (57, 1)] }, { coefficient := 1, powers := [(21, 1), (51, 1)] }, { coefficient := 1, powers := [(28, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (22, 1), (57, 1)] }, { coefficient := 1, powers := [(22, 1)] }, { coefficient := 1, powers := [(27, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (52, 1)] }, { coefficient := 1, powers := [(28, 1), (40, 1)] }, { coefficient := 1, powers := [(28, 1), (45, 1), (48, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (40, 1), (54, 1)] }, { coefficient := 1, powers := [(18, 1), (48, 1), (54, 1)] }, { coefficient := 1, powers := [(40, 1)] }, { coefficient := 1, powers := [(45, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (42, 1), (51, 1)] }, { coefficient := 1, powers := [(22, 1), (55, 1)] }, { coefficient := 1, powers := [(28, 1), (46, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1)] }, { coefficient := 1, powers := [(6, 1), (57, 1)] }, { coefficient := 1, powers := [(23, 1), (39, 1)] }, { coefficient := 1, powers := [(23, 1), (44, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (50, 1)] }, { coefficient := 1, powers := [(3, 1), (57, 1)] }, { coefficient := 1, powers := [(17, 1), (50, 1)] }, { coefficient := 1, powers := [(17, 1), (54, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (37, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (40, 1), (55, 1)] }, { coefficient := 1, powers := [(2, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(5, 1), (28, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (52, 1)] }, { coefficient := 1, powers := [(8, 1), (22, 1), (58, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1), (46, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (40, 1)] }, { coefficient := 1, powers := [(12, 1), (22, 1), (55, 1)] }, { coefficient := 1, powers := [(12, 1), (28, 1), (46, 1)] }, { coefficient := 1, powers := [(12, 1), (34, 1), (37, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1), (52, 1)] }, { coefficient := 1, powers := [(16, 1), (28, 1), (40, 1)] }, { coefficient := 1, powers := [(16, 1), (31, 1), (37, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1), (60, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(39, 1), (61, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(40, 1), (62, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 46 → SparsePoly (Fin 63) := ![
  [{ coefficient := -1, powers := [(0, 1), (6, 1), (34, 1), (50, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (3, 1), (31, 1), (44, 1), (46, 1)] }, { coefficient := -2, powers := [(0, 1), (6, 1), (22, 1), (50, 1), (58, 1)] }, { coefficient := 1, powers := [(0, 1), (6, 1), (34, 1), (40, 1), (50, 1)] }, { coefficient := 1, powers := [(0, 1), (6, 1), (34, 1), (40, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (12, 1), (25, 1), (28, 1), (44, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (16, 1), (18, 1), (19, 1), (31, 1), (37, 1), (44, 1), (50, 1), (60, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 1), (16, 1), (19, 1), (21, 1), (37, 1), (50, 1), (57, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (16, 1), (19, 1), (31, 1), (37, 1), (45, 1), (50, 1), (60, 1), (62, 1)] }, { coefficient := -1, powers := [(18, 1), (19, 1), (44, 1), (60, 1), (62, 1)] }, { coefficient := 1, powers := [(19, 1), (45, 1), (60, 1), (62, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (16, 1), (19, 1), (22, 1), (23, 1), (44, 1), (50, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (16, 1), (19, 1), (22, 1), (39, 1), (60, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (22, 1), (44, 1), (50, 1), (52, 1)] }, { coefficient := 1, powers := [(0, 1), (28, 1), (40, 1), (50, 2)] }, { coefficient := 2, powers := [(0, 1), (28, 1), (40, 1), (50, 1), (54, 1)] }, { coefficient := 1, powers := [(0, 1), (28, 1), (40, 1), (54, 2)] }, { coefficient := 1, powers := [(0, 1), (31, 1), (37, 1), (50, 1), (54, 1)] }, { coefficient := 1, powers := [(0, 1), (31, 1), (37, 1), (54, 2)] }],
  [{ coefficient := -2, powers := [(0, 1), (22, 1), (24, 1), (44, 1), (50, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (17, 1), (44, 1), (46, 1), (51, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (23, 1), (45, 1), (50, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (12, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (16, 1), (51, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (12, 1), (28, 1), (44, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (16, 1), (18, 1), (31, 1), (37, 1), (44, 1), (50, 1), (60, 1), (62, 1)] }, { coefficient := 1, powers := [(0, 1), (16, 1), (21, 1), (37, 1), (50, 1), (57, 1), (60, 1)] }, { coefficient := -1, powers := [(0, 1), (16, 1), (31, 1), (37, 1), (45, 1), (50, 1), (60, 1), (62, 1)] }, { coefficient := 1, powers := [(18, 1), (44, 1), (60, 1), (62, 1)] }, { coefficient := -1, powers := [(45, 1), (60, 1), (62, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (16, 1), (22, 1), (23, 1), (44, 1), (50, 1), (60, 1)] }, { coefficient := -1, powers := [(0, 1), (16, 1), (22, 1), (39, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (40, 1), (50, 1), (51, 1)] }, { coefficient := -1, powers := [(0, 1), (40, 1), (51, 1), (54, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (45, 1), (50, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (22, 1), (55, 1)] }, { coefficient := 1, powers := [(0, 1), (28, 1), (46, 1)] }, { coefficient := -1, powers := [(0, 1), (34, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(0, 2), (28, 1), (40, 1), (50, 1)] }, { coefficient := 1, powers := [(0, 2), (28, 1), (40, 1), (54, 1)] }, { coefficient := -1, powers := [(0, 1), (28, 1), (40, 1)] }, { coefficient := -1, powers := [(0, 1), (31, 1), (37, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (16, 1), (37, 1), (48, 1), (57, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (12, 1), (55, 1)] }, { coefficient := 1, powers := [(0, 1), (16, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (12, 1), (39, 1), (42, 1)] }, { coefficient := -1, powers := [(0, 1), (12, 1), (42, 1), (44, 1)] }, { coefficient := 1, powers := [(0, 1), (16, 1), (44, 1), (48, 1)] }],
  [{ coefficient := -1, powers := [(0, 2), (16, 1), (40, 1), (50, 1)] }, { coefficient := -1, powers := [(0, 2), (16, 1), (40, 1), (54, 1)] }, { coefficient := 1, powers := [(0, 1), (12, 1), (42, 1), (45, 1)] }, { coefficient := -1, powers := [(0, 1), (16, 1), (23, 1), (40, 1), (50, 1)] }, { coefficient := -1, powers := [(0, 1), (16, 1), (23, 1), (40, 1), (54, 1)] }, { coefficient := -1, powers := [(0, 1), (16, 1), (45, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (12, 1), (22, 1), (51, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (16, 1), (18, 1), (31, 1), (37, 1), (50, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 1), (16, 1), (22, 1), (51, 1)] }, { coefficient := -1, powers := [(18, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (16, 1), (37, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (21, 1), (44, 1), (46, 1), (51, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (22, 1), (50, 1), (52, 1)] }, { coefficient := 1, powers := [(0, 1), (27, 1), (45, 1), (50, 1), (52, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (16, 1), (22, 1), (44, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (6, 1), (50, 1), (52, 1), (57, 1)] }, { coefficient := -1, powers := [(0, 1), (52, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (3, 1), (44, 1), (46, 1), (57, 1)] }, { coefficient := -1, powers := [(0, 1), (46, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (28, 1), (54, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (6, 1), (22, 1), (50, 1), (57, 1)] }, { coefficient := -1, powers := [(0, 1), (22, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(0, 2), (40, 1), (44, 1), (50, 1), (61, 1)] }, { coefficient := 1, powers := [(0, 2), (40, 1), (44, 1), (54, 1), (61, 1)] }, { coefficient := 1, powers := [(0, 1), (23, 1), (40, 1), (44, 1), (50, 1), (61, 1)] }, { coefficient := 1, powers := [(0, 1), (23, 1), (40, 1), (44, 1), (54, 1), (61, 1)] }, { coefficient := 1, powers := [(0, 1), (23, 1), (40, 1), (50, 1)] }, { coefficient := 1, powers := [(0, 1), (23, 1), (40, 1), (54, 1)] }, { coefficient := 1, powers := [(0, 1), (40, 1), (50, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (12, 1), (44, 1), (46, 1)] }, { coefficient := 1, powers := [(0, 1), (16, 1), (40, 1), (50, 1)] }, { coefficient := 1, powers := [(0, 1), (16, 1), (40, 1), (54, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (12, 1), (50, 1), (55, 1)] }, { coefficient := -1, powers := [(0, 1), (16, 1), (50, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (16, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (16, 1), (31, 1), (37, 1), (50, 1), (62, 1)] }, { coefficient := 1, powers := [(62, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (12, 1), (44, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (8, 1), (34, 1), (40, 1), (50, 1)] }, { coefficient := -1, powers := [(0, 1), (8, 1), (34, 1), (40, 1), (54, 1)] }, { coefficient := -2, powers := [(0, 1), (16, 1), (22, 1), (50, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (16, 1), (28, 1), (40, 1), (50, 1)] }, { coefficient := -1, powers := [(0, 1), (16, 1), (28, 1), (40, 1), (54, 1)] }, { coefficient := -1, powers := [(0, 1), (16, 1), (31, 1), (37, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (12, 1), (28, 1), (44, 1), (46, 1)] }, { coefficient := -1, powers := [(0, 1), (16, 1), (18, 1), (31, 1), (37, 1), (44, 1), (48, 1), (50, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 1), (16, 1), (21, 1), (37, 1), (48, 1), (50, 1), (57, 1)] }, { coefficient := -2, powers := [(0, 1), (16, 1), (22, 1), (23, 1), (44, 1), (50, 1), (52, 1)] }, { coefficient := 1, powers := [(0, 1), (16, 1), (22, 1), (39, 1), (52, 1)] }, { coefficient := 1, powers := [(0, 1), (16, 1), (31, 1), (37, 1), (45, 1), (48, 1), (50, 1), (62, 1)] }, { coefficient := -1, powers := [(18, 1), (44, 1), (48, 1), (62, 1)] }, { coefficient := 1, powers := [(45, 1), (48, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(0, 2), (39, 1), (40, 1), (44, 1), (50, 1), (55, 1), (61, 1)] }, { coefficient := -1, powers := [(0, 2), (39, 1), (40, 1), (44, 1), (54, 1), (55, 1), (61, 1)] }, { coefficient := -1, powers := [(0, 1), (3, 1), (44, 1), (46, 1), (52, 1), (57, 1)] }, { coefficient := -1, powers := [(0, 1), (6, 1), (46, 1), (50, 1), (52, 1), (57, 1)] }, { coefficient := -1, powers := [(0, 1), (23, 1), (39, 1), (40, 1), (44, 1), (50, 1), (55, 1), (61, 1)] }, { coefficient := -1, powers := [(0, 1), (23, 1), (39, 1), (40, 1), (44, 1), (54, 1), (55, 1), (61, 1)] }, { coefficient := -1, powers := [(0, 1), (23, 1), (39, 1), (40, 1), (50, 1), (55, 1)] }, { coefficient := -1, powers := [(0, 1), (23, 1), (39, 1), (40, 1), (54, 1), (55, 1)] }, { coefficient := -1, powers := [(0, 1), (37, 1), (54, 1), (58, 1)] }, { coefficient := -1, powers := [(0, 1), (39, 1), (40, 1), (50, 1), (55, 1), (61, 1)] }, { coefficient := 1, powers := [(0, 1), (40, 1), (42, 1), (50, 1), (51, 1)] }, { coefficient := 1, powers := [(0, 1), (40, 1), (42, 1), (51, 1), (54, 1)] }, { coefficient := -2, powers := [(0, 1), (45, 1), (48, 1), (50, 1), (55, 1)] }, { coefficient := 1, powers := [(0, 1), (46, 1), (52, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(0, 2), (8, 1), (34, 1), (40, 1), (44, 1), (50, 1)] }, { coefficient := -1, powers := [(0, 2), (8, 1), (34, 1), (40, 1), (44, 1), (54, 1)] }, { coefficient := -1, powers := [(0, 2), (16, 1), (28, 1), (40, 1), (44, 1), (50, 1)] }, { coefficient := -1, powers := [(0, 2), (16, 1), (28, 1), (40, 1), (44, 1), (54, 1)] }, { coefficient := -1, powers := [(0, 1), (8, 1), (23, 1), (34, 1), (40, 1), (44, 1), (50, 1)] }, { coefficient := -1, powers := [(0, 1), (8, 1), (23, 1), (34, 1), (40, 1), (44, 1), (54, 1)] }, { coefficient := -1, powers := [(0, 1), (8, 1), (34, 1), (40, 1), (50, 1)] }, { coefficient := -1, powers := [(0, 1), (16, 1), (23, 1), (28, 1), (40, 1), (44, 1), (50, 1)] }, { coefficient := -1, powers := [(0, 1), (16, 1), (23, 1), (28, 1), (40, 1), (44, 1), (54, 1)] }, { coefficient := -1, powers := [(0, 1), (16, 1), (28, 1), (40, 1), (50, 1)] }],
  [{ coefficient := -1, powers := [(0, 2), (16, 1), (31, 1), (37, 1), (50, 1), (54, 1)] }, { coefficient := -1, powers := [(0, 1), (16, 1), (31, 1), (37, 1), (50, 1)] }, { coefficient := -1, powers := [(0, 1), (54, 1)] }, { coefficient := -1, powers := [] }]
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
    ¬ ∀ index : Fin 46,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component14.SelectedLeafB6_3.selectedHasNoCommonZero

end Krenn.Component14.SelectedLeafB6_3
