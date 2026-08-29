import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component14.SelectedLeafB6_2_2

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "e062b63dc0a47eb31bc5e3a1ab0260346f115537a5985e88053d09ca57c8f436"
def certificateSHA256 : String := "39dc2d21a6d998802a6984bbeef336d85de0eeda576a366c2f6d89d1578d9326"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 39 → Fin 643 := ![
  6,
  9,
  11,
  13,
  16,
  19,
  23,
  90,
  128,
  132,
  133,
  162,
  164,
  179,
  191,
  192,
  194,
  195,
  198,
  313,
  348,
  349,
  350,
  351,
  395,
  406,
  457,
  458,
  460,
  524,
  555,
  595,
  633,
  635,
  636,
  638,
  639,
  641,
  642
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 39 → SparsePoly (Fin 63) := ![
  [{ coefficient := 1, powers := [(5, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (23, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(15, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (21, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (27, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (42, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (48, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (46, 1)] }, { coefficient := 1, powers := [(11, 1), (25, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (52, 1)] }, { coefficient := 1, powers := [(15, 1), (19, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (44, 1)] }, { coefficient := 1, powers := [(12, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (50, 1)] }, { coefficient := 1, powers := [(22, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (51, 1)] }, { coefficient := 1, powers := [(28, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(28, 1), (39, 1)] }, { coefficient := 1, powers := [(28, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(39, 1), (42, 1)] }, { coefficient := 1, powers := [(42, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(44, 1), (48, 1)] }, { coefficient := 1, powers := [(48, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (23, 1), (39, 1)] }, { coefficient := 1, powers := [(16, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (46, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (52, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1)] }, { coefficient := 1, powers := [(12, 1), (28, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (58, 1)] }, { coefficient := 1, powers := [(12, 1), (46, 1)] }, { coefficient := 1, powers := [(16, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (58, 1)] }, { coefficient := 1, powers := [(12, 1), (55, 1)] }, { coefficient := 1, powers := [(16, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (28, 1), (57, 1)] }, { coefficient := 1, powers := [(21, 1), (51, 1)] }, { coefficient := 1, powers := [(28, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (22, 1), (57, 1)] }, { coefficient := 1, powers := [(22, 1)] }, { coefficient := 1, powers := [(27, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (34, 1)] }, { coefficient := 1, powers := [(21, 1), (42, 1)] }, { coefficient := 1, powers := [(27, 1), (42, 1)] }, { coefficient := 1, powers := [(34, 1), (35, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (31, 1)] }, { coefficient := 1, powers := [(21, 1), (48, 1)] }, { coefficient := 1, powers := [(27, 1), (48, 1)] }, { coefficient := 1, powers := [(31, 1), (35, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (52, 1)] }, { coefficient := 1, powers := [(28, 1), (40, 1)] }, { coefficient := 1, powers := [(28, 1), (45, 1), (48, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (42, 1), (51, 1)] }, { coefficient := 1, powers := [(22, 1), (55, 1)] }, { coefficient := 1, powers := [(28, 1), (46, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1)] }, { coefficient := 1, powers := [(6, 1), (57, 1)] }, { coefficient := 1, powers := [(23, 1), (39, 1)] }, { coefficient := 1, powers := [(23, 1), (44, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (35, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (42, 1), (48, 1)] }, { coefficient := 1, powers := [(12, 1), (27, 1), (42, 1)] }, { coefficient := 1, powers := [(12, 1), (34, 1), (35, 1)] }, { coefficient := 1, powers := [(16, 1), (21, 1), (48, 1)] }, { coefficient := 1, powers := [(16, 1), (31, 1), (35, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (37, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (40, 1), (55, 1)] }, { coefficient := 1, powers := [(2, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(5, 1), (28, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (52, 1)] }, { coefficient := 1, powers := [(8, 1), (22, 1), (58, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1), (46, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (40, 1)] }, { coefficient := 1, powers := [(12, 1), (22, 1), (55, 1)] }, { coefficient := 1, powers := [(12, 1), (28, 1), (46, 1)] }, { coefficient := 1, powers := [(12, 1), (34, 1), (37, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1), (52, 1)] }, { coefficient := 1, powers := [(16, 1), (28, 1), (40, 1)] }, { coefficient := 1, powers := [(16, 1), (31, 1), (37, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1), (60, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(39, 1), (61, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(40, 1)] }],
  [{ coefficient := 1, powers := [(54, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(55, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 39 → SparsePoly (Fin 63) := ![
  [{ coefficient := 1, powers := [(0, 1), (6, 1), (34, 1), (44, 1), (52, 1)] }, { coefficient := -1, powers := [(6, 2), (34, 1), (50, 1), (52, 1), (57, 1), (62, 1)] }, { coefficient := 1, powers := [(6, 1), (23, 1), (34, 1), (39, 1), (52, 1)] }, { coefficient := 1, powers := [(6, 1), (23, 1), (34, 1), (44, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (3, 1), (31, 1), (44, 1), (46, 1)] }, { coefficient := -1, powers := [(3, 1), (6, 1), (31, 1), (44, 1), (46, 1), (57, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (12, 1), (25, 1), (28, 1), (44, 1), (60, 1)] }, { coefficient := 1, powers := [(6, 1), (12, 1), (25, 1), (28, 1), (44, 1), (57, 1), (60, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(28, 1), (39, 1), (46, 1)] }, { coefficient := 1, powers := [(28, 1), (44, 1), (46, 1)] }, { coefficient := -1, powers := [(34, 1), (37, 1), (39, 1)] }, { coefficient := -1, powers := [(34, 1), (37, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (37, 1), (44, 1), (57, 1), (62, 1)] }, { coefficient := 1, powers := [(21, 1), (37, 1), (54, 1), (57, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (16, 1), (19, 1), (22, 1), (39, 1), (44, 1), (60, 1), (61, 1)] }, { coefficient := 1, powers := [(6, 1), (16, 1), (19, 1), (22, 1), (39, 1), (44, 1), (57, 1), (60, 1), (61, 1), (62, 1)] }, { coefficient := -1, powers := [(16, 1), (19, 1), (22, 1), (23, 1), (39, 2), (60, 1), (61, 1)] }, { coefficient := -1, powers := [(16, 1), (19, 1), (22, 1), (23, 1), (39, 1), (44, 1), (60, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (37, 1), (44, 1), (57, 1), (62, 1)] }, { coefficient := 1, powers := [(27, 1), (37, 1), (54, 1), (57, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (44, 1), (46, 1), (51, 1), (62, 1)] }, { coefficient := 1, powers := [(6, 1), (44, 1), (46, 1), (51, 1), (57, 1), (62, 2)] }],
  [{ coefficient := 1, powers := [(0, 1), (23, 1), (44, 1), (45, 1), (52, 1)] }, { coefficient := -1, powers := [(6, 1), (23, 1), (45, 1), (50, 1), (52, 1), (57, 1), (62, 1)] }, { coefficient := 1, powers := [(23, 2), (39, 1), (45, 1), (52, 1)] }, { coefficient := 1, powers := [(23, 2), (44, 1), (45, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (12, 1), (51, 1)] }, { coefficient := -1, powers := [(6, 1), (12, 1), (51, 1), (57, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (16, 1), (44, 1), (51, 1), (61, 1)] }, { coefficient := 1, powers := [(6, 1), (16, 1), (44, 1), (51, 1), (57, 1), (61, 1), (62, 1)] }, { coefficient := -1, powers := [(16, 1), (23, 1), (39, 1), (51, 1), (61, 1)] }, { coefficient := -1, powers := [(16, 1), (23, 1), (44, 1), (51, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (12, 1), (28, 1), (44, 1), (60, 1)] }, { coefficient := -1, powers := [(6, 1), (12, 1), (28, 1), (44, 1), (57, 1), (60, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (16, 1), (22, 1), (39, 1), (44, 1), (60, 1), (61, 1)] }, { coefficient := -1, powers := [(6, 1), (16, 1), (22, 1), (39, 1), (44, 1), (57, 1), (60, 1), (61, 1), (62, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1), (23, 1), (39, 2), (60, 1), (61, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1), (23, 1), (39, 1), (44, 1), (60, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (34, 1), (37, 1), (57, 1), (62, 1)] }, { coefficient := 1, powers := [(6, 1), (28, 1), (46, 1), (57, 1), (62, 1)] }, { coefficient := -1, powers := [(6, 1), (34, 1), (37, 1), (57, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (16, 1), (52, 1), (57, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (12, 1), (39, 1), (42, 1)] }, { coefficient := 1, powers := [(0, 1), (12, 1), (42, 1), (44, 1)] }, { coefficient := -1, powers := [(0, 1), (16, 1), (44, 2), (48, 1), (61, 1)] }, { coefficient := -1, powers := [(6, 1), (12, 1), (39, 1), (42, 1), (57, 1), (62, 1)] }, { coefficient := -1, powers := [(6, 1), (12, 1), (42, 1), (44, 1), (57, 1), (62, 1)] }, { coefficient := 1, powers := [(6, 1), (16, 1), (44, 2), (48, 1), (57, 1), (61, 1), (62, 1)] }, { coefficient := -1, powers := [(16, 1), (23, 1), (39, 1), (44, 1), (48, 1), (61, 1)] }, { coefficient := -1, powers := [(16, 1), (23, 1), (44, 2), (48, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (12, 1), (42, 1), (45, 1)] }, { coefficient := 1, powers := [(0, 1), (16, 1), (44, 1), (45, 1), (48, 1), (61, 1)] }, { coefficient := 1, powers := [(6, 1), (12, 1), (42, 1), (45, 1), (57, 1), (62, 1)] }, { coefficient := -1, powers := [(6, 1), (16, 1), (44, 1), (45, 1), (48, 1), (57, 1), (61, 1), (62, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1), (39, 1), (45, 1), (48, 1), (61, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1), (44, 1), (45, 1), (48, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (12, 1), (22, 1), (51, 1)] }, { coefficient := 1, powers := [(6, 1), (12, 1), (22, 1), (51, 1), (57, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (16, 1), (22, 1), (44, 1), (51, 1), (61, 1)] }, { coefficient := -1, powers := [(6, 1), (16, 1), (22, 1), (44, 1), (51, 1), (57, 1), (61, 1), (62, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1), (23, 1), (39, 1), (51, 1), (61, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1), (23, 1), (44, 1), (51, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (27, 1), (44, 1), (45, 1), (52, 1)] }, { coefficient := 1, powers := [(6, 1), (27, 1), (45, 1), (50, 1), (52, 1), (57, 1), (62, 1)] }, { coefficient := -1, powers := [(23, 1), (27, 1), (39, 1), (45, 1), (52, 1)] }, { coefficient := -1, powers := [(23, 1), (27, 1), (44, 1), (45, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (6, 1), (44, 1), (52, 1), (57, 1)] }, { coefficient := -1, powers := [(0, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(6, 2), (50, 1), (52, 1), (57, 2), (62, 1)] }, { coefficient := -1, powers := [(6, 1), (23, 1), (39, 1), (52, 1), (57, 1)] }, { coefficient := -1, powers := [(6, 1), (23, 1), (44, 1), (52, 1), (57, 1)] }, { coefficient := -1, powers := [(6, 1), (52, 1), (54, 1), (57, 1), (62, 1)] }, { coefficient := -1, powers := [(23, 1), (39, 1), (52, 1)] }, { coefficient := -1, powers := [(23, 1), (44, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (3, 1), (44, 1), (46, 1), (57, 1)] }, { coefficient := -1, powers := [(0, 1), (44, 1), (46, 1)] }, { coefficient := 1, powers := [(3, 1), (6, 1), (44, 1), (46, 1), (57, 2), (62, 1)] }, { coefficient := -1, powers := [(6, 1), (46, 1), (54, 1), (57, 1), (62, 1)] }, { coefficient := -1, powers := [(23, 1), (39, 1), (46, 1)] }, { coefficient := -1, powers := [(23, 1), (44, 1), (46, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (28, 1), (44, 1)] }, { coefficient := -1, powers := [(6, 1), (28, 1), (54, 1), (57, 1), (62, 1)] }, { coefficient := -1, powers := [(23, 1), (28, 1), (39, 1)] }, { coefficient := -1, powers := [(23, 1), (28, 1), (44, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (22, 1), (44, 1)] }, { coefficient := -1, powers := [(6, 1), (22, 1), (54, 1), (57, 1), (62, 1)] }, { coefficient := -1, powers := [(22, 1), (23, 1), (39, 1)] }, { coefficient := -1, powers := [(22, 1), (23, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (12, 1), (44, 1), (46, 1)] }, { coefficient := -1, powers := [(6, 1), (12, 1), (44, 1), (46, 1), (57, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (16, 1), (44, 1), (52, 1)] }, { coefficient := -1, powers := [(6, 1), (16, 1), (50, 1), (52, 1), (57, 1), (62, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1), (39, 1), (52, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1), (44, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (37, 1), (44, 1), (57, 1), (62, 1)] }, { coefficient := -1, powers := [(12, 1), (37, 1), (54, 1), (57, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(16, 1), (37, 1), (44, 1), (57, 1), (62, 1)] }, { coefficient := -1, powers := [(16, 1), (37, 1), (54, 1), (57, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (16, 1), (39, 1), (44, 1), (61, 1)] }, { coefficient := 1, powers := [(6, 1), (16, 1), (39, 1), (44, 1), (57, 1), (61, 1), (62, 1)] }, { coefficient := -1, powers := [(16, 1), (23, 1), (39, 2), (61, 1)] }, { coefficient := -1, powers := [(16, 1), (23, 1), (39, 1), (44, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (12, 1), (44, 1)] }, { coefficient := 1, powers := [(6, 1), (12, 1), (44, 1), (57, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(37, 1), (44, 1), (57, 1), (62, 1)] }, { coefficient := 1, powers := [(37, 1), (54, 1), (57, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1)] }, { coefficient := 1, powers := [(6, 1), (54, 1), (57, 1), (62, 1)] }, { coefficient := 1, powers := [(23, 1), (39, 1)] }, { coefficient := 1, powers := [(23, 1), (44, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (12, 1), (28, 1), (44, 1), (46, 1)] }, { coefficient := -1, powers := [(0, 1), (16, 1), (22, 1), (39, 1), (44, 1), (52, 1), (61, 1)] }, { coefficient := 1, powers := [(6, 1), (12, 1), (28, 1), (44, 1), (46, 1), (57, 1), (62, 1)] }, { coefficient := 1, powers := [(6, 1), (16, 1), (22, 1), (39, 1), (44, 1), (52, 1), (57, 1), (61, 1), (62, 1)] }, { coefficient := -1, powers := [(16, 1), (22, 1), (23, 1), (39, 2), (52, 1), (61, 1)] }, { coefficient := -1, powers := [(16, 1), (22, 1), (23, 1), (39, 1), (44, 1), (52, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (3, 1), (44, 1), (46, 1), (52, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (6, 1), (44, 1), (46, 1), (52, 1), (57, 1)] }, { coefficient := -1, powers := [(0, 1), (37, 1), (44, 1), (58, 1)] }, { coefficient := -1, powers := [(0, 1), (40, 1), (44, 1), (55, 1)] }, { coefficient := 1, powers := [(0, 1), (44, 1), (46, 1), (52, 1)] }, { coefficient := -1, powers := [(3, 1), (6, 1), (44, 1), (46, 1), (52, 1), (57, 2), (62, 1)] }, { coefficient := -1, powers := [(6, 2), (46, 1), (50, 1), (52, 1), (57, 2), (62, 1)] }, { coefficient := 1, powers := [(6, 1), (23, 1), (39, 1), (46, 1), (52, 1), (57, 1)] }, { coefficient := 1, powers := [(6, 1), (23, 1), (44, 1), (46, 1), (52, 1), (57, 1)] }, { coefficient := -1, powers := [(6, 1), (37, 1), (54, 1), (57, 1), (58, 1), (62, 1)] }, { coefficient := -1, powers := [(6, 1), (40, 1), (54, 1), (55, 1), (57, 1), (62, 1)] }, { coefficient := 1, powers := [(6, 1), (46, 1), (52, 1), (54, 1), (57, 1), (62, 1)] }, { coefficient := -1, powers := [(23, 1), (37, 1), (39, 1), (58, 1)] }, { coefficient := -1, powers := [(23, 1), (37, 1), (44, 1), (58, 1)] }, { coefficient := -1, powers := [(23, 1), (39, 1), (40, 1), (55, 1)] }, { coefficient := 1, powers := [(23, 1), (39, 1), (46, 1), (52, 1)] }, { coefficient := -1, powers := [(23, 1), (40, 1), (44, 1), (55, 1)] }, { coefficient := 1, powers := [(23, 1), (44, 1), (46, 1), (52, 1)] }, { coefficient := -1, powers := [(35, 1), (37, 1), (44, 1), (57, 1), (58, 1), (62, 1)] }, { coefficient := -1, powers := [(35, 1), (37, 1), (54, 1), (57, 1), (58, 1), (62, 1)] }, { coefficient := -1, powers := [(37, 1), (42, 1), (44, 1), (48, 1), (57, 1), (62, 1)] }, { coefficient := -1, powers := [(37, 1), (42, 1), (48, 1), (54, 1), (57, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (16, 1), (31, 1), (37, 1), (44, 1)] }, { coefficient := -1, powers := [(6, 1), (16, 1), (31, 1), (37, 1), (44, 1), (57, 1), (62, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1), (31, 1), (37, 1), (39, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1), (31, 1), (37, 1), (44, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (8, 1), (34, 1), (44, 1)] }, { coefficient := 1, powers := [(0, 1), (16, 1), (28, 1), (39, 1), (44, 1), (61, 1)] }, { coefficient := -1, powers := [(6, 1), (8, 1), (34, 1), (54, 1), (57, 1), (62, 1)] }, { coefficient := -1, powers := [(6, 1), (16, 1), (28, 1), (39, 1), (44, 1), (57, 1), (61, 1), (62, 1)] }, { coefficient := -1, powers := [(8, 1), (23, 1), (34, 1), (39, 1)] }, { coefficient := -1, powers := [(8, 1), (23, 1), (34, 1), (44, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1), (28, 1), (39, 2), (61, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1), (28, 1), (39, 1), (44, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (12, 1), (21, 1), (44, 1), (46, 1), (51, 1)] }, { coefficient := -1, powers := [(6, 1), (12, 1), (21, 1), (44, 1), (46, 1), (51, 1), (57, 1), (62, 1)] }, { coefficient := 1, powers := [(6, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (5, 1), (31, 1), (44, 1)] }, { coefficient := 1, powers := [(0, 1), (12, 1), (22, 1), (44, 1)] }, { coefficient := -1, powers := [(5, 1), (6, 1), (31, 1), (54, 1), (57, 1), (62, 1)] }, { coefficient := -1, powers := [(5, 1), (23, 1), (31, 1), (39, 1)] }, { coefficient := -1, powers := [(5, 1), (23, 1), (31, 1), (44, 1)] }, { coefficient := -1, powers := [(6, 1), (12, 1), (22, 1), (44, 1), (57, 1), (62, 1)] }]
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
    ¬ ∀ index : Fin 39,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component14.SelectedLeafB6_2_2.selectedHasNoCommonZero

end Krenn.Component14.SelectedLeafB6_2_2
