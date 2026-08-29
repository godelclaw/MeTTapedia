import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component39.SelectedLeafB4_0_2

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "b105e2b2bb3008571defcf744a111c7f8cecce5d0062d3f7229d3382fdc38447"
def certificateSHA256 : String := "39d4ea2de9bc726c3d1253c9f262b8c9921cf13b8d1007a5f00bd977c98558cb"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 45 → Fin 670 := ![
  180,
  181,
  183,
  184,
  187,
  188,
  191,
  192,
  193,
  250,
  251,
  276,
  277,
  300,
  301,
  302,
  313,
  316,
  397,
  410,
  415,
  419,
  425,
  427,
  430,
  434,
  440,
  451,
  460,
  470,
  482,
  555,
  566,
  580,
  618,
  620,
  623,
  625,
  637,
  660,
  661,
  663,
  665,
  666,
  669
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 45 → SparsePoly (Fin 63) := ![
  [{ coefficient := 1, powers := [(12, 1), (23, 1)] }, { coefficient := 1, powers := [(16, 1), (18, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (24, 1)] }, { coefficient := 1, powers := [(16, 1), (18, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (42, 1)] }, { coefficient := 1, powers := [(17, 1), (18, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (45, 1)] }, { coefficient := 1, powers := [(17, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (18, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (42, 1)] }, { coefficient := 1, powers := [(17, 1), (18, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (54, 1)] }, { coefficient := 1, powers := [(28, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (42, 1)] }, { coefficient := 1, powers := [(26, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (53, 1)] }, { coefficient := 1, powers := [(28, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (23, 1), (44, 1)] }, { coefficient := 1, powers := [(16, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (23, 1), (45, 1)] }, { coefficient := 1, powers := [(17, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (23, 1), (42, 1)] }, { coefficient := 1, powers := [(17, 1), (18, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (23, 1), (47, 1)] }, { coefficient := 1, powers := [(17, 1), (19, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1)] }, { coefficient := 1, powers := [(18, 1), (42, 1)] }, { coefficient := 1, powers := [(23, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (42, 1)] }, { coefficient := 1, powers := [(23, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (49, 1)] }, { coefficient := 1, powers := [(18, 1), (49, 1)] }, { coefficient := 1, powers := [(23, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (44, 1)] }, { coefficient := 1, powers := [(12, 1), (56, 1)] }, { coefficient := 1, powers := [(16, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (45, 1)] }, { coefficient := 1, powers := [(17, 1), (39, 1)] }, { coefficient := 1, powers := [(17, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (23, 1), (45, 1)] }, { coefficient := 1, powers := [(17, 1), (23, 1), (39, 1)] }, { coefficient := 1, powers := [(17, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1)] }, { coefficient := 1, powers := [(23, 1), (39, 1), (42, 1)] }, { coefficient := 1, powers := [(23, 1), (45, 1)] }, { coefficient := 1, powers := [(42, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (42, 1)] }, { coefficient := 1, powers := [(16, 1), (26, 1), (42, 1)] }, { coefficient := 1, powers := [(16, 1), (34, 1), (35, 1)] }, { coefficient := 1, powers := [(17, 1), (21, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (47, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1)] }, { coefficient := 1, powers := [(16, 1), (26, 1), (47, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1)] }, { coefficient := 1, powers := [(12, 1), (28, 1)] }, { coefficient := 1, powers := [(16, 1), (21, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (34, 1)] }, { coefficient := 1, powers := [(21, 1), (42, 1)] }, { coefficient := 1, powers := [(26, 1), (42, 1)] }, { coefficient := 1, powers := [(34, 1), (35, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (60, 1)] }, { coefficient := 1, powers := [(12, 1), (47, 1)] }, { coefficient := 1, powers := [(17, 1), (19, 1), (52, 1)] }, { coefficient := 1, powers := [(17, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (60, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (45, 1)] }, { coefficient := 1, powers := [(12, 1), (57, 1)] }, { coefficient := 1, powers := [(17, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (54, 1)] }, { coefficient := 1, powers := [(28, 1), (40, 1)] }, { coefficient := 1, powers := [(28, 1), (46, 1), (49, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1), (52, 1)] }, { coefficient := 1, powers := [(3, 1), (60, 1)] }, { coefficient := 1, powers := [(18, 1), (42, 1), (52, 1)] }, { coefficient := 1, powers := [(42, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1), (49, 1)] }, { coefficient := 1, powers := [(6, 1), (60, 1)] }, { coefficient := 1, powers := [(23, 1), (45, 1), (49, 1)] }, { coefficient := 1, powers := [(42, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1), (52, 1)] }, { coefficient := 1, powers := [(19, 1), (42, 1), (52, 1)] }, { coefficient := 1, powers := [(40, 1), (42, 1)] }, { coefficient := 1, powers := [(47, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (35, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1)] }, { coefficient := 1, powers := [(16, 1), (21, 1)] }, { coefficient := 1, powers := [(16, 1), (26, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (19, 1), (56, 1)] }, { coefficient := 1, powers := [(12, 1), (46, 1)] }, { coefficient := 1, powers := [(16, 1), (19, 1), (52, 1)] }, { coefficient := 1, powers := [(16, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (42, 1), (53, 1)] }, { coefficient := 1, powers := [(22, 1), (57, 1)] }, { coefficient := 1, powers := [(28, 1), (47, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1)] }, { coefficient := 1, powers := [(6, 1), (59, 1)] }, { coefficient := 1, powers := [(23, 1), (39, 1)] }, { coefficient := 1, powers := [(23, 1), (44, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (42, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (21, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1), (42, 1)] }, { coefficient := 1, powers := [(12, 1), (21, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1), (28, 1), (42, 1)] }, { coefficient := 1, powers := [(17, 1), (21, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (46, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1), (46, 1)] }, { coefficient := 1, powers := [(12, 1), (28, 1), (46, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1), (54, 1)] }, { coefficient := 1, powers := [(16, 1), (28, 1), (40, 1)] }, { coefficient := 1, powers := [(16, 1), (31, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (47, 1), (53, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (53, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1), (57, 1)] }, { coefficient := 1, powers := [(16, 1), (28, 1), (47, 1)] }, { coefficient := 1, powers := [(16, 1), (34, 1), (37, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (28, 1), (60, 1)] }, { coefficient := 1, powers := [(3, 1), (31, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (34, 1), (54, 1)] }, { coefficient := 1, powers := [(21, 1), (42, 1), (54, 1)] }, { coefficient := 1, powers := [(21, 1), (49, 1), (57, 1)] }, { coefficient := 1, powers := [(28, 1), (42, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (42, 1), (54, 1)] }, { coefficient := 1, powers := [(22, 1), (49, 1), (57, 1)] }, { coefficient := 1, powers := [(28, 1), (40, 1), (42, 1)] }, { coefficient := 1, powers := [(28, 1), (47, 1), (49, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1), (42, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (37, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (47, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (28, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (22, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1), (47, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (40, 1)] }, { coefficient := 1, powers := [(12, 1), (22, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1), (28, 1), (47, 1)] }, { coefficient := 1, powers := [(12, 1), (34, 1), (37, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (54, 1)] }, { coefficient := 1, powers := [(17, 1), (28, 1), (40, 1)] }, { coefficient := 1, powers := [(17, 1), (31, 1), (37, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (61, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(39, 1)] }],
  [{ coefficient := 1, powers := [(40, 1)] }],
  [{ coefficient := 1, powers := [(57, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 45 → SparsePoly (Fin 63) := ![
  [{ coefficient := 2, powers := [(28, 1), (47, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [(21, 1), (45, 1), (46, 1)] }, { coefficient := -1, powers := [(22, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(28, 1), (46, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (28, 1), (46, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (28, 1), (42, 1), (46, 1), (52, 1), (61, 1)] }, { coefficient := 2, powers := [(0, 1), (28, 1), (45, 1), (46, 1), (52, 1)] }, { coefficient := -2, powers := [(6, 1), (28, 1), (47, 1), (49, 1), (59, 1), (61, 1)] }, { coefficient := 2, powers := [(19, 1), (28, 1), (42, 1), (49, 1), (56, 1), (61, 1)] }, { coefficient := 2, powers := [(19, 1), (28, 1), (45, 1), (49, 1), (56, 1)] }, { coefficient := 1, powers := [(21, 1), (45, 1), (46, 1), (54, 1)] }, { coefficient := 1, powers := [(22, 1), (42, 1), (54, 1), (61, 1)] }, { coefficient := -1, powers := [(22, 1), (45, 1), (49, 1), (53, 1)] }, { coefficient := 2, powers := [(22, 1), (45, 1), (54, 1)] }, { coefficient := 1, powers := [(26, 1), (42, 1), (46, 1), (54, 1), (61, 1)] }, { coefficient := 1, powers := [(28, 1), (42, 1), (46, 1), (49, 1), (61, 1)] }, { coefficient := 2, powers := [(28, 1), (45, 1), (46, 1), (49, 1)] }, { coefficient := -2, powers := [(28, 1), (47, 1), (49, 1), (56, 1)] }, { coefficient := -1, powers := [(28, 1), (47, 1), (49, 1), (61, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (28, 1), (46, 1), (52, 1)] }, { coefficient := 2, powers := [(19, 1), (28, 1), (49, 1), (56, 1)] }, { coefficient := -1, powers := [(22, 1), (49, 1), (53, 1)] }, { coefficient := 1, powers := [(22, 1), (54, 1)] }, { coefficient := 2, powers := [(28, 1), (46, 1), (49, 1)] }],
  [{ coefficient := -1, powers := [(16, 1), (42, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (49, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (42, 1)] }, { coefficient := -1, powers := [(17, 1), (49, 1)] }],
  [{ coefficient := 2, powers := [(28, 1), (47, 1)] }],
  [{ coefficient := 2, powers := [(28, 1), (46, 1)] }],
  [{ coefficient := -1, powers := [(28, 1), (46, 1), (52, 1)] }],
  [{ coefficient := -2, powers := [(6, 1), (28, 1), (52, 1), (59, 1)] }, { coefficient := 2, powers := [(28, 1), (49, 1), (56, 1)] }, { coefficient := -1, powers := [(28, 1), (52, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (16, 1), (28, 1), (46, 1), (52, 1), (61, 1)] }, { coefficient := -2, powers := [(16, 1), (19, 1), (28, 1), (49, 1), (56, 1), (61, 1)] }, { coefficient := -1, powers := [(16, 1), (22, 1), (54, 1), (61, 1)] }, { coefficient := -1, powers := [(16, 1), (26, 1), (46, 1), (54, 1), (61, 1)] }, { coefficient := -1, powers := [(16, 1), (28, 1), (46, 1), (49, 1), (61, 1)] }, { coefficient := 1, powers := [(16, 1), (28, 1), (46, 1), (52, 1)] }],
  [{ coefficient := 2, powers := [(6, 1), (16, 1), (28, 1), (52, 1), (59, 1)] }, { coefficient := -2, powers := [(12, 1), (28, 1), (56, 1)] }, { coefficient := 1, powers := [(16, 1), (28, 1), (52, 1)] }],
  [{ coefficient := 2, powers := [(6, 1), (16, 1), (28, 1), (47, 1), (59, 1), (61, 1)] }, { coefficient := 1, powers := [(16, 1), (28, 1), (47, 1), (61, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (28, 1), (47, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (18, 1), (28, 1), (46, 1), (52, 1)] }, { coefficient := -2, powers := [(18, 1), (19, 1), (28, 1), (49, 1), (56, 1)] }, { coefficient := 1, powers := [(18, 1), (22, 1), (49, 1), (53, 1)] }, { coefficient := -1, powers := [(18, 1), (22, 1), (54, 1)] }, { coefficient := -2, powers := [(18, 1), (28, 1), (46, 1), (49, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (28, 1), (46, 1), (52, 1)] }, { coefficient := -2, powers := [(19, 1), (28, 1), (49, 1), (56, 1)] }, { coefficient := -1, powers := [(21, 1), (46, 1), (54, 1)] }, { coefficient := 1, powers := [(22, 1), (49, 1), (53, 1)] }, { coefficient := -2, powers := [(22, 1), (54, 1)] }, { coefficient := -2, powers := [(28, 1), (46, 1), (49, 1)] }],
  [{ coefficient := 2, powers := [(5, 1), (28, 1), (49, 1), (59, 1)] }, { coefficient := -2, powers := [(12, 1), (28, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(46, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(49, 1), (53, 1)] }, { coefficient := 1, powers := [(54, 1)] }],
  [{ coefficient := 1, powers := [(47, 1)] }],
  [{ coefficient := -1, powers := [(16, 1), (46, 1), (54, 1)] }],
  [{ coefficient := 2, powers := [(6, 1), (28, 1), (59, 1)] }, { coefficient := 1, powers := [(28, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (46, 1)] }, { coefficient := 1, powers := [(22, 1)] }],
  [{ coefficient := 1, powers := [(17, 1)] }],
  [{ coefficient := -1, powers := [(16, 1), (28, 1), (46, 1)] }],
  [{ coefficient := -2, powers := [(5, 1), (28, 1), (59, 1)] }],
  [{ coefficient := -2, powers := [(6, 1), (16, 1), (28, 1), (59, 1)] }, { coefficient := -3, powers := [(16, 1), (28, 1)] }],
  [{ coefficient := 1, powers := [(42, 1), (46, 1), (54, 1)] }, { coefficient := -1, powers := [(47, 1), (54, 1)] }],
  [{ coefficient := 2, powers := [(28, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(12, 1)] }],
  [{ coefficient := -2, powers := [(12, 1), (28, 1), (47, 1)] }],
  [{ coefficient := -1, powers := [(46, 1)] }],
  [{ coefficient := 1, powers := [(42, 1)] }],
  [{ coefficient := 1, powers := [(49, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (46, 1)] }],
  [{ coefficient := -1, powers := [(16, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := 2, powers := [(0, 1), (16, 1), (28, 1), (42, 1), (46, 1), (52, 1)] }, { coefficient := -2, powers := [(6, 1), (16, 1), (28, 1), (47, 1), (49, 1), (59, 1)] }, { coefficient := 2, powers := [(16, 1), (19, 1), (28, 1), (42, 1), (49, 1), (56, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1), (42, 1), (54, 1)] }, { coefficient := 1, powers := [(16, 1), (26, 1), (42, 1), (46, 1), (54, 1)] }, { coefficient := 1, powers := [(16, 1), (28, 1), (42, 1), (46, 1), (49, 1)] }, { coefficient := -1, powers := [(16, 1), (28, 1), (47, 1), (49, 1)] }],
  [{ coefficient := -1, powers := [(35, 1), (42, 1), (46, 1), (54, 1), (59, 1)] }, { coefficient := 1, powers := [(35, 1), (47, 1), (54, 1), (59, 1)] }, { coefficient := 1, powers := [(37, 1), (60, 1)] }, { coefficient := -2, powers := [(42, 1), (46, 1), (54, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (17, 1), (18, 1), (28, 1), (46, 1), (52, 1)] }, { coefficient := 2, powers := [(0, 1), (17, 1), (23, 1), (28, 1), (46, 1), (52, 1)] }, { coefficient := -2, powers := [(5, 1), (23, 1), (28, 1), (42, 1), (49, 1), (59, 1)] }, { coefficient := 2, powers := [(12, 1), (23, 1), (28, 1), (42, 1), (46, 1)] }, { coefficient := 2, powers := [(12, 1), (23, 1), (28, 1), (47, 1)] }, { coefficient := 2, powers := [(17, 1), (18, 1), (19, 1), (28, 1), (49, 1), (56, 1)] }, { coefficient := -1, powers := [(17, 1), (18, 1), (22, 1), (49, 1), (53, 1)] }, { coefficient := 1, powers := [(17, 1), (18, 1), (22, 1), (54, 1)] }, { coefficient := 2, powers := [(17, 1), (18, 1), (28, 1), (46, 1), (49, 1)] }, { coefficient := 2, powers := [(17, 1), (19, 1), (23, 1), (28, 1), (49, 1), (56, 1)] }, { coefficient := 1, powers := [(17, 1), (21, 1), (23, 1), (46, 1), (54, 1)] }, { coefficient := -1, powers := [(17, 1), (22, 1), (23, 1), (49, 1), (53, 1)] }, { coefficient := 2, powers := [(17, 1), (22, 1), (23, 1), (54, 1)] }, { coefficient := 2, powers := [(17, 1), (23, 1), (28, 1), (46, 1), (49, 1)] }],
  [{ coefficient := 2, powers := [(6, 1), (16, 1), (28, 1), (42, 1), (59, 1)] }, { coefficient := -2, powers := [(6, 1), (17, 1), (28, 1), (59, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1)] }, { coefficient := 1, powers := [(16, 1), (28, 1), (42, 1)] }, { coefficient := -1, powers := [(17, 1), (28, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (40, 1)] }, { coefficient := -1, powers := [(3, 1), (16, 1), (31, 1), (46, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1)] }, { coefficient := -1, powers := [(12, 1), (22, 1)] }, { coefficient := -1, powers := [(16, 1), (21, 1), (46, 1), (49, 1)] }]
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
    ¬ ∀ index : Fin 45,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component39.SelectedLeafB4_0_2.selectedHasNoCommonZero

end Krenn.Component39.SelectedLeafB4_0_2
