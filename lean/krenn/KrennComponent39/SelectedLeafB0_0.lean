import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component39.SelectedLeafB0_0

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "b975f9bf9033ba1e6b005f2e700278a27bcaebd2be68aca6ed72e4808f3a8006"
def certificateSHA256 : String := "4cc96706b2d553398cba84633dee417b5ca78f6999eabd0a0aff28b9c8d4fc51"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 60 → Fin 667 := ![
  14,
  26,
  29,
  180,
  181,
  187,
  188,
  191,
  192,
  193,
  196,
  232,
  250,
  277,
  280,
  300,
  301,
  302,
  304,
  305,
  313,
  316,
  318,
  319,
  322,
  324,
  382,
  385,
  397,
  419,
  425,
  430,
  434,
  440,
  445,
  457,
  458,
  462,
  467,
  470,
  478,
  511,
  512,
  555,
  566,
  580,
  602,
  603,
  607,
  608,
  618,
  620,
  644,
  659,
  660,
  661,
  662,
  663,
  665,
  666
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 60 → SparsePoly (Fin 61) := ![
  [{ coefficient := 1, powers := [(10, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (23, 1)] }, { coefficient := 1, powers := [(16, 1), (18, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (24, 1)] }, { coefficient := 1, powers := [(16, 1), (18, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (18, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (42, 1)] }, { coefficient := 1, powers := [(17, 1), (18, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (54, 1)] }, { coefficient := 1, powers := [(28, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (42, 1)] }, { coefficient := 1, powers := [(26, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (53, 1)] }, { coefficient := 1, powers := [(28, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (54, 1)] }, { coefficient := 1, powers := [(28, 1), (44, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (24, 1), (45, 1)] }, { coefficient := 1, powers := [(10, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (23, 1), (44, 1)] }, { coefficient := 1, powers := [(16, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (23, 1), (47, 1)] }, { coefficient := 1, powers := [(17, 1), (19, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (42, 1), (53, 1)] }, { coefficient := 1, powers := [(20, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1)] }, { coefficient := 1, powers := [(18, 1), (42, 1)] }, { coefficient := 1, powers := [(23, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (42, 1)] }, { coefficient := 1, powers := [(23, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (49, 1)] }, { coefficient := 1, powers := [(18, 1), (49, 1)] }, { coefficient := 1, powers := [(23, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (44, 1)] }, { coefficient := 1, powers := [(4, 1), (33, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (51, 1)] }, { coefficient := 1, powers := [(7, 1), (30, 1)] }, { coefficient := 1, powers := [(10, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (44, 1)] }, { coefficient := 1, powers := [(12, 1), (56, 1)] }, { coefficient := 1, powers := [(16, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (45, 1)] }, { coefficient := 1, powers := [(17, 1), (39, 1)] }, { coefficient := 1, powers := [(17, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (53, 1)] }, { coefficient := 1, powers := [(28, 1), (39, 1)] }, { coefficient := 1, powers := [(28, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1), (51, 1)] }, { coefficient := 1, powers := [(18, 1), (42, 1), (51, 1)] }, { coefficient := 1, powers := [(42, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1), (54, 1)] }, { coefficient := 1, powers := [(24, 1), (44, 1), (49, 1)] }, { coefficient := 1, powers := [(54, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1), (51, 1)] }, { coefficient := 1, powers := [(19, 1), (42, 1), (51, 1)] }, { coefficient := 1, powers := [(47, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (18, 1), (56, 1)] }, { coefficient := 1, powers := [(12, 1)] }, { coefficient := 1, powers := [(16, 1), (18, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (24, 1), (46, 1)] }, { coefficient := 1, powers := [(16, 1), (19, 1), (54, 1)] }, { coefficient := 1, powers := [(16, 1), (24, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (23, 1), (45, 1)] }, { coefficient := 1, powers := [(17, 1), (23, 1), (39, 1)] }, { coefficient := 1, powers := [(17, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (47, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1)] }, { coefficient := 1, powers := [(16, 1), (26, 1), (47, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1)] }, { coefficient := 1, powers := [(12, 1), (28, 1)] }, { coefficient := 1, powers := [(16, 1), (21, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (60, 1)] }, { coefficient := 1, powers := [(12, 1), (47, 1)] }, { coefficient := 1, powers := [(17, 1), (19, 1), (52, 1)] }, { coefficient := 1, powers := [(17, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (60, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (45, 1)] }, { coefficient := 1, powers := [(12, 1), (57, 1)] }, { coefficient := 1, powers := [(17, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (54, 1)] }, { coefficient := 1, powers := [(28, 1), (40, 1)] }, { coefficient := 1, powers := [(28, 1), (46, 1), (49, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (37, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (46, 1), (53, 1)] }, { coefficient := 1, powers := [(19, 1), (53, 1)] }, { coefficient := 1, powers := [(24, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(44, 1), (49, 1)] }, { coefficient := 1, powers := [(49, 1), (56, 1)] }, { coefficient := 1, powers := [(52, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1), (53, 1)] }, { coefficient := 1, powers := [(24, 1), (39, 1)] }, { coefficient := 1, powers := [(24, 1), (44, 1)] }, { coefficient := 1, powers := [(53, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1), (51, 1)] }, { coefficient := 1, powers := [(39, 1), (42, 1)] }, { coefficient := 1, powers := [(42, 1), (51, 1)] }, { coefficient := 1, powers := [(45, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1), (51, 1)] }, { coefficient := 1, powers := [(19, 1), (51, 1)] }, { coefficient := 1, powers := [(19, 1), (56, 1)] }, { coefficient := 1, powers := [(46, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1), (52, 1)] }, { coefficient := 1, powers := [(19, 1), (42, 1), (52, 1)] }, { coefficient := 1, powers := [(40, 1), (42, 1)] }, { coefficient := 1, powers := [(47, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (39, 1), (57, 1)] }, { coefficient := 1, powers := [(1, 1), (45, 1), (53, 1)] }, { coefficient := 1, powers := [(4, 1), (30, 1), (57, 1)] }, { coefficient := 1, powers := [(10, 1), (20, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (23, 1), (59, 1)] }, { coefficient := 1, powers := [(10, 1), (23, 1), (44, 1)] }, { coefficient := 1, powers := [(14, 1), (23, 1), (39, 1)] }, { coefficient := 1, powers := [(14, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (24, 1), (59, 1)] }, { coefficient := 1, powers := [(10, 1), (24, 1), (44, 1)] }, { coefficient := 1, powers := [(14, 1), (24, 1), (39, 1)] }, { coefficient := 1, powers := [(14, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (19, 1), (56, 1)] }, { coefficient := 1, powers := [(12, 1), (46, 1)] }, { coefficient := 1, powers := [(16, 1), (19, 1), (52, 1)] }, { coefficient := 1, powers := [(16, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (42, 1), (53, 1)] }, { coefficient := 1, powers := [(22, 1), (57, 1)] }, { coefficient := 1, powers := [(28, 1), (47, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1)] }, { coefficient := 1, powers := [(6, 1), (59, 1)] }, { coefficient := 1, powers := [(23, 1), (39, 1)] }, { coefficient := 1, powers := [(23, 1), (44, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(4, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (59, 1)] }, { coefficient := 1, powers := [(10, 1), (44, 1)] }, { coefficient := 1, powers := [(10, 1), (56, 1)] }, { coefficient := 1, powers := [(14, 1), (39, 1)] }, { coefficient := 1, powers := [(14, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (51, 1)] }, { coefficient := 1, powers := [(20, 1), (56, 1)] }, { coefficient := 1, powers := [(25, 1), (39, 1)] }, { coefficient := 1, powers := [(25, 1), (44, 1)] }, { coefficient := 1, powers := [(30, 1), (36, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (39, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (45, 1), (53, 1)] }, { coefficient := 1, powers := [(24, 1), (39, 1), (42, 1)] }, { coefficient := 1, powers := [(24, 1), (45, 1)] }, { coefficient := 1, powers := [(42, 1), (53, 1)] }, { coefficient := 1, powers := [(57, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (40, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(19, 1), (49, 1), (56, 1)] }, { coefficient := 1, powers := [(19, 1), (52, 1)] }, { coefficient := 1, powers := [(40, 1)] }, { coefficient := 1, powers := [(46, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (42, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (21, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1), (42, 1)] }, { coefficient := 1, powers := [(12, 1), (21, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1), (28, 1), (42, 1)] }, { coefficient := 1, powers := [(17, 1), (21, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (46, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1), (46, 1)] }, { coefficient := 1, powers := [(12, 1), (28, 1), (46, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1), (54, 1)] }, { coefficient := 1, powers := [(16, 1), (28, 1), (40, 1)] }, { coefficient := 1, powers := [(16, 1), (31, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (36, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (44, 1), (51, 1)] }, { coefficient := 1, powers := [(39, 1)] }, { coefficient := 1, powers := [(44, 1)] }, { coefficient := 1, powers := [(51, 1)] }, { coefficient := 1, powers := [(56, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (36, 1), (59, 1)] }, { coefficient := 1, powers := [(1, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(1, 1), (44, 1), (51, 1)] }, { coefficient := 1, powers := [(4, 1), (25, 1), (59, 1)] }, { coefficient := 1, powers := [(4, 1), (30, 1), (56, 1)] }, { coefficient := 1, powers := [(4, 1), (33, 1), (51, 1)] }, { coefficient := 1, powers := [(7, 1), (20, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (30, 1), (44, 1)] }, { coefficient := 1, powers := [(7, 1), (33, 1), (39, 1)] }, { coefficient := 1, powers := [(10, 1), (20, 1), (56, 1)] }, { coefficient := 1, powers := [(10, 1), (25, 1), (44, 1)] }, { coefficient := 1, powers := [(10, 1), (33, 1), (36, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1), (51, 1)] }, { coefficient := 1, powers := [(14, 1), (25, 1), (39, 1)] }, { coefficient := 1, powers := [(14, 1), (30, 1), (36, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (37, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (47, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (28, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (22, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1), (47, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (40, 1)] }, { coefficient := 1, powers := [(12, 1), (22, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1), (28, 1), (47, 1)] }, { coefficient := 1, powers := [(12, 1), (34, 1), (37, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (54, 1)] }, { coefficient := 1, powers := [(17, 1), (28, 1), (40, 1)] }, { coefficient := 1, powers := [(17, 1), (31, 1), (37, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1)] }],
  [{ coefficient := 1, powers := [(1, 1)] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(39, 1)] }],
  [{ coefficient := 1, powers := [(40, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 60 → SparsePoly (Fin 61) := ![
  [{ coefficient := 1, powers := [(5, 1), (6, 1), (23, 1), (31, 1), (33, 1), (36, 1), (53, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (6, 1), (24, 1), (31, 1), (33, 1), (36, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (23, 1), (24, 1), (31, 1), (33, 1), (36, 1), (44, 1)] }, { coefficient := 1, powers := [(5, 1), (23, 1), (31, 1), (33, 1), (36, 1), (53, 1)] }, { coefficient := -1, powers := [(5, 1), (24, 1), (25, 1), (31, 1), (51, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (7, 1), (31, 1), (42, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (14, 1), (31, 1), (42, 1), (51, 1)] }, { coefficient := 1, powers := [(5, 1), (14, 1), (31, 1), (42, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (7, 1), (24, 1), (31, 1), (51, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (7, 1), (31, 1), (53, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (14, 1), (24, 1), (31, 1), (51, 1), (56, 1)] }, { coefficient := -1, powers := [(5, 1), (14, 1), (31, 1), (53, 1), (56, 1)] }],
  [{ coefficient := -2, powers := [(28, 1), (47, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (45, 1), (46, 1)] }],
  [{ coefficient := -1, powers := [(21, 1), (45, 1), (46, 1), (54, 1)] }, { coefficient := -1, powers := [(22, 1), (42, 1), (52, 1), (53, 1)] }, { coefficient := 1, powers := [(22, 1), (45, 1), (49, 1), (53, 1)] }, { coefficient := 1, powers := [(22, 1), (45, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (49, 1), (53, 1)] }, { coefficient := 1, powers := [(22, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(16, 1), (47, 1)] }, { coefficient := -1, powers := [(17, 1), (46, 1)] }],
  [{ coefficient := -1, powers := [(16, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (42, 1)] }],
  [{ coefficient := -1, powers := [(16, 1), (19, 1), (42, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (6, 1), (31, 1), (33, 1), (36, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (25, 1), (31, 1), (51, 1)] }],
  [{ coefficient := -1, powers := [(22, 1), (42, 1), (53, 1)] }],
  [{ coefficient := -2, powers := [(28, 1), (49, 1), (51, 1)] }, { coefficient := 1, powers := [(28, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (7, 1), (31, 1), (59, 1)] }, { coefficient := -1, powers := [(5, 1), (14, 1), (31, 1), (51, 1)] }, { coefficient := -1, powers := [(5, 1), (14, 1), (31, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (5, 1), (23, 1), (31, 1), (33, 1), (36, 1), (51, 1), (53, 1), (59, 1)] }, { coefficient := -1, powers := [(12, 1), (22, 1), (53, 1), (56, 1)] }],
  [{ coefficient := 2, powers := [(12, 1), (28, 1), (51, 1)] }, { coefficient := -1, powers := [(16, 1), (28, 1), (52, 1)] }],
  [{ coefficient := 2, powers := [(16, 1), (28, 1), (47, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (31, 1), (51, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (31, 1), (51, 1), (57, 1)] }, { coefficient := -1, powers := [(5, 1), (31, 1), (56, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [(19, 1), (28, 1), (42, 1)] }, { coefficient := 1, powers := [(22, 1), (23, 1), (42, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(18, 1), (22, 1), (49, 1), (53, 1)] }, { coefficient := -1, powers := [(18, 1), (22, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (19, 1), (42, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (5, 1), (23, 1), (31, 1), (33, 1), (36, 1), (53, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(17, 1), (22, 1)] }],
  [{ coefficient := -2, powers := [(12, 1), (28, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (42, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (46, 1), (54, 1)] }, { coefficient := -1, powers := [(22, 1), (49, 1), (53, 1)] }, { coefficient := -1, powers := [(22, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(54, 1)] }],
  [{ coefficient := 1, powers := [(47, 1)] }],
  [{ coefficient := 1, powers := [(28, 1)] }],
  [{ coefficient := -1, powers := [(21, 1), (46, 1)] }, { coefficient := 1, powers := [(22, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (42, 1)] }, { coefficient := 1, powers := [(17, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (27, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (19, 1), (28, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (22, 1), (49, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (5, 1), (23, 2), (31, 1), (33, 1), (36, 1), (53, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (7, 1), (24, 1), (25, 1), (31, 1), (59, 1)] }, { coefficient := -1, powers := [(5, 1), (14, 1), (24, 1), (25, 1), (31, 1), (56, 1)] }],
  [{ coefficient := 2, powers := [(17, 1), (28, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (28, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (31, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (23, 1), (31, 1), (33, 1), (36, 1), (45, 1), (53, 1)] }, { coefficient := -1, powers := [(5, 1), (31, 1), (33, 1), (36, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (23, 1), (31, 1), (33, 1), (36, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(28, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(12, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (10, 1), (23, 1), (31, 1), (33, 1), (36, 1), (45, 1), (53, 1)] }, { coefficient := 1, powers := [(5, 1), (10, 1), (31, 1), (33, 1), (36, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (25, 1), (31, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (14, 1), (31, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (5, 1), (23, 1), (31, 1), (33, 1), (36, 1), (59, 1)] }, { coefficient := -1, powers := [(5, 1), (7, 1), (25, 1), (31, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (14, 1), (25, 1), (31, 1), (56, 1)] }, { coefficient := -1, powers := [(12, 1), (22, 1)] }],
  [{ coefficient := -1, powers := [(16, 1), (28, 1), (42, 1)] }, { coefficient := -2, powers := [(17, 1), (28, 1)] }],
  [{ coefficient := 1, powers := [(46, 1)] }],
  [{ coefficient := -1, powers := [(42, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (7, 1), (30, 1), (31, 1), (57, 1)] }, { coefficient := -1, powers := [(5, 1), (14, 1), (25, 1), (31, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (31, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(4, 1), (5, 1), (23, 2), (31, 1), (33, 1), (36, 1), (45, 1), (51, 1), (53, 1), (59, 1)] }, { coefficient := -1, powers := [(4, 1), (5, 1), (23, 1), (31, 1), (33, 1), (36, 1), (45, 1), (53, 1), (59, 1)] }, { coefficient := -1, powers := [(5, 1), (7, 1), (24, 1), (25, 1), (31, 1), (45, 1), (51, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (7, 1), (25, 1), (31, 1), (45, 1), (53, 1), (59, 1)] }, { coefficient := -1, powers := [(5, 1), (7, 1), (30, 1), (31, 1), (36, 1), (57, 1), (59, 1)] }, { coefficient := -1, powers := [(5, 1), (7, 1), (30, 1), (31, 1), (44, 1), (51, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (10, 1), (23, 1), (31, 1), (33, 1), (36, 1), (44, 1), (45, 1), (53, 1)] }, { coefficient := -1, powers := [(5, 1), (10, 1), (31, 1), (33, 1), (36, 1), (44, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (14, 1), (24, 1), (25, 1), (31, 1), (45, 1), (51, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (14, 1), (25, 1), (31, 1), (36, 1), (57, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (14, 1), (25, 1), (31, 1), (44, 1), (51, 1), (57, 1)] }, { coefficient := -1, powers := [(5, 1), (14, 1), (25, 1), (31, 1), (45, 1), (53, 1), (56, 1)] }, { coefficient := 1, powers := [(12, 1), (22, 1), (42, 1), (53, 1), (56, 1)] }, { coefficient := 1, powers := [(12, 1), (22, 1), (45, 1), (53, 1)] }, { coefficient := 1, powers := [(12, 1), (27, 1), (37, 1), (42, 1), (59, 1)] }, { coefficient := 1, powers := [(12, 1), (27, 1), (42, 1), (46, 1), (53, 1)] }, { coefficient := -1, powers := [(16, 1), (19, 1), (28, 1), (42, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(16, 1), (28, 1), (42, 1), (46, 1), (52, 1)] }, { coefficient := -2, powers := [(16, 1), (28, 1), (47, 1), (49, 1), (51, 1)] }, { coefficient := -1, powers := [(17, 1), (22, 1), (44, 1), (49, 1), (53, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (44, 1), (54, 1)] }, { coefficient := -2, powers := [(17, 1), (28, 1), (46, 1), (49, 1), (51, 1)] }, { coefficient := 2, powers := [(17, 1), (28, 1), (46, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (31, 1), (36, 1), (57, 1), (59, 1)] }, { coefficient := -1, powers := [(5, 1), (31, 1), (45, 1), (53, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (51, 2), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (51, 1), (56, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(37, 1), (60, 1)] }, { coefficient := -1, powers := [(47, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (4, 1), (5, 1), (23, 1), (31, 1), (33, 1), (36, 1), (57, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (5, 1), (7, 1), (25, 1), (31, 1), (57, 1), (59, 1)] }, { coefficient := -1, powers := [(0, 1), (5, 1), (7, 1), (30, 1), (31, 1), (56, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (12, 1), (22, 1), (57, 1)] }, { coefficient := 1, powers := [(4, 1), (5, 1), (23, 2), (31, 1), (33, 1), (36, 1), (42, 1), (53, 1), (59, 1)] }, { coefficient := -1, powers := [(4, 1), (5, 1), (23, 1), (24, 1), (31, 1), (33, 1), (36, 1), (42, 1), (59, 1)] }, { coefficient := -1, powers := [(5, 1), (7, 1), (30, 1), (31, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (7, 1), (31, 1), (33, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (10, 1), (23, 2), (31, 1), (33, 1), (36, 1), (45, 1), (53, 1)] }, { coefficient := -1, powers := [(5, 1), (10, 1), (23, 1), (31, 1), (33, 1), (36, 1), (57, 1)] }, { coefficient := -1, powers := [(5, 1), (14, 1), (23, 2), (31, 1), (33, 1), (36, 1), (45, 1), (53, 1)] }, { coefficient := 1, powers := [(5, 1), (14, 1), (23, 1), (24, 1), (31, 1), (33, 1), (36, 1), (45, 1)] }, { coefficient := 1, powers := [(5, 1), (14, 1), (23, 1), (31, 1), (33, 1), (36, 1), (57, 1)] }, { coefficient := -1, powers := [(12, 1), (19, 1), (28, 1), (42, 1)] }, { coefficient := 1, powers := [(12, 1), (22, 1), (24, 1), (42, 1)] }, { coefficient := 1, powers := [(17, 1), (18, 1), (22, 1), (49, 1), (53, 1)] }, { coefficient := 1, powers := [(17, 1), (18, 1), (22, 1), (54, 1)] }, { coefficient := -1, powers := [(17, 1), (21, 1), (23, 1), (46, 1), (54, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (23, 1), (49, 1), (53, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (23, 1), (54, 1)] }, { coefficient := -1, powers := [(17, 1), (22, 1), (24, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (16, 1), (28, 1), (42, 1), (56, 1)] }, { coefficient := 2, powers := [(0, 1), (17, 1), (28, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (57, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1)] }, { coefficient := -1, powers := [(16, 1), (24, 1), (27, 1), (42, 1)] }, { coefficient := -1, powers := [(16, 1), (28, 1), (42, 1)] }, { coefficient := 1, powers := [(17, 1), (28, 1)] }]
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
    (values : Fin 61 → R) :
    ¬ ∀ index : Fin 60,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component39.SelectedLeafB0_0.selectedHasNoCommonZero

end Krenn.Component39.SelectedLeafB0_0
