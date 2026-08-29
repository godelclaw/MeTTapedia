import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component18.SelectedLeafB5_7

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "61fd851cf1fb6ca91163733ea71360e10334bb94aa8300ceda218c53b6bc629f"
def certificateSHA256 : String := "c6b480ada529bf80c4c992e63b22f914c57247a6e3d31bb95764eac17d61b314"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 35 → Fin 664 := ![
  0,
  5,
  6,
  12,
  16,
  17,
  19,
  20,
  22,
  25,
  168,
  295,
  300,
  301,
  302,
  315,
  318,
  321,
  327,
  409,
  424,
  437,
  463,
  496,
  562,
  585,
  590,
  602,
  603,
  650,
  655,
  657,
  660,
  662,
  663
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 35 → SparsePoly (Fin 66) := ![
  [{ coefficient := 1, powers := [(3, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(30, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(43, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (53, 1)] }, { coefficient := 1, powers := [(31, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (49, 1)] }, { coefficient := 1, powers := [(20, 1), (45, 1)] }, { coefficient := 1, powers := [(25, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (44, 1)] }, { coefficient := 1, powers := [(17, 1), (23, 1), (55, 1)] }, { coefficient := 1, powers := [(17, 1), (29, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (60, 1)] }, { coefficient := 1, powers := [(13, 1), (49, 1)] }, { coefficient := 1, powers := [(18, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (58, 1)] }, { coefficient := 1, powers := [(9, 1), (55, 1)] }, { coefficient := 1, powers := [(14, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (47, 1)] }, { coefficient := 1, powers := [(18, 1), (42, 1)] }, { coefficient := 1, powers := [(18, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (54, 1)] }, { coefficient := 1, powers := [(31, 1), (43, 1)] }, { coefficient := 1, powers := [(34, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1), (55, 1)] }, { coefficient := 1, powers := [(6, 1), (35, 1), (43, 1)] }, { coefficient := 1, powers := [(14, 1), (25, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (49, 1), (52, 1)] }, { coefficient := 1, powers := [(20, 1), (45, 1), (52, 1)] }, { coefficient := 1, powers := [(49, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (25, 1), (47, 1)] }, { coefficient := 1, powers := [(18, 1), (25, 1), (42, 1)] }, { coefficient := 1, powers := [(18, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1)] }, { coefficient := 1, powers := [(25, 1), (42, 1), (45, 1)] }, { coefficient := 1, powers := [(25, 1), (47, 1)] }, { coefficient := 1, powers := [(45, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1)] }, { coefficient := 1, powers := [(13, 1), (31, 1)] }, { coefficient := 1, powers := [(17, 1), (23, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1), (52, 1)] }, { coefficient := 1, powers := [(42, 1), (45, 1)] }, { coefficient := 1, powers := [(45, 1), (52, 1)] }, { coefficient := 1, powers := [(47, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (31, 1), (60, 1)] }, { coefficient := 1, powers := [(3, 1), (34, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (37, 1), (54, 1)] }, { coefficient := 1, powers := [(23, 1), (45, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (45, 1), (53, 1)] }, { coefficient := 1, powers := [(24, 1), (57, 1)] }, { coefficient := 1, powers := [(31, 1), (49, 1)] }, { coefficient := 1, powers := [(37, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1), (55, 1)] }, { coefficient := 1, powers := [(6, 1), (35, 1), (42, 1)] }, { coefficient := 1, powers := [(14, 1), (25, 1), (42, 1)] }, { coefficient := 1, powers := [(14, 1)] }, { coefficient := 1, powers := [(55, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (41, 1), (55, 1)] }, { coefficient := 1, powers := [(2, 1), (44, 1), (50, 1)] }, { coefficient := 1, powers := [(12, 1), (23, 1), (55, 1)] }, { coefficient := 1, powers := [(12, 1), (29, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1)] }, { coefficient := 1, powers := [(3, 1), (35, 1)] }, { coefficient := 1, powers := [(14, 1), (19, 1)] }, { coefficient := 1, powers := [(19, 1), (55, 1)] }, { coefficient := 1, powers := [(25, 1), (44, 1)] }, { coefficient := 1, powers := [(35, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (50, 1)] }, { coefficient := 1, powers := [(6, 1), (32, 1)] }, { coefficient := 1, powers := [(9, 1), (25, 1)] }, { coefficient := 1, powers := [(19, 1), (50, 1)] }, { coefficient := 1, powers := [(25, 1), (41, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (42, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (47, 1), (53, 1)] }, { coefficient := 1, powers := [(8, 1), (37, 1), (42, 1)] }, { coefficient := 1, powers := [(17, 1), (30, 1), (57, 1)] }, { coefficient := 1, powers := [(17, 1), (31, 1), (47, 1)] }, { coefficient := 1, powers := [(18, 1), (30, 1), (53, 1)] }, { coefficient := 1, powers := [(18, 1), (31, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (38, 1), (58, 1)] }, { coefficient := 1, powers := [(0, 1), (41, 1), (55, 1)] }, { coefficient := 1, powers := [(0, 1), (44, 1), (50, 1)] }, { coefficient := 1, powers := [(3, 1), (25, 1), (58, 1)] }, { coefficient := 1, powers := [(3, 1), (32, 1), (55, 1)] }, { coefficient := 1, powers := [(3, 1), (35, 1), (50, 1)] }, { coefficient := 1, powers := [(6, 1), (19, 1), (58, 1)] }, { coefficient := 1, powers := [(6, 1), (32, 1), (44, 1)] }, { coefficient := 1, powers := [(6, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(9, 1), (19, 1), (55, 1)] }, { coefficient := 1, powers := [(9, 1), (25, 1), (44, 1)] }, { coefficient := 1, powers := [(9, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(14, 1), (19, 1), (50, 1)] }, { coefficient := 1, powers := [(14, 1), (25, 1), (41, 1)] }, { coefficient := 1, powers := [(14, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (40, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (43, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (49, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (37, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (49, 1)] }, { coefficient := 1, powers := [(8, 1), (37, 1), (43, 1)] }, { coefficient := 1, powers := [(13, 1), (24, 1), (57, 1)] }, { coefficient := 1, powers := [(13, 1), (31, 1), (49, 1)] }, { coefficient := 1, powers := [(13, 1), (37, 1), (40, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (54, 1)] }, { coefficient := 1, powers := [(18, 1), (31, 1), (43, 1)] }, { coefficient := 1, powers := [(18, 1), (34, 1), (40, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(42, 1), (64, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(43, 1), (65, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 35 → SparsePoly (Fin 66) := ![
  [{ coefficient := -1, powers := [(2, 1), (9, 1), (35, 1), (40, 1)] }, { coefficient := 1, powers := [(2, 1), (35, 1), (40, 1), (50, 1)] }, { coefficient := 1, powers := [(5, 1), (9, 1), (31, 1), (35, 1)] }, { coefficient := -1, powers := [(5, 1), (31, 1), (35, 1), (50, 1)] }, { coefficient := -1, powers := [(8, 1), (9, 1), (24, 1), (35, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (35, 1), (50, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (29, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (23, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (41, 1), (65, 1)] }, { coefficient := -1, powers := [(0, 1), (50, 1), (65, 1)] }, { coefficient := -1, powers := [(3, 1), (32, 1), (65, 1)] }, { coefficient := -1, powers := [(6, 1), (32, 1), (65, 1)] }, { coefficient := -1, powers := [(9, 1), (25, 1), (65, 1)] }, { coefficient := -1, powers := [(19, 1), (50, 1), (65, 1)] }, { coefficient := -1, powers := [(25, 1), (41, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (9, 1), (29, 1), (62, 1)] }, { coefficient := -1, powers := [(6, 1), (29, 1), (32, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (9, 1), (23, 1), (62, 1)] }, { coefficient := -1, powers := [(6, 1), (23, 1), (32, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (9, 1), (17, 1), (35, 1), (49, 1)] }, { coefficient := -1, powers := [(3, 1), (17, 1), (35, 1), (49, 1), (50, 1)] }, { coefficient := 1, powers := [(5, 1), (9, 1), (35, 1), (45, 1)] }, { coefficient := -1, powers := [(5, 1), (35, 1), (45, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (3, 1), (9, 1), (35, 1), (43, 1), (47, 1), (52, 1), (53, 1), (64, 1), (65, 1)] }, { coefficient := -1, powers := [(2, 1), (3, 1), (35, 1), (43, 1), (47, 1), (50, 1), (52, 1), (53, 1), (64, 1), (65, 1)] }, { coefficient := 2, powers := [(3, 1), (9, 1), (13, 1), (31, 1), (35, 1), (49, 1), (52, 1), (65, 1)] }, { coefficient := -1, powers := [(3, 1), (9, 1), (18, 1), (31, 1), (35, 1), (43, 1), (52, 2), (64, 1), (65, 1)] }, { coefficient := 1, powers := [(3, 1), (9, 1), (18, 1), (31, 1), (35, 1), (43, 1), (52, 1), (65, 1)] }, { coefficient := -2, powers := [(3, 1), (13, 1), (31, 1), (35, 1), (49, 1), (50, 1), (52, 1), (65, 1)] }, { coefficient := 1, powers := [(3, 1), (18, 1), (31, 1), (35, 1), (43, 1), (50, 1), (52, 2), (64, 1), (65, 1)] }, { coefficient := -1, powers := [(3, 1), (18, 1), (31, 1), (35, 1), (43, 1), (50, 1), (52, 1), (65, 1)] }, { coefficient := 1, powers := [(3, 1), (58, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (9, 1), (17, 1), (35, 1), (43, 1), (57, 1), (64, 1), (65, 1)] }, { coefficient := 1, powers := [(3, 1), (9, 1), (18, 1), (35, 1), (43, 1), (53, 1), (64, 1), (65, 1)] }, { coefficient := -1, powers := [(3, 1), (17, 1), (35, 1), (43, 1), (50, 1), (57, 1), (64, 1), (65, 1)] }, { coefficient := -1, powers := [(3, 1), (18, 1), (35, 1), (43, 1), (50, 1), (53, 1), (64, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (3, 1), (9, 1), (25, 1), (35, 1), (42, 1), (43, 1), (52, 1), (53, 1), (64, 1), (65, 1)] }, { coefficient := -1, powers := [(2, 1), (3, 1), (9, 1), (35, 1), (42, 1), (43, 1), (53, 1), (64, 1), (65, 1)] }, { coefficient := -1, powers := [(2, 1), (3, 1), (25, 1), (35, 1), (42, 1), (43, 1), (50, 1), (52, 1), (53, 1), (64, 1), (65, 1)] }, { coefficient := 1, powers := [(2, 1), (3, 1), (35, 1), (42, 1), (43, 1), (50, 1), (53, 1), (64, 1), (65, 1)] }, { coefficient := -1, powers := [(3, 1), (9, 1), (13, 1), (31, 1), (35, 1), (48, 1), (65, 1)] }, { coefficient := 1, powers := [(3, 1), (13, 1), (31, 1), (35, 1), (48, 1), (50, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (9, 1), (13, 1), (35, 1), (45, 1)] }, { coefficient := -1, powers := [(3, 1), (13, 1), (35, 1), (45, 1), (50, 1)] }],
  [{ coefficient := -2, powers := [(3, 1), (9, 1), (13, 1), (31, 1), (35, 1), (52, 1)] }, { coefficient := 2, powers := [(3, 1), (13, 1), (31, 1), (35, 1), (50, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (9, 1), (62, 1)] }, { coefficient := 1, powers := [(6, 1), (32, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (9, 1), (31, 1), (35, 1)] }, { coefficient := 1, powers := [(3, 1), (31, 1), (35, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(19, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (9, 1), (25, 1), (31, 1), (35, 1), (43, 1), (52, 1), (64, 1)] }, { coefficient := -1, powers := [(3, 1), (9, 1), (25, 1), (31, 1), (35, 1), (43, 1)] }, { coefficient := 1, powers := [(3, 1), (9, 1), (31, 1), (35, 1), (43, 1), (64, 1)] }, { coefficient := -1, powers := [(3, 1), (25, 1), (31, 1), (35, 1), (43, 1), (50, 1), (52, 1), (64, 1)] }, { coefficient := 1, powers := [(3, 1), (25, 1), (31, 1), (35, 1), (43, 1), (50, 1)] }, { coefficient := -1, powers := [(3, 1), (31, 1), (35, 1), (43, 1), (50, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (9, 1), (18, 1), (35, 1)] }, { coefficient := 1, powers := [(3, 1), (18, 1), (35, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (41, 1), (42, 1), (65, 1)] }, { coefficient := -1, powers := [(3, 1), (32, 1), (42, 1), (65, 1)] }, { coefficient := 1, powers := [(9, 1), (19, 1), (42, 1), (65, 1)] }, { coefficient := 1, powers := [(41, 1), (65, 1)] }],
  [{ coefficient := 2, powers := [(3, 1), (9, 1), (13, 1), (31, 1), (35, 1)] }, { coefficient := -2, powers := [(3, 1), (13, 1), (31, 1), (35, 1), (50, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (9, 1), (31, 1), (35, 1), (43, 1), (52, 1), (64, 1)] }, { coefficient := 1, powers := [(3, 1), (9, 1), (31, 1), (35, 1), (43, 1)] }, { coefficient := 1, powers := [(3, 1), (31, 1), (35, 1), (43, 1), (50, 1), (52, 1), (64, 1)] }, { coefficient := -1, powers := [(3, 1), (31, 1), (35, 1), (43, 1), (50, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (3, 1), (9, 1), (35, 1), (43, 1), (52, 1), (53, 1), (64, 1)] }, { coefficient := 1, powers := [(2, 1), (3, 1), (35, 1), (43, 1), (50, 1), (52, 1), (53, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (9, 1), (35, 1), (49, 1)] }, { coefficient := 1, powers := [(3, 1), (35, 1), (49, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (3, 1), (9, 1), (35, 1), (43, 1), (53, 1), (64, 1)] }, { coefficient := -1, powers := [(2, 1), (3, 1), (35, 1), (43, 1), (50, 1), (53, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (9, 1), (35, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (50, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (9, 1), (13, 1), (35, 1)] }, { coefficient := 1, powers := [(3, 1), (13, 1), (35, 1), (50, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (41, 1)] }, { coefficient := 1, powers := [(3, 1), (32, 1)] }, { coefficient := -1, powers := [(9, 1), (19, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(9, 1)] }],
  [{ coefficient := 1, powers := [(14, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (9, 1), (35, 1), (43, 1), (64, 1)] }, { coefficient := 1, powers := [(3, 1), (35, 1), (43, 1), (50, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(3, 1), (9, 1), (35, 1)] }, { coefficient := -1, powers := [(3, 1), (35, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (9, 1), (44, 1)] }, { coefficient := -1, powers := [(0, 1), (38, 1), (58, 1)] }, { coefficient := -1, powers := [(0, 1), (41, 1), (55, 1)] }, { coefficient := -1, powers := [(0, 1), (44, 1), (50, 1)] }, { coefficient := -1, powers := [(6, 1), (32, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (3, 1), (9, 1), (35, 1), (43, 1), (57, 1)] }, { coefficient := -1, powers := [(2, 1), (3, 1), (35, 1), (43, 1), (50, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (8, 1), (9, 1), (35, 1), (37, 1), (43, 1)] }, { coefficient := -1, powers := [(3, 1), (8, 1), (35, 1), (37, 1), (43, 1), (50, 1)] }],
  [{ coefficient := -1, powers := [(0, 2), (41, 1), (42, 1), (55, 1)] }, { coefficient := 1, powers := [(0, 1), (3, 1), (32, 1), (42, 1), (55, 1)] }, { coefficient := -1, powers := [(0, 1), (6, 1), (35, 1), (41, 1), (42, 1)] }, { coefficient := -1, powers := [(0, 1), (9, 1), (19, 1), (42, 1), (55, 1)] }, { coefficient := -1, powers := [(0, 1), (14, 1), (25, 1), (41, 1), (42, 1)] }, { coefficient := -1, powers := [(0, 1), (14, 1), (41, 1)] }, { coefficient := 1, powers := [(0, 1), (14, 1), (50, 1)] }, { coefficient := -1, powers := [(0, 1), (41, 1), (55, 1)] }, { coefficient := -1, powers := [(2, 1), (3, 1), (9, 1), (25, 1), (35, 1), (42, 1), (43, 1), (45, 1), (52, 1), (53, 1), (64, 1)] }, { coefficient := -1, powers := [(2, 1), (3, 1), (9, 1), (25, 1), (35, 1), (43, 1), (47, 1), (52, 1), (53, 1), (64, 1)] }, { coefficient := 1, powers := [(2, 1), (3, 1), (9, 1), (35, 1), (42, 1), (43, 1), (45, 1), (53, 1), (64, 1)] }, { coefficient := 1, powers := [(2, 1), (3, 1), (25, 1), (35, 1), (42, 1), (43, 1), (45, 1), (50, 1), (52, 1), (53, 1), (64, 1)] }, { coefficient := 1, powers := [(2, 1), (3, 1), (25, 1), (35, 1), (43, 1), (47, 1), (50, 1), (52, 1), (53, 1), (64, 1)] }, { coefficient := -1, powers := [(2, 1), (3, 1), (35, 1), (42, 1), (43, 1), (45, 1), (50, 1), (53, 1), (64, 1)] }, { coefficient := 1, powers := [(3, 1), (6, 1), (32, 1), (35, 1), (42, 1)] }, { coefficient := -2, powers := [(3, 1), (9, 1), (13, 1), (25, 1), (31, 1), (35, 1), (49, 1), (52, 1)] }, { coefficient := 1, powers := [(3, 1), (9, 1), (13, 1), (31, 1), (35, 1), (45, 1), (48, 1)] }, { coefficient := -1, powers := [(3, 1), (9, 1), (17, 1), (30, 1), (35, 1), (43, 1), (57, 1), (64, 1)] }, { coefficient := 1, powers := [(3, 1), (9, 1), (18, 1), (25, 1), (31, 1), (35, 1), (43, 1), (52, 2), (64, 1)] }, { coefficient := -1, powers := [(3, 1), (9, 1), (18, 1), (25, 1), (31, 1), (35, 1), (43, 1), (52, 1)] }, { coefficient := -1, powers := [(3, 1), (9, 1), (18, 1), (30, 1), (35, 1), (43, 1), (53, 1), (64, 1)] }, { coefficient := 2, powers := [(3, 1), (13, 1), (25, 1), (31, 1), (35, 1), (49, 1), (50, 1), (52, 1)] }, { coefficient := -1, powers := [(3, 1), (13, 1), (31, 1), (35, 1), (45, 1), (48, 1), (50, 1)] }, { coefficient := 1, powers := [(3, 1), (14, 1), (25, 1), (32, 1), (42, 1)] }, { coefficient := 1, powers := [(3, 1), (14, 1), (32, 1)] }, { coefficient := 1, powers := [(3, 1), (17, 1), (30, 1), (35, 1), (43, 1), (50, 1), (57, 1), (64, 1)] }, { coefficient := -1, powers := [(3, 1), (18, 1), (25, 1), (31, 1), (35, 1), (43, 1), (50, 1), (52, 2), (64, 1)] }, { coefficient := 1, powers := [(3, 1), (18, 1), (25, 1), (31, 1), (35, 1), (43, 1), (50, 1), (52, 1)] }, { coefficient := 1, powers := [(3, 1), (18, 1), (30, 1), (35, 1), (43, 1), (50, 1), (53, 1), (64, 1)] }, { coefficient := -1, powers := [(3, 1), (25, 1), (58, 1)] }, { coefficient := -1, powers := [(6, 1), (9, 1), (19, 1), (35, 1), (42, 1)] }, { coefficient := 1, powers := [(6, 1), (14, 1), (32, 1)] }, { coefficient := -1, powers := [(6, 1), (35, 1), (41, 1)] }, { coefficient := -1, powers := [(9, 1), (14, 1), (19, 1), (25, 1), (42, 1)] }, { coefficient := 1, powers := [(9, 1), (14, 1), (25, 1)] }, { coefficient := 1, powers := [(14, 1), (19, 1), (50, 1)] }]
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
    (values : Fin 66 → R) :
    ¬ ∀ index : Fin 35,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component18.SelectedLeafB5_7.selectedHasNoCommonZero

end Krenn.Component18.SelectedLeafB5_7
