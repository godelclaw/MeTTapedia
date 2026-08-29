import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component37.SelectedLeafB0_6_2_5

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "9728a0b34a3ca11888624de445644dc616e0f89d2c6cca4bbc51067f7287c44f"
def certificateSHA256 : String := "3368a3fa368c81365c6dbc95612a3a897c297077659582034af5ab696b14e199"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 39 → Fin 670 := ![
  8,
  16,
  19,
  68,
  151,
  152,
  153,
  167,
  171,
  175,
  179,
  180,
  231,
  295,
  301,
  303,
  433,
  438,
  446,
  450,
  470,
  473,
  475,
  481,
  566,
  602,
  603,
  612,
  645,
  655,
  657,
  658,
  660,
  661,
  663,
  664,
  666,
  667,
  669
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 39 → SparsePoly (Fin 67) := ![
  [{ coefficient := 1, powers := [(9, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (21, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (30, 1)] }, { coefficient := 1, powers := [(30, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (44, 1)] }, { coefficient := 1, powers := [(40, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (47, 1)] }, { coefficient := 1, powers := [(31, 1), (38, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (25, 1)] }, { coefficient := 1, powers := [(18, 1), (20, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (20, 1)] }, { coefficient := 1, powers := [(18, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (55, 1)] }, { coefficient := 1, powers := [(30, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (44, 1)] }, { coefficient := 1, powers := [(28, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (29, 1), (58, 1)] }, { coefficient := 1, powers := [(9, 1), (30, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (49, 1)] }, { coefficient := 1, powers := [(21, 1), (44, 1)] }, { coefficient := 1, powers := [(25, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (59, 1)] }, { coefficient := 1, powers := [(9, 1), (43, 1)] }, { coefficient := 1, powers := [(13, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (46, 1)] }, { coefficient := 1, powers := [(9, 1), (57, 1)] }, { coefficient := 1, powers := [(31, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (49, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1)] }, { coefficient := 1, powers := [(18, 1), (28, 1), (49, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1)] }, { coefficient := 1, powers := [(12, 1), (30, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (61, 1)] }, { coefficient := 1, powers := [(12, 1), (49, 1)] }, { coefficient := 1, powers := [(19, 1), (21, 1), (53, 1)] }, { coefficient := 1, powers := [(19, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (61, 1)] }, { coefficient := 1, powers := [(12, 1), (26, 1), (47, 1)] }, { coefficient := 1, powers := [(12, 1), (58, 1)] }, { coefficient := 1, powers := [(19, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1), (50, 1)] }, { coefficient := 1, powers := [(6, 1), (31, 1), (46, 1)] }, { coefficient := 1, powers := [(9, 1), (25, 1), (46, 1)] }, { coefficient := 1, powers := [(50, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1), (50, 1)] }, { coefficient := 1, powers := [(6, 1), (31, 1), (47, 1)] }, { coefficient := 1, powers := [(9, 1), (25, 1), (47, 1)] }, { coefficient := 1, powers := [(44, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1), (52, 1)] }, { coefficient := 1, powers := [(41, 1), (44, 1)] }, { coefficient := 1, powers := [(44, 1), (52, 1)] }, { coefficient := 1, powers := [(47, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (49, 1), (50, 1)] }, { coefficient := 1, powers := [(6, 1), (31, 1), (49, 1)] }, { coefficient := 1, powers := [(9, 1), (25, 1), (49, 1)] }, { coefficient := 1, powers := [(21, 1), (44, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (44, 1), (54, 1)] }, { coefficient := 1, powers := [(24, 1), (58, 1)] }, { coefficient := 1, powers := [(30, 1), (49, 1)] }, { coefficient := 1, powers := [(36, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1)] }, { coefficient := 1, powers := [(3, 1), (34, 1)] }, { coefficient := 1, powers := [(13, 1), (20, 1)] }, { coefficient := 1, powers := [(20, 1), (56, 1)] }, { coefficient := 1, powers := [(25, 1), (43, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (50, 1)] }, { coefficient := 1, powers := [(6, 1), (31, 1)] }, { coefficient := 1, powers := [(9, 1), (25, 1)] }, { coefficient := 1, powers := [(20, 1), (50, 1)] }, { coefficient := 1, powers := [(25, 1), (40, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1), (50, 1)] }, { coefficient := 1, powers := [(6, 1), (31, 1), (45, 1)] }, { coefficient := 1, powers := [(6, 1), (59, 1)] }, { coefficient := 1, powers := [(9, 1), (25, 1), (45, 1)] }, { coefficient := 1, powers := [(9, 1), (56, 1)] }, { coefficient := 1, powers := [(13, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (38, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (41, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(41, 1)] }, { coefficient := 1, powers := [(46, 1)] }, { coefficient := 1, powers := [(52, 1)] }, { coefficient := 1, powers := [(57, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (37, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (40, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (43, 1), (50, 1)] }, { coefficient := 1, powers := [(3, 1), (25, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (31, 1), (56, 1)] }, { coefficient := 1, powers := [(3, 1), (34, 1), (50, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (31, 1), (43, 1)] }, { coefficient := 1, powers := [(6, 1), (34, 1), (40, 1)] }, { coefficient := 1, powers := [(9, 1), (20, 1), (56, 1)] }, { coefficient := 1, powers := [(9, 1), (25, 1), (43, 1)] }, { coefficient := 1, powers := [(9, 1), (34, 1), (37, 1)] }, { coefficient := 1, powers := [(13, 1), (20, 1), (50, 1)] }, { coefficient := 1, powers := [(13, 1), (25, 1), (40, 1)] }, { coefficient := 1, powers := [(13, 1), (31, 1), (37, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (39, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (42, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (49, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (49, 1)] }, { coefficient := 1, powers := [(8, 1), (36, 1), (42, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (58, 1)] }, { coefficient := 1, powers := [(12, 1), (30, 1), (49, 1)] }, { coefficient := 1, powers := [(12, 1), (36, 1), (39, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (55, 1)] }, { coefficient := 1, powers := [(19, 1), (30, 1), (42, 1)] }, { coefficient := 1, powers := [(19, 1), (33, 1), (39, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1)] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(40, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(42, 1)] }],
  [{ coefficient := 1, powers := [(56, 1)] }],
  [{ coefficient := 1, powers := [(58, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (65, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(30, 1), (66, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 39 → SparsePoly (Fin 67) := ![
  [{ coefficient := 1, powers := [(6, 1), (12, 1), (30, 1), (34, 1)] }, { coefficient := -1, powers := [(12, 1), (13, 1), (25, 1), (30, 1), (50, 1), (62, 1)] }, { coefficient := -1, powers := [(12, 1), (13, 1), (25, 1), (30, 1)] }, { coefficient := -1, powers := [(12, 1), (20, 1), (25, 1), (30, 1), (45, 1), (50, 1), (62, 1)] }, { coefficient := -1, powers := [(12, 1), (20, 1), (25, 1), (30, 1), (45, 1)] }, { coefficient := 1, powers := [(12, 1), (25, 1), (30, 1), (43, 1)] }, { coefficient := -1, powers := [(12, 1), (28, 1), (54, 1), (62, 1)] }, { coefficient := -1, powers := [(12, 1), (30, 1), (34, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (44, 1), (55, 1), (62, 1)] }, { coefficient := -1, powers := [(25, 1), (30, 1), (49, 1), (51, 1), (62, 1), (65, 1)] }, { coefficient := 1, powers := [(30, 1), (49, 1), (51, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(21, 1), (30, 1), (53, 1), (62, 1)] }, { coefficient := 1, powers := [(24, 1), (26, 1), (53, 1), (62, 1)] }, { coefficient := -1, powers := [(24, 1), (55, 1), (62, 1)] }, { coefficient := 1, powers := [(33, 1), (39, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (20, 1), (30, 1), (44, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (12, 1), (30, 1), (34, 1), (49, 1), (66, 1)] }, { coefficient := 2, powers := [(12, 1), (13, 1), (20, 1), (25, 1), (30, 1), (46, 1), (49, 1), (66, 1)] }, { coefficient := 1, powers := [(12, 1), (25, 1), (30, 1), (34, 1), (37, 1), (46, 1), (49, 1), (66, 1)] }, { coefficient := 1, powers := [(12, 1), (25, 1), (30, 1), (43, 1), (49, 1), (66, 1)] }],
  [{ coefficient := 2, powers := [(12, 1), (13, 1), (20, 1), (21, 1), (30, 1), (46, 1), (50, 1), (62, 1)] }, { coefficient := 2, powers := [(12, 1), (13, 1), (20, 1), (21, 1), (30, 1), (46, 1)] }, { coefficient := 2, powers := [(12, 1), (13, 1), (20, 1), (21, 1), (30, 1), (50, 1), (57, 1), (62, 1)] }, { coefficient := -1, powers := [(12, 1), (13, 1), (21, 1), (30, 1), (50, 1), (62, 1)] }, { coefficient := -1, powers := [(12, 1), (13, 1), (21, 1), (30, 1)] }, { coefficient := -1, powers := [(12, 1), (20, 1), (21, 1), (30, 1), (45, 1), (50, 1), (62, 1)] }, { coefficient := 1, powers := [(12, 1), (21, 1), (30, 1), (34, 1), (37, 1), (46, 1), (50, 1), (62, 1)] }, { coefficient := 1, powers := [(12, 1), (21, 1), (30, 1), (34, 1), (37, 1), (46, 1)] }, { coefficient := 1, powers := [(12, 1), (21, 1), (30, 1), (34, 1), (37, 1), (50, 1), (57, 1), (62, 1)] }, { coefficient := 1, powers := [(12, 1), (21, 1), (30, 1), (43, 1)] }, { coefficient := -1, powers := [(12, 1), (24, 1), (54, 1), (62, 1)] }],
  [{ coefficient := 2, powers := [(12, 1), (13, 1), (20, 1), (21, 1), (30, 1), (50, 1), (62, 1)] }, { coefficient := 1, powers := [(12, 1), (21, 1), (30, 1), (34, 1), (37, 1), (50, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(30, 1), (49, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(24, 1), (26, 1)] }],
  [{ coefficient := 1, powers := [(30, 1), (49, 1), (51, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(18, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (12, 1), (54, 1), (62, 1)] }, { coefficient := -1, powers := [(18, 1), (55, 1)] }],
  [{ coefficient := -2, powers := [(12, 1), (13, 1), (20, 1), (21, 1), (30, 1), (50, 1), (62, 1), (66, 1)] }, { coefficient := -1, powers := [(12, 1), (21, 1), (30, 1), (34, 1), (37, 1), (50, 1), (62, 1), (66, 1)] }],
  [{ coefficient := -2, powers := [(9, 1), (12, 1), (13, 1), (20, 1), (30, 1), (46, 1)] }, { coefficient := 1, powers := [(9, 1), (12, 1), (13, 1), (30, 1), (50, 1), (62, 1)] }, { coefficient := 1, powers := [(9, 1), (12, 1), (13, 1), (30, 1)] }, { coefficient := 1, powers := [(9, 1), (12, 1), (20, 1), (30, 1), (45, 1), (50, 1), (62, 1)] }, { coefficient := 1, powers := [(9, 1), (12, 1), (20, 1), (30, 1), (45, 1)] }, { coefficient := -1, powers := [(9, 1), (12, 1), (30, 1), (34, 1), (37, 1), (46, 1)] }, { coefficient := -1, powers := [(9, 1), (12, 1), (30, 1), (43, 1)] }, { coefficient := -2, powers := [(12, 1), (13, 1), (20, 1), (30, 1), (40, 1), (46, 1)] }, { coefficient := 1, powers := [(12, 1), (13, 1), (30, 1), (40, 1)] }, { coefficient := -1, powers := [(12, 1), (30, 1), (34, 1), (37, 1), (40, 1), (46, 1)] }, { coefficient := -1, powers := [(12, 1), (30, 1), (40, 1), (43, 1)] }, { coefficient := 1, powers := [(12, 1), (30, 1), (43, 1), (50, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (25, 1), (30, 1), (49, 1)] }],
  [{ coefficient := -2, powers := [(12, 1), (13, 1), (20, 1), (21, 1), (30, 1), (44, 1), (50, 1), (62, 1)] }, { coefficient := -1, powers := [(12, 1), (21, 1), (30, 1), (34, 1), (37, 1), (44, 1), (50, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(55, 1)] }],
  [{ coefficient := 1, powers := [(49, 1)] }],
  [{ coefficient := 1, powers := [(30, 1)] }],
  [{ coefficient := 1, powers := [(24, 1)] }],
  [{ coefficient := -2, powers := [(12, 1), (13, 1), (20, 1), (21, 1), (30, 1), (47, 1)] }, { coefficient := 2, powers := [(12, 1), (13, 1), (20, 1), (30, 1), (49, 1)] }, { coefficient := -1, powers := [(12, 1), (21, 1), (30, 1), (34, 1), (37, 1), (47, 1)] }, { coefficient := 1, powers := [(12, 1), (30, 1), (34, 1), (37, 1), (49, 1)] }],
  [{ coefficient := 2, powers := [(12, 1), (13, 1), (20, 1), (21, 1), (30, 1), (46, 1)] }, { coefficient := 1, powers := [(12, 1), (21, 1), (30, 1), (34, 1), (37, 1), (46, 1)] }],
  [{ coefficient := 2, powers := [(12, 1), (13, 1), (20, 1), (21, 1), (30, 1), (50, 1)] }, { coefficient := 1, powers := [(12, 1), (21, 1), (30, 1), (34, 1), (37, 1), (50, 1)] }],
  [{ coefficient := -2, powers := [(12, 1), (13, 1), (20, 1), (30, 1), (46, 1)] }, { coefficient := 1, powers := [(12, 1), (13, 1), (30, 1)] }, { coefficient := 1, powers := [(12, 1), (20, 1), (30, 1), (45, 1)] }, { coefficient := -1, powers := [(12, 1), (30, 1), (34, 1), (37, 1), (46, 1)] }, { coefficient := -1, powers := [(12, 1), (30, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(12, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (30, 1), (49, 1), (50, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (13, 1), (30, 1), (49, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (20, 1), (30, 1), (49, 1)] }],
  [{ coefficient := -2, powers := [(12, 1), (13, 1), (20, 1), (21, 1), (30, 1), (44, 1), (50, 1)] }, { coefficient := -1, powers := [(12, 1), (21, 1), (30, 1), (34, 1), (37, 1), (44, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (30, 1), (49, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := 2, powers := [(9, 1), (12, 1), (13, 1), (20, 1), (30, 1), (46, 1), (49, 1)] }, { coefficient := -1, powers := [(9, 1), (12, 1), (13, 1), (30, 1), (49, 1), (50, 1), (62, 1)] }, { coefficient := -1, powers := [(9, 1), (12, 1), (13, 1), (30, 1), (49, 1)] }, { coefficient := -1, powers := [(9, 1), (12, 1), (20, 1), (30, 1), (45, 1), (49, 1), (50, 1), (62, 1)] }, { coefficient := -1, powers := [(9, 1), (12, 1), (20, 1), (30, 1), (45, 1), (49, 1)] }, { coefficient := 1, powers := [(9, 1), (12, 1), (30, 1), (34, 1), (37, 1), (46, 1), (49, 1)] }, { coefficient := 1, powers := [(9, 1), (12, 1), (30, 1), (43, 1), (49, 1)] }, { coefficient := 2, powers := [(12, 1), (13, 1), (20, 1), (21, 1), (30, 1), (38, 1), (44, 1), (50, 1), (60, 1)] }, { coefficient := 2, powers := [(12, 1), (13, 1), (20, 1), (21, 1), (30, 1), (41, 1), (44, 1), (50, 1), (57, 1)] }, { coefficient := 2, powers := [(12, 1), (13, 1), (20, 1), (21, 1), (30, 1), (44, 1), (46, 1), (50, 1), (52, 1)] }, { coefficient := -2, powers := [(12, 1), (13, 1), (20, 1), (21, 1), (30, 1), (47, 1), (50, 1), (52, 1)] }, { coefficient := 2, powers := [(12, 1), (13, 1), (20, 1), (30, 1), (40, 1), (46, 1), (49, 1)] }, { coefficient := -1, powers := [(12, 1), (13, 1), (30, 1), (40, 1), (49, 1)] }, { coefficient := 1, powers := [(12, 1), (21, 1), (30, 1), (34, 1), (37, 1), (38, 1), (44, 1), (50, 1), (60, 1)] }, { coefficient := 1, powers := [(12, 1), (21, 1), (30, 1), (34, 1), (37, 1), (41, 1), (44, 1), (50, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1), (21, 1), (30, 1), (34, 1), (37, 1), (44, 1), (46, 1), (50, 1), (52, 1)] }, { coefficient := -1, powers := [(12, 1), (21, 1), (30, 1), (34, 1), (37, 1), (47, 1), (50, 1), (52, 1)] }, { coefficient := 1, powers := [(12, 1), (30, 1), (34, 1), (37, 1), (40, 1), (46, 1), (49, 1)] }, { coefficient := -1, powers := [(12, 1), (30, 1), (37, 1), (49, 1), (59, 1)] }, { coefficient := 1, powers := [(12, 1), (30, 1), (40, 1), (43, 1), (49, 1)] }, { coefficient := -1, powers := [(12, 1), (30, 1), (40, 1), (49, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(39, 1), (61, 1)] }, { coefficient := -1, powers := [(49, 1), (55, 1)] }],
  [{ coefficient := -2, powers := [(12, 1), (13, 1), (20, 1), (21, 1), (30, 1), (44, 1), (46, 1), (50, 1)] }, { coefficient := -2, powers := [(12, 1), (13, 1), (20, 1), (21, 1), (30, 1), (44, 1), (50, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1), (13, 1), (21, 1), (30, 1), (44, 1), (50, 1)] }, { coefficient := 1, powers := [(12, 1), (20, 1), (21, 1), (30, 1), (44, 1), (45, 1), (50, 1)] }, { coefficient := -1, powers := [(12, 1), (21, 1), (30, 1), (34, 1), (37, 1), (44, 1), (46, 1), (50, 1)] }, { coefficient := -1, powers := [(12, 1), (21, 1), (30, 1), (34, 1), (37, 1), (44, 1), (50, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (44, 1), (54, 1)] }, { coefficient := -1, powers := [(18, 1), (24, 1), (44, 1), (55, 1)] }, { coefficient := 1, powers := [(18, 1), (25, 1), (30, 1), (49, 1), (51, 1), (65, 1)] }, { coefficient := -1, powers := [(18, 1), (30, 1), (49, 1), (51, 1)] }, { coefficient := 1, powers := [(19, 1), (21, 1), (30, 1), (53, 1)] }, { coefficient := -1, powers := [(19, 1), (24, 1), (26, 1), (53, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (55, 1)] }, { coefficient := -1, powers := [(19, 1), (33, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (58, 1)] }, { coefficient := 1, powers := [(8, 1), (36, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (12, 1), (30, 1), (31, 1), (49, 1)] }, { coefficient := 1, powers := [(12, 1), (20, 1), (30, 1), (49, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (33, 1)] }, { coefficient := 2, powers := [(9, 1), (12, 1), (13, 1), (20, 1), (21, 1), (29, 1), (30, 1), (50, 1), (62, 1), (66, 1)] }, { coefficient := 1, powers := [(9, 1), (12, 1), (21, 1), (29, 1), (30, 1), (34, 1), (37, 1), (50, 1), (62, 1), (66, 1)] }, { coefficient := -1, powers := [(12, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (30, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (9, 1), (12, 1), (30, 1), (34, 1), (49, 1)] }, { coefficient := 1, powers := [(6, 1), (12, 1), (30, 1), (34, 1), (40, 1), (49, 1)] }, { coefficient := 2, powers := [(9, 1), (12, 1), (13, 1), (20, 1), (21, 1), (30, 1), (47, 1), (50, 1), (62, 1)] }, { coefficient := -2, powers := [(9, 1), (12, 1), (13, 1), (20, 1), (25, 1), (30, 1), (46, 1), (49, 1)] }, { coefficient := 1, powers := [(9, 1), (12, 1), (21, 1), (30, 1), (34, 1), (37, 1), (47, 1), (50, 1), (62, 1)] }, { coefficient := -1, powers := [(9, 1), (12, 1), (25, 1), (30, 1), (34, 1), (37, 1), (46, 1), (49, 1)] }, { coefficient := -1, powers := [(9, 1), (12, 1), (25, 1), (30, 1), (43, 1), (49, 1)] }, { coefficient := -2, powers := [(12, 1), (13, 1), (20, 1), (25, 1), (30, 1), (40, 1), (46, 1), (49, 1)] }, { coefficient := -1, powers := [(12, 1), (25, 1), (30, 1), (34, 1), (37, 1), (40, 1), (46, 1), (49, 1)] }, { coefficient := -1, powers := [(12, 1), (25, 1), (30, 1), (40, 1), (43, 1), (49, 1)] }]
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
    (values : Fin 67 → R) :
    ¬ ∀ index : Fin 39,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component37.SelectedLeafB0_6_2_5.selectedHasNoCommonZero

end Krenn.Component37.SelectedLeafB0_6_2_5
