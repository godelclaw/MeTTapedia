import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component1.SelectedLeafB5_3

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "d0af373ec89c2233bf7f0e4b90f7ac7b64f44d00bd1c74207842374fcd880e96"
def certificateSHA256 : String := "cb881332f68d69dceaa59fca3b69b11693a1dabd0e922c0d5960f3f91c2b764b"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 47 → Fin 588 := ![
  1,
  25,
  27,
  32,
  35,
  37,
  40,
  47,
  48,
  218,
  219,
  220,
  224,
  225,
  229,
  260,
  264,
  265,
  276,
  292,
  354,
  371,
  382,
  384,
  385,
  386,
  392,
  425,
  448,
  493,
  503,
  507,
  521,
  545,
  546,
  548,
  550,
  559,
  560,
  564,
  579,
  581,
  582,
  584,
  585,
  586,
  587
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 47 → SparsePoly (Fin 61) := ![
  [{ coefficient := 1, powers := [(3, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(15, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (30, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (20, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(28, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(28, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1)] }, { coefficient := 1, powers := [(24, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1)] }, { coefficient := 1, powers := [(24, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (50, 1)] }, { coefficient := 1, powers := [(20, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (43, 1)] }, { coefficient := 1, powers := [(18, 1), (28, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (49, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (33, 1)] }, { coefficient := 1, powers := [(33, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (53, 1)] }, { coefficient := 1, powers := [(30, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1), (52, 1)] }, { coefficient := 1, powers := [(42, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1), (50, 1)] }, { coefficient := 1, powers := [(50, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (30, 1), (55, 1)] }, { coefficient := 1, powers := [(30, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (36, 1), (41, 1)] }, { coefficient := 1, powers := [(28, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (20, 1), (52, 1)] }, { coefficient := 1, powers := [(14, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (54, 1)] }, { coefficient := 1, powers := [(9, 1), (51, 1)] }, { coefficient := 1, powers := [(15, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (45, 1)] }, { coefficient := 1, powers := [(19, 1), (41, 1)] }, { coefficient := 1, powers := [(19, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (50, 1)] }, { coefficient := 1, powers := [(30, 1), (42, 1)] }, { coefficient := 1, powers := [(33, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (53, 1)] }, { coefficient := 1, powers := [(30, 1), (47, 1)] }, { coefficient := 1, powers := [(36, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (37, 1), (56, 1)] }, { coefficient := 1, powers := [(3, 1), (24, 1), (56, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1), (51, 1)] }, { coefficient := 1, powers := [(6, 1), (34, 1), (42, 1)] }, { coefficient := 1, powers := [(15, 1), (24, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (33, 1), (51, 1)] }, { coefficient := 1, powers := [(6, 1), (33, 1), (43, 1)] }, { coefficient := 1, powers := [(15, 1), (33, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (23, 1), (55, 1)] }, { coefficient := 1, powers := [(23, 1)] }, { coefficient := 1, powers := [(28, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (24, 1), (45, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (41, 1)] }, { coefficient := 1, powers := [(19, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (47, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1)] }, { coefficient := 1, powers := [(18, 1), (28, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (23, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (56, 1)] }, { coefficient := 1, powers := [(14, 1), (25, 1), (45, 1)] }, { coefficient := 1, powers := [(14, 1), (53, 1)] }, { coefficient := 1, powers := [(19, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (37, 1), (54, 1)] }, { coefficient := 1, powers := [(2, 1), (40, 1), (51, 1)] }, { coefficient := 1, powers := [(2, 1), (43, 1), (48, 1)] }, { coefficient := 1, powers := [(13, 1), (28, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1)] }, { coefficient := 1, powers := [(6, 1), (55, 1)] }, { coefficient := 1, powers := [(24, 1), (41, 1)] }, { coefficient := 1, powers := [(24, 1), (44, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (49, 1)] }, { coefficient := 1, powers := [(3, 1), (55, 1)] }, { coefficient := 1, powers := [(20, 1), (49, 1)] }, { coefficient := 1, powers := [(20, 1), (52, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (41, 1), (51, 1)] }, { coefficient := 1, powers := [(6, 1), (34, 1), (41, 1)] }, { coefficient := 1, powers := [(15, 1), (24, 1), (41, 1)] }, { coefficient := 1, powers := [(15, 1)] }, { coefficient := 1, powers := [(51, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (41, 1), (53, 1)] }, { coefficient := 1, powers := [(8, 1), (36, 1), (41, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (53, 1)] }, { coefficient := 1, powers := [(18, 1), (30, 1), (45, 1)] }, { coefficient := 1, powers := [(19, 1), (30, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1)] }, { coefficient := 1, powers := [(3, 1), (34, 1)] }, { coefficient := 1, powers := [(15, 1), (20, 1)] }, { coefficient := 1, powers := [(20, 1), (51, 1)] }, { coefficient := 1, powers := [(24, 1), (43, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (48, 1)] }, { coefficient := 1, powers := [(6, 1), (31, 1)] }, { coefficient := 1, powers := [(9, 1), (24, 1)] }, { coefficient := 1, powers := [(20, 1), (48, 1)] }, { coefficient := 1, powers := [(24, 1), (40, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (37, 1), (55, 1)] }, { coefficient := 1, powers := [(0, 1)] }, { coefficient := 1, powers := [(3, 1), (24, 1), (55, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1), (55, 1)] }, { coefficient := 1, powers := [(20, 1)] }, { coefficient := 1, powers := [(24, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (37, 1), (54, 1)] }, { coefficient := 1, powers := [(0, 1), (40, 1), (51, 1)] }, { coefficient := 1, powers := [(0, 1), (43, 1), (48, 1)] }, { coefficient := 1, powers := [(3, 1), (24, 1), (54, 1)] }, { coefficient := 1, powers := [(3, 1), (31, 1), (51, 1)] }, { coefficient := 1, powers := [(3, 1), (34, 1), (48, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1), (54, 1)] }, { coefficient := 1, powers := [(6, 1), (31, 1), (43, 1)] }, { coefficient := 1, powers := [(6, 1), (34, 1), (40, 1)] }, { coefficient := 1, powers := [(9, 1), (20, 1), (51, 1)] }, { coefficient := 1, powers := [(9, 1), (24, 1), (43, 1)] }, { coefficient := 1, powers := [(9, 1), (34, 1), (37, 1)] }, { coefficient := 1, powers := [(15, 1), (20, 1), (48, 1)] }, { coefficient := 1, powers := [(15, 1), (24, 1), (40, 1)] }, { coefficient := 1, powers := [(15, 1), (31, 1), (37, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (42, 1), (53, 1)] }, { coefficient := 1, powers := [(2, 1), (47, 1), (50, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (53, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1), (50, 1)] }, { coefficient := 1, powers := [(8, 1), (23, 1), (56, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (47, 1)] }, { coefficient := 1, powers := [(8, 1), (36, 1), (42, 1)] }, { coefficient := 1, powers := [(14, 1), (23, 1), (53, 1)] }, { coefficient := 1, powers := [(14, 1), (30, 1), (47, 1)] }, { coefficient := 1, powers := [(14, 1), (36, 1), (39, 1)] }, { coefficient := 1, powers := [(19, 1), (23, 1), (50, 1)] }, { coefficient := 1, powers := [(19, 1), (30, 1), (42, 1)] }, { coefficient := 1, powers := [(19, 1), (33, 1), (39, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (57, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (58, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(40, 1)] }],
  [{ coefficient := 1, powers := [(41, 1), (59, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(42, 1), (60, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 47 → SparsePoly (Fin 61) := ![
  [{ coefficient := -1, powers := [(2, 1), (24, 1), (39, 1), (49, 1), (55, 1)] }, { coefficient := 1, powers := [(2, 1), (24, 1), (39, 1), (55, 1), (57, 1)] }, { coefficient := -1, powers := [(2, 1), (39, 1), (55, 1)] }, { coefficient := -2, powers := [(5, 1), (30, 1), (55, 1)] }],
  [{ coefficient := -2, powers := [(23, 1), (25, 1)] }],
  [{ coefficient := 2, powers := [(0, 2), (5, 1), (9, 1), (33, 1), (44, 1), (53, 1), (60, 1)] }, { coefficient := -2, powers := [(0, 2), (5, 1), (33, 1), (44, 1), (48, 1), (53, 1), (60, 1)] }, { coefficient := 2, powers := [(0, 1), (5, 1), (6, 1), (9, 1), (33, 1), (53, 1), (55, 1), (60, 1)] }, { coefficient := -2, powers := [(0, 1), (5, 1), (6, 1), (33, 1), (48, 1), (53, 1), (55, 1), (60, 1)] }, { coefficient := -2, powers := [(0, 1), (5, 1), (20, 1), (33, 1), (44, 1), (48, 1), (53, 1), (60, 1)] }, { coefficient := -2, powers := [(5, 1), (6, 1), (20, 1), (33, 1), (48, 1), (53, 1), (55, 1), (60, 1)] }, { coefficient := -2, powers := [(5, 1), (20, 1), (33, 1), (48, 1), (53, 1), (60, 1)] }],
  [{ coefficient := -2, powers := [(19, 1), (29, 1), (42, 1), (58, 1), (59, 1)] }, { coefficient := 2, powers := [(42, 1), (45, 1), (59, 1)] }],
  [{ coefficient := -2, powers := [(23, 1), (44, 1), (50, 1)] }],
  [{ coefficient := 2, powers := [(14, 1), (23, 1), (52, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (5, 1), (9, 1), (15, 1), (33, 1), (41, 1), (53, 1), (60, 1)] }, { coefficient := 2, powers := [(0, 1), (5, 1), (9, 1), (15, 1), (33, 1), (44, 1), (53, 1), (60, 1)] }, { coefficient := -2, powers := [(0, 1), (5, 1), (15, 1), (33, 1), (41, 1), (48, 1), (53, 1), (60, 1)] }, { coefficient := -2, powers := [(0, 1), (5, 1), (15, 1), (33, 1), (44, 1), (48, 1), (53, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (3, 1), (39, 1), (49, 1), (55, 1), (56, 1), (60, 1)] }, { coefficient := -1, powers := [(2, 1), (3, 1), (39, 1), (55, 1), (56, 1), (57, 1), (60, 1)] }, { coefficient := 2, powers := [(2, 1), (6, 1), (47, 1), (50, 1), (55, 1), (57, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (39, 1), (49, 1), (56, 1), (60, 1)] }, { coefficient := -1, powers := [(2, 1), (39, 1), (56, 1), (57, 1), (60, 1)] }, { coefficient := 2, powers := [(3, 1), (5, 1), (33, 1), (53, 1), (54, 1), (60, 1)] }, { coefficient := 2, powers := [(5, 1), (9, 1), (15, 1), (33, 1), (53, 1), (60, 1)] }, { coefficient := -2, powers := [(5, 1), (15, 1), (20, 1), (33, 1), (41, 1), (48, 1), (53, 1), (60, 1)] }, { coefficient := -2, powers := [(5, 1), (15, 1), (20, 1), (33, 1), (44, 1), (48, 1), (53, 1), (60, 1)] }, { coefficient := -2, powers := [(5, 1), (15, 1), (33, 1), (48, 1), (53, 1), (60, 1)] }, { coefficient := -2, powers := [(5, 1), (28, 1), (45, 1), (50, 1), (55, 1), (57, 1), (59, 1), (60, 1)] }, { coefficient := -2, powers := [(5, 1), (33, 1), (43, 1), (48, 1), (53, 1), (60, 1)] }, { coefficient := -2, powers := [(8, 1), (33, 1), (47, 1), (57, 1), (60, 1)] }, { coefficient := 2, powers := [(19, 1), (28, 1), (46, 1), (49, 1), (50, 1), (60, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (5, 1), (13, 1), (33, 1), (53, 1), (58, 1)] }, { coefficient := 4, powers := [(0, 1), (5, 1), (18, 1), (33, 1), (48, 1), (53, 1), (58, 1)] }, { coefficient := 2, powers := [(5, 1), (18, 1), (20, 1), (33, 1), (48, 1), (53, 1), (58, 1)] }],
  [{ coefficient := -2, powers := [(6, 1), (18, 1), (50, 1), (55, 1)] }, { coefficient := -2, powers := [(18, 1), (50, 1)] }],
  [{ coefficient := 2, powers := [(5, 1), (28, 1), (50, 1), (55, 1), (57, 1), (59, 1)] }],
  [{ coefficient := -2, powers := [(2, 1), (6, 1), (50, 1), (55, 1), (57, 1)] }, { coefficient := 2, powers := [(8, 1), (33, 1), (57, 1)] }],
  [{ coefficient := 2, powers := [(19, 1), (23, 1), (44, 1)] }],
  [{ coefficient := -4, powers := [(0, 1), (5, 1), (33, 1), (48, 1), (53, 1), (58, 1)] }, { coefficient := -2, powers := [(5, 1), (20, 1), (33, 1), (48, 1), (53, 1), (58, 1)] }],
  [{ coefficient := 2, powers := [(19, 1), (30, 1), (42, 1), (58, 1), (59, 1)] }],
  [{ coefficient := 2, powers := [(5, 1), (9, 1), (34, 1), (53, 1)] }, { coefficient := -2, powers := [(5, 1), (31, 1), (43, 1), (53, 1)] }, { coefficient := -2, powers := [(5, 1), (34, 1), (48, 1), (53, 1)] }],
  [{ coefficient := -2, powers := [(18, 1), (42, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (20, 1), (39, 1), (56, 1), (57, 1), (60, 1)] }],
  [{ coefficient := -2, powers := [(19, 1), (23, 1)] }],
  [{ coefficient := 2, powers := [(5, 1), (56, 1)] }],
  [{ coefficient := -2, powers := [(5, 1), (50, 1), (55, 1), (59, 1)] }],
  [{ coefficient := -2, powers := [(23, 1), (53, 1)] }],
  [{ coefficient := 2, powers := [(5, 1), (20, 1), (33, 1), (53, 1)] }],
  [{ coefficient := -2, powers := [(24, 1), (28, 1), (46, 1), (50, 1)] }, { coefficient := -2, powers := [(30, 1), (42, 1), (59, 1)] }],
  [{ coefficient := 2, powers := [(19, 1)] }],
  [{ coefficient := 2, powers := [(14, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (39, 1), (49, 1), (55, 1)] }, { coefficient := -1, powers := [(2, 1), (39, 1), (55, 1), (57, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (5, 1), (9, 1), (33, 1), (41, 1), (53, 1), (60, 1)] }, { coefficient := 2, powers := [(0, 1), (5, 1), (33, 1), (41, 1), (48, 1), (53, 1), (60, 1)] }, { coefficient := -2, powers := [(5, 1), (9, 1), (33, 1), (53, 1), (60, 1)] }, { coefficient := 2, powers := [(5, 1), (20, 1), (33, 1), (41, 1), (48, 1), (53, 1), (60, 1)] }, { coefficient := 2, powers := [(5, 1), (33, 1), (48, 1), (53, 1), (60, 1)] }],
  [{ coefficient := 2, powers := [(5, 1), (31, 1), (53, 1)] }],
  [{ coefficient := -2, powers := [(19, 1), (50, 1)] }],
  [{ coefficient := 2, powers := [(28, 1), (46, 1), (50, 1)] }],
  [{ coefficient := 2, powers := [(6, 1), (50, 1), (55, 1)] }, { coefficient := 2, powers := [(50, 1)] }],
  [{ coefficient := 2, powers := [(23, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (5, 1), (33, 1), (53, 1), (58, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (5, 1), (9, 1), (15, 1), (33, 1), (53, 1)] }, { coefficient := 2, powers := [(0, 1), (5, 1), (15, 1), (33, 1), (48, 1), (53, 1)] }, { coefficient := 2, powers := [(5, 1), (15, 1), (20, 1), (33, 1), (48, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (39, 1), (56, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (5, 1), (9, 1), (33, 1), (53, 1)] }, { coefficient := -2, powers := [(0, 1), (5, 1), (33, 1), (48, 1), (53, 1)] }, { coefficient := -2, powers := [(5, 1), (20, 1), (33, 1), (48, 1), (53, 1)] }],
  [{ coefficient := 2, powers := [(42, 1), (59, 1)] }],
  [{ coefficient := 2, powers := [(5, 1), (33, 1), (48, 1), (53, 1)] }],
  [{ coefficient := 2, powers := [(5, 1), (33, 1), (43, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (39, 1), (49, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (39, 1), (56, 1), (57, 1)] }],
  [{ coefficient := -2, powers := [(5, 1), (33, 1), (53, 1)] }],
  [{ coefficient := -2, powers := [] }],
  [{ coefficient := 2, powers := [(2, 1), (6, 1), (47, 1), (50, 1), (55, 1)] }, { coefficient := 1, powers := [(2, 1), (20, 1), (39, 1), (42, 1), (52, 1), (56, 1), (60, 1)] }, { coefficient := -1, powers := [(2, 1), (39, 1), (56, 1)] }, { coefficient := -2, powers := [(5, 1), (28, 1), (45, 1), (50, 1), (55, 1), (59, 1)] }, { coefficient := -2, powers := [(8, 1), (33, 1), (47, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (5, 1), (33, 1), (37, 1), (53, 1), (54, 1)] }, { coefficient := 2, powers := [(0, 1), (5, 1), (33, 1), (43, 1), (48, 1), (53, 1)] }, { coefficient := 2, powers := [(5, 1), (20, 1), (33, 1), (43, 1), (48, 1), (53, 1)] }, { coefficient := -2, powers := [(19, 1), (30, 1), (42, 1), (49, 1), (59, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (2, 1), (5, 1), (33, 1), (51, 1), (53, 1), (58, 1)] }, { coefficient := 2, powers := [(0, 1), (5, 1), (33, 1), (51, 1), (53, 1)] }, { coefficient := 2, powers := [(5, 1), (6, 1), (33, 1), (34, 1), (53, 1)] }, { coefficient := 2, powers := [(5, 1), (15, 1), (24, 1), (33, 1), (53, 1)] }, { coefficient := -2, powers := [(5, 1), (24, 1), (33, 1), (43, 1), (53, 1)] }],
  [{ coefficient := -2, powers := [(2, 1), (42, 1), (53, 1)] }, { coefficient := 2, powers := [(5, 1), (6, 1), (36, 1), (50, 1), (55, 1)] }, { coefficient := -2, powers := [(8, 1), (36, 1), (42, 1)] }],
  [{ coefficient := -2, powers := [(0, 2), (5, 1), (9, 1), (15, 1), (33, 1), (44, 1), (53, 1)] }, { coefficient := 2, powers := [(0, 2), (5, 1), (9, 1), (33, 1), (41, 1), (51, 1), (53, 1)] }, { coefficient := 2, powers := [(0, 2), (5, 1), (15, 1), (33, 1), (44, 1), (48, 1), (53, 1)] }, { coefficient := -2, powers := [(0, 2), (5, 1), (33, 1), (41, 1), (48, 1), (51, 1), (53, 1)] }, { coefficient := -2, powers := [(0, 1), (5, 1), (6, 1), (9, 1), (15, 1), (33, 1), (53, 1), (55, 1)] }, { coefficient := 2, powers := [(0, 1), (5, 1), (6, 1), (9, 1), (33, 1), (34, 1), (41, 1), (53, 1)] }, { coefficient := 2, powers := [(0, 1), (5, 1), (6, 1), (15, 1), (33, 1), (48, 1), (53, 1), (55, 1)] }, { coefficient := -2, powers := [(0, 1), (5, 1), (6, 1), (33, 1), (34, 1), (41, 1), (48, 1), (53, 1)] }, { coefficient := -2, powers := [(0, 1), (5, 1), (9, 1), (15, 1), (24, 1), (33, 1), (44, 1), (53, 1)] }, { coefficient := 2, powers := [(0, 1), (5, 1), (9, 1), (33, 1), (51, 1), (53, 1)] }, { coefficient := 2, powers := [(0, 1), (5, 1), (15, 1), (20, 1), (33, 1), (44, 1), (48, 1), (53, 1)] }, { coefficient := 2, powers := [(0, 1), (5, 1), (15, 1), (24, 1), (33, 1), (44, 1), (48, 1), (53, 1)] }, { coefficient := -2, powers := [(0, 1), (5, 1), (20, 1), (33, 1), (41, 1), (48, 1), (51, 1), (53, 1)] }, { coefficient := -2, powers := [(0, 1), (5, 1), (33, 1), (48, 1), (51, 1), (53, 1)] }, { coefficient := -1, powers := [(2, 1), (3, 1), (24, 1), (39, 1), (49, 1), (55, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (3, 1), (24, 1), (39, 1), (55, 1), (56, 1), (57, 1)] }, { coefficient := -2, powers := [(2, 1), (6, 1), (24, 1), (47, 1), (50, 1), (55, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (20, 1), (39, 1), (52, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (20, 1), (39, 1), (56, 1), (57, 1)] }, { coefficient := -1, powers := [(2, 1), (24, 1), (39, 1), (49, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (24, 1), (39, 1), (56, 1), (57, 1)] }, { coefficient := -2, powers := [(3, 1), (5, 1), (24, 1), (33, 1), (53, 1), (54, 1)] }, { coefficient := 2, powers := [(5, 1), (6, 1), (9, 1), (33, 1), (34, 1), (53, 1)] }, { coefficient := 2, powers := [(5, 1), (6, 1), (15, 1), (20, 1), (33, 1), (48, 1), (53, 1), (55, 1)] }, { coefficient := -2, powers := [(5, 1), (6, 1), (20, 1), (33, 1), (34, 1), (41, 1), (48, 1), (53, 1)] }, { coefficient := -2, powers := [(5, 1), (6, 1), (33, 1), (34, 1), (48, 1), (53, 1)] }, { coefficient := 2, powers := [(5, 1), (15, 1), (20, 1), (24, 1), (33, 1), (44, 1), (48, 1), (53, 1)] }, { coefficient := 2, powers := [(5, 1), (15, 1), (20, 1), (33, 1), (48, 1), (53, 1)] }, { coefficient := 2, powers := [(5, 1), (24, 1), (28, 1), (45, 1), (50, 1), (55, 1), (57, 1), (59, 1)] }, { coefficient := 2, powers := [(5, 1), (24, 1), (33, 1), (43, 1), (48, 1), (53, 1)] }, { coefficient := 2, powers := [(8, 1), (24, 1), (33, 1), (47, 1), (57, 1)] }, { coefficient := -2, powers := [(19, 1), (24, 1), (28, 1), (46, 1), (49, 1), (50, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
/-- Lean replays the exact selected-row integer certificate. -/
theorem constantIdentity :
    ∑ index, (multipliers index).toPoly *
      (selectedEquations index).toPoly = C (2 : ℤ) := by
  simp (config := { maxSteps := 1000000 })
    [Fin.sum_univ_succ, multipliers, selectedEquations,
    SparsePoly.toPoly, SparseTerm.toPoly]
  ring

/-- The selected rows have no common zero in a characteristic-zero ring. -/
theorem selectedHasNoCommonZero {R : Type*} [CommRing R] [Nontrivial R] [CharZero R]
    (values : Fin 61 → R) :
    ¬ ∀ index : Fin 47,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((2 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (2 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (2 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component1.SelectedLeafB5_3.selectedHasNoCommonZero

end Krenn.Component1.SelectedLeafB5_3
