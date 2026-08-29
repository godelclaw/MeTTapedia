import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component25.SelectedLeafB7_1

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "18e3be10339294fad0ac7ad40d18befcc23234bb5b86d560e5ead8e33096f145"
def certificateSHA256 : String := "22d588de7bcd6ee53f22c77fac5a78f9ff2c9c757337ef685cb1e4c034b89a23"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 40 → Fin 662 := ![
  5,
  10,
  11,
  12,
  21,
  143,
  146,
  147,
  148,
  162,
  170,
  175,
  294,
  312,
  319,
  402,
  422,
  423,
  424,
  427,
  433,
  449,
  450,
  451,
  463,
  467,
  469,
  475,
  578,
  579,
  609,
  637,
  643,
  647,
  655,
  656,
  657,
  658,
  660,
  661
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 40 → SparsePoly (Fin 65) := ![
  [{ coefficient := 1, powers := [(10, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (43, 1)] }, { coefficient := 1, powers := [(10, 1), (25, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (50, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (53, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (54, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (18, 1)] }, { coefficient := 1, powers := [(16, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (43, 1)] }, { coefficient := 1, powers := [(27, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(57, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (50, 1)] }, { coefficient := 1, powers := [(18, 1), (50, 1)] }, { coefficient := 1, powers := [(24, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (57, 1)] }, { coefficient := 1, powers := [(29, 1), (48, 1)] }, { coefficient := 1, powers := [(35, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1), (50, 1)] }, { coefficient := 1, powers := [(24, 1), (45, 1), (50, 1)] }, { coefficient := 1, powers := [(50, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (18, 1), (52, 1)] }, { coefficient := 1, powers := [(16, 1), (18, 1), (56, 1)] }, { coefficient := 1, powers := [(16, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1)] }, { coefficient := 1, powers := [(24, 1), (40, 1), (43, 1)] }, { coefficient := 1, powers := [(24, 1), (46, 1)] }, { coefficient := 1, powers := [(43, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1)] }, { coefficient := 1, powers := [(6, 1), (19, 1), (59, 1)] }, { coefficient := 1, powers := [(19, 1)] }, { coefficient := 1, powers := [(24, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (53, 1)] }, { coefficient := 1, powers := [(18, 1), (50, 1), (56, 1)] }, { coefficient := 1, powers := [(18, 1), (53, 1)] }, { coefficient := 1, powers := [(50, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (45, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1), (40, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1), (45, 1)] }, { coefficient := 1, powers := [(16, 1), (28, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (52, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1), (52, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1), (56, 1)] }, { coefficient := 1, powers := [(16, 1), (28, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (40, 1)] }, { coefficient := 1, powers := [(16, 1), (45, 1)] }, { coefficient := 1, powers := [(16, 1), (52, 1)] }, { coefficient := 1, powers := [(16, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (54, 1)] }, { coefficient := 1, powers := [(29, 1), (41, 1)] }, { coefficient := 1, powers := [(29, 1), (47, 1), (50, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(28, 1), (40, 1)] }, { coefficient := 1, powers := [(28, 1), (45, 1)] }, { coefficient := 1, powers := [(28, 1), (52, 1)] }, { coefficient := 1, powers := [(28, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1), (50, 1)] }, { coefficient := 1, powers := [(6, 1), (60, 1)] }, { coefficient := 1, powers := [(24, 1), (46, 1), (50, 1)] }, { coefficient := 1, powers := [(43, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1), (50, 1)] }, { coefficient := 1, powers := [(19, 1), (50, 1)] }, { coefficient := 1, powers := [(24, 1), (41, 1)] }, { coefficient := 1, powers := [(24, 1), (47, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1), (52, 1)] }, { coefficient := 1, powers := [(19, 1), (52, 1)] }, { coefficient := 1, powers := [(19, 1), (56, 1)] }, { coefficient := 1, powers := [(47, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (36, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1)] }, { coefficient := 1, powers := [(6, 1), (59, 1)] }, { coefficient := 1, powers := [(24, 1), (40, 1)] }, { coefficient := 1, powers := [(24, 1), (45, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (52, 1)] }, { coefficient := 1, powers := [(3, 1), (59, 1)] }, { coefficient := 1, powers := [(18, 1), (52, 1)] }, { coefficient := 1, powers := [(18, 1), (56, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (41, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (47, 1), (53, 1)] }, { coefficient := 1, powers := [(19, 1), (50, 1), (56, 1)] }, { coefficient := 1, powers := [(19, 1), (53, 1)] }, { coefficient := 1, powers := [(41, 1)] }, { coefficient := 1, powers := [(47, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (23, 1), (60, 1)] }, { coefficient := 1, powers := [(6, 1), (32, 1), (48, 1)] }, { coefficient := 1, powers := [(6, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(23, 1), (43, 1), (50, 1)] }, { coefficient := 1, powers := [(27, 1), (41, 1), (43, 1)] }, { coefficient := 1, powers := [(27, 1), (48, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (37, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (40, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (45, 1), (52, 1)] }, { coefficient := 1, powers := [(40, 1)] }, { coefficient := 1, powers := [(45, 1)] }, { coefficient := 1, powers := [(52, 1)] }, { coefficient := 1, powers := [(56, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (37, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (40, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (45, 1), (52, 1)] }, { coefficient := 1, powers := [(16, 1), (28, 1), (40, 1)] }, { coefficient := 1, powers := [(16, 1), (28, 1), (45, 1)] }, { coefficient := 1, powers := [(16, 1), (28, 1), (52, 1)] }, { coefficient := 1, powers := [(16, 1), (28, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (41, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (48, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (23, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (48, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(12, 1), (23, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1), (29, 1), (48, 1)] }, { coefficient := 1, powers := [(12, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(17, 1), (23, 1), (54, 1)] }, { coefficient := 1, powers := [(17, 1), (29, 1), (41, 1)] }, { coefficient := 1, powers := [(17, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (61, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(40, 1)] }],
  [{ coefficient := 1, powers := [(41, 1), (64, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 40 → SparsePoly (Fin 65) := ![
  [{ coefficient := 1, powers := [(8, 1), (25, 1), (27, 1), (36, 1), (41, 1), (59, 2), (62, 1)] }, { coefficient := -1, powers := [(8, 1), (25, 1), (27, 1), (41, 1), (59, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (20, 1), (47, 1), (59, 1), (62, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(18, 1), (20, 1), (47, 1), (62, 1), (64, 1)] }, { coefficient := 1, powers := [(19, 1), (20, 1), (62, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (6, 1), (20, 1), (36, 1), (48, 1), (59, 2), (62, 1)] }, { coefficient := 1, powers := [(2, 1), (6, 1), (20, 1), (48, 1), (59, 1), (62, 1)] }, { coefficient := -1, powers := [(5, 1), (6, 1), (20, 1), (35, 1), (36, 1), (59, 2), (62, 1)] }, { coefficient := 1, powers := [(5, 1), (6, 1), (20, 1), (35, 1), (59, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (17, 1), (36, 1), (50, 1), (59, 2)] }, { coefficient := 1, powers := [(6, 1), (17, 1), (50, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (27, 1), (36, 1), (41, 1), (59, 2), (62, 1)] }, { coefficient := 1, powers := [(8, 1), (27, 1), (41, 1), (59, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (47, 1), (59, 1), (62, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (47, 1), (62, 1), (64, 1)] }, { coefficient := -1, powers := [(19, 1), (62, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (6, 1), (36, 1), (48, 1), (59, 2), (62, 1)] }, { coefficient := -1, powers := [(2, 1), (6, 1), (48, 1), (59, 1), (62, 1)] }, { coefficient := 1, powers := [(5, 1), (6, 1), (35, 1), (36, 1), (59, 2), (62, 1)] }, { coefficient := -1, powers := [(5, 1), (6, 1), (35, 1), (59, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(16, 1), (22, 2), (52, 1), (63, 2)] }, { coefficient := -1, powers := [(16, 1), (22, 2), (56, 1), (63, 2)] }, { coefficient := -1, powers := [(16, 1), (22, 1), (27, 1), (52, 1), (63, 2)] }, { coefficient := -1, powers := [(16, 1), (22, 1), (27, 1), (56, 1), (63, 2)] }, { coefficient := -1, powers := [(16, 1), (22, 1), (28, 1), (63, 2)] }, { coefficient := -1, powers := [(16, 1), (27, 1), (28, 1), (63, 2)] }, { coefficient := -1, powers := [(22, 1), (36, 1), (52, 1), (59, 1), (63, 1)] }, { coefficient := -1, powers := [(22, 1), (36, 1), (56, 1), (59, 1), (63, 1)] }, { coefficient := 1, powers := [(27, 1), (52, 1), (63, 1)] }, { coefficient := 1, powers := [(27, 1), (56, 1), (63, 1)] }, { coefficient := -1, powers := [(28, 1), (36, 1), (59, 1), (63, 1)] }, { coefficient := -1, powers := [(28, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (36, 1), (50, 1), (59, 2)] }, { coefficient := 1, powers := [(8, 1), (50, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (6, 1), (36, 1), (41, 1), (59, 2)] }, { coefficient := -1, powers := [(2, 1), (6, 1), (41, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (6, 1), (32, 1), (36, 1), (59, 2)] }, { coefficient := -1, powers := [(5, 1), (6, 1), (32, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(47, 1), (52, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (12, 1), (36, 1), (59, 2)] }, { coefficient := -1, powers := [(6, 1), (12, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (19, 1), (22, 1), (52, 1), (63, 1), (64, 1)] }, { coefficient := 1, powers := [(16, 1), (19, 1), (22, 1), (56, 1), (63, 1), (64, 1)] }, { coefficient := 1, powers := [(16, 1), (19, 1), (27, 1), (52, 1), (63, 1), (64, 1)] }, { coefficient := 1, powers := [(16, 1), (19, 1), (27, 1), (56, 1), (63, 1), (64, 1)] }, { coefficient := -1, powers := [(19, 1), (36, 1), (45, 1), (59, 1), (64, 1)] }, { coefficient := 1, powers := [(19, 1), (45, 1), (64, 1)] }, { coefficient := 1, powers := [(19, 1), (52, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(22, 1), (63, 1)] }, { coefficient := -1, powers := [(27, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (36, 1), (38, 1), (50, 1), (59, 2)] }, { coefficient := 1, powers := [(2, 1), (38, 1), (50, 1), (59, 1)] }, { coefficient := -1, powers := [(5, 1), (29, 1), (36, 1), (50, 1), (59, 2)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (50, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (22, 1), (50, 1), (52, 1), (63, 1), (64, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1), (50, 1), (56, 1), (63, 1), (64, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1), (50, 1), (52, 1), (63, 1), (64, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1), (50, 1), (56, 1), (63, 1), (64, 1)] }, { coefficient := -1, powers := [(36, 1), (45, 1), (50, 1), (59, 1), (64, 1)] }, { coefficient := 1, powers := [(45, 1), (50, 1), (64, 1)] }, { coefficient := 1, powers := [(50, 1), (52, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(47, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (63, 1)] }, { coefficient := 1, powers := [(16, 1), (18, 1), (22, 1), (63, 2)] }, { coefficient := 1, powers := [(16, 1), (18, 1), (27, 1), (63, 2)] }, { coefficient := 1, powers := [(16, 1), (22, 1), (24, 1), (63, 2)] }, { coefficient := 1, powers := [(16, 1), (24, 1), (27, 1), (63, 2)] }, { coefficient := 1, powers := [(18, 1), (36, 1), (59, 1), (63, 1)] }, { coefficient := 1, powers := [(18, 1), (63, 1)] }, { coefficient := 1, powers := [(24, 1), (36, 1), (59, 1), (63, 1)] }, { coefficient := 1, powers := [(24, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (27, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (17, 1), (36, 1), (59, 2)] }, { coefficient := -1, powers := [(6, 1), (17, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(0, 2), (16, 1), (36, 1), (59, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (36, 1), (38, 1), (59, 2)] }, { coefficient := -1, powers := [(2, 1), (38, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (36, 1), (59, 2)] }, { coefficient := -1, powers := [(5, 1), (29, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(16, 1), (22, 1), (52, 1), (63, 1), (64, 1)] }, { coefficient := -1, powers := [(16, 1), (22, 1), (56, 1), (63, 1), (64, 1)] }, { coefficient := -1, powers := [(16, 1), (27, 1), (52, 1), (63, 1), (64, 1)] }, { coefficient := -1, powers := [(16, 1), (27, 1), (56, 1), (63, 1), (64, 1)] }, { coefficient := 1, powers := [(36, 1), (45, 1), (59, 1), (64, 1)] }, { coefficient := -1, powers := [(45, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(50, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (52, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (56, 1), (63, 1)] }, { coefficient := -1, powers := [(18, 1), (52, 1), (63, 1)] }, { coefficient := -1, powers := [(24, 1), (52, 1), (63, 1)] }, { coefficient := 1, powers := [(63, 1)] }],
  [{ coefficient := -1, powers := [(16, 1), (19, 1), (22, 1), (50, 1), (52, 1), (63, 1), (64, 1)] }, { coefficient := -1, powers := [(16, 1), (19, 1), (22, 1), (50, 1), (56, 1), (63, 1), (64, 1)] }, { coefficient := -1, powers := [(16, 1), (19, 1), (27, 1), (50, 1), (52, 1), (63, 1), (64, 1)] }, { coefficient := -1, powers := [(16, 1), (19, 1), (27, 1), (50, 1), (56, 1), (63, 1), (64, 1)] }, { coefficient := 1, powers := [(19, 1), (36, 1), (45, 1), (50, 1), (59, 1), (64, 1)] }, { coefficient := -1, powers := [(19, 1), (45, 1), (50, 1), (64, 1)] }, { coefficient := -1, powers := [(19, 1), (50, 1), (52, 1), (64, 1)] }, { coefficient := -1, powers := [(36, 1), (59, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(47, 1), (50, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(64, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (36, 1), (59, 2)] }, { coefficient := -1, powers := [(8, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(0, 2), (36, 1), (59, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(0, 2), (36, 1), (59, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (36, 1), (59, 2)] }, { coefficient := 1, powers := [(6, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(0, 2), (36, 1), (37, 1), (59, 2)] }, { coefficient := -1, powers := [(0, 2), (36, 1), (45, 1), (52, 1), (59, 1)] }, { coefficient := -1, powers := [(0, 1), (36, 1), (45, 1), (59, 1)] }, { coefficient := -1, powers := [(0, 1), (36, 1), (52, 1), (59, 1)] }, { coefficient := -1, powers := [(0, 1), (36, 1), (56, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (6, 1), (36, 1), (48, 1), (54, 1), (59, 2)] }, { coefficient := 1, powers := [(2, 1), (6, 1), (48, 1), (54, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (47, 1), (50, 1), (59, 1), (64, 1)] }, { coefficient := -1, powers := [(5, 1), (6, 1), (35, 1), (36, 1), (54, 1), (59, 2)] }, { coefficient := 1, powers := [(5, 1), (6, 1), (35, 1), (54, 1), (59, 1)] }, { coefficient := 1, powers := [(8, 1), (27, 1), (36, 1), (41, 1), (43, 1), (59, 2)] }, { coefficient := -1, powers := [(8, 1), (27, 1), (41, 1), (43, 1), (59, 1)] }, { coefficient := -1, powers := [(18, 1), (47, 1), (53, 1), (64, 1)] }, { coefficient := 1, powers := [(19, 1), (53, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(0, 2), (36, 1), (37, 1), (59, 2)] }, { coefficient := 1, powers := [(0, 2), (36, 1), (45, 1), (52, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (36, 1), (52, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (36, 1), (56, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (45, 1)] }, { coefficient := 1, powers := [(0, 1), (56, 1)] }, { coefficient := -1, powers := [(16, 1), (18, 1), (22, 1), (52, 1), (63, 1)] }, { coefficient := -1, powers := [(16, 1), (18, 1), (27, 1), (52, 1), (63, 1)] }, { coefficient := -1, powers := [(16, 1), (22, 1), (24, 1), (52, 1), (63, 1)] }, { coefficient := -1, powers := [(16, 1), (24, 1), (27, 1), (52, 1), (63, 1)] }, { coefficient := -1, powers := [(36, 1), (59, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(0, 3), (36, 1), (56, 1), (59, 1), (61, 1)] }, { coefficient := 1, powers := [(0, 2), (2, 1), (36, 1), (56, 1), (59, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 2), (36, 1), (59, 1), (61, 1)] }, { coefficient := -1, powers := [(0, 1), (2, 1), (6, 1), (36, 1), (41, 1), (57, 1), (59, 2)] }, { coefficient := 1, powers := [(0, 1), (2, 1), (6, 1), (41, 1), (57, 1), (59, 1)] }, { coefficient := -1, powers := [(0, 1), (5, 1), (6, 1), (32, 1), (36, 1), (57, 1), (59, 2)] }, { coefficient := 1, powers := [(0, 1), (5, 1), (6, 1), (32, 1), (57, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (24, 1), (36, 1), (38, 1), (43, 1), (50, 1), (59, 2)] }, { coefficient := -1, powers := [(2, 1), (24, 1), (38, 1), (43, 1), (50, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (24, 1), (29, 1), (36, 1), (43, 1), (50, 1), (59, 2)] }, { coefficient := -1, powers := [(5, 1), (24, 1), (29, 1), (43, 1), (50, 1), (59, 1)] }, { coefficient := 1, powers := [(16, 1), (19, 1), (22, 1), (24, 1), (50, 1), (52, 1), (63, 1), (64, 1)] }, { coefficient := 1, powers := [(16, 1), (19, 1), (22, 1), (24, 1), (50, 1), (56, 1), (63, 1), (64, 1)] }, { coefficient := 1, powers := [(16, 1), (19, 1), (24, 1), (27, 1), (50, 1), (52, 1), (63, 1), (64, 1)] }, { coefficient := 1, powers := [(16, 1), (19, 1), (24, 1), (27, 1), (50, 1), (56, 1), (63, 1), (64, 1)] }, { coefficient := -1, powers := [(19, 1), (24, 1), (36, 1), (45, 1), (50, 1), (59, 1), (64, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (45, 1), (50, 1), (64, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (50, 1), (52, 1), (64, 1)] }, { coefficient := 1, powers := [(24, 1), (36, 1), (59, 1)] }, { coefficient := -1, powers := [(24, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (56, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1), (24, 1), (52, 1), (63, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1), (24, 1), (56, 1), (63, 1)] }, { coefficient := 1, powers := [(16, 1), (24, 1), (27, 1), (52, 1), (63, 1)] }, { coefficient := 1, powers := [(16, 1), (24, 1), (27, 1), (56, 1), (63, 1)] }, { coefficient := -1, powers := [(24, 1), (36, 1), (45, 1), (59, 1)] }, { coefficient := 1, powers := [(24, 1), (45, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
/-- Lean replays the exact selected-row integer certificate. -/
theorem constantIdentity :
    ∑ index, (multipliers index).toPoly *
      (selectedEquations index).toPoly = C (3 : ℤ) := by
  simp (config := { maxSteps := 1000000 })
    [Fin.sum_univ_succ, multipliers, selectedEquations,
    SparsePoly.toPoly, SparseTerm.toPoly]
  ring

/-- The selected rows have no common zero in a characteristic-zero ring. -/
theorem selectedHasNoCommonZero {R : Type*} [CommRing R] [Nontrivial R] [CharZero R]
    (values : Fin 65 → R) :
    ¬ ∀ index : Fin 40,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((3 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (3 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (3 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component25.SelectedLeafB7_1.selectedHasNoCommonZero

end Krenn.Component25.SelectedLeafB7_1
