import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component25.SelectedLeafB5_7_3

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "8b685ba33140553715e34f7eecadb132e619852cb203ef88783fde2bf934e18b"
def certificateSHA256 : String := "0e56843675bbd70c9730b21ef3911a916ffe2163c88de2e4657107f7719e58dc"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 42 → Fin 665 := ![
  2,
  14,
  15,
  16,
  17,
  21,
  142,
  152,
  162,
  170,
  173,
  175,
  294,
  300,
  311,
  312,
  319,
  388,
  423,
  427,
  429,
  430,
  435,
  438,
  439,
  440,
  449,
  450,
  467,
  475,
  578,
  580,
  588,
  648,
  655,
  656,
  658,
  659,
  660,
  661,
  663,
  664
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 42 → SparsePoly (Fin 68) := ![
  [{ coefficient := 1, powers := [(9, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (54, 1)] }, { coefficient := 1, powers := [(18, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (29, 1)] }, { coefficient := 1, powers := [(29, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (18, 1)] }, { coefficient := 1, powers := [(16, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (43, 1)] }, { coefficient := 1, powers := [(27, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (40, 1)] }, { coefficient := 1, powers := [(29, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(57, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (50, 1)] }, { coefficient := 1, powers := [(18, 1), (50, 1)] }, { coefficient := 1, powers := [(24, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (60, 1)] }, { coefficient := 1, powers := [(12, 1), (57, 1)] }, { coefficient := 1, powers := [(17, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (52, 1)] }, { coefficient := 1, powers := [(23, 1), (56, 1)] }, { coefficient := 1, powers := [(28, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (57, 1)] }, { coefficient := 1, powers := [(29, 1), (48, 1)] }, { coefficient := 1, powers := [(35, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1), (50, 1)] }, { coefficient := 1, powers := [(24, 1), (45, 1), (50, 1)] }, { coefficient := 1, powers := [(50, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (18, 1), (56, 1)] }, { coefficient := 1, powers := [(12, 1)] }, { coefficient := 1, powers := [(16, 1), (18, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1)] }, { coefficient := 1, powers := [(6, 1), (19, 1), (59, 1)] }, { coefficient := 1, powers := [(19, 1)] }, { coefficient := 1, powers := [(24, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (45, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1), (40, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1), (45, 1)] }, { coefficient := 1, powers := [(16, 1), (28, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (47, 1)] }, { coefficient := 1, powers := [(5, 1), (27, 1), (59, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (48, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1), (48, 1)] }, { coefficient := 1, powers := [(17, 1), (23, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1)] }, { coefficient := 1, powers := [(12, 1), (29, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (59, 1)] }, { coefficient := 1, powers := [(16, 1), (19, 1), (52, 1)] }, { coefficient := 1, powers := [(16, 1), (19, 1), (56, 1)] }, { coefficient := 1, powers := [(16, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (60, 1)] }, { coefficient := 1, powers := [(12, 1), (48, 1)] }, { coefficient := 1, powers := [(17, 1), (19, 1), (53, 1)] }, { coefficient := 1, powers := [(17, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (32, 1)] }, { coefficient := 1, powers := [(22, 1), (50, 1)] }, { coefficient := 1, powers := [(27, 1), (50, 1)] }, { coefficient := 1, powers := [(32, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (40, 1)] }, { coefficient := 1, powers := [(16, 1), (45, 1)] }, { coefficient := 1, powers := [(16, 1), (52, 1)] }, { coefficient := 1, powers := [(16, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (54, 1)] }, { coefficient := 1, powers := [(29, 1), (41, 1)] }, { coefficient := 1, powers := [(29, 1), (47, 1), (50, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1), (50, 1)] }, { coefficient := 1, powers := [(19, 1), (50, 1)] }, { coefficient := 1, powers := [(24, 1), (41, 1)] }, { coefficient := 1, powers := [(24, 1), (47, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (36, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1)] }, { coefficient := 1, powers := [(6, 1), (59, 1)] }, { coefficient := 1, powers := [(24, 1), (40, 1)] }, { coefficient := 1, powers := [(24, 1), (45, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (38, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (41, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (48, 1), (54, 1)] }, { coefficient := 1, powers := [(19, 1), (43, 1), (54, 1)] }, { coefficient := 1, powers := [(19, 1), (50, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (40, 1)] }, { coefficient := 1, powers := [(16, 1), (28, 1), (57, 1)] }, { coefficient := 1, powers := [(16, 1), (29, 1), (46, 1)] }, { coefficient := 1, powers := [(17, 1), (29, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (41, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (47, 1), (53, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (56, 1)] }, { coefficient := 1, powers := [(12, 1), (23, 1), (56, 1)] }, { coefficient := 1, powers := [(12, 1), (28, 1), (47, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1), (53, 1)] }, { coefficient := 1, powers := [(16, 1), (28, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (41, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (48, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (23, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (48, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(12, 1), (23, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1), (29, 1), (48, 1)] }, { coefficient := 1, powers := [(12, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(17, 1), (23, 1), (54, 1)] }, { coefficient := 1, powers := [(17, 1), (29, 1), (41, 1)] }, { coefficient := 1, powers := [(17, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (61, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(39, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(40, 1), (64, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(41, 1), (65, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(56, 1), (66, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(57, 1), (67, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 42 → SparsePoly (Fin 68) := ![
  [{ coefficient := -2, powers := [(6, 1), (12, 1), (29, 1), (48, 1), (59, 1), (63, 1), (67, 1)] }, { coefficient := 1, powers := [(6, 1), (17, 1), (29, 1), (41, 1), (45, 1), (59, 1), (63, 1), (64, 1), (67, 1)] }, { coefficient := -1, powers := [(6, 1), (17, 1), (29, 1), (41, 1), (59, 1), (63, 1), (67, 1)] }, { coefficient := -2, powers := [(12, 1), (29, 1), (36, 1), (48, 1), (59, 1), (63, 1), (67, 1)] }, { coefficient := 1, powers := [(17, 1), (29, 1), (36, 1), (41, 1), (45, 1), (59, 1), (63, 1), (64, 1), (67, 1)] }, { coefficient := -1, powers := [(17, 1), (29, 1), (36, 1), (41, 1), (59, 1), (63, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (22, 1), (48, 1), (59, 1)] }, { coefficient := 1, powers := [(22, 1), (36, 1), (48, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (27, 1), (52, 1), (62, 1), (67, 1)] }, { coefficient := -1, powers := [(0, 1), (27, 1), (56, 1), (62, 1), (67, 1)] }, { coefficient := 1, powers := [(0, 1), (28, 1), (62, 1), (67, 1)] }, { coefficient := -1, powers := [(6, 1), (19, 1), (27, 1), (52, 1), (53, 1), (57, 1), (59, 1), (66, 1), (67, 1)] }, { coefficient := -1, powers := [(6, 1), (19, 1), (27, 1), (53, 1), (56, 1), (57, 1), (59, 1), (66, 1), (67, 1)] }, { coefficient := 1, powers := [(6, 1), (23, 1), (24, 1), (52, 1), (53, 1), (57, 1), (59, 1), (66, 1), (67, 1)] }, { coefficient := 1, powers := [(6, 1), (23, 1), (24, 1), (53, 1), (57, 1), (59, 1), (67, 1)] }, { coefficient := -1, powers := [(6, 1), (23, 1), (43, 1), (54, 1), (59, 1), (67, 1)] }, { coefficient := -1, powers := [(6, 1), (28, 1), (41, 1), (57, 1), (59, 1), (66, 1), (67, 1)] }, { coefficient := 1, powers := [(6, 1), (28, 1), (41, 1), (59, 1), (64, 1)] }, { coefficient := 1, powers := [(6, 1), (29, 1), (41, 1), (46, 1), (59, 1), (64, 1), (67, 1)] }, { coefficient := -1, powers := [(19, 1), (27, 1), (36, 1), (52, 1), (53, 1), (57, 1), (59, 1), (66, 1), (67, 1)] }, { coefficient := -1, powers := [(19, 1), (27, 1), (36, 1), (53, 1), (56, 1), (57, 1), (59, 1), (66, 1), (67, 1)] }, { coefficient := -1, powers := [(22, 1), (62, 1), (67, 1)] }, { coefficient := 1, powers := [(23, 1), (24, 1), (36, 1), (52, 1), (53, 1), (57, 1), (59, 1), (66, 1), (67, 1)] }, { coefficient := 1, powers := [(23, 1), (24, 1), (36, 1), (53, 1), (57, 1), (59, 1), (67, 1)] }, { coefficient := -1, powers := [(23, 1), (36, 1), (43, 1), (54, 1), (59, 1), (67, 1)] }, { coefficient := -1, powers := [(24, 1), (27, 1), (52, 1), (62, 1), (67, 1)] }, { coefficient := -1, powers := [(24, 1), (27, 1), (56, 1), (62, 1), (67, 1)] }, { coefficient := 1, powers := [(24, 1), (28, 1), (62, 1), (67, 1)] }, { coefficient := -1, powers := [(27, 1), (62, 1), (67, 1)] }, { coefficient := -1, powers := [(28, 1), (36, 1), (41, 1), (57, 1), (59, 1), (66, 1), (67, 1)] }, { coefficient := 1, powers := [(28, 1), (36, 1), (41, 1), (59, 1), (64, 1)] }, { coefficient := 1, powers := [(29, 1), (36, 1), (41, 1), (46, 1), (59, 1), (64, 1), (67, 1)] }],
  [{ coefficient := 2, powers := [(2, 1), (6, 1), (40, 1), (48, 1), (54, 1), (59, 1), (67, 1)] }, { coefficient := 2, powers := [(2, 1), (36, 1), (40, 1), (48, 1), (54, 1), (59, 1), (67, 1)] }, { coefficient := 2, powers := [(5, 1), (22, 1), (45, 1), (50, 1), (57, 1), (59, 1), (67, 1)] }, { coefficient := 2, powers := [(5, 1), (27, 1), (45, 1), (50, 1), (57, 1), (59, 1), (67, 1)] }, { coefficient := -1, powers := [(6, 1), (12, 1), (23, 1), (52, 1), (56, 1), (57, 1), (59, 1), (66, 1), (67, 1)] }, { coefficient := -1, powers := [(6, 1), (12, 1), (23, 1), (56, 1), (57, 1), (59, 1), (67, 1)] }, { coefficient := 2, powers := [(6, 1), (17, 1), (23, 1), (40, 1), (54, 1), (59, 1), (67, 1)] }, { coefficient := -1, powers := [(12, 1), (23, 1), (36, 1), (52, 1), (56, 1), (57, 1), (59, 1), (66, 1), (67, 1)] }, { coefficient := -1, powers := [(12, 1), (23, 1), (36, 1), (56, 1), (57, 1), (59, 1), (67, 1)] }, { coefficient := 2, powers := [(17, 1), (23, 1), (36, 1), (40, 1), (54, 1), (59, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (40, 1), (45, 1), (50, 1), (65, 1), (67, 1)] }, { coefficient := 1, powers := [(2, 1), (6, 1), (43, 1), (54, 1), (59, 1), (61, 1), (67, 1)] }, { coefficient := 1, powers := [(2, 1), (6, 1), (50, 1), (59, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (36, 1), (43, 1), (54, 1), (59, 1), (61, 1), (67, 1)] }, { coefficient := 1, powers := [(2, 1), (36, 1), (50, 1), (59, 1), (61, 1)] }, { coefficient := 1, powers := [(6, 1), (17, 1), (29, 1), (53, 1), (59, 1), (67, 1)] }, { coefficient := 1, powers := [(17, 1), (29, 1), (36, 1), (53, 1), (59, 1), (67, 1)] }, { coefficient := 1, powers := [(24, 1), (40, 2), (50, 1), (65, 1), (67, 1)] }, { coefficient := 1, powers := [(24, 1), (40, 1), (45, 1), (50, 1), (65, 1), (67, 1)] }, { coefficient := 1, powers := [(40, 1), (50, 1), (65, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (17, 1), (50, 1), (59, 1)] }, { coefficient := 1, powers := [(17, 1), (36, 1), (50, 1), (59, 1)] }],
  [{ coefficient := -2, powers := [(2, 1), (6, 1), (40, 1), (48, 1), (59, 1)] }, { coefficient := -2, powers := [(2, 1), (36, 1), (40, 1), (48, 1), (59, 1)] }, { coefficient := -2, powers := [(6, 1), (17, 1), (23, 1), (40, 1), (59, 1)] }, { coefficient := -2, powers := [(17, 1), (23, 1), (36, 1), (40, 1), (59, 1)] }],
  [{ coefficient := 2, powers := [(6, 1), (12, 1), (48, 1), (59, 1), (63, 1)] }, { coefficient := -1, powers := [(6, 1), (17, 1), (41, 1), (45, 1), (59, 1), (63, 1), (64, 1)] }, { coefficient := 1, powers := [(6, 1), (17, 1), (41, 1), (59, 1), (63, 1)] }, { coefficient := 2, powers := [(12, 1), (36, 1), (48, 1), (59, 1), (63, 1)] }, { coefficient := -1, powers := [(17, 1), (36, 1), (41, 1), (45, 1), (59, 1), (63, 1), (64, 1)] }, { coefficient := 1, powers := [(17, 1), (36, 1), (41, 1), (59, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (23, 1), (52, 1), (53, 1), (57, 1), (59, 1), (66, 1)] }, { coefficient := -1, powers := [(6, 1), (23, 1), (53, 1), (57, 1), (59, 1)] }, { coefficient := -1, powers := [(23, 1), (36, 1), (52, 1), (53, 1), (57, 1), (59, 1), (66, 1)] }, { coefficient := -1, powers := [(23, 1), (36, 1), (53, 1), (57, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (16, 1), (54, 1), (59, 1)] }, { coefficient := 1, powers := [(16, 1), (36, 1), (54, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (17, 1), (41, 1), (59, 1), (64, 1)] }, { coefficient := 1, powers := [(17, 1), (36, 1), (41, 1), (59, 1), (64, 1)] }],
  [{ coefficient := 2, powers := [(2, 1), (6, 1), (48, 1), (54, 1), (59, 1), (67, 1)] }, { coefficient := 2, powers := [(2, 1), (36, 1), (48, 1), (54, 1), (59, 1), (67, 1)] }, { coefficient := 2, powers := [(6, 1), (17, 1), (23, 1), (54, 1), (59, 1), (67, 1)] }, { coefficient := 2, powers := [(17, 1), (23, 1), (36, 1), (54, 1), (59, 1), (67, 1)] }],
  [{ coefficient := -2, powers := [(5, 1), (22, 1), (45, 1), (57, 1), (59, 1)] }, { coefficient := -2, powers := [(5, 1), (27, 1), (45, 1), (57, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (23, 1), (59, 1)] }, { coefficient := -1, powers := [(23, 1), (36, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (12, 1), (57, 1), (59, 1), (66, 1)] }, { coefficient := -1, powers := [(12, 1), (36, 1), (57, 1), (59, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (12, 1), (59, 1)] }, { coefficient := -1, powers := [(12, 1), (36, 1), (59, 1)] }],
  [{ coefficient := 2, powers := [(5, 1), (22, 1), (57, 1), (59, 1)] }, { coefficient := 2, powers := [(5, 1), (27, 1), (57, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (23, 1), (52, 1), (57, 1), (59, 1), (66, 1)] }, { coefficient := 1, powers := [(6, 1), (23, 1), (57, 1), (59, 1)] }, { coefficient := 1, powers := [(23, 1), (36, 1), (52, 1), (57, 1), (59, 1), (66, 1)] }, { coefficient := 1, powers := [(23, 1), (36, 1), (57, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(40, 1), (50, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (62, 1)] }, { coefficient := -1, powers := [(24, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (53, 1), (57, 1), (59, 1), (66, 1)] }, { coefficient := -1, powers := [(36, 1), (53, 1), (57, 1), (59, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (54, 1), (59, 1)] }, { coefficient := -1, powers := [(36, 1), (54, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (48, 1), (59, 1)] }, { coefficient := -1, powers := [(36, 1), (48, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (27, 1), (53, 1), (57, 1), (59, 1), (66, 1)] }, { coefficient := 1, powers := [(27, 1), (36, 1), (53, 1), (57, 1), (59, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (29, 1), (59, 1)] }, { coefficient := -1, powers := [(29, 1), (36, 1), (59, 1)] }],
  [{ coefficient := -2, powers := [(5, 1), (57, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (27, 1), (62, 1)] }, { coefficient := 1, powers := [(24, 1), (27, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (17, 1), (59, 1)] }, { coefficient := -1, powers := [(17, 1), (36, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(40, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(62, 1)] }],
  [{ coefficient := -1, powers := [(19, 1), (40, 1), (50, 1), (65, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := -1, powers := [(2, 1), (6, 1), (59, 1), (61, 1)] }, { coefficient := -1, powers := [(2, 1), (36, 1), (59, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (41, 1), (59, 1), (64, 1)] }, { coefficient := -1, powers := [(36, 1), (41, 1), (59, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (57, 1), (59, 1), (66, 1)] }, { coefficient := 1, powers := [(36, 1), (57, 1), (59, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (59, 1)] }, { coefficient := 1, powers := [(36, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (6, 1), (38, 1), (59, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (6, 1), (41, 1), (57, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (6, 1), (48, 1), (54, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (36, 1), (38, 1), (59, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (36, 1), (41, 1), (57, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (36, 1), (48, 1), (54, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1)] }, { coefficient := 1, powers := [(24, 1), (45, 1)] }, { coefficient := -1, powers := [(36, 1), (59, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := -2, powers := [(6, 1), (12, 1), (29, 1), (48, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (17, 1), (29, 1), (41, 1), (45, 1), (59, 1), (64, 1)] }, { coefficient := -1, powers := [(6, 1), (17, 1), (29, 1), (41, 1), (59, 1)] }, { coefficient := -2, powers := [(12, 1), (29, 1), (36, 1), (48, 1), (59, 1)] }, { coefficient := 1, powers := [(17, 1), (29, 1), (36, 1), (41, 1), (45, 1), (59, 1), (64, 1)] }, { coefficient := -1, powers := [(17, 1), (29, 1), (36, 1), (41, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (6, 1), (41, 1), (57, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (36, 1), (41, 1), (57, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (8, 1), (35, 1), (41, 1), (59, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (36, 1), (41, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (40, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (6, 1), (41, 1), (57, 1), (59, 1)] }, { coefficient := -1, powers := [(2, 1), (36, 1), (41, 1), (57, 1), (59, 1)] }, { coefficient := -1, powers := [(5, 1), (6, 1), (32, 1), (57, 1), (59, 1)] }, { coefficient := -1, powers := [(5, 1), (32, 1), (36, 1), (57, 1), (59, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (2, 1), (6, 1), (40, 1), (48, 1), (54, 1), (59, 1)] }, { coefficient := -2, powers := [(0, 1), (2, 1), (36, 1), (40, 1), (48, 1), (54, 1), (59, 1)] }, { coefficient := -2, powers := [(0, 1), (6, 1), (17, 1), (23, 1), (40, 1), (54, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (16, 1), (27, 1), (52, 1), (62, 1)] }, { coefficient := 1, powers := [(0, 1), (16, 1), (27, 1), (56, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 1), (16, 1), (28, 1), (62, 1)] }, { coefficient := -2, powers := [(0, 1), (17, 1), (23, 1), (36, 1), (40, 1), (54, 1), (59, 1)] }, { coefficient := -1, powers := [(0, 1), (19, 1), (40, 1), (45, 1), (50, 1), (65, 1)] }, { coefficient := -2, powers := [(2, 1), (6, 1), (18, 1), (40, 1), (48, 1), (54, 1), (59, 1)] }, { coefficient := -1, powers := [(2, 1), (6, 1), (19, 1), (43, 1), (54, 1), (59, 1), (61, 1)] }, { coefficient := -2, powers := [(2, 1), (6, 1), (48, 1), (54, 1), (59, 1)] }, { coefficient := -2, powers := [(2, 1), (18, 1), (36, 1), (40, 1), (48, 1), (54, 1), (59, 1)] }, { coefficient := -1, powers := [(2, 1), (19, 1), (36, 1), (43, 1), (54, 1), (59, 1), (61, 1)] }, { coefficient := -2, powers := [(2, 1), (36, 1), (48, 1), (54, 1), (59, 1)] }, { coefficient := -2, powers := [(5, 1), (18, 1), (22, 1), (45, 1), (50, 1), (57, 1), (59, 1)] }, { coefficient := -2, powers := [(5, 1), (18, 1), (27, 1), (45, 1), (50, 1), (57, 1), (59, 1)] }, { coefficient := 2, powers := [(6, 1), (9, 1), (12, 1), (29, 1), (48, 1), (59, 1), (63, 1)] }, { coefficient := -1, powers := [(6, 1), (9, 1), (17, 1), (29, 1), (41, 1), (45, 1), (59, 1), (63, 1), (64, 1)] }, { coefficient := 1, powers := [(6, 1), (9, 1), (17, 1), (29, 1), (41, 1), (59, 1), (63, 1)] }, { coefficient := 1, powers := [(6, 1), (12, 1), (18, 1), (23, 1), (52, 1), (56, 1), (57, 1), (59, 1), (66, 1)] }, { coefficient := 1, powers := [(6, 1), (12, 1), (18, 1), (23, 1), (56, 1), (57, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (16, 1), (19, 1), (27, 1), (52, 1), (53, 1), (57, 1), (59, 1), (66, 1)] }, { coefficient := 1, powers := [(6, 1), (16, 1), (19, 1), (27, 1), (53, 1), (56, 1), (57, 1), (59, 1), (66, 1)] }, { coefficient := -1, powers := [(6, 1), (16, 1), (23, 1), (24, 1), (52, 1), (53, 1), (57, 1), (59, 1), (66, 1)] }, { coefficient := -1, powers := [(6, 1), (16, 1), (23, 1), (24, 1), (53, 1), (57, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (16, 1), (23, 1), (43, 1), (54, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (16, 1), (28, 1), (41, 1), (57, 1), (59, 1), (66, 1)] }, { coefficient := -1, powers := [(6, 1), (16, 1), (29, 1), (41, 1), (46, 1), (59, 1), (64, 1)] }, { coefficient := -2, powers := [(6, 1), (17, 1), (18, 1), (23, 1), (40, 1), (54, 1), (59, 1)] }, { coefficient := -1, powers := [(6, 1), (17, 1), (19, 1), (29, 1), (53, 1), (59, 1)] }, { coefficient := -2, powers := [(6, 1), (17, 1), (23, 1), (54, 1), (59, 1)] }, { coefficient := 2, powers := [(9, 1), (12, 1), (29, 1), (36, 1), (48, 1), (59, 1), (63, 1)] }, { coefficient := -1, powers := [(9, 1), (17, 1), (29, 1), (36, 1), (41, 1), (45, 1), (59, 1), (63, 1), (64, 1)] }, { coefficient := 1, powers := [(9, 1), (17, 1), (29, 1), (36, 1), (41, 1), (59, 1), (63, 1)] }, { coefficient := 1, powers := [(12, 1), (18, 1), (23, 1), (36, 1), (52, 1), (56, 1), (57, 1), (59, 1), (66, 1)] }, { coefficient := 1, powers := [(12, 1), (18, 1), (23, 1), (36, 1), (56, 1), (57, 1), (59, 1)] }, { coefficient := 1, powers := [(16, 1), (19, 1), (27, 1), (36, 1), (52, 1), (53, 1), (57, 1), (59, 1), (66, 1)] }, { coefficient := 1, powers := [(16, 1), (19, 1), (27, 1), (36, 1), (53, 1), (56, 1), (57, 1), (59, 1), (66, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1), (62, 1)] }, { coefficient := -1, powers := [(16, 1), (23, 1), (24, 1), (36, 1), (52, 1), (53, 1), (57, 1), (59, 1), (66, 1)] }, { coefficient := -1, powers := [(16, 1), (23, 1), (24, 1), (36, 1), (53, 1), (57, 1), (59, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1), (36, 1), (43, 1), (54, 1), (59, 1)] }, { coefficient := 1, powers := [(16, 1), (24, 1), (27, 1), (52, 1), (62, 1)] }, { coefficient := 1, powers := [(16, 1), (24, 1), (27, 1), (56, 1), (62, 1)] }, { coefficient := -1, powers := [(16, 1), (24, 1), (28, 1), (62, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1), (62, 1)] }, { coefficient := 1, powers := [(16, 1), (28, 1), (36, 1), (41, 1), (57, 1), (59, 1), (66, 1)] }, { coefficient := -1, powers := [(16, 1), (29, 1), (36, 1), (41, 1), (46, 1), (59, 1), (64, 1)] }, { coefficient := -2, powers := [(17, 1), (18, 1), (23, 1), (36, 1), (40, 1), (54, 1), (59, 1)] }, { coefficient := -1, powers := [(17, 1), (19, 1), (29, 1), (36, 1), (53, 1), (59, 1)] }, { coefficient := -2, powers := [(17, 1), (23, 1), (36, 1), (54, 1), (59, 1)] }, { coefficient := -1, powers := [(19, 1), (24, 1), (40, 2), (50, 1), (65, 1)] }, { coefficient := -1, powers := [(19, 1), (24, 1), (40, 1), (45, 1), (50, 1), (65, 1)] }, { coefficient := -1, powers := [(19, 1), (40, 1), (50, 1), (65, 1)] }]
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
    (values : Fin 68 → R) :
    ¬ ∀ index : Fin 42,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((2 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (2 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (2 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component25.SelectedLeafB5_7_3.selectedHasNoCommonZero

end Krenn.Component25.SelectedLeafB5_7_3
