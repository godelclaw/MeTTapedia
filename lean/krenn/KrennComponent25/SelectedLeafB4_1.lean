import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component25.SelectedLeafB4_1

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "59f1804d4873c382db2914ebfc8c601db227559afbabfee05eefbc6c25f97b26"
def certificateSHA256 : String := "ef9e541fe7c1d367b5b1e8e6d02d07ed003fa724862c9c06258b128758da8814"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 24 → Fin 662 := ![
  1,
  14,
  21,
  175,
  294,
  312,
  319,
  423,
  424,
  438,
  450,
  461,
  467,
  478,
  578,
  579,
  606,
  609,
  643,
  655,
  656,
  658,
  660,
  661
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 24 → SparsePoly (Fin 63) := ![
  [{ coefficient := 1, powers := [(8, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(57, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (50, 1)] }, { coefficient := 1, powers := [(18, 1), (50, 1)] }, { coefficient := 1, powers := [(24, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (57, 1)] }, { coefficient := 1, powers := [(29, 1), (48, 1)] }, { coefficient := 1, powers := [(35, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1), (50, 1)] }, { coefficient := 1, powers := [(24, 1), (45, 1), (50, 1)] }, { coefficient := 1, powers := [(50, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1)] }, { coefficient := 1, powers := [(6, 1), (19, 1), (59, 1)] }, { coefficient := 1, powers := [(19, 1)] }, { coefficient := 1, powers := [(24, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (53, 1)] }, { coefficient := 1, powers := [(18, 1), (50, 1), (56, 1)] }, { coefficient := 1, powers := [(18, 1), (53, 1)] }, { coefficient := 1, powers := [(50, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (59, 1)] }, { coefficient := 1, powers := [(16, 1), (19, 1), (52, 1)] }, { coefficient := 1, powers := [(16, 1), (19, 1), (56, 1)] }, { coefficient := 1, powers := [(16, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (54, 1)] }, { coefficient := 1, powers := [(29, 1), (41, 1)] }, { coefficient := 1, powers := [(29, 1), (47, 1), (50, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1), (53, 1)] }, { coefficient := 1, powers := [(45, 1), (50, 1)] }, { coefficient := 1, powers := [(50, 1), (56, 1)] }, { coefficient := 1, powers := [(53, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1), (50, 1)] }, { coefficient := 1, powers := [(19, 1), (50, 1)] }, { coefficient := 1, powers := [(24, 1), (41, 1)] }, { coefficient := 1, powers := [(24, 1), (47, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (59, 1)] }, { coefficient := 1, powers := [(8, 1), (23, 1), (59, 1)] }, { coefficient := 1, powers := [(16, 1), (29, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1)] }, { coefficient := 1, powers := [(6, 1), (59, 1)] }, { coefficient := 1, powers := [(24, 1), (40, 1)] }, { coefficient := 1, powers := [(24, 1), (45, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (52, 1)] }, { coefficient := 1, powers := [(3, 1), (59, 1)] }, { coefficient := 1, powers := [(18, 1), (52, 1)] }, { coefficient := 1, powers := [(18, 1), (56, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (36, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1)] }, { coefficient := 1, powers := [(3, 1), (24, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (18, 1), (59, 1)] }, { coefficient := 1, powers := [(18, 1)] }, { coefficient := 1, powers := [(24, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (41, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (47, 1), (53, 1)] }, { coefficient := 1, powers := [(19, 1), (50, 1), (56, 1)] }, { coefficient := 1, powers := [(19, 1), (53, 1)] }, { coefficient := 1, powers := [(41, 1)] }, { coefficient := 1, powers := [(47, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (37, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (40, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (45, 1), (52, 1)] }, { coefficient := 1, powers := [(40, 1)] }, { coefficient := 1, powers := [(45, 1)] }, { coefficient := 1, powers := [(52, 1)] }, { coefficient := 1, powers := [(56, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (41, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (48, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (23, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (48, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(12, 1), (23, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1), (29, 1), (48, 1)] }, { coefficient := 1, powers := [(12, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(17, 1), (23, 1), (54, 1)] }, { coefficient := 1, powers := [(17, 1), (29, 1), (41, 1)] }, { coefficient := 1, powers := [(17, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (61, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(40, 1)] }],
  [{ coefficient := 1, powers := [(41, 1), (62, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 24 → SparsePoly (Fin 63) := ![
  [{ coefficient := 1, powers := [(0, 1), (18, 1), (32, 1), (37, 1), (48, 1)] }, { coefficient := 1, powers := [(0, 1), (18, 1), (35, 1), (37, 1), (41, 1)] }, { coefficient := 2, powers := [(0, 1), (32, 1), (36, 1), (48, 1), (52, 1)] }, { coefficient := 2, powers := [(0, 1), (35, 1), (36, 1), (41, 1), (52, 1)] }, { coefficient := -2, powers := [(3, 1), (32, 1), (48, 1)] }, { coefficient := -2, powers := [(3, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(6, 1), (18, 1), (32, 1), (48, 1), (52, 1)] }, { coefficient := -1, powers := [(6, 1), (18, 1), (32, 1), (48, 1), (61, 1)] }, { coefficient := 1, powers := [(6, 1), (18, 1), (35, 1), (41, 1), (52, 1)] }, { coefficient := -1, powers := [(6, 1), (18, 1), (35, 1), (41, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (18, 1), (19, 1), (35, 1), (37, 1), (52, 1)] }, { coefficient := -1, powers := [(0, 1), (18, 1), (19, 1), (35, 1), (37, 1), (56, 1)] }, { coefficient := -1, powers := [(0, 1), (18, 1), (35, 1), (37, 1), (47, 1)] }, { coefficient := -2, powers := [(0, 1), (19, 1), (35, 1), (36, 1), (52, 2)] }, { coefficient := -2, powers := [(0, 1), (19, 1), (35, 1), (36, 1), (52, 1), (56, 1)] }, { coefficient := -2, powers := [(0, 1), (35, 1), (36, 1), (47, 1), (52, 1)] }, { coefficient := 2, powers := [(3, 1), (19, 1), (35, 1), (52, 1)] }, { coefficient := 2, powers := [(3, 1), (19, 1), (35, 1), (56, 1)] }, { coefficient := 2, powers := [(3, 1), (35, 1), (47, 1)] }, { coefficient := -1, powers := [(6, 1), (18, 1), (19, 1), (35, 1), (52, 2)] }, { coefficient := -1, powers := [(6, 1), (18, 1), (19, 1), (35, 1), (52, 1), (56, 1)] }, { coefficient := 1, powers := [(6, 1), (18, 1), (19, 1), (35, 1), (52, 1), (61, 1)] }, { coefficient := 1, powers := [(6, 1), (18, 1), (19, 1), (35, 1), (56, 1), (61, 1)] }, { coefficient := -1, powers := [(6, 1), (18, 1), (35, 1), (47, 1), (52, 1)] }, { coefficient := 1, powers := [(6, 1), (18, 1), (35, 1), (47, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (16, 1), (18, 1), (37, 1), (60, 1)] }, { coefficient := -2, powers := [(0, 1), (16, 1), (36, 1), (52, 1), (60, 1)] }, { coefficient := -1, powers := [(0, 1), (17, 1), (18, 1), (37, 1), (50, 1), (59, 1)] }, { coefficient := -2, powers := [(0, 1), (17, 1), (36, 1), (50, 1), (52, 1), (59, 1)] }, { coefficient := 2, powers := [(3, 1), (16, 1), (60, 1)] }, { coefficient := 2, powers := [(3, 1), (17, 1), (50, 1), (59, 1)] }, { coefficient := -1, powers := [(6, 1), (16, 1), (18, 1), (52, 1), (60, 1)] }, { coefficient := 1, powers := [(6, 1), (16, 1), (18, 1), (60, 1), (61, 1)] }, { coefficient := -1, powers := [(6, 1), (17, 1), (18, 1), (50, 1), (52, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (17, 1), (18, 1), (50, 1), (59, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (5, 1), (18, 1), (32, 1), (37, 1), (59, 1)] }, { coefficient := 2, powers := [(0, 1), (5, 1), (32, 1), (36, 1), (52, 1), (59, 1)] }, { coefficient := -2, powers := [(3, 1), (5, 1), (32, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (6, 1), (18, 1), (32, 1), (52, 1), (59, 1)] }, { coefficient := -1, powers := [(5, 1), (6, 1), (18, 1), (32, 1), (59, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(47, 1), (56, 1), (62, 1)] }, { coefficient := 1, powers := [(47, 1), (61, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (12, 1), (18, 1), (37, 1), (59, 1)] }, { coefficient := 2, powers := [(0, 1), (12, 1), (36, 1), (52, 1), (59, 1)] }, { coefficient := -2, powers := [(3, 1), (12, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (12, 1), (18, 1), (52, 1), (59, 1)] }, { coefficient := -1, powers := [(6, 1), (12, 1), (18, 1), (59, 1), (61, 1)] }],
  [{ coefficient := -2, powers := [(3, 1), (19, 1), (52, 1), (59, 1), (62, 1)] }, { coefficient := -1, powers := [(18, 1), (19, 1), (37, 1), (59, 1), (62, 1)] }, { coefficient := -1, powers := [(18, 1), (19, 1), (52, 1), (61, 1), (62, 1)] }, { coefficient := -1, powers := [(18, 1), (19, 1), (56, 1), (61, 1), (62, 1)] }, { coefficient := -2, powers := [(19, 1), (52, 1), (62, 1)] }, { coefficient := 2, powers := [(19, 1), (56, 1), (62, 1)] }],
  [{ coefficient := -2, powers := [(3, 1), (50, 1), (52, 1), (59, 1), (62, 1)] }, { coefficient := -1, powers := [(18, 1), (37, 1), (50, 1), (59, 1), (62, 1)] }, { coefficient := -1, powers := [(18, 1), (50, 1), (52, 1), (61, 1), (62, 1)] }, { coefficient := -1, powers := [(18, 1), (50, 1), (56, 1), (61, 1), (62, 1)] }, { coefficient := -2, powers := [(50, 1), (52, 1), (62, 1)] }, { coefficient := 2, powers := [(50, 1), (56, 1), (62, 1)] }, { coefficient := -1, powers := [(50, 1), (61, 1), (62, 1)] }, { coefficient := -1, powers := [(53, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (61, 1), (62, 1)] }, { coefficient := 1, powers := [(47, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (18, 1), (35, 1), (37, 1), (54, 1)] }, { coefficient := 2, powers := [(0, 1), (35, 1), (36, 1), (52, 1), (54, 1)] }, { coefficient := -2, powers := [(3, 1), (35, 1), (54, 1)] }, { coefficient := 1, powers := [(6, 1), (18, 1), (35, 1), (52, 1), (54, 1)] }, { coefficient := -1, powers := [(6, 1), (18, 1), (35, 1), (54, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (17, 1), (18, 1), (37, 1), (59, 1)] }, { coefficient := 2, powers := [(0, 1), (17, 1), (36, 1), (52, 1), (59, 1)] }, { coefficient := -2, powers := [(3, 1), (17, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (17, 1), (18, 1), (52, 1), (59, 1)] }, { coefficient := -1, powers := [(6, 1), (17, 1), (18, 1), (59, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (19, 1), (61, 1), (62, 1)] }, { coefficient := -1, powers := [(19, 1), (24, 1), (61, 1), (62, 1)] }],
  [{ coefficient := 2, powers := [(3, 1), (52, 1), (59, 1), (62, 1)] }, { coefficient := 1, powers := [(18, 1), (37, 1), (59, 1), (62, 1)] }, { coefficient := 1, powers := [(18, 1), (52, 1), (61, 1), (62, 1)] }, { coefficient := 1, powers := [(18, 1), (56, 1), (61, 1), (62, 1)] }, { coefficient := 2, powers := [(52, 1), (62, 1)] }, { coefficient := -1, powers := [(56, 1), (62, 1)] }, { coefficient := -1, powers := [(61, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (18, 1), (37, 1), (60, 1)] }, { coefficient := 2, powers := [(0, 1), (36, 1), (52, 1), (60, 1)] }, { coefficient := -2, powers := [(3, 1), (60, 1)] }, { coefficient := 1, powers := [(6, 1), (18, 1), (52, 1), (60, 1)] }, { coefficient := -1, powers := [(6, 1), (18, 1), (60, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (19, 1), (53, 1), (61, 1), (62, 1)] }, { coefficient := 2, powers := [(3, 1), (19, 1), (50, 1), (52, 1), (59, 1), (62, 1)] }, { coefficient := 1, powers := [(18, 1), (19, 1), (37, 1), (50, 1), (59, 1), (62, 1)] }, { coefficient := 1, powers := [(18, 1), (19, 1), (50, 1), (52, 1), (61, 1), (62, 1)] }, { coefficient := 1, powers := [(18, 1), (19, 1), (50, 1), (56, 1), (61, 1), (62, 1)] }, { coefficient := 1, powers := [(18, 1), (52, 1)] }, { coefficient := 1, powers := [(18, 1), (61, 1)] }, { coefficient := 2, powers := [(19, 1), (50, 1), (52, 1), (62, 1)] }, { coefficient := -2, powers := [(19, 1), (50, 1), (56, 1), (62, 1)] }, { coefficient := 1, powers := [(19, 1), (50, 1), (61, 1), (62, 1)] }],
  [{ coefficient := 2, powers := [] }],
  [{ coefficient := -2, powers := [(52, 1)] }],
  [{ coefficient := -1, powers := [(18, 1), (61, 1), (62, 1)] }, { coefficient := 1, powers := [(24, 1), (61, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(18, 1), (24, 1), (61, 1)] }, { coefficient := -1, powers := [(18, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (18, 1), (37, 1), (59, 1)] }, { coefficient := -2, powers := [(0, 1), (36, 1), (52, 1), (59, 1)] }, { coefficient := 2, powers := [(3, 1), (59, 1)] }, { coefficient := -1, powers := [(6, 1), (18, 1), (52, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (18, 1), (59, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (19, 1), (53, 1), (59, 1), (62, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (37, 1), (59, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (45, 1), (52, 1)] }, { coefficient := 1, powers := [(18, 1), (41, 1), (56, 1), (62, 1)] }, { coefficient := -1, powers := [(18, 1), (45, 1)] }, { coefficient := 1, powers := [(18, 1), (47, 1), (53, 1), (62, 1)] }, { coefficient := 1, powers := [(19, 1), (50, 1), (56, 1), (62, 1)] }, { coefficient := -1, powers := [(19, 1), (53, 1), (62, 1)] }, { coefficient := -1, powers := [(24, 1), (41, 1), (56, 1), (62, 1)] }, { coefficient := -1, powers := [(24, 1), (47, 1), (53, 1), (62, 1)] }, { coefficient := 1, powers := [(47, 1), (50, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (18, 1), (37, 1), (41, 1), (57, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (18, 1), (37, 1), (48, 1), (54, 1), (59, 1)] }, { coefficient := 2, powers := [(0, 1), (36, 1), (41, 1), (52, 1), (57, 1), (59, 1)] }, { coefficient := 2, powers := [(0, 1), (36, 1), (48, 1), (52, 1), (54, 1), (59, 1)] }, { coefficient := -2, powers := [(3, 1), (41, 1), (57, 1), (59, 1)] }, { coefficient := -2, powers := [(3, 1), (48, 1), (54, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (18, 1), (41, 1), (52, 1), (57, 1), (59, 1)] }, { coefficient := -1, powers := [(6, 1), (18, 1), (41, 1), (57, 1), (59, 1), (61, 1)] }, { coefficient := 1, powers := [(6, 1), (18, 1), (48, 1), (52, 1), (54, 1), (59, 1)] }, { coefficient := -1, powers := [(6, 1), (18, 1), (48, 1), (54, 1), (59, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(0, 2), (5, 1), (18, 1), (32, 1), (37, 1), (57, 1), (59, 1)] }, { coefficient := -2, powers := [(0, 2), (5, 1), (32, 1), (36, 1), (52, 1), (57, 1), (59, 1)] }, { coefficient := 2, powers := [(0, 1), (3, 1), (5, 1), (32, 1), (57, 1), (59, 1)] }, { coefficient := -1, powers := [(0, 1), (5, 1), (6, 1), (18, 1), (32, 1), (52, 1), (57, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (5, 1), (6, 1), (18, 1), (32, 1), (57, 1), (59, 1), (61, 1)] }, { coefficient := 1, powers := [(0, 1), (18, 1), (24, 1), (56, 1), (61, 1)] }, { coefficient := 1, powers := [(0, 1), (18, 1), (56, 1)] }, { coefficient := -1, powers := [(0, 1), (19, 1), (24, 1), (53, 1), (61, 1), (62, 1)] }, { coefficient := -2, powers := [(3, 1), (19, 1), (24, 1), (50, 1), (52, 1), (59, 1), (62, 1)] }, { coefficient := -1, powers := [(18, 1), (19, 1), (24, 1), (37, 1), (50, 1), (59, 1), (62, 1)] }, { coefficient := -1, powers := [(18, 1), (19, 1), (24, 1), (50, 1), (52, 1), (61, 1), (62, 1)] }, { coefficient := -1, powers := [(18, 1), (19, 1), (24, 1), (50, 1), (56, 1), (61, 1), (62, 1)] }, { coefficient := -1, powers := [(18, 1), (24, 1), (52, 1)] }, { coefficient := 1, powers := [(18, 1)] }, { coefficient := -2, powers := [(19, 1), (24, 1), (50, 1), (52, 1), (62, 1)] }, { coefficient := 2, powers := [(19, 1), (24, 1), (50, 1), (56, 1), (62, 1)] }, { coefficient := -1, powers := [(19, 1), (24, 1), (50, 1), (61, 1), (62, 1)] }],
  [{ coefficient := -2, powers := [(3, 1), (24, 1), (52, 1), (59, 1)] }, { coefficient := -1, powers := [(18, 1), (24, 1), (37, 1), (59, 1)] }, { coefficient := -1, powers := [(18, 1), (24, 1), (52, 1), (61, 1)] }, { coefficient := -1, powers := [(18, 1), (24, 1), (56, 1), (61, 1)] }, { coefficient := 1, powers := [(18, 1), (56, 1)] }, { coefficient := 1, powers := [(18, 1), (61, 1)] }, { coefficient := -2, powers := [(24, 1), (52, 1)] }]
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
    (values : Fin 63 → R) :
    ¬ ∀ index : Fin 24,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((2 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (2 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (2 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component25.SelectedLeafB4_1.selectedHasNoCommonZero

end Krenn.Component25.SelectedLeafB4_1
