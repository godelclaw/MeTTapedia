import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component25.SelectedLeafB5_2_3

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "10dbc483d37cf9fe3ea7f7c01dc9678877382a7a53d3ae58d8211050f243601b"
def certificateSHA256 : String := "e58b9cb3f4ed9f2bea8e65fb57460282d4b538caaaa2a9aad21a7d21ea98e2ca"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 27 → Fin 665 := ![
  0,
  2,
  15,
  16,
  70,
  175,
  199,
  310,
  427,
  433,
  449,
  451,
  460,
  579,
  588,
  600,
  601,
  643,
  647,
  653,
  656,
  658,
  659,
  660,
  662,
  663,
  664
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 27 → SparsePoly (Fin 66) := ![
  [{ coefficient := 1, powers := [(8, 1), (30, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (33, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(57, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (30, 1), (44, 1)] }, { coefficient := 1, powers := [(8, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (46, 1)] }, { coefficient := 1, powers := [(17, 1), (40, 1)] }, { coefficient := 1, powers := [(17, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (45, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1), (40, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1), (45, 1)] }, { coefficient := 1, powers := [(16, 1), (28, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (52, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1), (52, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1), (56, 1)] }, { coefficient := 1, powers := [(16, 1), (28, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (40, 1)] }, { coefficient := 1, powers := [(16, 1), (45, 1)] }, { coefficient := 1, powers := [(16, 1), (52, 1)] }, { coefficient := 1, powers := [(16, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(28, 1), (40, 1)] }, { coefficient := 1, powers := [(28, 1), (45, 1)] }, { coefficient := 1, powers := [(28, 1), (52, 1)] }, { coefficient := 1, powers := [(28, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1), (49, 1)] }, { coefficient := 1, powers := [(6, 1), (30, 1), (45, 1)] }, { coefficient := 1, powers := [(9, 1), (24, 1), (45, 1)] }, { coefficient := 1, powers := [(49, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (52, 1)] }, { coefficient := 1, powers := [(3, 1), (59, 1)] }, { coefficient := 1, powers := [(18, 1), (52, 1)] }, { coefficient := 1, powers := [(18, 1), (56, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (40, 1)] }, { coefficient := 1, powers := [(16, 1), (28, 1), (57, 1)] }, { coefficient := 1, powers := [(16, 1), (29, 1), (46, 1)] }, { coefficient := 1, powers := [(17, 1), (29, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1)] }, { coefficient := 1, powers := [(3, 1), (33, 1)] }, { coefficient := 1, powers := [(13, 1), (18, 1)] }, { coefficient := 1, powers := [(18, 1), (55, 1)] }, { coefficient := 1, powers := [(24, 1), (42, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (49, 1)] }, { coefficient := 1, powers := [(6, 1), (30, 1)] }, { coefficient := 1, powers := [(9, 1), (24, 1)] }, { coefficient := 1, powers := [(18, 1), (49, 1)] }, { coefficient := 1, powers := [(24, 1), (39, 1)] }, { coefficient := 1, powers := [(30, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (37, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (40, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (45, 1), (52, 1)] }, { coefficient := 1, powers := [(40, 1)] }, { coefficient := 1, powers := [(45, 1)] }, { coefficient := 1, powers := [(52, 1)] }, { coefficient := 1, powers := [(56, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (37, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (40, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (45, 1), (52, 1)] }, { coefficient := 1, powers := [(16, 1), (28, 1), (40, 1)] }, { coefficient := 1, powers := [(16, 1), (28, 1), (45, 1)] }, { coefficient := 1, powers := [(16, 1), (28, 1), (52, 1)] }, { coefficient := 1, powers := [(16, 1), (28, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (36, 1), (58, 1)] }, { coefficient := 1, powers := [(0, 1), (39, 1), (55, 1)] }, { coefficient := 1, powers := [(0, 1), (42, 1), (49, 1)] }, { coefficient := 1, powers := [(3, 1), (24, 1), (58, 1)] }, { coefficient := 1, powers := [(3, 1), (30, 1), (55, 1)] }, { coefficient := 1, powers := [(3, 1), (33, 1), (49, 1)] }, { coefficient := 1, powers := [(6, 1), (18, 1), (58, 1)] }, { coefficient := 1, powers := [(6, 1), (30, 1), (42, 1)] }, { coefficient := 1, powers := [(6, 1), (33, 1), (39, 1)] }, { coefficient := 1, powers := [(9, 1), (18, 1), (55, 1)] }, { coefficient := 1, powers := [(9, 1), (24, 1), (42, 1)] }, { coefficient := 1, powers := [(9, 1), (33, 1), (36, 1)] }, { coefficient := 1, powers := [(13, 1), (18, 1), (49, 1)] }, { coefficient := 1, powers := [(13, 1), (24, 1), (39, 1)] }, { coefficient := 1, powers := [(13, 1), (30, 1), (36, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (61, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(39, 1)] }],
  [{ coefficient := 1, powers := [(40, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(55, 1)] }],
  [{ coefficient := 1, powers := [(56, 1), (64, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(57, 1), (65, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 27 → SparsePoly (Fin 66) := ![
  [{ coefficient := -1, powers := [(0, 1), (35, 1), (36, 1), (40, 1), (42, 1), (45, 1), (62, 1), (64, 1), (65, 1)] }, { coefficient := -1, powers := [(0, 1), (35, 1), (36, 1), (40, 1), (44, 1), (62, 1), (64, 1), (65, 1)] }, { coefficient := -1, powers := [(3, 1), (24, 1), (35, 1), (40, 1), (44, 1), (62, 1), (64, 1), (65, 1)] }, { coefficient := 1, powers := [(13, 1), (35, 1), (36, 1), (40, 1), (62, 1), (64, 1), (65, 1)] }, { coefficient := -1, powers := [(24, 1), (35, 1), (36, 1), (40, 1), (42, 1), (45, 1), (62, 1), (64, 1), (65, 1)] }, { coefficient := -1, powers := [(35, 1), (36, 1), (40, 1), (42, 1), (62, 1), (64, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (33, 1), (35, 1), (36, 1), (40, 1), (62, 1), (64, 1), (65, 2)] }],
  [{ coefficient := 1, powers := [(3, 1), (27, 1), (52, 1), (59, 1), (62, 1), (64, 1), (65, 1)] }, { coefficient := 1, powers := [(3, 1), (27, 1), (56, 1), (59, 1), (62, 1), (64, 1), (65, 1)] }, { coefficient := -1, powers := [(3, 1), (28, 1), (59, 1), (62, 1), (64, 1), (65, 1)] }, { coefficient := -1, powers := [(8, 1), (22, 1), (35, 1), (52, 1), (62, 2), (64, 1), (65, 2)] }, { coefficient := -1, powers := [(8, 1), (22, 1), (35, 1), (56, 1), (62, 2), (64, 1), (65, 2)] }, { coefficient := -1, powers := [(8, 1), (28, 1), (35, 1), (62, 2), (64, 1), (65, 2)] }, { coefficient := 1, powers := [(22, 1), (45, 1), (52, 1), (62, 1), (63, 1), (64, 1), (65, 1)] }, { coefficient := 1, powers := [(22, 1), (45, 1), (56, 1), (62, 1), (63, 1), (64, 1), (65, 1)] }, { coefficient := -1, powers := [(22, 1), (52, 1), (57, 1), (62, 1), (64, 1), (65, 2)] }, { coefficient := 1, powers := [(22, 1), (52, 1), (62, 1), (64, 1), (65, 1)] }, { coefficient := -1, powers := [(22, 1), (56, 1), (57, 1), (62, 1), (64, 1), (65, 2)] }, { coefficient := 1, powers := [(22, 1), (56, 1), (62, 1), (64, 1), (65, 1)] }, { coefficient := 1, powers := [(28, 1), (45, 1), (62, 1), (63, 1), (64, 1), (65, 1)] }, { coefficient := 1, powers := [(28, 1), (52, 1), (62, 1), (63, 1), (64, 1), (65, 1)] }, { coefficient := -1, powers := [(28, 1), (57, 1), (62, 1), (64, 1), (65, 2)] }, { coefficient := 2, powers := [(28, 1), (62, 1), (64, 1), (65, 1)] }, { coefficient := 1, powers := [(29, 1), (46, 1), (52, 1), (62, 1), (63, 1), (64, 1), (65, 2)] }],
  [{ coefficient := -1, powers := [(0, 1), (8, 1), (35, 1), (40, 1), (42, 1), (45, 1), (49, 1), (62, 1), (64, 1), (65, 2)] }, { coefficient := 1, powers := [(6, 1), (8, 1), (35, 1), (40, 1), (58, 1), (62, 1), (64, 1), (65, 2)] }, { coefficient := -1, powers := [(8, 1), (24, 1), (35, 1), (40, 1), (42, 1), (45, 1), (49, 1), (62, 1), (64, 1), (65, 2)] }, { coefficient := -1, powers := [(8, 1), (35, 1), (40, 1), (42, 1), (49, 1), (62, 1), (64, 1), (65, 2)] }, { coefficient := 1, powers := [(45, 1), (52, 1), (64, 1), (65, 1)] }, { coefficient := 1, powers := [(45, 1), (56, 1), (64, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(35, 1), (36, 1), (40, 1), (49, 1), (62, 1), (63, 1), (64, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (37, 1), (59, 1), (61, 1), (63, 1), (64, 1), (65, 1)] }, { coefficient := -1, powers := [(0, 1), (56, 1), (61, 1), (64, 1), (65, 1)] }, { coefficient := -1, powers := [(2, 1), (56, 1), (61, 1), (62, 1), (63, 1), (64, 1), (65, 1)] }, { coefficient := 1, powers := [(2, 1), (61, 1), (62, 1), (64, 1), (65, 1)] }, { coefficient := 1, powers := [(56, 1), (61, 1), (63, 1), (64, 1), (65, 1)] }, { coefficient := -1, powers := [(61, 1), (64, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (35, 1), (36, 1), (40, 1), (62, 1), (64, 1), (65, 1)] }, { coefficient := 1, powers := [(3, 1), (24, 1), (35, 1), (40, 1), (62, 1), (64, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (62, 1), (64, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (59, 1), (62, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (35, 1), (62, 2), (64, 1), (65, 1)] }, { coefficient := -1, powers := [(45, 1), (62, 1), (63, 1), (64, 1)] }, { coefficient := 1, powers := [(57, 1), (62, 1), (64, 1), (65, 1)] }, { coefficient := -1, powers := [(62, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (27, 1), (59, 1), (62, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(16, 1), (62, 1), (63, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (8, 1), (35, 1), (40, 1), (42, 1), (62, 1), (64, 1), (65, 1)] }, { coefficient := -1, powers := [(8, 1), (24, 1), (35, 1), (40, 1), (42, 1), (62, 1), (64, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(45, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(52, 1), (62, 1), (63, 1), (64, 1), (65, 1)] }, { coefficient := -1, powers := [(62, 1), (64, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (35, 1), (40, 1), (49, 1), (62, 1), (64, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (8, 1), (35, 1), (40, 1), (42, 1), (45, 1), (62, 1), (64, 1), (65, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (35, 1), (40, 1), (42, 1), (45, 1), (62, 1), (64, 1), (65, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (40, 1), (42, 1), (62, 1), (64, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(64, 1)] }],
  [{ coefficient := 1, powers := [(62, 1), (63, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (35, 1), (40, 1), (62, 1), (64, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (37, 1), (40, 1), (57, 1), (59, 1), (63, 1), (64, 1), (65, 1)] }, { coefficient := 1, powers := [(0, 1), (40, 1), (56, 1), (57, 1), (64, 1), (65, 1)] }, { coefficient := 1, powers := [(2, 1), (40, 1), (56, 1), (57, 1), (62, 1), (63, 1), (64, 1), (65, 1)] }, { coefficient := -1, powers := [(2, 1), (40, 1), (57, 1), (62, 1), (64, 1), (65, 1)] }, { coefficient := 1, powers := [(37, 1), (59, 1), (63, 1), (64, 1)] }, { coefficient := -1, powers := [(40, 1), (56, 1), (57, 1), (63, 1), (64, 1), (65, 1)] }, { coefficient := 1, powers := [(40, 1), (57, 1), (64, 1), (65, 1)] }, { coefficient := 1, powers := [(56, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (45, 1), (59, 1), (64, 1)] }, { coefficient := -1, powers := [(8, 1), (35, 1), (52, 1), (62, 1), (64, 1), (65, 1)] }, { coefficient := -1, powers := [(37, 1), (59, 1), (63, 1), (64, 1)] }, { coefficient := 1, powers := [(52, 1), (64, 1)] }, { coefficient := 1, powers := [(56, 1), (61, 1), (63, 1), (64, 1)] }, { coefficient := -1, powers := [(57, 1), (61, 1), (64, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (8, 1), (24, 1), (35, 1), (40, 1), (42, 1), (45, 1), (62, 1), (64, 1), (65, 1)] }, { coefficient := 1, powers := [(6, 1), (8, 1), (33, 1), (35, 1), (40, 1), (62, 1), (64, 1), (65, 1)] }, { coefficient := 1, powers := [(8, 1), (13, 1), (24, 1), (35, 1), (40, 1), (62, 1), (64, 1), (65, 1)] }, { coefficient := -1, powers := [(8, 1), (24, 2), (35, 1), (40, 1), (42, 1), (45, 1), (62, 1), (64, 1), (65, 1)] }, { coefficient := -1, powers := [(8, 1), (24, 1), (35, 1), (40, 1), (42, 1), (62, 1), (64, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (37, 1), (59, 1), (64, 1)] }, { coefficient := 1, powers := [(2, 1), (52, 1), (57, 1), (62, 1), (64, 1), (65, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (35, 1), (36, 1), (40, 1), (49, 1), (62, 1), (64, 1), (65, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (52, 1), (62, 1), (64, 1), (65, 1)] }, { coefficient := 1, powers := [(17, 1), (29, 1), (52, 1), (62, 1), (64, 1), (65, 1)] }, { coefficient := -1, powers := [(56, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (8, 1), (35, 1), (39, 1), (40, 1), (62, 1), (64, 1), (65, 1)] }, { coefficient := 1, powers := [(3, 1), (8, 1), (30, 1), (35, 1), (40, 1), (62, 1), (64, 1), (65, 1)] }, { coefficient := 1, powers := [(8, 1), (9, 1), (18, 1), (35, 1), (40, 1), (62, 1), (64, 1), (65, 1)] }, { coefficient := -1, powers := [(8, 1), (18, 1), (35, 1), (40, 1), (49, 1), (62, 1), (64, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (8, 1), (18, 1), (35, 1), (40, 1), (42, 1), (45, 1), (49, 1), (62, 1), (64, 1), (65, 1)] }, { coefficient := 1, powers := [(0, 1), (37, 1), (40, 1), (59, 1), (63, 1), (64, 1)] }, { coefficient := 1, powers := [(0, 1), (37, 1), (59, 1), (61, 1), (63, 1), (64, 1)] }, { coefficient := 1, powers := [(0, 1), (40, 1), (56, 1), (64, 1)] }, { coefficient := 1, powers := [(0, 1), (56, 1), (61, 1), (64, 1)] }, { coefficient := 1, powers := [(2, 1), (40, 1), (56, 1), (62, 1), (63, 1), (64, 1)] }, { coefficient := 1, powers := [(2, 1), (56, 1), (61, 1), (62, 1), (63, 1), (64, 1)] }, { coefficient := -1, powers := [(3, 1), (16, 1), (27, 1), (52, 1), (59, 1), (62, 1), (64, 1)] }, { coefficient := -1, powers := [(3, 1), (16, 1), (27, 1), (56, 1), (59, 1), (62, 1), (64, 1)] }, { coefficient := 1, powers := [(3, 1), (16, 1), (28, 1), (59, 1), (62, 1), (64, 1)] }, { coefficient := -1, powers := [(6, 1), (8, 1), (18, 1), (35, 1), (40, 1), (58, 1), (62, 1), (64, 1), (65, 1)] }, { coefficient := -1, powers := [(8, 1), (9, 1), (33, 1), (35, 1), (36, 1), (40, 1), (62, 1), (64, 1), (65, 1)] }, { coefficient := 1, powers := [(8, 1), (16, 1), (22, 1), (35, 1), (52, 1), (62, 2), (64, 1), (65, 1)] }, { coefficient := 1, powers := [(8, 1), (16, 1), (22, 1), (35, 1), (56, 1), (62, 2), (64, 1), (65, 1)] }, { coefficient := 1, powers := [(8, 1), (16, 1), (28, 1), (35, 1), (62, 2), (64, 1), (65, 1)] }, { coefficient := 1, powers := [(8, 1), (18, 1), (24, 1), (35, 1), (40, 1), (42, 1), (45, 1), (49, 1), (62, 1), (64, 1), (65, 1)] }, { coefficient := 1, powers := [(8, 1), (18, 1), (35, 1), (40, 1), (42, 1), (49, 1), (62, 1), (64, 1), (65, 1)] }, { coefficient := -1, powers := [(16, 1), (22, 1), (45, 1), (52, 1), (62, 1), (63, 1), (64, 1)] }, { coefficient := -1, powers := [(16, 1), (22, 1), (45, 1), (56, 1), (62, 1), (63, 1), (64, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1), (52, 1), (57, 1), (62, 1), (64, 1), (65, 1)] }, { coefficient := -1, powers := [(16, 1), (22, 1), (52, 1), (62, 1), (64, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1), (56, 1), (57, 1), (62, 1), (64, 1), (65, 1)] }, { coefficient := -1, powers := [(16, 1), (22, 1), (56, 1), (62, 1), (64, 1)] }, { coefficient := -1, powers := [(16, 1), (28, 1), (45, 1), (62, 1), (63, 1), (64, 1)] }, { coefficient := 1, powers := [(16, 1), (28, 1), (57, 1), (62, 1), (64, 1), (65, 1)] }, { coefficient := -1, powers := [(16, 1), (28, 1), (62, 1), (64, 1)] }, { coefficient := -1, powers := [(16, 1), (29, 1), (46, 1), (52, 1), (62, 1), (63, 1), (64, 1), (65, 1)] }, { coefficient := -1, powers := [(18, 1), (45, 1), (52, 1), (64, 1)] }, { coefficient := -1, powers := [(18, 1), (45, 1), (56, 1), (64, 1)] }, { coefficient := -1, powers := [(40, 1), (56, 1), (63, 1), (64, 1)] }, { coefficient := 1, powers := [(40, 1), (64, 1)] }, { coefficient := -1, powers := [(56, 1), (61, 1), (63, 1), (64, 1)] }]
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
    ¬ ∀ index : Fin 27,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component25.SelectedLeafB5_2_3.selectedHasNoCommonZero

end Krenn.Component25.SelectedLeafB5_2_3
