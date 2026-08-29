import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component39.SelectedLeafB1_2_2_7

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "4e6d5401a2d2680a050c9780298f940df140bf7f2e9add1127b74f341799cb30"
def certificateSHA256 : String := "59c7a44c79d9613fe2b66cd289f26d12de6f6600f1ae1bbc9725ee4cbe9e08f8"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 34 → Fin 673 := ![
  22,
  28,
  177,
  308,
  318,
  349,
  414,
  416,
  420,
  422,
  436,
  439,
  441,
  446,
  448,
  482,
  580,
  584,
  600,
  601,
  616,
  644,
  648,
  649,
  658,
  661,
  663,
  664,
  665,
  667,
  668,
  670,
  671,
  672
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 34 → SparsePoly (Fin 67) := ![
  [{ coefficient := 1, powers := [(16, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (25, 1)] }, { coefficient := 1, powers := [(16, 1), (25, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (26, 1)] }, { coefficient := 1, powers := [(21, 1), (48, 1)] }, { coefficient := 1, powers := [(26, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (53, 1)] }, { coefficient := 1, powers := [(28, 1), (39, 1)] }, { coefficient := 1, powers := [(28, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (25, 1), (58, 1)] }, { coefficient := 1, powers := [(9, 1), (25, 1), (41, 1)] }, { coefficient := 1, powers := [(13, 1), (25, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (41, 1)] }, { coefficient := 1, powers := [(15, 1), (21, 1)] }, { coefficient := 1, powers := [(16, 1), (21, 1), (55, 1)] }, { coefficient := 1, powers := [(16, 1), (26, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (44, 1)] }, { coefficient := 1, powers := [(16, 1), (26, 1), (39, 1)] }, { coefficient := 1, powers := [(16, 1), (26, 1), (44, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (48, 1)] }, { coefficient := 1, powers := [(11, 1), (26, 1)] }, { coefficient := 1, powers := [(16, 1), (21, 1), (48, 1)] }, { coefficient := 1, powers := [(16, 1), (26, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (51, 1)] }, { coefficient := 1, powers := [(16, 1), (21, 1), (51, 1)] }, { coefficient := 1, powers := [(16, 1), (21, 1), (56, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (44, 1)] }, { coefficient := 1, powers := [(11, 1), (56, 1)] }, { coefficient := 1, powers := [(16, 1), (29, 1), (36, 1)] }, { coefficient := 1, powers := [(16, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (39, 1)] }, { coefficient := 1, powers := [(16, 1), (44, 1)] }, { coefficient := 1, powers := [(16, 1), (51, 1)] }, { coefficient := 1, powers := [(16, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (39, 1)] }, { coefficient := 1, powers := [(27, 1), (44, 1)] }, { coefficient := 1, powers := [(27, 1), (51, 1)] }, { coefficient := 1, powers := [(27, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (41, 1), (51, 1)] }, { coefficient := 1, powers := [(3, 1), (32, 1), (51, 1)] }, { coefficient := 1, powers := [(13, 1), (18, 1), (51, 1)] }, { coefficient := 1, powers := [(41, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (41, 1), (53, 1)] }, { coefficient := 1, powers := [(3, 1), (32, 1), (53, 1)] }, { coefficient := 1, powers := [(13, 1), (18, 1), (53, 1)] }, { coefficient := 1, powers := [(24, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (35, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1)] }, { coefficient := 1, powers := [(16, 1), (21, 1)] }, { coefficient := 1, powers := [(16, 1), (26, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1)] }, { coefficient := 1, powers := [(6, 1), (59, 1)] }, { coefficient := 1, powers := [(23, 1), (39, 1)] }, { coefficient := 1, powers := [(23, 1), (44, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1), (50, 1)] }, { coefficient := 1, powers := [(9, 1), (44, 1)] }, { coefficient := 1, powers := [(9, 1), (56, 1)] }, { coefficient := 1, powers := [(29, 1), (36, 1)] }, { coefficient := 1, powers := [(50, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (41, 1)] }, { coefficient := 1, powers := [(3, 1), (32, 1)] }, { coefficient := 1, powers := [(13, 1), (18, 1)] }, { coefficient := 1, powers := [(18, 1), (55, 1)] }, { coefficient := 1, powers := [(23, 1), (41, 1)] }, { coefficient := 1, powers := [(32, 1), (35, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (48, 1)] }, { coefficient := 1, powers := [(6, 1), (29, 1)] }, { coefficient := 1, powers := [(9, 1), (23, 1)] }, { coefficient := 1, powers := [(18, 1), (48, 1)] }, { coefficient := 1, powers := [(23, 1), (38, 1)] }, { coefficient := 1, powers := [(29, 1), (35, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (50, 1)] }, { coefficient := 1, powers := [(11, 1), (21, 1), (56, 1)] }, { coefficient := 1, powers := [(11, 1), (27, 1)] }, { coefficient := 1, powers := [(16, 1), (21, 1), (50, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (36, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (44, 1), (51, 1)] }, { coefficient := 1, powers := [(39, 1)] }, { coefficient := 1, powers := [(44, 1)] }, { coefficient := 1, powers := [(51, 1)] }, { coefficient := 1, powers := [(56, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (35, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (38, 1), (55, 1)] }, { coefficient := 1, powers := [(2, 1), (41, 1), (48, 1)] }, { coefficient := 1, powers := [(11, 1), (21, 1), (55, 1)] }, { coefficient := 1, powers := [(11, 1), (26, 1), (41, 1)] }, { coefficient := 1, powers := [(15, 1), (21, 1), (48, 1)] }, { coefficient := 1, powers := [(15, 1), (26, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (36, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (44, 1), (51, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1), (39, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1), (44, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1), (51, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (35, 1), (58, 1)] }, { coefficient := 1, powers := [(0, 1), (38, 1), (55, 1)] }, { coefficient := 1, powers := [(0, 1), (41, 1), (48, 1)] }, { coefficient := 1, powers := [(3, 1), (23, 1), (58, 1)] }, { coefficient := 1, powers := [(3, 1), (29, 1), (55, 1)] }, { coefficient := 1, powers := [(3, 1), (32, 1), (48, 1)] }, { coefficient := 1, powers := [(6, 1), (18, 1), (58, 1)] }, { coefficient := 1, powers := [(6, 1), (29, 1), (41, 1)] }, { coefficient := 1, powers := [(6, 1), (32, 1), (38, 1)] }, { coefficient := 1, powers := [(9, 1), (18, 1), (55, 1)] }, { coefficient := 1, powers := [(9, 1), (23, 1), (41, 1)] }, { coefficient := 1, powers := [(9, 1), (32, 1), (35, 1)] }, { coefficient := 1, powers := [(13, 1), (18, 1), (48, 1)] }, { coefficient := 1, powers := [(13, 1), (23, 1), (38, 1)] }, { coefficient := 1, powers := [(13, 1), (29, 1), (35, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (61, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(38, 1)] }],
  [{ coefficient := 1, powers := [(39, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(55, 1)] }],
  [{ coefficient := 1, powers := [(56, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(23, 1), (64, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(25, 1), (65, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(28, 1), (66, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 34 → SparsePoly (Fin 67) := ![
  [{ coefficient := -2, powers := [(2, 1), (6, 1), (18, 1), (21, 1), (58, 1), (61, 2), (65, 1)] }, { coefficient := -2, powers := [(2, 1), (6, 1), (18, 1), (26, 1), (58, 1), (61, 2), (65, 1)] }, { coefficient := 2, powers := [(3, 1), (9, 1), (26, 1), (32, 1), (61, 1), (65, 1)] }, { coefficient := 1, powers := [(6, 1), (13, 1), (21, 1), (23, 1), (29, 1), (61, 1), (64, 1), (65, 1)] }, { coefficient := 1, powers := [(6, 1), (13, 1), (23, 1), (26, 1), (29, 1), (61, 1), (64, 1), (65, 1)] }, { coefficient := -2, powers := [(6, 1), (18, 1), (26, 1), (41, 1), (48, 1), (59, 1), (61, 1), (65, 1)] }, { coefficient := 1, powers := [(9, 1), (13, 1), (18, 1), (23, 1), (26, 1), (61, 1), (64, 1), (65, 1)] }, { coefficient := -1, powers := [(9, 1), (13, 1), (21, 1), (23, 1), (51, 1), (61, 1), (62, 1), (65, 1)] }, { coefficient := -1, powers := [(9, 1), (13, 1), (21, 1), (23, 1), (56, 1), (61, 1), (62, 1), (65, 1)] }, { coefficient := -1, powers := [(9, 1), (13, 1), (23, 1), (27, 1), (61, 1), (62, 1), (65, 1)] }, { coefficient := -1, powers := [(13, 1), (21, 1), (23, 1), (29, 1), (35, 1), (51, 1), (61, 1), (65, 1)] }, { coefficient := -1, powers := [(13, 1), (21, 1), (23, 1), (29, 1), (35, 1), (56, 1), (61, 1), (65, 1)] }, { coefficient := -1, powers := [(13, 1), (23, 1), (26, 1), (29, 1), (35, 1), (51, 2), (61, 1), (62, 1), (65, 1)] }, { coefficient := -1, powers := [(13, 1), (23, 1), (26, 1), (29, 1), (35, 1), (51, 1), (56, 1), (61, 1), (62, 1), (65, 1)] }, { coefficient := 1, powers := [(13, 1), (23, 1), (26, 1), (29, 1), (36, 1), (61, 1), (62, 1), (65, 1)] }, { coefficient := 1, powers := [(13, 1), (23, 1), (27, 1), (29, 1), (35, 1), (51, 1), (61, 1), (62, 1), (65, 1)] }, { coefficient := -1, powers := [(13, 1), (23, 1), (27, 1), (29, 1), (35, 1), (61, 1), (65, 1)] }],
  [{ coefficient := 2, powers := [(6, 1), (11, 1), (18, 1), (26, 1), (59, 1), (61, 1), (65, 1)] }, { coefficient := 2, powers := [(6, 1), (29, 1), (65, 1)] }, { coefficient := -2, powers := [(9, 1), (23, 1), (65, 1)] }, { coefficient := 2, powers := [(9, 1), (24, 1), (27, 1), (63, 1), (65, 1), (66, 1)] }, { coefficient := -2, powers := [(9, 1), (63, 1), (65, 1)] }],
  [{ coefficient := -2, powers := [(3, 1), (26, 1), (32, 1), (61, 1), (65, 1)] }, { coefficient := -1, powers := [(13, 1), (18, 1), (23, 1), (26, 1), (61, 1), (64, 1), (65, 1)] }, { coefficient := -1, powers := [(13, 1), (21, 1), (23, 1), (44, 1), (61, 1), (62, 1), (65, 1)] }, { coefficient := 1, powers := [(13, 1), (23, 1), (27, 1), (61, 1), (62, 1), (65, 1)] }],
  [{ coefficient := -2, powers := [(3, 1), (16, 1), (32, 1), (61, 1)] }, { coefficient := -1, powers := [(13, 1), (16, 1), (18, 1), (23, 1), (61, 1), (64, 1)] }],
  [{ coefficient := 2, powers := [(3, 1), (9, 1), (32, 1), (63, 1), (66, 1)] }, { coefficient := 2, powers := [(9, 1), (13, 1), (18, 1), (63, 1), (66, 1)] }],
  [{ coefficient := 2, powers := [(23, 1), (65, 1)] }],
  [{ coefficient := 2, powers := [(6, 1), (18, 1), (48, 1), (59, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(13, 1), (23, 1), (29, 1), (35, 1), (51, 1), (61, 1), (62, 1)] }],
  [{ coefficient := 2, powers := [(3, 1), (32, 1), (61, 1)] }, { coefficient := 1, powers := [(13, 1), (18, 1), (23, 1), (61, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (13, 1), (23, 1), (61, 1), (62, 1)] }, { coefficient := 1, powers := [(13, 1), (23, 1), (29, 1), (35, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (21, 1), (23, 1), (61, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (23, 1), (26, 1), (29, 1), (35, 1), (51, 1), (61, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(13, 1), (16, 1), (23, 1), (29, 1), (35, 1), (61, 1), (62, 1)] }],
  [{ coefficient := 2, powers := [(9, 1), (63, 1)] }],
  [{ coefficient := -2, powers := [(9, 1), (27, 1), (63, 1), (66, 1)] }],
  [{ coefficient := 2, powers := [(2, 1), (6, 1), (18, 1), (58, 1), (61, 2)] }, { coefficient := -1, powers := [(6, 1), (13, 1), (23, 1), (29, 1), (61, 1), (64, 1)] }, { coefficient := -1, powers := [(13, 1), (23, 1), (29, 1), (36, 1), (61, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (23, 1), (29, 1), (35, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (23, 1), (62, 1)] }],
  [{ coefficient := 2, powers := [(9, 1)] }],
  [{ coefficient := -1, powers := [(13, 1), (23, 1), (64, 1)] }, { coefficient := 2, powers := [(13, 1)] }],
  [{ coefficient := -1, powers := [(13, 1), (23, 1), (61, 1), (62, 1)] }],
  [{ coefficient := -2, powers := [(3, 1), (9, 1), (32, 1), (63, 1)] }, { coefficient := -2, powers := [(9, 1), (13, 1), (18, 1), (63, 1)] }, { coefficient := -1, powers := [(9, 1), (13, 1), (23, 1), (62, 1)] }, { coefficient := -1, powers := [(13, 1), (23, 2), (29, 1), (35, 1), (64, 1)] }],
  [{ coefficient := -2, powers := [(6, 1), (18, 1), (59, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (23, 1), (29, 1), (35, 1), (61, 1), (62, 1)] }],
  [{ coefficient := -2, powers := [] }],
  [{ coefficient := 2, powers := [(3, 1), (9, 1), (32, 1), (36, 1), (59, 1), (63, 1)] }, { coefficient := 2, powers := [(3, 1), (9, 1), (32, 1), (39, 1), (56, 1), (63, 1)] }, { coefficient := 2, powers := [(3, 1), (9, 1), (32, 1), (44, 1), (51, 1), (63, 1)] }, { coefficient := 2, powers := [(9, 1), (13, 1), (18, 1), (36, 1), (59, 1), (63, 1)] }, { coefficient := 2, powers := [(9, 1), (13, 1), (18, 1), (39, 1), (56, 1), (63, 1)] }, { coefficient := 2, powers := [(9, 1), (13, 1), (18, 1), (44, 1), (51, 1), (63, 1)] }, { coefficient := 1, powers := [(9, 1), (13, 1), (23, 1), (36, 1), (59, 1), (62, 1)] }, { coefficient := 1, powers := [(9, 1), (13, 1), (23, 1), (39, 1), (56, 1), (62, 1)] }, { coefficient := 1, powers := [(9, 1), (13, 1), (23, 1), (44, 1), (51, 1), (62, 1)] }, { coefficient := 2, powers := [(9, 1), (27, 1), (41, 1), (53, 1), (63, 1), (66, 1)] }, { coefficient := -2, powers := [(9, 1), (41, 1), (51, 1), (63, 1)] }, { coefficient := -2, powers := [(9, 1), (41, 1)] }, { coefficient := 1, powers := [(13, 1), (23, 2), (29, 1), (35, 1), (36, 1), (59, 1), (64, 1)] }, { coefficient := 1, powers := [(13, 1), (23, 2), (29, 1), (35, 1), (39, 1), (56, 1), (64, 1)] }, { coefficient := 1, powers := [(13, 1), (23, 2), (29, 1), (35, 1), (44, 1), (51, 1), (64, 1)] }, { coefficient := -1, powers := [(13, 1), (23, 1), (29, 1), (35, 1), (44, 1), (64, 1)] }, { coefficient := -1, powers := [(13, 1), (23, 1), (44, 1), (50, 1), (62, 1)] }, { coefficient := 1, powers := [(13, 1), (23, 1), (48, 1), (64, 1)] }, { coefficient := -2, powers := [(13, 1), (48, 1)] }, { coefficient := 2, powers := [(35, 1), (58, 1)] }, { coefficient := 2, powers := [(38, 1), (55, 1)] }, { coefficient := 2, powers := [(41, 1), (48, 1)] }],
  [{ coefficient := -2, powers := [(2, 1), (6, 1), (18, 1), (35, 1), (58, 1), (59, 1), (61, 1)] }, { coefficient := -2, powers := [(2, 1), (6, 1), (18, 1), (58, 1), (61, 1)] }, { coefficient := -2, powers := [(3, 1), (32, 1), (48, 1)] }, { coefficient := 1, powers := [(6, 1), (13, 1), (23, 1), (29, 1), (35, 1), (59, 1), (64, 1)] }, { coefficient := 1, powers := [(6, 1), (13, 1), (23, 1), (29, 1), (64, 1)] }, { coefficient := -2, powers := [(6, 1), (18, 1), (58, 1)] }, { coefficient := -1, powers := [(9, 1), (13, 1), (23, 1), (51, 1), (62, 1)] }, { coefficient := -1, powers := [(13, 1), (18, 1), (23, 1), (48, 1), (64, 1)] }, { coefficient := -1, powers := [(13, 1), (23, 1), (29, 1), (35, 1), (39, 1), (56, 1), (62, 1)] }, { coefficient := -1, powers := [(13, 1), (23, 1), (29, 1), (35, 1), (51, 1)] }, { coefficient := 1, powers := [(13, 1), (23, 1), (29, 1), (36, 1), (62, 1)] }, { coefficient := 1, powers := [(13, 1), (23, 1), (50, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (13, 1), (23, 1), (56, 1), (61, 1), (62, 1)] }, { coefficient := 2, powers := [(3, 1), (16, 1), (25, 1), (26, 1), (32, 1), (61, 1), (65, 1)] }, { coefficient := 2, powers := [(6, 1), (15, 1), (18, 1), (26, 1), (59, 1), (61, 1)] }, { coefficient := 2, powers := [(6, 1), (32, 1)] }, { coefficient := 1, powers := [(13, 1), (16, 1), (18, 1), (23, 1), (25, 1), (26, 1), (61, 1), (64, 1), (65, 1)] }, { coefficient := 1, powers := [(13, 1), (16, 1), (21, 1), (23, 1), (25, 1), (44, 1), (61, 1), (62, 1), (65, 1)] }, { coefficient := -1, powers := [(13, 1), (16, 1), (23, 1), (25, 1), (27, 1), (61, 1), (62, 1), (65, 1)] }, { coefficient := 1, powers := [(13, 1), (16, 1), (23, 1), (27, 1), (61, 1), (62, 1)] }, { coefficient := 1, powers := [(13, 1), (23, 2), (64, 1)] }, { coefficient := -2, powers := [(13, 1), (23, 1), (25, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (13, 1), (23, 1)] }, { coefficient := -1, powers := [(13, 1), (23, 1), (29, 1), (35, 1), (56, 1)] }],
  [{ coefficient := 2, powers := [(2, 1), (6, 1), (18, 1), (38, 1), (59, 1), (61, 1)] }, { coefficient := 2, powers := [(3, 1), (29, 1)] }, { coefficient := 2, powers := [(6, 1), (11, 1), (18, 1), (21, 1), (59, 1), (61, 1)] }, { coefficient := -2, powers := [(6, 1), (16, 1), (18, 1), (21, 1), (48, 1), (59, 1), (61, 1)] }],
  [{ coefficient := 2, powers := [(3, 1), (9, 1), (32, 1)] }, { coefficient := 2, powers := [(9, 1), (13, 1), (18, 1)] }],
  [{ coefficient := 2, powers := [(6, 1), (13, 1), (29, 1)] }, { coefficient := 1, powers := [(9, 1), (13, 1), (23, 1)] }, { coefficient := 1, powers := [(13, 1), (23, 1), (29, 1), (35, 1), (51, 1)] }, { coefficient := 1, powers := [(13, 1), (23, 1), (29, 1), (35, 1), (56, 1)] }],
  [{ coefficient := 2, powers := [(2, 1), (6, 1), (16, 1), (18, 1), (21, 1), (58, 1), (61, 2)] }, { coefficient := 2, powers := [(2, 1), (6, 1), (16, 1), (18, 1), (26, 1), (58, 1), (61, 2)] }, { coefficient := -2, powers := [(3, 1), (9, 1), (16, 1), (26, 1), (32, 1), (61, 1)] }, { coefficient := 2, powers := [(3, 1), (11, 1), (26, 1), (32, 1), (61, 1)] }, { coefficient := -2, powers := [(3, 1), (23, 1), (58, 1)] }, { coefficient := -2, powers := [(6, 1), (11, 1), (18, 1), (26, 1), (41, 1), (59, 1), (61, 1)] }, { coefficient := -1, powers := [(6, 1), (13, 1), (16, 1), (21, 1), (23, 1), (29, 1), (61, 1), (64, 1)] }, { coefficient := -1, powers := [(6, 1), (13, 1), (16, 1), (23, 1), (26, 1), (29, 1), (61, 1), (64, 1)] }, { coefficient := 2, powers := [(6, 1), (16, 1), (18, 1), (26, 1), (41, 1), (48, 1), (59, 1), (61, 1)] }, { coefficient := -2, powers := [(6, 1), (29, 1), (41, 1)] }, { coefficient := -1, powers := [(9, 1), (13, 1), (16, 1), (18, 1), (23, 1), (26, 1), (61, 1), (64, 1)] }, { coefficient := 1, powers := [(9, 1), (13, 1), (16, 1), (21, 1), (23, 1), (51, 1), (61, 1), (62, 1)] }, { coefficient := 1, powers := [(9, 1), (13, 1), (16, 1), (21, 1), (23, 1), (56, 1), (61, 1), (62, 1)] }, { coefficient := 1, powers := [(9, 1), (13, 1), (16, 1), (23, 1), (27, 1), (61, 1), (62, 1)] }, { coefficient := -2, powers := [(9, 1), (24, 1), (27, 1), (41, 1), (63, 1), (66, 1)] }, { coefficient := 2, powers := [(9, 1), (41, 1), (63, 1)] }, { coefficient := 1, powers := [(11, 1), (13, 1), (18, 1), (23, 1), (26, 1), (61, 1), (64, 1)] }, { coefficient := 1, powers := [(11, 1), (13, 1), (21, 1), (23, 1), (44, 1), (61, 1), (62, 1)] }, { coefficient := -1, powers := [(11, 1), (13, 1), (23, 1), (27, 1), (61, 1), (62, 1)] }, { coefficient := 1, powers := [(13, 1), (16, 1), (21, 1), (23, 1), (29, 1), (35, 1), (51, 1), (61, 1)] }, { coefficient := 1, powers := [(13, 1), (16, 1), (21, 1), (23, 1), (29, 1), (35, 1), (56, 1), (61, 1)] }, { coefficient := 1, powers := [(13, 1), (16, 1), (23, 1), (26, 1), (29, 1), (35, 1), (51, 2), (61, 1), (62, 1)] }, { coefficient := 1, powers := [(13, 1), (16, 1), (23, 1), (26, 1), (29, 1), (35, 1), (51, 1), (56, 1), (61, 1), (62, 1)] }, { coefficient := -1, powers := [(13, 1), (16, 1), (23, 1), (26, 1), (29, 1), (36, 1), (61, 1), (62, 1)] }, { coefficient := -1, powers := [(13, 1), (16, 1), (23, 1), (27, 1), (29, 1), (35, 1), (51, 1), (61, 1), (62, 1)] }, { coefficient := 1, powers := [(13, 1), (16, 1), (23, 1), (27, 1), (29, 1), (35, 1), (61, 1)] }],
  [{ coefficient := -2, powers := [(3, 1), (9, 1), (32, 1), (39, 1), (63, 1)] }, { coefficient := -2, powers := [(3, 1), (9, 1), (32, 1), (44, 1), (63, 1)] }, { coefficient := -2, powers := [(9, 1), (13, 1), (18, 1), (39, 1), (63, 1)] }, { coefficient := -2, powers := [(9, 1), (13, 1), (18, 1), (44, 1), (63, 1)] }]
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
    (values : Fin 67 → R) :
    ¬ ∀ index : Fin 34,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((2 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (2 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (2 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component39.SelectedLeafB1_2_2_7.selectedHasNoCommonZero

end Krenn.Component39.SelectedLeafB1_2_2_7
