import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component18.SelectedLeafB7_6_1_3

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "828b0daa304736061855c82d9ee925bc44f23c7e177bdd8626bc7e8cff3e1fbc"
def certificateSHA256 : String := "3317fa2efd0d3f12df2782a52cd5a1fb6f45e6631786353b8d57166a06fe6d05"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 23 → Fin 670 := ![
  148,
  149,
  151,
  162,
  319,
  403,
  449,
  478,
  501,
  502,
  505,
  523,
  604,
  605,
  606,
  607,
  645,
  649,
  656,
  660,
  665,
  667,
  669
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 23 → SparsePoly (Fin 69) := ![
  [{ coefficient := 1, powers := [(11, 1), (25, 1)] }, { coefficient := 1, powers := [(15, 1), (19, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (26, 1)] }, { coefficient := 1, powers := [(15, 1), (19, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (31, 1)] }, { coefficient := 1, powers := [(15, 1), (23, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (19, 1)] }, { coefficient := 1, powers := [(17, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(30, 1), (53, 1)] }, { coefficient := 1, powers := [(31, 1), (42, 1)] }, { coefficient := 1, powers := [(31, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (19, 1), (52, 1)] }, { coefficient := 1, powers := [(17, 1), (19, 1), (56, 1)] }, { coefficient := 1, powers := [(17, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (42, 1)] }, { coefficient := 1, powers := [(17, 1), (46, 1)] }, { coefficient := 1, powers := [(17, 1), (52, 1)] }, { coefficient := 1, powers := [(17, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1)] }, { coefficient := 1, powers := [(17, 1), (23, 1)] }, { coefficient := 1, powers := [(17, 1), (29, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (25, 1), (59, 1)] }, { coefficient := 1, powers := [(11, 1), (25, 1), (46, 1)] }, { coefficient := 1, powers := [(15, 1), (25, 1), (42, 1)] }, { coefficient := 1, powers := [(15, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (26, 1), (59, 1)] }, { coefficient := 1, powers := [(11, 1), (26, 1), (46, 1)] }, { coefficient := 1, powers := [(15, 1), (26, 1), (42, 1)] }, { coefficient := 1, powers := [(15, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (31, 1), (59, 1)] }, { coefficient := 1, powers := [(11, 1), (31, 1), (46, 1)] }, { coefficient := 1, powers := [(15, 1), (30, 1), (53, 1)] }, { coefficient := 1, powers := [(15, 1), (31, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (23, 1), (59, 1)] }, { coefficient := 1, powers := [(11, 1), (23, 1), (56, 1)] }, { coefficient := 1, powers := [(11, 1), (30, 1)] }, { coefficient := 1, powers := [(15, 1), (23, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (46, 1)] }, { coefficient := 1, powers := [(4, 1), (27, 1), (59, 1)] }, { coefficient := 1, powers := [(4, 1), (36, 1)] }, { coefficient := 1, powers := [(11, 1), (27, 1), (46, 1)] }, { coefficient := 1, powers := [(15, 1), (22, 1)] }, { coefficient := 1, powers := [(15, 1), (27, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (52, 1)] }, { coefficient := 1, powers := [(7, 1), (21, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (33, 1)] }, { coefficient := 1, powers := [(11, 1), (21, 1), (56, 1)] }, { coefficient := 1, powers := [(11, 1), (28, 1)] }, { coefficient := 1, powers := [(15, 1), (21, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (59, 1)] }, { coefficient := 1, powers := [(11, 1), (46, 1)] }, { coefficient := 1, powers := [(11, 1), (56, 1)] }, { coefficient := 1, powers := [(15, 1), (42, 1)] }, { coefficient := 1, powers := [(15, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (52, 1)] }, { coefficient := 1, powers := [(22, 1), (56, 1)] }, { coefficient := 1, powers := [(28, 1), (42, 1)] }, { coefficient := 1, powers := [(28, 1), (46, 1)] }, { coefficient := 1, powers := [(33, 1), (39, 1)] }, { coefficient := 1, powers := [(36, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (39, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (42, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(42, 1)] }, { coefficient := 1, powers := [(46, 1)] }, { coefficient := 1, powers := [(52, 1)] }, { coefficient := 1, powers := [(56, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (39, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (42, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(17, 1), (30, 1), (42, 1)] }, { coefficient := 1, powers := [(17, 1), (30, 1), (46, 1)] }, { coefficient := 1, powers := [(17, 1), (30, 1), (52, 1)] }, { coefficient := 1, powers := [(17, 1), (30, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (39, 1), (59, 1)] }, { coefficient := 1, powers := [(1, 1), (42, 1), (56, 1)] }, { coefficient := 1, powers := [(1, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(4, 1), (28, 1), (59, 1)] }, { coefficient := 1, powers := [(4, 1), (33, 1), (56, 1)] }, { coefficient := 1, powers := [(4, 1), (36, 1), (52, 1)] }, { coefficient := 1, powers := [(7, 1), (22, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (33, 1), (46, 1)] }, { coefficient := 1, powers := [(7, 1), (36, 1), (42, 1)] }, { coefficient := 1, powers := [(11, 1), (22, 1), (56, 1)] }, { coefficient := 1, powers := [(11, 1), (28, 1), (46, 1)] }, { coefficient := 1, powers := [(11, 1), (36, 1), (39, 1)] }, { coefficient := 1, powers := [(15, 1), (22, 1), (52, 1)] }, { coefficient := 1, powers := [(15, 1), (28, 1), (42, 1)] }, { coefficient := 1, powers := [(15, 1), (33, 1), (39, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(56, 1)] }],
  [{ coefficient := 1, powers := [(25, 1)] }],
  [{ coefficient := 1, powers := [(31, 1), (68, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 23 → SparsePoly (Fin 69) := ![
  [{ coefficient := -1, powers := [(28, 1), (30, 1), (46, 1), (53, 1), (68, 1)] }, { coefficient := -1, powers := [(30, 1), (36, 1), (39, 1), (53, 1), (68, 1)] }],
  [{ coefficient := 1, powers := [(28, 1), (30, 1), (46, 1), (68, 1)] }, { coefficient := 1, powers := [(30, 1), (36, 1), (39, 1), (68, 1)] }],
  [{ coefficient := 1, powers := [(28, 1), (46, 1), (68, 1)] }, { coefficient := 1, powers := [(36, 1), (39, 1), (68, 1)] }],
  [{ coefficient := 2, powers := [(7, 1), (23, 1), (33, 1), (46, 1), (52, 1), (63, 1)] }, { coefficient := -1, powers := [(7, 1), (23, 1), (36, 1), (46, 1), (52, 1), (63, 1)] }, { coefficient := -1, powers := [(7, 1), (23, 1), (36, 1), (52, 2), (63, 1)] }, { coefficient := 2, powers := [(7, 1), (29, 1), (33, 1), (46, 1), (52, 1), (63, 1)] }, { coefficient := -1, powers := [(7, 1), (29, 1), (36, 1), (46, 1), (52, 1), (63, 1)] }, { coefficient := -1, powers := [(7, 1), (29, 1), (36, 1), (52, 2), (63, 1)] }],
  [{ coefficient := 1, powers := [(15, 1), (21, 1), (46, 1), (68, 1)] }, { coefficient := 1, powers := [(15, 1), (22, 1), (68, 1)] }, { coefficient := 1, powers := [(15, 1), (27, 1), (52, 1), (68, 1)] }, { coefficient := -1, powers := [(15, 1), (28, 1), (68, 1)] }, { coefficient := -2, powers := [(15, 1), (33, 1), (38, 1), (46, 1), (68, 1)] }, { coefficient := 1, powers := [(15, 1), (36, 1), (38, 1), (46, 1), (68, 1)] }, { coefficient := 1, powers := [(15, 1), (36, 1), (38, 1), (52, 1), (68, 1)] }],
  [{ coefficient := -2, powers := [(7, 1), (23, 1), (33, 1), (46, 1), (63, 1)] }, { coefficient := 1, powers := [(7, 1), (23, 1), (36, 1), (46, 1), (63, 1)] }, { coefficient := 1, powers := [(7, 1), (23, 1), (36, 1), (52, 1), (63, 1)] }, { coefficient := -2, powers := [(7, 1), (29, 1), (33, 1), (46, 1), (63, 1)] }, { coefficient := 1, powers := [(7, 1), (29, 1), (36, 1), (46, 1), (63, 1)] }, { coefficient := 1, powers := [(7, 1), (29, 1), (36, 1), (52, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (7, 1), (30, 1), (36, 1), (63, 1)] }, { coefficient := -1, powers := [(1, 1), (30, 1), (63, 1)] }],
  [{ coefficient := 2, powers := [(7, 1), (33, 1), (46, 1), (63, 1)] }, { coefficient := -1, powers := [(7, 1), (36, 1), (46, 1), (63, 1)] }, { coefficient := -1, powers := [(7, 1), (36, 1), (52, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(21, 1), (42, 1), (46, 1)] }, { coefficient := -1, powers := [(21, 1), (46, 2)] }, { coefficient := -1, powers := [(22, 1), (42, 1)] }, { coefficient := -1, powers := [(22, 1), (46, 1)] }, { coefficient := -2, powers := [(22, 1), (52, 1)] }, { coefficient := -1, powers := [(27, 1), (42, 1), (52, 1)] }, { coefficient := -1, powers := [(27, 1), (46, 1), (52, 1)] }, { coefficient := 2, powers := [(33, 1), (38, 1), (42, 1), (46, 1)] }, { coefficient := 2, powers := [(33, 1), (38, 1), (46, 2)] }, { coefficient := 2, powers := [(33, 1), (38, 1), (46, 1), (52, 1)] }, { coefficient := -1, powers := [(36, 1), (38, 1), (42, 1), (46, 1)] }, { coefficient := -1, powers := [(36, 1), (38, 1), (42, 1), (52, 1)] }, { coefficient := -1, powers := [(36, 1), (38, 1), (46, 2)] }, { coefficient := -2, powers := [(36, 1), (38, 1), (46, 1), (52, 1)] }, { coefficient := -1, powers := [(36, 1), (38, 1), (52, 2)] }, { coefficient := -1, powers := [(36, 1), (39, 1)] }],
  [{ coefficient := -1, powers := [(23, 1), (28, 1), (46, 1), (68, 1)] }, { coefficient := -1, powers := [(23, 1), (36, 1), (39, 1), (68, 1)] }],
  [{ coefficient := -1, powers := [(21, 1), (46, 1), (68, 1)] }, { coefficient := -1, powers := [(22, 1), (68, 1)] }, { coefficient := -1, powers := [(27, 1), (52, 1), (68, 1)] }, { coefficient := 1, powers := [(28, 1), (68, 1)] }, { coefficient := 2, powers := [(33, 1), (38, 1), (46, 1), (68, 1)] }, { coefficient := -1, powers := [(36, 1), (38, 1), (46, 1), (68, 1)] }, { coefficient := -1, powers := [(36, 1), (38, 1), (52, 1), (68, 1)] }],
  [{ coefficient := -1, powers := [(26, 1), (28, 1), (46, 1), (68, 1)] }, { coefficient := -1, powers := [(26, 1), (36, 1), (39, 1), (68, 1)] }],
  [{ coefficient := 1, powers := [(52, 1)] }],
  [{ coefficient := -1, powers := [(46, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (31, 1), (46, 1), (68, 1)] }, { coefficient := 1, powers := [(22, 1), (31, 1), (68, 1)] }, { coefficient := 1, powers := [(23, 1), (26, 1), (28, 1), (46, 1), (68, 1)] }, { coefficient := 1, powers := [(23, 1), (26, 1), (36, 1), (39, 1), (68, 1)] }, { coefficient := 1, powers := [(27, 1), (31, 1), (52, 1), (68, 1)] }, { coefficient := -1, powers := [(27, 1), (52, 1)] }, { coefficient := -1, powers := [(28, 1), (31, 1), (68, 1)] }, { coefficient := 1, powers := [(28, 1)] }, { coefficient := -2, powers := [(31, 1), (33, 1), (38, 1), (46, 1), (68, 1)] }, { coefficient := 1, powers := [(31, 1), (36, 1), (38, 1), (46, 1), (68, 1)] }, { coefficient := 1, powers := [(31, 1), (36, 1), (38, 1), (52, 1), (68, 1)] }],
  [{ coefficient := 1, powers := [(15, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (36, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (7, 1), (36, 1), (63, 1)] }, { coefficient := 1, powers := [(1, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (7, 1), (36, 1), (39, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (7, 1), (36, 1), (46, 1), (52, 1)] }, { coefficient := -1, powers := [(1, 1), (39, 1), (59, 1)] }, { coefficient := -1, powers := [(1, 1), (46, 1), (52, 1)] }, { coefficient := -2, powers := [(7, 1), (33, 1), (38, 1), (46, 1), (59, 1)] }, { coefficient := -2, powers := [(7, 1), (33, 1), (46, 1)] }, { coefficient := 1, powers := [(7, 1), (36, 1), (38, 1), (46, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (36, 1), (38, 1), (52, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (36, 1), (46, 1)] }, { coefficient := 1, powers := [(7, 1), (36, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (2, 1), (7, 1), (36, 1), (42, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (7, 1), (36, 1), (42, 1)] }, { coefficient := -1, powers := [(1, 1), (2, 1), (42, 1), (63, 1)] }, { coefficient := 1, powers := [(1, 1), (42, 1)] }, { coefficient := 1, powers := [(4, 1), (33, 1)] }, { coefficient := 2, powers := [(7, 1), (17, 1), (19, 1), (23, 1), (33, 1), (46, 1), (63, 1)] }, { coefficient := -1, powers := [(7, 1), (17, 1), (19, 1), (23, 1), (36, 1), (46, 1), (63, 1)] }, { coefficient := -1, powers := [(7, 1), (17, 1), (19, 1), (23, 1), (36, 1), (52, 1), (63, 1)] }, { coefficient := 2, powers := [(7, 1), (17, 1), (19, 1), (29, 1), (33, 1), (46, 1), (63, 1)] }, { coefficient := -1, powers := [(7, 1), (17, 1), (19, 1), (29, 1), (36, 1), (46, 1), (63, 1)] }, { coefficient := -1, powers := [(7, 1), (17, 1), (19, 1), (29, 1), (36, 1), (52, 1), (63, 1)] }, { coefficient := -1, powers := [(7, 1), (36, 1)] }, { coefficient := -1, powers := [(11, 1), (21, 1), (31, 1), (46, 1), (68, 1)] }, { coefficient := 1, powers := [(11, 1), (21, 1), (46, 1)] }, { coefficient := -1, powers := [(11, 1), (22, 1), (31, 1), (68, 1)] }, { coefficient := 1, powers := [(11, 1), (22, 1)] }, { coefficient := -1, powers := [(11, 1), (27, 1), (31, 1), (52, 1), (68, 1)] }, { coefficient := 1, powers := [(11, 1), (27, 1), (52, 1)] }, { coefficient := 1, powers := [(11, 1), (28, 1), (31, 1), (68, 1)] }, { coefficient := -1, powers := [(11, 1), (28, 1)] }, { coefficient := 2, powers := [(11, 1), (31, 1), (33, 1), (38, 1), (46, 1), (68, 1)] }, { coefficient := -1, powers := [(11, 1), (31, 1), (36, 1), (38, 1), (46, 1), (68, 1)] }, { coefficient := -1, powers := [(11, 1), (31, 1), (36, 1), (38, 1), (52, 1), (68, 1)] }, { coefficient := -1, powers := [(15, 1), (22, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (21, 1), (42, 1), (46, 1), (59, 1)] }, { coefficient := 1, powers := [(4, 1), (21, 1), (46, 2), (59, 1)] }, { coefficient := 1, powers := [(4, 1), (22, 1), (42, 1), (59, 1)] }, { coefficient := 1, powers := [(4, 1), (22, 1), (46, 1), (59, 1)] }, { coefficient := 2, powers := [(4, 1), (22, 1), (52, 1), (59, 1)] }, { coefficient := 1, powers := [(4, 1), (27, 1), (42, 1), (52, 1), (59, 1)] }, { coefficient := 1, powers := [(4, 1), (27, 1), (46, 1), (52, 1), (59, 1)] }, { coefficient := -2, powers := [(4, 1), (33, 1), (38, 1), (42, 1), (46, 1), (59, 1)] }, { coefficient := -2, powers := [(4, 1), (33, 1), (38, 1), (46, 2), (59, 1)] }, { coefficient := -2, powers := [(4, 1), (33, 1), (38, 1), (46, 1), (52, 1), (59, 1)] }, { coefficient := 1, powers := [(4, 1), (36, 1), (38, 1), (42, 1), (46, 1), (59, 1)] }, { coefficient := 1, powers := [(4, 1), (36, 1), (38, 1), (42, 1), (52, 1), (59, 1)] }, { coefficient := 1, powers := [(4, 1), (36, 1), (38, 1), (46, 2), (59, 1)] }, { coefficient := 2, powers := [(4, 1), (36, 1), (38, 1), (46, 1), (52, 1), (59, 1)] }, { coefficient := 1, powers := [(4, 1), (36, 1), (38, 1), (52, 2), (59, 1)] }, { coefficient := 1, powers := [(4, 1), (36, 1), (39, 1), (59, 1)] }, { coefficient := -2, powers := [(7, 1), (17, 1), (23, 1), (33, 1), (46, 1), (52, 1), (63, 1)] }, { coefficient := 1, powers := [(7, 1), (17, 1), (23, 1), (36, 1), (46, 1), (52, 1), (63, 1)] }, { coefficient := 1, powers := [(7, 1), (17, 1), (23, 1), (36, 1), (52, 2), (63, 1)] }, { coefficient := -2, powers := [(7, 1), (17, 1), (29, 1), (33, 1), (46, 1), (52, 1), (63, 1)] }, { coefficient := 1, powers := [(7, 1), (17, 1), (29, 1), (36, 1), (46, 1), (52, 1), (63, 1)] }, { coefficient := 1, powers := [(7, 1), (17, 1), (29, 1), (36, 1), (52, 2), (63, 1)] }, { coefficient := 1, powers := [(11, 1), (21, 1), (42, 1), (46, 2)] }, { coefficient := 1, powers := [(11, 1), (21, 1), (46, 3)] }, { coefficient := 1, powers := [(11, 1), (22, 1), (42, 1), (46, 1)] }, { coefficient := 1, powers := [(11, 1), (22, 1), (46, 2)] }, { coefficient := 2, powers := [(11, 1), (22, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(11, 1), (27, 1), (42, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(11, 1), (27, 1), (46, 2), (52, 1)] }, { coefficient := 1, powers := [(11, 1), (28, 1), (30, 1), (46, 1), (53, 1), (68, 1)] }, { coefficient := 1, powers := [(11, 1), (30, 1), (36, 1), (39, 1), (53, 1), (68, 1)] }, { coefficient := -2, powers := [(11, 1), (33, 1), (38, 1), (42, 1), (46, 2)] }, { coefficient := -2, powers := [(11, 1), (33, 1), (38, 1), (46, 3)] }, { coefficient := -2, powers := [(11, 1), (33, 1), (38, 1), (46, 2), (52, 1)] }, { coefficient := 1, powers := [(11, 1), (36, 1), (38, 1), (42, 1), (46, 2)] }, { coefficient := 1, powers := [(11, 1), (36, 1), (38, 1), (42, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(11, 1), (36, 1), (38, 1), (46, 3)] }, { coefficient := 2, powers := [(11, 1), (36, 1), (38, 1), (46, 2), (52, 1)] }, { coefficient := 1, powers := [(11, 1), (36, 1), (38, 1), (46, 1), (52, 2)] }, { coefficient := 1, powers := [(11, 1), (36, 1), (39, 1), (46, 1)] }, { coefficient := 1, powers := [(15, 1), (21, 1), (42, 2), (46, 1)] }, { coefficient := 1, powers := [(15, 1), (21, 1), (42, 1), (46, 2)] }, { coefficient := 1, powers := [(15, 1), (22, 1), (42, 2)] }, { coefficient := 1, powers := [(15, 1), (22, 1), (42, 1), (46, 1)] }, { coefficient := 2, powers := [(15, 1), (22, 1), (42, 1), (52, 1)] }, { coefficient := 1, powers := [(15, 1), (27, 1), (42, 2), (52, 1)] }, { coefficient := 1, powers := [(15, 1), (27, 1), (42, 1), (46, 1), (52, 1)] }, { coefficient := -2, powers := [(15, 1), (33, 1), (38, 1), (42, 2), (46, 1)] }, { coefficient := -2, powers := [(15, 1), (33, 1), (38, 1), (42, 1), (46, 2)] }, { coefficient := -2, powers := [(15, 1), (33, 1), (38, 1), (42, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(15, 1), (36, 1), (38, 1), (42, 2), (46, 1)] }, { coefficient := 1, powers := [(15, 1), (36, 1), (38, 1), (42, 2), (52, 1)] }, { coefficient := 1, powers := [(15, 1), (36, 1), (38, 1), (42, 1), (46, 2)] }, { coefficient := 2, powers := [(15, 1), (36, 1), (38, 1), (42, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(15, 1), (36, 1), (38, 1), (42, 1), (52, 2)] }, { coefficient := 1, powers := [(15, 1), (36, 1), (39, 1), (42, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (21, 1), (46, 1), (59, 1)] }, { coefficient := -1, powers := [(7, 1), (22, 1), (59, 1)] }, { coefficient := -1, powers := [(7, 1), (27, 1), (52, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (28, 1), (59, 1)] }, { coefficient := 2, powers := [(7, 1), (33, 1), (38, 1), (46, 1), (59, 1)] }, { coefficient := -1, powers := [(7, 1), (36, 1), (38, 1), (46, 1), (59, 1)] }, { coefficient := -1, powers := [(7, 1), (36, 1), (38, 1), (52, 1), (59, 1)] }, { coefficient := -1, powers := [(11, 1), (28, 1), (46, 1)] }, { coefficient := -1, powers := [(11, 1), (36, 1), (39, 1)] }, { coefficient := -1, powers := [(15, 1), (21, 1), (42, 1), (46, 1)] }, { coefficient := -1, powers := [(15, 1), (21, 1), (46, 2)] }, { coefficient := -1, powers := [(15, 1), (21, 1), (46, 1), (52, 1)] }, { coefficient := -1, powers := [(15, 1), (22, 1), (42, 1)] }, { coefficient := -1, powers := [(15, 1), (22, 1), (46, 1)] }, { coefficient := -1, powers := [(15, 1), (22, 1), (52, 1)] }, { coefficient := -1, powers := [(15, 1), (27, 1), (42, 1), (52, 1)] }, { coefficient := -1, powers := [(15, 1), (27, 1), (46, 1), (52, 1)] }, { coefficient := -1, powers := [(15, 1), (27, 1), (52, 2)] }, { coefficient := 1, powers := [(15, 1), (28, 1), (42, 1)] }, { coefficient := 1, powers := [(15, 1), (28, 1), (46, 1)] }, { coefficient := 1, powers := [(15, 1), (28, 1), (52, 1)] }, { coefficient := 2, powers := [(15, 1), (33, 1), (38, 1), (42, 1), (46, 1)] }, { coefficient := 2, powers := [(15, 1), (33, 1), (38, 1), (46, 2)] }, { coefficient := 2, powers := [(15, 1), (33, 1), (38, 1), (46, 1), (52, 1)] }, { coefficient := -1, powers := [(15, 1), (36, 1), (38, 1), (42, 1), (46, 1)] }, { coefficient := -1, powers := [(15, 1), (36, 1), (38, 1), (42, 1), (52, 1)] }, { coefficient := -1, powers := [(15, 1), (36, 1), (38, 1), (46, 2)] }, { coefficient := -2, powers := [(15, 1), (36, 1), (38, 1), (46, 1), (52, 1)] }, { coefficient := -1, powers := [(15, 1), (36, 1), (38, 1), (52, 2)] }]
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
    (values : Fin 69 → R) :
    ¬ ∀ index : Fin 23,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component18.SelectedLeafB7_6_1_3.selectedHasNoCommonZero

end Krenn.Component18.SelectedLeafB7_6_1_3
