import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component39.SelectedLeafB5_7_0

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "286db0a86358194da42ea65d59af8799e72fafd260903e129c9e067ad4fb4ff3"
def certificateSHA256 : String := "ae6d786c7302dd9ace65b5881073f702e15c25358b2721e039d782fad101ccfd"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 35 → Fin 670 := ![
  21,
  22,
  30,
  173,
  187,
  194,
  195,
  250,
  302,
  304,
  305,
  313,
  317,
  321,
  345,
  382,
  396,
  418,
  423,
  439,
  467,
  479,
  508,
  567,
  591,
  602,
  603,
  608,
  651,
  659,
  661,
  662,
  663,
  666,
  668
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 35 → SparsePoly (Fin 66) := ![
  [{ coefficient := 1, powers := [(16, 1), (20, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (23, 1)] }, { coefficient := 1, powers := [(14, 1), (18, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (18, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (40, 1)] }, { coefficient := 1, powers := [(25, 1), (46, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(26, 1), (52, 1)] }, { coefficient := -1, powers := [(27, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (23, 1), (44, 1)] }, { coefficient := 1, powers := [(16, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (49, 1)] }, { coefficient := 1, powers := [(18, 1), (49, 1)] }, { coefficient := 1, powers := [(23, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (44, 1)] }, { coefficient := 1, powers := [(4, 1), (33, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (51, 1)] }, { coefficient := 1, powers := [(7, 1), (30, 1)] }, { coefficient := 1, powers := [(10, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (44, 1)] }, { coefficient := 1, powers := [(12, 1), (56, 1)] }, { coefficient := 1, powers := [(16, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (51, 1)] }, { coefficient := 1, powers := [(22, 1), (56, 1)] }, { coefficient := 1, powers := [(27, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1), (49, 1)] }, { coefficient := 1, powers := [(23, 1), (44, 1), (49, 1)] }, { coefficient := 1, powers := [(49, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (44, 1), (49, 1)] }, { coefficient := 1, powers := [(12, 1), (26, 1), (44, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (18, 1), (56, 1)] }, { coefficient := 1, powers := [(12, 1)] }, { coefficient := 1, powers := [(16, 1), (18, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (23, 1), (39, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1), (44, 1)] }, { coefficient := 1, powers := [(16, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (46, 1)] }, { coefficient := 1, powers := [(5, 1), (26, 1), (59, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1)] }, { coefficient := 1, powers := [(16, 1), (26, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (52, 1)] }, { coefficient := 1, powers := [(12, 1), (21, 1), (56, 1)] }, { coefficient := 1, powers := [(12, 1), (27, 1)] }, { coefficient := 1, powers := [(16, 1), (21, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (39, 1)] }, { coefficient := 1, powers := [(16, 1), (44, 1)] }, { coefficient := 1, powers := [(16, 1), (51, 1)] }, { coefficient := 1, powers := [(16, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1), (51, 1)] }, { coefficient := 1, powers := [(19, 1), (51, 1)] }, { coefficient := 1, powers := [(19, 1), (56, 1)] }, { coefficient := 1, powers := [(46, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (40, 1), (56, 1)] }, { coefficient := 1, powers := [(1, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(7, 1), (33, 1), (40, 1)] }, { coefficient := 1, powers := [(14, 1), (25, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (31, 1), (56, 1)] }, { coefficient := 1, powers := [(21, 1), (49, 1), (56, 1)] }, { coefficient := 1, powers := [(21, 1), (52, 1)] }, { coefficient := 1, powers := [(27, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (49, 1), (56, 1)] }, { coefficient := 1, powers := [(22, 1), (52, 1)] }, { coefficient := 1, powers := [(27, 1), (40, 1)] }, { coefficient := 1, powers := [(27, 1), (46, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (46, 1), (51, 1)] }, { coefficient := 1, powers := [(5, 1), (27, 1), (59, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1), (51, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1), (56, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (59, 1)] }, { coefficient := 1, powers := [(10, 1), (44, 1)] }, { coefficient := 1, powers := [(10, 1), (56, 1)] }, { coefficient := 1, powers := [(14, 1), (39, 1)] }, { coefficient := 1, powers := [(14, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (51, 1)] }, { coefficient := 1, powers := [(20, 1), (56, 1)] }, { coefficient := 1, powers := [(25, 1), (39, 1)] }, { coefficient := 1, powers := [(25, 1), (44, 1)] }, { coefficient := 1, powers := [(30, 1), (36, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (40, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(19, 1), (49, 1), (56, 1)] }, { coefficient := 1, powers := [(19, 1), (52, 1)] }, { coefficient := 1, powers := [(40, 1)] }, { coefficient := 1, powers := [(46, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (40, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (56, 1)] }, { coefficient := 1, powers := [(12, 1), (22, 1), (56, 1)] }, { coefficient := 1, powers := [(12, 1), (27, 1), (46, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1), (52, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (36, 1), (59, 1)] }, { coefficient := 1, powers := [(1, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(1, 1), (44, 1), (51, 1)] }, { coefficient := 1, powers := [(4, 1), (25, 1), (59, 1)] }, { coefficient := 1, powers := [(4, 1), (30, 1), (56, 1)] }, { coefficient := 1, powers := [(4, 1), (33, 1), (51, 1)] }, { coefficient := 1, powers := [(7, 1), (20, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (30, 1), (44, 1)] }, { coefficient := 1, powers := [(7, 1), (33, 1), (39, 1)] }, { coefficient := 1, powers := [(10, 1), (20, 1), (56, 1)] }, { coefficient := 1, powers := [(10, 1), (25, 1), (44, 1)] }, { coefficient := 1, powers := [(10, 1), (33, 1), (36, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1), (51, 1)] }, { coefficient := 1, powers := [(14, 1), (25, 1), (39, 1)] }, { coefficient := 1, powers := [(14, 1), (30, 1), (36, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (61, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(40, 1), (65, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(56, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 35 → SparsePoly (Fin 66) := ![
  [{ coefficient := -2, powers := [(0, 1), (7, 1), (27, 1), (40, 1), (59, 1), (62, 1), (65, 1)] }, { coefficient := 2, powers := [(0, 1), (14, 1), (27, 1), (40, 1), (51, 1), (62, 1), (65, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (7, 1), (27, 1), (40, 1), (59, 1), (62, 1), (65, 1)] }, { coefficient := 2, powers := [(0, 1), (10, 1), (27, 1), (40, 1), (44, 1), (62, 1), (65, 1)] }, { coefficient := 2, powers := [(0, 1), (14, 1), (27, 1), (39, 1), (40, 1), (62, 1), (65, 1)] }, { coefficient := 2, powers := [(0, 1), (14, 1), (27, 1), (40, 1), (44, 1), (62, 1), (65, 1)] }, { coefficient := 2, powers := [(0, 1), (14, 1), (27, 1), (40, 1), (51, 1), (62, 1), (65, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (14, 1), (16, 1), (27, 1), (40, 1), (44, 1), (49, 1), (62, 1), (65, 2)] }, { coefficient := 2, powers := [(0, 1), (14, 1), (16, 1), (27, 1), (40, 1), (49, 1), (51, 1), (62, 1), (65, 2)] }],
  [{ coefficient := -2, powers := [(0, 1), (16, 1), (27, 1), (33, 1), (36, 1), (40, 1), (51, 1), (62, 1), (65, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (14, 1), (27, 1), (33, 1), (36, 1), (40, 1), (51, 1), (62, 1), (65, 1)] }, { coefficient := -1, powers := [(0, 1), (19, 1), (27, 1), (52, 1), (61, 1), (62, 1), (65, 1)] }, { coefficient := 1, powers := [(0, 1), (22, 1), (49, 1), (51, 1), (61, 1), (62, 1), (65, 1)] }, { coefficient := 1, powers := [(0, 1), (27, 1), (46, 1), (49, 1), (61, 1), (62, 1), (65, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (14, 1), (16, 1), (27, 1), (40, 1), (44, 1), (62, 1), (65, 2)] }, { coefficient := -2, powers := [(0, 1), (14, 1), (16, 1), (27, 1), (40, 1), (51, 1), (62, 1), (65, 2)] }],
  [{ coefficient := -1, powers := [(0, 2), (16, 1), (19, 1), (51, 1), (61, 1), (62, 1), (65, 1)] }, { coefficient := 1, powers := [(0, 1), (5, 1), (59, 1), (62, 1), (65, 1)] }, { coefficient := -1, powers := [(0, 1), (16, 1), (19, 1), (23, 1), (51, 1), (61, 1), (62, 1), (65, 1)] }, { coefficient := 1, powers := [(0, 1), (16, 1), (46, 1), (62, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (19, 1), (27, 1), (61, 1), (62, 1), (65, 1)] }, { coefficient := 1, powers := [(0, 1), (22, 1), (51, 1), (62, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (16, 1), (22, 1), (51, 1), (61, 1), (62, 1), (65, 1)] }, { coefficient := -1, powers := [(0, 1), (16, 1), (27, 1), (46, 1), (61, 1), (62, 1), (65, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (16, 1), (27, 1), (40, 1), (51, 1), (62, 1), (65, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (16, 1), (27, 1), (40, 1), (44, 1), (62, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(0, 2), (19, 1), (26, 1), (51, 1), (61, 1), (62, 1), (65, 1)] }, { coefficient := 1, powers := [(0, 1), (19, 1), (23, 1), (26, 1), (51, 1), (61, 1), (62, 1), (65, 1)] }, { coefficient := 1, powers := [(0, 1), (19, 1), (23, 1), (27, 1), (61, 1), (62, 1), (65, 1)] }, { coefficient := -1, powers := [(0, 1), (22, 1), (23, 1), (51, 1), (62, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (16, 1), (49, 1), (62, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (19, 1), (51, 1), (61, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(0, 2), (19, 1), (51, 1), (61, 1), (62, 1), (65, 1)] }, { coefficient := -1, powers := [(0, 1), (19, 1), (23, 1), (51, 1), (61, 1), (62, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (19, 1), (27, 1), (61, 1), (62, 1), (65, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (10, 1), (27, 1), (33, 1), (36, 1), (40, 1), (62, 1), (65, 1)] }, { coefficient := 2, powers := [(0, 1), (14, 1), (27, 1), (33, 1), (36, 1), (40, 1), (62, 1), (65, 1)] }, { coefficient := -1, powers := [(0, 1), (22, 1), (52, 1), (62, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (52, 1), (62, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (19, 1), (61, 1), (62, 1), (65, 1)] }, { coefficient := -1, powers := [(0, 1), (46, 1), (62, 1), (65, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (7, 1), (27, 1), (33, 1), (40, 1), (62, 1), (65, 1)] }, { coefficient := 2, powers := [(0, 1), (10, 1), (23, 1), (27, 1), (33, 1), (36, 1), (40, 1), (62, 1), (65, 1)] }, { coefficient := -2, powers := [(0, 1), (14, 1), (23, 1), (27, 1), (33, 1), (36, 1), (40, 1), (62, 1), (65, 1)] }, { coefficient := 1, powers := [(0, 1), (22, 1), (23, 1), (52, 1), (62, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(0, 2), (52, 1), (61, 1), (65, 1)] }, { coefficient := -1, powers := [(0, 1), (49, 1), (61, 1), (65, 1)] }, { coefficient := 1, powers := [(0, 1), (52, 1), (65, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (16, 1), (27, 1), (40, 1), (44, 1), (62, 1), (65, 2)] }, { coefficient := 2, powers := [(0, 1), (16, 1), (27, 1), (40, 1), (51, 1), (62, 1), (65, 2)] }],
  [{ coefficient := 1, powers := [(0, 1), (16, 1), (19, 1), (61, 1), (62, 1), (65, 1)] }, { coefficient := 1, powers := [(0, 1), (16, 1), (46, 1), (62, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (16, 1), (62, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (49, 1), (62, 1), (65, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (16, 1), (25, 1), (27, 1), (40, 1), (62, 1), (65, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (14, 1), (16, 1), (27, 1), (40, 1), (62, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(0, 2), (51, 1), (61, 1), (65, 1)] }, { coefficient := -1, powers := [(0, 1), (51, 1), (65, 1)] }, { coefficient := 1, powers := [(0, 1), (61, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (62, 1), (65, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (16, 1), (27, 1), (40, 1), (62, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (16, 1), (22, 1), (49, 1), (51, 1), (62, 1), (65, 1)] }, { coefficient := 1, powers := [(0, 1), (16, 1), (27, 1), (46, 1), (49, 1), (62, 1), (65, 1)] }, { coefficient := -1, powers := [(0, 1), (40, 1), (51, 1), (65, 1)] }, { coefficient := -1, powers := [(40, 1), (65, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (16, 1), (27, 1), (36, 1), (40, 1), (59, 1), (62, 1), (65, 1)] }, { coefficient := -2, powers := [(0, 1), (16, 1), (27, 1), (39, 1), (40, 1), (56, 1), (62, 1), (65, 1)] }, { coefficient := -2, powers := [(0, 1), (16, 1), (27, 1), (40, 2), (44, 1), (56, 1), (62, 1), (65, 2)] }, { coefficient := -2, powers := [(0, 1), (16, 1), (27, 1), (40, 2), (51, 1), (56, 1), (62, 1), (65, 2)] }, { coefficient := -2, powers := [(0, 1), (16, 1), (27, 1), (40, 1), (44, 1), (46, 1), (52, 1), (62, 1), (65, 2)] }, { coefficient := 2, powers := [(0, 1), (16, 1), (27, 1), (40, 1), (44, 1), (51, 1), (62, 1), (65, 1)] }, { coefficient := -2, powers := [(0, 1), (16, 1), (27, 1), (40, 1), (46, 1), (51, 1), (52, 1), (62, 1), (65, 2)] }],
  [{ coefficient := 1, powers := [(0, 2), (19, 1), (44, 1), (49, 1), (51, 1), (61, 1), (65, 1)] }, { coefficient := 1, powers := [(0, 1), (19, 1), (23, 1), (44, 1), (49, 1), (51, 1), (61, 1), (65, 1)] }, { coefficient := 1, powers := [(0, 1), (19, 1), (52, 1), (61, 1), (65, 1)] }, { coefficient := -1, powers := [(0, 1), (46, 1), (49, 1), (51, 1), (65, 1)] }, { coefficient := 1, powers := [(0, 1), (46, 1), (52, 1), (65, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (7, 1), (16, 1), (27, 1), (33, 1), (40, 1), (44, 1), (62, 1), (65, 1)] }, { coefficient := -2, powers := [(0, 1), (7, 1), (16, 1), (27, 1), (33, 1), (40, 1), (51, 1), (62, 1), (65, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(0, 3), (40, 1), (51, 1), (61, 1), (65, 1)] }, { coefficient := -1, powers := [(0, 2), (12, 1), (19, 1), (26, 1), (51, 1), (61, 1), (62, 1), (65, 1)] }, { coefficient := -1, powers := [(0, 2), (19, 1), (49, 1), (51, 1), (61, 1), (65, 1)] }, { coefficient := 1, powers := [(0, 2), (19, 1), (52, 1), (61, 1), (65, 1)] }, { coefficient := 1, powers := [(0, 2), (40, 1), (51, 1), (65, 1)] }, { coefficient := -1, powers := [(0, 2), (40, 1), (61, 1), (65, 1)] }, { coefficient := -1, powers := [(0, 1), (2, 1), (40, 1), (62, 1), (65, 1)] }, { coefficient := -1, powers := [(0, 1), (3, 1), (16, 1), (19, 1), (31, 1), (61, 1), (62, 1), (65, 1)] }, { coefficient := -1, powers := [(0, 1), (3, 1), (16, 1), (31, 1), (46, 1), (62, 1), (65, 1)] }, { coefficient := -2, powers := [(0, 1), (4, 1), (16, 1), (27, 1), (30, 1), (40, 1), (62, 1), (65, 1)] }, { coefficient := -1, powers := [(0, 1), (5, 1), (31, 1), (62, 1), (65, 1)] }, { coefficient := 2, powers := [(0, 1), (7, 1), (16, 1), (27, 1), (33, 1), (40, 1), (62, 1), (65, 1)] }, { coefficient := -2, powers := [(0, 1), (10, 1), (16, 1), (20, 1), (27, 1), (40, 1), (62, 1), (65, 1)] }, { coefficient := -2, powers := [(0, 1), (10, 1), (16, 1), (23, 1), (27, 1), (33, 1), (36, 1), (40, 1), (62, 1), (65, 1)] }, { coefficient := 2, powers := [(0, 1), (10, 1), (16, 1), (25, 1), (27, 1), (40, 1), (62, 1), (65, 1)] }, { coefficient := -1, powers := [(0, 1), (12, 1), (18, 1), (19, 1), (27, 1), (61, 1), (62, 1), (65, 1)] }, { coefficient := 1, powers := [(0, 1), (12, 1), (19, 1), (21, 1), (61, 1), (62, 1), (65, 1)] }, { coefficient := -1, powers := [(0, 1), (12, 1), (19, 1), (23, 1), (26, 1), (51, 1), (61, 1), (62, 1), (65, 1)] }, { coefficient := -1, powers := [(0, 1), (12, 1), (19, 1), (23, 1), (27, 1), (61, 1), (62, 1), (65, 1)] }, { coefficient := 1, powers := [(0, 1), (12, 1), (21, 1), (46, 1), (62, 1), (65, 1)] }, { coefficient := 1, powers := [(0, 1), (12, 1), (22, 1), (23, 1), (51, 1), (62, 1), (65, 1)] }, { coefficient := -1, powers := [(0, 1), (12, 1), (22, 1), (62, 1), (65, 1)] }, { coefficient := 2, powers := [(0, 1), (14, 1), (16, 1), (20, 1), (27, 1), (40, 1), (62, 1), (65, 1)] }, { coefficient := 2, powers := [(0, 1), (14, 1), (16, 1), (23, 1), (27, 1), (33, 1), (36, 1), (40, 1), (62, 1), (65, 1)] }, { coefficient := -1, powers := [(0, 1), (16, 1), (19, 1), (21, 1), (49, 1), (61, 1), (62, 1), (65, 1)] }, { coefficient := -1, powers := [(0, 1), (16, 1), (21, 1), (46, 1), (49, 1), (62, 1), (65, 1)] }, { coefficient := -1, powers := [(0, 1), (16, 1), (22, 1), (23, 1), (52, 1), (62, 1), (65, 1)] }, { coefficient := -1, powers := [(0, 1), (16, 1), (22, 1), (49, 1), (62, 1), (65, 1)] }, { coefficient := 1, powers := [(0, 1), (19, 1), (49, 1), (51, 1), (65, 1)] }, { coefficient := -1, powers := [(0, 1), (19, 1), (52, 1), (65, 1)] }]
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

#print axioms Krenn.Component39.SelectedLeafB5_7_0.selectedHasNoCommonZero

end Krenn.Component39.SelectedLeafB5_7_0
