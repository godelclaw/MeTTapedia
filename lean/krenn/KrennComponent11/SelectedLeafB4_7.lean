import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component11.SelectedLeafB4_7

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "93ac95b67b43b529e7817a61629201c844a88f3124861ad35c1872cd354095d6"
def certificateSHA256 : String := "96cd3c0e7f636938bf62fd269b9e6f47375b56df334e11e4341d94000573e48d"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 38 → Fin 669 := ![
  4,
  6,
  16,
  20,
  24,
  25,
  27,
  30,
  160,
  179,
  182,
  184,
  186,
  236,
  286,
  322,
  323,
  329,
  332,
  341,
  342,
  343,
  348,
  350,
  451,
  453,
  462,
  496,
  557,
  589,
  601,
  614,
  662,
  663,
  665,
  666,
  667,
  668
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 38 → SparsePoly (Fin 65) := ![
  [{ coefficient := 1, powers := [(3, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (18, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(42, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (54, 1)] }, { coefficient := 1, powers := [(18, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (41, 1)] }, { coefficient := 1, powers := [(17, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (44, 1)] }, { coefficient := 1, powers := [(28, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1), (56, 1)] }, { coefficient := 1, powers := [(42, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1), (54, 1)] }, { coefficient := 1, powers := [(54, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (30, 1), (46, 1)] }, { coefficient := 1, powers := [(25, 1), (29, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (24, 1), (41, 1)] }, { coefficient := 1, powers := [(17, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1)] }, { coefficient := 1, powers := [(18, 1), (44, 1)] }, { coefficient := 1, powers := [(24, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (49, 1)] }, { coefficient := 1, powers := [(19, 1), (44, 1)] }, { coefficient := 1, powers := [(24, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1)] }, { coefficient := 1, powers := [(12, 1), (30, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (30, 1)] }, { coefficient := 1, powers := [(22, 1), (25, 1), (51, 1)] }, { coefficient := 1, powers := [(30, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (54, 1)] }, { coefficient := 1, powers := [(30, 1), (42, 1)] }, { coefficient := 1, powers := [(33, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (53, 1)] }, { coefficient := 1, powers := [(30, 1), (41, 1)] }, { coefficient := 1, powers := [(30, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (37, 1), (60, 1)] }, { coefficient := 1, powers := [(3, 1), (24, 1), (60, 1)] }, { coefficient := 1, powers := [(6, 1), (18, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (48, 1), (54, 1)] }, { coefficient := 1, powers := [(19, 1), (54, 1)] }, { coefficient := 1, powers := [(25, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (49, 1), (52, 1)] }, { coefficient := 1, powers := [(19, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(49, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (36, 1)] }, { coefficient := 1, powers := [(22, 1), (44, 1)] }, { coefficient := 1, powers := [(28, 1), (44, 1)] }, { coefficient := 1, powers := [(36, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (60, 1)] }, { coefficient := 1, powers := [(12, 1), (25, 1), (47, 1)] }, { coefficient := 1, powers := [(12, 1), (57, 1)] }, { coefficient := 1, powers := [(17, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1), (53, 1)] }, { coefficient := 1, powers := [(18, 1), (44, 1), (53, 1)] }, { coefficient := 1, powers := [(18, 1), (57, 1)] }, { coefficient := 1, powers := [(25, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (30, 1), (60, 1)] }, { coefficient := 1, powers := [(3, 1), (33, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (36, 1), (54, 1)] }, { coefficient := 1, powers := [(22, 1), (44, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (44, 1), (53, 1)] }, { coefficient := 1, powers := [(23, 1), (57, 1)] }, { coefficient := 1, powers := [(30, 1), (49, 1)] }, { coefficient := 1, powers := [(36, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (52, 1)] }, { coefficient := 1, powers := [(3, 1), (59, 1)] }, { coefficient := 1, powers := [(18, 1), (52, 1)] }, { coefficient := 1, powers := [(18, 1), (56, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (41, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (47, 1), (53, 1)] }, { coefficient := 1, powers := [(8, 1), (36, 1), (41, 1)] }, { coefficient := 1, powers := [(17, 1), (29, 1), (53, 1)] }, { coefficient := 1, powers := [(17, 1), (30, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (37, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1)] }, { coefficient := 1, powers := [(3, 1), (24, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (18, 1), (59, 1)] }, { coefficient := 1, powers := [(18, 1)] }, { coefficient := 1, powers := [(24, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (39, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (42, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (49, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (23, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (49, 1)] }, { coefficient := 1, powers := [(8, 1), (36, 1), (42, 1)] }, { coefficient := 1, powers := [(12, 1), (23, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1), (30, 1), (49, 1)] }, { coefficient := 1, powers := [(12, 1), (36, 1), (39, 1)] }, { coefficient := 1, powers := [(17, 1), (23, 1), (54, 1)] }, { coefficient := 1, powers := [(17, 1), (30, 1), (42, 1)] }, { coefficient := 1, powers := [(17, 1), (33, 1), (39, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (61, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(40, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(41, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(42, 1), (64, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 38 → SparsePoly (Fin 65) := ![
  [{ coefficient := 1, powers := [(0, 1), (5, 1), (12, 1), (23, 1), (30, 1), (57, 1), (59, 1), (61, 1)] }, { coefficient := -1, powers := [(0, 1), (5, 1), (30, 1), (59, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (12, 1), (18, 1), (23, 1), (30, 1), (57, 1), (59, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (12, 1), (23, 1), (24, 1), (30, 1), (52, 1), (57, 1), (59, 1)] }, { coefficient := -1, powers := [(5, 1), (12, 1), (23, 1), (24, 1), (30, 1), (57, 1), (59, 1), (61, 1)] }, { coefficient := -1, powers := [(5, 1), (18, 1), (30, 1), (59, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (12, 1), (23, 1), (33, 1), (37, 1), (52, 1), (57, 2)] }, { coefficient := 1, powers := [(0, 1), (12, 1), (23, 1), (33, 1), (37, 1), (57, 2), (61, 1)] }, { coefficient := 1, powers := [(0, 1), (33, 1), (37, 1), (52, 1), (57, 1)] }, { coefficient := -1, powers := [(0, 1), (33, 1), (37, 1), (57, 1), (61, 1)] }, { coefficient := 1, powers := [(3, 1), (12, 1), (23, 1), (33, 1), (57, 2)] }, { coefficient := -1, powers := [(3, 1), (33, 1), (57, 1)] }, { coefficient := -1, powers := [(6, 1), (12, 1), (18, 1), (23, 1), (33, 1), (52, 1), (57, 2)] }, { coefficient := 1, powers := [(6, 1), (12, 1), (18, 1), (23, 1), (33, 1), (57, 2), (61, 1)] }, { coefficient := 1, powers := [(6, 1), (18, 1), (33, 1), (52, 1), (57, 1)] }, { coefficient := -1, powers := [(6, 1), (18, 1), (33, 1), (57, 1), (61, 1)] }],
  [{ coefficient := 2, powers := [(12, 1), (23, 2), (25, 1), (57, 1)] }, { coefficient := 2, powers := [(12, 1), (23, 1), (25, 1), (36, 1), (39, 1)] }, { coefficient := -2, powers := [(23, 1), (25, 1)] }],
  [{ coefficient := 2, powers := [(12, 1), (23, 2), (46, 1), (54, 1), (57, 1)] }, { coefficient := 2, powers := [(12, 1), (23, 1), (36, 1), (39, 1), (46, 1), (54, 1)] }, { coefficient := -2, powers := [(23, 1), (46, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (12, 1), (23, 1), (44, 1), (57, 1), (59, 1)] }, { coefficient := -2, powers := [(5, 1), (18, 1), (48, 1), (51, 1), (60, 1), (62, 1), (64, 1)] }, { coefficient := 2, powers := [(5, 1), (19, 1), (51, 1), (60, 1), (62, 1), (64, 1)] }, { coefficient := 1, powers := [(5, 1), (44, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (5, 1), (12, 1), (23, 1), (30, 1), (52, 1), (57, 1), (59, 1), (60, 1), (64, 1)] }, { coefficient := 1, powers := [(3, 1), (5, 1), (12, 1), (23, 1), (30, 1), (57, 1), (59, 1), (60, 1), (61, 1), (64, 1)] }, { coefficient := -1, powers := [(3, 1), (5, 1), (12, 1), (23, 1), (33, 1), (52, 1), (57, 2), (59, 1), (64, 1)] }, { coefficient := 1, powers := [(3, 1), (5, 1), (12, 1), (23, 1), (33, 1), (57, 2), (59, 1), (61, 1), (64, 1)] }, { coefficient := 1, powers := [(3, 1), (5, 1), (33, 1), (52, 1), (57, 1), (59, 1), (64, 1)] }, { coefficient := -1, powers := [(3, 1), (5, 1), (33, 1), (57, 1), (59, 1), (61, 1), (64, 1)] }, { coefficient := -1, powers := [(5, 1), (12, 1), (23, 1), (30, 1), (52, 1), (57, 1), (60, 1), (64, 1)] }, { coefficient := 1, powers := [(5, 1), (12, 1), (23, 1), (30, 1), (57, 1), (60, 1), (61, 1), (64, 1)] }, { coefficient := -1, powers := [(5, 1), (12, 1), (23, 1), (33, 1), (52, 1), (57, 2), (64, 1)] }, { coefficient := 1, powers := [(5, 1), (12, 1), (23, 1), (33, 1), (57, 2), (61, 1), (64, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (52, 1), (57, 1), (64, 1)] }, { coefficient := -1, powers := [(5, 1), (33, 1), (57, 1), (61, 1), (64, 1)] }, { coefficient := -2, powers := [(12, 1), (17, 1), (23, 1), (30, 1), (39, 1), (52, 1), (60, 1), (64, 1)] }, { coefficient := 2, powers := [(12, 1), (17, 1), (23, 1), (30, 1), (42, 1), (52, 1), (57, 1), (64, 1)] }, { coefficient := 2, powers := [(12, 1), (28, 1), (49, 1), (52, 1), (53, 1), (64, 1)] }, { coefficient := -2, powers := [(12, 1), (30, 1), (49, 1), (52, 1), (64, 1)] }, { coefficient := -2, powers := [(17, 1), (30, 1), (42, 1), (52, 1), (64, 1)] }],
  [{ coefficient := 2, powers := [(5, 1), (9, 1), (53, 1), (60, 1), (62, 1), (63, 1), (64, 1)] }, { coefficient := -2, powers := [(5, 1), (25, 1), (51, 1), (60, 1), (62, 1), (63, 1), (64, 1)] }, { coefficient := -2, powers := [(12, 1), (17, 1), (23, 1), (39, 1), (53, 1), (60, 1), (63, 1), (64, 1)] }, { coefficient := 2, powers := [(12, 1), (17, 1), (23, 1), (42, 1), (53, 1), (57, 1), (63, 1), (64, 1)] }, { coefficient := -2, powers := [(17, 1), (42, 1), (53, 1), (63, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (5, 1), (12, 1), (23, 1), (28, 1), (54, 1), (57, 1), (59, 1), (61, 1), (64, 1)] }, { coefficient := 1, powers := [(0, 1), (5, 1), (28, 1), (54, 1), (59, 1), (61, 1), (64, 1)] }, { coefficient := 1, powers := [(3, 1), (5, 1), (12, 1), (23, 1), (24, 1), (33, 1), (53, 1), (57, 1), (59, 1), (61, 1), (64, 1)] }, { coefficient := -1, powers := [(3, 1), (5, 1), (12, 1), (23, 1), (25, 1), (33, 1), (57, 1), (59, 1), (61, 1), (64, 1)] }, { coefficient := -1, powers := [(3, 1), (5, 1), (24, 1), (33, 1), (53, 1), (59, 1), (61, 1), (64, 1)] }, { coefficient := 1, powers := [(3, 1), (5, 1), (25, 1), (33, 1), (59, 1), (61, 1), (64, 1)] }, { coefficient := -1, powers := [(5, 1), (12, 1), (18, 1), (23, 1), (28, 1), (54, 1), (57, 1), (59, 1), (61, 1), (64, 1)] }, { coefficient := 1, powers := [(5, 1), (18, 1), (28, 1), (54, 1), (59, 1), (61, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (12, 1), (23, 1), (36, 1), (37, 1), (57, 1), (59, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (12, 1), (23, 1), (36, 1), (42, 1), (52, 1), (57, 1), (64, 1)] }, { coefficient := 1, powers := [(5, 1), (12, 1), (23, 1), (36, 1), (42, 1), (56, 1), (57, 1), (64, 1)] }, { coefficient := 2, powers := [(5, 1), (22, 1), (48, 1), (51, 1), (60, 1), (62, 1), (64, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1), (37, 1), (59, 1), (61, 1)] }, { coefficient := -1, powers := [(5, 1), (36, 1), (42, 1), (52, 1), (64, 1)] }, { coefficient := -1, powers := [(5, 1), (36, 1), (42, 1), (56, 1), (64, 1)] }, { coefficient := -2, powers := [(12, 1), (17, 1), (23, 2), (46, 1), (57, 1)] }, { coefficient := -2, powers := [(12, 1), (17, 1), (23, 1), (36, 1), (39, 1), (46, 1)] }, { coefficient := 2, powers := [(17, 1), (23, 1), (46, 1)] }],
  [{ coefficient := 2, powers := [(12, 1), (23, 1), (24, 1), (30, 1), (39, 1), (60, 1)] }, { coefficient := -2, powers := [(12, 1), (23, 1), (24, 1), (30, 1), (42, 1), (57, 1)] }, { coefficient := 2, powers := [(24, 1), (30, 1), (42, 1)] }],
  [{ coefficient := -2, powers := [(12, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (12, 1), (18, 1), (23, 1), (30, 1), (57, 1), (60, 1), (61, 1), (64, 1)] }, { coefficient := 1, powers := [(5, 1), (12, 1), (18, 1), (23, 1), (33, 1), (57, 2), (61, 1), (64, 1)] }, { coefficient := -1, powers := [(5, 1), (12, 1), (23, 1), (36, 1), (54, 1), (57, 1), (64, 1)] }, { coefficient := -1, powers := [(5, 1), (18, 1), (33, 1), (57, 1), (61, 1), (64, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1), (54, 1), (64, 1)] }],
  [{ coefficient := 2, powers := [(12, 1), (17, 1), (23, 2), (57, 1)] }, { coefficient := 2, powers := [(12, 1), (17, 1), (23, 1), (36, 1), (39, 1)] }, { coefficient := -2, powers := [(17, 1), (23, 1)] }],
  [{ coefficient := 2, powers := [(5, 1), (60, 1), (62, 1), (63, 1)] }],
  [{ coefficient := -2, powers := [(12, 1), (23, 1), (30, 1), (39, 1), (60, 1)] }, { coefficient := 2, powers := [(12, 1), (23, 1), (30, 1), (42, 1), (57, 1)] }, { coefficient := -2, powers := [(30, 1), (42, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (5, 1), (12, 1), (23, 1), (33, 1), (53, 1), (57, 1), (59, 1), (61, 1)] }, { coefficient := 1, powers := [(3, 1), (5, 1), (33, 1), (53, 1), (59, 1), (61, 1)] }],
  [{ coefficient := -2, powers := [(12, 1), (28, 1), (52, 1), (53, 1)] }, { coefficient := 2, powers := [(12, 1), (30, 1), (52, 1)] }],
  [{ coefficient := -2, powers := [(12, 1), (23, 1), (49, 1), (57, 1)] }, { coefficient := 2, powers := [(49, 1)] }],
  [{ coefficient := 2, powers := [(5, 1), (60, 1), (62, 1)] }],
  [{ coefficient := -2, powers := [(12, 1), (17, 1), (23, 1), (57, 1)] }, { coefficient := 2, powers := [(17, 1)] }],
  [{ coefficient := -2, powers := [(5, 1), (9, 1), (60, 1), (62, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (12, 1), (23, 1), (30, 1), (52, 1), (57, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (12, 1), (23, 1), (30, 1), (57, 1), (59, 1), (61, 1)] }],
  [{ coefficient := -2, powers := [(5, 1), (22, 1), (51, 1), (60, 1), (62, 1), (64, 1)] }],
  [{ coefficient := 2, powers := [(12, 1), (28, 1), (53, 1)] }, { coefficient := -2, powers := [(12, 1), (30, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (5, 1), (12, 1), (23, 1), (54, 1), (57, 1), (59, 1), (61, 1)] }, { coefficient := -1, powers := [(0, 1), (5, 1), (54, 1), (59, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (12, 1), (18, 1), (23, 1), (54, 1), (57, 1), (59, 1), (61, 1)] }, { coefficient := -1, powers := [(5, 1), (18, 1), (54, 1), (59, 1), (61, 1)] }],
  [{ coefficient := -2, powers := [(12, 1), (23, 2), (57, 1)] }, { coefficient := -2, powers := [(12, 1), (23, 1), (36, 1), (39, 1)] }, { coefficient := 2, powers := [(23, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (5, 1), (12, 1), (23, 1), (33, 1), (57, 1), (59, 1), (61, 1)] }, { coefficient := -1, powers := [(3, 1), (5, 1), (33, 1), (59, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (5, 1), (12, 1), (23, 1), (57, 1), (59, 1), (61, 1)] }, { coefficient := 1, powers := [(0, 1), (5, 1), (59, 1), (61, 1)] }, { coefficient := -1, powers := [(5, 1), (12, 1), (18, 1), (23, 1), (57, 1), (59, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (12, 1), (23, 1), (57, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (18, 1), (59, 1), (61, 1)] }, { coefficient := -1, powers := [(5, 1), (59, 1)] }],
  [{ coefficient := 2, powers := [(12, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (12, 1), (23, 1), (30, 1), (57, 1), (60, 1)] }, { coefficient := -1, powers := [(5, 1), (12, 1), (23, 1), (33, 1), (57, 2)] }, { coefficient := -1, powers := [(5, 1), (12, 1), (23, 1), (36, 1), (42, 1), (54, 1), (57, 1), (64, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1), (42, 1), (54, 1), (64, 1)] }],
  [{ coefficient := 2, powers := [(12, 1), (23, 1), (39, 1), (60, 1), (63, 1)] }, { coefficient := -2, powers := [(12, 1), (23, 1), (42, 1), (57, 1), (63, 1)] }, { coefficient := 2, powers := [(42, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (12, 1), (23, 1), (30, 1), (52, 1), (57, 1), (60, 1)] }, { coefficient := -1, powers := [(5, 1), (12, 1), (23, 1), (30, 1), (57, 1), (60, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (12, 1), (23, 1), (33, 1), (52, 1), (57, 2)] }, { coefficient := -1, powers := [(5, 1), (12, 1), (23, 1), (33, 1), (57, 2), (61, 1)] }, { coefficient := -1, powers := [(5, 1), (33, 1), (52, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (57, 1), (61, 1)] }],
  [{ coefficient := 2, powers := [(12, 1), (23, 1), (57, 1)] }, { coefficient := -2, powers := [] }],
  [{ coefficient := 1, powers := [(3, 1), (5, 1), (12, 1), (23, 1), (33, 1), (57, 2), (59, 1)] }, { coefficient := -1, powers := [(3, 1), (5, 1), (33, 1), (57, 1), (59, 1)] }, { coefficient := -1, powers := [(5, 1), (12, 1), (18, 1), (23, 1), (30, 1), (42, 1), (56, 1), (57, 1), (60, 1), (64, 1)] }, { coefficient := -1, powers := [(5, 1), (12, 1), (18, 1), (23, 1), (33, 1), (42, 1), (56, 1), (57, 2), (64, 1)] }, { coefficient := 1, powers := [(5, 1), (12, 1), (23, 1), (30, 1), (57, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (12, 1), (23, 1), (33, 1), (57, 2)] }, { coefficient := 1, powers := [(5, 1), (18, 1), (33, 1), (42, 1), (56, 1), (57, 1), (64, 1)] }, { coefficient := -1, powers := [(5, 1), (33, 1), (57, 1)] }],
  [{ coefficient := -2, powers := [(12, 1), (23, 1), (39, 1), (41, 1), (57, 1), (60, 1), (63, 1)] }, { coefficient := -2, powers := [(12, 1), (23, 1), (39, 1), (47, 1), (53, 1), (60, 1), (63, 1)] }, { coefficient := -2, powers := [(12, 1), (23, 1), (39, 1), (57, 1), (60, 1)] }, { coefficient := 2, powers := [(12, 1), (23, 1), (41, 1), (42, 1), (57, 2), (63, 1)] }, { coefficient := 2, powers := [(12, 1), (23, 1), (42, 1), (47, 1), (53, 1), (57, 1), (63, 1)] }, { coefficient := -2, powers := [(12, 1), (23, 1), (42, 1), (57, 2)] }, { coefficient := 2, powers := [(39, 1), (60, 1)] }, { coefficient := -2, powers := [(41, 1), (42, 1), (57, 1), (63, 1)] }, { coefficient := -2, powers := [(42, 1), (47, 1), (53, 1), (63, 1)] }, { coefficient := 2, powers := [(42, 1), (57, 1)] }],
  [{ coefficient := -2, powers := [(5, 1), (30, 1), (60, 1)] }],
  [{ coefficient := 2, powers := [(5, 1), (9, 1), (30, 1), (60, 1), (62, 1)] }, { coefficient := -2, powers := [(8, 1), (12, 1), (23, 1), (36, 1), (39, 1), (60, 1)] }, { coefficient := 2, powers := [(8, 1), (12, 1), (23, 1), (36, 1), (42, 1), (57, 1)] }, { coefficient := -2, powers := [(8, 1), (36, 1), (42, 1)] }, { coefficient := -2, powers := [(12, 1), (17, 1), (23, 1), (30, 1), (39, 1), (60, 1)] }, { coefficient := 2, powers := [(12, 1), (17, 1), (23, 1), (30, 1), (42, 1), (57, 1)] }, { coefficient := -2, powers := [(17, 1), (30, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (5, 1), (12, 1), (23, 1), (28, 1), (44, 1), (54, 1), (57, 1), (59, 1), (61, 1)] }, { coefficient := -1, powers := [(0, 1), (5, 1), (28, 1), (44, 1), (54, 1), (59, 1), (61, 1)] }, { coefficient := 1, powers := [(3, 1), (5, 1), (12, 1), (23, 1), (24, 1), (30, 1), (52, 1), (57, 1), (59, 1), (60, 1)] }, { coefficient := -1, powers := [(3, 1), (5, 1), (12, 1), (23, 1), (24, 1), (30, 1), (57, 1), (59, 1), (60, 1), (61, 1)] }, { coefficient := -1, powers := [(3, 1), (5, 1), (12, 1), (23, 1), (24, 1), (33, 1), (44, 1), (53, 1), (57, 1), (59, 1), (61, 1)] }, { coefficient := 1, powers := [(3, 1), (5, 1), (12, 1), (23, 1), (24, 1), (33, 1), (52, 1), (57, 2), (59, 1)] }, { coefficient := -1, powers := [(3, 1), (5, 1), (12, 1), (23, 1), (24, 1), (33, 1), (57, 2), (59, 1), (61, 1)] }, { coefficient := 1, powers := [(3, 1), (5, 1), (12, 1), (23, 1), (25, 1), (33, 1), (44, 1), (57, 1), (59, 1), (61, 1)] }, { coefficient := 1, powers := [(3, 1), (5, 1), (12, 1), (23, 1), (36, 1), (54, 1), (57, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (5, 1), (24, 1), (33, 1), (44, 1), (53, 1), (59, 1), (61, 1)] }, { coefficient := -1, powers := [(3, 1), (5, 1), (24, 1), (33, 1), (52, 1), (57, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (5, 1), (24, 1), (33, 1), (57, 1), (59, 1), (61, 1)] }, { coefficient := -1, powers := [(3, 1), (5, 1), (25, 1), (33, 1), (44, 1), (59, 1), (61, 1)] }, { coefficient := -1, powers := [(3, 1), (5, 1), (36, 1), (54, 1), (59, 1)] }, { coefficient := -2, powers := [(5, 1), (9, 1), (29, 1), (53, 1), (60, 1), (62, 1), (63, 1)] }, { coefficient := 1, powers := [(5, 1), (12, 1), (18, 1), (23, 1), (28, 1), (44, 1), (54, 1), (57, 1), (59, 1), (61, 1)] }, { coefficient := -1, powers := [(5, 1), (12, 1), (18, 1), (23, 1), (30, 1), (56, 1), (57, 1), (60, 1)] }, { coefficient := -1, powers := [(5, 1), (12, 1), (18, 1), (23, 1), (30, 1), (57, 1), (60, 1), (61, 1)] }, { coefficient := -1, powers := [(5, 1), (12, 1), (18, 1), (23, 1), (33, 1), (56, 1), (57, 2)] }, { coefficient := -1, powers := [(5, 1), (12, 1), (18, 1), (23, 1), (33, 1), (57, 2), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (12, 1), (23, 1), (24, 1), (30, 1), (52, 1), (57, 1), (60, 1)] }, { coefficient := -1, powers := [(5, 1), (12, 1), (23, 1), (24, 1), (30, 1), (57, 1), (60, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (12, 1), (23, 1), (24, 1), (33, 1), (52, 1), (57, 2)] }, { coefficient := -1, powers := [(5, 1), (12, 1), (23, 1), (24, 1), (33, 1), (57, 2), (61, 1)] }, { coefficient := 2, powers := [(5, 1), (12, 1), (23, 1), (36, 1), (54, 1), (57, 1)] }, { coefficient := -1, powers := [(5, 1), (18, 1), (28, 1), (44, 1), (54, 1), (59, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (18, 1), (33, 1), (56, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (18, 1), (33, 1), (57, 1), (61, 1)] }, { coefficient := 2, powers := [(5, 1), (22, 1), (25, 1), (51, 1), (60, 1), (62, 1)] }, { coefficient := -1, powers := [(5, 1), (24, 1), (33, 1), (52, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (24, 1), (33, 1), (57, 1), (61, 1)] }, { coefficient := 2, powers := [(5, 1), (25, 1), (29, 1), (51, 1), (60, 1), (62, 1), (63, 1)] }, { coefficient := -2, powers := [(5, 1), (36, 1), (54, 1)] }, { coefficient := 2, powers := [(12, 1), (17, 1), (23, 1), (24, 1), (30, 1), (39, 1), (52, 1), (60, 1)] }, { coefficient := -2, powers := [(12, 1), (17, 1), (23, 1), (24, 1), (30, 1), (42, 1), (52, 1), (57, 1)] }, { coefficient := 2, powers := [(12, 1), (17, 1), (23, 1), (29, 1), (39, 1), (53, 1), (60, 1), (63, 1)] }, { coefficient := -2, powers := [(12, 1), (17, 1), (23, 1), (29, 1), (42, 1), (53, 1), (57, 1), (63, 1)] }, { coefficient := -2, powers := [(12, 1), (24, 1), (28, 1), (49, 1), (52, 1), (53, 1)] }, { coefficient := 2, powers := [(12, 1), (24, 1), (30, 1), (49, 1), (52, 1)] }, { coefficient := 2, powers := [(17, 1), (24, 1), (30, 1), (42, 1), (52, 1)] }, { coefficient := 2, powers := [(17, 1), (29, 1), (42, 1), (53, 1), (63, 1)] }]
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
    (values : Fin 65 → R) :
    ¬ ∀ index : Fin 38,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((2 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (2 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (2 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component11.SelectedLeafB4_7.selectedHasNoCommonZero

end Krenn.Component11.SelectedLeafB4_7
