import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component47.SelectedLeafB4_2_1

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "83c39c67544a90b479367bac1349a2adbf872b4571d901bd2be51260f853cb85"
def certificateSHA256 : String := "f9c5cdceda5542537de7de32f39369d11c8975fa4316b00b54c5f95b94fcefe1"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 32 → Fin 596 := ![
  2,
  3,
  7,
  28,
  34,
  70,
  210,
  220,
  221,
  247,
  272,
  286,
  287,
  364,
  370,
  376,
  377,
  411,
  423,
  482,
  544,
  545,
  584,
  586,
  587,
  589,
  590,
  591,
  592,
  593,
  594,
  595
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 32 → SparsePoly (Fin 61) := ![
  [{ coefficient := 1, powers := [(3, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (29, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (32, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (51, 1)] }, { coefficient := 1, powers := [(20, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (33, 1)] }, { coefficient := 1, powers := [(18, 1), (21, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (32, 1)] }, { coefficient := 1, powers := [(32, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (40, 1)] }, { coefficient := 1, powers := [(29, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (29, 1), (56, 1)] }, { coefficient := 1, powers := [(29, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (33, 1), (48, 1)] }, { coefficient := 1, powers := [(5, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (24, 1), (56, 1)] }, { coefficient := 1, powers := [(24, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (51, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1)] }, { coefficient := 1, powers := [(14, 1), (29, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (43, 1)] }, { coefficient := 1, powers := [(14, 1), (53, 1)] }, { coefficient := 1, powers := [(18, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (51, 1)] }, { coefficient := 1, powers := [(29, 1), (41, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (54, 1)] }, { coefficient := 1, powers := [(29, 1), (46, 1)] }, { coefficient := 1, powers := [(35, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (32, 1), (52, 1)] }, { coefficient := 1, powers := [(6, 1), (32, 1), (42, 1)] }, { coefficient := 1, powers := [(15, 1), (32, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (24, 1), (57, 1)] }, { coefficient := 1, powers := [(6, 1), (32, 1), (46, 1)] }, { coefficient := 1, powers := [(6, 1), (35, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1), (47, 1)] }, { coefficient := 1, powers := [(6, 1), (30, 1), (43, 1)] }, { coefficient := 1, powers := [(9, 1), (25, 1), (43, 1)] }, { coefficient := 1, powers := [(47, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1)] }, { coefficient := 1, powers := [(3, 1), (33, 1)] }, { coefficient := 1, powers := [(15, 1), (20, 1)] }, { coefficient := 1, powers := [(20, 1), (52, 1)] }, { coefficient := 1, powers := [(25, 1), (42, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1)] }, { coefficient := 1, powers := [(6, 1), (30, 1)] }, { coefficient := 1, powers := [(9, 1), (25, 1)] }, { coefficient := 1, powers := [(20, 1), (47, 1)] }, { coefficient := 1, powers := [(25, 1), (39, 1)] }, { coefficient := 1, powers := [(30, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (36, 1), (55, 1)] }, { coefficient := 1, powers := [(0, 1), (39, 1), (52, 1)] }, { coefficient := 1, powers := [(0, 1), (42, 1), (47, 1)] }, { coefficient := 1, powers := [(3, 1), (25, 1), (55, 1)] }, { coefficient := 1, powers := [(3, 1), (30, 1), (52, 1)] }, { coefficient := 1, powers := [(3, 1), (33, 1), (47, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1), (55, 1)] }, { coefficient := 1, powers := [(6, 1), (30, 1), (42, 1)] }, { coefficient := 1, powers := [(6, 1), (33, 1), (39, 1)] }, { coefficient := 1, powers := [(9, 1), (20, 1), (52, 1)] }, { coefficient := 1, powers := [(9, 1), (25, 1), (42, 1)] }, { coefficient := 1, powers := [(9, 1), (33, 1), (36, 1)] }, { coefficient := 1, powers := [(15, 1), (20, 1), (47, 1)] }, { coefficient := 1, powers := [(15, 1), (25, 1), (39, 1)] }, { coefficient := 1, powers := [(15, 1), (30, 1), (36, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (41, 1), (54, 1)] }, { coefficient := 1, powers := [(2, 1), (46, 1), (51, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (51, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (57, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (46, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(14, 1), (24, 1), (54, 1)] }, { coefficient := 1, powers := [(14, 1), (29, 1), (46, 1)] }, { coefficient := 1, powers := [(14, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (51, 1)] }, { coefficient := 1, powers := [(19, 1), (29, 1), (41, 1)] }, { coefficient := 1, powers := [(19, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (58, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(39, 1)] }],
  [{ coefficient := 1, powers := [(40, 1), (59, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(41, 1)] }],
  [{ coefficient := 1, powers := [(52, 1)] }],
  [{ coefficient := 1, powers := [(53, 1)] }],
  [{ coefficient := 1, powers := [(54, 1), (60, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 32 → SparsePoly (Fin 61) := ![
  [{ coefficient := -1, powers := [(0, 1), (5, 1), (29, 1), (36, 1), (55, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (5, 1), (29, 1), (42, 1), (47, 1), (56, 1)] }, { coefficient := -1, powers := [(3, 1), (5, 1), (25, 1), (29, 1), (55, 1), (56, 1)] }, { coefficient := -1, powers := [(5, 1), (15, 1), (29, 1), (30, 1), (36, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (25, 1), (29, 1), (42, 1), (47, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (30, 1), (36, 1), (42, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (33, 1), (36, 1), (47, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (8, 1), (24, 1), (36, 1), (55, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (8, 1), (24, 1), (42, 1), (47, 1), (56, 1)] }, { coefficient := -1, powers := [(3, 1), (8, 1), (24, 1), (25, 1), (55, 1), (56, 1)] }, { coefficient := -1, powers := [(8, 1), (15, 1), (24, 1), (30, 1), (36, 1), (56, 1)] }, { coefficient := 1, powers := [(8, 1), (15, 1), (24, 1), (30, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (25, 1), (42, 1), (47, 1), (56, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (30, 1), (36, 1), (42, 1), (56, 1)] }, { coefficient := -1, powers := [(8, 1), (24, 1), (30, 1), (42, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (33, 1), (36, 1), (47, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(33, 1), (36, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (36, 1), (46, 1), (50, 1), (55, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (42, 1), (46, 1), (47, 1), (50, 1), (59, 1)] }, { coefficient := -1, powers := [(3, 1), (25, 1), (46, 1), (50, 1), (55, 1), (59, 1)] }, { coefficient := 1, powers := [(25, 1), (42, 1), (46, 1), (47, 1), (50, 1), (59, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1), (46, 1), (47, 1), (50, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (5, 1), (32, 1), (42, 1), (43, 1), (47, 1), (54, 1), (60, 1)] }, { coefficient := -1, powers := [(0, 1), (5, 1), (35, 1), (36, 1), (51, 1), (55, 1), (58, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (5, 1), (35, 1), (42, 1), (47, 1), (51, 1), (58, 1), (60, 1)] }, { coefficient := -1, powers := [(3, 1), (5, 1), (25, 1), (35, 1), (51, 1), (55, 1), (58, 1), (60, 1)] }, { coefficient := -1, powers := [(5, 1), (15, 1), (30, 1), (35, 1), (36, 1), (51, 1), (58, 1), (60, 1)] }, { coefficient := -1, powers := [(5, 1), (25, 1), (32, 1), (42, 1), (43, 1), (47, 1), (54, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (25, 1), (35, 1), (42, 1), (47, 1), (51, 1), (58, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (35, 1), (36, 1), (42, 1), (51, 1), (58, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (35, 1), (36, 1), (47, 1), (51, 1), (58, 1), (60, 1)] }, { coefficient := 1, powers := [(6, 1), (55, 1), (60, 1)] }, { coefficient := -1, powers := [(42, 1), (47, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (5, 1), (30, 1), (42, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (25, 1), (30, 1), (42, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (5, 1), (35, 1), (36, 1), (55, 1), (58, 1)] }, { coefficient := -1, powers := [(0, 1), (5, 1), (35, 1), (42, 1), (47, 1), (58, 1)] }, { coefficient := 1, powers := [(3, 1), (5, 1), (25, 1), (35, 1), (55, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (15, 1), (30, 1), (35, 1), (36, 1), (58, 1)] }, { coefficient := -1, powers := [(5, 1), (25, 1), (35, 1), (42, 1), (47, 1), (58, 1)] }, { coefficient := -1, powers := [(5, 1), (30, 1), (35, 1), (36, 1), (42, 1), (58, 1)] }, { coefficient := -1, powers := [(5, 1), (33, 1), (35, 1), (36, 1), (47, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (32, 1), (36, 1), (48, 1), (54, 1)] }, { coefficient := -1, powers := [(3, 1), (25, 1), (32, 1), (48, 1), (54, 1)] }, { coefficient := -1, powers := [(32, 1), (36, 1), (47, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (5, 1), (30, 1), (42, 1), (43, 1), (54, 1)] }, { coefficient := -1, powers := [(5, 1), (25, 1), (30, 1), (42, 1), (43, 1), (54, 1)] }, { coefficient := -1, powers := [(5, 1), (30, 1), (42, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (15, 1), (30, 1), (46, 1)] }, { coefficient := -1, powers := [(8, 1), (30, 1), (42, 1), (46, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (14, 1), (36, 1), (46, 1), (55, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (14, 1), (42, 1), (46, 1), (47, 1), (59, 1)] }, { coefficient := -1, powers := [(3, 1), (14, 1), (25, 1), (46, 1), (55, 1), (59, 1)] }, { coefficient := 1, powers := [(14, 1), (25, 1), (42, 1), (46, 1), (47, 1), (59, 1)] }, { coefficient := 1, powers := [(14, 1), (33, 1), (36, 1), (46, 1), (47, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (5, 1), (36, 1), (55, 1), (57, 1)] }, { coefficient := -1, powers := [(0, 1), (5, 1), (42, 1), (47, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (5, 1), (25, 1), (55, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (15, 1), (30, 1), (36, 1), (57, 1)] }, { coefficient := -1, powers := [(5, 1), (25, 1), (42, 1), (47, 1), (57, 1)] }, { coefficient := -1, powers := [(5, 1), (30, 1), (36, 1), (42, 1), (57, 1)] }, { coefficient := -1, powers := [(5, 1), (33, 1), (36, 1), (47, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (32, 1), (36, 1), (54, 1)] }, { coefficient := 1, powers := [(3, 1), (25, 1), (32, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (8, 1), (36, 1), (55, 1), (57, 1)] }, { coefficient := -1, powers := [(0, 1), (8, 1), (42, 1), (47, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (8, 1), (25, 1), (55, 1), (57, 1)] }, { coefficient := 1, powers := [(8, 1), (15, 1), (30, 1), (36, 1), (57, 1)] }, { coefficient := -1, powers := [(8, 1), (25, 1), (42, 1), (47, 1), (57, 1)] }, { coefficient := -1, powers := [(8, 1), (30, 1), (36, 1), (42, 1), (57, 1)] }, { coefficient := -1, powers := [(8, 1), (33, 1), (36, 1), (47, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (36, 1), (40, 1), (46, 1), (55, 1), (59, 1)] }, { coefficient := -1, powers := [(0, 1), (40, 1), (42, 1), (46, 1), (47, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (25, 1), (40, 1), (46, 1), (55, 1), (59, 1)] }, { coefficient := -1, powers := [(25, 1), (40, 1), (42, 1), (46, 1), (47, 1), (59, 1)] }, { coefficient := -1, powers := [(33, 1), (36, 1), (40, 1), (46, 1), (47, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (29, 1), (36, 1), (46, 1), (55, 1), (59, 1)] }, { coefficient := -1, powers := [(0, 1), (29, 1), (42, 1), (46, 1), (47, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (25, 1), (29, 1), (46, 1), (55, 1), (59, 1)] }, { coefficient := -1, powers := [(25, 1), (29, 1), (42, 1), (46, 1), (47, 1), (59, 1)] }, { coefficient := -1, powers := [(29, 1), (33, 1), (36, 1), (46, 1), (47, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (19, 1), (36, 1), (55, 1)] }, { coefficient := -1, powers := [(0, 1), (19, 1), (42, 1), (47, 1)] }, { coefficient := 1, powers := [(3, 1), (19, 1), (25, 1), (55, 1)] }, { coefficient := 1, powers := [(15, 1), (19, 1), (30, 1), (36, 1)] }, { coefficient := -1, powers := [(19, 1), (25, 1), (42, 1), (47, 1)] }, { coefficient := -1, powers := [(19, 1), (30, 1), (36, 1), (42, 1)] }, { coefficient := -1, powers := [(19, 1), (33, 1), (36, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (14, 1), (36, 1), (55, 1)] }, { coefficient := -1, powers := [(0, 1), (14, 1), (42, 1), (47, 1)] }, { coefficient := 1, powers := [(3, 1), (14, 1), (25, 1), (55, 1)] }, { coefficient := 1, powers := [(14, 1), (15, 1), (30, 1), (36, 1)] }, { coefficient := -1, powers := [(14, 1), (25, 1), (42, 1), (47, 1)] }, { coefficient := -1, powers := [(14, 1), (30, 1), (36, 1), (42, 1)] }, { coefficient := -1, powers := [(14, 1), (33, 1), (36, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (30, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (15, 1), (30, 1)] }, { coefficient := 1, powers := [(8, 1), (30, 1), (42, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (5, 1), (32, 1), (42, 1), (54, 1)] }, { coefficient := -1, powers := [(5, 1), (25, 1), (32, 1), (42, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(47, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (5, 1), (32, 1), (42, 1), (43, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (25, 1), (32, 1), (42, 1), (43, 1), (54, 1)] }, { coefficient := 1, powers := [(42, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(0, 1), (36, 1), (55, 1)] }, { coefficient := 1, powers := [(0, 1), (42, 1), (47, 1)] }, { coefficient := -1, powers := [(3, 1), (25, 1), (55, 1)] }, { coefficient := -1, powers := [(15, 1), (30, 1), (36, 1)] }, { coefficient := 1, powers := [(25, 1), (42, 1), (47, 1)] }, { coefficient := 1, powers := [(30, 1), (36, 1), (42, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1), (47, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (5, 1), (35, 1), (36, 1), (51, 1), (55, 1)] }, { coefficient := 1, powers := [(0, 1), (5, 1), (35, 1), (42, 1), (47, 1), (51, 1)] }, { coefficient := -1, powers := [(3, 1), (5, 1), (25, 1), (35, 1), (51, 1), (55, 1)] }, { coefficient := -1, powers := [(5, 1), (15, 1), (30, 1), (35, 1), (36, 1), (51, 1)] }, { coefficient := 1, powers := [(5, 1), (25, 1), (35, 1), (42, 1), (47, 1), (51, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (35, 1), (36, 1), (42, 1), (51, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (35, 1), (36, 1), (47, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (36, 1), (38, 1), (55, 1), (57, 1)] }, { coefficient := -1, powers := [(0, 1), (36, 1), (40, 1), (46, 1), (51, 1), (55, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (36, 1), (46, 1), (51, 1), (55, 1)] }, { coefficient := -1, powers := [(0, 1), (38, 1), (42, 1), (47, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (40, 1), (42, 1), (46, 1), (47, 1), (51, 1), (59, 1)] }, { coefficient := -1, powers := [(0, 1), (42, 1), (46, 1), (47, 1), (51, 1)] }, { coefficient := 1, powers := [(3, 1), (25, 1), (38, 1), (55, 1), (57, 1)] }, { coefficient := -1, powers := [(3, 1), (25, 1), (40, 1), (46, 1), (51, 1), (55, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (25, 1), (46, 1), (51, 1), (55, 1)] }, { coefficient := 1, powers := [(15, 1), (30, 1), (36, 1), (38, 1), (57, 1)] }, { coefficient := 1, powers := [(15, 1), (30, 1), (36, 1), (46, 1), (51, 1)] }, { coefficient := -1, powers := [(25, 1), (38, 1), (42, 1), (47, 1), (57, 1)] }, { coefficient := 1, powers := [(25, 1), (40, 1), (42, 1), (46, 1), (47, 1), (51, 1), (59, 1)] }, { coefficient := -1, powers := [(25, 1), (42, 1), (46, 1), (47, 1), (51, 1)] }, { coefficient := -1, powers := [(30, 1), (36, 1), (38, 1), (42, 1), (57, 1)] }, { coefficient := -1, powers := [(30, 1), (36, 1), (42, 1), (46, 1), (51, 1)] }, { coefficient := -1, powers := [(33, 1), (36, 1), (38, 1), (47, 1), (57, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1), (40, 1), (46, 1), (47, 1), (51, 1), (59, 1)] }, { coefficient := -1, powers := [(33, 1), (36, 1), (46, 1), (47, 1), (51, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (5, 1), (25, 1), (32, 1), (42, 1), (43, 1), (54, 1)] }, { coefficient := -1, powers := [(5, 1), (25, 2), (32, 1), (42, 1), (43, 1), (54, 1)] }, { coefficient := 1, powers := [(6, 1), (33, 1)] }, { coefficient := 1, powers := [(15, 1), (25, 1)] }, { coefficient := -1, powers := [(25, 1), (42, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (8, 1), (32, 1), (36, 1), (46, 1), (55, 1)] }, { coefficient := 1, powers := [(0, 1), (8, 1), (32, 1), (42, 1), (46, 1), (47, 1)] }, { coefficient := -1, powers := [(3, 1), (8, 1), (25, 1), (32, 1), (46, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (25, 1), (32, 1), (42, 1), (46, 1), (47, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (33, 1), (36, 1), (46, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (2, 1), (36, 1), (54, 1), (55, 1)] }, { coefficient := -1, powers := [(0, 1), (2, 1), (42, 1), (47, 1), (54, 1)] }, { coefficient := 1, powers := [(0, 1), (8, 1), (35, 1), (36, 1), (55, 1)] }, { coefficient := -1, powers := [(0, 1), (8, 1), (35, 1), (42, 1), (47, 1)] }, { coefficient := 1, powers := [(2, 1), (3, 1), (25, 1), (54, 1), (55, 1)] }, { coefficient := 1, powers := [(2, 1), (15, 1), (30, 1), (36, 1), (54, 1)] }, { coefficient := -1, powers := [(2, 1), (25, 1), (42, 1), (47, 1), (54, 1)] }, { coefficient := -1, powers := [(2, 1), (30, 1), (36, 1), (42, 1), (54, 1)] }, { coefficient := -1, powers := [(2, 1), (33, 1), (36, 1), (47, 1), (54, 1)] }, { coefficient := 1, powers := [(3, 1), (8, 1), (25, 1), (35, 1), (55, 1)] }, { coefficient := 1, powers := [(6, 1), (8, 1), (15, 1), (30, 1), (35, 1)] }, { coefficient := -1, powers := [(6, 1), (8, 1), (30, 1), (35, 1), (42, 1)] }, { coefficient := 1, powers := [(8, 1), (15, 1), (30, 1), (35, 1), (36, 1)] }, { coefficient := -1, powers := [(8, 1), (25, 1), (35, 1), (42, 1), (47, 1)] }, { coefficient := -1, powers := [(8, 1), (30, 1), (35, 1), (36, 1), (42, 1)] }, { coefficient := -1, powers := [(8, 1), (33, 1), (35, 1), (36, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (18, 1), (21, 1), (32, 1), (36, 1), (48, 1), (54, 1)] }, { coefficient := 1, powers := [(0, 1), (39, 1)] }, { coefficient := -1, powers := [(3, 1), (5, 1), (30, 1), (32, 1), (54, 1)] }, { coefficient := 1, powers := [(3, 1), (18, 1), (21, 1), (25, 1), (32, 1), (48, 1), (54, 1)] }, { coefficient := 1, powers := [(3, 1), (30, 1)] }, { coefficient := 1, powers := [(9, 1), (20, 1)] }, { coefficient := 1, powers := [(18, 1), (21, 1), (32, 1), (36, 1), (47, 1), (54, 1)] }, { coefficient := -1, powers := [(20, 1), (47, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (14, 1), (29, 1), (36, 1), (46, 1), (55, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (14, 1), (29, 1), (42, 1), (46, 1), (47, 1), (59, 1)] }, { coefficient := -1, powers := [(3, 1), (14, 1), (25, 1), (29, 1), (46, 1), (55, 1), (59, 1)] }, { coefficient := 1, powers := [(14, 1), (25, 1), (29, 1), (42, 1), (46, 1), (47, 1), (59, 1)] }, { coefficient := 1, powers := [(14, 1), (29, 1), (33, 1), (36, 1), (46, 1), (47, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (5, 1), (20, 1), (32, 1), (42, 1), (43, 1), (47, 1), (54, 1)] }, { coefficient := 1, powers := [(0, 1), (5, 1), (20, 1), (35, 1), (36, 1), (51, 1), (55, 1), (58, 1)] }, { coefficient := -1, powers := [(0, 1), (5, 1), (20, 1), (35, 1), (42, 1), (47, 1), (51, 1), (58, 1)] }, { coefficient := 1, powers := [(3, 1), (5, 1), (20, 1), (25, 1), (35, 1), (51, 1), (55, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (15, 1), (20, 1), (30, 1), (35, 1), (36, 1), (51, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (20, 1), (25, 1), (32, 1), (42, 1), (43, 1), (47, 1), (54, 1)] }, { coefficient := -1, powers := [(5, 1), (20, 1), (25, 1), (35, 1), (42, 1), (47, 1), (51, 1), (58, 1)] }, { coefficient := -1, powers := [(5, 1), (20, 1), (30, 1), (35, 1), (36, 1), (42, 1), (51, 1), (58, 1)] }, { coefficient := -1, powers := [(5, 1), (20, 1), (33, 1), (35, 1), (36, 1), (47, 1), (51, 1), (58, 1)] }, { coefficient := -1, powers := [(6, 1), (20, 1), (55, 1)] }, { coefficient := -1, powers := [(9, 1), (33, 1), (36, 1)] }, { coefficient := 1, powers := [(20, 1), (42, 1), (47, 1)] }]
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
    (values : Fin 61 → R) :
    ¬ ∀ index : Fin 32,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component47.SelectedLeafB4_2_1.selectedHasNoCommonZero

end Krenn.Component47.SelectedLeafB4_2_1
