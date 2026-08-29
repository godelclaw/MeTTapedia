import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.FrozenCase0NoncollapseType01Chart3B4W01ZeroCertificate

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "f971c49352500c158ea2a276dc567588ece5432e98414dbf46cead3a8feb73d4"
def certificateSHA256 : String := "e22e637312af3d806aaa7be3989df1b3e7d0b924e5a127199609a67e44015c8c"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 34 → Fin 547 := ![
  0,
  1,
  27,
  28,
  30,
  31,
  83,
  87,
  97,
  99,
  211,
  217,
  218,
  220,
  221,
  257,
  259,
  260,
  265,
  266,
  270,
  273,
  274,
  357,
  380,
  381,
  389,
  390,
  392,
  393,
  540,
  542,
  545,
  546
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 34 → SparsePoly (Fin 63) := ![
  [{ coefficient := 1, powers := [(5, 1), (38, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (40, 1), (56, 1)] }, { coefficient := 1, powers := [(7, 1), (26, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (32, 1), (56, 1)] }, { coefficient := 1, powers := [(7, 1), (35, 1), (48, 1)] }, { coefficient := 1, powers := [(10, 1), (21, 1), (59, 1)] }, { coefficient := 1, powers := [(10, 1), (35, 1), (40, 1)] }, { coefficient := 1, powers := [(15, 1), (21, 1), (48, 1)] }, { coefficient := 1, powers := [(15, 1), (26, 1), (40, 1)] }, { coefficient := 1, powers := [(15, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(5, 1), (48, 1)] }, { coefficient := 1, powers := [(10, 1), (32, 1)] }, { coefficient := 1, powers := [(21, 1), (48, 1)] }, { coefficient := 1, powers := [(26, 1), (40, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (43, 1), (48, 1)] }, { coefficient := 1, powers := [(10, 1), (32, 1), (43, 1)] }, { coefficient := 1, powers := [(10, 1), (59, 1)] }, { coefficient := 1, powers := [(15, 1), (48, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (41, 1), (48, 1)] }, { coefficient := -1, powers := [(10, 1), (32, 1), (41, 1)] }, { coefficient := 1, powers := [(48, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (41, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (43, 1)] }, { coefficient := 1, powers := [(10, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(15, 1), (26, 1), (41, 1)] }, { coefficient := 1, powers := [(15, 1)] }, { coefficient := 1, powers := [(26, 1), (43, 1)] }, { coefficient := 1, powers := [(56, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (41, 1)] }, { coefficient := 1, powers := [(10, 1), (60, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(7, 1), (36, 1)] }, { coefficient := 1, powers := [(10, 1), (33, 1)] }, { coefficient := 1, powers := [(33, 1), (38, 1)] }, { coefficient := 1, powers := [(36, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (33, 1), (57, 1)] }, { coefficient := 1, powers := [(7, 1), (36, 1), (51, 1)] }],
  [{ coefficient := -1, powers := [(10, 1), (33, 1), (41, 1)] }, { coefficient := 1, powers := [(10, 1), (36, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(15, 1), (28, 1), (41, 1)] }, { coefficient := 1, powers := [(28, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (35, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (35, 1), (50, 1)] }, { coefficient := 1, powers := [(8, 1), (59, 1)] }, { coefficient := 1, powers := [(11, 1), (32, 1), (43, 1)] }, { coefficient := 1, powers := [(11, 1), (59, 1)] }, { coefficient := 1, powers := [(13, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (32, 1), (57, 1)] }, { coefficient := -1, powers := [(11, 1), (32, 1), (41, 1)] }, { coefficient := -1, powers := [(13, 1), (41, 1)] }, { coefficient := 1, powers := [(13, 1), (57, 1)] }, { coefficient := 1, powers := [(17, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (35, 1), (51, 1)] }, { coefficient := 1, powers := [(11, 1), (35, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (60, 1)] }, { coefficient := 1, powers := [(11, 1), (60, 1)] }, { coefficient := 1, powers := [(17, 1), (41, 1)] }, { coefficient := 1, powers := [(17, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (33, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (36, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (33, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (33, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (33, 1), (57, 1)] }, { coefficient := 1, powers := [(8, 1), (36, 1), (51, 1)] }, { coefficient := -1, powers := [(11, 1), (33, 1), (41, 1)] }, { coefficient := 1, powers := [(11, 1), (36, 1), (41, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(8, 1), (28, 1), (59, 1)] }, { coefficient := 1, powers := [(13, 1), (28, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (36, 1), (53, 1)] }, { coefficient := -1, powers := [(13, 1), (28, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (21, 1)] }, { coefficient := 1, powers := [(14, 1), (21, 1)] }, { coefficient := 1, powers := [(14, 1), (26, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (48, 1)] }, { coefficient := 1, powers := [(14, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (50, 1)] }, { coefficient := 1, powers := [(14, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (43, 1)] }, { coefficient := 1, powers := [(19, 1), (41, 1)] }, { coefficient := 1, powers := [(19, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (41, 1)] }, { coefficient := 1, powers := [(1, 1), (51, 1)] }, { coefficient := 1, powers := [(14, 1), (51, 1)] }, { coefficient := 1, powers := [(14, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (4, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1), (21, 1), (51, 1)] }, { coefficient := 1, powers := [(1, 1), (26, 1), (51, 1)] }, { coefficient := -1, powers := [(1, 1)] }, { coefficient := 1, powers := [(14, 1), (21, 1), (51, 1)] }, { coefficient := 1, powers := [(14, 1), (21, 1), (57, 1)] }, { coefficient := 1, powers := [(14, 1), (26, 1), (51, 1)] }, { coefficient := 1, powers := [(14, 1), (26, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (41, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(28, 1), (62, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 34 → SparsePoly (Fin 63) := ![
  [{ coefficient := -2, powers := [] }],
  [{ coefficient := -2, powers := [(0, 2), (41, 1), (43, 1)] }, { coefficient := 2, powers := [(0, 1), (15, 1), (41, 1)] }, { coefficient := -4, powers := [(0, 1), (26, 1), (41, 1), (43, 1)] }, { coefficient := 2, powers := [(0, 1), (43, 1)] }, { coefficient := 4, powers := [(26, 1), (43, 1)] }, { coefficient := -2, powers := [(56, 1)] }],
  [{ coefficient := -2, powers := [(0, 1)] }, { coefficient := -4, powers := [(26, 1)] }],
  [{ coefficient := -2, powers := [(0, 2), (43, 1)] }, { coefficient := 2, powers := [(0, 1), (15, 1)] }, { coefficient := -4, powers := [(0, 1), (26, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (48, 1)] }, { coefficient := 1, powers := [(21, 1), (48, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (38, 1), (59, 1)] }, { coefficient := -1, powers := [(5, 1), (15, 1), (48, 1)] }, { coefficient := 1, powers := [(5, 1), (48, 1), (56, 1)] }, { coefficient := -1, powers := [(15, 1), (21, 1), (48, 1)] }, { coefficient := 1, powers := [(21, 1), (48, 1), (56, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (8, 1), (38, 1), (57, 1), (59, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (8, 1), (15, 1), (48, 1), (57, 1), (60, 1)] }, { coefficient := -1, powers := [(5, 1), (8, 1), (48, 1), (56, 1), (57, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (15, 1), (21, 1), (48, 1), (57, 1), (60, 1)] }, { coefficient := -1, powers := [(8, 1), (21, 1), (48, 1), (56, 1), (57, 1), (60, 1)] }, { coefficient := 2, powers := [(8, 1), (26, 1), (57, 1), (59, 1)] }, { coefficient := 2, powers := [(8, 1), (32, 1), (56, 1), (57, 1)] }, { coefficient := 2, powers := [(11, 1), (26, 1), (41, 1), (59, 1)] }, { coefficient := 2, powers := [(11, 1), (32, 1), (41, 1), (56, 1)] }],
  [{ coefficient := 2, powers := [(8, 1), (26, 1), (59, 1)] }, { coefficient := 2, powers := [(8, 1), (32, 1), (56, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (11, 1), (38, 1), (59, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (11, 1), (15, 1), (48, 1), (60, 1)] }, { coefficient := -1, powers := [(5, 1), (11, 1), (48, 1), (56, 1), (60, 1)] }, { coefficient := 1, powers := [(11, 1), (15, 1), (21, 1), (48, 1), (60, 1)] }, { coefficient := -1, powers := [(11, 1), (21, 1), (48, 1), (56, 1), (60, 1)] }, { coefficient := 2, powers := [(11, 1), (26, 1), (59, 1)] }, { coefficient := 2, powers := [(11, 1), (32, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [(5, 2), (48, 1), (62, 1)] }, { coefficient := -1, powers := [(5, 1), (21, 1), (48, 1), (62, 1)] }, { coefficient := -1, powers := [(5, 1), (26, 1), (48, 1), (62, 1)] }, { coefficient := 2, powers := [(13, 1), (21, 1), (33, 1), (38, 1), (57, 1), (62, 1)] }, { coefficient := 4, powers := [(13, 1), (26, 1), (33, 1), (38, 1), (57, 1), (62, 1)] }, { coefficient := -1, powers := [(21, 1), (26, 1), (48, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (10, 1), (33, 1), (41, 1), (48, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (10, 1), (36, 1), (41, 1), (48, 1), (51, 1)] }, { coefficient := 2, powers := [(7, 1), (33, 1), (48, 1), (57, 1)] }, { coefficient := -2, powers := [(7, 1), (36, 1), (48, 1), (51, 1)] }, { coefficient := -1, powers := [(10, 1), (21, 1), (33, 1), (41, 1), (48, 1), (57, 1)] }, { coefficient := 1, powers := [(10, 1), (21, 1), (36, 1), (41, 1), (48, 1), (51, 1)] }, { coefficient := 2, powers := [(10, 1), (33, 1), (40, 1), (57, 1)] }, { coefficient := -2, powers := [(10, 1), (36, 1), (40, 1), (51, 1)] }, { coefficient := 2, powers := [(21, 1), (36, 1), (38, 1), (41, 1), (50, 1)] }, { coefficient := 4, powers := [(26, 1), (36, 1), (38, 1), (41, 1), (50, 1)] }],
  [{ coefficient := -2, powers := [(21, 1), (36, 1), (38, 1), (41, 1)] }, { coefficient := -4, powers := [(26, 1), (36, 1), (38, 1), (41, 1)] }],
  [{ coefficient := -2, powers := [(21, 1), (36, 1), (38, 1), (43, 1)] }, { coefficient := -4, powers := [(26, 1), (36, 1), (38, 1), (43, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (10, 1), (36, 1), (41, 1), (48, 1)] }, { coefficient := 2, powers := [(7, 1), (36, 1), (48, 1)] }, { coefficient := -1, powers := [(10, 1), (21, 1), (36, 1), (41, 1), (48, 1)] }, { coefficient := 2, powers := [(10, 1), (36, 1), (40, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (33, 1), (38, 2), (57, 1), (59, 1)] }, { coefficient := -1, powers := [(5, 1), (15, 1), (33, 1), (38, 1), (48, 1), (57, 1)] }, { coefficient := -1, powers := [(15, 1), (21, 1), (33, 1), (38, 1), (48, 1), (57, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (38, 1), (41, 1), (57, 1), (59, 1)] }, { coefficient := 2, powers := [(0, 1), (38, 1), (51, 1), (57, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (15, 1), (41, 1), (48, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (15, 1), (48, 1), (51, 1), (57, 1)] }, { coefficient := 1, powers := [(15, 1), (21, 1), (41, 1), (48, 1), (57, 1)] }, { coefficient := 1, powers := [(15, 1), (21, 1), (48, 1), (51, 1), (57, 1)] }],
  [{ coefficient := 2, powers := [(5, 1), (41, 1), (56, 1)] }, { coefficient := 2, powers := [(26, 1), (41, 1), (56, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (38, 2), (57, 1), (59, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (10, 1), (35, 1), (41, 2), (48, 1)] }, { coefficient := 1, powers := [(5, 1), (15, 1), (38, 1), (48, 1), (57, 1), (60, 1)] }, { coefficient := -2, powers := [(5, 1), (40, 1), (41, 1), (56, 1)] }, { coefficient := -2, powers := [(7, 1), (26, 1), (41, 1), (59, 1)] }, { coefficient := -2, powers := [(7, 1), (32, 1), (41, 1), (56, 1)] }, { coefficient := -2, powers := [(7, 1), (35, 1), (41, 1), (48, 1)] }, { coefficient := 1, powers := [(10, 1), (21, 1), (35, 1), (41, 2), (48, 1)] }, { coefficient := -2, powers := [(10, 1), (26, 1), (41, 1), (59, 1)] }, { coefficient := -2, powers := [(10, 1), (32, 1), (41, 1), (56, 1)] }, { coefficient := -2, powers := [(10, 1), (35, 1), (40, 1), (41, 1)] }, { coefficient := 1, powers := [(15, 1), (21, 1), (38, 1), (48, 1), (57, 1), (60, 1)] }, { coefficient := 2, powers := [(21, 1), (38, 1), (41, 1), (59, 1)] }, { coefficient := -2, powers := [(26, 1), (40, 1), (41, 1), (56, 1)] }, { coefficient := -4, powers := [(32, 1), (38, 1), (41, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (38, 1), (48, 1), (57, 1), (60, 1)] }, { coefficient := 2, powers := [(5, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(21, 1), (38, 1), (48, 1), (57, 1), (60, 1)] }, { coefficient := 2, powers := [(26, 1), (40, 1), (57, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (7, 1), (38, 1), (57, 1), (59, 1), (60, 1)] }, { coefficient := 2, powers := [(0, 1), (10, 1), (38, 1), (51, 1), (59, 1), (60, 1)] }, { coefficient := -2, powers := [(0, 1), (38, 2), (57, 1), (59, 1), (60, 1)] }, { coefficient := -1, powers := [(5, 1), (7, 1), (15, 1), (48, 1), (57, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (7, 1), (48, 1), (56, 1), (57, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (10, 1), (15, 1), (48, 1), (51, 1), (60, 1)] }, { coefficient := -1, powers := [(5, 1), (10, 1), (35, 1), (41, 1), (48, 1), (51, 1)] }, { coefficient := -1, powers := [(5, 1), (10, 1), (48, 1), (51, 1), (56, 1), (60, 1)] }, { coefficient := -1, powers := [(5, 1), (15, 1), (38, 1), (48, 1), (57, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (38, 1), (48, 1), (56, 1), (57, 1), (60, 1)] }, { coefficient := 2, powers := [(5, 1), (40, 1), (51, 1), (56, 1)] }, { coefficient := -1, powers := [(7, 1), (15, 1), (21, 1), (48, 1), (57, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (21, 1), (48, 1), (56, 1), (57, 1), (60, 1)] }, { coefficient := -2, powers := [(7, 1), (26, 1), (57, 1), (59, 1)] }, { coefficient := -2, powers := [(7, 1), (32, 1), (56, 1), (57, 1)] }, { coefficient := 2, powers := [(7, 1), (35, 1), (48, 1), (51, 1)] }, { coefficient := 1, powers := [(10, 1), (15, 1), (21, 1), (48, 1), (51, 1), (60, 1)] }, { coefficient := -1, powers := [(10, 1), (21, 1), (35, 1), (41, 1), (48, 1), (51, 1)] }, { coefficient := -1, powers := [(10, 1), (21, 1), (48, 1), (51, 1), (56, 1), (60, 1)] }, { coefficient := 2, powers := [(10, 1), (26, 1), (51, 1), (59, 1)] }, { coefficient := 2, powers := [(10, 1), (32, 1), (51, 1), (56, 1)] }, { coefficient := 2, powers := [(10, 1), (35, 1), (40, 1), (51, 1)] }, { coefficient := -2, powers := [(15, 1), (21, 1), (33, 1), (38, 1), (53, 1), (57, 1), (62, 1)] }, { coefficient := -1, powers := [(15, 1), (21, 1), (38, 1), (48, 1), (57, 1), (60, 1)] }, { coefficient := -4, powers := [(15, 1), (26, 1), (33, 1), (38, 1), (53, 1), (57, 1), (62, 1)] }, { coefficient := 2, powers := [(21, 1), (32, 1), (38, 1), (43, 1), (57, 1)] }, { coefficient := 2, powers := [(21, 1), (38, 1), (41, 1), (59, 1)] }, { coefficient := 1, powers := [(21, 1), (38, 1), (48, 1), (56, 1), (57, 1), (60, 1)] }, { coefficient := -2, powers := [(21, 1), (38, 1), (51, 1), (59, 1)] }, { coefficient := -2, powers := [(21, 1), (38, 1), (57, 1), (59, 1)] }, { coefficient := 4, powers := [(26, 1), (32, 1), (38, 1), (43, 1), (57, 1)] }, { coefficient := 4, powers := [(26, 1), (38, 1), (41, 1), (59, 1)] }, { coefficient := -2, powers := [(26, 1), (38, 1), (51, 1), (59, 1)] }, { coefficient := -6, powers := [(26, 1), (38, 1), (57, 1), (59, 1)] }, { coefficient := 2, powers := [(26, 1), (40, 1), (51, 1), (56, 1)] }, { coefficient := 2, powers := [(32, 1), (38, 1), (51, 1), (56, 1)] }, { coefficient := -2, powers := [(32, 1), (38, 1), (56, 1), (57, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (10, 1), (38, 1), (59, 1), (60, 1)] }, { coefficient := -1, powers := [(5, 1), (10, 1), (15, 1), (48, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (10, 1), (35, 1), (41, 1), (48, 1)] }, { coefficient := 1, powers := [(5, 1), (10, 1), (48, 1), (56, 1), (60, 1)] }, { coefficient := -2, powers := [(5, 1), (40, 1), (56, 1)] }, { coefficient := -2, powers := [(7, 1), (26, 1), (59, 1)] }, { coefficient := -2, powers := [(7, 1), (32, 1), (56, 1)] }, { coefficient := -2, powers := [(7, 1), (35, 1), (48, 1)] }, { coefficient := -1, powers := [(10, 1), (15, 1), (21, 1), (48, 1), (60, 1)] }, { coefficient := 1, powers := [(10, 1), (21, 1), (35, 1), (41, 1), (48, 1)] }, { coefficient := 1, powers := [(10, 1), (21, 1), (48, 1), (56, 1), (60, 1)] }, { coefficient := -2, powers := [(10, 1), (26, 1), (59, 1)] }, { coefficient := -2, powers := [(10, 1), (32, 1), (56, 1)] }, { coefficient := -2, powers := [(10, 1), (35, 1), (40, 1)] }, { coefficient := 2, powers := [(21, 1), (38, 1), (59, 1)] }, { coefficient := 2, powers := [(26, 1), (38, 1), (59, 1)] }, { coefficient := -2, powers := [(26, 1), (40, 1), (56, 1)] }, { coefficient := -2, powers := [(32, 1), (38, 1), (56, 1)] }],
  [{ coefficient := -2, powers := [(21, 1), (33, 1), (38, 1), (57, 1), (62, 1)] }, { coefficient := 2, powers := [(21, 1), (36, 1), (38, 1), (57, 1), (62, 1)] }, { coefficient := -4, powers := [(26, 1), (33, 1), (38, 1), (57, 1), (62, 1)] }, { coefficient := 4, powers := [(26, 1), (36, 1), (38, 1), (57, 1), (62, 1)] }],
  [{ coefficient := 2, powers := [(15, 1), (21, 1), (33, 1), (38, 1), (57, 1), (62, 1)] }, { coefficient := 4, powers := [(15, 1), (26, 1), (33, 1), (38, 1), (57, 1), (62, 1)] }],
  [{ coefficient := -4, powers := [(4, 1), (15, 1), (48, 1)] }],
  [{ coefficient := 2, powers := [(0, 2), (4, 1), (41, 1)] }, { coefficient := 2, powers := [(0, 2), (4, 1), (51, 1)] }, { coefficient := 4, powers := [(0, 1), (4, 1), (26, 1), (41, 1)] }, { coefficient := 4, powers := [(0, 1), (4, 1), (26, 1), (51, 1)] }],
  [{ coefficient := 2, powers := [(0, 2), (4, 1), (43, 1)] }, { coefficient := 4, powers := [(0, 1), (4, 1), (26, 1), (43, 1)] }, { coefficient := 4, powers := [(4, 1), (15, 1), (21, 1)] }, { coefficient := 4, powers := [(4, 1), (15, 1), (26, 1)] }],
  [{ coefficient := 2, powers := [(4, 1), (17, 1), (21, 1), (36, 1), (38, 1), (41, 1)] }, { coefficient := 2, powers := [(4, 1), (17, 1), (21, 1), (36, 1), (38, 1), (51, 1)] }, { coefficient := 4, powers := [(4, 1), (17, 1), (26, 1), (36, 1), (38, 1), (41, 1)] }, { coefficient := 4, powers := [(4, 1), (17, 1), (26, 1), (36, 1), (38, 1), (51, 1)] }],
  [{ coefficient := 2, powers := [(4, 1), (17, 1), (21, 1), (36, 1), (38, 1), (43, 1)] }, { coefficient := 4, powers := [(4, 1), (17, 1), (26, 1), (36, 1), (38, 1), (43, 1)] }],
  [{ coefficient := -2, powers := [(0, 2), (4, 1), (48, 1)] }, { coefficient := -4, powers := [(0, 1), (4, 1), (26, 1), (48, 1)] }, { coefficient := -2, powers := [(4, 1), (17, 1), (21, 1), (36, 1), (38, 1), (50, 1)] }, { coefficient := -4, powers := [(4, 1), (17, 1), (26, 1), (36, 1), (38, 1), (50, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (4, 1), (10, 1), (21, 1), (59, 1)] }, { coefficient := 2, powers := [(0, 1), (4, 1), (10, 1), (26, 1), (59, 1)] }, { coefficient := 2, powers := [(0, 1), (4, 1), (21, 1), (38, 1), (59, 1)] }, { coefficient := 2, powers := [(0, 1), (4, 1), (26, 1), (38, 1), (59, 1)] }],
  [{ coefficient := -2, powers := [(0, 2), (43, 1), (48, 1)] }, { coefficient := -2, powers := [(0, 1), (10, 1), (21, 1), (41, 1), (59, 1)] }, { coefficient := -2, powers := [(0, 1), (10, 1), (26, 1), (41, 1), (59, 1)] }, { coefficient := -2, powers := [(0, 1), (10, 1), (59, 1)] }, { coefficient := -2, powers := [(0, 1), (21, 1), (38, 1), (41, 1), (59, 1)] }, { coefficient := -2, powers := [(0, 1), (26, 1), (38, 1), (41, 1), (59, 1)] }, { coefficient := -4, powers := [(0, 1), (26, 1), (43, 1), (48, 1)] }, { coefficient := -2, powers := [(0, 1), (38, 1), (59, 1)] }, { coefficient := -4, powers := [(15, 1), (26, 1), (48, 1)] }, { coefficient := -2, powers := [(17, 1), (21, 1), (36, 1), (38, 1), (43, 1), (50, 1)] }, { coefficient := -4, powers := [(17, 1), (26, 1), (36, 1), (38, 1), (43, 1), (50, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (4, 1), (10, 1), (59, 1)] }, { coefficient := -2, powers := [(0, 1), (4, 1), (38, 1), (59, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (21, 1), (43, 1), (48, 1)] }, { coefficient := 2, powers := [(0, 1), (26, 1), (40, 1), (43, 1)] }, { coefficient := 2, powers := [(0, 1), (32, 1), (38, 1), (43, 1)] }, { coefficient := -2, powers := [(5, 1), (38, 1), (59, 1)] }, { coefficient := -2, powers := [(10, 1), (21, 1), (59, 1)] }, { coefficient := -2, powers := [(10, 1), (26, 1), (59, 1)] }, { coefficient := -2, powers := [(15, 1), (21, 1), (48, 1)] }, { coefficient := -2, powers := [(15, 1), (26, 1), (40, 1)] }, { coefficient := -2, powers := [(15, 1), (32, 1), (38, 1)] }, { coefficient := 4, powers := [(21, 1), (26, 1), (43, 1), (48, 1)] }, { coefficient := -2, powers := [(21, 1), (38, 1), (59, 1)] }, { coefficient := 4, powers := [(26, 2), (40, 1), (43, 1)] }, { coefficient := 4, powers := [(26, 1), (32, 1), (38, 1), (43, 1)] }, { coefficient := -2, powers := [(26, 1), (38, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(5, 2), (15, 1), (41, 1), (48, 1)] }, { coefficient := 1, powers := [(5, 2), (43, 1), (48, 1)] }, { coefficient := 1, powers := [(5, 1), (15, 1), (21, 1), (41, 1), (48, 1)] }, { coefficient := 1, powers := [(5, 1), (15, 1), (26, 1), (41, 1), (48, 1)] }, { coefficient := 1, powers := [(5, 1), (21, 1), (43, 1), (48, 1)] }, { coefficient := 1, powers := [(5, 1), (26, 1), (43, 1), (48, 1)] }, { coefficient := 2, powers := [(8, 1), (21, 1), (33, 1), (38, 1), (57, 1), (59, 1)] }, { coefficient := -2, powers := [(8, 1), (21, 1), (36, 1), (38, 1), (57, 1), (59, 1)] }, { coefficient := 4, powers := [(8, 1), (26, 1), (33, 1), (38, 1), (57, 1), (59, 1)] }, { coefficient := -4, powers := [(8, 1), (26, 1), (36, 1), (38, 1), (57, 1), (59, 1)] }, { coefficient := -2, powers := [(13, 1), (21, 1), (36, 1), (38, 1), (43, 1), (57, 1)] }, { coefficient := -4, powers := [(13, 1), (26, 1), (36, 1), (38, 1), (43, 1), (57, 1)] }, { coefficient := 1, powers := [(15, 1), (21, 1), (26, 1), (41, 1), (48, 1)] }, { coefficient := 1, powers := [(21, 1), (26, 1), (43, 1), (48, 1)] }]
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
    ¬ ∀ index : Fin 34,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((2 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (2 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (2 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.FrozenCase0NoncollapseType01Chart3B4W01ZeroCertificate.selectedHasNoCommonZero

end Krenn.FrozenCase0NoncollapseType01Chart3B4W01ZeroCertificate
