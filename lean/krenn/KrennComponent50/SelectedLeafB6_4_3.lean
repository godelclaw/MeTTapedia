import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component50.SelectedLeafB6_4_3

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "fe33b55846f5447b43fbb98655cb087cabb181c1f4280ed7949a256420c3ccc4"
def certificateSHA256 : String := "bf91c27b495d1cb13764f91ef74f269668c60e4bdba2f12f9ac576fc88869be2"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 36 → Fin 644 := ![
  2,
  7,
  26,
  45,
  163,
  164,
  169,
  170,
  174,
  191,
  196,
  208,
  228,
  241,
  343,
  349,
  355,
  362,
  363,
  364,
  432,
  448,
  465,
  560,
  576,
  577,
  632,
  634,
  635,
  636,
  637,
  639,
  640,
  641,
  642,
  643
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 36 → SparsePoly (Fin 65) := ![
  [{ coefficient := 1, powers := [(3, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (33, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (51, 1)] }, { coefficient := 1, powers := [(20, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (53, 1)] }, { coefficient := 1, powers := [(20, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (51, 1)] }, { coefficient := 1, powers := [(14, 1), (29, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (52, 1)] }, { coefficient := 1, powers := [(18, 1), (30, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (34, 1)] }, { coefficient := 1, powers := [(18, 1), (21, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (45, 1)] }, { coefficient := 1, powers := [(19, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (20, 1)] }, { coefficient := 1, powers := [(18, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1), (49, 1)] }, { coefficient := 1, powers := [(9, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (30, 1), (58, 1)] }, { coefficient := 1, powers := [(30, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (34, 1), (49, 1)] }, { coefficient := 1, powers := [(5, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (43, 1)] }, { coefficient := 1, powers := [(11, 1), (22, 1), (54, 1)] }, { coefficient := 1, powers := [(11, 1), (27, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (53, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1)] }, { coefficient := 1, powers := [(14, 1), (30, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (44, 1)] }, { coefficient := 1, powers := [(14, 1), (55, 1)] }, { coefficient := 1, powers := [(18, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (53, 1)] }, { coefficient := 1, powers := [(30, 1), (42, 1)] }, { coefficient := 1, powers := [(33, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (56, 1)] }, { coefficient := 1, powers := [(30, 1), (47, 1)] }, { coefficient := 1, powers := [(36, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (52, 1)] }, { coefficient := 1, powers := [(30, 1), (41, 1)] }, { coefficient := 1, powers := [(30, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (20, 1), (55, 1)] }, { coefficient := 1, powers := [(14, 1)] }, { coefficient := 1, powers := [(18, 1), (20, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (26, 1), (45, 1), (49, 1)] }, { coefficient := 1, powers := [(9, 1), (26, 1), (45, 1)] }, { coefficient := 1, powers := [(9, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (59, 1)] }, { coefficient := 1, powers := [(14, 1), (26, 1), (45, 1)] }, { coefficient := 1, powers := [(14, 1), (56, 1)] }, { coefficient := 1, powers := [(19, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (41, 1), (54, 1)] }, { coefficient := 1, powers := [(6, 1), (34, 1), (41, 1)] }, { coefficient := 1, powers := [(15, 1), (25, 1), (41, 1)] }, { coefficient := 1, powers := [(15, 1)] }, { coefficient := 1, powers := [(54, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1)] }, { coefficient := 1, powers := [(3, 1), (34, 1)] }, { coefficient := 1, powers := [(15, 1), (20, 1)] }, { coefficient := 1, powers := [(20, 1), (54, 1)] }, { coefficient := 1, powers := [(25, 1), (43, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (48, 1)] }, { coefficient := 1, powers := [(6, 1), (31, 1)] }, { coefficient := 1, powers := [(9, 1), (25, 1)] }, { coefficient := 1, powers := [(20, 1), (48, 1)] }, { coefficient := 1, powers := [(25, 1), (40, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (37, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (40, 1), (54, 1)] }, { coefficient := 1, powers := [(0, 1), (43, 1), (48, 1)] }, { coefficient := 1, powers := [(3, 1), (25, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (31, 1), (54, 1)] }, { coefficient := 1, powers := [(3, 1), (34, 1), (48, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1), (57, 1)] }, { coefficient := 1, powers := [(6, 1), (31, 1), (43, 1)] }, { coefficient := 1, powers := [(6, 1), (34, 1), (40, 1)] }, { coefficient := 1, powers := [(9, 1), (20, 1), (54, 1)] }, { coefficient := 1, powers := [(9, 1), (25, 1), (43, 1)] }, { coefficient := 1, powers := [(9, 1), (34, 1), (37, 1)] }, { coefficient := 1, powers := [(15, 1), (20, 1), (48, 1)] }, { coefficient := 1, powers := [(15, 1), (25, 1), (40, 1)] }, { coefficient := 1, powers := [(15, 1), (31, 1), (37, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (39, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (42, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (47, 1), (53, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1), (53, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (59, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (47, 1)] }, { coefficient := 1, powers := [(8, 1), (36, 1), (42, 1)] }, { coefficient := 1, powers := [(14, 1), (24, 1), (56, 1)] }, { coefficient := 1, powers := [(14, 1), (30, 1), (47, 1)] }, { coefficient := 1, powers := [(14, 1), (36, 1), (39, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (53, 1)] }, { coefficient := 1, powers := [(19, 1), (30, 1), (42, 1)] }, { coefficient := 1, powers := [(19, 1), (33, 1), (39, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (60, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1), (61, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(41, 1)] }],
  [{ coefficient := 1, powers := [(42, 1)] }],
  [{ coefficient := 1, powers := [(54, 1)] }],
  [{ coefficient := 1, powers := [(55, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(56, 1), (64, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 36 → SparsePoly (Fin 65) := ![
  [{ coefficient := -1, powers := [(0, 1), (5, 1), (30, 1), (37, 1), (57, 1), (58, 1)] }, { coefficient := -1, powers := [(3, 1), (5, 1), (25, 1), (30, 1), (57, 1), (58, 1)] }, { coefficient := -1, powers := [(5, 1), (6, 1), (30, 1), (34, 1), (40, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (34, 1), (37, 1), (48, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (27, 1), (48, 1), (61, 1)] }, { coefficient := 1, powers := [(25, 1), (27, 1), (40, 1), (61, 1)] }, { coefficient := 1, powers := [(25, 1), (27, 1), (48, 1), (61, 1)] }, { coefficient := 1, powers := [(27, 1), (31, 1), (37, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (5, 1), (36, 1), (37, 1), (53, 1), (57, 1), (60, 1), (64, 1)] }, { coefficient := 1, powers := [(0, 1), (14, 1), (24, 1), (37, 1), (55, 1), (56, 1), (57, 1), (64, 1)] }, { coefficient := 1, powers := [(0, 1), (18, 1), (24, 1), (25, 1), (37, 1), (51, 1), (56, 1), (57, 1), (60, 1), (64, 1)] }, { coefficient := -1, powers := [(0, 1), (19, 1), (24, 1), (26, 1), (37, 1), (51, 1), (57, 1), (60, 1), (64, 1)] }, { coefficient := 1, powers := [(0, 1), (19, 1), (24, 1), (37, 1), (53, 1), (57, 1), (60, 1), (64, 1)] }, { coefficient := -1, powers := [(3, 1), (5, 1), (25, 1), (36, 1), (53, 1), (57, 1), (60, 1), (64, 1)] }, { coefficient := 1, powers := [(3, 1), (14, 1), (24, 1), (25, 1), (55, 1), (56, 1), (57, 1), (64, 1)] }, { coefficient := 1, powers := [(3, 1), (18, 1), (24, 1), (25, 2), (51, 1), (56, 1), (57, 1), (60, 1), (64, 1)] }, { coefficient := -1, powers := [(3, 1), (19, 1), (24, 1), (25, 1), (26, 1), (51, 1), (57, 1), (60, 1), (64, 1)] }, { coefficient := 1, powers := [(3, 1), (19, 1), (24, 1), (25, 1), (53, 1), (57, 1), (60, 1), (64, 1)] }, { coefficient := -1, powers := [(5, 1), (6, 1), (34, 1), (36, 1), (40, 1), (53, 1), (60, 1), (64, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (36, 1), (37, 1), (48, 1), (53, 1), (60, 1), (64, 1)] }, { coefficient := 1, powers := [(6, 1), (14, 1), (24, 1), (34, 1), (40, 1), (55, 1), (56, 1), (64, 1)] }, { coefficient := 1, powers := [(6, 1), (18, 1), (24, 1), (25, 1), (34, 1), (40, 1), (51, 1), (56, 1), (60, 1), (64, 1)] }, { coefficient := -1, powers := [(6, 1), (19, 1), (24, 1), (26, 1), (34, 1), (40, 1), (51, 1), (60, 1), (64, 1)] }, { coefficient := 1, powers := [(6, 1), (19, 1), (24, 1), (34, 1), (40, 1), (53, 1), (60, 1), (64, 1)] }, { coefficient := 1, powers := [(6, 1), (57, 1), (64, 1)] }, { coefficient := -1, powers := [(14, 1), (24, 1), (34, 1), (37, 1), (48, 1), (55, 1), (56, 1), (64, 1)] }, { coefficient := -1, powers := [(18, 1), (24, 1), (25, 1), (34, 1), (37, 1), (48, 1), (51, 1), (56, 1), (60, 1), (64, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (26, 1), (34, 1), (37, 1), (48, 1), (51, 1), (60, 1), (64, 1)] }, { coefficient := -1, powers := [(19, 1), (24, 1), (34, 1), (37, 1), (48, 1), (53, 1), (60, 1), (64, 1)] }, { coefficient := -1, powers := [(43, 1), (48, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (25, 1), (56, 1), (57, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (18, 1), (24, 1), (25, 1), (37, 1), (56, 1), (57, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (19, 1), (24, 1), (26, 1), (37, 1), (57, 1), (60, 1)] }, { coefficient := -1, powers := [(3, 1), (18, 1), (24, 1), (25, 2), (56, 1), (57, 1), (60, 1)] }, { coefficient := 1, powers := [(3, 1), (19, 1), (24, 1), (25, 1), (26, 1), (57, 1), (60, 1)] }, { coefficient := -1, powers := [(6, 1), (18, 1), (24, 1), (25, 1), (34, 1), (40, 1), (56, 1), (60, 1)] }, { coefficient := 1, powers := [(6, 1), (19, 1), (24, 1), (26, 1), (34, 1), (40, 1), (60, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (25, 1), (34, 1), (37, 1), (48, 1), (56, 1), (60, 1)] }, { coefficient := -1, powers := [(19, 1), (24, 1), (26, 1), (34, 1), (37, 1), (48, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (5, 1), (36, 1), (37, 1), (57, 1), (60, 1)] }, { coefficient := -1, powers := [(0, 1), (19, 1), (24, 1), (37, 1), (57, 1), (60, 1)] }, { coefficient := 1, powers := [(3, 1), (5, 1), (25, 1), (36, 1), (57, 1), (60, 1)] }, { coefficient := -1, powers := [(3, 1), (19, 1), (24, 1), (25, 1), (57, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (6, 1), (34, 1), (36, 1), (40, 1), (60, 1)] }, { coefficient := -1, powers := [(5, 1), (34, 1), (36, 1), (37, 1), (48, 1), (60, 1)] }, { coefficient := -1, powers := [(6, 1), (19, 1), (24, 1), (34, 1), (40, 1), (60, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (34, 1), (37, 1), (48, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (37, 1), (47, 1), (52, 1), (57, 1), (63, 1)] }, { coefficient := -1, powers := [(3, 1), (25, 1), (47, 1), (52, 1), (57, 1), (63, 1)] }, { coefficient := -1, powers := [(6, 1), (34, 1), (40, 1), (47, 1), (52, 1), (63, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1), (47, 1), (48, 1), (52, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (37, 1), (47, 1), (51, 1), (57, 1), (63, 1)] }, { coefficient := 1, powers := [(3, 1), (25, 1), (47, 1), (51, 1), (57, 1), (63, 1)] }, { coefficient := 1, powers := [(6, 1), (34, 1), (40, 1), (47, 1), (51, 1), (63, 1)] }, { coefficient := -1, powers := [(34, 1), (37, 1), (47, 1), (48, 1), (51, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (33, 1), (37, 1), (49, 1), (56, 1)] }, { coefficient := 1, powers := [(6, 1), (33, 1), (40, 1), (56, 1)] }, { coefficient := -1, powers := [(33, 1), (37, 1), (48, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (24, 1), (26, 1), (37, 1), (57, 1)] }, { coefficient := -1, powers := [(3, 1), (24, 1), (25, 1), (26, 1), (57, 1)] }, { coefficient := -1, powers := [(6, 1), (24, 1), (26, 1), (34, 1), (40, 1)] }, { coefficient := 1, powers := [(24, 1), (26, 1), (34, 1), (37, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (24, 1), (37, 1), (51, 1), (56, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (24, 1), (25, 1), (51, 1), (56, 1), (57, 1)] }, { coefficient := 1, powers := [(6, 1), (24, 1), (34, 1), (40, 1), (51, 1), (56, 1)] }, { coefficient := -1, powers := [(24, 1), (34, 1), (37, 1), (48, 1), (51, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [(26, 1), (34, 1), (37, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (5, 1), (37, 1), (57, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (5, 1), (25, 1), (57, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (6, 1), (34, 1), (40, 1), (59, 1)] }, { coefficient := -1, powers := [(5, 1), (34, 1), (37, 1), (48, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (33, 1), (37, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (48, 1), (61, 1)] }, { coefficient := -1, powers := [(25, 1), (40, 1), (61, 1)] }, { coefficient := -1, powers := [(25, 1), (48, 1), (61, 1)] }, { coefficient := -1, powers := [(31, 1), (37, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (37, 1), (47, 1), (55, 1), (57, 1), (63, 1)] }, { coefficient := 1, powers := [(3, 1), (25, 1), (47, 1), (55, 1), (57, 1), (63, 1)] }, { coefficient := 1, powers := [(6, 1), (34, 1), (40, 1), (47, 1), (55, 1), (63, 1)] }, { coefficient := -1, powers := [(34, 1), (37, 1), (47, 1), (48, 1), (55, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (30, 1), (37, 1), (47, 1), (57, 1), (63, 1)] }, { coefficient := -1, powers := [(3, 1), (25, 1), (30, 1), (47, 1), (57, 1), (63, 1)] }, { coefficient := -1, powers := [(6, 1), (30, 1), (34, 1), (40, 1), (47, 1), (63, 1)] }, { coefficient := 1, powers := [(30, 1), (34, 1), (37, 1), (47, 1), (48, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (19, 1), (37, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (19, 1), (25, 1), (57, 1)] }, { coefficient := 1, powers := [(6, 1), (19, 1), (34, 1), (40, 1)] }, { coefficient := -1, powers := [(19, 1), (34, 1), (37, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (14, 1), (37, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (14, 1), (25, 1), (57, 1)] }, { coefficient := 1, powers := [(6, 1), (14, 1), (34, 1), (40, 1)] }, { coefficient := -1, powers := [(14, 1), (34, 1), (37, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (14, 1), (37, 1), (47, 1), (57, 1), (63, 1)] }, { coefficient := 1, powers := [(3, 1), (14, 1), (25, 1), (47, 1), (57, 1), (63, 1)] }, { coefficient := 1, powers := [(6, 1), (14, 1), (34, 1), (40, 1), (47, 1), (63, 1)] }, { coefficient := -1, powers := [(14, 1), (34, 1), (37, 1), (47, 1), (48, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (24, 1), (37, 1), (56, 1), (57, 1)] }, { coefficient := -1, powers := [(3, 1), (24, 1), (25, 1), (56, 1), (57, 1)] }, { coefficient := -1, powers := [(6, 1), (24, 1), (34, 1), (40, 1), (56, 1)] }, { coefficient := 1, powers := [(24, 1), (34, 1), (37, 1), (48, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(34, 1), (37, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (24, 1), (37, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (24, 1), (25, 1), (57, 1)] }, { coefficient := 1, powers := [(6, 1), (24, 1), (34, 1), (40, 1)] }, { coefficient := -1, powers := [(24, 1), (34, 1), (37, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (40, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(48, 1)] }],
  [{ coefficient := 1, powers := [(43, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(0, 1), (37, 1), (57, 1)] }, { coefficient := -1, powers := [(3, 1), (25, 1), (57, 1)] }, { coefficient := -1, powers := [(6, 1), (34, 1), (40, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1), (48, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (5, 1), (36, 1), (37, 1), (53, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (18, 1), (24, 1), (25, 1), (37, 1), (51, 1), (56, 1), (57, 1)] }, { coefficient := -1, powers := [(0, 1), (19, 1), (24, 1), (26, 1), (37, 1), (51, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (19, 1), (24, 1), (37, 1), (53, 1), (57, 1)] }, { coefficient := -1, powers := [(3, 1), (5, 1), (25, 1), (36, 1), (53, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (18, 1), (24, 1), (25, 2), (51, 1), (56, 1), (57, 1)] }, { coefficient := -1, powers := [(3, 1), (19, 1), (24, 1), (25, 1), (26, 1), (51, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (19, 1), (24, 1), (25, 1), (53, 1), (57, 1)] }, { coefficient := -1, powers := [(5, 1), (6, 1), (34, 1), (36, 1), (40, 1), (53, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (36, 1), (37, 1), (48, 1), (53, 1)] }, { coefficient := 1, powers := [(6, 1), (18, 1), (24, 1), (25, 1), (34, 1), (40, 1), (51, 1), (56, 1)] }, { coefficient := -1, powers := [(6, 1), (19, 1), (24, 1), (26, 1), (34, 1), (40, 1), (51, 1)] }, { coefficient := 1, powers := [(6, 1), (19, 1), (24, 1), (34, 1), (40, 1), (53, 1)] }, { coefficient := -1, powers := [(18, 1), (24, 1), (25, 1), (34, 1), (37, 1), (48, 1), (51, 1), (56, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (26, 1), (34, 1), (37, 1), (48, 1), (51, 1)] }, { coefficient := -1, powers := [(19, 1), (24, 1), (34, 1), (37, 1), (48, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1), (48, 1)] }, { coefficient := 1, powers := [(25, 1), (40, 1), (43, 1)] }, { coefficient := 1, powers := [(25, 1), (43, 1), (48, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (37, 1), (39, 1), (57, 1), (59, 1)] }, { coefficient := -1, powers := [(0, 1), (37, 1), (47, 1), (53, 1), (55, 1), (57, 1), (63, 1)] }, { coefficient := 1, powers := [(0, 1), (37, 1), (47, 1), (53, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (25, 1), (39, 1), (57, 1), (59, 1)] }, { coefficient := -1, powers := [(3, 1), (25, 1), (47, 1), (53, 1), (55, 1), (57, 1), (63, 1)] }, { coefficient := 1, powers := [(3, 1), (25, 1), (47, 1), (53, 1), (57, 1)] }, { coefficient := 1, powers := [(6, 1), (34, 1), (39, 1), (40, 1), (59, 1)] }, { coefficient := -1, powers := [(6, 1), (34, 1), (40, 1), (47, 1), (53, 1), (55, 1), (63, 1)] }, { coefficient := 1, powers := [(6, 1), (34, 1), (40, 1), (47, 1), (53, 1)] }, { coefficient := -1, powers := [(34, 1), (37, 1), (39, 1), (48, 1), (59, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1), (47, 1), (48, 1), (53, 1), (55, 1), (63, 1)] }, { coefficient := -1, powers := [(34, 1), (37, 1), (47, 1), (48, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (14, 1), (30, 1), (37, 1), (47, 1), (57, 1), (63, 1)] }, { coefficient := -1, powers := [(3, 1), (14, 1), (25, 1), (30, 1), (47, 1), (57, 1), (63, 1)] }, { coefficient := -1, powers := [(6, 1), (14, 1), (30, 1), (34, 1), (40, 1), (47, 1), (63, 1)] }, { coefficient := -1, powers := [(6, 1), (25, 1), (34, 1), (40, 1)] }, { coefficient := -1, powers := [(6, 1), (31, 1), (34, 1), (37, 1)] }, { coefficient := 1, powers := [(14, 1), (30, 1), (34, 1), (37, 1), (47, 1), (48, 1), (63, 1)] }, { coefficient := -1, powers := [(15, 1), (25, 2), (40, 1)] }, { coefficient := -1, powers := [(15, 1), (25, 1), (31, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (2, 1), (37, 1), (56, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (8, 1), (36, 1), (37, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (3, 1), (25, 1), (56, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (6, 1), (34, 1), (40, 1), (56, 1)] }, { coefficient := -1, powers := [(2, 1), (34, 1), (37, 1), (48, 1), (56, 1)] }, { coefficient := 1, powers := [(3, 1), (8, 1), (25, 1), (36, 1), (57, 1)] }, { coefficient := 1, powers := [(6, 1), (8, 1), (34, 1), (36, 1), (40, 1)] }, { coefficient := -1, powers := [(8, 1), (34, 1), (36, 1), (37, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (11, 1), (22, 1), (48, 1), (61, 1)] }, { coefficient := 1, powers := [(0, 1), (18, 1), (21, 1), (33, 1), (37, 1), (49, 1), (56, 1)] }, { coefficient := -1, powers := [(0, 1), (25, 1), (40, 1), (41, 1)] }, { coefficient := -1, powers := [(0, 1), (31, 1), (37, 1), (41, 1)] }, { coefficient := 1, powers := [(0, 1), (40, 1)] }, { coefficient := 1, powers := [(3, 1), (31, 1)] }, { coefficient := -1, powers := [(6, 1), (18, 1), (21, 1), (33, 1), (40, 1), (56, 1)] }, { coefficient := 1, powers := [(9, 1), (20, 1)] }, { coefficient := 1, powers := [(11, 1), (22, 1), (25, 1), (40, 1), (61, 1)] }, { coefficient := 1, powers := [(11, 1), (22, 1), (25, 1), (48, 1), (61, 1)] }, { coefficient := 1, powers := [(11, 1), (22, 1), (31, 1), (37, 1), (61, 1)] }, { coefficient := 1, powers := [(18, 1), (21, 1), (33, 1), (37, 1), (48, 1), (56, 1)] }, { coefficient := -1, powers := [(20, 1), (48, 1)] }, { coefficient := -1, powers := [(25, 1), (40, 1)] }, { coefficient := -1, powers := [(31, 1), (37, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (8, 1), (33, 1), (37, 1), (47, 1), (57, 1)] }, { coefficient := -1, powers := [(3, 1), (5, 1), (25, 1), (33, 1), (56, 1), (57, 1)] }, { coefficient := -1, powers := [(3, 1), (8, 1), (25, 1), (33, 1), (47, 1), (57, 1)] }, { coefficient := -1, powers := [(6, 1), (8, 1), (33, 1), (34, 1), (40, 1), (47, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (34, 1), (37, 1), (47, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (5, 1), (20, 1), (36, 1), (37, 1), (53, 1), (57, 1), (60, 1)] }, { coefficient := -1, powers := [(0, 1), (14, 1), (20, 1), (24, 1), (37, 1), (55, 1), (56, 1), (57, 1)] }, { coefficient := -1, powers := [(0, 1), (18, 1), (20, 1), (24, 1), (25, 1), (37, 1), (51, 1), (56, 1), (57, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (19, 1), (20, 1), (24, 1), (26, 1), (37, 1), (51, 1), (57, 1), (60, 1)] }, { coefficient := -1, powers := [(0, 1), (19, 1), (20, 1), (24, 1), (37, 1), (53, 1), (57, 1), (60, 1)] }, { coefficient := 1, powers := [(3, 1), (5, 1), (20, 1), (25, 1), (36, 1), (53, 1), (57, 1), (60, 1)] }, { coefficient := -1, powers := [(3, 1), (14, 1), (20, 1), (24, 1), (25, 1), (55, 1), (56, 1), (57, 1)] }, { coefficient := -1, powers := [(3, 1), (18, 1), (20, 1), (24, 1), (25, 2), (51, 1), (56, 1), (57, 1), (60, 1)] }, { coefficient := 1, powers := [(3, 1), (19, 1), (20, 1), (24, 1), (25, 1), (26, 1), (51, 1), (57, 1), (60, 1)] }, { coefficient := -1, powers := [(3, 1), (19, 1), (20, 1), (24, 1), (25, 1), (53, 1), (57, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (6, 1), (20, 1), (34, 1), (36, 1), (40, 1), (53, 1), (60, 1)] }, { coefficient := -1, powers := [(5, 1), (20, 1), (34, 1), (36, 1), (37, 1), (48, 1), (53, 1), (60, 1)] }, { coefficient := -1, powers := [(6, 1), (14, 1), (20, 1), (24, 1), (34, 1), (40, 1), (55, 1), (56, 1)] }, { coefficient := -1, powers := [(6, 1), (18, 1), (20, 1), (24, 1), (25, 1), (34, 1), (40, 1), (51, 1), (56, 1), (60, 1)] }, { coefficient := 1, powers := [(6, 1), (19, 1), (20, 1), (24, 1), (26, 1), (34, 1), (40, 1), (51, 1), (60, 1)] }, { coefficient := -1, powers := [(6, 1), (19, 1), (20, 1), (24, 1), (34, 1), (40, 1), (53, 1), (60, 1)] }, { coefficient := -1, powers := [(6, 1), (20, 1), (57, 1)] }, { coefficient := -1, powers := [(9, 1), (34, 1), (37, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1), (24, 1), (34, 1), (37, 1), (48, 1), (55, 1), (56, 1)] }, { coefficient := 1, powers := [(18, 1), (20, 1), (24, 1), (25, 1), (34, 1), (37, 1), (48, 1), (51, 1), (56, 1), (60, 1)] }, { coefficient := -1, powers := [(19, 1), (20, 1), (24, 1), (26, 1), (34, 1), (37, 1), (48, 1), (51, 1), (60, 1)] }, { coefficient := 1, powers := [(19, 1), (20, 1), (24, 1), (34, 1), (37, 1), (48, 1), (53, 1), (60, 1)] }, { coefficient := 1, powers := [(20, 1), (43, 1), (48, 1)] }]
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
    (values : Fin 65 → R) :
    ¬ ∀ index : Fin 36,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component50.SelectedLeafB6_4_3.selectedHasNoCommonZero

end Krenn.Component50.SelectedLeafB6_4_3
