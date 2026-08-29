import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component15.SelectedLeafB0

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "830e31eed0a59302d41831a390e11c4231e349419152a95c7ca393f0bba45e69"
def certificateSHA256 : String := "2529ca5d338b6d4e676148d14e04c8f795ceb0bf9e2bb467f1db5cb925a71b55"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 43 → Fin 589 := ![
  10,
  12,
  13,
  17,
  26,
  29,
  31,
  34,
  36,
  37,
  38,
  45,
  184,
  211,
  227,
  228,
  232,
  237,
  340,
  362,
  363,
  364,
  365,
  366,
  367,
  368,
  379,
  381,
  421,
  423,
  471,
  476,
  496,
  519,
  527,
  528,
  546,
  575,
  584,
  585,
  586,
  587,
  588
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 43 → SparsePoly (Fin 57) := ![
  [{ coefficient := 1, powers := [(4, 1), (32, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (31, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(15, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (17, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (19, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(32, 1), (34, 1)] }],
  [{ coefficient := 1, powers := [(26, 1), (42, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (46, 1)] }, { coefficient := 1, powers := [(12, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (40, 1)] }, { coefficient := 1, powers := [(25, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (48, 1)] }, { coefficient := 1, powers := [(21, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(26, 1), (37, 1)] }, { coefficient := 1, powers := [(26, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(42, 1), (46, 1)] }, { coefficient := 1, powers := [(46, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (40, 1), (49, 1)] }, { coefficient := 1, powers := [(19, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (50, 1)] }, { coefficient := 1, powers := [(17, 1), (50, 1)] }, { coefficient := 1, powers := [(23, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (42, 1)] }, { coefficient := 1, powers := [(4, 1), (31, 1)] }, { coefficient := 1, powers := [(15, 1), (19, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (48, 1)] }, { coefficient := 1, powers := [(7, 1), (28, 1)] }, { coefficient := 1, powers := [(11, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (44, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1)] }, { coefficient := 1, powers := [(16, 1), (21, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (50, 1)] }, { coefficient := 1, powers := [(8, 1), (29, 1)] }, { coefficient := 1, powers := [(12, 1), (26, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (56, 1)] }, { coefficient := 1, powers := [(12, 1), (44, 1)] }, { coefficient := 1, powers := [(16, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (56, 1)] }, { coefficient := 1, powers := [(12, 1), (53, 1)] }, { coefficient := 1, powers := [(16, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1), (50, 1)] }, { coefficient := 1, powers := [(23, 1), (42, 1), (46, 1)] }, { coefficient := 1, powers := [(50, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1), (48, 1)] }, { coefficient := 1, powers := [(18, 1), (40, 1), (48, 1)] }, { coefficient := 1, powers := [(44, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (32, 1), (48, 1)] }, { coefficient := 1, powers := [(7, 1), (32, 1), (37, 1)] }, { coefficient := 1, powers := [(11, 1), (32, 1), (34, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (24, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (28, 1), (52, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (50, 1)] }, { coefficient := 1, powers := [(26, 1), (38, 1)] }, { coefficient := 1, powers := [(26, 1), (43, 1), (46, 1)] }, { coefficient := 1, powers := [(29, 1), (35, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (38, 1), (52, 1)] }, { coefficient := 1, powers := [(18, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(38, 1)] }, { coefficient := 1, powers := [(43, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (24, 1), (55, 1)] }, { coefficient := 1, powers := [(3, 1), (28, 1), (52, 1)] }, { coefficient := 1, powers := [(3, 1), (31, 1), (48, 1)] }, { coefficient := 1, powers := [(24, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (40, 1), (49, 1)] }, { coefficient := 1, powers := [(21, 1), (53, 1)] }, { coefficient := 1, powers := [(26, 1), (44, 1)] }, { coefficient := 1, powers := [(32, 1), (35, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1)] }, { coefficient := 1, powers := [(6, 1), (55, 1)] }, { coefficient := 1, powers := [(22, 1), (37, 1)] }, { coefficient := 1, powers := [(22, 1), (42, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (48, 1)] }, { coefficient := 1, powers := [(3, 1), (55, 1)] }, { coefficient := 1, powers := [(17, 1), (48, 1)] }, { coefficient := 1, powers := [(17, 1), (52, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(19, 1), (48, 1)] }, { coefficient := 1, powers := [(19, 1), (52, 1)] }, { coefficient := 1, powers := [(24, 1), (37, 1)] }, { coefficient := 1, powers := [(24, 1), (42, 1)] }, { coefficient := 1, powers := [(28, 1), (34, 1)] }, { coefficient := 1, powers := [(31, 1), (34, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (34, 1), (55, 1)] }, { coefficient := 1, powers := [(0, 1), (37, 1), (52, 1)] }, { coefficient := 1, powers := [(0, 1), (42, 1), (48, 1)] }, { coefficient := 1, powers := [(37, 1)] }, { coefficient := 1, powers := [(42, 1)] }, { coefficient := 1, powers := [(48, 1)] }, { coefficient := 1, powers := [(52, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (34, 1), (55, 1)] }, { coefficient := 1, powers := [(1, 1), (37, 1), (52, 1)] }, { coefficient := 1, powers := [(1, 1), (42, 1), (48, 1)] }, { coefficient := 1, powers := [(4, 1), (24, 1), (55, 1)] }, { coefficient := 1, powers := [(4, 1), (28, 1), (52, 1)] }, { coefficient := 1, powers := [(4, 1), (31, 1), (48, 1)] }, { coefficient := 1, powers := [(7, 1), (19, 1), (55, 1)] }, { coefficient := 1, powers := [(7, 1), (28, 1), (42, 1)] }, { coefficient := 1, powers := [(7, 1), (31, 1), (37, 1)] }, { coefficient := 1, powers := [(11, 1), (19, 1), (52, 1)] }, { coefficient := 1, powers := [(11, 1), (24, 1), (42, 1)] }, { coefficient := 1, powers := [(11, 1), (31, 1), (34, 1)] }, { coefficient := 1, powers := [(15, 1), (19, 1), (48, 1)] }, { coefficient := 1, powers := [(15, 1), (24, 1), (37, 1)] }, { coefficient := 1, powers := [(15, 1), (28, 1), (34, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (35, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (38, 1), (53, 1)] }, { coefficient := 1, powers := [(2, 1), (44, 1), (50, 1)] }, { coefficient := 1, powers := [(5, 1), (26, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (53, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (50, 1)] }, { coefficient := 1, powers := [(8, 1), (21, 1), (56, 1)] }, { coefficient := 1, powers := [(8, 1), (29, 1), (44, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (38, 1)] }, { coefficient := 1, powers := [(12, 1), (21, 1), (53, 1)] }, { coefficient := 1, powers := [(12, 1), (26, 1), (44, 1)] }, { coefficient := 1, powers := [(12, 1), (32, 1), (35, 1)] }, { coefficient := 1, powers := [(16, 1), (21, 1), (50, 1)] }, { coefficient := 1, powers := [(16, 1), (26, 1), (38, 1)] }, { coefficient := 1, powers := [(16, 1), (29, 1), (35, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1)] }],
  [{ coefficient := 1, powers := [(1, 1)] }],
  [{ coefficient := 1, powers := [(2, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 43 → SparsePoly (Fin 57) := ![
  [{ coefficient := 1, powers := [(8, 1), (24, 1), (38, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (28, 1), (38, 1), (52, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1), (38, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (29, 1), (52, 1), (53, 1)] }, { coefficient := -1, powers := [(7, 1), (29, 1), (42, 1), (53, 1)] }, { coefficient := -1, powers := [(7, 1), (29, 1), (48, 1), (53, 1)] }, { coefficient := -1, powers := [(7, 1), (29, 1), (52, 1), (53, 1)] }, { coefficient := 1, powers := [(11, 1), (29, 1), (34, 1), (53, 1)] }, { coefficient := -1, powers := [(15, 1), (29, 1), (34, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (19, 1), (29, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (21, 1), (56, 1)] }, { coefficient := -2, powers := [(6, 1), (29, 1), (44, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (24, 1), (32, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (50, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (11, 1), (29, 2), (35, 1), (52, 1), (53, 1)] }, { coefficient := 1, powers := [(7, 1), (8, 1), (29, 1), (32, 1), (35, 1), (38, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (11, 1), (29, 1), (32, 1), (35, 1), (38, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (8, 1), (11, 1), (18, 1), (29, 2), (48, 1), (52, 1), (53, 1)] }, { coefficient := 1, powers := [(5, 1), (11, 1), (12, 1), (18, 1), (26, 1), (29, 1), (48, 1), (52, 1), (53, 1)] }, { coefficient := -1, powers := [(7, 1), (8, 2), (18, 1), (29, 1), (32, 1), (38, 1), (48, 1), (55, 1)] }, { coefficient := 1, powers := [(7, 1), (8, 1), (12, 1), (18, 1), (26, 1), (32, 1), (38, 1), (48, 1), (55, 1)] }, { coefficient := -1, powers := [(8, 2), (11, 1), (18, 1), (29, 1), (32, 1), (38, 1), (48, 1), (52, 1)] }, { coefficient := 1, powers := [(8, 1), (11, 1), (12, 1), (18, 1), (26, 1), (32, 1), (38, 1), (48, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (8, 1), (11, 1), (18, 1), (29, 1), (32, 1), (52, 2), (53, 1)] }, { coefficient := -1, powers := [(5, 1), (8, 1), (11, 1), (29, 1), (32, 1), (43, 1), (52, 1), (53, 1)] }, { coefficient := -1, powers := [(7, 1), (8, 2), (18, 1), (32, 2), (38, 1), (52, 1), (55, 1)] }, { coefficient := -1, powers := [(7, 1), (8, 2), (32, 2), (38, 1), (43, 1), (55, 1)] }, { coefficient := -1, powers := [(8, 2), (11, 1), (18, 1), (32, 2), (38, 1), (52, 2)] }, { coefficient := -1, powers := [(8, 2), (11, 1), (32, 2), (38, 1), (43, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(5, 2), (11, 1), (29, 2), (40, 1), (52, 1), (53, 1)] }, { coefficient := -1, powers := [(5, 1), (7, 1), (8, 1), (29, 1), (32, 1), (38, 1), (40, 1), (55, 1)] }, { coefficient := -1, powers := [(5, 1), (8, 1), (11, 1), (29, 1), (32, 1), (38, 1), (40, 1), (52, 1)] }, { coefficient := 1, powers := [(5, 1), (11, 1), (12, 1), (21, 1), (29, 1), (40, 1), (52, 1), (53, 1)] }, { coefficient := 1, powers := [(5, 1), (11, 1), (12, 1), (25, 1), (29, 1), (44, 1), (52, 1), (53, 1)] }, { coefficient := 1, powers := [(7, 1), (8, 1), (12, 1), (21, 1), (32, 1), (38, 1), (40, 1), (55, 1)] }, { coefficient := 1, powers := [(7, 1), (8, 1), (12, 1), (25, 1), (32, 1), (38, 1), (44, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (11, 1), (12, 1), (21, 1), (32, 1), (38, 1), (40, 1), (52, 1)] }, { coefficient := 1, powers := [(8, 1), (11, 1), (12, 1), (25, 1), (32, 1), (38, 1), (44, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (11, 1), (16, 1), (21, 1), (29, 1), (52, 1), (53, 1)] }, { coefficient := -1, powers := [(7, 1), (8, 1), (16, 1), (21, 1), (32, 1), (38, 1), (55, 1)] }, { coefficient := -1, powers := [(8, 1), (11, 1), (16, 1), (21, 1), (32, 1), (38, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (15, 1), (31, 1), (38, 1)] }],
  [{ coefficient := -1, powers := [(16, 1), (18, 1)] }],
  [{ coefficient := 1, powers := [(44, 1), (49, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (11, 1), (12, 1), (19, 1), (29, 1), (49, 1), (52, 1), (53, 1)] }, { coefficient := -1, powers := [(7, 1), (8, 1), (12, 1), (19, 1), (32, 1), (38, 1), (49, 1), (55, 1)] }, { coefficient := -1, powers := [(8, 1), (11, 1), (12, 1), (19, 1), (32, 1), (38, 1), (49, 1), (52, 1)] }, { coefficient := -1, powers := [(12, 1), (49, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (17, 1), (56, 1)] }],
  [{ coefficient := 2, powers := [(12, 1), (22, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (18, 1), (26, 1)] }, { coefficient := 1, powers := [(16, 1), (21, 1), (23, 1)] }],
  [{ coefficient := 1, powers := [(5, 2), (11, 1), (29, 2), (52, 1), (53, 1)] }, { coefficient := 1, powers := [(5, 1), (7, 1), (8, 1), (29, 1), (32, 1), (38, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (8, 1), (11, 1), (29, 1), (32, 1), (38, 1), (52, 1)] }, { coefficient := -1, powers := [(5, 1), (11, 1), (12, 1), (21, 1), (29, 1), (52, 1), (53, 1)] }, { coefficient := -1, powers := [(7, 1), (8, 1), (12, 1), (21, 1), (32, 1), (38, 1), (55, 1)] }, { coefficient := -1, powers := [(8, 1), (11, 1), (12, 1), (21, 1), (32, 1), (38, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(16, 1), (21, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (29, 1), (52, 1), (53, 1)] }, { coefficient := -1, powers := [(8, 1), (32, 1), (38, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (29, 1), (42, 1), (53, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (38, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (11, 1), (19, 1), (29, 1), (50, 1), (52, 1), (53, 1)] }, { coefficient := 1, powers := [(7, 1), (8, 1), (19, 1), (32, 1), (38, 1), (50, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (11, 1), (19, 1), (32, 1), (38, 1), (50, 1), (52, 1)] }, { coefficient := 1, powers := [(50, 1)] }],
  [{ coefficient := 2, powers := [(6, 1), (44, 1), (55, 1)] }, { coefficient := 1, powers := [(44, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (11, 1), (19, 1), (26, 1), (29, 1), (52, 1), (53, 1)] }, { coefficient := 1, powers := [(7, 1), (8, 1), (19, 1), (26, 1), (32, 1), (38, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (11, 1), (19, 1), (26, 1), (32, 1), (38, 1), (52, 1)] }, { coefficient := 1, powers := [(26, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (11, 1), (19, 1), (21, 1), (29, 1), (52, 1), (53, 1)] }, { coefficient := 1, powers := [(7, 1), (8, 1), (19, 1), (21, 1), (32, 1), (38, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (11, 1), (19, 1), (21, 1), (32, 1), (38, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(16, 1), (21, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (8, 1), (11, 1), (19, 1), (29, 2), (52, 1), (53, 1)] }, { coefficient := -1, powers := [(5, 1), (11, 1), (12, 1), (19, 1), (26, 1), (29, 1), (52, 1), (53, 1)] }, { coefficient := 1, powers := [(7, 1), (8, 2), (19, 1), (29, 1), (32, 1), (38, 1), (55, 1)] }, { coefficient := -1, powers := [(7, 1), (8, 1), (12, 1), (19, 1), (26, 1), (32, 1), (38, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 2), (11, 1), (19, 1), (29, 1), (32, 1), (38, 1), (52, 1)] }, { coefficient := -1, powers := [(8, 1), (11, 1), (12, 1), (19, 1), (26, 1), (32, 1), (38, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (31, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (15, 1), (29, 1), (42, 1), (53, 1)] }, { coefficient := 1, powers := [(4, 1), (29, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(16, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (8, 1), (11, 1), (19, 1), (29, 1), (32, 1), (52, 1), (53, 1)] }, { coefficient := 1, powers := [(7, 1), (8, 2), (19, 1), (32, 2), (38, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 2), (11, 1), (19, 1), (32, 2), (38, 1), (52, 1)] }, { coefficient := -1, powers := [(16, 1), (26, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (15, 1), (29, 1), (42, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (11, 1), (12, 1), (19, 1), (29, 1), (52, 1), (53, 1)] }, { coefficient := 1, powers := [(7, 1), (8, 1), (12, 1), (19, 1), (32, 1), (38, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (11, 1), (12, 1), (19, 1), (32, 1), (38, 1), (52, 1)] }, { coefficient := 1, powers := [(12, 1)] }],
  [{ coefficient := -2, powers := [(12, 1), (26, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (21, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (15, 1), (29, 1), (53, 1)] }, { coefficient := 1, powers := [(8, 1), (15, 1), (32, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (7, 1), (29, 1), (31, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (29, 1), (53, 1)] }, { coefficient := -1, powers := [(8, 1), (32, 1), (38, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (11, 1), (19, 1), (29, 1), (52, 1), (53, 1)] }, { coefficient := -1, powers := [(7, 1), (8, 1), (19, 1), (32, 1), (38, 1), (55, 1)] }, { coefficient := -1, powers := [(8, 1), (11, 1), (19, 1), (32, 1), (38, 1), (52, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(5, 1), (7, 1), (29, 1), (31, 1), (34, 1), (53, 1), (55, 1)] }, { coefficient := -1, powers := [(5, 1), (7, 1), (29, 1), (31, 1), (37, 1), (52, 1), (53, 1)] }, { coefficient := -1, powers := [(5, 1), (7, 1), (29, 1), (31, 1), (42, 1), (48, 1), (53, 1)] }, { coefficient := -1, powers := [(5, 1), (8, 1), (11, 1), (19, 1), (29, 2), (44, 1), (48, 1), (52, 1), (53, 1)] }, { coefficient := -1, powers := [(5, 1), (8, 1), (11, 1), (19, 1), (29, 1), (32, 1), (38, 1), (52, 2), (53, 1)] }, { coefficient := 1, powers := [(5, 1), (11, 1), (12, 1), (19, 1), (26, 1), (29, 1), (44, 1), (48, 1), (52, 1), (53, 1)] }, { coefficient := -1, powers := [(7, 1), (8, 2), (19, 1), (29, 1), (32, 1), (38, 1), (44, 1), (48, 1), (55, 1)] }, { coefficient := -1, powers := [(7, 1), (8, 2), (19, 1), (32, 2), (38, 2), (52, 1), (55, 1)] }, { coefficient := 1, powers := [(7, 1), (8, 1), (12, 1), (19, 1), (26, 1), (32, 1), (38, 1), (44, 1), (48, 1), (55, 1)] }, { coefficient := -1, powers := [(8, 2), (11, 1), (19, 1), (29, 1), (32, 1), (38, 1), (44, 1), (48, 1), (52, 1)] }, { coefficient := -1, powers := [(8, 2), (11, 1), (19, 1), (32, 2), (38, 2), (52, 2)] }, { coefficient := 1, powers := [(8, 1), (11, 1), (12, 1), (19, 1), (26, 1), (32, 1), (38, 1), (44, 1), (48, 1), (52, 1)] }, { coefficient := -1, powers := [(8, 1), (21, 1), (48, 1), (56, 1)] }, { coefficient := 2, powers := [(12, 1), (26, 1), (42, 1), (44, 1)] }, { coefficient := 1, powers := [(16, 1), (21, 1), (42, 1), (50, 1)] }, { coefficient := 1, powers := [(16, 1), (21, 1), (50, 1), (52, 1)] }, { coefficient := 1, powers := [(16, 1), (26, 1), (38, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (29, 1), (34, 1), (53, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (37, 1), (52, 1), (53, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (42, 1), (52, 1), (53, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (34, 1), (38, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (37, 1), (38, 1), (52, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (38, 1), (42, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (11, 1), (19, 1), (29, 1), (35, 1), (52, 1), (53, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (11, 1), (19, 1), (29, 1), (38, 1), (52, 1), (53, 2)] }, { coefficient := -2, powers := [(6, 1), (44, 1), (50, 1), (55, 1)] }, { coefficient := 1, powers := [(7, 1), (8, 1), (19, 1), (32, 1), (35, 1), (38, 1), (55, 1), (56, 1)] }, { coefficient := 1, powers := [(7, 1), (8, 1), (19, 1), (32, 1), (38, 2), (53, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (11, 1), (19, 1), (32, 1), (35, 1), (38, 1), (52, 1), (56, 1)] }, { coefficient := 1, powers := [(8, 1), (11, 1), (19, 1), (32, 1), (38, 2), (52, 1), (53, 1)] }, { coefficient := 1, powers := [(35, 1), (56, 1)] }, { coefficient := 1, powers := [(38, 1), (53, 1)] }, { coefficient := -1, powers := [(44, 1), (46, 1), (49, 1)] }, { coefficient := -1, powers := [(44, 1), (50, 1)] }]
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
    (values : Fin 57 → R) :
    ¬ ∀ index : Fin 43,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component15.SelectedLeafB0.selectedHasNoCommonZero

end Krenn.Component15.SelectedLeafB0
