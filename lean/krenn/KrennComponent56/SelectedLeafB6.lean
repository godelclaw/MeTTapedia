import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component56.SelectedLeafB6

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "f803378b73c8686988210f1d93e2ddf589b38a65bc7dda36279ee9e2ff6d130d"
def certificateSHA256 : String := "38a69b034692ab5103bb3618b9018b3aad8c585595c66cb0421fb5b1f562cac4"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 49 → Fin 589 := ![
  8,
  9,
  11,
  13,
  15,
  16,
  17,
  24,
  25,
  26,
  29,
  32,
  207,
  208,
  209,
  210,
  211,
  212,
  214,
  226,
  234,
  235,
  236,
  237,
  241,
  242,
  243,
  263,
  274,
  365,
  366,
  372,
  373,
  383,
  398,
  416,
  417,
  467,
  472,
  473,
  527,
  546,
  547,
  549,
  575,
  585,
  586,
  587,
  588
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 49 → SparsePoly (Fin 59) := ![
  [{ coefficient := 1, powers := [(4, 1), (32, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (26, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (18, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (40, 1)] }, { coefficient := 1, powers := [(10, 1), (24, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (43, 1)] }, { coefficient := 1, powers := [(10, 1), (24, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (44, 1)] }, { coefficient := 1, powers := [(10, 1), (24, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (46, 1)] }, { coefficient := 1, powers := [(14, 1), (19, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (49, 1)] }, { coefficient := 1, powers := [(14, 1), (19, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (50, 1)] }, { coefficient := 1, powers := [(14, 1), (19, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (56, 1)] }, { coefficient := 1, powers := [(7, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (42, 1)] }, { coefficient := 1, powers := [(12, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (37, 1)] }, { coefficient := 1, powers := [(16, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (53, 1)] }, { coefficient := 1, powers := [(23, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (46, 1)] }, { coefficient := 1, powers := [(22, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (48, 1)] }, { coefficient := 1, powers := [(18, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (48, 1)] }, { coefficient := 1, powers := [(21, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (37, 1)] }, { coefficient := 1, powers := [(23, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(26, 1), (37, 1)] }, { coefficient := 1, powers := [(26, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (26, 1), (55, 1)] }, { coefficient := 1, powers := [(26, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (21, 1), (55, 1)] }, { coefficient := 1, powers := [(21, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (44, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1)] }, { coefficient := 1, powers := [(16, 1), (21, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (50, 1)] }, { coefficient := 1, powers := [(8, 1), (29, 1)] }, { coefficient := 1, powers := [(12, 1), (26, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (50, 1)] }, { coefficient := 1, powers := [(26, 1), (38, 1)] }, { coefficient := 1, powers := [(29, 1), (35, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (53, 1)] }, { coefficient := 1, powers := [(26, 1), (44, 1)] }, { coefficient := 1, powers := [(32, 1), (35, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (37, 1), (53, 1)] }, { coefficient := 1, powers := [(4, 1), (28, 1), (53, 1)] }, { coefficient := 1, powers := [(10, 1), (20, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (37, 1), (53, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (37, 1)] }, { coefficient := 1, powers := [(16, 1), (26, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (26, 1), (55, 1)] }, { coefficient := 1, powers := [(10, 1), (26, 1), (42, 1)] }, { coefficient := 1, powers := [(14, 1), (26, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (26, 1), (56, 1)] }, { coefficient := 1, powers := [(4, 1), (29, 1), (53, 1)] }, { coefficient := 1, powers := [(4, 1), (32, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (56, 1)] }, { coefficient := 1, powers := [(12, 1), (44, 1)] }, { coefficient := 1, powers := [(16, 1), (18, 1), (49, 1)] }, { coefficient := 1, powers := [(16, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (37, 1), (53, 1)] }, { coefficient := 1, powers := [(23, 1), (37, 1), (40, 1)] }, { coefficient := 1, powers := [(23, 1), (43, 1)] }, { coefficient := 1, powers := [(53, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (38, 1), (52, 1)] }, { coefficient := 1, powers := [(18, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(18, 1), (49, 1)] }, { coefficient := 1, powers := [(38, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1)] }, { coefficient := 1, powers := [(6, 1), (55, 1)] }, { coefficient := 1, powers := [(22, 1), (37, 1)] }, { coefficient := 1, powers := [(22, 1), (42, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1), (48, 1)] }, { coefficient := 1, powers := [(7, 1), (19, 1), (55, 1)] }, { coefficient := 1, powers := [(7, 1), (28, 1)] }, { coefficient := 1, powers := [(10, 1), (19, 1), (52, 1)] }, { coefficient := 1, powers := [(10, 1), (25, 1)] }, { coefficient := 1, powers := [(14, 1), (19, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (55, 1)] }, { coefficient := 1, powers := [(7, 1), (55, 1)] }, { coefficient := 1, powers := [(10, 1), (42, 1)] }, { coefficient := 1, powers := [(10, 1), (52, 1)] }, { coefficient := 1, powers := [(14, 1), (37, 1)] }, { coefficient := 1, powers := [(14, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (33, 1), (55, 1)] }, { coefficient := 1, powers := [(0, 1)] }, { coefficient := 1, powers := [(3, 1), (22, 1), (55, 1)] }, { coefficient := 1, powers := [(6, 1), (17, 1), (55, 1)] }, { coefficient := 1, powers := [(17, 1)] }, { coefficient := 1, powers := [(22, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (34, 1), (55, 1)] }, { coefficient := 1, powers := [(0, 1), (37, 1), (52, 1)] }, { coefficient := 1, powers := [(0, 1), (42, 1), (48, 1)] }, { coefficient := 1, powers := [(37, 1)] }, { coefficient := 1, powers := [(42, 1)] }, { coefficient := 1, powers := [(48, 1)] }, { coefficient := 1, powers := [(52, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (35, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (38, 1), (53, 1)] }, { coefficient := 1, powers := [(2, 1), (44, 1), (50, 1)] }, { coefficient := 1, powers := [(5, 1), (26, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (53, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (50, 1)] }, { coefficient := 1, powers := [(8, 1), (21, 1), (56, 1)] }, { coefficient := 1, powers := [(8, 1), (29, 1), (44, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (38, 1)] }, { coefficient := 1, powers := [(12, 1), (21, 1), (53, 1)] }, { coefficient := 1, powers := [(12, 1), (26, 1), (44, 1)] }, { coefficient := 1, powers := [(12, 1), (32, 1), (35, 1)] }, { coefficient := 1, powers := [(16, 1), (21, 1), (50, 1)] }, { coefficient := 1, powers := [(16, 1), (26, 1), (38, 1)] }, { coefficient := 1, powers := [(16, 1), (29, 1), (35, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (57, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1), (58, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 49 → SparsePoly (Fin 59) := ![
  [{ coefficient := 2, powers := [(5, 2), (22, 1), (28, 1), (29, 1), (50, 1), (53, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(0, 2), (8, 1), (26, 1), (32, 1), (34, 1), (38, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 2), (8, 1), (29, 1), (32, 1), (34, 1), (38, 1), (53, 1)] }, { coefficient := 1, powers := [(0, 2), (8, 1), (32, 2), (34, 1), (38, 1), (50, 1)] }, { coefficient := -2, powers := [(0, 1), (5, 1), (26, 1), (29, 1), (33, 1), (53, 1), (56, 1), (57, 1)] }, { coefficient := -2, powers := [(0, 1), (5, 1), (29, 2), (33, 1), (53, 2), (57, 1)] }, { coefficient := -2, powers := [(0, 1), (5, 1), (29, 1), (32, 1), (33, 1), (50, 1), (53, 1), (57, 1)] }, { coefficient := -1, powers := [(0, 1), (6, 1), (8, 1), (26, 1), (32, 1), (38, 1), (48, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (6, 1), (8, 1), (26, 1), (32, 1), (38, 1), (52, 1), (56, 1)] }, { coefficient := -1, powers := [(0, 1), (6, 1), (8, 1), (29, 1), (32, 1), (38, 1), (48, 1), (53, 1)] }, { coefficient := 1, powers := [(0, 1), (6, 1), (8, 1), (29, 1), (32, 1), (38, 1), (52, 1), (53, 1)] }, { coefficient := -1, powers := [(0, 1), (6, 1), (8, 1), (32, 2), (38, 1), (48, 1), (50, 1)] }, { coefficient := 1, powers := [(0, 1), (6, 1), (8, 1), (32, 2), (38, 1), (50, 1), (52, 1)] }, { coefficient := -2, powers := [(3, 1), (5, 2), (22, 1), (26, 2), (29, 1), (48, 1), (53, 1), (56, 2)] }, { coefficient := -2, powers := [(3, 1), (5, 2), (22, 1), (26, 1), (29, 2), (48, 1), (53, 2), (56, 1)] }, { coefficient := -2, powers := [(3, 1), (5, 2), (22, 1), (26, 1), (29, 1), (32, 1), (48, 1), (50, 1), (53, 1), (56, 1)] }, { coefficient := 2, powers := [(3, 1), (5, 1), (22, 1), (26, 1), (29, 1), (42, 1), (53, 1), (56, 1)] }, { coefficient := 2, powers := [(3, 1), (5, 1), (22, 1), (26, 1), (29, 1), (48, 1), (53, 1), (56, 1)] }, { coefficient := -2, powers := [(3, 1), (5, 1), (22, 1), (26, 1), (29, 1), (53, 1), (56, 1), (57, 1)] }, { coefficient := -2, powers := [(3, 1), (5, 1), (22, 1), (29, 2), (53, 2), (57, 1)] }, { coefficient := -2, powers := [(3, 1), (5, 1), (22, 1), (29, 1), (32, 1), (50, 1), (53, 1), (57, 1)] }, { coefficient := -2, powers := [(3, 1), (26, 1), (56, 1)] }, { coefficient := -2, powers := [(5, 1), (6, 1), (17, 1), (26, 1), (29, 1), (53, 1), (56, 1), (57, 1)] }, { coefficient := -2, powers := [(5, 1), (6, 1), (17, 1), (29, 2), (53, 2), (57, 1)] }, { coefficient := -2, powers := [(5, 1), (6, 1), (17, 1), (29, 1), (32, 1), (50, 1), (53, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(0, 2), (8, 1), (21, 1), (32, 1), (34, 1), (38, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 2), (8, 1), (29, 1), (32, 1), (34, 1), (38, 1), (44, 1)] }, { coefficient := 1, powers := [(0, 2), (8, 1), (32, 2), (34, 1), (38, 2)] }, { coefficient := -2, powers := [(0, 1), (5, 1), (21, 1), (29, 1), (33, 1), (53, 1), (56, 1), (57, 1)] }, { coefficient := -2, powers := [(0, 1), (5, 1), (29, 2), (33, 1), (44, 1), (53, 1), (57, 1)] }, { coefficient := -2, powers := [(0, 1), (5, 1), (29, 1), (32, 1), (33, 1), (38, 1), (53, 1), (57, 1)] }, { coefficient := -1, powers := [(0, 1), (6, 1), (8, 1), (21, 1), (32, 1), (38, 1), (48, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (6, 1), (8, 1), (21, 1), (32, 1), (38, 1), (52, 1), (56, 1)] }, { coefficient := -1, powers := [(0, 1), (6, 1), (8, 1), (29, 1), (32, 1), (38, 1), (44, 1), (48, 1)] }, { coefficient := 1, powers := [(0, 1), (6, 1), (8, 1), (29, 1), (32, 1), (38, 1), (44, 1), (52, 1)] }, { coefficient := -1, powers := [(0, 1), (6, 1), (8, 1), (32, 2), (38, 2), (48, 1)] }, { coefficient := 1, powers := [(0, 1), (6, 1), (8, 1), (32, 2), (38, 2), (52, 1)] }, { coefficient := -2, powers := [(3, 1), (5, 2), (21, 1), (22, 1), (26, 1), (29, 1), (48, 1), (53, 1), (56, 2)] }, { coefficient := -4, powers := [(3, 1), (5, 2), (22, 1), (26, 1), (29, 2), (44, 1), (48, 1), (53, 1), (56, 1)] }, { coefficient := -2, powers := [(3, 1), (5, 1), (21, 1), (22, 1), (29, 1), (53, 1), (56, 1), (57, 1)] }, { coefficient := -2, powers := [(3, 1), (5, 1), (22, 1), (29, 2), (44, 1), (53, 1), (57, 1)] }, { coefficient := -2, powers := [(3, 1), (5, 1), (22, 1), (29, 1), (32, 1), (38, 1), (53, 1), (57, 1)] }, { coefficient := -2, powers := [(5, 2), (6, 1), (21, 1), (22, 1), (29, 2), (48, 1), (53, 2), (56, 1)] }, { coefficient := 2, powers := [(5, 2), (6, 1), (21, 1), (22, 1), (29, 1), (32, 1), (48, 1), (50, 1), (53, 1), (56, 1)] }, { coefficient := -2, powers := [(5, 1), (6, 1), (17, 1), (21, 1), (29, 1), (53, 1), (56, 1), (57, 1)] }, { coefficient := -2, powers := [(5, 1), (6, 1), (17, 1), (29, 2), (44, 1), (53, 1), (57, 1)] }, { coefficient := -2, powers := [(5, 1), (6, 1), (17, 1), (29, 1), (32, 1), (38, 1), (53, 1), (57, 1)] }, { coefficient := -2, powers := [(5, 1), (6, 1), (21, 1), (22, 1), (29, 1), (37, 1), (53, 1), (56, 1)] }, { coefficient := -2, powers := [(6, 1), (21, 1), (56, 1)] }],
  [{ coefficient := 2, powers := [(5, 2), (22, 1), (25, 1), (29, 1), (53, 1), (56, 1), (58, 1)] }],
  [{ coefficient := 2, powers := [(5, 1), (22, 1), (23, 1), (24, 1), (29, 1), (42, 1), (57, 1), (58, 1)] }, { coefficient := -2, powers := [(5, 1), (23, 1), (24, 1), (29, 1), (57, 1), (58, 1)] }],
  [{ coefficient := -2, powers := [(5, 1), (22, 1), (23, 1), (24, 1), (29, 1), (57, 1), (58, 1)] }],
  [{ coefficient := -2, powers := [(5, 1), (8, 1), (22, 1), (24, 1), (29, 2), (48, 1), (53, 1), (58, 1)] }, { coefficient := -2, powers := [(5, 1), (8, 1), (22, 1), (24, 1), (29, 2), (52, 1), (53, 1), (58, 1)] }, { coefficient := -2, powers := [(8, 1), (24, 1), (29, 1), (58, 1)] }],
  [{ coefficient := 3, powers := [(0, 1), (8, 1), (18, 1), (19, 1), (32, 1), (37, 1), (52, 1), (58, 1)] }, { coefficient := 3, powers := [(0, 1), (8, 1), (18, 1), (19, 1), (32, 1), (42, 1), (52, 1), (58, 1)] }, { coefficient := 2, powers := [(0, 1), (8, 1), (18, 1), (19, 1), (32, 1), (52, 1), (57, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (8, 1), (18, 1), (19, 1), (32, 1), (37, 1), (58, 1)] }, { coefficient := 1, powers := [(0, 1), (8, 1), (18, 1), (19, 1), (32, 1), (42, 1), (58, 1)] }, { coefficient := 2, powers := [(0, 1), (8, 1), (18, 1), (19, 1), (32, 1), (57, 1), (58, 1)] }],
  [{ coefficient := -2, powers := [(5, 2), (19, 1), (22, 1), (29, 1), (32, 1), (52, 1), (53, 1), (58, 1)] }, { coefficient := -2, powers := [(5, 1), (19, 1), (32, 1), (58, 1)] }],
  [{ coefficient := -2, powers := [(5, 1), (22, 1), (26, 1), (29, 1), (48, 1), (49, 1), (53, 1)] }],
  [{ coefficient := -2, powers := [(5, 2), (10, 1), (22, 1), (29, 2), (53, 1), (58, 1)] }],
  [{ coefficient := -2, powers := [(5, 1), (22, 1), (23, 1), (29, 1), (42, 1), (57, 1), (58, 1)] }, { coefficient := 2, powers := [(5, 1), (23, 1), (29, 1), (57, 1), (58, 1)] }],
  [{ coefficient := 2, powers := [(5, 1), (22, 1), (23, 1), (29, 1), (57, 1), (58, 1)] }],
  [{ coefficient := 2, powers := [(5, 1), (8, 1), (22, 1), (29, 2), (48, 1), (53, 1), (58, 1)] }, { coefficient := 2, powers := [(5, 1), (8, 1), (22, 1), (29, 2), (52, 1), (53, 1), (58, 1)] }, { coefficient := 2, powers := [(8, 1), (29, 1), (58, 1)] }],
  [{ coefficient := -3, powers := [(0, 1), (8, 1), (18, 1), (32, 1), (37, 1), (52, 1), (58, 1)] }, { coefficient := -3, powers := [(0, 1), (8, 1), (18, 1), (32, 1), (42, 1), (52, 1), (58, 1)] }, { coefficient := -2, powers := [(0, 1), (8, 1), (18, 1), (32, 1), (52, 1), (57, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (8, 1), (18, 1), (32, 1), (37, 1), (58, 1)] }, { coefficient := -1, powers := [(0, 1), (8, 1), (18, 1), (32, 1), (42, 1), (58, 1)] }, { coefficient := -2, powers := [(0, 1), (8, 1), (18, 1), (32, 1), (57, 1), (58, 1)] }],
  [{ coefficient := 2, powers := [(5, 2), (22, 1), (29, 1), (32, 1), (52, 1), (53, 1), (58, 1)] }, { coefficient := 2, powers := [(5, 1), (32, 1), (58, 1)] }],
  [{ coefficient := 2, powers := [(5, 2), (22, 1), (26, 1), (28, 1), (29, 1), (53, 1), (58, 1)] }],
  [{ coefficient := 2, powers := [(5, 1), (22, 1), (26, 1), (29, 1), (44, 1), (53, 1)] }],
  [{ coefficient := -2, powers := [(5, 1), (21, 1), (22, 1), (29, 1), (50, 1), (53, 1)] }, { coefficient := -2, powers := [(5, 1), (22, 1), (26, 1), (29, 1), (38, 1), (53, 1)] }],
  [{ coefficient := -2, powers := [(5, 1), (29, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (8, 1), (32, 1), (37, 1), (48, 1)] }, { coefficient := 1, powers := [(0, 1), (8, 1), (32, 1), (37, 1), (52, 1)] }, { coefficient := -1, powers := [(0, 1), (8, 1), (32, 1), (42, 1), (48, 1)] }, { coefficient := 1, powers := [(0, 1), (8, 1), (32, 1), (42, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (8, 1), (32, 1), (37, 1), (46, 1)] }, { coefficient := 1, powers := [(0, 1), (8, 1), (32, 1), (42, 1), (46, 1)] }],
  [{ coefficient := 2, powers := [(5, 1), (16, 1), (22, 1), (29, 1), (50, 1), (53, 1)] }],
  [{ coefficient := 2, powers := [(5, 1), (22, 1), (29, 1), (40, 1), (57, 1)] }],
  [{ coefficient := 2, powers := [(5, 2), (22, 1), (29, 1), (53, 1), (56, 1)] }, { coefficient := -2, powers := [(5, 1), (12, 1), (22, 1), (29, 1), (44, 1), (53, 1)] }],
  [{ coefficient := 2, powers := [(5, 3), (22, 1), (26, 1), (29, 1), (48, 1), (53, 1), (56, 2)] }, { coefficient := 2, powers := [(5, 3), (22, 1), (29, 2), (48, 1), (53, 2), (56, 1)] }, { coefficient := 2, powers := [(5, 3), (22, 1), (29, 1), (32, 1), (48, 1), (50, 1), (53, 1), (56, 1)] }, { coefficient := 2, powers := [(5, 2), (8, 1), (21, 1), (22, 1), (29, 1), (48, 1), (53, 1), (56, 2)] }, { coefficient := 4, powers := [(5, 2), (8, 1), (22, 1), (29, 2), (44, 1), (48, 1), (53, 1), (56, 1)] }, { coefficient := -2, powers := [(5, 2), (22, 1), (29, 1), (42, 1), (53, 1), (56, 1)] }, { coefficient := -2, powers := [(5, 2), (22, 1), (29, 1), (48, 1), (53, 1), (56, 1)] }, { coefficient := 2, powers := [(5, 1), (56, 1)] }],
  [{ coefficient := 2, powers := [(5, 2), (8, 1), (22, 1), (29, 2), (48, 1), (53, 2), (56, 1)] }, { coefficient := -2, powers := [(5, 2), (8, 1), (22, 1), (29, 1), (32, 1), (48, 1), (50, 1), (53, 1), (56, 1)] }, { coefficient := 2, powers := [(5, 1), (8, 1), (22, 1), (29, 1), (37, 1), (53, 1), (56, 1)] }, { coefficient := 2, powers := [(8, 1), (56, 1)] }],
  [{ coefficient := 2, powers := [(5, 1), (22, 1), (29, 1), (37, 1), (50, 1), (53, 1)] }, { coefficient := -2, powers := [(5, 1), (22, 1), (29, 1), (50, 1), (52, 1), (53, 1)] }],
  [{ coefficient := 2, powers := [(5, 1), (22, 1), (29, 1), (37, 1), (44, 1), (53, 1)] }, { coefficient := -2, powers := [(5, 1), (22, 1), (29, 1), (44, 1), (48, 1), (53, 1)] }, { coefficient := -2, powers := [(5, 1), (22, 1), (29, 1), (44, 1), (52, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(0, 2), (8, 1), (16, 1), (32, 1), (34, 1), (38, 1), (55, 1)] }, { coefficient := -2, powers := [(0, 1), (5, 1), (16, 1), (29, 1), (33, 1), (53, 1), (55, 1), (57, 1)] }, { coefficient := -1, powers := [(0, 1), (6, 1), (8, 1), (16, 1), (32, 1), (38, 1), (48, 1), (55, 1)] }, { coefficient := 1, powers := [(0, 1), (6, 1), (8, 1), (16, 1), (32, 1), (38, 1), (52, 1), (55, 1)] }, { coefficient := -2, powers := [(3, 1), (5, 1), (16, 1), (22, 1), (29, 1), (53, 1), (55, 1), (57, 1)] }, { coefficient := 2, powers := [(5, 2), (8, 1), (22, 1), (29, 1), (32, 1), (48, 1), (53, 1), (56, 1)] }, { coefficient := 2, powers := [(5, 2), (16, 1), (22, 1), (26, 1), (29, 1), (48, 1), (53, 1), (56, 1)] }, { coefficient := -2, powers := [(5, 1), (6, 1), (16, 1), (17, 1), (29, 1), (53, 1), (55, 1), (57, 1)] }, { coefficient := 2, powers := [(5, 1), (16, 1), (22, 1), (29, 1), (37, 1), (53, 1)] }, { coefficient := 2, powers := [(16, 1)] }],
  [{ coefficient := 1, powers := [(0, 2), (8, 1), (12, 1), (32, 1), (34, 1), (38, 1), (55, 1)] }, { coefficient := -2, powers := [(0, 1), (5, 1), (12, 1), (29, 1), (33, 1), (53, 1), (55, 1), (57, 1)] }, { coefficient := -1, powers := [(0, 1), (6, 1), (8, 1), (12, 1), (32, 1), (38, 1), (48, 1), (55, 1)] }, { coefficient := 1, powers := [(0, 1), (6, 1), (8, 1), (12, 1), (32, 1), (38, 1), (52, 1), (55, 1)] }, { coefficient := -2, powers := [(3, 1), (5, 1), (12, 1), (22, 1), (29, 1), (53, 1), (55, 1), (57, 1)] }, { coefficient := -2, powers := [(5, 2), (8, 1), (22, 1), (29, 2), (48, 1), (53, 1), (56, 1)] }, { coefficient := 2, powers := [(5, 2), (12, 1), (22, 1), (26, 1), (29, 1), (48, 1), (53, 1), (56, 1)] }, { coefficient := -2, powers := [(5, 1), (6, 1), (12, 1), (17, 1), (29, 1), (53, 1), (55, 1), (57, 1)] }, { coefficient := 2, powers := [(5, 1), (12, 1), (22, 1), (29, 1), (37, 1), (53, 1)] }, { coefficient := 2, powers := [(12, 1)] }],
  [{ coefficient := 2, powers := [(5, 2), (22, 1), (29, 2), (53, 1), (58, 1)] }],
  [{ coefficient := 2, powers := [(5, 1), (22, 1), (29, 1), (38, 1), (53, 1)] }],
  [{ coefficient := -2, powers := [(5, 2), (19, 1), (22, 1), (29, 1), (53, 1), (56, 1), (58, 1)] }],
  [{ coefficient := -2, powers := [(5, 2), (22, 1), (28, 1), (29, 1), (53, 1), (58, 1)] }],
  [{ coefficient := 2, powers := [(5, 1), (22, 1), (26, 1), (29, 1), (48, 1), (53, 1)] }],
  [{ coefficient := -2, powers := [(5, 1), (22, 1), (29, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (8, 1), (32, 1), (37, 1)] }, { coefficient := 1, powers := [(0, 1), (8, 1), (32, 1), (42, 1)] }, { coefficient := 2, powers := [(0, 1), (8, 1), (32, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (8, 1), (32, 1), (38, 1), (48, 1)] }, { coefficient := -1, powers := [(0, 1), (8, 1), (32, 1), (38, 1), (52, 1)] }],
  [{ coefficient := -2, powers := [(5, 2), (22, 1), (26, 1), (29, 1), (53, 1), (56, 1), (58, 1)] }],
  [{ coefficient := 2, powers := [(5, 2), (19, 1), (22, 1), (26, 1), (29, 1), (53, 1), (56, 1), (58, 1)] }],
  [{ coefficient := 2, powers := [(5, 1), (29, 1), (53, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (8, 1), (32, 1), (38, 1)] }],
  [{ coefficient := -1, powers := [(0, 2), (8, 1), (32, 1), (34, 1), (38, 1), (55, 1)] }, { coefficient := 2, powers := [(0, 1), (5, 1), (29, 1), (33, 1), (53, 1), (55, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (6, 1), (8, 1), (32, 1), (38, 1), (48, 1), (55, 1)] }, { coefficient := -1, powers := [(0, 1), (6, 1), (8, 1), (32, 1), (38, 1), (52, 1), (55, 1)] }, { coefficient := 2, powers := [(3, 1), (5, 1), (22, 1), (29, 1), (53, 1), (55, 1), (57, 1)] }, { coefficient := -2, powers := [(5, 2), (22, 1), (26, 1), (29, 1), (48, 1), (53, 1), (56, 1)] }, { coefficient := 2, powers := [(5, 1), (6, 1), (17, 1), (29, 1), (53, 1), (55, 1), (57, 1)] }, { coefficient := -2, powers := [(5, 1), (22, 1), (29, 1), (37, 1), (53, 1)] }, { coefficient := -2, powers := [] }],
  [{ coefficient := -2, powers := [(0, 1), (8, 1), (32, 1), (38, 1), (52, 1)] }, { coefficient := 2, powers := [(5, 1), (22, 1), (29, 1), (37, 1), (53, 1)] }, { coefficient := -2, powers := [(5, 1), (29, 1), (53, 1)] }, { coefficient := -2, powers := [(8, 1), (32, 1), (38, 1)] }],
  [{ coefficient := 3, powers := [(0, 1), (8, 1), (18, 1), (32, 1), (37, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(0, 1), (8, 1), (18, 1), (32, 1), (37, 1), (49, 1)] }, { coefficient := 3, powers := [(0, 1), (8, 1), (18, 1), (32, 1), (42, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(0, 1), (8, 1), (18, 1), (32, 1), (42, 1), (49, 1)] }, { coefficient := 2, powers := [(0, 1), (8, 1), (18, 1), (32, 1), (46, 1), (52, 1), (57, 1)] }, { coefficient := 2, powers := [(0, 1), (8, 1), (18, 1), (32, 1), (49, 1), (57, 1)] }, { coefficient := 2, powers := [(5, 2), (22, 1), (26, 1), (29, 1), (48, 1), (53, 1), (56, 1)] }, { coefficient := -2, powers := [(5, 2), (22, 1), (29, 2), (37, 1), (53, 2)] }, { coefficient := -2, powers := [(5, 2), (22, 1), (29, 1), (32, 1), (50, 1), (52, 1), (53, 1)] }, { coefficient := -2, powers := [(5, 1), (8, 1), (22, 1), (29, 2), (44, 1), (48, 1), (53, 1)] }, { coefficient := -2, powers := [(5, 1), (8, 1), (22, 1), (29, 2), (44, 1), (52, 1), (53, 1)] }, { coefficient := 2, powers := [(5, 1), (22, 1), (23, 1), (29, 1), (40, 1), (42, 1), (57, 1)] }, { coefficient := -2, powers := [(5, 1), (22, 1), (23, 1), (29, 1), (43, 1), (57, 1)] }, { coefficient := -2, powers := [(5, 1), (23, 1), (29, 1), (40, 1), (57, 1)] }, { coefficient := -2, powers := [(5, 1), (32, 1), (50, 1)] }, { coefficient := -2, powers := [(8, 1), (29, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(0, 2), (8, 1), (32, 1), (34, 1), (35, 1), (38, 1), (55, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 2), (8, 1), (32, 1), (34, 1), (38, 2), (53, 1), (55, 1)] }, { coefficient := 1, powers := [(0, 2), (8, 1), (32, 1), (34, 1), (38, 1), (44, 1), (50, 1), (55, 1)] }, { coefficient := -2, powers := [(0, 1), (5, 1), (29, 1), (33, 1), (35, 1), (53, 1), (55, 1), (56, 1), (57, 1)] }, { coefficient := -2, powers := [(0, 1), (5, 1), (29, 1), (33, 1), (38, 1), (53, 2), (55, 1), (57, 1)] }, { coefficient := -2, powers := [(0, 1), (5, 1), (29, 1), (33, 1), (44, 1), (50, 1), (53, 1), (55, 1), (57, 1)] }, { coefficient := -1, powers := [(0, 1), (6, 1), (8, 1), (32, 1), (35, 1), (38, 1), (48, 1), (55, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (6, 1), (8, 1), (32, 1), (35, 1), (38, 1), (52, 1), (55, 1), (56, 1)] }, { coefficient := -1, powers := [(0, 1), (6, 1), (8, 1), (32, 1), (38, 2), (48, 1), (53, 1), (55, 1)] }, { coefficient := 1, powers := [(0, 1), (6, 1), (8, 1), (32, 1), (38, 2), (52, 1), (53, 1), (55, 1)] }, { coefficient := -1, powers := [(0, 1), (6, 1), (8, 1), (32, 1), (38, 1), (44, 1), (48, 1), (50, 1), (55, 1)] }, { coefficient := 1, powers := [(0, 1), (6, 1), (8, 1), (32, 1), (38, 1), (44, 1), (50, 1), (52, 1), (55, 1)] }, { coefficient := -2, powers := [(3, 1), (5, 1), (22, 1), (29, 1), (35, 1), (53, 1), (55, 1), (56, 1), (57, 1)] }, { coefficient := -2, powers := [(3, 1), (5, 1), (22, 1), (29, 1), (38, 1), (53, 2), (55, 1), (57, 1)] }, { coefficient := -2, powers := [(3, 1), (5, 1), (22, 1), (29, 1), (44, 1), (50, 1), (53, 1), (55, 1), (57, 1)] }, { coefficient := 2, powers := [(5, 2), (22, 1), (26, 1), (29, 1), (35, 1), (48, 1), (53, 1), (56, 2)] }, { coefficient := 2, powers := [(5, 2), (22, 1), (26, 1), (29, 1), (38, 1), (48, 1), (53, 2), (56, 1)] }, { coefficient := 2, powers := [(5, 2), (22, 1), (26, 1), (29, 1), (44, 1), (48, 1), (50, 1), (53, 1), (56, 1)] }, { coefficient := -2, powers := [(5, 1), (6, 1), (17, 1), (29, 1), (35, 1), (53, 1), (55, 1), (56, 1), (57, 1)] }, { coefficient := -2, powers := [(5, 1), (6, 1), (17, 1), (29, 1), (38, 1), (53, 2), (55, 1), (57, 1)] }, { coefficient := -2, powers := [(5, 1), (6, 1), (17, 1), (29, 1), (44, 1), (50, 1), (53, 1), (55, 1), (57, 1)] }, { coefficient := 2, powers := [(5, 1), (22, 1), (29, 1), (35, 1), (37, 1), (53, 1), (56, 1)] }, { coefficient := -2, powers := [(5, 1), (22, 1), (29, 1), (37, 1), (44, 1), (50, 1), (53, 1)] }, { coefficient := 2, powers := [(5, 1), (22, 1), (29, 1), (44, 1), (48, 1), (50, 1), (53, 1)] }, { coefficient := 4, powers := [(5, 1), (22, 1), (29, 1), (44, 1), (50, 1), (52, 1), (53, 1)] }, { coefficient := 2, powers := [(35, 1), (56, 1)] }, { coefficient := 2, powers := [(38, 1), (53, 1)] }, { coefficient := 2, powers := [(44, 1), (50, 1)] }]
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
    (values : Fin 59 → R) :
    ¬ ∀ index : Fin 49,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((2 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (2 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (2 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component56.SelectedLeafB6.selectedHasNoCommonZero

end Krenn.Component56.SelectedLeafB6
