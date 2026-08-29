import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component56.SelectedLeafB4

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "b3d4147437af753af30fbfb12afc98f03dcbb36b557454a2a8a9b413b79a45c8"
def certificateSHA256 : String := "8cf6246e1faa85722a9f05866631a421207c662b86678bf0c1e8e7e4d8294caa"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 75 → Fin 589 := ![
  8,
  9,
  10,
  11,
  13,
  16,
  17,
  19,
  20,
  22,
  25,
  26,
  28,
  29,
  31,
  32,
  35,
  37,
  38,
  40,
  42,
  43,
  79,
  99,
  214,
  226,
  234,
  235,
  241,
  243,
  263,
  264,
  274,
  276,
  292,
  302,
  303,
  322,
  359,
  360,
  361,
  362,
  365,
  366,
  372,
  373,
  377,
  398,
  399,
  416,
  417,
  418,
  421,
  422,
  429,
  430,
  433,
  446,
  467,
  468,
  478,
  484,
  496,
  508,
  527,
  528,
  547,
  548,
  558,
  565,
  584,
  585,
  586,
  587,
  588
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 75 → SparsePoly (Fin 58) := ![
  [{ coefficient := 1, powers := [(4, 1), (32, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (29, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (26, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (22, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (23, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (21, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (17, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (18, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(26, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (34, 1)] }],
  [{ coefficient := 1, powers := [(32, 1), (34, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (32, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (29, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (56, 1)] }, { coefficient := 1, powers := [(7, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (42, 1)] }, { coefficient := 1, powers := [(12, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (37, 1)] }, { coefficient := 1, powers := [(16, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (53, 1)] }, { coefficient := 1, powers := [(23, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (48, 1)] }, { coefficient := 1, powers := [(21, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(26, 1), (37, 1)] }, { coefficient := 1, powers := [(26, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (26, 1), (55, 1)] }, { coefficient := 1, powers := [(26, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (28, 1), (53, 1)] }, { coefficient := 1, powers := [(19, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (21, 1), (55, 1)] }, { coefficient := 1, powers := [(21, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (31, 1), (38, 1)] }, { coefficient := 1, powers := [(24, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (23, 1), (43, 1)] }, { coefficient := 1, powers := [(10, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (17, 1), (52, 1)] }, { coefficient := 1, powers := [(12, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (19, 1), (52, 1)] }, { coefficient := 1, powers := [(12, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (18, 1), (49, 1)] }, { coefficient := 1, powers := [(14, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (40, 1)] }, { coefficient := 1, powers := [(17, 1), (40, 1)] }, { coefficient := 1, powers := [(22, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1)] }, { coefficient := 1, powers := [(18, 1), (40, 1)] }, { coefficient := 1, powers := [(22, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1)] }, { coefficient := 1, powers := [(17, 1), (46, 1)] }, { coefficient := 1, powers := [(22, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (50, 1)] }, { coefficient := 1, powers := [(17, 1), (50, 1)] }, { coefficient := 1, powers := [(23, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (44, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1)] }, { coefficient := 1, powers := [(16, 1), (21, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (50, 1)] }, { coefficient := 1, powers := [(8, 1), (29, 1)] }, { coefficient := 1, powers := [(12, 1), (26, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (50, 1)] }, { coefficient := 1, powers := [(26, 1), (38, 1)] }, { coefficient := 1, powers := [(29, 1), (35, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (53, 1)] }, { coefficient := 1, powers := [(26, 1), (44, 1)] }, { coefficient := 1, powers := [(32, 1), (35, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1), (50, 1)] }, { coefficient := 1, powers := [(23, 1), (42, 1), (46, 1)] }, { coefficient := 1, powers := [(50, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (37, 1), (53, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (37, 1)] }, { coefficient := 1, powers := [(16, 1), (26, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (52, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (52, 1)] }, { coefficient := 1, powers := [(12, 1), (21, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (26, 1), (55, 1)] }, { coefficient := 1, powers := [(10, 1), (26, 1), (42, 1)] }, { coefficient := 1, powers := [(14, 1), (26, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (26, 1), (56, 1)] }, { coefficient := 1, powers := [(4, 1), (29, 1), (53, 1)] }, { coefficient := 1, powers := [(4, 1), (32, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (29, 1), (52, 1)] }, { coefficient := 1, powers := [(7, 1), (29, 1), (42, 1)] }, { coefficient := 1, powers := [(14, 1), (29, 1), (34, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (25, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (28, 1), (52, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (25, 1), (56, 1)] }, { coefficient := 1, powers := [(12, 1), (25, 1), (44, 1)] }, { coefficient := 1, powers := [(16, 1), (25, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (21, 1), (55, 1)] }, { coefficient := 1, powers := [(10, 1), (21, 1), (52, 1)] }, { coefficient := 1, powers := [(14, 1), (21, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (21, 1), (56, 1)] }, { coefficient := 1, powers := [(7, 1), (29, 1), (44, 1)] }, { coefficient := 1, powers := [(7, 1), (32, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (20, 1), (56, 1)] }, { coefficient := 1, powers := [(12, 1), (20, 1), (53, 1)] }, { coefficient := 1, powers := [(16, 1), (20, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (20, 1), (52, 1)] }, { coefficient := 1, powers := [(12, 1), (25, 1), (42, 1)] }, { coefficient := 1, powers := [(12, 1), (31, 1), (34, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (56, 1)] }, { coefficient := 1, powers := [(12, 1), (44, 1)] }, { coefficient := 1, powers := [(16, 1), (18, 1), (49, 1)] }, { coefficient := 1, powers := [(16, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (56, 1)] }, { coefficient := 1, powers := [(12, 1), (23, 1), (43, 1)] }, { coefficient := 1, powers := [(12, 1), (53, 1)] }, { coefficient := 1, powers := [(16, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (40, 1), (49, 1)] }, { coefficient := 1, powers := [(3, 1), (56, 1)] }, { coefficient := 1, powers := [(17, 1), (40, 1), (49, 1)] }, { coefficient := 1, powers := [(40, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1), (46, 1)] }, { coefficient := 1, powers := [(6, 1), (56, 1)] }, { coefficient := 1, powers := [(22, 1), (43, 1), (46, 1)] }, { coefficient := 1, powers := [(40, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (26, 1), (56, 1)] }, { coefficient := 1, powers := [(3, 1), (29, 1), (53, 1)] }, { coefficient := 1, powers := [(3, 1), (32, 1), (50, 1)] }, { coefficient := 1, powers := [(26, 1), (40, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (21, 1), (56, 1)] }, { coefficient := 1, powers := [(6, 1), (29, 1), (44, 1)] }, { coefficient := 1, powers := [(6, 1), (32, 1), (38, 1)] }, { coefficient := 1, powers := [(21, 1), (40, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1)] }, { coefficient := 1, powers := [(6, 1), (55, 1)] }, { coefficient := 1, powers := [(22, 1), (37, 1)] }, { coefficient := 1, powers := [(22, 1), (42, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (48, 1)] }, { coefficient := 1, powers := [(3, 1), (55, 1)] }, { coefficient := 1, powers := [(17, 1), (48, 1)] }, { coefficient := 1, powers := [(17, 1), (52, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(4, 1), (55, 1)] }, { coefficient := 1, powers := [(7, 1), (55, 1)] }, { coefficient := 1, powers := [(10, 1), (42, 1)] }, { coefficient := 1, powers := [(10, 1), (52, 1)] }, { coefficient := 1, powers := [(14, 1), (37, 1)] }, { coefficient := 1, powers := [(14, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (48, 1)] }, { coefficient := 1, powers := [(20, 1), (52, 1)] }, { coefficient := 1, powers := [(25, 1), (37, 1)] }, { coefficient := 1, powers := [(25, 1), (42, 1)] }, { coefficient := 1, powers := [(28, 1), (34, 1)] }, { coefficient := 1, powers := [(31, 1), (34, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (25, 1), (55, 1)] }, { coefficient := 1, powers := [(3, 1), (28, 1), (52, 1)] }, { coefficient := 1, powers := [(3, 1), (31, 1), (48, 1)] }, { coefficient := 1, powers := [(19, 1), (48, 1)] }, { coefficient := 1, powers := [(19, 1), (52, 1)] }, { coefficient := 1, powers := [(25, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (20, 1), (55, 1)] }, { coefficient := 1, powers := [(6, 1), (28, 1), (42, 1)] }, { coefficient := 1, powers := [(6, 1), (31, 1), (37, 1)] }, { coefficient := 1, powers := [(20, 1)] }, { coefficient := 1, powers := [(24, 1), (37, 1)] }, { coefficient := 1, powers := [(24, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (34, 1), (55, 1)] }, { coefficient := 1, powers := [(1, 1), (37, 1), (52, 1)] }, { coefficient := 1, powers := [(1, 1), (42, 1), (48, 1)] }, { coefficient := 1, powers := [(4, 1), (25, 1), (55, 1)] }, { coefficient := 1, powers := [(4, 1), (28, 1), (52, 1)] }, { coefficient := 1, powers := [(4, 1), (31, 1), (48, 1)] }, { coefficient := 1, powers := [(7, 1), (20, 1), (55, 1)] }, { coefficient := 1, powers := [(7, 1), (28, 1), (42, 1)] }, { coefficient := 1, powers := [(7, 1), (31, 1), (37, 1)] }, { coefficient := 1, powers := [(10, 1), (20, 1), (52, 1)] }, { coefficient := 1, powers := [(10, 1), (25, 1), (42, 1)] }, { coefficient := 1, powers := [(10, 1), (31, 1), (34, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1), (48, 1)] }, { coefficient := 1, powers := [(14, 1), (25, 1), (37, 1)] }, { coefficient := 1, powers := [(14, 1), (28, 1), (34, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (35, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (38, 1), (53, 1)] }, { coefficient := 1, powers := [(2, 1), (44, 1), (50, 1)] }, { coefficient := 1, powers := [(5, 1), (26, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (53, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (50, 1)] }, { coefficient := 1, powers := [(8, 1), (21, 1), (56, 1)] }, { coefficient := 1, powers := [(8, 1), (29, 1), (44, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (38, 1)] }, { coefficient := 1, powers := [(12, 1), (21, 1), (53, 1)] }, { coefficient := 1, powers := [(12, 1), (26, 1), (44, 1)] }, { coefficient := 1, powers := [(12, 1), (32, 1), (35, 1)] }, { coefficient := 1, powers := [(16, 1), (21, 1), (50, 1)] }, { coefficient := 1, powers := [(16, 1), (26, 1), (38, 1)] }, { coefficient := 1, powers := [(16, 1), (29, 1), (35, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (57, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1)] }],
  [{ coefficient := 1, powers := [(2, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 75 → SparsePoly (Fin 58) := ![
  [{ coefficient := 1, powers := [(8, 1), (28, 1), (38, 1), (52, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1), (38, 1), (48, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (7, 1), (26, 1), (28, 1), (42, 1), (56, 1)] }, { coefficient := -1, powers := [(3, 1), (7, 1), (26, 1), (31, 1), (37, 1), (56, 1)] }, { coefficient := -1, powers := [(3, 1), (10, 1), (20, 1), (26, 1), (52, 1), (56, 1)] }, { coefficient := -1, powers := [(3, 1), (10, 1), (26, 1), (31, 1), (34, 1), (56, 1)] }, { coefficient := -1, powers := [(3, 1), (12, 1), (14, 1), (21, 1), (25, 1), (26, 1), (42, 1), (53, 1), (56, 1)] }, { coefficient := -1, powers := [(3, 1), (12, 1), (14, 1), (21, 1), (25, 1), (29, 1), (42, 1), (53, 2)] }, { coefficient := -1, powers := [(3, 1), (12, 1), (14, 1), (21, 1), (25, 1), (32, 1), (42, 1), (50, 1), (53, 1)] }, { coefficient := -1, powers := [(3, 1), (14, 1), (20, 1), (26, 1), (42, 1), (56, 1)] }, { coefficient := -1, powers := [(3, 1), (14, 1), (20, 1), (26, 1), (48, 1), (56, 1)] }, { coefficient := 1, powers := [(3, 1), (14, 1), (20, 1), (26, 1), (52, 1), (56, 1)] }, { coefficient := 1, powers := [(3, 1), (14, 1), (25, 1), (26, 1), (48, 1), (56, 1)] }, { coefficient := 1, powers := [(3, 1), (14, 1), (26, 1), (31, 1), (34, 1), (56, 1)] }, { coefficient := -1, powers := [(4, 1), (20, 1), (26, 1), (56, 1)] }, { coefficient := -1, powers := [(4, 1), (20, 1), (29, 1), (53, 1)] }, { coefficient := 1, powers := [(4, 1), (25, 1), (26, 1), (56, 1)] }, { coefficient := 1, powers := [(4, 1), (25, 1), (29, 1), (53, 1)] }, { coefficient := -1, powers := [(6, 1), (8, 1), (10, 1), (20, 1), (26, 1), (32, 1), (38, 1), (52, 1), (56, 1)] }, { coefficient := -1, powers := [(6, 1), (8, 1), (10, 1), (20, 1), (29, 1), (32, 1), (38, 1), (52, 1), (53, 1)] }, { coefficient := -1, powers := [(6, 1), (8, 1), (10, 1), (20, 1), (32, 2), (38, 1), (50, 1), (52, 1)] }, { coefficient := -1, powers := [(7, 1), (12, 1), (20, 1), (21, 1), (26, 1), (53, 1), (56, 1)] }, { coefficient := -1, powers := [(7, 1), (12, 1), (20, 1), (21, 1), (29, 1), (53, 2)] }, { coefficient := -1, powers := [(7, 1), (12, 1), (20, 1), (21, 1), (32, 1), (50, 1), (53, 1)] }, { coefficient := 1, powers := [(7, 1), (12, 1), (21, 1), (25, 1), (26, 1), (53, 1), (56, 1)] }, { coefficient := 1, powers := [(7, 1), (12, 1), (21, 1), (25, 1), (29, 1), (53, 2)] }, { coefficient := 1, powers := [(7, 1), (12, 1), (21, 1), (25, 1), (32, 1), (50, 1), (53, 1)] }, { coefficient := -1, powers := [(7, 1), (16, 1), (20, 1), (26, 2), (38, 1), (56, 1)] }, { coefficient := -1, powers := [(7, 1), (16, 1), (20, 1), (26, 1), (29, 1), (38, 1), (53, 1)] }, { coefficient := -1, powers := [(7, 1), (16, 1), (20, 1), (26, 1), (32, 1), (38, 1), (50, 1)] }, { coefficient := 1, powers := [(7, 1), (16, 1), (25, 1), (26, 2), (38, 1), (56, 1)] }, { coefficient := 1, powers := [(7, 1), (16, 1), (25, 1), (26, 1), (29, 1), (38, 1), (53, 1)] }, { coefficient := 1, powers := [(7, 1), (16, 1), (25, 1), (26, 1), (32, 1), (38, 1), (50, 1)] }, { coefficient := 1, powers := [(7, 1), (20, 1), (26, 1), (56, 1)] }, { coefficient := 1, powers := [(7, 1), (20, 1), (32, 1), (50, 1)] }, { coefficient := -1, powers := [(7, 1), (25, 1), (26, 1), (56, 1)] }, { coefficient := -1, powers := [(7, 1), (25, 1), (32, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (28, 1), (42, 1), (53, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (37, 1), (53, 1)] }, { coefficient := -1, powers := [(8, 1), (28, 1), (42, 1), (44, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (12, 1), (14, 1), (21, 2), (25, 1), (42, 1), (53, 1), (56, 1)] }, { coefficient := -1, powers := [(3, 1), (12, 1), (14, 1), (21, 1), (25, 1), (29, 1), (42, 1), (44, 1), (53, 1)] }, { coefficient := -1, powers := [(3, 1), (12, 1), (14, 1), (21, 1), (25, 1), (32, 1), (38, 1), (42, 1), (53, 1)] }, { coefficient := -1, powers := [(6, 1), (8, 1), (10, 1), (20, 1), (21, 1), (32, 1), (38, 1), (52, 1), (56, 1)] }, { coefficient := -1, powers := [(6, 1), (8, 1), (10, 1), (20, 1), (29, 1), (32, 1), (38, 1), (44, 1), (52, 1)] }, { coefficient := -1, powers := [(6, 1), (8, 1), (10, 1), (20, 1), (32, 2), (38, 2), (52, 1)] }, { coefficient := -1, powers := [(7, 1), (12, 1), (20, 1), (21, 2), (53, 1), (56, 1)] }, { coefficient := -1, powers := [(7, 1), (12, 1), (20, 1), (21, 1), (29, 1), (44, 1), (53, 1)] }, { coefficient := -1, powers := [(7, 1), (12, 1), (20, 1), (21, 1), (32, 1), (38, 1), (53, 1)] }, { coefficient := 1, powers := [(7, 1), (12, 1), (21, 2), (25, 1), (53, 1), (56, 1)] }, { coefficient := 1, powers := [(7, 1), (12, 1), (21, 1), (25, 1), (29, 1), (44, 1), (53, 1)] }, { coefficient := 1, powers := [(7, 1), (12, 1), (21, 1), (25, 1), (32, 1), (38, 1), (53, 1)] }, { coefficient := -1, powers := [(7, 1), (16, 1), (20, 1), (21, 1), (26, 1), (38, 1), (56, 1)] }, { coefficient := -1, powers := [(7, 1), (16, 1), (20, 1), (26, 1), (29, 1), (38, 1), (44, 1)] }, { coefficient := -1, powers := [(7, 1), (16, 1), (20, 1), (26, 1), (32, 1), (38, 2)] }, { coefficient := 1, powers := [(7, 1), (16, 1), (21, 1), (25, 1), (26, 1), (38, 1), (56, 1)] }, { coefficient := 1, powers := [(7, 1), (16, 1), (25, 1), (26, 1), (29, 1), (38, 1), (44, 1)] }, { coefficient := 1, powers := [(7, 1), (16, 1), (25, 1), (26, 1), (32, 1), (38, 2)] }, { coefficient := 1, powers := [(7, 1), (20, 1), (21, 1), (56, 1)] }, { coefficient := 1, powers := [(7, 1), (20, 1), (29, 1), (44, 1)] }, { coefficient := 1, powers := [(7, 1), (20, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [(7, 1), (21, 1), (25, 1), (56, 1)] }, { coefficient := -1, powers := [(7, 1), (25, 1), (29, 1), (44, 1)] }, { coefficient := -1, powers := [(7, 1), (25, 1), (32, 1), (38, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (20, 1), (42, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (25, 1), (42, 1), (56, 1)] }, { coefficient := -1, powers := [(12, 1), (20, 1), (42, 1), (44, 1)] }, { coefficient := -1, powers := [(12, 1), (20, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(12, 1), (25, 1), (42, 1), (44, 1)] }, { coefficient := 1, powers := [(12, 1), (25, 1), (44, 1), (52, 1)] }, { coefficient := -1, powers := [(16, 1), (20, 1), (38, 1), (52, 1)] }, { coefficient := 1, powers := [(16, 1), (25, 1), (38, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (20, 1), (23, 1), (29, 1), (42, 1)] }, { coefficient := -1, powers := [(5, 1), (23, 1), (25, 1), (29, 1), (42, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (20, 1), (29, 1), (42, 1)] }, { coefficient := -1, powers := [(8, 1), (20, 1), (29, 1), (52, 1)] }, { coefficient := 1, powers := [(8, 1), (25, 1), (29, 1), (42, 1)] }, { coefficient := 1, powers := [(8, 1), (25, 1), (29, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (26, 1), (31, 1), (44, 1), (48, 1), (57, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1), (26, 1), (44, 1), (48, 1), (57, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1), (26, 1), (44, 1), (52, 1), (57, 1)] }, { coefficient := 1, powers := [(14, 1), (21, 1), (25, 1), (37, 1), (42, 1), (53, 1)] }, { coefficient := 1, powers := [(14, 1), (21, 1), (25, 1), (42, 2), (53, 1)] }, { coefficient := -1, powers := [(14, 1), (25, 1), (26, 1), (44, 1), (48, 1), (57, 1)] }, { coefficient := -1, powers := [(14, 1), (25, 1), (26, 1), (44, 1), (52, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (21, 1), (28, 1), (40, 1), (52, 2)] }, { coefficient := 1, powers := [(7, 1), (21, 1), (28, 1), (43, 1), (52, 1)] }, { coefficient := 1, powers := [(7, 1), (21, 1), (31, 1), (40, 1), (48, 1), (52, 1)] }, { coefficient := 1, powers := [(7, 1), (21, 1), (31, 1), (43, 1), (48, 1)] }, { coefficient := 1, powers := [(10, 1), (21, 1), (25, 1), (40, 1), (52, 2)] }, { coefficient := 1, powers := [(10, 1), (21, 1), (25, 1), (43, 1), (52, 1)] }, { coefficient := -1, powers := [(10, 1), (21, 1), (31, 1), (34, 1), (40, 1), (52, 1)] }, { coefficient := -1, powers := [(10, 1), (21, 1), (31, 1), (34, 1), (43, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1), (21, 1), (37, 1), (40, 1), (52, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1), (21, 1), (37, 1), (43, 1)] }, { coefficient := 1, powers := [(14, 1), (21, 1), (25, 1), (40, 1), (42, 1), (52, 1)] }, { coefficient := 1, powers := [(14, 1), (21, 1), (25, 1), (42, 1), (43, 1)] }, { coefficient := 1, powers := [(14, 1), (21, 1), (31, 1), (34, 1), (40, 1), (52, 1)] }, { coefficient := 1, powers := [(14, 1), (21, 1), (31, 1), (34, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (20, 1), (37, 1), (56, 1)] }, { coefficient := 1, powers := [(8, 1), (20, 1), (48, 1), (56, 1)] }, { coefficient := -1, powers := [(8, 1), (25, 1), (37, 1), (56, 1)] }, { coefficient := -1, powers := [(8, 1), (25, 1), (48, 1), (56, 1)] }, { coefficient := -1, powers := [(12, 1), (20, 1), (48, 1), (53, 1)] }, { coefficient := 1, powers := [(12, 1), (25, 1), (48, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (18, 1), (20, 1), (32, 1), (48, 1)] }, { coefficient := 1, powers := [(8, 1), (18, 1), (25, 1), (32, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (20, 1), (32, 1), (37, 1)] }, { coefficient := 1, powers := [(5, 1), (20, 1), (32, 1), (48, 1)] }, { coefficient := -1, powers := [(5, 1), (25, 1), (32, 1), (37, 1)] }, { coefficient := -1, powers := [(5, 1), (25, 1), (32, 1), (48, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (21, 1), (28, 1), (42, 2), (50, 1)] }, { coefficient := 1, powers := [(7, 1), (21, 1), (28, 1), (42, 1), (50, 1), (52, 1)] }, { coefficient := -1, powers := [(7, 1), (21, 1), (31, 1), (37, 1), (42, 1), (50, 1)] }, { coefficient := 1, powers := [(7, 1), (21, 1), (31, 1), (42, 1), (48, 1), (50, 1)] }, { coefficient := 2, powers := [(10, 1), (21, 1), (25, 1), (42, 1), (50, 1), (52, 1)] }, { coefficient := -1, powers := [(10, 1), (21, 1), (31, 1), (34, 1), (42, 1), (50, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1), (21, 1), (37, 1), (42, 1), (50, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1), (21, 1), (42, 1), (50, 1), (52, 1)] }, { coefficient := 2, powers := [(14, 1), (21, 1), (25, 1), (42, 2), (50, 1)] }, { coefficient := 1, powers := [(14, 1), (21, 1), (31, 1), (34, 1), (42, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (20, 1), (26, 1), (48, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (10, 1), (32, 1), (52, 1)] }, { coefficient := -1, powers := [(5, 1), (14, 1), (32, 1), (48, 1)] }, { coefficient := -1, powers := [(5, 1), (14, 1), (32, 1), (52, 1)] }, { coefficient := -1, powers := [(10, 1), (16, 1), (21, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (10, 1), (29, 1), (52, 1)] }, { coefficient := -1, powers := [(5, 1), (14, 1), (29, 1), (37, 1)] }, { coefficient := -1, powers := [(5, 1), (14, 1), (29, 1), (48, 1)] }, { coefficient := -1, powers := [(5, 1), (14, 1), (29, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (10, 1), (17, 1), (28, 1), (42, 1), (43, 1), (52, 1)] }, { coefficient := -1, powers := [(8, 1), (10, 1), (17, 1), (31, 1), (42, 1), (43, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (10, 1), (32, 1), (52, 1)] }, { coefficient := 1, powers := [(8, 1), (14, 1), (32, 1), (37, 1)] }, { coefficient := 1, powers := [(10, 1), (16, 1), (26, 1), (52, 1)] }, { coefficient := 1, powers := [(14, 1), (16, 1), (26, 1), (42, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (10, 1), (29, 1), (52, 1)] }, { coefficient := 2, powers := [(8, 1), (14, 1), (29, 1), (37, 1)] }, { coefficient := 1, powers := [(8, 1), (14, 1), (29, 1), (42, 1)] }, { coefficient := 1, powers := [(12, 1), (14, 1), (26, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (12, 1), (18, 1), (31, 1), (48, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (14, 1), (22, 1), (28, 1), (42, 1), (48, 1), (49, 1)] }, { coefficient := 1, powers := [(12, 1), (14, 1), (18, 1), (20, 1), (48, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1), (14, 1), (18, 1), (20, 1), (52, 1), (57, 1)] }, { coefficient := -1, powers := [(12, 1), (14, 1), (18, 1), (25, 1), (48, 1), (57, 1)] }, { coefficient := -1, powers := [(12, 1), (14, 1), (18, 1), (25, 1), (52, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (10, 1), (31, 1), (53, 1)] }, { coefficient := -1, powers := [(5, 1), (14, 1), (31, 1), (53, 1)] }, { coefficient := 1, powers := [(8, 1), (10, 1), (31, 1), (44, 1)] }, { coefficient := 1, powers := [(8, 1), (14, 1), (28, 1), (44, 1)] }, { coefficient := 1, powers := [(8, 1), (14, 1), (31, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (10, 1), (31, 1), (50, 1)] }, { coefficient := -1, powers := [(5, 1), (14, 1), (31, 1), (50, 1)] }, { coefficient := 1, powers := [(8, 1), (10, 1), (31, 1), (38, 1)] }, { coefficient := 1, powers := [(8, 1), (14, 1), (28, 1), (38, 1)] }, { coefficient := -1, powers := [(10, 1), (12, 1), (31, 1), (35, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (14, 1), (28, 1), (42, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (10, 1), (28, 1), (44, 1), (52, 1)] }, { coefficient := -1, powers := [(8, 1), (10, 1), (31, 1), (44, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (21, 1), (28, 1), (52, 1)] }, { coefficient := 1, powers := [(8, 1), (21, 1), (31, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (14, 1), (21, 1), (25, 1), (42, 1), (53, 1)] }, { coefficient := -1, powers := [(10, 1), (25, 1), (32, 1), (35, 1)] }, { coefficient := -1, powers := [(14, 1), (25, 1), (26, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (20, 1), (21, 1), (50, 1)] }, { coefficient := 1, powers := [(14, 1), (25, 1), (26, 1), (38, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (12, 1), (21, 1), (28, 1), (52, 2)] }, { coefficient := -1, powers := [(7, 1), (12, 1), (21, 1), (31, 1), (48, 1), (52, 1)] }, { coefficient := -1, powers := [(10, 1), (12, 1), (21, 1), (25, 1), (52, 2)] }, { coefficient := 1, powers := [(10, 1), (12, 1), (21, 1), (31, 1), (34, 1), (52, 1)] }, { coefficient := -1, powers := [(12, 1), (14, 1), (20, 1), (21, 1), (37, 1), (52, 1)] }, { coefficient := -1, powers := [(12, 1), (14, 1), (21, 1), (25, 1), (42, 1), (52, 1)] }, { coefficient := -1, powers := [(12, 1), (14, 1), (21, 1), (31, 1), (34, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (12, 1), (14, 1), (25, 1), (42, 1), (53, 1)] }, { coefficient := -1, powers := [(8, 1), (14, 1), (20, 1), (56, 1)] }, { coefficient := -1, powers := [(12, 1), (14, 1), (17, 1), (25, 1), (42, 1), (53, 1)] }, { coefficient := -1, powers := [(14, 1), (16, 1), (20, 1), (50, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (14, 1), (20, 1), (56, 1)] }, { coefficient := 1, powers := [(12, 1), (14, 1), (25, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (7, 1), (28, 1), (42, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (7, 1), (31, 1), (37, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (10, 1), (20, 1), (52, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (10, 1), (31, 1), (34, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (14, 1), (20, 1), (42, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (14, 1), (20, 1), (48, 1), (56, 1)] }, { coefficient := -1, powers := [(5, 1), (14, 1), (20, 1), (52, 1), (56, 1)] }, { coefficient := -1, powers := [(5, 1), (14, 1), (25, 1), (48, 1), (56, 1)] }, { coefficient := -1, powers := [(5, 1), (14, 1), (31, 1), (34, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (14, 1), (29, 1), (42, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (14, 1), (25, 1), (42, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (10, 1), (32, 1), (37, 1), (52, 1)] }, { coefficient := -1, powers := [(8, 1), (10, 1), (32, 1), (42, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (20, 1), (29, 1), (42, 1)] }, { coefficient := 1, powers := [(5, 1), (25, 1), (29, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (21, 1), (28, 1), (52, 1), (53, 1)] }, { coefficient := 1, powers := [(7, 1), (21, 1), (31, 1), (48, 1), (53, 1)] }, { coefficient := 1, powers := [(10, 1), (21, 1), (25, 1), (52, 1), (53, 1)] }, { coefficient := -1, powers := [(10, 1), (21, 1), (31, 1), (34, 1), (53, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1), (21, 1), (37, 1), (53, 1)] }, { coefficient := 1, powers := [(14, 1), (21, 1), (25, 1), (42, 1), (53, 1)] }, { coefficient := 1, powers := [(14, 1), (21, 1), (31, 1), (34, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(14, 1), (21, 1), (42, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (20, 1), (32, 1), (48, 1)] }, { coefficient := -1, powers := [(8, 1), (25, 1), (32, 1), (48, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (14, 1), (26, 1), (28, 1), (42, 1), (48, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (8, 1), (29, 1), (31, 1), (48, 1), (57, 1)] }, { coefficient := 1, powers := [(8, 1), (14, 1), (20, 1), (29, 1), (48, 1), (57, 1)] }, { coefficient := 1, powers := [(8, 1), (14, 1), (20, 1), (29, 1), (52, 1), (57, 1)] }, { coefficient := -1, powers := [(8, 1), (14, 1), (25, 1), (29, 1), (48, 1), (57, 1)] }, { coefficient := -1, powers := [(8, 1), (14, 1), (25, 1), (29, 1), (52, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (10, 1), (21, 1), (28, 1), (42, 1), (43, 1), (52, 1)] }, { coefficient := 1, powers := [(8, 1), (10, 1), (21, 1), (31, 1), (42, 1), (43, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (16, 1), (21, 1), (28, 1), (42, 2)] }, { coefficient := -1, powers := [(7, 1), (16, 1), (21, 1), (28, 1), (42, 1), (52, 1)] }, { coefficient := 1, powers := [(7, 1), (16, 1), (21, 1), (31, 1), (37, 1), (42, 1)] }, { coefficient := -1, powers := [(7, 1), (16, 1), (21, 1), (31, 1), (42, 1), (48, 1)] }, { coefficient := -2, powers := [(10, 1), (16, 1), (21, 1), (25, 1), (42, 1), (52, 1)] }, { coefficient := 1, powers := [(10, 1), (16, 1), (21, 1), (31, 1), (34, 1), (42, 1)] }, { coefficient := -1, powers := [(14, 1), (16, 1), (20, 1), (21, 1), (37, 1), (42, 1)] }, { coefficient := -1, powers := [(14, 1), (16, 1), (20, 1), (21, 1), (42, 1), (52, 1)] }, { coefficient := -2, powers := [(14, 1), (16, 1), (21, 1), (25, 1), (42, 2)] }, { coefficient := -1, powers := [(14, 1), (16, 1), (21, 1), (31, 1), (34, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (28, 1), (42, 1), (50, 1)] }, { coefficient := 1, powers := [(7, 1), (31, 1), (37, 1), (50, 1)] }, { coefficient := -1, powers := [(10, 1), (25, 1), (50, 1), (52, 1)] }, { coefficient := -1, powers := [(14, 1), (20, 1), (37, 1), (50, 1)] }, { coefficient := -1, powers := [(14, 1), (25, 1), (42, 1), (50, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (18, 1), (31, 1), (40, 1), (48, 1), (57, 1)] }, { coefficient := -1, powers := [(4, 1), (20, 1), (44, 1), (55, 1)] }, { coefficient := -1, powers := [(4, 1), (22, 1), (31, 1), (44, 1), (48, 1), (57, 1)] }, { coefficient := 1, powers := [(4, 1), (25, 1), (44, 1), (55, 1)] }, { coefficient := -1, powers := [(7, 1), (20, 1), (44, 1), (55, 1)] }, { coefficient := 1, powers := [(7, 1), (25, 1), (44, 1), (55, 1)] }, { coefficient := 1, powers := [(10, 1), (20, 1), (44, 1), (52, 1)] }, { coefficient := -1, powers := [(14, 1), (18, 1), (20, 1), (40, 1), (48, 1), (57, 1)] }, { coefficient := -1, powers := [(14, 1), (18, 1), (20, 1), (40, 1), (52, 1), (57, 1)] }, { coefficient := 1, powers := [(14, 1), (18, 1), (25, 1), (40, 1), (48, 1), (57, 1)] }, { coefficient := 1, powers := [(14, 1), (18, 1), (25, 1), (40, 1), (52, 1), (57, 1)] }, { coefficient := -1, powers := [(14, 1), (20, 1), (22, 1), (44, 1), (48, 1), (57, 1)] }, { coefficient := -1, powers := [(14, 1), (20, 1), (22, 1), (44, 1), (52, 1), (57, 1)] }, { coefficient := -1, powers := [(14, 1), (20, 1), (37, 1), (44, 1)] }, { coefficient := 1, powers := [(14, 1), (22, 1), (25, 1), (44, 1), (48, 1), (57, 1)] }, { coefficient := 1, powers := [(14, 1), (22, 1), (25, 1), (44, 1), (52, 1), (57, 1)] }, { coefficient := 1, powers := [(14, 1), (25, 1), (44, 1), (48, 1)] }, { coefficient := 1, powers := [(14, 1), (25, 1), (44, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (12, 1), (14, 1), (16, 1), (21, 1), (25, 1), (42, 1), (53, 1), (55, 1)] }, { coefficient := -1, powers := [(4, 1), (16, 1), (20, 1), (55, 1)] }, { coefficient := 1, powers := [(4, 1), (16, 1), (25, 1), (55, 1)] }, { coefficient := 1, powers := [(4, 1), (16, 1), (28, 1), (52, 1)] }, { coefficient := 1, powers := [(4, 1), (16, 1), (31, 1), (48, 1)] }, { coefficient := -1, powers := [(6, 1), (8, 1), (10, 1), (16, 1), (20, 1), (32, 1), (38, 1), (52, 1), (55, 1)] }, { coefficient := -1, powers := [(7, 1), (12, 1), (16, 1), (20, 1), (21, 1), (53, 1), (55, 1)] }, { coefficient := 1, powers := [(7, 1), (12, 1), (16, 1), (21, 1), (25, 1), (53, 1), (55, 1)] }, { coefficient := -1, powers := [(7, 1), (16, 2), (20, 1), (26, 1), (38, 1), (55, 1)] }, { coefficient := 1, powers := [(7, 1), (16, 2), (25, 1), (26, 1), (38, 1), (55, 1)] }, { coefficient := 1, powers := [(7, 1), (16, 1), (28, 1), (42, 1)] }, { coefficient := 1, powers := [(7, 1), (16, 1), (31, 1), (37, 1)] }, { coefficient := -1, powers := [(10, 1), (16, 1), (20, 1), (42, 1)] }, { coefficient := 1, powers := [(10, 1), (16, 1), (25, 1), (42, 1)] }, { coefficient := 1, powers := [(10, 1), (16, 1), (31, 1), (34, 1)] }, { coefficient := -1, powers := [(14, 1), (16, 1), (20, 1), (37, 1)] }, { coefficient := -1, powers := [(14, 1), (16, 1), (20, 1), (48, 1)] }, { coefficient := -1, powers := [(14, 1), (16, 1), (20, 1), (52, 1)] }, { coefficient := -1, powers := [(14, 1), (16, 1), (25, 1), (42, 1)] }, { coefficient := -1, powers := [(14, 1), (16, 1), (31, 1), (34, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (12, 2), (14, 1), (21, 1), (25, 1), (42, 1), (53, 1), (55, 1)] }, { coefficient := -1, powers := [(4, 1), (12, 1), (20, 1), (55, 1)] }, { coefficient := 1, powers := [(4, 1), (12, 1), (25, 1), (55, 1)] }, { coefficient := 1, powers := [(4, 1), (12, 1), (28, 1), (52, 1)] }, { coefficient := 1, powers := [(4, 1), (12, 1), (31, 1), (48, 1)] }, { coefficient := -1, powers := [(6, 1), (8, 1), (10, 1), (12, 1), (20, 1), (32, 1), (38, 1), (52, 1), (55, 1)] }, { coefficient := -1, powers := [(7, 1), (12, 2), (20, 1), (21, 1), (53, 1), (55, 1)] }, { coefficient := 1, powers := [(7, 1), (12, 2), (21, 1), (25, 1), (53, 1), (55, 1)] }, { coefficient := -1, powers := [(7, 1), (12, 1), (16, 1), (20, 1), (26, 1), (38, 1), (55, 1)] }, { coefficient := 1, powers := [(7, 1), (12, 1), (16, 1), (25, 1), (26, 1), (38, 1), (55, 1)] }, { coefficient := 1, powers := [(7, 1), (12, 1), (28, 1), (42, 1)] }, { coefficient := 1, powers := [(7, 1), (12, 1), (31, 1), (37, 1)] }, { coefficient := -1, powers := [(10, 1), (12, 1), (20, 1), (42, 1)] }, { coefficient := -1, powers := [(10, 1), (12, 1), (20, 1), (52, 1)] }, { coefficient := 1, powers := [(10, 1), (12, 1), (25, 1), (42, 1)] }, { coefficient := 1, powers := [(10, 1), (12, 1), (25, 1), (52, 1)] }, { coefficient := 1, powers := [(10, 1), (12, 1), (31, 1), (34, 1)] }, { coefficient := -1, powers := [(12, 1), (14, 1), (20, 1), (37, 1)] }, { coefficient := -1, powers := [(12, 1), (14, 1), (20, 1), (48, 1)] }, { coefficient := -1, powers := [(12, 1), (14, 1), (20, 1), (52, 1)] }, { coefficient := -1, powers := [(12, 1), (14, 1), (25, 1), (42, 1)] }, { coefficient := -1, powers := [(12, 1), (14, 1), (31, 1), (34, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (16, 1), (21, 1), (28, 1), (42, 1)] }, { coefficient := 1, powers := [(7, 1), (16, 1), (21, 1), (28, 1), (52, 1)] }, { coefficient := -1, powers := [(7, 1), (16, 1), (21, 1), (31, 1), (37, 1)] }, { coefficient := 1, powers := [(7, 1), (16, 1), (21, 1), (31, 1), (48, 1)] }, { coefficient := 2, powers := [(10, 1), (16, 1), (21, 1), (25, 1), (52, 1)] }, { coefficient := -1, powers := [(10, 1), (16, 1), (21, 1), (31, 1), (34, 1)] }, { coefficient := 1, powers := [(14, 1), (16, 1), (20, 1), (21, 1), (37, 1)] }, { coefficient := 1, powers := [(14, 1), (16, 1), (20, 1), (21, 1), (52, 1)] }, { coefficient := 2, powers := [(14, 1), (16, 1), (21, 1), (25, 1), (42, 1)] }, { coefficient := 1, powers := [(14, 1), (16, 1), (21, 1), (31, 1), (34, 1)] }],
  [{ coefficient := -1, powers := [(14, 1), (25, 1), (38, 1)] }],
  [{ coefficient := -1, powers := [(10, 1), (20, 1), (53, 1)] }, { coefficient := 1, powers := [(14, 1), (19, 1), (42, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (20, 1), (56, 1)] }, { coefficient := -1, powers := [(5, 1), (25, 1), (56, 1)] }, { coefficient := -1, powers := [(16, 1), (20, 1), (38, 1)] }, { coefficient := 1, powers := [(16, 1), (25, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (28, 1), (52, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (28, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (14, 1), (29, 1), (42, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(10, 1), (26, 1), (52, 1)] }, { coefficient := -1, powers := [(14, 1), (26, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (20, 1), (53, 1)] }, { coefficient := -1, powers := [(12, 1), (25, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (28, 1), (42, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (21, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (32, 1), (35, 1)] }],
  [{ coefficient := -1, powers := [(14, 1), (20, 1), (26, 1), (48, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (21, 1), (28, 1), (52, 1)] }, { coefficient := -1, powers := [(7, 1), (21, 1), (31, 1), (48, 1)] }, { coefficient := -1, powers := [(10, 1), (21, 1), (25, 1), (52, 1)] }, { coefficient := 1, powers := [(10, 1), (21, 1), (31, 1), (34, 1)] }, { coefficient := -1, powers := [(14, 1), (20, 1), (21, 1), (37, 1)] }, { coefficient := -1, powers := [(14, 1), (21, 1), (25, 1), (42, 1)] }, { coefficient := -1, powers := [(14, 1), (21, 1), (31, 1), (34, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (14, 1), (26, 1), (28, 1), (42, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (10, 1), (21, 1), (28, 1), (42, 1), (52, 1)] }, { coefficient := -1, powers := [(8, 1), (10, 1), (21, 1), (31, 1), (42, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (14, 1), (28, 1), (42, 1), (48, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (10, 1), (28, 1), (42, 1), (52, 1)] }, { coefficient := 1, powers := [(8, 1), (10, 1), (31, 1), (42, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (14, 1), (21, 1), (25, 1), (42, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (14, 1), (21, 1), (25, 1), (42, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (20, 1), (26, 1), (56, 1)] }, { coefficient := -1, powers := [(5, 1), (20, 1), (32, 1), (50, 1)] }, { coefficient := 1, powers := [(5, 1), (25, 1), (26, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (25, 1), (32, 1), (50, 1)] }, { coefficient := -1, powers := [(8, 1), (20, 1), (21, 1), (56, 1)] }, { coefficient := -1, powers := [(8, 1), (20, 1), (32, 1), (38, 1)] }, { coefficient := 1, powers := [(8, 1), (21, 1), (25, 1), (56, 1)] }, { coefficient := 1, powers := [(8, 1), (25, 1), (32, 1), (38, 1)] }, { coefficient := 1, powers := [(12, 1), (20, 1), (26, 1), (44, 1)] }, { coefficient := -1, powers := [(12, 1), (25, 1), (26, 1), (44, 1)] }, { coefficient := 1, powers := [(16, 1), (20, 1), (26, 1), (38, 1)] }, { coefficient := -1, powers := [(16, 1), (25, 1), (26, 1), (38, 1)] }, { coefficient := 1, powers := [(20, 1)] }],
  [{ coefficient := -2, powers := [(8, 1), (14, 1), (29, 1), (44, 1)] }, { coefficient := -1, powers := [(8, 1), (14, 1), (32, 1), (38, 1)] }, { coefficient := 1, powers := [(14, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (14, 1), (29, 1), (42, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (10, 1), (32, 1), (38, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(3, 1), (12, 1), (14, 1), (21, 1), (25, 1), (42, 1), (53, 1), (55, 1)] }, { coefficient := 1, powers := [(4, 1), (20, 1), (55, 1)] }, { coefficient := -1, powers := [(4, 1), (25, 1), (55, 1)] }, { coefficient := -1, powers := [(4, 1), (28, 1), (52, 1)] }, { coefficient := -1, powers := [(4, 1), (31, 1), (48, 1)] }, { coefficient := 1, powers := [(6, 1), (8, 1), (10, 1), (20, 1), (32, 1), (38, 1), (52, 1), (55, 1)] }, { coefficient := 1, powers := [(7, 1), (12, 1), (20, 1), (21, 1), (53, 1), (55, 1)] }, { coefficient := -1, powers := [(7, 1), (12, 1), (21, 1), (25, 1), (53, 1), (55, 1)] }, { coefficient := 1, powers := [(7, 1), (16, 1), (20, 1), (26, 1), (38, 1), (55, 1)] }, { coefficient := -1, powers := [(7, 1), (16, 1), (25, 1), (26, 1), (38, 1), (55, 1)] }, { coefficient := -1, powers := [(7, 1), (28, 1), (42, 1)] }, { coefficient := -1, powers := [(7, 1), (31, 1), (37, 1)] }, { coefficient := 1, powers := [(10, 1), (20, 1), (42, 1)] }, { coefficient := -1, powers := [(10, 1), (25, 1), (42, 1)] }, { coefficient := -1, powers := [(10, 1), (31, 1), (34, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1), (37, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1), (48, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1), (52, 1)] }, { coefficient := 1, powers := [(14, 1), (25, 1), (42, 1)] }, { coefficient := 1, powers := [(14, 1), (31, 1), (34, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (8, 1), (29, 1), (31, 1), (44, 1), (48, 1)] }, { coefficient := -1, powers := [(8, 1), (14, 1), (20, 1), (29, 1), (44, 1), (48, 1)] }, { coefficient := -1, powers := [(8, 1), (14, 1), (20, 1), (29, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(8, 1), (14, 1), (25, 1), (29, 1), (44, 1), (48, 1)] }, { coefficient := 1, powers := [(8, 1), (14, 1), (25, 1), (29, 1), (44, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(34, 1), (55, 1)] }, { coefficient := 1, powers := [(37, 1), (52, 1)] }, { coefficient := 1, powers := [(42, 1), (48, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (12, 1), (14, 1), (21, 1), (25, 1), (35, 1), (42, 1), (53, 1), (55, 1), (56, 1)] }, { coefficient := -1, powers := [(3, 1), (12, 1), (14, 1), (21, 1), (25, 1), (38, 1), (42, 1), (53, 2), (55, 1)] }, { coefficient := -1, powers := [(3, 1), (12, 1), (14, 1), (21, 1), (25, 1), (42, 1), (44, 1), (50, 1), (53, 1), (55, 1)] }, { coefficient := 1, powers := [(4, 1), (18, 1), (31, 1), (40, 1), (48, 1), (50, 1), (57, 1)] }, { coefficient := -1, powers := [(4, 1), (20, 1), (35, 1), (55, 1), (56, 1)] }, { coefficient := -1, powers := [(4, 1), (20, 1), (38, 1), (53, 1), (55, 1)] }, { coefficient := 1, powers := [(4, 1), (22, 1), (31, 1), (44, 1), (48, 1), (50, 1), (57, 1)] }, { coefficient := 1, powers := [(4, 1), (25, 1), (35, 1), (55, 1), (56, 1)] }, { coefficient := 1, powers := [(4, 1), (25, 1), (38, 1), (53, 1), (55, 1)] }, { coefficient := 1, powers := [(4, 1), (28, 1), (35, 1), (52, 1), (56, 1)] }, { coefficient := 1, powers := [(4, 1), (28, 1), (38, 1), (52, 1), (53, 1)] }, { coefficient := 1, powers := [(4, 1), (28, 1), (44, 1), (50, 1), (52, 1)] }, { coefficient := 1, powers := [(4, 1), (31, 1), (35, 1), (48, 1), (56, 1)] }, { coefficient := 1, powers := [(4, 1), (31, 1), (38, 1), (48, 1), (53, 1)] }, { coefficient := 1, powers := [(4, 1), (31, 1), (44, 1), (48, 1), (50, 1)] }, { coefficient := -1, powers := [(6, 1), (8, 1), (10, 1), (20, 1), (32, 1), (35, 1), (38, 1), (52, 1), (55, 1), (56, 1)] }, { coefficient := -1, powers := [(6, 1), (8, 1), (10, 1), (20, 1), (32, 1), (38, 2), (52, 1), (53, 1), (55, 1)] }, { coefficient := -1, powers := [(6, 1), (8, 1), (10, 1), (20, 1), (32, 1), (38, 1), (44, 1), (50, 1), (52, 1), (55, 1)] }, { coefficient := -1, powers := [(7, 1), (12, 1), (20, 1), (21, 1), (35, 1), (53, 1), (55, 1), (56, 1)] }, { coefficient := -1, powers := [(7, 1), (12, 1), (20, 1), (21, 1), (38, 1), (53, 2), (55, 1)] }, { coefficient := -1, powers := [(7, 1), (12, 1), (20, 1), (21, 1), (44, 1), (50, 1), (53, 1), (55, 1)] }, { coefficient := 1, powers := [(7, 1), (12, 1), (21, 1), (25, 1), (35, 1), (53, 1), (55, 1), (56, 1)] }, { coefficient := 1, powers := [(7, 1), (12, 1), (21, 1), (25, 1), (38, 1), (53, 2), (55, 1)] }, { coefficient := 1, powers := [(7, 1), (12, 1), (21, 1), (25, 1), (44, 1), (50, 1), (53, 1), (55, 1)] }, { coefficient := -1, powers := [(7, 1), (16, 1), (20, 1), (26, 1), (35, 1), (38, 1), (55, 1), (56, 1)] }, { coefficient := -1, powers := [(7, 1), (16, 1), (20, 1), (26, 1), (38, 2), (53, 1), (55, 1)] }, { coefficient := -1, powers := [(7, 1), (16, 1), (20, 1), (26, 1), (38, 1), (44, 1), (50, 1), (55, 1)] }, { coefficient := 1, powers := [(7, 1), (16, 1), (25, 1), (26, 1), (35, 1), (38, 1), (55, 1), (56, 1)] }, { coefficient := 1, powers := [(7, 1), (16, 1), (25, 1), (26, 1), (38, 2), (53, 1), (55, 1)] }, { coefficient := 1, powers := [(7, 1), (16, 1), (25, 1), (26, 1), (38, 1), (44, 1), (50, 1), (55, 1)] }, { coefficient := 1, powers := [(7, 1), (20, 1), (44, 1), (50, 1), (55, 1)] }, { coefficient := -1, powers := [(7, 1), (25, 1), (44, 1), (50, 1), (55, 1)] }, { coefficient := 1, powers := [(7, 1), (28, 1), (35, 1), (42, 1), (56, 1)] }, { coefficient := 1, powers := [(7, 1), (28, 1), (38, 1), (42, 1), (53, 1)] }, { coefficient := 1, powers := [(7, 1), (31, 1), (35, 1), (37, 1), (56, 1)] }, { coefficient := 1, powers := [(7, 1), (31, 1), (37, 1), (38, 1), (53, 1)] }, { coefficient := -1, powers := [(10, 1), (20, 1), (35, 1), (42, 1), (56, 1)] }, { coefficient := -1, powers := [(10, 1), (20, 1), (38, 1), (42, 1), (53, 1)] }, { coefficient := 1, powers := [(10, 1), (20, 1), (38, 1), (52, 1), (53, 1)] }, { coefficient := -1, powers := [(10, 1), (20, 1), (42, 1), (44, 1), (50, 1)] }, { coefficient := -1, powers := [(10, 1), (20, 1), (44, 1), (50, 1), (52, 1)] }, { coefficient := 1, powers := [(10, 1), (25, 1), (35, 1), (42, 1), (56, 1)] }, { coefficient := 1, powers := [(10, 1), (25, 1), (38, 1), (42, 1), (53, 1)] }, { coefficient := 1, powers := [(10, 1), (25, 1), (42, 1), (44, 1), (50, 1)] }, { coefficient := 1, powers := [(10, 1), (25, 1), (44, 1), (50, 1), (52, 1)] }, { coefficient := 1, powers := [(10, 1), (31, 1), (34, 1), (35, 1), (56, 1)] }, { coefficient := 1, powers := [(10, 1), (31, 1), (34, 1), (38, 1), (53, 1)] }, { coefficient := 1, powers := [(10, 1), (31, 1), (34, 1), (44, 1), (50, 1)] }, { coefficient := 1, powers := [(14, 1), (18, 1), (20, 1), (40, 1), (48, 1), (50, 1), (57, 1)] }, { coefficient := 1, powers := [(14, 1), (18, 1), (20, 1), (40, 1), (50, 1), (52, 1), (57, 1)] }, { coefficient := -1, powers := [(14, 1), (18, 1), (25, 1), (40, 1), (48, 1), (50, 1), (57, 1)] }, { coefficient := -1, powers := [(14, 1), (18, 1), (25, 1), (40, 1), (50, 1), (52, 1), (57, 1)] }, { coefficient := -1, powers := [(14, 1), (19, 1), (38, 1), (42, 1), (52, 1), (53, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1), (22, 1), (44, 1), (48, 1), (50, 1), (57, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1), (22, 1), (44, 1), (50, 1), (52, 1), (57, 1)] }, { coefficient := -1, powers := [(14, 1), (20, 1), (35, 1), (37, 1), (56, 1)] }, { coefficient := -1, powers := [(14, 1), (20, 1), (35, 1), (48, 1), (56, 1)] }, { coefficient := -1, powers := [(14, 1), (20, 1), (35, 1), (52, 1), (56, 1)] }, { coefficient := -1, powers := [(14, 1), (20, 1), (37, 1), (38, 1), (53, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1), (37, 1), (44, 1), (50, 1)] }, { coefficient := -1, powers := [(14, 1), (20, 1), (38, 1), (48, 1), (53, 1)] }, { coefficient := -1, powers := [(14, 1), (20, 1), (38, 1), (52, 1), (53, 1)] }, { coefficient := -1, powers := [(14, 1), (20, 1), (44, 1), (48, 1), (50, 1)] }, { coefficient := -1, powers := [(14, 1), (20, 1), (44, 1), (50, 1), (52, 1)] }, { coefficient := -1, powers := [(14, 1), (22, 1), (25, 1), (44, 1), (48, 1), (50, 1), (57, 1)] }, { coefficient := -1, powers := [(14, 1), (22, 1), (25, 1), (44, 1), (50, 1), (52, 1), (57, 1)] }, { coefficient := -1, powers := [(14, 1), (25, 1), (35, 1), (42, 1), (56, 1)] }, { coefficient := 1, powers := [(14, 1), (25, 1), (37, 1), (38, 1), (53, 1)] }, { coefficient := -1, powers := [(14, 1), (25, 1), (38, 1), (42, 1), (53, 1)] }, { coefficient := -1, powers := [(14, 1), (25, 1), (44, 1), (48, 1), (50, 1)] }, { coefficient := -1, powers := [(14, 1), (25, 1), (44, 1), (50, 1), (52, 1)] }, { coefficient := -1, powers := [(14, 1), (31, 1), (34, 1), (35, 1), (56, 1)] }, { coefficient := -1, powers := [(14, 1), (31, 1), (34, 1), (38, 1), (53, 1)] }, { coefficient := -1, powers := [(14, 1), (31, 1), (34, 1), (44, 1), (50, 1)] }]
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
    (values : Fin 58 → R) :
    ¬ ∀ index : Fin 75,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component56.SelectedLeafB4.selectedHasNoCommonZero

end Krenn.Component56.SelectedLeafB4
