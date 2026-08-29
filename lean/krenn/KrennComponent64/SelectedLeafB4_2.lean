import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component64.SelectedLeafB4_2

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "23236a409b8170b6747568f962061e9022325720e9c02cd5fbfc42c50139ba8b"
def certificateSHA256 : String := "35c48c9241e2b79d85bc1d75d4ff8db620534094de04a9eb30ccce213b656555"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 59 → Fin 641 := ![
  7,
  9,
  10,
  24,
  26,
  27,
  29,
  32,
  71,
  161,
  162,
  163,
  164,
  166,
  170,
  173,
  187,
  191,
  193,
  198,
  205,
  209,
  222,
  231,
  235,
  243,
  283,
  284,
  309,
  310,
  343,
  344,
  349,
  350,
  351,
  352,
  356,
  358,
  367,
  369,
  390,
  415,
  433,
  444,
  466,
  479,
  507,
  548,
  556,
  557,
  576,
  577,
  632,
  634,
  635,
  637,
  638,
  639,
  640
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 59 → SparsePoly (Fin 62) := ![
  [{ coefficient := 1, powers := [(5, 1), (31, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (28, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(31, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (33, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1)] }, { coefficient := 1, powers := [(24, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1)] }, { coefficient := 1, powers := [(24, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (52, 1)] }, { coefficient := 1, powers := [(20, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (53, 1)] }, { coefficient := 1, powers := [(20, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (45, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (58, 1)] }, { coefficient := 1, powers := [(18, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (27, 1)] }, { coefficient := 1, powers := [(27, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (24, 1)] }, { coefficient := 1, powers := [(18, 1), (20, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (23, 1)] }, { coefficient := 1, powers := [(23, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (20, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (50, 1)] }, { coefficient := 1, powers := [(23, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1), (53, 1)] }, { coefficient := 1, powers := [(53, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1), (50, 1)] }, { coefficient := 1, powers := [(46, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (27, 1), (58, 1)] }, { coefficient := 1, powers := [(27, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (31, 1), (49, 1)] }, { coefficient := 1, powers := [(5, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (23, 1), (58, 1)] }, { coefficient := 1, powers := [(23, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (28, 1), (42, 1)] }, { coefficient := 1, powers := [(8, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (24, 1), (42, 1)] }, { coefficient := 1, powers := [(13, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (24, 1), (43, 1)] }, { coefficient := 1, powers := [(18, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (24, 1), (41, 1)] }, { coefficient := 1, powers := [(19, 1), (20, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (24, 1), (42, 1)] }, { coefficient := 1, powers := [(18, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (41, 1)] }, { coefficient := 1, powers := [(20, 1), (41, 1)] }, { coefficient := 1, powers := [(24, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (48, 1)] }, { coefficient := 1, powers := [(20, 1), (48, 1)] }, { coefficient := 1, powers := [(24, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (46, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1)] }, { coefficient := 1, powers := [(19, 1), (23, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (53, 1)] }, { coefficient := 1, powers := [(8, 1), (30, 1)] }, { coefficient := 1, powers := [(13, 1), (27, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (59, 1)] }, { coefficient := 1, powers := [(13, 1), (46, 1)] }, { coefficient := 1, powers := [(19, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (59, 1)] }, { coefficient := 1, powers := [(13, 1), (56, 1)] }, { coefficient := 1, powers := [(19, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (43, 1)] }, { coefficient := 1, powers := [(13, 1), (55, 1)] }, { coefficient := 1, powers := [(18, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (44, 1)] }, { coefficient := 1, powers := [(19, 1), (38, 1)] }, { coefficient := 1, powers := [(19, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (41, 1), (52, 1)] }, { coefficient := 1, powers := [(20, 1), (41, 1), (52, 1)] }, { coefficient := 1, powers := [(20, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1), (48, 1)] }, { coefficient := 1, powers := [(24, 1), (43, 1), (48, 1)] }, { coefficient := 1, powers := [(48, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (39, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (54, 1)] }, { coefficient := 1, powers := [(13, 1), (23, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (28, 1), (56, 1)] }, { coefficient := 1, powers := [(8, 1), (28, 1), (46, 1)] }, { coefficient := 1, powers := [(19, 1), (28, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (20, 1), (55, 1)] }, { coefficient := 1, powers := [(13, 1)] }, { coefficient := 1, powers := [(18, 1), (20, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (24, 1), (38, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (43, 1)] }, { coefficient := 1, powers := [(18, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (53, 1)] }, { coefficient := 1, powers := [(27, 1), (39, 1)] }, { coefficient := 1, powers := [(27, 1), (45, 1), (48, 1)] }, { coefficient := 1, powers := [(30, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1), (48, 1)] }, { coefficient := 1, powers := [(6, 1), (59, 1)] }, { coefficient := 1, powers := [(24, 1), (44, 1), (48, 1)] }, { coefficient := 1, powers := [(41, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (27, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (30, 1), (56, 1)] }, { coefficient := 1, powers := [(3, 1), (33, 1), (53, 1)] }, { coefficient := 1, powers := [(27, 1), (41, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (41, 1), (52, 1)] }, { coefficient := 1, powers := [(23, 1), (56, 1)] }, { coefficient := 1, powers := [(27, 1), (46, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1)] }, { coefficient := 1, powers := [(6, 1), (58, 1)] }, { coefficient := 1, powers := [(24, 1), (38, 1)] }, { coefficient := 1, powers := [(24, 1), (43, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (50, 1)] }, { coefficient := 1, powers := [(3, 1), (58, 1)] }, { coefficient := 1, powers := [(20, 1), (50, 1)] }, { coefficient := 1, powers := [(20, 1), (55, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (40, 1)] }, { coefficient := 1, powers := [(3, 1), (31, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1)] }, { coefficient := 1, powers := [(20, 1), (54, 1)] }, { coefficient := 1, powers := [(24, 1), (40, 1)] }, { coefficient := 1, powers := [(31, 1), (34, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1)] }, { coefficient := 1, powers := [(6, 1), (28, 1)] }, { coefficient := 1, powers := [(9, 1), (24, 1)] }, { coefficient := 1, powers := [(20, 1), (47, 1)] }, { coefficient := 1, powers := [(24, 1), (37, 1)] }, { coefficient := 1, powers := [(28, 1), (34, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (34, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (37, 1), (54, 1)] }, { coefficient := 1, powers := [(0, 1), (40, 1), (47, 1)] }, { coefficient := 1, powers := [(3, 1), (24, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (28, 1), (54, 1)] }, { coefficient := 1, powers := [(3, 1), (31, 1), (47, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1), (57, 1)] }, { coefficient := 1, powers := [(6, 1), (28, 1), (40, 1)] }, { coefficient := 1, powers := [(6, 1), (31, 1), (37, 1)] }, { coefficient := 1, powers := [(9, 1), (20, 1), (54, 1)] }, { coefficient := 1, powers := [(9, 1), (24, 1), (40, 1)] }, { coefficient := 1, powers := [(9, 1), (31, 1), (34, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1), (47, 1)] }, { coefficient := 1, powers := [(14, 1), (24, 1), (37, 1)] }, { coefficient := 1, powers := [(14, 1), (28, 1), (34, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (36, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (46, 1), (53, 1)] }, { coefficient := 1, powers := [(5, 1), (27, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (53, 1)] }, { coefficient := 1, powers := [(8, 1), (23, 1), (59, 1)] }, { coefficient := 1, powers := [(8, 1), (30, 1), (46, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (39, 1)] }, { coefficient := 1, powers := [(13, 1), (23, 1), (56, 1)] }, { coefficient := 1, powers := [(13, 1), (27, 1), (46, 1)] }, { coefficient := 1, powers := [(13, 1), (33, 1), (36, 1)] }, { coefficient := 1, powers := [(19, 1), (23, 1), (53, 1)] }, { coefficient := 1, powers := [(19, 1), (27, 1), (39, 1)] }, { coefficient := 1, powers := [(19, 1), (30, 1), (36, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (60, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(37, 1)] }],
  [{ coefficient := 1, powers := [(38, 1), (61, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(39, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 59 → SparsePoly (Fin 62) := ![
  [{ coefficient := -1, powers := [(0, 1), (30, 1), (34, 1), (49, 1), (56, 1)] }, { coefficient := -1, powers := [(0, 1), (33, 1), (34, 1), (49, 1), (53, 1)] }, { coefficient := -1, powers := [(3, 1), (24, 1), (30, 1), (49, 1), (56, 1)] }, { coefficient := -1, powers := [(3, 1), (24, 1), (33, 1), (49, 1), (53, 1)] }, { coefficient := -1, powers := [(6, 1), (20, 1), (30, 1), (49, 1), (56, 1)] }, { coefficient := -1, powers := [(6, 1), (20, 1), (33, 1), (49, 1), (53, 1)] }, { coefficient := 1, powers := [(9, 1), (27, 1), (34, 1), (59, 1)] }, { coefficient := 1, powers := [(9, 1), (30, 1), (34, 1), (56, 1)] }, { coefficient := 2, powers := [(9, 1), (33, 1), (34, 1), (53, 1)] }, { coefficient := -1, powers := [(27, 1), (34, 1), (47, 1), (59, 1)] }, { coefficient := -1, powers := [(30, 1), (34, 1), (47, 1), (56, 1)] }, { coefficient := -2, powers := [(33, 1), (34, 1), (47, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (23, 1), (34, 1), (42, 1), (59, 1)] }, { coefficient := -2, powers := [(0, 1), (30, 1), (34, 1), (42, 1), (46, 1)] }, { coefficient := -1, powers := [(3, 1), (23, 1), (24, 1), (42, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (23, 1), (54, 1), (59, 1)] }, { coefficient := -2, powers := [(3, 1), (24, 1), (30, 1), (42, 1), (46, 1)] }, { coefficient := 1, powers := [(3, 1), (30, 1), (46, 1), (54, 1)] }, { coefficient := -1, powers := [(6, 1), (20, 1), (23, 1), (42, 1), (59, 1)] }, { coefficient := -2, powers := [(6, 1), (20, 1), (30, 1), (42, 1), (46, 1)] }, { coefficient := -1, powers := [(6, 1), (23, 1), (24, 1), (40, 1), (50, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (23, 1), (40, 1), (59, 1)] }, { coefficient := -1, powers := [(6, 1), (24, 1), (30, 1), (40, 1), (46, 1), (50, 1)] }, { coefficient := 1, powers := [(6, 1), (30, 1), (40, 1), (46, 1)] }, { coefficient := 1, powers := [(14, 1), (23, 1), (34, 1), (59, 1)] }, { coefficient := 1, powers := [(14, 1), (30, 1), (34, 1), (46, 1)] }, { coefficient := -1, powers := [(23, 1), (24, 1), (34, 1), (40, 1), (50, 1), (59, 1)] }, { coefficient := -1, powers := [(24, 1), (30, 1), (34, 1), (40, 1), (46, 1), (50, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (24, 2), (30, 1), (40, 1), (50, 1)] }, { coefficient := 1, powers := [(5, 1), (24, 1), (30, 1), (40, 1)] }, { coefficient := 1, powers := [(13, 1), (23, 1), (24, 2), (40, 1), (50, 1)] }, { coefficient := -1, powers := [(13, 1), (23, 1), (24, 1), (40, 1)] }],
  [{ coefficient := -1, powers := [(23, 1), (24, 2), (40, 1), (44, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (13, 1), (24, 1), (40, 1), (47, 1), (50, 1), (52, 1)] }, { coefficient := -1, powers := [(0, 1), (13, 1), (34, 1), (52, 1), (57, 1)] }, { coefficient := -1, powers := [(3, 1), (13, 1), (24, 1), (52, 1), (57, 1)] }, { coefficient := -1, powers := [(3, 1), (13, 1), (28, 1), (52, 1), (54, 1)] }, { coefficient := -1, powers := [(6, 1), (13, 1), (20, 1), (52, 1), (57, 1)] }, { coefficient := 1, powers := [(6, 1), (13, 1), (24, 1), (28, 1), (40, 1), (50, 1), (52, 1)] }, { coefficient := -1, powers := [(6, 1), (13, 1), (28, 1), (40, 1), (52, 1)] }, { coefficient := -1, powers := [(9, 1), (13, 1), (20, 1), (52, 1), (54, 1)] }, { coefficient := 1, powers := [(9, 1), (13, 1), (24, 2), (40, 1), (50, 1), (52, 1)] }, { coefficient := -1, powers := [(9, 1), (13, 1), (24, 1), (40, 1), (52, 1)] }, { coefficient := -1, powers := [(13, 1), (14, 1), (28, 1), (34, 1), (52, 1)] }, { coefficient := 1, powers := [(13, 1), (20, 1), (24, 1), (40, 1), (47, 1), (50, 1), (52, 1)] }, { coefficient := 1, powers := [(13, 1), (20, 1), (47, 1), (52, 1), (54, 1)] }, { coefficient := 1, powers := [(13, 1), (24, 1), (28, 1), (34, 1), (40, 1), (50, 1), (52, 1)] }, { coefficient := 1, powers := [(13, 1), (24, 1), (40, 1), (47, 1), (52, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (40, 1), (47, 1), (53, 1)] }],
  [{ coefficient := -2, powers := [(13, 1), (14, 1), (20, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (19, 1), (24, 1), (40, 1), (45, 1), (47, 1), (50, 1)] }, { coefficient := -1, powers := [(0, 1), (19, 1), (34, 1), (45, 1), (57, 1)] }, { coefficient := -1, powers := [(3, 1), (19, 1), (24, 1), (45, 1), (57, 1)] }, { coefficient := -1, powers := [(5, 1), (24, 1), (40, 1), (41, 1), (47, 1), (58, 1)] }, { coefficient := -1, powers := [(6, 1), (19, 1), (20, 1), (45, 1), (57, 1)] }, { coefficient := -1, powers := [(9, 1), (19, 1), (20, 1), (45, 1), (54, 1)] }, { coefficient := 1, powers := [(9, 1), (19, 1), (24, 2), (40, 1), (45, 1), (50, 1)] }, { coefficient := -1, powers := [(9, 1), (19, 1), (24, 1), (40, 1), (45, 1)] }, { coefficient := -1, powers := [(9, 1), (19, 1), (31, 1), (34, 1), (45, 1)] }, { coefficient := 1, powers := [(19, 1), (20, 1), (24, 1), (40, 1), (45, 1), (47, 1), (50, 1)] }, { coefficient := 1, powers := [(19, 1), (20, 1), (45, 1), (47, 1), (54, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (40, 1), (45, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (31, 1), (34, 1), (45, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (13, 1), (33, 1), (34, 1)] }, { coefficient := -1, powers := [(13, 1), (33, 1), (34, 1), (47, 1)] }],
  [{ coefficient := -2, powers := [(9, 1), (18, 1), (24, 2), (40, 1), (45, 1), (50, 1), (53, 1), (61, 1)] }, { coefficient := 2, powers := [(9, 1), (18, 1), (24, 1), (40, 1), (45, 1), (53, 1), (61, 1)] }, { coefficient := 2, powers := [(14, 1), (18, 1), (20, 1), (45, 1), (47, 1), (53, 1), (61, 1)] }],
  [{ coefficient := 2, powers := [(9, 1), (18, 1), (20, 1), (27, 1), (41, 1), (43, 1), (48, 1), (54, 1)] }, { coefficient := -2, powers := [(9, 1), (18, 1), (20, 1), (27, 1), (44, 1), (48, 1), (54, 1)] }, { coefficient := -2, powers := [(18, 1), (20, 1), (24, 1), (27, 1), (40, 1), (41, 1), (43, 1), (47, 1), (48, 1), (50, 1)] }, { coefficient := 2, powers := [(18, 1), (20, 1), (24, 1), (27, 1), (40, 1), (44, 1), (47, 1), (48, 1), (50, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (27, 1), (40, 1), (41, 1), (43, 1), (47, 1), (48, 1)] }, { coefficient := -1, powers := [(18, 1), (24, 1), (27, 1), (40, 1), (44, 1), (47, 1), (48, 1)] }],
  [{ coefficient := 2, powers := [(9, 1), (13, 1), (20, 1), (27, 1), (43, 1), (54, 1)] }, { coefficient := -2, powers := [(13, 1), (20, 1), (24, 1), (27, 1), (40, 1), (43, 1), (47, 1), (50, 1)] }, { coefficient := 1, powers := [(13, 1), (24, 1), (27, 1), (40, 1), (43, 1), (47, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (9, 1), (30, 1), (41, 1), (54, 1)] }, { coefficient := -1, powers := [(5, 1), (24, 1), (30, 1), (40, 1), (41, 1), (47, 1), (55, 1)] }, { coefficient := 1, powers := [(9, 1), (13, 1), (23, 1), (41, 1), (54, 1)] }, { coefficient := -1, powers := [(13, 1), (23, 1), (24, 1), (40, 1), (41, 1), (43, 1), (47, 1)] }, { coefficient := -1, powers := [(13, 1), (23, 1), (24, 1), (40, 1), (41, 1), (47, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (24, 1), (33, 1), (40, 1), (47, 1), (50, 1)] }, { coefficient := -1, powers := [(19, 1), (23, 1), (24, 1), (40, 1), (43, 1), (47, 1)] }, { coefficient := 2, powers := [(19, 1), (23, 1), (24, 1), (40, 1), (47, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (24, 1), (40, 1), (47, 1), (51, 1), (56, 1)] }, { coefficient := 1, powers := [(24, 1), (40, 1), (47, 1), (48, 1), (56, 1)] }],
  [{ coefficient := -2, powers := [(6, 1), (9, 1), (20, 1), (27, 1), (54, 1), (59, 1)] }, { coefficient := 2, powers := [(6, 1), (9, 1), (24, 2), (33, 1), (40, 1), (50, 1), (53, 1)] }, { coefficient := -2, powers := [(6, 1), (9, 1), (24, 1), (33, 1), (40, 1), (53, 1)] }, { coefficient := -2, powers := [(6, 1), (14, 1), (20, 1), (33, 1), (47, 1), (53, 1)] }, { coefficient := 2, powers := [(6, 1), (20, 1), (24, 1), (27, 1), (40, 1), (47, 1), (50, 1), (59, 1)] }, { coefficient := -1, powers := [(6, 1), (24, 1), (27, 1), (40, 1), (47, 1), (59, 1)] }],
  [{ coefficient := 2, powers := [(13, 1), (24, 2), (40, 1), (46, 1), (50, 1)] }, { coefficient := -2, powers := [(13, 1), (24, 1), (40, 1), (46, 1)] }],
  [{ coefficient := 2, powers := [(9, 1), (20, 1), (27, 1), (38, 1), (46, 1), (54, 1)] }, { coefficient := 2, powers := [(9, 1), (20, 1), (27, 1), (43, 1), (46, 1), (54, 1)] }, { coefficient := -2, powers := [(20, 1), (24, 1), (27, 1), (38, 1), (40, 1), (46, 1), (47, 1), (50, 1)] }, { coefficient := -2, powers := [(20, 1), (24, 1), (27, 1), (40, 1), (43, 1), (46, 1), (47, 1), (50, 1)] }, { coefficient := -2, powers := [(20, 1), (27, 1), (42, 1), (46, 1), (47, 1)] }, { coefficient := -1, powers := [(23, 1), (24, 1), (38, 1), (40, 1), (47, 1), (56, 1)] }, { coefficient := -1, powers := [(23, 1), (24, 1), (40, 1), (43, 1), (47, 1), (56, 1)] }, { coefficient := 1, powers := [(24, 1), (27, 1), (38, 1), (40, 1), (46, 1), (47, 1)] }, { coefficient := 1, powers := [(24, 1), (27, 1), (40, 1), (43, 1), (46, 1), (47, 1)] }],
  [{ coefficient := 2, powers := [(13, 1), (20, 1), (47, 1), (56, 1)] }, { coefficient := 2, powers := [(19, 1), (20, 1), (47, 1), (53, 1)] }],
  [{ coefficient := -2, powers := [(9, 1), (20, 1), (27, 1), (38, 1), (46, 1), (48, 1), (54, 1)] }, { coefficient := -2, powers := [(9, 1), (20, 1), (27, 1), (43, 1), (46, 1), (48, 1), (54, 1)] }, { coefficient := -2, powers := [(9, 1), (23, 1), (24, 1), (41, 1), (53, 1), (54, 1), (60, 1)] }, { coefficient := 2, powers := [(20, 1), (24, 1), (27, 1), (38, 1), (40, 1), (46, 1), (47, 1), (48, 1), (50, 1)] }, { coefficient := 2, powers := [(20, 1), (24, 1), (27, 1), (40, 1), (43, 1), (46, 1), (47, 1), (48, 1), (50, 1)] }, { coefficient := 2, powers := [(20, 1), (27, 1), (42, 1), (46, 1), (47, 1), (48, 1)] }, { coefficient := -2, powers := [(20, 1), (27, 1), (46, 1), (47, 1), (48, 1), (54, 1), (60, 1)] }, { coefficient := 2, powers := [(23, 1), (24, 2), (40, 1), (41, 1), (47, 1), (50, 1), (53, 1), (60, 1)] }, { coefficient := 1, powers := [(23, 1), (24, 1), (38, 1), (40, 1), (47, 1), (48, 1), (56, 1)] }, { coefficient := 1, powers := [(23, 1), (24, 1), (40, 1), (43, 1), (47, 1), (48, 1), (56, 1)] }, { coefficient := 1, powers := [(23, 1), (24, 1), (40, 1), (44, 1), (47, 1), (53, 1)] }, { coefficient := -1, powers := [(24, 1), (27, 1), (38, 1), (40, 1), (46, 1), (47, 1), (48, 1)] }, { coefficient := -1, powers := [(24, 1), (27, 1), (40, 1), (43, 1), (46, 1), (47, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (13, 1), (24, 1), (40, 1), (47, 1), (56, 1)] }, { coefficient := -1, powers := [(19, 1), (20, 1), (24, 1), (40, 1), (47, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (23, 1), (24, 1), (40, 1), (47, 1)] }],
  [{ coefficient := 2, powers := [(13, 1), (24, 1), (27, 1), (40, 1), (47, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (24, 1), (40, 1), (47, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (30, 1), (34, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (33, 1), (34, 1), (53, 1)] }, { coefficient := 1, powers := [(3, 1), (24, 1), (30, 1), (56, 1)] }, { coefficient := 1, powers := [(3, 1), (24, 1), (33, 1), (53, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1), (30, 1), (56, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1), (33, 1), (53, 1)] }],
  [{ coefficient := 2, powers := [(9, 1), (19, 1), (24, 2), (40, 1), (50, 1), (53, 1)] }, { coefficient := -2, powers := [(9, 1), (19, 1), (24, 1), (40, 1), (53, 1)] }, { coefficient := -1, powers := [(13, 1), (24, 1), (40, 1), (47, 1), (56, 1)] }, { coefficient := -2, powers := [(14, 1), (19, 1), (20, 1), (47, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (23, 1), (34, 1), (59, 1)] }, { coefficient := 2, powers := [(0, 1), (30, 1), (34, 1), (46, 1)] }, { coefficient := 1, powers := [(3, 1), (23, 1), (24, 1), (59, 1)] }, { coefficient := 2, powers := [(3, 1), (24, 1), (30, 1), (46, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1), (23, 1), (59, 1)] }, { coefficient := 2, powers := [(6, 1), (20, 1), (30, 1), (46, 1)] }],
  [{ coefficient := 2, powers := [(20, 1), (27, 1), (46, 1), (47, 1)] }],
  [{ coefficient := -2, powers := [(9, 1), (20, 1), (27, 1), (46, 1), (54, 1)] }, { coefficient := 2, powers := [(20, 1), (24, 1), (27, 1), (40, 1), (46, 1), (47, 1), (50, 1)] }, { coefficient := -1, powers := [(24, 1), (27, 1), (40, 1), (46, 1), (47, 1)] }],
  [{ coefficient := -2, powers := [(9, 1), (23, 1), (53, 1), (54, 1)] }, { coefficient := 1, powers := [(23, 1), (24, 1), (38, 1), (40, 1), (47, 1), (53, 1)] }, { coefficient := 1, powers := [(23, 1), (24, 1), (40, 1), (43, 1), (47, 1), (53, 1)] }, { coefficient := 2, powers := [(23, 1), (24, 1), (40, 1), (47, 1), (50, 1), (53, 1)] }],
  [{ coefficient := -2, powers := [(20, 1), (27, 1), (46, 1), (47, 1), (48, 1)] }],
  [{ coefficient := 2, powers := [(9, 1), (18, 1), (23, 1), (24, 1), (53, 1), (54, 1), (60, 1)] }, { coefficient := -2, powers := [(18, 1), (23, 1), (24, 2), (40, 1), (47, 1), (50, 1), (53, 1), (60, 1)] }],
  [{ coefficient := 2, powers := [(18, 1), (20, 1), (27, 1), (46, 1), (47, 1), (54, 1), (60, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (9, 1), (24, 2), (40, 1), (43, 1), (50, 1), (53, 1)] }, { coefficient := -2, powers := [(0, 1), (9, 1), (24, 1), (40, 1), (43, 1), (53, 1)] }, { coefficient := -2, powers := [(0, 1), (14, 1), (20, 1), (43, 1), (47, 1), (53, 1)] }, { coefficient := -1, powers := [(0, 1), (24, 1), (40, 1), (47, 1), (50, 1), (53, 1)] }, { coefficient := 1, powers := [(3, 1), (28, 1), (53, 1), (54, 1)] }, { coefficient := -1, powers := [(6, 1), (24, 1), (28, 1), (40, 1), (50, 1), (53, 1)] }, { coefficient := 1, powers := [(6, 1), (28, 1), (40, 1), (53, 1)] }, { coefficient := 1, powers := [(9, 1), (20, 1), (53, 1), (54, 1)] }, { coefficient := 2, powers := [(9, 1), (24, 3), (38, 1), (40, 1), (50, 1), (53, 1)] }, { coefficient := 2, powers := [(9, 1), (24, 3), (40, 1), (43, 1), (50, 1), (53, 1)] }, { coefficient := -2, powers := [(9, 1), (24, 2), (38, 1), (40, 1), (53, 1)] }, { coefficient := -2, powers := [(9, 1), (24, 2), (40, 1), (43, 1), (53, 1)] }, { coefficient := 1, powers := [(9, 1), (24, 2), (40, 1), (50, 1), (53, 1)] }, { coefficient := -1, powers := [(9, 1), (24, 1), (40, 1), (53, 1)] }, { coefficient := -1, powers := [(9, 1), (31, 1), (34, 1), (53, 1)] }, { coefficient := -2, powers := [(14, 1), (20, 1), (24, 1), (38, 1), (47, 1), (53, 1)] }, { coefficient := -2, powers := [(14, 1), (20, 1), (24, 1), (43, 1), (47, 1), (53, 1)] }, { coefficient := -2, powers := [(14, 1), (20, 1), (47, 1), (53, 1)] }, { coefficient := 1, powers := [(14, 1), (28, 1), (34, 1), (53, 1)] }, { coefficient := -1, powers := [(20, 1), (24, 1), (40, 1), (47, 1), (50, 1), (53, 1)] }, { coefficient := 1, powers := [(20, 1), (24, 1), (40, 1), (47, 1), (53, 1), (55, 1)] }, { coefficient := -1, powers := [(20, 1), (47, 1), (53, 1), (54, 1)] }, { coefficient := -1, powers := [(24, 1), (28, 1), (34, 1), (40, 1), (50, 1), (53, 1)] }, { coefficient := 1, powers := [(31, 1), (34, 1), (47, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (24, 1), (40, 1), (46, 1), (47, 1), (50, 1)] }, { coefficient := -1, powers := [(0, 1), (34, 1), (46, 1), (57, 1)] }, { coefficient := -1, powers := [(3, 1), (24, 1), (46, 1), (57, 1)] }, { coefficient := -1, powers := [(3, 1), (28, 1), (46, 1), (54, 1)] }, { coefficient := -1, powers := [(6, 1), (20, 1), (46, 1), (57, 1)] }, { coefficient := 1, powers := [(6, 1), (24, 1), (28, 1), (40, 1), (46, 1), (50, 1)] }, { coefficient := -1, powers := [(6, 1), (28, 1), (40, 1), (46, 1)] }, { coefficient := 1, powers := [(9, 1), (20, 1), (46, 1), (54, 1)] }, { coefficient := -1, powers := [(9, 1), (24, 2), (40, 1), (46, 1), (50, 1)] }, { coefficient := 1, powers := [(9, 1), (24, 1), (40, 1), (46, 1)] }, { coefficient := 1, powers := [(9, 1), (31, 1), (34, 1), (46, 1)] }, { coefficient := -1, powers := [(14, 1), (28, 1), (34, 1), (46, 1)] }, { coefficient := -1, powers := [(20, 1), (24, 1), (40, 1), (46, 1), (47, 1), (50, 1)] }, { coefficient := -1, powers := [(20, 1), (46, 1), (47, 1), (54, 1)] }, { coefficient := 1, powers := [(24, 1), (28, 1), (34, 1), (40, 1), (46, 1), (50, 1)] }, { coefficient := -1, powers := [(24, 1), (40, 1), (46, 1), (47, 1)] }, { coefficient := -1, powers := [(31, 1), (34, 1), (46, 1), (47, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (9, 1), (20, 1), (27, 1), (43, 1), (54, 1)] }, { coefficient := 2, powers := [(0, 1), (20, 1), (24, 1), (27, 1), (40, 1), (43, 1), (47, 1), (50, 1)] }, { coefficient := -1, powers := [(0, 1), (24, 1), (27, 1), (40, 1), (43, 1), (47, 1)] }, { coefficient := -1, powers := [(0, 1), (24, 1), (27, 1), (40, 1), (47, 1), (50, 1)] }, { coefficient := 1, powers := [(0, 1), (27, 1), (34, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (24, 1), (27, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (27, 1), (28, 1), (54, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1), (27, 1), (57, 1)] }, { coefficient := -1, powers := [(6, 1), (24, 1), (27, 1), (28, 1), (40, 1), (50, 1)] }, { coefficient := 1, powers := [(6, 1), (27, 1), (28, 1), (40, 1)] }, { coefficient := -2, powers := [(9, 1), (20, 1), (24, 1), (27, 1), (38, 1), (54, 1)] }, { coefficient := -2, powers := [(9, 1), (20, 1), (24, 1), (27, 1), (43, 1), (54, 1)] }, { coefficient := -1, powers := [(9, 1), (20, 1), (27, 1), (54, 1)] }, { coefficient := -1, powers := [(9, 1), (24, 2), (27, 1), (40, 1), (50, 1)] }, { coefficient := 1, powers := [(9, 1), (24, 1), (27, 1), (40, 1)] }, { coefficient := 1, powers := [(14, 1), (27, 1), (28, 1), (34, 1)] }, { coefficient := 2, powers := [(20, 1), (24, 2), (27, 1), (38, 1), (40, 1), (47, 1), (50, 1)] }, { coefficient := 2, powers := [(20, 1), (24, 2), (27, 1), (40, 1), (43, 1), (47, 1), (50, 1)] }, { coefficient := 1, powers := [(20, 1), (24, 1), (27, 1), (40, 1), (47, 1), (50, 1)] }, { coefficient := -1, powers := [(20, 1), (27, 1), (47, 1), (54, 1)] }, { coefficient := -1, powers := [(24, 2), (27, 1), (38, 1), (40, 1), (47, 1)] }, { coefficient := -1, powers := [(24, 2), (27, 1), (40, 1), (43, 1), (47, 1)] }, { coefficient := -1, powers := [(24, 1), (27, 1), (28, 1), (34, 1), (40, 1), (50, 1)] }, { coefficient := -1, powers := [(24, 1), (27, 1), (40, 1), (47, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (23, 1), (24, 1), (40, 1), (47, 1), (50, 1)] }, { coefficient := 1, powers := [(9, 1), (20, 1), (23, 1), (54, 1)] }, { coefficient := -1, powers := [(9, 1), (23, 1), (24, 2), (40, 1), (50, 1)] }, { coefficient := 1, powers := [(9, 1), (23, 1), (24, 1), (40, 1)] }, { coefficient := 1, powers := [(9, 1), (23, 1), (31, 1), (34, 1)] }, { coefficient := -1, powers := [(20, 1), (23, 1), (24, 1), (40, 1), (47, 1), (50, 1)] }, { coefficient := -1, powers := [(20, 1), (23, 1), (47, 1), (54, 1)] }, { coefficient := -1, powers := [(23, 1), (24, 1), (40, 1), (47, 1)] }, { coefficient := -1, powers := [(23, 1), (31, 1), (34, 1), (47, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (23, 1), (24, 1), (40, 1), (47, 1), (56, 1)] }, { coefficient := -1, powers := [(20, 1), (23, 1), (24, 1), (40, 1), (47, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [(20, 1), (23, 1), (24, 1), (40, 1), (47, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (9, 1), (30, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (24, 1), (30, 1), (40, 1), (47, 1), (55, 1)] }, { coefficient := -1, powers := [(9, 1), (13, 1), (23, 1), (54, 1)] }, { coefficient := 1, powers := [(13, 1), (23, 1), (24, 1), (40, 1), (43, 1), (47, 1)] }, { coefficient := 1, powers := [(13, 1), (23, 1), (24, 1), (40, 1), (47, 1), (50, 1)] }],
  [{ coefficient := -2, powers := [(9, 1), (18, 1), (20, 1), (27, 1), (41, 1), (45, 1), (54, 1)] }, { coefficient := 2, powers := [(18, 1), (20, 1), (24, 1), (27, 1), (40, 1), (41, 1), (45, 1), (47, 1), (50, 1)] }, { coefficient := -1, powers := [(18, 1), (24, 1), (27, 1), (40, 1), (41, 1), (45, 1), (47, 1)] }],
  [{ coefficient := -1, powers := [(20, 1), (47, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (30, 1), (54, 1)] }, { coefficient := -1, powers := [(6, 1), (24, 1), (30, 1), (40, 1), (50, 1)] }, { coefficient := 1, powers := [(6, 1), (30, 1), (40, 1)] }, { coefficient := 1, powers := [(14, 1), (30, 1), (34, 1)] }, { coefficient := -1, powers := [(24, 1), (30, 1), (34, 1), (40, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (24, 1), (40, 1), (47, 1), (56, 1)] }],
  [{ coefficient := 2, powers := [(9, 1), (20, 1), (27, 1), (46, 1), (48, 1), (54, 1)] }, { coefficient := -2, powers := [(20, 1), (24, 1), (27, 1), (40, 1), (46, 1), (47, 1), (48, 1), (50, 1)] }, { coefficient := -1, powers := [(23, 1), (24, 1), (40, 1), (41, 1), (47, 1), (53, 1)] }, { coefficient := -1, powers := [(23, 1), (24, 1), (40, 1), (47, 1), (48, 1), (56, 1)] }, { coefficient := 1, powers := [(24, 1), (27, 1), (40, 1), (46, 1), (47, 1), (48, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (19, 1), (24, 1), (40, 1), (47, 1), (50, 1)] }, { coefficient := 1, powers := [(0, 1), (19, 1), (34, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (19, 1), (24, 1), (57, 1)] }, { coefficient := 1, powers := [(6, 1), (19, 1), (20, 1), (57, 1)] }, { coefficient := 1, powers := [(9, 1), (19, 1), (20, 1), (54, 1)] }, { coefficient := -1, powers := [(9, 1), (19, 1), (24, 2), (40, 1), (50, 1)] }, { coefficient := 1, powers := [(9, 1), (19, 1), (24, 1), (40, 1)] }, { coefficient := 1, powers := [(9, 1), (19, 1), (31, 1), (34, 1)] }, { coefficient := -1, powers := [(19, 1), (20, 1), (24, 1), (40, 1), (47, 1), (50, 1)] }, { coefficient := -1, powers := [(19, 1), (20, 1), (47, 1), (54, 1)] }, { coefficient := -1, powers := [(19, 1), (24, 1), (40, 1), (47, 1)] }, { coefficient := -1, powers := [(19, 1), (31, 1), (34, 1), (47, 1)] }],
  [{ coefficient := 2, powers := [(9, 1), (18, 1), (20, 1), (27, 1), (45, 1), (54, 1)] }, { coefficient := -2, powers := [(18, 1), (20, 1), (24, 1), (27, 1), (40, 1), (45, 1), (47, 1), (50, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (27, 1), (40, 1), (45, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (24, 1), (40, 1), (47, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (13, 1), (24, 1), (40, 1), (47, 1), (50, 1)] }, { coefficient := 1, powers := [(0, 1), (13, 1), (34, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (13, 1), (24, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (13, 1), (28, 1), (54, 1)] }, { coefficient := 1, powers := [(6, 1), (13, 1), (20, 1), (57, 1)] }, { coefficient := -1, powers := [(6, 1), (13, 1), (24, 1), (28, 1), (40, 1), (50, 1)] }, { coefficient := 1, powers := [(6, 1), (13, 1), (28, 1), (40, 1)] }, { coefficient := 1, powers := [(9, 1), (13, 1), (20, 1), (54, 1)] }, { coefficient := -1, powers := [(9, 1), (13, 1), (24, 2), (40, 1), (50, 1)] }, { coefficient := 1, powers := [(9, 1), (13, 1), (24, 1), (40, 1)] }, { coefficient := 1, powers := [(13, 1), (14, 1), (28, 1), (34, 1)] }, { coefficient := -1, powers := [(13, 1), (20, 1), (24, 1), (40, 1), (47, 1), (50, 1)] }, { coefficient := -1, powers := [(13, 1), (20, 1), (47, 1), (54, 1)] }, { coefficient := -1, powers := [(13, 1), (24, 1), (28, 1), (34, 1), (40, 1), (50, 1)] }, { coefficient := -1, powers := [(13, 1), (24, 1), (40, 1), (47, 1)] }],
  [{ coefficient := 2, powers := [(5, 1), (9, 1), (20, 1), (27, 1), (54, 1), (59, 1)] }, { coefficient := -2, powers := [(5, 1), (9, 1), (24, 2), (33, 1), (40, 1), (50, 1), (53, 1)] }, { coefficient := 2, powers := [(5, 1), (9, 1), (24, 1), (33, 1), (40, 1), (53, 1)] }, { coefficient := 2, powers := [(5, 1), (14, 1), (20, 1), (33, 1), (47, 1), (53, 1)] }, { coefficient := -2, powers := [(5, 1), (20, 1), (24, 1), (27, 1), (40, 1), (47, 1), (50, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (24, 1), (27, 1), (40, 1), (47, 1), (59, 1)] }, { coefficient := -2, powers := [(9, 1), (19, 1), (23, 1), (24, 2), (40, 1), (50, 1), (53, 1)] }, { coefficient := 2, powers := [(9, 1), (19, 1), (23, 1), (24, 1), (40, 1), (53, 1)] }, { coefficient := 1, powers := [(13, 1), (23, 1), (24, 1), (40, 1), (47, 1), (56, 1)] }, { coefficient := 2, powers := [(14, 1), (19, 1), (20, 1), (23, 1), (47, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (24, 1), (30, 1), (40, 1), (47, 1), (56, 1)] }, { coefficient := -1, powers := [(5, 1), (24, 1), (33, 1), (40, 1), (47, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(47, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (40, 1), (50, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (24, 1), (40, 1), (47, 1), (50, 1)] }, { coefficient := -1, powers := [(0, 1), (34, 1), (57, 1)] }, { coefficient := -1, powers := [(3, 1), (24, 1), (57, 1)] }, { coefficient := -1, powers := [(3, 1), (28, 1), (54, 1)] }, { coefficient := -1, powers := [(6, 1), (20, 1), (57, 1)] }, { coefficient := 1, powers := [(6, 1), (24, 1), (28, 1), (40, 1), (50, 1)] }, { coefficient := -1, powers := [(6, 1), (28, 1), (40, 1)] }, { coefficient := -1, powers := [(9, 1), (20, 1), (54, 1)] }, { coefficient := 1, powers := [(9, 1), (24, 2), (40, 1), (50, 1)] }, { coefficient := -1, powers := [(9, 1), (24, 1), (40, 1)] }, { coefficient := -1, powers := [(9, 1), (31, 1), (34, 1)] }, { coefficient := -1, powers := [(14, 1), (28, 1), (34, 1)] }, { coefficient := 1, powers := [(20, 1), (24, 1), (40, 1), (47, 1), (50, 1)] }, { coefficient := 1, powers := [(20, 1), (47, 1), (54, 1)] }, { coefficient := 1, powers := [(24, 1), (28, 1), (34, 1), (40, 1), (50, 1)] }, { coefficient := 1, powers := [(24, 1), (40, 1), (47, 1)] }, { coefficient := 1, powers := [(31, 1), (34, 1), (47, 1)] }],
  [{ coefficient := -2, powers := [(9, 1), (18, 1), (23, 1), (24, 1), (41, 1), (53, 1), (54, 1)] }, { coefficient := -2, powers := [(18, 1), (20, 1), (27, 1), (46, 1), (47, 1), (48, 1), (54, 1)] }, { coefficient := 2, powers := [(18, 1), (23, 1), (24, 2), (40, 1), (41, 1), (47, 1), (50, 1), (53, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (9, 1), (24, 2), (40, 1), (43, 1), (46, 1), (50, 1), (53, 1)] }, { coefficient := 2, powers := [(0, 1), (9, 1), (24, 1), (40, 1), (43, 1), (46, 1), (53, 1)] }, { coefficient := 2, powers := [(0, 1), (14, 1), (20, 1), (43, 1), (46, 1), (47, 1), (53, 1)] }, { coefficient := -1, powers := [(0, 1), (24, 1), (36, 1), (40, 1), (47, 1), (50, 1), (59, 1)] }, { coefficient := -1, powers := [(0, 1), (24, 1), (39, 1), (40, 1), (47, 1), (50, 1), (56, 1)] }, { coefficient := -1, powers := [(0, 1), (24, 1), (40, 1), (45, 1), (47, 1), (51, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (24, 1), (40, 1), (46, 1), (47, 1), (50, 1), (53, 1)] }, { coefficient := 1, powers := [(0, 1), (34, 1), (36, 1), (57, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (34, 1), (39, 1), (56, 1), (57, 1)] }, { coefficient := 2, powers := [(0, 1), (34, 1), (46, 1), (53, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (24, 1), (36, 1), (57, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (24, 1), (39, 1), (56, 1), (57, 1)] }, { coefficient := 2, powers := [(3, 1), (24, 1), (46, 1), (53, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (28, 1), (36, 1), (54, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (28, 1), (39, 1), (54, 1), (56, 1)] }, { coefficient := 1, powers := [(3, 1), (28, 1), (46, 1), (53, 1), (54, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1), (36, 1), (57, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1), (39, 1), (56, 1), (57, 1)] }, { coefficient := 2, powers := [(6, 1), (20, 1), (46, 1), (53, 1), (57, 1)] }, { coefficient := -1, powers := [(6, 1), (24, 1), (28, 1), (36, 1), (40, 1), (50, 1), (59, 1)] }, { coefficient := -1, powers := [(6, 1), (24, 1), (28, 1), (39, 1), (40, 1), (50, 1), (56, 1)] }, { coefficient := -1, powers := [(6, 1), (24, 1), (28, 1), (40, 1), (46, 1), (50, 1), (53, 1)] }, { coefficient := 1, powers := [(6, 1), (28, 1), (36, 1), (40, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (28, 1), (39, 1), (40, 1), (56, 1)] }, { coefficient := 1, powers := [(6, 1), (28, 1), (40, 1), (46, 1), (53, 1)] }, { coefficient := 1, powers := [(9, 1), (20, 1), (36, 1), (54, 1), (59, 1)] }, { coefficient := 1, powers := [(9, 1), (20, 1), (39, 1), (54, 1), (56, 1)] }, { coefficient := -1, powers := [(9, 1), (20, 1), (46, 1), (53, 1), (54, 1)] }, { coefficient := -2, powers := [(9, 1), (24, 3), (38, 1), (40, 1), (46, 1), (50, 1), (53, 1)] }, { coefficient := -2, powers := [(9, 1), (24, 3), (40, 1), (43, 1), (46, 1), (50, 1), (53, 1)] }, { coefficient := -1, powers := [(9, 1), (24, 2), (36, 1), (40, 1), (50, 1), (59, 1)] }, { coefficient := 2, powers := [(9, 1), (24, 2), (38, 1), (40, 1), (46, 1), (53, 1)] }, { coefficient := -1, powers := [(9, 1), (24, 2), (39, 1), (40, 1), (50, 1), (56, 1)] }, { coefficient := 2, powers := [(9, 1), (24, 2), (40, 1), (43, 1), (46, 1), (53, 1)] }, { coefficient := -1, powers := [(9, 1), (24, 2), (40, 1), (46, 1), (50, 1), (53, 1)] }, { coefficient := 1, powers := [(9, 1), (24, 1), (36, 1), (40, 1), (59, 1)] }, { coefficient := 1, powers := [(9, 1), (24, 1), (39, 1), (40, 1), (56, 1)] }, { coefficient := 1, powers := [(9, 1), (24, 1), (40, 1), (46, 1), (53, 1)] }, { coefficient := 1, powers := [(9, 1), (31, 1), (34, 1), (36, 1), (59, 1)] }, { coefficient := 1, powers := [(9, 1), (31, 1), (34, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(9, 1), (31, 1), (34, 1), (46, 1), (53, 1)] }, { coefficient := 2, powers := [(14, 1), (20, 1), (24, 1), (38, 1), (46, 1), (47, 1), (53, 1)] }, { coefficient := 2, powers := [(14, 1), (20, 1), (24, 1), (43, 1), (46, 1), (47, 1), (53, 1)] }, { coefficient := 2, powers := [(14, 1), (20, 1), (46, 1), (47, 1), (53, 1)] }, { coefficient := 1, powers := [(14, 1), (28, 1), (34, 1), (36, 1), (59, 1)] }, { coefficient := 1, powers := [(14, 1), (28, 1), (34, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(14, 1), (28, 1), (34, 1), (46, 1), (53, 1)] }, { coefficient := -1, powers := [(20, 1), (24, 1), (36, 1), (40, 1), (47, 1), (50, 1), (59, 1)] }, { coefficient := -1, powers := [(20, 1), (24, 1), (39, 1), (40, 1), (47, 1), (50, 1), (56, 1)] }, { coefficient := 1, powers := [(20, 1), (24, 1), (40, 1), (46, 1), (47, 1), (50, 1), (53, 1)] }, { coefficient := -1, powers := [(20, 1), (24, 1), (40, 1), (46, 1), (47, 1), (53, 1), (55, 1)] }, { coefficient := -1, powers := [(20, 1), (36, 1), (47, 1), (54, 1), (59, 1)] }, { coefficient := 1, powers := [(20, 1), (46, 1), (47, 1), (53, 1), (54, 1)] }, { coefficient := -1, powers := [(24, 1), (28, 1), (34, 1), (36, 1), (40, 1), (50, 1), (59, 1)] }, { coefficient := -1, powers := [(24, 1), (28, 1), (34, 1), (39, 1), (40, 1), (50, 1), (56, 1)] }, { coefficient := -1, powers := [(24, 1), (28, 1), (34, 1), (40, 1), (46, 1), (50, 1), (53, 1)] }, { coefficient := -1, powers := [(24, 1), (36, 1), (40, 1), (47, 1), (59, 1)] }, { coefficient := -1, powers := [(24, 1), (39, 1), (40, 1), (47, 1), (56, 1)] }, { coefficient := -1, powers := [(24, 1), (40, 1), (45, 1), (47, 1), (48, 1), (56, 1)] }, { coefficient := -1, powers := [(31, 1), (34, 1), (36, 1), (47, 1), (59, 1)] }, { coefficient := -1, powers := [(31, 1), (34, 1), (39, 1), (47, 1), (56, 1)] }, { coefficient := -1, powers := [(31, 1), (34, 1), (46, 1), (47, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (54, 1)] }, { coefficient := 1, powers := [(6, 1), (31, 1)] }, { coefficient := -2, powers := [(13, 1), (24, 2), (27, 1), (40, 1), (46, 1), (50, 1)] }, { coefficient := 2, powers := [(13, 1), (24, 1), (27, 1), (40, 1), (46, 1)] }, { coefficient := 1, powers := [(14, 1), (24, 1)] }, { coefficient := -1, powers := [(24, 2), (40, 1), (50, 1)] }],
  [{ coefficient := 2, powers := [(6, 1), (9, 1), (18, 1), (24, 2), (33, 1), (40, 1), (45, 1), (50, 1), (53, 1)] }, { coefficient := -2, powers := [(6, 1), (9, 1), (18, 1), (24, 1), (33, 1), (40, 1), (45, 1), (53, 1)] }, { coefficient := -2, powers := [(6, 1), (14, 1), (18, 1), (20, 1), (33, 1), (45, 1), (47, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (8, 1), (24, 1), (33, 1), (40, 1), (47, 1), (50, 1)] }, { coefficient := 1, powers := [(0, 1), (8, 1), (33, 1), (34, 1), (57, 1)] }, { coefficient := 2, powers := [(0, 1), (9, 1), (19, 1), (20, 1), (27, 1), (43, 1), (54, 1)] }, { coefficient := -2, powers := [(0, 1), (19, 1), (20, 1), (24, 1), (27, 1), (40, 1), (43, 1), (47, 1), (50, 1)] }, { coefficient := 1, powers := [(0, 1), (19, 1), (24, 1), (27, 1), (40, 1), (43, 1), (47, 1)] }, { coefficient := 1, powers := [(0, 1), (19, 1), (24, 1), (27, 1), (40, 1), (47, 1), (50, 1)] }, { coefficient := -1, powers := [(0, 1), (19, 1), (27, 1), (34, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (8, 1), (24, 1), (33, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (8, 1), (28, 1), (33, 1), (54, 1)] }, { coefficient := -1, powers := [(3, 1), (19, 1), (24, 1), (27, 1), (57, 1)] }, { coefficient := 1, powers := [(6, 1), (8, 1), (20, 1), (33, 1), (57, 1)] }, { coefficient := -1, powers := [(6, 1), (8, 1), (24, 1), (28, 1), (33, 1), (40, 1), (50, 1)] }, { coefficient := 1, powers := [(6, 1), (8, 1), (28, 1), (33, 1), (40, 1)] }, { coefficient := -1, powers := [(6, 1), (19, 1), (20, 1), (27, 1), (57, 1)] }, { coefficient := 1, powers := [(8, 1), (9, 1), (20, 1), (33, 1), (54, 1)] }, { coefficient := -1, powers := [(8, 1), (9, 1), (24, 2), (33, 1), (40, 1), (50, 1)] }, { coefficient := 1, powers := [(8, 1), (9, 1), (24, 1), (33, 1), (40, 1)] }, { coefficient := 1, powers := [(8, 1), (9, 1), (31, 1), (33, 1), (34, 1)] }, { coefficient := 1, powers := [(8, 1), (14, 1), (28, 1), (33, 1), (34, 1)] }, { coefficient := -1, powers := [(8, 1), (20, 1), (24, 1), (33, 1), (40, 1), (47, 1), (50, 1)] }, { coefficient := -1, powers := [(8, 1), (20, 1), (33, 1), (47, 1), (54, 1)] }, { coefficient := -1, powers := [(8, 1), (24, 1), (28, 1), (33, 1), (34, 1), (40, 1), (50, 1)] }, { coefficient := -1, powers := [(8, 1), (24, 1), (33, 1), (40, 1), (47, 1)] }, { coefficient := -1, powers := [(8, 1), (31, 1), (33, 1), (34, 1), (47, 1)] }, { coefficient := 2, powers := [(9, 1), (19, 1), (20, 1), (24, 1), (27, 1), (38, 1), (54, 1)] }, { coefficient := 2, powers := [(9, 1), (19, 1), (20, 1), (24, 1), (27, 1), (43, 1), (54, 1)] }, { coefficient := 1, powers := [(9, 1), (19, 1), (20, 1), (27, 1), (54, 1)] }, { coefficient := 1, powers := [(9, 1), (19, 1), (24, 2), (27, 1), (40, 1), (50, 1)] }, { coefficient := -1, powers := [(9, 1), (19, 1), (24, 1), (27, 1), (40, 1)] }, { coefficient := -2, powers := [(19, 1), (20, 1), (24, 2), (27, 1), (38, 1), (40, 1), (47, 1), (50, 1)] }, { coefficient := -2, powers := [(19, 1), (20, 1), (24, 2), (27, 1), (40, 1), (43, 1), (47, 1), (50, 1)] }, { coefficient := -1, powers := [(19, 1), (20, 1), (24, 1), (27, 1), (40, 1), (47, 1), (50, 1)] }, { coefficient := 1, powers := [(19, 1), (20, 1), (27, 1), (47, 1), (54, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 2), (27, 1), (38, 1), (40, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 2), (27, 1), (40, 1), (43, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (27, 1), (40, 1), (47, 1)] }]
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
    (values : Fin 62 → R) :
    ¬ ∀ index : Fin 59,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component64.SelectedLeafB4_2.selectedHasNoCommonZero

end Krenn.Component64.SelectedLeafB4_2
