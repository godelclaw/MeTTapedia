import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.FrozenCase0NoncollapseType01Chart3B0Z1W14ZeroCertificate

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "1df070152f8c6a026c39ad06c62d011828f019a740ede6f28da75547beb35377"
def certificateSHA256 : String := "0894996ee3f1d2dbab2be13a7fbcba520ecf7343ea211a248ca2e35f845c1691"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 39 → Fin 508 := ![
  13,
  31,
  40,
  43,
  59,
  71,
  82,
  86,
  97,
  123,
  253,
  254,
  340,
  343,
  349,
  352,
  361,
  368,
  370,
  376,
  379,
  380,
  386,
  388,
  389,
  395,
  407,
  418,
  427,
  433,
  451,
  460,
  497,
  500,
  501,
  503,
  504,
  505,
  507
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 39 → SparsePoly (Fin 64) := ![
  [{ coefficient := 1, powers := [(5, 1), (52, 1)] }, { coefficient := 1, powers := [(7, 1), (61, 1)] }, { coefficient := 1, powers := [(24, 1), (52, 1)] }, { coefficient := 1, powers := [(24, 1), (58, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := -1, powers := [(5, 1), (40, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := -1, powers := [(5, 1), (40, 1), (52, 1)] }, { coefficient := 1, powers := [(5, 1), (40, 1), (58, 1)] }, { coefficient := 1, powers := [(52, 1)] }, { coefficient := 1, powers := [(58, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (40, 1), (53, 1)] }, { coefficient := -1, powers := [(10, 1), (40, 1)] }, { coefficient := 1, powers := [(10, 1), (58, 1)] }, { coefficient := 1, powers := [(53, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (48, 1)] }, { coefficient := 1, powers := [(18, 1), (25, 1)] }, { coefficient := 1, powers := [(28, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (48, 1), (53, 1)] }, { coefficient := 1, powers := [(10, 1), (48, 1)] }, { coefficient := 1, powers := [(18, 1), (25, 1), (53, 1)] }, { coefficient := 1, powers := [(18, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (36, 1)] }, { coefficient := 1, powers := [(36, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (36, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (30, 1)] }, { coefficient := 1, powers := [(26, 1), (50, 1)] }, { coefficient := 1, powers := [(34, 1), (38, 1)] }],
  [{ coefficient := -1, powers := [(10, 1), (30, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (36, 1), (40, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(8, 1), (36, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (24, 1)] }, { coefficient := 1, powers := [(15, 1), (24, 1)] }, { coefficient := 1, powers := [(15, 1), (28, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (24, 1), (50, 1)] }, { coefficient := 1, powers := [(15, 1), (24, 1), (50, 1)] }, { coefficient := 1, powers := [(16, 1), (28, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (24, 1), (52, 1)] }, { coefficient := 1, powers := [(15, 1), (24, 1), (52, 1)] }, { coefficient := 1, powers := [(15, 1), (24, 1), (58, 1)] }, { coefficient := 1, powers := [(15, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (24, 1), (53, 1)] }, { coefficient := 1, powers := [(15, 1), (24, 1), (53, 1)] }, { coefficient := 1, powers := [(16, 1), (24, 1), (58, 1)] }, { coefficient := 1, powers := [(16, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (24, 1), (56, 1)] }, { coefficient := 1, powers := [(15, 1), (24, 1), (56, 1)] }, { coefficient := 1, powers := [(16, 1), (29, 1)] }],
  [{ coefficient := 1, powers := [(15, 1), (28, 1), (45, 1)] }, { coefficient := 1, powers := [(23, 1), (28, 1), (40, 1)] }, { coefficient := 1, powers := [(23, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (50, 1)] }, { coefficient := 1, powers := [(15, 1), (50, 1)] }, { coefficient := -1, powers := [(16, 1), (28, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (40, 1)] }, { coefficient := 1, powers := [(1, 1), (52, 1)] }, { coefficient := 1, powers := [(15, 1), (52, 1)] }, { coefficient := 1, powers := [(15, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (53, 1)] }, { coefficient := 1, powers := [(15, 1), (53, 1)] }, { coefficient := -1, powers := [(16, 1), (40, 1)] }, { coefficient := 1, powers := [(16, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (45, 1)] }, { coefficient := 1, powers := [(23, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(15, 1), (29, 1), (45, 1)] }, { coefficient := 1, powers := [(15, 1), (59, 1)] }, { coefficient := 1, powers := [(23, 1), (29, 1), (40, 1)] }, { coefficient := 1, powers := [(23, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (56, 1)] }, { coefficient := 1, powers := [(15, 1), (56, 1)] }, { coefficient := -1, powers := [(16, 1), (29, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (29, 1), (45, 1)] }, { coefficient := 1, powers := [(16, 1), (59, 1)] }, { coefficient := 1, powers := [(23, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(15, 1), (28, 1), (48, 1)] }, { coefficient := 1, powers := [(23, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (48, 1)] }, { coefficient := 1, powers := [(23, 1), (25, 1), (53, 1)] }, { coefficient := 1, powers := [(23, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(15, 1), (36, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (26, 1), (50, 1)] }, { coefficient := 1, powers := [(1, 1), (34, 1), (38, 1)] }, { coefficient := 1, powers := [(6, 1), (50, 1)] }, { coefficient := 1, powers := [(15, 1), (26, 1), (50, 1)] }, { coefficient := 1, powers := [(15, 1), (34, 1), (38, 1)] }, { coefficient := 1, powers := [(16, 1), (30, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (26, 1), (52, 1)] }, { coefficient := 1, powers := [(6, 1), (52, 1)] }, { coefficient := 1, powers := [(15, 1), (26, 1), (52, 1)] }, { coefficient := 1, powers := [(15, 1), (26, 1), (58, 1)] }, { coefficient := 1, powers := [(15, 1), (31, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (30, 1), (40, 1)] }, { coefficient := -1, powers := [(6, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (31, 1), (40, 1)] }, { coefficient := -1, powers := [(6, 1), (40, 1), (52, 1)] }, { coefficient := 1, powers := [(6, 1), (40, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (48, 1), (55, 1)] }, { coefficient := 1, powers := [(15, 1), (27, 1), (59, 1)] }, { coefficient := 1, powers := [(15, 1), (32, 1), (48, 1)] }, { coefficient := 1, powers := [(23, 1), (27, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (41, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (48, 1), (56, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1), (59, 1)] }, { coefficient := 1, powers := [(16, 1), (32, 1), (48, 1)] }, { coefficient := 1, powers := [(23, 1), (27, 1), (56, 1)] }, { coefficient := 1, powers := [(23, 1), (32, 1), (41, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1), (4, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1), (24, 1), (52, 1)] }, { coefficient := 1, powers := [(1, 1), (28, 1), (52, 1)] }, { coefficient := -1, powers := [(1, 1)] }, { coefficient := 1, powers := [(15, 1), (24, 1), (52, 1)] }, { coefficient := 1, powers := [(15, 1), (24, 1), (58, 1)] }, { coefficient := 1, powers := [(15, 1), (28, 1), (52, 1)] }, { coefficient := 1, powers := [(15, 1), (28, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (24, 1)] }, { coefficient := 1, powers := [(3, 1), (28, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1), (2, 1), (40, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(36, 1), (63, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 39 → SparsePoly (Fin 64) := ![
  [{ coefficient := -2, powers := [(1, 2), (2, 1), (29, 1), (31, 1), (48, 1), (53, 1)] }, { coefficient := -2, powers := [(1, 1), (2, 1), (15, 1), (29, 1), (31, 1), (48, 1), (53, 1)] }, { coefficient := -2, powers := [(1, 1), (2, 1), (16, 1), (29, 1), (31, 1), (48, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(1, 1), (2, 1), (7, 1), (16, 1), (29, 1), (31, 1), (48, 1), (52, 1), (61, 1)] }, { coefficient := 1, powers := [(1, 1), (2, 1), (7, 1), (16, 1), (29, 1), (31, 1), (48, 1), (58, 1), (61, 1)] }, { coefficient := -1, powers := [(1, 1), (2, 1), (16, 1), (29, 1), (31, 1), (48, 1), (52, 1)] }, { coefficient := -1, powers := [(1, 1), (2, 1), (16, 1), (29, 1), (31, 1), (48, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (6, 1), (16, 1), (29, 1), (40, 1), (48, 1), (52, 1)] }, { coefficient := -1, powers := [(2, 1), (6, 1), (16, 1), (29, 1), (40, 1), (48, 1), (58, 1)] }, { coefficient := -1, powers := [(3, 1), (4, 1), (15, 1), (16, 1), (24, 1), (26, 1), (29, 1), (48, 1), (52, 1)] }, { coefficient := 1, powers := [(3, 1), (4, 1), (15, 1), (16, 1), (24, 1), (26, 1), (29, 1), (48, 1), (58, 1)] }, { coefficient := -1, powers := [(3, 1), (4, 1), (15, 1), (16, 1), (26, 1), (28, 1), (29, 1), (48, 1), (52, 1)] }, { coefficient := 1, powers := [(3, 1), (4, 1), (15, 1), (16, 1), (26, 1), (28, 1), (29, 1), (48, 1), (58, 1)] }, { coefficient := 1, powers := [(3, 1), (15, 1), (26, 1), (28, 1), (29, 1), (48, 1), (50, 1), (52, 1)] }, { coefficient := -1, powers := [(3, 1), (15, 1), (26, 1), (28, 1), (29, 1), (48, 1), (50, 1), (58, 1)] }, { coefficient := -1, powers := [(3, 1), (16, 1), (24, 1), (26, 1), (29, 1), (48, 1), (52, 1)] }, { coefficient := 1, powers := [(3, 1), (16, 1), (24, 1), (26, 1), (29, 1), (48, 1), (58, 1)] }, { coefficient := -1, powers := [(3, 1), (16, 1), (26, 1), (28, 1), (29, 1), (48, 1), (52, 1)] }, { coefficient := 1, powers := [(3, 1), (16, 1), (26, 1), (28, 1), (29, 1), (48, 1), (58, 1)] }, { coefficient := -1, powers := [(4, 1), (6, 1), (15, 1), (24, 1), (48, 1), (52, 1), (56, 1)] }, { coefficient := 1, powers := [(4, 1), (6, 1), (15, 1), (24, 1), (48, 1), (56, 1), (58, 1)] }, { coefficient := -1, powers := [(4, 1), (6, 1), (15, 1), (28, 1), (48, 1), (52, 1), (56, 1)] }, { coefficient := 1, powers := [(4, 1), (6, 1), (15, 1), (28, 1), (48, 1), (56, 1), (58, 1)] }, { coefficient := 1, powers := [(4, 1), (15, 1), (16, 1), (24, 1), (29, 1), (31, 1), (48, 1), (52, 1)] }, { coefficient := -1, powers := [(4, 1), (15, 1), (16, 1), (24, 1), (29, 1), (31, 1), (48, 1), (58, 1)] }, { coefficient := 1, powers := [(4, 1), (15, 1), (16, 1), (28, 1), (29, 1), (31, 1), (48, 1), (52, 1)] }, { coefficient := -1, powers := [(4, 1), (15, 1), (16, 1), (28, 1), (29, 1), (31, 1), (48, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (6, 1), (10, 1), (48, 1), (52, 1), (55, 1)] }, { coefficient := -1, powers := [(5, 1), (6, 1), (10, 1), (48, 1), (55, 1), (58, 1)] }, { coefficient := -2, powers := [(5, 1), (6, 1), (48, 1), (53, 1), (55, 1)] }, { coefficient := -2, powers := [(6, 1), (10, 1), (48, 1), (55, 1)] }, { coefficient := 1, powers := [(15, 1), (24, 1), (29, 1), (31, 1), (48, 1), (50, 1), (52, 1)] }, { coefficient := -1, powers := [(15, 1), (24, 1), (29, 1), (31, 1), (48, 1), (50, 1), (58, 1)] }, { coefficient := -2, powers := [(15, 1), (26, 1), (29, 1), (48, 1), (50, 1), (52, 1)] }, { coefficient := 2, powers := [(15, 1), (26, 1), (29, 1), (48, 1), (50, 1), (58, 1)] }, { coefficient := 1, powers := [(16, 1), (26, 1), (29, 1), (48, 1), (52, 1)] }, { coefficient := -1, powers := [(16, 1), (26, 1), (29, 1), (48, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (2, 1), (7, 1), (16, 1), (29, 1), (31, 1), (48, 1), (61, 1)] }, { coefficient := -1, powers := [(1, 1), (2, 1), (16, 1), (29, 1), (31, 1), (48, 1)] }, { coefficient := -1, powers := [(2, 1), (6, 1), (16, 1), (29, 1), (40, 1), (48, 1)] }, { coefficient := 1, powers := [(3, 1), (4, 1), (15, 1), (16, 1), (24, 1), (26, 1), (29, 1), (48, 1)] }, { coefficient := 1, powers := [(3, 1), (4, 1), (15, 1), (16, 1), (26, 1), (28, 1), (29, 1), (48, 1)] }, { coefficient := -1, powers := [(3, 1), (15, 1), (26, 1), (28, 1), (29, 1), (48, 1), (50, 1)] }, { coefficient := 1, powers := [(3, 1), (16, 1), (24, 1), (26, 1), (29, 1), (48, 1)] }, { coefficient := 1, powers := [(3, 1), (16, 1), (26, 1), (28, 1), (29, 1), (48, 1)] }, { coefficient := 1, powers := [(4, 1), (6, 1), (15, 1), (24, 1), (48, 1), (56, 1)] }, { coefficient := 1, powers := [(4, 1), (6, 1), (15, 1), (28, 1), (48, 1), (56, 1)] }, { coefficient := -1, powers := [(4, 1), (15, 1), (16, 1), (24, 1), (29, 1), (31, 1), (48, 1)] }, { coefficient := -1, powers := [(4, 1), (15, 1), (16, 1), (28, 1), (29, 1), (31, 1), (48, 1)] }, { coefficient := -1, powers := [(5, 1), (6, 1), (10, 1), (48, 1), (55, 1)] }, { coefficient := -1, powers := [(15, 1), (24, 1), (29, 1), (31, 1), (48, 1), (50, 1)] }, { coefficient := 2, powers := [(15, 1), (26, 1), (29, 1), (48, 1), (50, 1)] }, { coefficient := -1, powers := [(16, 1), (26, 1), (29, 1), (48, 1)] }],
  [{ coefficient := 2, powers := [(5, 1), (6, 1), (48, 1), (55, 1)] }],
  [{ coefficient := -2, powers := [(6, 1), (53, 1), (55, 1)] }],
  [{ coefficient := 2, powers := [(6, 1), (55, 1)] }],
  [{ coefficient := 2, powers := [(1, 1), (2, 1), (15, 1), (29, 1), (31, 1), (48, 1), (53, 1), (61, 1), (63, 1)] }],
  [{ coefficient := 2, powers := [(1, 2), (2, 1), (29, 1), (31, 1), (48, 1), (61, 1), (63, 1)] }],
  [{ coefficient := 2, powers := [(1, 1), (29, 1), (40, 1), (48, 1)] }],
  [{ coefficient := 2, powers := [(1, 1), (29, 1), (48, 1)] }],
  [{ coefficient := 2, powers := [(6, 1), (18, 1), (41, 1), (55, 1)] }, { coefficient := -2, powers := [(6, 1), (41, 1), (59, 1)] }],
  [{ coefficient := -2, powers := [(6, 1), (18, 1), (40, 1), (55, 1)] }, { coefficient := 2, powers := [(6, 1), (40, 1), (59, 1)] }],
  [{ coefficient := 2, powers := [(3, 1), (4, 1), (16, 1), (26, 1), (29, 1), (48, 1), (52, 1)] }, { coefficient := 2, powers := [(4, 1), (6, 1), (48, 1), (52, 1), (56, 1)] }, { coefficient := -2, powers := [(4, 1), (16, 1), (29, 1), (31, 1), (48, 1), (52, 1)] }, { coefficient := -2, powers := [(31, 1), (48, 1), (56, 1)] }],
  [{ coefficient := 2, powers := [(3, 1), (26, 1), (29, 1), (48, 1), (52, 1)] }, { coefficient := -2, powers := [(29, 1), (31, 1), (48, 1), (52, 1)] }],
  [{ coefficient := -2, powers := [(3, 1), (26, 1), (29, 1), (48, 1), (50, 1)] }, { coefficient := 2, powers := [(26, 1), (48, 1), (56, 1)] }, { coefficient := 2, powers := [(29, 1), (31, 1), (48, 1), (50, 1)] }],
  [{ coefficient := 2, powers := [(1, 1), (2, 1), (29, 1), (31, 1), (48, 1), (52, 1)] }, { coefficient := 2, powers := [(1, 1), (2, 1), (29, 1), (31, 1), (48, 1), (58, 1)] }, { coefficient := -2, powers := [(3, 1), (26, 1), (29, 1), (48, 1)] }],
  [{ coefficient := 2, powers := [(31, 1), (48, 1)] }],
  [{ coefficient := 2, powers := [(27, 1), (29, 1), (53, 1)] }],
  [{ coefficient := 2, powers := [(3, 1), (26, 1), (29, 1), (48, 1)] }],
  [{ coefficient := -2, powers := [(26, 1), (29, 1), (48, 1), (50, 1)] }, { coefficient := -2, powers := [(29, 1), (34, 1), (38, 1), (48, 1)] }],
  [{ coefficient := 2, powers := [(1, 1), (2, 1), (5, 1), (29, 1), (31, 1), (48, 1), (52, 1)] }, { coefficient := 2, powers := [(1, 1), (2, 1), (29, 1), (31, 1), (48, 1)] }, { coefficient := -2, powers := [(3, 1), (26, 1), (28, 1), (29, 1), (48, 1)] }, { coefficient := 2, powers := [(26, 1), (29, 1), (48, 1)] }],
  [{ coefficient := -2, powers := [(27, 1), (29, 1)] }],
  [{ coefficient := -2, powers := [(27, 1), (28, 1), (53, 1)] }],
  [{ coefficient := -2, powers := [(26, 1), (48, 1)] }],
  [{ coefficient := 2, powers := [(27, 1)] }],
  [{ coefficient := -2, powers := [(32, 1), (53, 1)] }],
  [{ coefficient := 2, powers := [(32, 1)] }],
  [{ coefficient := -2, powers := [(1, 1), (2, 1), (29, 1), (31, 1), (48, 1), (53, 1), (61, 1), (63, 1)] }, { coefficient := 2, powers := [(29, 1), (34, 1), (48, 1), (58, 1), (63, 1)] }],
  [{ coefficient := 2, powers := [(29, 1), (48, 1), (52, 1)] }],
  [{ coefficient := 2, powers := [(28, 1), (48, 1), (56, 1)] }, { coefficient := -2, powers := [(29, 1), (48, 1), (50, 1)] }],
  [{ coefficient := -2, powers := [(2, 1), (16, 1), (29, 1), (48, 1), (52, 1)] }],
  [{ coefficient := 2, powers := [(2, 1), (16, 1), (29, 1), (48, 1)] }],
  [{ coefficient := 2, powers := [(28, 1), (53, 1)] }],
  [{ coefficient := -2, powers := [] }],
  [{ coefficient := 2, powers := [(3, 1), (16, 1), (26, 1), (28, 1), (29, 1), (48, 1), (52, 1)] }, { coefficient := -2, powers := [(3, 1), (16, 1), (26, 1), (29, 1), (48, 1)] }, { coefficient := 2, powers := [(6, 1), (28, 1), (48, 1), (52, 1), (56, 1)] }, { coefficient := -2, powers := [(6, 1), (48, 1), (56, 1)] }, { coefficient := -2, powers := [(16, 1), (28, 1), (29, 1), (31, 1), (48, 1), (52, 1)] }, { coefficient := 2, powers := [(16, 1), (29, 1), (31, 1), (48, 1)] }],
  [{ coefficient := -2, powers := [(3, 1), (4, 1), (16, 1), (26, 1), (29, 1), (48, 1)] }, { coefficient := 2, powers := [(3, 1), (26, 1), (29, 1), (48, 1), (50, 1)] }, { coefficient := -2, powers := [(4, 1), (6, 1), (48, 1), (56, 1)] }, { coefficient := 2, powers := [(4, 1), (16, 1), (29, 1), (31, 1), (48, 1)] }, { coefficient := -2, powers := [(26, 1), (48, 1), (56, 1)] }],
  [{ coefficient := -2, powers := [(1, 1), (26, 1), (29, 1), (48, 1), (50, 1), (52, 1)] }, { coefficient := 2, powers := [(1, 1), (26, 1), (29, 1), (48, 1), (53, 1)] }, { coefficient := -2, powers := [(15, 1), (26, 1), (29, 1), (48, 1), (50, 1), (52, 1)] }, { coefficient := 2, powers := [(15, 1), (26, 1), (29, 1), (48, 1), (53, 1)] }],
  [{ coefficient := 2, powers := [(16, 1), (29, 1), (30, 1), (48, 1), (52, 1)] }],
  [{ coefficient := -2, powers := [(1, 2), (2, 1), (7, 1), (29, 1), (31, 1), (48, 1), (53, 1), (61, 1)] }, { coefficient := -2, powers := [(1, 1), (2, 1), (7, 1), (15, 1), (29, 1), (31, 1), (48, 1), (53, 1), (61, 1)] }, { coefficient := -2, powers := [(15, 1), (29, 1), (34, 1), (38, 1), (48, 1), (58, 1)] }]
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
    (values : Fin 64 → R) :
    ¬ ∀ index : Fin 39,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((2 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (2 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (2 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.FrozenCase0NoncollapseType01Chart3B0Z1W14ZeroCertificate.selectedHasNoCommonZero

end Krenn.FrozenCase0NoncollapseType01Chart3B0Z1W14ZeroCertificate
