import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component20.SelectedLeafB6_2

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "9f32b98da2e6b5a34360d02b41f81c7ac940fa40245ddd0ebc41f558e4699294"
def certificateSHA256 : String := "da736cffcc5db9347be290d55ba8e398a689e3a63ddbf2145e8936dfdd9cbd75"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 28 → Fin 642 := ![
  0,
  1,
  2,
  3,
  5,
  8,
  9,
  12,
  163,
  165,
  191,
  198,
  284,
  349,
  352,
  353,
  388,
  415,
  468,
  480,
  551,
  558,
  592,
  598,
  635,
  637,
  638,
  641
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 28 → SparsePoly (Fin 63) := ![
  [{ coefficient := 1, powers := [(1, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (32, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (31, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (59, 1)] }, { coefficient := 1, powers := [(43, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (59, 1)] }, { coefficient := 1, powers := [(43, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (52, 1)] }, { coefficient := 1, powers := [(29, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(43, 1), (53, 1)] }, { coefficient := 1, powers := [(49, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (20, 1), (55, 1)] }, { coefficient := 1, powers := [(13, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (51, 1)] }, { coefficient := 1, powers := [(7, 1), (31, 1)] }, { coefficient := 1, powers := [(11, 1), (27, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (59, 1)] }, { coefficient := 1, powers := [(13, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (59, 1)] }, { coefficient := 1, powers := [(13, 1), (56, 1)] }, { coefficient := 1, powers := [(19, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (41, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (55, 1)] }, { coefficient := 1, powers := [(13, 1), (24, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (24, 1), (58, 1)] }, { coefficient := 1, powers := [(24, 1)] }, { coefficient := 1, powers := [(28, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (35, 1)] }, { coefficient := 1, powers := [(23, 1), (43, 1)] }, { coefficient := 1, powers := [(28, 1), (43, 1)] }, { coefficient := 1, powers := [(35, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (53, 1)] }, { coefficient := 1, powers := [(29, 1), (41, 1)] }, { coefficient := 1, powers := [(29, 1), (46, 1), (49, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (43, 1), (52, 1)] }, { coefficient := 1, powers := [(24, 1), (56, 1)] }, { coefficient := 1, powers := [(29, 1), (47, 1)] }, { coefficient := 1, powers := [(35, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (51, 1)] }, { coefficient := 1, powers := [(3, 1), (58, 1)] }, { coefficient := 1, powers := [(20, 1), (51, 1)] }, { coefficient := 1, powers := [(20, 1), (55, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (58, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (58, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (52, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (29, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (32, 1), (56, 1)] }, { coefficient := 1, powers := [(3, 1), (35, 1), (53, 1)] }, { coefficient := 1, powers := [(23, 1), (43, 1), (53, 1)] }, { coefficient := 1, powers := [(23, 1), (49, 1), (56, 1)] }, { coefficient := 1, powers := [(29, 1), (43, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (41, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (47, 1), (53, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (53, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (59, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (47, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(13, 1), (24, 1), (56, 1)] }, { coefficient := 1, powers := [(13, 1), (29, 1), (47, 1)] }, { coefficient := 1, powers := [(13, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (53, 1)] }, { coefficient := 1, powers := [(19, 1), (29, 1), (41, 1)] }, { coefficient := 1, powers := [(19, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1), (61, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(41, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 28 → SparsePoly (Fin 63) := ![
  [{ coefficient := 1, powers := [(0, 1), (7, 1), (13, 1), (29, 1), (31, 1), (46, 1), (61, 2)] }, { coefficient := 1, powers := [(0, 1), (11, 1), (13, 1), (27, 1), (29, 1), (46, 1), (61, 2)] }, { coefficient := -1, powers := [(3, 1), (13, 1), (29, 1), (46, 1), (58, 1), (61, 1)] }, { coefficient := 1, powers := [(7, 1), (13, 1), (20, 1), (29, 1), (31, 1), (46, 1), (61, 2)] }, { coefficient := 1, powers := [(11, 1), (13, 1), (20, 1), (27, 1), (29, 1), (46, 1), (61, 2)] }, { coefficient := -1, powers := [(13, 1), (20, 1), (29, 1), (46, 1), (55, 1), (61, 1)] }],
  [{ coefficient := -2, powers := [(8, 1), (28, 1), (59, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (7, 1), (8, 1), (31, 1), (32, 1), (61, 2)] }, { coefficient := -1, powers := [(0, 1), (7, 1), (13, 1), (29, 1), (31, 1), (61, 2)] }, { coefficient := 1, powers := [(0, 1), (8, 1), (11, 1), (27, 1), (32, 1), (61, 2)] }, { coefficient := -1, powers := [(0, 1), (11, 1), (13, 1), (27, 1), (29, 1), (61, 2)] }, { coefficient := -1, powers := [(3, 1), (8, 1), (32, 1), (58, 1), (61, 1)] }, { coefficient := 1, powers := [(3, 1), (13, 1), (29, 1), (58, 1), (61, 1)] }, { coefficient := 1, powers := [(7, 1), (8, 1), (20, 1), (31, 1), (32, 1), (61, 2)] }, { coefficient := -1, powers := [(7, 1), (13, 1), (20, 1), (29, 1), (31, 1), (61, 2)] }, { coefficient := 1, powers := [(8, 1), (11, 1), (20, 1), (27, 1), (32, 1), (61, 2)] }, { coefficient := -1, powers := [(8, 1), (20, 1), (32, 1), (55, 1), (61, 1)] }, { coefficient := -1, powers := [(11, 1), (13, 1), (20, 1), (27, 1), (29, 1), (61, 2)] }, { coefficient := 1, powers := [(13, 1), (20, 1), (29, 1), (55, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (7, 1), (19, 1), (29, 1), (31, 1), (46, 1), (61, 2)] }, { coefficient := -1, powers := [(0, 1), (11, 1), (19, 1), (27, 1), (29, 1), (46, 1), (61, 2)] }, { coefficient := 1, powers := [(3, 1), (19, 1), (29, 1), (46, 1), (58, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (23, 1), (56, 1), (58, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (28, 1), (56, 1), (58, 1), (61, 1)] }, { coefficient := -2, powers := [(5, 1), (29, 1), (43, 1), (58, 1), (61, 1)] }, { coefficient := -1, powers := [(7, 1), (19, 1), (20, 1), (29, 1), (31, 1), (46, 1), (61, 2)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (43, 1), (58, 1), (61, 1)] }, { coefficient := -1, powers := [(11, 1), (19, 1), (20, 1), (27, 1), (29, 1), (46, 1), (61, 2)] }, { coefficient := 1, powers := [(19, 1), (20, 1), (29, 1), (46, 1), (55, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (5, 1), (7, 1), (31, 1), (35, 1), (61, 2)] }, { coefficient := 1, powers := [(0, 1), (5, 1), (11, 1), (27, 1), (35, 1), (61, 2)] }, { coefficient := -1, powers := [(0, 1), (11, 1), (19, 1), (24, 1), (27, 1), (61, 2)] }, { coefficient := -1, powers := [(3, 1), (5, 1), (35, 1), (58, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (7, 1), (20, 1), (31, 1), (35, 1), (61, 2)] }, { coefficient := 1, powers := [(5, 1), (11, 1), (20, 1), (27, 1), (35, 1), (61, 2)] }, { coefficient := -1, powers := [(5, 1), (20, 1), (35, 1), (55, 1), (61, 1)] }, { coefficient := -1, powers := [(5, 1), (35, 1), (36, 1), (58, 1), (61, 1)] }, { coefficient := -1, powers := [(11, 1), (19, 1), (20, 1), (24, 1), (27, 1), (61, 2)] }, { coefficient := 1, powers := [(19, 1), (20, 1), (24, 1), (55, 1), (61, 1)] }, { coefficient := 2, powers := [(19, 1), (24, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (5, 1), (31, 1), (56, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (20, 1), (31, 1), (56, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (7, 1), (24, 1), (59, 1), (61, 1)] }, { coefficient := 1, powers := [(7, 1), (20, 1), (24, 1), (59, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (5, 1), (27, 1), (32, 1), (61, 1)] }, { coefficient := -1, powers := [(0, 1), (13, 1), (24, 1), (27, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (20, 1), (27, 1), (32, 1), (61, 1)] }, { coefficient := -1, powers := [(13, 1), (20, 1), (24, 1), (27, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (29, 1), (58, 1)] }, { coefficient := -1, powers := [(8, 1), (24, 1), (58, 1)] }],
  [{ coefficient := 2, powers := [(5, 1), (29, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (7, 1), (13, 1), (31, 1), (43, 1), (61, 1)] }, { coefficient := -1, powers := [(0, 1), (11, 1), (13, 1), (27, 1), (43, 1), (61, 1)] }, { coefficient := 1, powers := [(3, 1), (13, 1), (43, 1), (58, 1)] }, { coefficient := 2, powers := [(6, 1), (18, 1), (59, 1)] }, { coefficient := -1, powers := [(7, 1), (13, 1), (20, 1), (31, 1), (43, 1), (61, 1)] }, { coefficient := -1, powers := [(11, 1), (13, 1), (20, 1), (27, 1), (43, 1), (61, 1)] }, { coefficient := 1, powers := [(13, 1), (20, 1), (43, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (28, 1), (58, 1)] }],
  [{ coefficient := 2, powers := [(24, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (61, 1)] }, { coefficient := -1, powers := [(20, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (7, 1), (29, 1), (31, 1), (61, 1)] }, { coefficient := 1, powers := [(0, 1), (11, 1), (27, 1), (29, 1), (61, 1)] }, { coefficient := -1, powers := [(3, 1), (29, 1), (58, 1)] }, { coefficient := 1, powers := [(7, 1), (20, 1), (29, 1), (31, 1), (61, 1)] }, { coefficient := 1, powers := [(11, 1), (20, 1), (27, 1), (29, 1), (61, 1)] }, { coefficient := -1, powers := [(20, 1), (29, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (11, 1), (24, 1), (27, 1), (61, 1)] }, { coefficient := 1, powers := [(11, 1), (20, 1), (24, 1), (27, 1), (61, 1)] }, { coefficient := -1, powers := [(20, 1), (24, 1), (55, 1)] }, { coefficient := -2, powers := [(24, 1)] }],
  [{ coefficient := -1, powers := [(20, 1), (56, 1)] }],
  [{ coefficient := 2, powers := [(8, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (53, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (7, 1), (19, 1), (31, 1), (61, 1)] }, { coefficient := 1, powers := [(0, 1), (11, 1), (19, 1), (27, 1), (61, 1)] }, { coefficient := -1, powers := [(3, 1), (19, 1), (58, 1)] }, { coefficient := 1, powers := [(7, 1), (19, 1), (20, 1), (31, 1), (61, 1)] }, { coefficient := 1, powers := [(11, 1), (19, 1), (20, 1), (27, 1), (61, 1)] }, { coefficient := -1, powers := [(19, 1), (20, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (7, 1), (13, 1), (31, 1), (61, 1)] }, { coefficient := 1, powers := [(0, 1), (11, 1), (13, 1), (27, 1), (61, 1)] }, { coefficient := -1, powers := [(3, 1), (13, 1), (58, 1)] }, { coefficient := 1, powers := [(7, 1), (13, 1), (20, 1), (31, 1), (61, 1)] }, { coefficient := 1, powers := [(11, 1), (13, 1), (20, 1), (27, 1), (61, 1)] }, { coefficient := -1, powers := [(13, 1), (20, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [] }],
  [{ coefficient := -2, powers := [(6, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (7, 1), (31, 1), (61, 1)] }, { coefficient := -1, powers := [(0, 1), (11, 1), (27, 1), (61, 1)] }, { coefficient := 1, powers := [(3, 1), (58, 1)] }, { coefficient := -1, powers := [(7, 1), (20, 1), (31, 1), (61, 1)] }, { coefficient := -1, powers := [(11, 1), (20, 1), (27, 1), (61, 1)] }, { coefficient := 1, powers := [(20, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (5, 1), (7, 1), (31, 1), (35, 1), (53, 1), (61, 1)] }, { coefficient := -1, powers := [(0, 1), (5, 1), (11, 1), (27, 1), (35, 1), (53, 1), (61, 1)] }, { coefficient := -1, powers := [(0, 1), (7, 1), (8, 1), (31, 1), (32, 1), (47, 1), (61, 1)] }, { coefficient := -1, powers := [(0, 1), (7, 1), (13, 1), (29, 1), (31, 1), (43, 1), (46, 1), (61, 1)] }, { coefficient := 1, powers := [(0, 1), (7, 1), (13, 1), (29, 1), (31, 1), (47, 1), (61, 1)] }, { coefficient := 1, powers := [(0, 1), (7, 1), (19, 1), (29, 1), (31, 1), (46, 1), (49, 1), (61, 1)] }, { coefficient := -1, powers := [(0, 1), (8, 1), (11, 1), (27, 1), (32, 1), (47, 1), (61, 1)] }, { coefficient := -1, powers := [(0, 1), (11, 1), (13, 1), (27, 1), (29, 1), (43, 1), (46, 1), (61, 1)] }, { coefficient := 1, powers := [(0, 1), (11, 1), (13, 1), (27, 1), (29, 1), (47, 1), (61, 1)] }, { coefficient := 1, powers := [(0, 1), (11, 1), (19, 1), (24, 1), (27, 1), (53, 1), (61, 1)] }, { coefficient := 1, powers := [(0, 1), (11, 1), (19, 1), (27, 1), (29, 1), (46, 1), (49, 1), (61, 1)] }, { coefficient := 1, powers := [(0, 1), (51, 1)] }, { coefficient := 1, powers := [(3, 1), (5, 1), (35, 1), (53, 1), (58, 1)] }, { coefficient := 1, powers := [(3, 1), (8, 1), (32, 1), (47, 1), (58, 1)] }, { coefficient := 1, powers := [(3, 1), (13, 1), (29, 1), (43, 1), (46, 1), (58, 1)] }, { coefficient := -1, powers := [(3, 1), (13, 1), (29, 1), (47, 1), (58, 1)] }, { coefficient := -1, powers := [(3, 1), (19, 1), (29, 1), (46, 1), (49, 1), (58, 1)] }, { coefficient := -1, powers := [(5, 1), (7, 1), (20, 1), (31, 1), (35, 1), (53, 1), (61, 1)] }, { coefficient := -1, powers := [(5, 1), (11, 1), (20, 1), (27, 1), (35, 1), (53, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (20, 1), (35, 1), (53, 1), (55, 1)] }, { coefficient := -1, powers := [(5, 1), (23, 1), (49, 1), (56, 1), (58, 1)] }, { coefficient := -1, powers := [(5, 1), (28, 1), (49, 1), (56, 1), (58, 1)] }, { coefficient := 2, powers := [(5, 1), (29, 1), (43, 1), (49, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (36, 1), (53, 1), (58, 1)] }, { coefficient := -1, powers := [(7, 1), (8, 1), (20, 1), (31, 1), (32, 1), (47, 1), (61, 1)] }, { coefficient := -1, powers := [(7, 1), (13, 1), (20, 1), (29, 1), (31, 1), (43, 1), (46, 1), (61, 1)] }, { coefficient := 1, powers := [(7, 1), (13, 1), (20, 1), (29, 1), (31, 1), (47, 1), (61, 1)] }, { coefficient := 1, powers := [(7, 1), (19, 1), (20, 1), (29, 1), (31, 1), (46, 1), (49, 1), (61, 1)] }, { coefficient := -1, powers := [(8, 1), (11, 1), (20, 1), (27, 1), (32, 1), (47, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (20, 1), (32, 1), (47, 1), (55, 1)] }, { coefficient := -1, powers := [(8, 1), (24, 1), (43, 1), (49, 1), (58, 1)] }, { coefficient := 2, powers := [(8, 1), (28, 1), (46, 1), (59, 1)] }, { coefficient := -1, powers := [(11, 1), (13, 1), (20, 1), (27, 1), (29, 1), (43, 1), (46, 1), (61, 1)] }, { coefficient := 1, powers := [(11, 1), (13, 1), (20, 1), (27, 1), (29, 1), (47, 1), (61, 1)] }, { coefficient := 1, powers := [(11, 1), (19, 1), (20, 1), (24, 1), (27, 1), (53, 1), (61, 1)] }, { coefficient := 1, powers := [(11, 1), (19, 1), (20, 1), (27, 1), (29, 1), (46, 1), (49, 1), (61, 1)] }, { coefficient := 1, powers := [(13, 1), (20, 1), (29, 1), (43, 1), (46, 1), (55, 1)] }, { coefficient := -1, powers := [(13, 1), (20, 1), (29, 1), (47, 1), (55, 1)] }, { coefficient := -1, powers := [(19, 1), (20, 1), (24, 1), (53, 1), (55, 1)] }, { coefficient := -1, powers := [(19, 1), (20, 1), (29, 1), (46, 1), (49, 1), (55, 1)] }, { coefficient := -2, powers := [(19, 1), (24, 1), (53, 1)] }, { coefficient := 1, powers := [(20, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (7, 1), (31, 1), (38, 1), (59, 1), (61, 1)] }, { coefficient := 1, powers := [(0, 1), (7, 1), (31, 1), (41, 1), (56, 1), (61, 1)] }, { coefficient := 1, powers := [(0, 1), (7, 1), (31, 1), (47, 1), (53, 1), (61, 1)] }, { coefficient := 1, powers := [(0, 1), (11, 1), (27, 1), (38, 1), (59, 1), (61, 1)] }, { coefficient := 1, powers := [(0, 1), (11, 1), (27, 1), (41, 1), (56, 1), (61, 1)] }, { coefficient := 1, powers := [(0, 1), (11, 1), (27, 1), (47, 1), (53, 1), (61, 1)] }, { coefficient := -1, powers := [(3, 1), (38, 1), (58, 1), (59, 1)] }, { coefficient := -1, powers := [(3, 1), (41, 1), (56, 1), (58, 1)] }, { coefficient := -1, powers := [(3, 1), (47, 1), (53, 1), (58, 1)] }, { coefficient := 2, powers := [(6, 1), (38, 1), (58, 1), (59, 1)] }, { coefficient := 2, powers := [(6, 1), (46, 1), (52, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (20, 1), (31, 1), (38, 1), (59, 1), (61, 1)] }, { coefficient := 1, powers := [(7, 1), (20, 1), (31, 1), (41, 1), (56, 1), (61, 1)] }, { coefficient := 1, powers := [(7, 1), (20, 1), (31, 1), (47, 1), (53, 1), (61, 1)] }, { coefficient := 1, powers := [(11, 1), (20, 1), (27, 1), (38, 1), (59, 1), (61, 1)] }, { coefficient := 1, powers := [(11, 1), (20, 1), (27, 1), (41, 1), (56, 1), (61, 1)] }, { coefficient := 1, powers := [(11, 1), (20, 1), (27, 1), (47, 1), (53, 1), (61, 1)] }, { coefficient := -1, powers := [(20, 1), (38, 1), (55, 1), (59, 1)] }, { coefficient := -1, powers := [(20, 1), (47, 1), (53, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (7, 1), (8, 1), (31, 1), (35, 1), (61, 1)] }, { coefficient := -1, powers := [(0, 1), (7, 1), (19, 1), (29, 1), (31, 1), (61, 1)] }, { coefficient := 1, powers := [(0, 1), (8, 1), (11, 1), (27, 1), (35, 1), (61, 1)] }, { coefficient := -1, powers := [(0, 1), (11, 1), (19, 1), (27, 1), (29, 1), (61, 1)] }, { coefficient := -1, powers := [(3, 1), (8, 1), (35, 1), (58, 1)] }, { coefficient := 1, powers := [(3, 1), (19, 1), (29, 1), (58, 1)] }, { coefficient := 1, powers := [(7, 1), (8, 1), (20, 1), (31, 1), (35, 1), (61, 1)] }, { coefficient := -1, powers := [(7, 1), (19, 1), (20, 1), (29, 1), (31, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (11, 1), (20, 1), (27, 1), (35, 1), (61, 1)] }, { coefficient := -1, powers := [(8, 1), (20, 1), (35, 1), (55, 1)] }, { coefficient := -1, powers := [(11, 1), (19, 1), (20, 1), (27, 1), (29, 1), (61, 1)] }, { coefficient := 1, powers := [(19, 1), (20, 1), (29, 1), (55, 1)] }]
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
    (values : Fin 63 → R) :
    ¬ ∀ index : Fin 28,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component20.SelectedLeafB6_2.selectedHasNoCommonZero

end Krenn.Component20.SelectedLeafB6_2
