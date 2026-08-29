import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component17.SelectedLeafB5_4_3

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "babae7c74245f3f66fbb3606b07bb599e0f61bd0922584495b5820d70b9395c2"
def certificateSHA256 : String := "4b75bbaa556c964add0b635faeb4a40b357a52b763d3c0a8c76a553017ae4cda"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 52 → Fin 611 := ![
  12,
  14,
  17,
  18,
  26,
  32,
  40,
  60,
  121,
  183,
  189,
  190,
  206,
  207,
  210,
  214,
  230,
  285,
  306,
  307,
  310,
  311,
  312,
  323,
  325,
  330,
  334,
  350,
  414,
  415,
  423,
  427,
  428,
  430,
  434,
  441,
  507,
  541,
  552,
  553,
  557,
  567,
  568,
  572,
  599,
  601,
  602,
  604,
  606,
  607,
  608,
  609
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 52 → SparsePoly (Fin 64) := ![
  [{ coefficient := 1, powers := [(12, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(28, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (32, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (27, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (52, 1)] }, { coefficient := 1, powers := [(19, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (33, 1)] }, { coefficient := 1, powers := [(17, 1), (20, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (32, 1)] }, { coefficient := 1, powers := [(32, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (19, 1)] }, { coefficient := 1, powers := [(17, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (43, 1)] }, { coefficient := 1, powers := [(18, 1), (19, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (43, 1)] }, { coefficient := 1, powers := [(27, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(52, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (33, 1), (49, 1)] }, { coefficient := 1, powers := [(5, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (25, 1), (44, 1)] }, { coefficient := 1, powers := [(17, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1)] }, { coefficient := 1, powers := [(19, 1), (43, 1)] }, { coefficient := 1, powers := [(24, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1)] }, { coefficient := 1, powers := [(20, 1), (43, 1)] }, { coefficient := 1, powers := [(24, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (42, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (53, 1)] }, { coefficient := 1, powers := [(17, 1), (27, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (58, 1)] }, { coefficient := 1, powers := [(13, 1), (47, 1)] }, { coefficient := 1, powers := [(18, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (56, 1)] }, { coefficient := 1, powers := [(9, 1), (53, 1)] }, { coefficient := 1, powers := [(14, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (45, 1)] }, { coefficient := 1, powers := [(18, 1), (40, 1)] }, { coefficient := 1, powers := [(18, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (52, 1)] }, { coefficient := 1, powers := [(29, 1), (41, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1), (50, 1)] }, { coefficient := 1, powers := [(19, 1), (43, 1), (50, 1)] }, { coefficient := 1, powers := [(43, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1), (50, 1)] }, { coefficient := 1, powers := [(20, 1), (43, 1), (50, 1)] }, { coefficient := 1, powers := [(47, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (56, 1)] }, { coefficient := 1, powers := [(8, 1), (23, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (24, 1), (40, 1)] }, { coefficient := 1, powers := [(17, 1), (24, 1), (44, 1)] }, { coefficient := 1, powers := [(17, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (24, 1), (45, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (40, 1)] }, { coefficient := 1, powers := [(18, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1)] }, { coefficient := 1, powers := [(24, 1), (40, 1), (43, 1)] }, { coefficient := 1, powers := [(24, 1), (45, 1)] }, { coefficient := 1, powers := [(43, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (44, 1)] }, { coefficient := 1, powers := [(17, 1), (27, 1), (40, 1)] }, { coefficient := 1, powers := [(17, 1), (27, 1), (44, 1)] }, { coefficient := 1, powers := [(17, 1), (28, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (45, 1)] }, { coefficient := 1, powers := [(17, 1), (27, 1), (45, 1)] }, { coefficient := 1, powers := [(18, 1), (27, 1), (40, 1)] }, { coefficient := 1, powers := [(18, 1), (28, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (47, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1)] }, { coefficient := 1, powers := [(17, 1), (27, 1), (47, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (52, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1)] }, { coefficient := 1, powers := [(13, 1), (29, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (58, 1)] }, { coefficient := 1, powers := [(13, 1), (25, 1), (45, 1)] }, { coefficient := 1, powers := [(13, 1), (55, 1)] }, { coefficient := 1, powers := [(18, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (35, 1), (40, 1)] }, { coefficient := 1, powers := [(27, 1), (40, 1), (43, 1)] }, { coefficient := 1, powers := [(27, 1), (45, 1)] }, { coefficient := 1, powers := [(28, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (43, 1), (51, 1)] }, { coefficient := 1, powers := [(23, 1), (55, 1)] }, { coefficient := 1, powers := [(29, 1), (47, 1)] }, { coefficient := 1, powers := [(35, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (38, 1), (58, 1)] }, { coefficient := 1, powers := [(0, 1), (41, 1), (55, 1)] }, { coefficient := 1, powers := [(0, 1), (47, 1), (52, 1)] }, { coefficient := 1, powers := [(20, 1), (43, 1), (52, 1)] }, { coefficient := 1, powers := [(25, 1), (41, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (40, 1), (53, 1)] }, { coefficient := 1, powers := [(6, 1), (33, 1), (40, 1)] }, { coefficient := 1, powers := [(14, 1), (24, 1), (40, 1)] }, { coefficient := 1, powers := [(14, 1)] }, { coefficient := 1, powers := [(53, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (36, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (39, 1), (53, 1)] }, { coefficient := 1, powers := [(2, 1), (42, 1), (48, 1)] }, { coefficient := 1, powers := [(12, 1), (22, 1), (53, 1)] }, { coefficient := 1, powers := [(12, 1), (27, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1)] }, { coefficient := 1, powers := [(3, 1), (33, 1)] }, { coefficient := 1, powers := [(14, 1), (19, 1)] }, { coefficient := 1, powers := [(19, 1), (53, 1)] }, { coefficient := 1, powers := [(24, 1), (42, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (48, 1)] }, { coefficient := 1, powers := [(6, 1), (30, 1)] }, { coefficient := 1, powers := [(9, 1), (24, 1)] }, { coefficient := 1, powers := [(19, 1), (48, 1)] }, { coefficient := 1, powers := [(24, 1), (39, 1)] }, { coefficient := 1, powers := [(30, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (40, 1), (55, 1)] }, { coefficient := 1, powers := [(0, 1), (45, 1), (51, 1)] }, { coefficient := 1, powers := [(25, 1), (40, 1), (43, 1)] }, { coefficient := 1, powers := [(25, 1), (45, 1)] }, { coefficient := 1, powers := [(43, 1), (51, 1)] }, { coefficient := 1, powers := [(55, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (36, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (39, 1), (53, 1)] }, { coefficient := 1, powers := [(0, 1), (42, 1), (48, 1)] }, { coefficient := 1, powers := [(3, 1), (24, 1), (56, 1)] }, { coefficient := 1, powers := [(3, 1), (30, 1), (53, 1)] }, { coefficient := 1, powers := [(3, 1), (33, 1), (48, 1)] }, { coefficient := 1, powers := [(6, 1), (19, 1), (56, 1)] }, { coefficient := 1, powers := [(6, 1), (30, 1), (42, 1)] }, { coefficient := 1, powers := [(6, 1), (33, 1), (39, 1)] }, { coefficient := 1, powers := [(9, 1), (19, 1), (53, 1)] }, { coefficient := 1, powers := [(9, 1), (24, 1), (42, 1)] }, { coefficient := 1, powers := [(9, 1), (33, 1), (36, 1)] }, { coefficient := 1, powers := [(14, 1), (19, 1), (48, 1)] }, { coefficient := 1, powers := [(14, 1), (24, 1), (39, 1)] }, { coefficient := 1, powers := [(14, 1), (30, 1), (36, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (41, 1), (55, 1)] }, { coefficient := 1, powers := [(2, 1), (47, 1), (52, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (52, 1)] }, { coefficient := 1, powers := [(8, 1), (23, 1), (58, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (47, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(13, 1), (23, 1), (55, 1)] }, { coefficient := 1, powers := [(13, 1), (29, 1), (47, 1)] }, { coefficient := 1, powers := [(13, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (52, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (41, 1)] }, { coefficient := 1, powers := [(18, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (59, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (60, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(40, 1)] }],
  [{ coefficient := 1, powers := [(41, 1)] }],
  [{ coefficient := 1, powers := [(53, 1)] }],
  [{ coefficient := 1, powers := [(54, 1), (62, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 52 → SparsePoly (Fin 64) := ![
  [{ coefficient := -1, powers := [(0, 1), (5, 1), (27, 1), (32, 1), (55, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (5, 1), (24, 1), (29, 1), (32, 1), (47, 1), (50, 1), (55, 1), (56, 1)] }, { coefficient := -2, powers := [(29, 1), (47, 1), (50, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (5, 1), (23, 1), (24, 1), (32, 1), (51, 1), (55, 1), (56, 1)] }, { coefficient := -1, powers := [(23, 1), (51, 1)] }],
  [{ coefficient := -1, powers := [(23, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (5, 1), (9, 1), (27, 1), (32, 1), (55, 1), (60, 1)] }, { coefficient := -1, powers := [(0, 1), (5, 1), (27, 1), (32, 1), (39, 1), (55, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (5, 1), (27, 1), (32, 1), (48, 1), (55, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (9, 1), (24, 1), (27, 1), (32, 1), (55, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (19, 1), (27, 1), (32, 1), (48, 1), (55, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (27, 1), (30, 1), (32, 1), (36, 1), (55, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (5, 1), (17, 1), (24, 1), (32, 1), (47, 1), (55, 1), (56, 1)] }, { coefficient := -1, powers := [(17, 1), (47, 1)] }],
  [{ coefficient := -2, powers := [(17, 1), (24, 1), (47, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (9, 1), (33, 1), (55, 1), (62, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (39, 1), (55, 1), (62, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (48, 1), (55, 1), (62, 1)] }],
  [{ coefficient := -2, powers := [(25, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (20, 1), (43, 1), (50, 1), (59, 1)] }, { coefficient := 2, powers := [(2, 1), (44, 1), (47, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (5, 1), (24, 1), (32, 2), (49, 1), (55, 2)] }, { coefficient := -1, powers := [(3, 1), (5, 1), (24, 1), (32, 1), (35, 1), (49, 1), (52, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (33, 1), (39, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(13, 1), (23, 1), (24, 1), (28, 1), (45, 1), (51, 1), (60, 1)] }, { coefficient := 1, powers := [(13, 1), (23, 1), (25, 1), (28, 1), (45, 1), (60, 1)] }, { coefficient := 1, powers := [(23, 1), (43, 1), (52, 1), (59, 1)] }, { coefficient := 2, powers := [(23, 1), (45, 1), (52, 1)] }, { coefficient := 2, powers := [(27, 1), (44, 1), (47, 1), (52, 1)] }, { coefficient := 2, powers := [(28, 1), (47, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(13, 1), (23, 1), (24, 1), (28, 1), (51, 1), (60, 1)] }, { coefficient := 1, powers := [(13, 1), (23, 1), (25, 1), (28, 1), (60, 1)] }, { coefficient := 2, powers := [(23, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(17, 1), (52, 1)] }],
  [{ coefficient := -2, powers := [(2, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (5, 1), (24, 1), (32, 2), (55, 2)] }, { coefficient := 1, powers := [(3, 1), (5, 1), (24, 1), (32, 1), (35, 1), (52, 1), (55, 1)] }],
  [{ coefficient := 2, powers := [(27, 1), (47, 1)] }],
  [{ coefficient := -1, powers := [(17, 1), (23, 1), (52, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (5, 1), (13, 1), (24, 1), (29, 1), (32, 1), (50, 1), (55, 1), (56, 1)] }, { coefficient := 2, powers := [(13, 1), (29, 1), (50, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (5, 1), (9, 1), (32, 1), (55, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (5, 1), (32, 1), (39, 1), (55, 1), (60, 1)] }, { coefficient := -1, powers := [(0, 1), (5, 1), (32, 1), (48, 1), (55, 1), (60, 1)] }, { coefficient := -1, powers := [(5, 1), (9, 1), (24, 1), (32, 1), (55, 1), (60, 1)] }, { coefficient := -1, powers := [(5, 1), (19, 1), (32, 1), (48, 1), (55, 1), (60, 1)] }, { coefficient := -1, powers := [(5, 1), (30, 1), (32, 1), (36, 1), (55, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(29, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (19, 1), (32, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (19, 1), (23, 1), (24, 1), (28, 1), (51, 1), (60, 1)] }, { coefficient := -1, powers := [(13, 1), (19, 1), (23, 1), (25, 1), (28, 1), (60, 1)] }, { coefficient := -2, powers := [(19, 1), (23, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (5, 1), (18, 1), (24, 1), (32, 1), (55, 1), (56, 1)] }, { coefficient := 1, powers := [(18, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (20, 1), (52, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (5, 1), (13, 1), (24, 1), (29, 1), (32, 1), (55, 1), (56, 1)] }, { coefficient := -2, powers := [(13, 1), (29, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (5, 1), (24, 1), (32, 1), (55, 1), (58, 1)] }],
  [{ coefficient := -2, powers := [(27, 1), (47, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (23, 1), (24, 1), (28, 1), (51, 1), (60, 1)] }, { coefficient := -1, powers := [(13, 1), (23, 1), (25, 1), (28, 1), (60, 1)] }, { coefficient := -2, powers := [(23, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (23, 1), (51, 1)] }],
  [{ coefficient := -2, powers := [(19, 1), (47, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(13, 1), (23, 1), (24, 1), (51, 1), (60, 1)] }, { coefficient := 1, powers := [(13, 1), (23, 1), (25, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(52, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (5, 1), (24, 1), (32, 1), (47, 1), (55, 1), (56, 1)] }, { coefficient := 1, powers := [(47, 1)] }],
  [{ coefficient := 1, powers := [(23, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (17, 1), (23, 1), (24, 1), (51, 1), (60, 1)] }, { coefficient := -1, powers := [(13, 1), (17, 1), (23, 1), (25, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (5, 1), (13, 1), (24, 1), (32, 1), (55, 1), (56, 1)] }, { coefficient := 1, powers := [(13, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (9, 1), (19, 1), (32, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (19, 1), (32, 1), (39, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (24, 1), (32, 1), (39, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (32, 1), (36, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (5, 1), (32, 1), (55, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (9, 1), (32, 1), (55, 1)] }, { coefficient := -1, powers := [(5, 1), (32, 1), (39, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (32, 1), (42, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(13, 1), (23, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (32, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (5, 1), (24, 1), (32, 1), (55, 1), (56, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(2, 1), (38, 1), (58, 1)] }, { coefficient := -1, powers := [(2, 1), (47, 1), (52, 1)] }, { coefficient := 1, powers := [(17, 1), (23, 1), (43, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (5, 1), (9, 1), (32, 1), (42, 1), (55, 1)] }, { coefficient := -1, powers := [(0, 1), (5, 1), (32, 1), (36, 1), (55, 1), (56, 1)] }, { coefficient := -1, powers := [(0, 1), (5, 1), (32, 1), (39, 1), (42, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (9, 1), (24, 1), (32, 1), (42, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (19, 1), (32, 1), (42, 1), (48, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (32, 1), (36, 1), (42, 1), (55, 1)] }, { coefficient := 1, powers := [(13, 1), (23, 1), (24, 1), (45, 1), (51, 1)] }, { coefficient := -1, powers := [(13, 1), (23, 1), (25, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (13, 1), (23, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (6, 1), (9, 1), (19, 1), (32, 1), (33, 1), (55, 1)] }, { coefficient := -1, powers := [(5, 1), (6, 1), (19, 1), (32, 1), (33, 1), (39, 1), (55, 1)] }, { coefficient := -1, powers := [(5, 1), (6, 1), (24, 1), (32, 1), (33, 1), (39, 1), (55, 1)] }, { coefficient := -1, powers := [(5, 1), (6, 1), (30, 1), (32, 1), (33, 1), (36, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (9, 1), (14, 1), (19, 1), (24, 1), (32, 1), (55, 1)] }, { coefficient := -1, powers := [(5, 1), (14, 1), (19, 1), (24, 1), (32, 1), (39, 1), (55, 1)] }, { coefficient := -1, powers := [(5, 1), (14, 1), (24, 2), (32, 1), (39, 1), (55, 1)] }, { coefficient := -1, powers := [(5, 1), (14, 1), (24, 1), (30, 1), (32, 1), (36, 1), (55, 1)] }, { coefficient := -1, powers := [(6, 1), (13, 1), (17, 1), (23, 1), (24, 1), (35, 1), (51, 1), (60, 1)] }, { coefficient := 1, powers := [(6, 1), (13, 1), (17, 1), (23, 1), (25, 1), (35, 1), (60, 1)] }, { coefficient := -1, powers := [(13, 1), (17, 1), (23, 1), (24, 1), (27, 1), (43, 1), (51, 1), (60, 1)] }, { coefficient := 1, powers := [(13, 1), (17, 1), (23, 1), (25, 1), (27, 1), (43, 1), (60, 1)] }, { coefficient := -1, powers := [(13, 1), (18, 1), (19, 1), (23, 1), (24, 1), (28, 1), (51, 1), (60, 1)] }, { coefficient := 1, powers := [(13, 1), (18, 1), (19, 1), (23, 1), (25, 1), (28, 1), (60, 1)] }, { coefficient := -1, powers := [(13, 1), (18, 1), (23, 1), (24, 2), (28, 1), (51, 1), (60, 1)] }, { coefficient := 1, powers := [(13, 1), (18, 1), (23, 1), (24, 1), (25, 1), (28, 1), (60, 1)] }, { coefficient := 1, powers := [(13, 1), (18, 1), (23, 1), (24, 1), (27, 1), (51, 1), (60, 1)] }, { coefficient := -1, powers := [(13, 1), (18, 1), (23, 1), (25, 1), (27, 1), (60, 1)] }, { coefficient := -1, powers := [(13, 1), (23, 1), (24, 1), (43, 1), (51, 1)] }, { coefficient := 1, powers := [(13, 1), (23, 1), (25, 1), (43, 1)] }, { coefficient := 2, powers := [(17, 1), (19, 1), (27, 1), (47, 1), (52, 1)] }, { coefficient := 2, powers := [(17, 1), (24, 1), (27, 1), (47, 1), (52, 1)] }, { coefficient := 2, powers := [(18, 1), (19, 1), (23, 1), (52, 1)] }, { coefficient := 2, powers := [(18, 1), (23, 1), (24, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (2, 1), (55, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (3, 1), (5, 1), (24, 1), (32, 1), (55, 2), (56, 1)] }, { coefficient := -1, powers := [(2, 1), (25, 1), (43, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (55, 1)] }, { coefficient := 1, powers := [(3, 1), (5, 1), (8, 1), (24, 1), (32, 1), (35, 1), (55, 1), (56, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1)] }, { coefficient := -1, powers := [(18, 1), (29, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (2, 1), (5, 1), (32, 1), (39, 1), (55, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (5, 1), (9, 1), (17, 1), (22, 1), (32, 1), (55, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (5, 1), (9, 1), (19, 1), (32, 1), (40, 1), (55, 1)] }, { coefficient := -1, powers := [(0, 1), (5, 1), (12, 1), (22, 1), (32, 1), (55, 1), (60, 1)] }, { coefficient := -1, powers := [(0, 1), (5, 1), (17, 1), (22, 1), (32, 1), (39, 1), (55, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (5, 1), (17, 1), (22, 1), (32, 1), (48, 1), (55, 1), (60, 1)] }, { coefficient := -1, powers := [(0, 1), (5, 1), (19, 1), (32, 1), (39, 1), (40, 1), (55, 1)] }, { coefficient := -1, powers := [(0, 1), (5, 1), (24, 1), (32, 1), (39, 1), (40, 1), (55, 1)] }, { coefficient := -1, powers := [(0, 1), (5, 1), (30, 1), (32, 1), (36, 1), (40, 1), (55, 1)] }, { coefficient := 1, powers := [(0, 1), (5, 1), (32, 1), (39, 1), (55, 1)] }, { coefficient := 1, powers := [(3, 1), (5, 1), (17, 1), (20, 1), (24, 1), (32, 2), (49, 1), (55, 2)] }, { coefficient := 1, powers := [(3, 1), (5, 1), (17, 1), (20, 1), (24, 1), (32, 1), (35, 1), (49, 1), (52, 1), (55, 1)] }, { coefficient := 1, powers := [(3, 1), (5, 1), (30, 1), (32, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (9, 1), (17, 1), (22, 1), (24, 1), (32, 1), (55, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (17, 1), (19, 1), (22, 1), (32, 1), (48, 1), (55, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (17, 1), (22, 1), (30, 1), (32, 1), (36, 1), (55, 1), (60, 1)] }, { coefficient := -1, powers := [(5, 1), (24, 1), (32, 1), (39, 1), (55, 1)] }, { coefficient := -1, powers := [(5, 1), (30, 1), (32, 1), (36, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (5, 1), (9, 1), (32, 1), (33, 1), (55, 1)] }, { coefficient := -1, powers := [(3, 1), (5, 1), (32, 1), (33, 1), (39, 1), (55, 1)] }, { coefficient := -1, powers := [(3, 1), (5, 1), (32, 1), (33, 1), (48, 1), (55, 1)] }]
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
    (values : Fin 64 → R) :
    ¬ ∀ index : Fin 52,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component17.SelectedLeafB5_4_3.selectedHasNoCommonZero

end Krenn.Component17.SelectedLeafB5_4_3
